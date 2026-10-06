import NumStability.Analysis.FunctionalCalculus.Resolvent.Analyticity
import NumStability.Analysis.FunctionalCalculus.Resolvent.DunfordResidue

/-!
# Analysis.LinearOperators.Pseudospectra.PowerBounds.Contour

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

/-- Higham (18.8)--(18.9), resolvent representation of the
`epsilon`-pseudospectrum.  Spectral points are included explicitly because
Mathlib's totalized `resolvent` is zero there. -/
def resolventPseudospectrum (epsilon : ℝ) (a : A) : Set ℂ :=
  spectrum ℂ a ∪ {z : ℂ | epsilon⁻¹ ≤ ‖resolvent a z‖}

/-- The moduli occurring in the resolvent-form `epsilon`-pseudospectrum.
An `IsGreatest` witness for this set is exactly the maximum in (18.9). -/
def resolventPseudospectrumModulusSet (epsilon : ℝ) (a : A) : Set ℝ :=
  {r : ℝ | ∃ z ∈ resolventPseudospectrum epsilon a, r = ‖z‖}

lemma norm_mem_resolventPseudospectrumModulusSet {epsilon : ℝ} {a : A}
    {z : ℂ} (hz : z ∈ resolventPseudospectrum epsilon a) :
    ‖z‖ ∈ resolventPseudospectrumModulusSet epsilon a :=
  ⟨z, hz, rfl⟩

lemma resolventPseudospectralRadius_nonneg {epsilon rho : ℝ} {a : A}
    (hrho : IsGreatest (resolventPseudospectrumModulusSet epsilon a) rho) :
    0 ≤ rho := by
  rcases hrho.1 with ⟨z, _hz, rfl⟩
  exact norm_nonneg z

/-- Every point whose modulus is strictly larger than the resolvent
pseudospectral radius lies in the resolvent set. -/
lemma mem_resolventSet_of_resolventPseudospectralRadius_lt_norm
    {epsilon rho : ℝ} {a : A}
    (hrho : IsGreatest (resolventPseudospectrumModulusSet epsilon a) rho)
    {z : ℂ} (hz : rho < ‖z‖) :
    z ∈ resolventSet ℂ a := by
  by_contra hres
  have hspec : z ∈ spectrum ℂ a := by
    simpa [spectrum] using hres
  have hpseudo : z ∈ resolventPseudospectrum epsilon a := by
    exact Or.inl hspec
  exact (not_lt_of_ge (hrho.2
    (norm_mem_resolventPseudospectrumModulusSet hpseudo))) hz

/-- Outside the resolvent pseudospectral radius the resolvent norm is
strictly smaller than `epsilon⁻¹`. -/
lemma norm_resolvent_lt_inv_of_resolventPseudospectralRadius_lt_norm
    {epsilon rho : ℝ} {a : A}
    (hrho : IsGreatest (resolventPseudospectrumModulusSet epsilon a) rho)
    {z : ℂ} (hz : rho < ‖z‖) :
    ‖resolvent a z‖ < epsilon⁻¹ := by
  by_contra hnot
  have hlarge : epsilon⁻¹ ≤ ‖resolvent a z‖ := le_of_not_gt hnot
  have hpseudo : z ∈ resolventPseudospectrum epsilon a := by
    exact Or.inr hlarge
  exact (not_lt_of_ge (hrho.2
    (norm_mem_resolventPseudospectrumModulusSet hpseudo))) hz

variable [CompleteSpace A]

/-- For positive `epsilon`, the resolvent-form pseudospectrum is closed.  The
union with the spectrum repairs the discontinuity of Mathlib's totalized
resolvent at spectral points. -/
theorem isClosed_resolventPseudospectrum (a : A) (epsilon : ℝ) :
    IsClosed (resolventPseudospectrum epsilon a) := by
  rw [← isOpen_compl_iff]
  have hopen : IsOpen (resolventSet ℂ a ∩
      (fun z : ℂ => ‖resolvent a z‖) ⁻¹' Iio epsilon⁻¹) :=
    (resolvent_continuousOn a).norm.isOpen_inter_preimage
      (spectrum.isOpen_resolventSet a) isOpen_Iio
  have heq : (resolventPseudospectrum epsilon a)ᶜ =
      resolventSet ℂ a ∩
        (fun z : ℂ => ‖resolvent a z‖) ⁻¹' Iio epsilon⁻¹ := by
    ext z
    simp [resolventPseudospectrum, spectrum]
  rwa [heq]

/-- The resolvent-form pseudospectrum is bounded for positive `epsilon`.
This is the finite-radius content of `resolvent_tendsto_cobounded`. -/
theorem isBounded_resolventPseudospectrum (a : A) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    Bornology.IsBounded (resolventPseudospectrum epsilon a) := by
  have hball : Metric.ball (0 : A) epsilon⁻¹ ∈ 𝓝 (0 : A) :=
    Metric.ball_mem_nhds _ (inv_pos.mpr hepsilon)
  have hraw : ∀ᶠ z : ℂ in Bornology.cobounded ℂ,
      resolvent a z ∈ Metric.ball (0 : A) epsilon⁻¹ :=
    (spectrum.resolvent_tendsto_cobounded (𝕜 := ℂ) a).eventually hball
  have hevent : ∀ᶠ z : ℂ in Bornology.cobounded ℂ,
      ‖resolvent a z‖ < epsilon⁻¹ := by
    filter_upwards [hraw] with z hz
    simpa [Metric.mem_ball, dist_zero_left] using hz
  have hcob : Bornology.IsCobounded
      {z : ℂ | ‖resolvent a z‖ < epsilon⁻¹} := hevent
  have hlarge : Bornology.IsBounded
      {z : ℂ | epsilon⁻¹ ≤ ‖resolvent a z‖} := by
    have hcompl := hcob.compl
    simpa only [Set.compl_setOf, not_lt] using hcompl
  exact (spectrum.isBounded a).union hlarge

/-- Compactness of the positive-`epsilon` resolvent pseudospectrum. -/
theorem isCompact_resolventPseudospectrum (a : A) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    IsCompact (resolventPseudospectrum epsilon a) :=
  Metric.isCompact_of_isClosed_isBounded
    (isClosed_resolventPseudospectrum a epsilon)
    (isBounded_resolventPseudospectrum a hepsilon)

omit [CompleteSpace A] in
lemma resolventPseudospectrumModulusSet_eq_image (epsilon : ℝ) (a : A) :
    resolventPseudospectrumModulusSet epsilon a =
      norm '' resolventPseudospectrum epsilon a := by
  ext r
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

/-- The maximum in Higham's definition (18.9), now as a concrete scalar. -/
noncomputable def resolventPseudospectralRadius (epsilon : ℝ) (a : A) : ℝ :=
  sSup (resolventPseudospectrumModulusSet epsilon a)

/-- The maximum defining the pseudospectral radius exists in every nontrivial
complex Banach algebra when `epsilon > 0`. -/
theorem resolventPseudospectralRadius_isGreatest [Nontrivial A]
    (a : A) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    IsGreatest (resolventPseudospectrumModulusSet epsilon a)
      (resolventPseudospectralRadius epsilon a) := by
  have hcompact : IsCompact (resolventPseudospectrumModulusSet epsilon a) := by
    rw [resolventPseudospectrumModulusSet_eq_image]
    exact (isCompact_resolventPseudospectrum a hepsilon).image continuous_norm
  have hpseudo : (resolventPseudospectrum epsilon a).Nonempty :=
    (spectrum.nonempty a).mono (subset_union_left)
  have hmod : (resolventPseudospectrumModulusSet epsilon a).Nonempty := by
    rw [resolventPseudospectrumModulusSet_eq_image]
    exact hpseudo.image norm
  exact hcompact.isGreatest_sSup hmod

/-- The Dunford residue identity holds on every circle strictly outside the
resolvent-form pseudospectrum.  This removes the earlier `‖a‖ < R`
restriction by deforming from a larger circle through a resolvent annulus. -/
theorem pow_eq_two_pi_I_inv_smul_circleIntegral_of_resolventPseudospectralRadius_lt
    (a : A) (k : ℕ) {epsilon rho R : ℝ}
    (hrho : IsGreatest (resolventPseudospectrumModulusSet epsilon a) rho)
    (hrhoR : rho < R) :
    a ^ k = (2 * Real.pi * I : ℂ)⁻¹ •
      ∮ z in C(0, R), z ^ k • resolvent a z := by
  let Rbig : ℝ := max R (‖a‖ + 1)
  have hRpos : 0 < R :=
    (resolventPseudospectralRadius_nonneg hrho).trans_lt hrhoR
  have hRle : R ≤ Rbig := le_max_left _ _
  have haRbig : ‖a‖ < Rbig := by
    exact (lt_add_one ‖a‖).trans_le (le_max_right _ _)
  have hannulus : closedBall (0 : ℂ) Rbig \ ball 0 R ⊆
      resolventSet ℂ a := by
    intro z hz
    have hRz : R ≤ ‖z‖ := by
      have hznot : z ∉ ball (0 : ℂ) R := hz.2
      simpa [mem_ball, dist_zero_right, not_lt] using hznot
    exact mem_resolventSet_of_resolventPseudospectralRadius_lt_norm hrho
      (hrhoR.trans_le hRz)
  have hcont : ContinuousOn (fun z : ℂ => z ^ k • resolvent a z)
      (closedBall (0 : ℂ) Rbig \ ball 0 R) := by
    exact (continuous_pow k).continuousOn.smul
      ((resolvent_continuousOn a).mono hannulus)
  have hdiff : ∀ z ∈
      (ball (0 : ℂ) Rbig \ closedBall 0 R) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun w : ℂ => w ^ k • resolvent a w) z := by
    intro z hz
    have hRz : R < ‖z‖ := by
      have hznot : z ∉ closedBall (0 : ℂ) R := hz.1.2
      simpa [mem_closedBall, dist_zero_right, not_le] using hznot
    have hres :=
      mem_resolventSet_of_resolventPseudospectralRadius_lt_norm hrho
        (hrhoR.trans hRz)
    exact (differentiable_pow k z).smul (resolvent_differentiableAt a hres)
  have hcircle :
      (∮ z in C(0, Rbig), z ^ k • resolvent a z) =
        ∮ z in C(0, R), z ^ k • resolvent a z := by
    exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      hRpos hRle (s := (∅ : Set ℂ)) Set.countable_empty hcont hdiff
  calc
    a ^ k = (2 * Real.pi * I : ℂ)⁻¹ •
        ∮ z in C(0, Rbig), z ^ k • resolvent a z :=
      pow_eq_two_pi_I_inv_smul_circleIntegral a k haRbig
    _ = (2 * Real.pi * I : ℂ)⁻¹ •
        ∮ z in C(0, R), z ^ k • resolvent a z := by rw [hcircle]

/-- Equation (18.8) on an arbitrary circle of radius `R` strictly larger
than the exact resolvent pseudospectral radius `rho`:
`‖a^k‖ ≤ epsilon⁻¹ R^(k+1)`. -/
theorem norm_pow_le_inv_mul_pow_of_resolventPseudospectralRadius_lt
    (a : A) (k : ℕ) {epsilon rho R : ℝ}
    (hrho : IsGreatest (resolventPseudospectrumModulusSet epsilon a) rho)
    (hrhoR : rho < R) :
    ‖a ^ k‖ ≤ epsilon⁻¹ * R ^ (k + 1) := by
  have hRpos : 0 ≤ R :=
    ((resolventPseudospectralRadius_nonneg hrho).trans_lt hrhoR).le
  have hC : ∀ z ∈ sphere (0 : ℂ) R,
      ‖z ^ k • resolvent a z‖ ≤ R ^ k * epsilon⁻¹ := by
    intro z hz
    have hznorm : ‖z‖ = R := by
      simpa [mem_sphere, dist_zero_right] using hz
    have hreslt : ‖resolvent a z‖ < epsilon⁻¹ :=
      norm_resolvent_lt_inv_of_resolventPseudospectralRadius_lt_norm hrho
        (by simpa [hznorm] using hrhoR)
    calc
      ‖z ^ k • resolvent a z‖ = R ^ k * ‖resolvent a z‖ := by
        rw [norm_smul, norm_pow, hznorm]
      _ ≤ R ^ k * epsilon⁻¹ :=
        mul_le_mul_of_nonneg_left hreslt.le (pow_nonneg hRpos k)
  rw [pow_eq_two_pi_I_inv_smul_circleIntegral_of_resolventPseudospectralRadius_lt
    a k hrho hrhoR]
  have hML := norm_two_pi_I_inv_smul_circleIntegral_pow_smul_resolvent_le
    a 0 k hRpos hC
  calc
    ‖(2 * Real.pi * I : ℂ)⁻¹ •
        ∮ z in C(0, R), z ^ k • resolvent a z‖
        ≤ R * (R ^ k * epsilon⁻¹) := hML
    _ = epsilon⁻¹ * R ^ (k + 1) := by
      rw [pow_succ]
      ring
















































end ComplexBanachAlgebra

end NumStability
