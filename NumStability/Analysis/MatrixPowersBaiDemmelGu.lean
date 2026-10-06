/-
# Bai--Demmel--Gu matrix-power bound

This module formalizes the matrix-power estimate used in the proof of
Lemma 2 of Bai, Demmel, and Gu (1997) and quoted in Higham, *Accuracy and
Stability of Numerical Algorithms*, 2nd ed., Chapter 18.

For an element `a` of a complex Banach algebra whose spectral radius is less
than one, we define `d(a)` to be the attained minimum of

`  ‖resolvent a z‖⁻¹,   ‖z‖ = 1.`

For `CStarMatrix`, the norm in this definition is the operator norm.  The
standard finite-dimensional identification with
`min_{|z|=1} σ_min(zI-A)` uses an additional SVD/minimum-singular-value bridge;
this module does not claim that identity without such a theorem.  The proof
below does not assume the desired inner-circle resolvent estimate: it derives
it from the inverse-resolvent minimum by a Neumann perturbation, then combines
it with the repository's Dunford contour identity.
-/

import NumStability.Analysis.PseudospectralPowerBound
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace NumStability

open scoped Real Topology ComplexOrder
open Complex Metric Set Filter

section ComplexBanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The inverse resolvent norms on the unit circle. -/
def unitCircleResolventInvNormSet (a : A) : Set ℝ :=
  {d : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ d = ‖resolvent a z‖⁻¹}

/-- The unit-circle stability radius, defined without a supplied bound. -/
noncomputable def unitCircleStabilityRadius (a : A) : ℝ :=
  sInf (unitCircleResolventInvNormSet a)

omit [CompleteSpace A] in
lemma unitCircleResolventInvNormSet_eq_image (a : A) :
    unitCircleResolventInvNormSet a =
      (fun z : ℂ => ‖resolvent a z‖⁻¹) '' sphere (0 : ℂ) 1 := by
  ext d
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    simpa [mem_sphere, dist_zero_right] using hz
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    simpa [mem_sphere, dist_zero_right] using hz

omit [CompleteSpace A] in
lemma resolvent_ne_zero_of_mem_resolventSet [Nontrivial A]
    (a : A) {z : ℂ} (hz : z ∈ resolventSet ℂ a) :
    resolvent a z ≠ 0 := by
  intro hzero
  have hmul : (algebraMap ℂ A z - a) * resolvent a z = 1 :=
    Ring.mul_inverse_cancel _ hz
  rw [hzero, mul_zero] at hmul
  exact zero_ne_one hmul

omit [CompleteSpace A] in
/-- Spectral radius below one puts the whole unit circle in the resolvent set. -/
lemma unitSphere_subset_resolventSet_of_spectralRadius_lt_one [Nontrivial A]
    (a : A) (hrho : spectralRadius ℂ a < 1) :
    sphere (0 : ℂ) 1 ⊆ resolventSet ℂ a := by
  intro z hz
  apply spectrum.mem_resolventSet_of_spectralRadius_lt
  have hnorm : ‖z‖ = 1 := by
    simpa [mem_sphere, dist_zero_right] using hz
  have hnnorm : ‖z‖₊ = (1 : NNReal) := by
    ext
    simpa using hnorm
  simpa only [hnnorm, ENNReal.coe_one] using hrho

/-- The defining infimum is an attained minimum. -/
theorem unitCircleStabilityRadius_isLeast [Nontrivial A]
    (a : A) (hrho : spectralRadius ℂ a < 1) :
    IsLeast (unitCircleResolventInvNormSet a)
      (unitCircleStabilityRadius a) := by
  have hsub := unitSphere_subset_resolventSet_of_spectralRadius_lt_one a hrho
  have hnonzero : ∀ z ∈ sphere (0 : ℂ) 1, ‖resolvent a z‖ ≠ 0 := by
    intro z hz
    exact norm_ne_zero_iff.mpr
      (resolvent_ne_zero_of_mem_resolventSet a (hsub hz))
  have hcont : ContinuousOn (fun z : ℂ => ‖resolvent a z‖⁻¹)
      (sphere (0 : ℂ) 1) :=
    ((resolvent_continuousOn a).mono hsub).norm.inv₀ hnonzero
  have hcompact : IsCompact (unitCircleResolventInvNormSet a) := by
    rw [unitCircleResolventInvNormSet_eq_image]
    exact (isCompact_sphere (0 : ℂ) 1).image_of_continuousOn hcont
  have hnonempty : (unitCircleResolventInvNormSet a).Nonempty := by
    refine ⟨‖resolvent a 1‖⁻¹, 1, ?_, rfl⟩
    simp
  exact hcompact.isLeast_sInf hnonempty

/-- The unit-circle stability radius is strictly positive. -/
theorem unitCircleStabilityRadius_pos [Nontrivial A]
    (a : A) (hrho : spectralRadius ℂ a < 1) :
    0 < unitCircleStabilityRadius a := by
  have hleast := unitCircleStabilityRadius_isLeast a hrho
  rcases hleast.1 with ⟨z, hz, hEq⟩
  rw [hEq]
  have hzSphere : z ∈ sphere (0 : ℂ) 1 := by
    simpa [mem_sphere, dist_zero_right] using hz
  have hzRes := unitSphere_subset_resolventSet_of_spectralRadius_lt_one a hrho hzSphere
  exact inv_pos.mpr (norm_pos_iff.mpr
    (resolvent_ne_zero_of_mem_resolventSet a hzRes))

omit [NormedAlgebra ℂ A] in
/-- Quantitative Neumann bound for the totalized ring inverse. -/
lemma norm_ringInverse_one_sub_le [NormOneClass A]
    (t : A) (ht : ‖t‖ < 1) :
    ‖Ring.inverse (1 - t)‖ ≤ (1 - ‖t‖)⁻¹ := by
  rw [NormedRing.inverse_one_sub t ht]
  change ‖∑' n : ℕ, t ^ n‖ ≤ (1 - ‖t‖)⁻¹
  simpa using tsum_geometric_le_of_norm_lt_one t ht

/-- Resolvent perturbation from a unit-circle point to a nearby point.

This is the singular-value Lipschitz step in Bai--Demmel--Gu, proved directly
in a Banach algebra.  If `‖R(w)‖ ≤ d⁻¹` and `z` is within distance `d` of `w`,
then `z` is a resolvent point and
`‖R(z)‖ ≤ (d - ‖z-w‖)⁻¹`.
-/
theorem norm_resolvent_le_inv_sub_norm_sub [Nontrivial A]
    [NormOneClass A]
    (a : A) {w z : ℂ} (hw : w ∈ resolventSet ℂ a)
    {d : ℝ} (hd : 0 < d)
    (hRw : ‖resolvent a w‖ ≤ d⁻¹)
    (hzw : ‖z - w‖ < d) :
    z ∈ resolventSet ℂ a ∧
      ‖resolvent a z‖ ≤ (d - ‖z - w‖)⁻¹ := by
  let x : A := algebraMap ℂ A w - a
  let delta : A := algebraMap ℂ A (z - w)
  let q : A := -(delta * resolvent a w)
  have hdelta : ‖delta‖ = ‖z - w‖ := by
    simpa only [delta] using (norm_algebraMap' A (z - w))
  have hq_le : ‖q‖ ≤ ‖z - w‖ * d⁻¹ := by
    calc
      ‖q‖ = ‖delta * resolvent a w‖ := by simp [q]
      _ ≤ ‖delta‖ * ‖resolvent a w‖ := norm_mul_le _ _
      _ = ‖z - w‖ * ‖resolvent a w‖ := by rw [hdelta]
      _ ≤ ‖z - w‖ * d⁻¹ :=
        mul_le_mul_of_nonneg_left hRw (norm_nonneg _)
  have hratio_lt : ‖z - w‖ * d⁻¹ < 1 := by
    simpa [div_eq_mul_inv] using (div_lt_one hd).2 hzw
  have hq : ‖q‖ < 1 := hq_le.trans_lt hratio_lt
  have hB : IsUnit (1 - q) := isUnit_one_sub_of_norm_lt_one hq
  have hxRw : x * resolvent a w = 1 := by
    exact Ring.mul_inverse_cancel x hw
  have hRwx : resolvent a w * x = 1 := by
    exact Ring.inverse_mul_cancel x hw
  have hfactor : algebraMap ℂ A z - a = (1 - q) * x := by
    symm
    calc
      (1 - q) * x = x + delta := by
        rw [show 1 - q = 1 + delta * resolvent a w by simp [q]]
        rw [add_mul, one_mul, mul_assoc, hRwx, mul_one]
      _ = algebraMap ℂ A z - a := by
        simp only [x, delta, map_sub]
        abel
  have hz : z ∈ resolventSet ℂ a := by
    change IsUnit (algebraMap ℂ A z - a)
    rw [hfactor]
    exact hB.mul hw
  have hright : (algebraMap ℂ A z - a) *
      (resolvent a w * Ring.inverse (1 - q)) = 1 := by
    rw [hfactor]
    calc
      ((1 - q) * x) * (resolvent a w * Ring.inverse (1 - q)) =
          (1 - q) * (x * resolvent a w) * Ring.inverse (1 - q) := by
            simp only [mul_assoc]
      _ = (1 - q) * Ring.inverse (1 - q) := by rw [hxRw, mul_one]
      _ = 1 := Ring.mul_inverse_cancel _ hB
  have hinv : resolvent a z =
      resolvent a w * Ring.inverse (1 - q) := by
    unfold resolvent
    have hEq := (Ring.inverse_mul_eq_iff_eq_mul
      (algebraMap ℂ A z - a) 1
      (resolvent a w * Ring.inverse (1 - q)) hz).2 hright.symm
    simpa using hEq
  have hInvB : ‖Ring.inverse (1 - q)‖ ≤ (1 - ‖q‖)⁻¹ :=
    norm_ringInverse_one_sub_le q hq
  have hdenq : 0 < 1 - ‖q‖ := sub_pos.mpr hq
  have hdens : 0 < d - ‖z - w‖ := sub_pos.mpr hzw
  have hden_le : (d - ‖z - w‖) / d ≤ 1 - ‖q‖ := by
    have hd0 : d ≠ 0 := hd.ne'
    calc
      (d - ‖z - w‖) / d = 1 - ‖z - w‖ * d⁻¹ := by
        field_simp
      _ ≤ 1 - ‖q‖ := by linarith [hq_le]
  have hInvB' : ‖Ring.inverse (1 - q)‖ ≤
      ((d - ‖z - w‖) / d)⁻¹ := by
    exact hInvB.trans (inv_anti₀ (div_pos hdens hd) hden_le)
  refine ⟨hz, ?_⟩
  rw [hinv]
  calc
    ‖resolvent a w * Ring.inverse (1 - q)‖ ≤
        ‖resolvent a w‖ * ‖Ring.inverse (1 - q)‖ := norm_mul_le _ _
    _ ≤ d⁻¹ * (((d - ‖z - w‖) / d)⁻¹) :=
      mul_le_mul hRw hInvB' (norm_nonneg _) (inv_nonneg.mpr hd.le)
    _ = (d - ‖z - w‖)⁻¹ := by
      field_simp

/-- The defining minimum gives the uniform unit-circle resolvent bound. -/
theorem norm_resolvent_unitCircle_le_stabilityRadius_inv [Nontrivial A]
    [NormOneClass A]
    (a : A) (hrho : spectralRadius ℂ a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖resolvent a z‖ ≤ (unitCircleStabilityRadius a)⁻¹ := by
  let d := unitCircleStabilityRadius a
  have hd : 0 < d := unitCircleStabilityRadius_pos a hrho
  have hzSphere : z ∈ sphere (0 : ℂ) 1 := by
    simpa [mem_sphere, dist_zero_right] using hz
  have hzRes := unitSphere_subset_resolventSet_of_spectralRadius_lt_one a hrho hzSphere
  have hRpos : 0 < ‖resolvent a z‖ := norm_pos_iff.mpr
    (resolvent_ne_zero_of_mem_resolventSet a hzRes)
  have hdle : d ≤ ‖resolvent a z‖⁻¹ :=
    (unitCircleStabilityRadius_isLeast a hrho).2 ⟨z, hz, rfl⟩
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hd).2
  calc
    ‖resolvent a z‖ * d ≤
        ‖resolvent a z‖ * ‖resolvent a z‖⁻¹ :=
      mul_le_mul_of_nonneg_left hdle hRpos.le
    _ = 1 := mul_inv_cancel₀ hRpos.ne'

/-- Bai--Demmel--Gu's inner-circle resolvent estimate.  It is derived from the
unit-circle minimum by radial Neumann perturbation. -/
theorem norm_resolvent_on_sphere_le_baiDemmelGu [Nontrivial A]
    [NormOneClass A]
    (a : A) (hrho : spectralRadius ℂ a < 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hrd : 1 - unitCircleStabilityRadius a < r)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) r) :
    ‖resolvent a z‖ ≤
      (unitCircleStabilityRadius a - 1 + r)⁻¹ := by
  let d := unitCircleStabilityRadius a
  let w : ℂ := ((r : ℂ)⁻¹) * z
  have hzNorm : ‖z‖ = r := by
    simpa [mem_sphere, dist_zero_right] using hz
  have hr0 : r ≠ 0 := hr.ne'
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr, hzNorm, inv_mul_cancel₀ hr0]
  have hwSphere : w ∈ sphere (0 : ℂ) 1 := by
    simpa [mem_sphere, dist_zero_right] using hwNorm
  have hwRes := unitSphere_subset_resolventSet_of_spectralRadius_lt_one a hrho hwSphere
  have hRw := norm_resolvent_unitCircle_le_stabilityRadius_inv a hrho hwNorm
  have hz_eq : z = (r : ℂ) * w := by
    dsimp [w]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr0), one_mul]
  have hzwNorm : ‖z - w‖ = 1 - r := by
    rw [hz_eq]
    have hsub : (r : ℂ) * w - w = ((r - 1 : ℝ) : ℂ) * w := by
      push_cast
      ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, hwNorm, mul_one]
    rw [abs_of_nonpos (sub_nonpos.mpr hr1)]
    ring
  have hd : 0 < d := unitCircleStabilityRadius_pos a hrho
  have hzw : ‖z - w‖ < d := by
    rw [hzwNorm]
    dsimp [d]
    linarith
  have hpert := norm_resolvent_le_inv_sub_norm_sub a hwRes hd hRw hzw
  calc
    ‖resolvent a z‖ ≤ (d - (1 - r))⁻¹ := by
      simpa only [hzwNorm] using hpert.2
    _ = (unitCircleStabilityRadius a - 1 + r)⁻¹ := by
      congr 1
      dsimp [d]
      ring

/-- Dunford's power identity on any circle outside the spectral radius. -/
theorem pow_eq_two_pi_I_inv_smul_circleIntegral_of_spectralRadius_toReal_lt
    [Nontrivial A]
    (a : A) (k : ℕ) {r : ℝ}
    (hrho : spectralRadius ℂ a < 1)
    (hrhor : (spectralRadius ℂ a).toReal < r) :
    a ^ k = (2 * Real.pi * I : ℂ)⁻¹ •
      ∮ z in C(0, r), z ^ k • resolvent a z := by
  let Rbig : ℝ := max r (‖a‖ + 1)
  have hrpos : 0 < r := (ENNReal.toReal_nonneg.trans_lt hrhor)
  have hrle : r ≤ Rbig := le_max_left _ _
  have haRbig : ‖a‖ < Rbig := by
    exact (lt_add_one ‖a‖).trans_le (le_max_right _ _)
  have hres_of_norm {z : ℂ} (hz : r ≤ ‖z‖) :
      z ∈ resolventSet ℂ a := by
    apply spectrum.mem_resolventSet_of_spectralRadius_lt
    apply (ENNReal.toReal_lt_toReal (ne_top_of_lt hrho)
      ENNReal.coe_ne_top).1
    simpa using hrhor.trans_le hz
  have hannulus : closedBall (0 : ℂ) Rbig \ ball 0 r ⊆
      resolventSet ℂ a := by
    intro z hz
    apply hres_of_norm
    have hznot : z ∉ ball (0 : ℂ) r := hz.2
    simpa [mem_ball, dist_zero_right, not_lt] using hznot
  have hcont : ContinuousOn (fun z : ℂ => z ^ k • resolvent a z)
      (closedBall (0 : ℂ) Rbig \ ball 0 r) := by
    exact (continuous_pow k).continuousOn.smul
      ((resolvent_continuousOn a).mono hannulus)
  have hdiff : ∀ z ∈
      (ball (0 : ℂ) Rbig \ closedBall 0 r) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun w : ℂ => w ^ k • resolvent a w) z := by
    intro z hz
    have hrz : r < ‖z‖ := by
      have hznot : z ∉ closedBall (0 : ℂ) r := hz.1.2
      simpa [mem_closedBall, dist_zero_right, not_le] using hznot
    exact (differentiable_pow k z).smul
      (resolvent_differentiableAt a (hres_of_norm hrz.le))
  have hcircle :
      (∮ z in C(0, Rbig), z ^ k • resolvent a z) =
        ∮ z in C(0, r), z ^ k • resolvent a z := by
    exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      hrpos hrle (s := (∅ : Set ℂ)) Set.countable_empty hcont hdiff
  calc
    a ^ k = (2 * Real.pi * I : ℂ)⁻¹ •
        ∮ z in C(0, Rbig), z ^ k • resolvent a z :=
      pow_eq_two_pi_I_inv_smul_circleIntegral a k haRbig
    _ = (2 * Real.pi * I : ℂ)⁻¹ •
        ∮ z in C(0, r), z ^ k • resolvent a z := by rw [hcircle]

/-- The unoptimized Bai--Demmel--Gu contour estimate

`  ‖a^m‖ ≤ r^(m+1) / (d(a) - 1 + r)`

for every contour radius strictly larger than both the spectral radius and
`1-d(a)`, with `r ≤ 1`.
-/
theorem norm_pow_le_baiDemmelGu_contour [Nontrivial A] [NormOneClass A]
    (a : A) (hrho : spectralRadius ℂ a < 1)
    (m : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hrhor : (spectralRadius ℂ a).toReal < r)
    (hrd : 1 - unitCircleStabilityRadius a < r) :
    ‖a ^ m‖ ≤ r ^ (m + 1) *
      (unitCircleStabilityRadius a - 1 + r)⁻¹ := by
  have hden : 0 < unitCircleStabilityRadius a - 1 + r := by
    linarith
  have hC : ∀ z ∈ sphere (0 : ℂ) r,
      ‖z ^ m • resolvent a z‖ ≤
        r ^ m * (unitCircleStabilityRadius a - 1 + r)⁻¹ := by
    intro z hz
    have hzNorm : ‖z‖ = r := by
      simpa [mem_sphere, dist_zero_right] using hz
    have hR := norm_resolvent_on_sphere_le_baiDemmelGu
      a hrho hr hr1 hrd hz
    rw [norm_smul, norm_pow, hzNorm]
    exact mul_le_mul_of_nonneg_left hR (pow_nonneg hr.le m)
  rw [pow_eq_two_pi_I_inv_smul_circleIntegral_of_spectralRadius_toReal_lt
    a m hrho hrhor]
  have hML := norm_two_pi_I_inv_smul_circleIntegral_pow_smul_resolvent_le
    a 0 m hr.le hC
  calc
    ‖(2 * Real.pi * I : ℂ)⁻¹ •
        ∮ z in C(0, r), z ^ m • resolvent a z‖
        ≤ r * (r ^ m *
          (unitCircleStabilityRadius a - 1 + r)⁻¹) := hML
    _ = r ^ (m + 1) *
        (unitCircleStabilityRadius a - 1 + r)⁻¹ := by
      rw [pow_succ]
      ring

/-- The stability radius cannot exceed the radial gap from the attained
spectral-radius point to the unit circle.  This is the fact that guarantees
the optimizing contour remains outside the spectrum. -/
theorem unitCircleStabilityRadius_le_one_sub_spectralRadius_toReal
    [Nontrivial A] [NormOneClass A]
    (a : A) (hrho : spectralRadius ℂ a < 1) :
    unitCircleStabilityRadius a ≤ 1 - (spectralRadius ℂ a).toReal := by
  let rho : ℝ := (spectralRadius ℂ a).toReal
  obtain ⟨lam, hlamSpec, hlamRadius⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius a
  have hrhoTop : spectralRadius ℂ a ≠ ⊤ := ne_top_of_lt hrho
  have hlamNorm : ‖lam‖ = rho := by
    have h := congrArg ENNReal.toReal hlamRadius
    simpa [rho] using h
  have hrhoReal : rho < 1 := by
    have h := (ENNReal.toReal_lt_toReal hrhoTop ENNReal.one_ne_top).2 hrho
    simpa [rho] using h
  have hleast := unitCircleStabilityRadius_isLeast a hrho
  by_cases hlam0 : lam = 0
  · subst lam
    have hrho0 : rho = 0 := by simpa using hlamNorm.symm
    have hzSphere : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
    have hzRes := unitSphere_subset_resolventSet_of_spectralRadius_lt_one
      a hrho hzSphere
    have hRne := resolvent_ne_zero_of_mem_resolventSet a hzRes
    have hdist := dist_ge_one_div_norm_resolvent
      a (0 : ℂ) (1 : ℂ) hlamSpec hzRes hRne
    calc
      unitCircleStabilityRadius a ≤ ‖resolvent a 1‖⁻¹ :=
        hleast.2 ⟨1, by simp, rfl⟩
      _ ≤ dist (1 : ℂ) 0 := by simpa [one_div] using hdist
      _ = 1 - rho := by simp [hrho0]
      _ = 1 - (spectralRadius ℂ a).toReal := rfl
  · have hlamPos : 0 < ‖lam‖ := norm_pos_iff.mpr hlam0
    let z : ℂ := ((‖lam‖ : ℂ)⁻¹) * lam
    have hzNorm : ‖z‖ = 1 := by
      dsimp [z]
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hlamPos, inv_mul_cancel₀ hlamPos.ne']
    have hzSphere : z ∈ sphere (0 : ℂ) 1 := by
      simpa [mem_sphere, dist_zero_right] using hzNorm
    have hzRes := unitSphere_subset_resolventSet_of_spectralRadius_lt_one
      a hrho hzSphere
    have hRne := resolvent_ne_zero_of_mem_resolventSet a hzRes
    have hlamLt : ‖lam‖ < 1 := by simpa [hlamNorm] using hrhoReal
    have hinvGe : 1 ≤ ‖lam‖⁻¹ :=
      (one_le_inv₀ hlamPos).2 hlamLt.le
    have hsub : z - lam = (((‖lam‖⁻¹ - 1 : ℝ) : ℂ) * lam) := by
      dsimp [z]
      push_cast
      ring
    have hdistEq : dist z lam = 1 - rho := by
      rw [dist_eq_norm, hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hinvGe)]
      have hscalar : (‖lam‖⁻¹ - 1) * ‖lam‖ = 1 - ‖lam‖ := by
        field_simp
      rw [hscalar, hlamNorm]
    have hdist := dist_ge_one_div_norm_resolvent
      a lam z hlamSpec hzRes hRne
    calc
      unitCircleStabilityRadius a ≤ ‖resolvent a z‖⁻¹ :=
        hleast.2 ⟨z, hzNorm, rfl⟩
      _ ≤ dist z lam := by simpa [one_div] using hdist
      _ = 1 - rho := hdistEq
      _ = 1 - (spectralRadius ℂ a).toReal := rfl

/-- The constant `α_m = (1 + 1/m)^(m+1)` in Bai--Demmel--Gu. -/
noncomputable def baiDemmelGuAlpha (m : ℕ) : ℝ :=
  (1 + 1 / (m : ℝ)) ^ (m + 1)

/-- The second branch of the Bai--Demmel--Gu power bound.  In fact the
`1/d(a)` estimate holds for every power; the displayed threshold records the
source's branch split. -/
theorem higham18_baiDemmelGu_smallPower [Nontrivial A] [NormOneClass A]
    (a : A) (hrho : spectralRadius ℂ a < 1) (m : ℕ)
    (_hm : (m : ℝ) ≤
      (1 - unitCircleStabilityRadius a) / unitCircleStabilityRadius a) :
    ‖a ^ m‖ ≤ (unitCircleStabilityRadius a)⁻¹ := by
  have hd := unitCircleStabilityRadius_pos a hrho
  have hrhoReal : (spectralRadius ℂ a).toReal < 1 := by
    exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hrho)
      ENNReal.one_ne_top).2 hrho
  have hcontour := norm_pow_le_baiDemmelGu_contour
    a hrho m (r := 1) one_pos le_rfl hrhoReal (by linarith)
  simpa using hcontour

/-- Boundary case needed by the optimized branch: if the unit-circle
stability radius is one, every positive power vanishes.  This follows by
letting the valid contour radius tend to zero; no semisimplicity assumption is
used. -/
theorem pow_eq_zero_of_unitCircleStabilityRadius_eq_one
    [Nontrivial A] [NormOneClass A]
    (a : A) (hrho : spectralRadius ℂ a < 1)
    (m : ℕ) (hm : 0 < m)
    (hd1 : unitCircleStabilityRadius a = 1) :
    a ^ m = 0 := by
  have hgap := unitCircleStabilityRadius_le_one_sub_spectralRadius_toReal
    a hrho
  have hrho0 : (spectralRadius ℂ a).toReal = 0 := by
    have hrnonneg : 0 ≤ (spectralRadius ℂ a).toReal := ENNReal.toReal_nonneg
    rw [hd1] at hgap
    linarith
  have hpoint : ∀ r : ℝ, 0 < r → r < 1 → ‖a ^ m‖ ≤ r ^ m := by
    intro r hr hr1
    have hcontour := norm_pow_le_baiDemmelGu_contour
      a hrho m hr hr1.le (by simpa [hrho0] using hr)
      (by rw [hd1]; linarith)
    calc
      ‖a ^ m‖ ≤ r ^ (m + 1) *
          (unitCircleStabilityRadius a - 1 + r)⁻¹ := hcontour
      _ = r ^ m := by
        rw [hd1]
        have hden : (1 : ℝ) - 1 + r = r := by ring
        rw [hden]
        rw [pow_succ]
        field_simp
  have htend : Tendsto (fun r : ℝ => r ^ m)
      (nhdsWithin 0 (Ioo (0 : ℝ) 1)) (nhds 0) := by
    have h : Tendsto (fun r : ℝ => r ^ m) (nhds (0 : ℝ))
        (nhds ((0 : ℝ) ^ m)) :=
      (continuousAt_id.pow m).tendsto
    simpa [Nat.ne_of_gt hm] using h.mono_left inf_le_left
  have hevent : ∀ᶠ r in nhdsWithin 0 (Ioo (0 : ℝ) 1),
      ‖a ^ m‖ ≤ r ^ m := by
    filter_upwards [self_mem_nhdsWithin] with r hrange
    exact hpoint r hrange.1 hrange.2
  letI : NeBot (nhdsWithin (0 : ℝ) (Ioo 0 1)) :=
    left_nhdsWithin_Ioo_neBot (by norm_num)
  have hle0 : ‖a ^ m‖ ≤ 0 := ge_of_tendsto htend hevent
  exact norm_eq_zero.mp (le_antisymm hle0 (norm_nonneg _))

/-- The optimized, large-power branch of Bai--Demmel--Gu's bound. -/
theorem higham18_baiDemmelGu_largePower [Nontrivial A] [NormOneClass A]
    (a : A) (hrho : spectralRadius ℂ a < 1) (m : ℕ)
    (hm : (1 - unitCircleStabilityRadius a) /
        unitCircleStabilityRadius a < (m : ℝ)) :
    ‖a ^ m‖ ≤ baiDemmelGuAlpha m * (m : ℝ) *
      (1 - unitCircleStabilityRadius a) ^ m := by
  let d : ℝ := unitCircleStabilityRadius a
  let M : ℝ := (m : ℝ)
  let rho : ℝ := (spectralRadius ℂ a).toReal
  have hd : 0 < d := unitCircleStabilityRadius_pos a hrho
  have hgap := unitCircleStabilityRadius_le_one_sub_spectralRadius_toReal
    a hrho
  have hrhoNonneg : 0 ≤ rho := ENNReal.toReal_nonneg
  have hd1 : d ≤ 1 := by
    dsimp [d, rho] at hgap ⊢
    linarith
  have hcritNonneg : 0 ≤ (1 - d) / d :=
    div_nonneg (sub_nonneg.mpr hd1) hd.le
  have hm' : (1 - d) / d < M := by simpa [d, M] using hm
  have hMpos : 0 < M := hcritNonneg.trans_lt hm'
  have hmNat : 0 < m := by
    have hmR : (0 : ℝ) < (m : ℝ) := by simpa [M] using hMpos
    exact_mod_cast hmR
  by_cases hdEq : d = 1
  · have hpow : a ^ m = 0 :=
      pow_eq_zero_of_unitCircleStabilityRadius_eq_one a hrho m hmNat
        (by simpa [d] using hdEq)
    rw [hpow, norm_zero]
    simp [d, hdEq, Nat.ne_of_gt hmNat]
  · have hdlt : d < 1 := lt_of_le_of_ne hd1 hdEq
    have hgapPos : 0 < 1 - d := sub_pos.mpr hdlt
    have hcrit : 1 - d < M * d :=
      (div_lt_iff₀ hd).1 hm'
    let rstar : ℝ := (1 + 1 / M) * (1 - d)
    have hrstar : 0 < rstar := by
      dsimp [rstar]
      exact mul_pos (by positivity) hgapPos
    have hrd : 1 - d < rstar := by
      dsimp [rstar]
      have hsmall : 0 < (1 / M) * (1 - d) :=
        mul_pos (one_div_pos.mpr hMpos) hgapPos
      nlinarith
    have hrform : rstar = ((M + 1) * (1 - d)) / M := by
      dsimp [rstar]
      field_simp
    have hrstar1 : rstar ≤ 1 := by
      rw [hrform]
      apply (div_le_one hMpos).2
      nlinarith
    have hrhole : rho ≤ 1 - d := by
      dsimp [d, rho] at hgap ⊢
      linarith
    have hrhor : (spectralRadius ℂ a).toReal < rstar := by
      dsimp [rho] at hrhole
      exact hrhole.trans_lt hrd
    have hcontour := norm_pow_le_baiDemmelGu_contour
      a hrho m hrstar hrstar1 hrhor (by simpa [d] using hrd)
    have hdenEq : d - 1 + rstar = (1 - d) / M := by
      dsimp [rstar]
      field_simp
      ring
    calc
      ‖a ^ m‖ ≤ rstar ^ (m + 1) *
          (unitCircleStabilityRadius a - 1 + rstar)⁻¹ := hcontour
      _ = rstar ^ (m + 1) * (d - 1 + rstar)⁻¹ := by rfl
      _ = baiDemmelGuAlpha m * M * (1 - d) ^ m := by
        rw [hdenEq]
        dsimp [rstar, baiDemmelGuAlpha, M]
        rw [mul_pow, inv_div, pow_succ (1 - d) m]
        field_simp
      _ = baiDemmelGuAlpha m * (m : ℝ) *
          (1 - unitCircleStabilityRadius a) ^ m := by rfl

/-- **Bai--Demmel--Gu matrix-power bound quoted in Higham Chapter 18.**

Both source branches are packaged in one assumption-free endpoint.  The only
matrix datum in the conclusion is the stability radius defined above as the
actual attained unit-circle resolvent minimum.
-/
theorem higham18_baiDemmelGu_matrixPowerBound
    [Nontrivial A] [NormOneClass A]
    (a : A) (hrho : spectralRadius ℂ a < 1) (m : ℕ) :
    (((1 - unitCircleStabilityRadius a) /
          unitCircleStabilityRadius a < (m : ℝ)) →
      ‖a ^ m‖ ≤ baiDemmelGuAlpha m * (m : ℝ) *
        (1 - unitCircleStabilityRadius a) ^ m) ∧
    (((m : ℝ) ≤ (1 - unitCircleStabilityRadius a) /
          unitCircleStabilityRadius a) →
      ‖a ^ m‖ ≤ (unitCircleStabilityRadius a)⁻¹) := by
  exact ⟨higham18_baiDemmelGu_largePower a hrho m,
    higham18_baiDemmelGu_smallPower a hrho m⟩

end ComplexBanachAlgebra

section CStarMatrixSpecialization

/-- For finite complex `CStarMatrix`, `unitCircleStabilityRadius` is exactly the
attained minimum of the inverse **operator** norms of the unit-circle
resolvents.  This is the matrix-norm bridge used by the power bound.  No
unformalized identification with minimum singular values is asserted here. -/
theorem cstarMatrix_unitCircleStabilityRadius_isLeast
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : CStarMatrix ι ι ℂ) (hrho : spectralRadius ℂ a < 1) :
    IsLeast {d : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧ d = ‖resolvent a z‖⁻¹}
      (unitCircleStabilityRadius a) := by
  exact unitCircleStabilityRadius_isLeast a hrho

end CStarMatrixSpecialization

section AlphaBounds

/-- The elementary upper bound `α_m ≤ 4` stated by Bai--Demmel--Gu. -/
theorem baiDemmelGuAlpha_le_four (m : ℕ) (hm : 1 ≤ m) :
    baiDemmelGuAlpha m ≤ 4 := by
  by_cases hm1 : m = 1
  · subst m
    unfold baiDemmelGuAlpha
    norm_num [div_self]
    exact (show ((1 + 1 : ℝ) ^ 2) = 4 by ring).le
  by_cases hm2 : m = 2
  · subst m
    norm_num [baiDemmelGuAlpha]
  have hm3 : 3 ≤ m := by omega
  have hMpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hMge : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
  let base : ℝ := 1 + 1 / (m : ℝ)
  have hbasePos : 0 < base := by
    dsimp [base]
    positivity
  have hbaseExp : base ≤ Real.exp (1 / (m : ℝ)) := by
    dsimp [base]
    have h := Real.add_one_le_exp (1 / (m : ℝ))
    linarith
  have hpow : base ^ m ≤ Real.exp 1 := by
    calc
      base ^ m ≤ Real.exp (1 / (m : ℝ)) ^ m :=
        pow_le_pow_left₀ hbasePos.le hbaseExp m
      _ = Real.exp ((m : ℝ) * (1 / (m : ℝ))) :=
        (Real.exp_nat_mul _ m).symm
      _ = Real.exp 1 := by
        rw [mul_one_div, div_self hMpos.ne']
  have hbaseFourThirds : base ≤ (4 / 3 : ℝ) := by
    have hinv : 1 / (m : ℝ) ≤ (1 / 3 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hMge
    dsimp [base]
    linarith
  have hexpThree : Real.exp 1 < 3 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  rw [baiDemmelGuAlpha, pow_succ]
  change base ^ m * base ≤ 4
  calc
    base ^ m * base ≤ Real.exp 1 * base :=
      mul_le_mul_of_nonneg_right hpow hbasePos.le
    _ ≤ 3 * base := (mul_lt_mul_of_pos_right hexpThree hbasePos).le
    _ ≤ 3 * (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hbaseFourThirds (by norm_num)
    _ = 4 := by norm_num

/-- The elementary lower bound `exp 1 ≤ α_m` stated by Bai--Demmel--Gu. -/
theorem exp_one_le_baiDemmelGuAlpha (m : ℕ) (hm : 1 ≤ m) :
    Real.exp 1 ≤ baiDemmelGuAlpha m := by
  let M : ℝ := (m : ℝ)
  let b : ℝ := 1 + 1 / M
  have hMpos : 0 < M := by
    dsimp [M]
    exact_mod_cast hm
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hlog0 := Real.one_sub_inv_le_log_of_pos hb
  have hid : 1 - b⁻¹ = 1 / (M + 1) := by
    dsimp [b]
    field_simp
    ring
  have hlog : 1 / (M + 1) ≤ Real.log b := by
    rwa [hid] at hlog0
  have hM1pos : 0 < M + 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog hM1pos.le
  have hleft : (M + 1) * (1 / (M + 1)) = 1 := by
    field_simp
  rw [hleft] at hmul
  have hexp := Real.exp_le_exp.mpr hmul
  calc
    Real.exp 1 ≤ Real.exp ((M + 1) * Real.log b) := hexp
    _ = Real.exp (Real.log b) ^ (m + 1) := by
      have hcoeff : M + 1 = ((m + 1 : ℕ) : ℝ) := by
        dsimp [M]
        push_cast
        rfl
      rw [hcoeff]
      exact Real.exp_nat_mul _ _
    _ = b ^ (m + 1) := by rw [Real.exp_log hb]
    _ = baiDemmelGuAlpha m := by rfl

end AlphaBounds

end NumStability
