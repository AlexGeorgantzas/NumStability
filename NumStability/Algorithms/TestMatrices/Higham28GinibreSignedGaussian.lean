/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedScalar
import NumStability.Algorithms.TestMatrices.Higham28GaussianOrthogonal

/-! # Higham Chapter 28: the ordered signed Gaussian integral

This file evaluates the two scalar Gaussian coordinates left by the signed
two-incidence formula.  The orthogonal change of variables

`u = (s - t) / sqrt 2`, `x = (s + t) / sqrt 2`

sends the ordered region `u < x` to the positive half-line `0 < t`.  Gaussian
orthogonal invariance then reduces the answer to the boundary and Gamma
integrals proved in `Higham28GinibreSignedScalar`.
-/

namespace NumStability

open Matrix MeasureTheory ProbabilityTheory Set Real Filter
open scoped BigOperators

noncomputable section

/-! ## The orthogonal change of coordinates -/

/-- The coefficient `1 / sqrt 2`, written in a form convenient for algebra. -/
noncomputable def ginibreSignedGaussianRotationScale : ℝ := Real.sqrt 2 / 2

theorem ginibreSignedGaussianRotationScale_sq :
    ginibreSignedGaussianRotationScale ^ 2 = 1 / 2 := by
  unfold ginibreSignedGaussianRotationScale
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  nlinarith

theorem ginibreSignedGaussianRotationScale_pos :
    0 < ginibreSignedGaussianRotationScale := by
  unfold ginibreSignedGaussianRotationScale
  positivity

/-- The inverse `45°` rotation, taking `(s,t)` to the original `(u,x)`
coordinates. -/
noncomputable def ginibreSignedGaussianRotationMatrix :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![ginibreSignedGaussianRotationScale, -ginibreSignedGaussianRotationScale;
     ginibreSignedGaussianRotationScale, ginibreSignedGaussianRotationScale]

noncomputable def ginibreSignedGaussianRotationOrthogonal :
    Matrix.orthogonalGroup (Fin 2) ℝ :=
  ⟨ginibreSignedGaussianRotationMatrix, by
    have hs := ginibreSignedGaussianRotationScale_sq
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ginibreSignedGaussianRotationMatrix, Matrix.mul_apply,
        Fin.sum_univ_succ] <;>
      nlinarith⟩

/-- The inverse `45°` rotation as a measurable equivalence of pairs. -/
noncomputable def ginibreSignedGaussianRotation : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toEquiv :=
    { toFun := fun p =>
        (ginibreSignedGaussianRotationScale * (p.1 - p.2),
          ginibreSignedGaussianRotationScale * (p.1 + p.2))
      invFun := fun p =>
        (ginibreSignedGaussianRotationScale * (p.1 + p.2),
          ginibreSignedGaussianRotationScale * (-p.1 + p.2))
      left_inv := by
        intro p
        have hs := ginibreSignedGaussianRotationScale_sq
        apply Prod.ext
        · dsimp
          calc
            ginibreSignedGaussianRotationScale *
                (ginibreSignedGaussianRotationScale * (p.1 - p.2) +
                  ginibreSignedGaussianRotationScale * (p.1 + p.2)) =
                2 * ginibreSignedGaussianRotationScale ^ 2 * p.1 := by ring
            _ = p.1 := by rw [hs]; ring
        · dsimp
          calc
            ginibreSignedGaussianRotationScale *
                (-(ginibreSignedGaussianRotationScale * (p.1 - p.2)) +
                  ginibreSignedGaussianRotationScale * (p.1 + p.2)) =
                2 * ginibreSignedGaussianRotationScale ^ 2 * p.2 := by ring
            _ = p.2 := by rw [hs]; ring
      right_inv := by
        intro p
        have hs := ginibreSignedGaussianRotationScale_sq
        apply Prod.ext
        · dsimp
          calc
            ginibreSignedGaussianRotationScale *
                (ginibreSignedGaussianRotationScale * (p.1 + p.2) -
                  ginibreSignedGaussianRotationScale * (-p.1 + p.2)) =
                2 * ginibreSignedGaussianRotationScale ^ 2 * p.1 := by ring
            _ = p.1 := by rw [hs]; ring
        · dsimp
          calc
            ginibreSignedGaussianRotationScale *
                (ginibreSignedGaussianRotationScale * (p.1 + p.2) +
                  ginibreSignedGaussianRotationScale * (-p.1 + p.2)) =
                2 * ginibreSignedGaussianRotationScale ^ 2 * p.2 := by ring
            _ = p.2 := by rw [hs]; ring }
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

@[simp] theorem ginibreSignedGaussianRotation_apply (p : ℝ × ℝ) :
    ginibreSignedGaussianRotation p =
      (ginibreSignedGaussianRotationScale * (p.1 - p.2),
        ginibreSignedGaussianRotationScale * (p.1 + p.2)) := rfl

@[simp] theorem ginibreSignedGaussianRotation_symm_apply (p : ℝ × ℝ) :
    ginibreSignedGaussianRotation.symm p =
      (ginibreSignedGaussianRotationScale * (p.1 + p.2),
        ginibreSignedGaussianRotationScale * (-p.1 + p.2)) := rfl

/-- The pair rotation preserves two independent standard real Gaussians. -/
theorem measurePreserving_ginibreSignedGaussianRotation :
    MeasurePreserving ginibreSignedGaussianRotation
      ((gaussianReal 0 1).prod (gaussianReal 0 1))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let e : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.finTwoArrow
  let T : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x =>
    Matrix.mulVec ginibreSignedGaussianRotationMatrix x
  have he : MeasurePreserving e (standardGaussianVectorMeasure 2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa [standardGaussianVectorMeasure, e] using
      measurePreserving_finTwoArrow (gaussianReal 0 1)
  have hT : MeasurePreserving T (standardGaussianVectorMeasure 2)
      (standardGaussianVectorMeasure 2) :=
    ⟨by fun_prop,
      standardGaussianVectorMeasure_map_orthogonalGroup 2
        ginibreSignedGaussianRotationOrthogonal⟩
  have h := he.comp (hT.comp (MeasurePreserving.symm e he))
  change MeasurePreserving (e ∘ T ∘ e.symm)
    ((gaussianReal 0 1).prod (gaussianReal 0 1))
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) at h
  have hfun : (e ∘ T ∘ e.symm) = ginibreSignedGaussianRotation := by
    funext p
    ext <;>
      simp [e, T, ginibreSignedGaussianRotation,
        ginibreSignedGaussianRotationMatrix, Function.comp_def,
        dotProduct, Fin.sum_univ_succ,
        MeasurableEquiv.finTwoArrow_apply] <;>
      ring
  rw [hfun] at h
  exact h

/-! ## Integrability of the ordered polynomial -/

/-- Every polynomial moment is integrable under a standard real Gaussian. -/
theorem integrable_standardGaussian_pow_all (r : ℕ) :
    Integrable (fun x : ℝ => x ^ r) (gaussianReal 0 1) := by
  apply integrable_pow_of_mem_interior_integrableExpSet
  simp

/-- A signed product monomial has an integrable two-Gaussian envelope. -/
theorem integrable_ginibreSignedGaussianMonomial (r : ℕ) :
    Integrable (fun p : ℝ × ℝ =>
      (p.1 - p.2) * (p.1 * p.2) ^ r)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hleft := (integrable_standardGaussian_pow_all (r + 1)).mul_prod
    (integrable_standardGaussian_pow_all r)
  have hright := (integrable_standardGaussian_pow_all r).mul_prod
    (integrable_standardGaussian_pow_all (r + 1))
  apply (hleft.sub hright).congr
  filter_upwards with p
  rw [mul_pow]
  simp only [Pi.sub_apply]
  ring

/-- The polynomial integrand occurring in the ordered Gaussian moment. -/
def ginibreOrderedGaussianSignedIntegrand (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  (p.1 - p.2) *
    ((m : ℝ) * (p.1 * p.2) ^ (m - 1) + (p.1 * p.2) ^ m)

theorem integrable_ginibreOrderedGaussianSignedIntegrand (m : ℕ) :
    Integrable (ginibreOrderedGaussianSignedIntegrand m)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hm1 := (integrable_ginibreSignedGaussianMonomial (m - 1)).const_mul (m : ℝ)
  have hm := integrable_ginibreSignedGaussianMonomial m
  apply (hm1.add hm).congr
  filter_upwards with p
  simp only [ginibreOrderedGaussianSignedIntegrand, Pi.add_apply]
  ring

/-- The ordered-root region for the two scalar incidence coordinates. -/
def ginibreOrderedGaussianRegion : Set (ℝ × ℝ) := {p | p.1 < p.2}

theorem measurableSet_ginibreOrderedGaussianRegion :
    MeasurableSet ginibreOrderedGaussianRegion := by
  exact measurableSet_lt measurable_fst measurable_snd

/-- The exact scalar quantity left after applying the signed incidence
formula twice. -/
noncomputable def ginibreOrderedGaussianSignedMoment (m : ℕ) : ℝ :=
  ∫ p : ℝ × ℝ in ginibreOrderedGaussianRegion,
    ginibreOrderedGaussianSignedIntegrand m p
    ∂((gaussianReal 0 1).prod (gaussianReal 0 1))

/-! ## Rotation to the half-plane and evaluation -/

/-- The transformed polynomial before inserting the Gaussian densities. -/
def ginibreSignedGaussianRotatedIntegrand (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  (-Real.sqrt 2 * p.2) *
    ((m : ℝ) * (p.1 ^ 2 / 2 - p.2 ^ 2 / 2) ^ (m - 1) +
      (p.1 ^ 2 / 2 - p.2 ^ 2 / 2) ^ m)

def ginibreSignedGaussianPositiveRegion : Set (ℝ × ℝ) :=
  {p | 0 < p.2}

theorem measurableSet_ginibreSignedGaussianPositiveRegion :
    MeasurableSet ginibreSignedGaussianPositiveRegion := by
  exact measurableSet_lt measurable_const measurable_snd

theorem ginibreSignedGaussianRotation_mem_ordered_iff (p : ℝ × ℝ) :
    ginibreSignedGaussianRotation p ∈ ginibreOrderedGaussianRegion ↔
      p ∈ ginibreSignedGaussianPositiveRegion := by
  have hc := ginibreSignedGaussianRotationScale_pos
  simp only [ginibreSignedGaussianRotation_apply,
    ginibreOrderedGaussianRegion, ginibreSignedGaussianPositiveRegion,
    mem_setOf_eq]
  constructor <;> intro h
  · nlinarith
  · nlinarith

theorem ginibreOrderedGaussianSignedIntegrand_rotation (m : ℕ)
    (p : ℝ × ℝ) :
    ginibreOrderedGaussianSignedIntegrand m
        (ginibreSignedGaussianRotation p) =
      ginibreSignedGaussianRotatedIntegrand m p := by
  have hs := ginibreSignedGaussianRotationScale_sq
  have hdiff :
      ginibreSignedGaussianRotationScale * (p.1 - p.2) -
          ginibreSignedGaussianRotationScale * (p.1 + p.2) =
        -Real.sqrt 2 * p.2 := by
    unfold ginibreSignedGaussianRotationScale
    ring
  have hprod :
      (ginibreSignedGaussianRotationScale * (p.1 - p.2)) *
          (ginibreSignedGaussianRotationScale * (p.1 + p.2)) =
        p.1 ^ 2 / 2 - p.2 ^ 2 / 2 := by
    rw [show
      (ginibreSignedGaussianRotationScale * (p.1 - p.2)) *
          (ginibreSignedGaussianRotationScale * (p.1 + p.2)) =
        ginibreSignedGaussianRotationScale ^ 2 *
          ((p.1 - p.2) * (p.1 + p.2)) by ring]
    rw [hs]
    ring
  simp only [ginibreOrderedGaussianSignedIntegrand,
    ginibreSignedGaussianRotation_apply, hdiff, hprod,
    ginibreSignedGaussianRotatedIntegrand]

theorem ginibreOrderedGaussian_indicator_rotation (m : ℕ)
    (p : ℝ × ℝ) :
    ginibreOrderedGaussianRegion.indicator
        (ginibreOrderedGaussianSignedIntegrand m)
        (ginibreSignedGaussianRotation p) =
      ginibreSignedGaussianPositiveRegion.indicator
        (ginibreSignedGaussianRotatedIntegrand m) p := by
  by_cases hp : p ∈ ginibreSignedGaussianPositiveRegion
  · rw [indicator_of_mem hp,
      indicator_of_mem ((ginibreSignedGaussianRotation_mem_ordered_iff p).mpr hp)]
    exact ginibreOrderedGaussianSignedIntegrand_rotation m p
  · rw [indicator_of_notMem hp,
      indicator_of_notMem (fun h => hp
        ((ginibreSignedGaussianRotation_mem_ordered_iff p).mp h))]

/-- The rotated restricted integrand is integrable, as a consequence of
orthogonal invariance rather than a separate two-variable estimate. -/
theorem integrable_ginibreSignedGaussianRotatedIndicator (m : ℕ) :
    Integrable
      (ginibreSignedGaussianPositiveRegion.indicator
        (ginibreSignedGaussianRotatedIntegrand m))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let f := ginibreOrderedGaussianRegion.indicator
    (ginibreOrderedGaussianSignedIntegrand m)
  have hf : Integrable f
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (integrable_ginibreOrderedGaussianSignedIntegrand m).indicator
      measurableSet_ginibreOrderedGaussianRegion
  have hcomp : Integrable (f ∘ ginibreSignedGaussianRotation)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    measurePreserving_ginibreSignedGaussianRotation.integrable_comp_of_integrable hf
  apply hcomp.congr
  filter_upwards with p
  exact ginibreOrderedGaussian_indicator_rotation m p

/-- The product of two standard Gaussian densities in Cartesian
coordinates. -/
theorem gaussianPDFReal_zero_one_prod (s t : ℝ) :
    gaussianPDFReal 0 1 s * gaussianPDFReal 0 1 t =
      (2 * Real.pi)⁻¹ *
        Real.exp (-(1 / 2 : ℝ) * s ^ 2) *
        Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hsqrt : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := by
    rw [Real.sq_sqrt]
    positivity
  have hcoeff : (Real.sqrt (2 * Real.pi))⁻¹ *
      (Real.sqrt (2 * Real.pi))⁻¹ = (2 * Real.pi)⁻¹ := by
    rw [← mul_inv, ← pow_two, hsqrt]
  rw [show
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-s ^ 2 / 2) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2)) =
      ((Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.sqrt (2 * Real.pi))⁻¹) *
        Real.exp (-s ^ 2 / 2) * Real.exp (-t ^ 2 / 2) by ring]
  rw [hcoeff]
  have hsarg : -s ^ 2 / 2 = -(1 / 2 : ℝ) * s ^ 2 := by ring
  have htarg : -t ^ 2 / 2 = -(1 / 2 : ℝ) * t ^ 2 := by ring
  rw [hsarg, htarg]

/-- Conversion of the rotated product-Gaussian integral to the exact density
integral evaluated in `Higham28GinibreSignedScalar`. -/
theorem integral_ginibreSignedGaussianRotatedIndicator_eq_density (m : ℕ) :
    (∫ p : ℝ × ℝ,
        ginibreSignedGaussianPositiveRegion.indicator
          (ginibreSignedGaussianRotatedIntegrand m) p
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
      ∫ s : ℝ, ∫ t : ℝ in Ioi 0,
        (-Real.sqrt 2 / (2 * Real.pi)) *
          Real.exp (-(1 / 2 : ℝ) * s ^ 2) *
          (t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
            ((m : ℝ) * (s ^ 2 / 2 - t ^ 2 / 2) ^ (m - 1) +
              (s ^ 2 / 2 - t ^ 2 / 2) ^ m)) := by
  let f : ℝ × ℝ → ℝ :=
    ginibreSignedGaussianPositiveRegion.indicator
      (ginibreSignedGaussianRotatedIntegrand m)
  have hf : Integrable f
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    integrable_ginibreSignedGaussianRotatedIndicator m
  change (∫ p : ℝ × ℝ, f p
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = _
  rw [integral_prod f hf]
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with s
  rw [← integral_const_mul]
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : 0 < t
  · have htI : t ∈ Ioi (0 : ℝ) := ht
    rw [indicator_of_mem htI]
    have hmem : (s, t) ∈ ginibreSignedGaussianPositiveRegion := ht
    rw [show f (s, t) = ginibreSignedGaussianRotatedIntegrand m (s, t) by
      simp only [f]
      rw [indicator_of_mem hmem]]
    rw [show gaussianPDFReal 0 1 t *
          (gaussianPDFReal 0 1 s *
            ginibreSignedGaussianRotatedIntegrand m (s, t)) =
        (gaussianPDFReal 0 1 s * gaussianPDFReal 0 1 t) *
          ginibreSignedGaussianRotatedIntegrand m (s, t) by ring]
    rw [gaussianPDFReal_zero_one_prod s t]
    simp only [ginibreSignedGaussianRotatedIntegrand]
    field_simp [ne_of_gt Real.pi_pos]
  · have htI : t ∉ Ioi (0 : ℝ) := ht
    rw [indicator_of_notMem htI]
    have hmem : (s, t) ∉ ginibreSignedGaussianPositiveRegion := by
      simpa [ginibreSignedGaussianPositiveRegion] using ht
    simp [f, indicator_of_notMem hmem]

/-- Exact ordered two-Gaussian signed moment.  This is the dimension-free
constant needed by the signed Ginibre recurrence. -/
theorem ginibreOrderedGaussianSignedMoment_eq (m : ℕ) :
    ginibreOrderedGaussianSignedMoment m =
      -Real.Gamma ((m : ℝ) + 1 / 2) / Real.pi := by
  let μ := (gaussianReal 0 1).prod (gaussianReal 0 1)
  let f := ginibreOrderedGaussianRegion.indicator
    (ginibreOrderedGaussianSignedIntegrand m)
  have hchange :=
    measurePreserving_ginibreSignedGaussianRotation.integral_comp'
      (f := ginibreSignedGaussianRotation) f
  unfold ginibreOrderedGaussianSignedMoment
  rw [← integral_indicator measurableSet_ginibreOrderedGaussianRegion]
  change (∫ p : ℝ × ℝ, f p ∂μ) = _
  calc
    (∫ p : ℝ × ℝ, f p ∂μ) =
        ∫ p : ℝ × ℝ, f (ginibreSignedGaussianRotation p) ∂μ := by
      exact hchange.symm
    _ = ∫ p : ℝ × ℝ,
        ginibreSignedGaussianPositiveRegion.indicator
          (ginibreSignedGaussianRotatedIntegrand m) p ∂μ := by
      apply integral_congr_ae
      filter_upwards with p
      exact ginibreOrderedGaussian_indicator_rotation m p
    _ = ∫ s : ℝ, ∫ t : ℝ in Ioi 0,
        (-Real.sqrt 2 / (2 * Real.pi)) *
          Real.exp (-(1 / 2 : ℝ) * s ^ 2) *
          (t * Real.exp (-(1 / 2 : ℝ) * t ^ 2) *
            ((m : ℝ) * (s ^ 2 / 2 - t ^ 2 / 2) ^ (m - 1) +
              (s ^ 2 / 2 - t ^ 2 / 2) ^ m)) := by
      simpa [μ] using
        integral_ginibreSignedGaussianRotatedIndicator_eq_density m
    _ = -Real.Gamma ((m : ℝ) + 1 / 2) / Real.pi :=
      integral_integral_ginibre_signed_rotated m

end

end NumStability
