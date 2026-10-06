/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreMeasure

/-! # Higham Chapter 28: Ginibre--Gaussian joint density

This file records the ordinary-integral density conversion for an independent
real-Ginibre matrix and standard Gaussian scalar.  The statement is
unconditional, using the standard zero convention for nonintegrable Bochner
integrals.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

noncomputable section

private local instance ginibreJointDensityMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- Integrability of the finite standard-Gaussian vector density. -/
theorem integrable_standardGaussianVectorDensity (n : ℕ) :
    Integrable (fun z : Fin n → ℝ =>
      ∏ i : Fin n, gaussianPDFReal 0 1 (z i)) :=
  Integrable.fintype_prod (fun _ : Fin n =>
    integrable_gaussianPDFReal 0 1)

/-- The product density of a finite standard-Gaussian vector has ordinary
Lebesgue integral one. -/
theorem integral_standardGaussianVectorDensity_eq_one (n : ℕ) :
    (∫ z : Fin n → ℝ,
      ∏ i : Fin n, gaussianPDFReal 0 1 (z i)) = 1 := by
  rw [integral_fintype_prod_volume_eq_prod]
  simp [integral_gaussianPDFReal_eq_one]

/-- Convert an integral under the independent real-Ginibre and standard
Gaussian laws into the corresponding density-weighted product-Lebesgue
integral. -/
theorem integral_realGinibre_prod_gaussian_eq_jointDensity
    (n : ℕ) (g : RSqMat n × ℝ → ℝ) :
    (∫ p, g p ∂((realGinibreMeasure n).prod (gaussianReal 0 1))) =
      ∫ p,
        (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2) * g p
        ∂((realGinibreLebesgueMeasure n).prod volume) := by
  rw [realGinibreMeasure_eq_withDensity]
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [prod_withDensity
    (measurable_realGinibreDensityReal n).ennreal_ofReal
    (measurable_gaussianPDF 0 1)]
  have hdensity : Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal (realGinibreDensityReal n p.1) *
        gaussianPDF 0 1 p.2) :=
    (((measurable_realGinibreDensityReal n).ennreal_ofReal.comp
      measurable_fst).mul
        ((measurable_gaussianPDF 0 1).comp measurable_snd))
  rw [integral_withDensity_eq_integral_toReal_smul hdensity]
  · apply integral_congr_ae
    filter_upwards with p
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal
        (le_of_lt (realGinibreDensityReal_pos n p.1)),
      toReal_gaussianPDF]
    simp only [smul_eq_mul]
  · filter_upwards with p
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top gaussianPDF_lt_top

end

end NumStability
