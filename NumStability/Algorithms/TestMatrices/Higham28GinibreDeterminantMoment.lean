/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Probability
import NumStability.Analysis.Probability.Gaussian.AbsoluteMoment
import Mathlib.MeasureTheory.Measure.Prod

/-! # Higham Chapter 28: the Ginibre absolute characteristic moment

The eigenvalue-inflation reduction naturally introduces

`Dₙ = 𝔼_{Gₙ,λ} |det (Gₙ - λ I)|`,

where `Gₙ` is a standard real-Ginibre matrix and `λ` is an independent
standard real Gaussian.  This file defines that sequence, verifies its first
two values without assumptions, and records the exact dimension-shift of the
normalizing factor in the inflation formula.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

noncomputable section

local instance ginibreDeterminantMomentMeasurableSpace (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

local instance ginibreDeterminantMomentSigmaFinite (n : ℕ) :
    SigmaFinite (realGinibreMeasure n) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
  infer_instance

/-- The absolute characteristic determinant averaged over an independent
standard real-Ginibre matrix and standard real Gaussian shift. -/
noncomputable def realGinibreAbsoluteCharacteristicMoment (n : ℕ) : ℝ :=
  ∫ p : RSqMat n × ℝ,
    |(p.1 - p.2 • (1 : RSqMat n)).det|
    ∂(realGinibreMeasure n).prod (gaussianReal 0 1)

/-- The scalar normalization multiplying `Dₙ₋₁` in the classical
eigenvalue-inflation determinant integral for an `n × n` matrix. -/
noncomputable def ginibreCorollary31Factor (n : ℕ) : ℝ :=
  Real.sqrt Real.pi /
    (Real.rpow 2 (((n : ℝ) - 1) / 2) * Real.Gamma ((n : ℝ) / 2))

/-- The explicit scalar increment that a two-step recurrence for `Dₘ` must
produce after the eigenvalue-inflation normalization is removed.  This is a
coefficient definition, not an assertion that the determinant moments obey
the recurrence. -/
noncomputable def ginibreAbsoluteCharacteristicMomentIncrement (m : ℕ) : ℝ :=
  Real.rpow 2 ((3 - (m : ℝ)) / 2) *
    Real.Gamma ((m : ℝ) - 1 / 2) /
      (Real.sqrt Real.pi * Real.Gamma ((m : ℝ) / 2))

/-- Raising the ambient matrix dimension by two divides the inflation
normalization by the old dimension. -/
theorem ginibreCorollary31Factor_shift_two (m : ℕ) (hm : 0 < m) :
    ginibreCorollary31Factor m =
      (m : ℝ) * ginibreCorollary31Factor (m + 2) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmhalf : (m : ℝ) / 2 ≠ 0 := by positivity
  have hpow : Real.rpow 2 ((((m + 2 : ℕ) : ℝ) - 1) / 2) =
      2 * Real.rpow 2 (((m : ℝ) - 1) / 2) := by
    rw [show (((m + 2 : ℕ) : ℝ) - 1) / 2 =
      ((m : ℝ) - 1) / 2 + 1 by norm_num; ring]
    change (2 : ℝ) ^ (((m : ℝ) - 1) / 2 + 1) =
      2 * (2 : ℝ) ^ (((m : ℝ) - 1) / 2)
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  have hgamma : Real.Gamma (((m + 2 : ℕ) : ℝ) / 2) =
      ((m : ℝ) / 2) * Real.Gamma ((m : ℝ) / 2) := by
    rw [show (((m + 2 : ℕ) : ℝ) / 2) = (m : ℝ) / 2 + 1 by
      norm_num; ring]
    rw [Real.Gamma_add_one hmhalf]
  unfold ginibreCorollary31Factor
  rw [hpow, hgamma]
  have hG : Real.Gamma ((m : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (div_pos hmR (by norm_num)))
  have hp : Real.rpow 2 (((m : ℝ) - 1) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp

/-- The only entry of a standard `1 × 1` real-Ginibre matrix has the
standard real Gaussian law. -/
theorem realGinibreMeasure_one_map_entry :
    (realGinibreMeasure 1).map (fun A : RSqMat 1 => A 0 0) =
      gaussianReal 0 1 := by
  unfold realGinibreMeasure
  rw [show (fun A : RSqMat 1 => A 0 0) =
      (fun r : Fin 1 → ℝ => r 0) ∘ (fun A : RSqMat 1 => A 0) by rfl]
  rw [← Measure.map_map (measurable_pi_apply 0) (measurable_pi_apply 0)]
  change Measure.map (Function.eval 0)
    (Measure.map (Function.eval 0)
      (Measure.pi fun _ : Fin 1 =>
        Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) = _
  have hrow : (Measure.pi fun _ : Fin 1 =>
      Measure.pi fun _ : Fin 1 => gaussianReal 0 1).map
        (Function.eval 0) = Measure.pi fun _ : Fin 1 => gaussianReal 0 1 := by
    rw [Measure.pi_map_eval]
    simp
  rw [hrow]
  change (Measure.pi fun _ : Fin 1 => gaussianReal 0 1).map
    (Function.eval 0) = gaussianReal 0 1
  rw [Measure.pi_map_eval]
  simp

/-- Jointly retaining the sole matrix entry and the independent scalar shift
gives exactly two independent standard real Gaussians. -/
theorem realGinibreMeasure_one_prod_map_entry :
    ((realGinibreMeasure 1).prod (gaussianReal 0 1)).map
        (fun p : RSqMat 1 × ℝ => (p.1 0 0, p.2)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let hA : MeasurePreserving (fun A : RSqMat 1 => A 0 0)
      (realGinibreMeasure 1) (gaussianReal 0 1) :=
    ⟨by fun_prop, realGinibreMeasure_one_map_entry⟩
  have h := hA.prod (MeasurePreserving.id (gaussianReal 0 1))
  simpa [Prod.map] using h.map_eq

/-- The empty determinant has absolute characteristic moment one. -/
theorem realGinibreAbsoluteCharacteristicMoment_zero :
    realGinibreAbsoluteCharacteristicMoment 0 = 1 := by
  unfold realGinibreAbsoluteCharacteristicMoment
  simp only [Matrix.det_isEmpty, abs_one, integral_const, measureReal_def]
  have hprod : ((realGinibreMeasure 0).prod (gaussianReal 0 1)) Set.univ = 1 := by
    rw [Measure.prod_apply MeasurableSet.univ]
    simp [realGinibreMeasure_univ]
  rw [hprod, ENNReal.toReal_one]
  simp

/-- The one-dimensional determinant is the difference of two independent
standard Gaussians, so its absolute moment is `2 / √π`. -/
theorem realGinibreAbsoluteCharacteristicMoment_one :
    realGinibreAbsoluteCharacteristicMoment 1 =
      2 / Real.sqrt Real.pi := by
  unfold realGinibreAbsoluteCharacteristicMoment
  let F : RSqMat 1 × ℝ → ℝ × ℝ := fun p => (p.1 0 0, p.2)
  let μ := (realGinibreMeasure 1).prod (gaussianReal 0 1)
  have hF : AEMeasurable F μ := by fun_prop
  calc
    (∫ p : RSqMat 1 × ℝ, |(p.1 - p.2 • (1 : RSqMat 1)).det| ∂μ) =
        ∫ p : RSqMat 1 × ℝ, |p.1 0 0 - p.2| ∂μ := by
          apply integral_congr_ae
          filter_upwards with p
          simp
    _ = ∫ p : ℝ × ℝ, |p.1 - p.2| ∂μ.map F := by
          exact (integral_map hF
            ((measurable_fst.sub measurable_snd).abs.aestronglyMeasurable)).symm
    _ = ∫ p : ℝ × ℝ, |p.1 - p.2|
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
          rw [show μ.map F =
            (gaussianReal 0 1).prod (gaussianReal 0 1) by
              simpa [μ, F] using realGinibreMeasure_one_prod_map_entry]
    _ = 2 / Real.sqrt Real.pi := integral_abs_standardGaussian_difference

end
end NumStability
