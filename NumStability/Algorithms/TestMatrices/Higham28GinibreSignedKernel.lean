/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedGaussian

/-! # Higham Chapter 28: ordered characteristic-kernel moment

The twice-applied signed incidence formula produces an ordered two-Gaussian
integral of the characteristic-product kernel.  This file proves that the
two-step difference of those kernel moments is exactly the scalar signed
moment already evaluated in `Higham28GinibreSignedGaussian`.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Ordered two-Gaussian integrand of the characteristic-product kernel. -/
def ginibreOrderedGaussianKernelIntegrand (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  (p.1 - p.2) *
    ginibreCharacteristicProductKernel m (p.1 * p.2)

theorem integrable_ginibreOrderedGaussianKernelIntegrand (m : ℕ) :
    Integrable (ginibreOrderedGaussianKernelIntegrand m)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hsum : Integrable (fun p : ℝ × ℝ =>
      ∑ k ∈ Finset.range (m + 1),
        ((m.factorial : ℝ) / (k.factorial : ℝ)) *
          ((p.1 - p.2) * (p.1 * p.2) ^ k))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    apply integrable_finset_sum
    intro k hk
    exact (integrable_ginibreSignedGaussianMonomial k).const_mul
      ((m.factorial : ℝ) / (k.factorial : ℝ))
  apply hsum.congr
  filter_upwards with p
  unfold ginibreOrderedGaussianKernelIntegrand
    ginibreCharacteristicProductKernel
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Ordered-root moment of the finite characteristic-product kernel. -/
def ginibreOrderedGaussianKernelMoment (m : ℕ) : ℝ :=
  ∫ p : ℝ × ℝ in ginibreOrderedGaussianRegion,
    ginibreOrderedGaussianKernelIntegrand m p
    ∂((gaussianReal 0 1).prod (gaussianReal 0 1))

theorem integrableOn_ginibreOrderedGaussianKernelIntegrand (m : ℕ) :
    IntegrableOn (ginibreOrderedGaussianKernelIntegrand m)
      ginibreOrderedGaussianRegion
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
  (integrable_ginibreOrderedGaussianKernelIntegrand m).integrableOn

/-- Exact kernel-moment recurrence, including the two vanishing-prefactor
base cases through natural subtraction. -/
theorem ginibreOrderedGaussianKernelMoment_eq_sub_two_add_signedMoment
    (m : ℕ) :
    ginibreOrderedGaussianKernelMoment m =
      (m : ℝ) * ((m - 1 : ℕ) : ℝ) *
          ginibreOrderedGaussianKernelMoment (m - 2) +
        ginibreOrderedGaussianSignedMoment m := by
  unfold ginibreOrderedGaussianKernelMoment
  rw [show (fun p : ℝ × ℝ => ginibreOrderedGaussianKernelIntegrand m p) =
      fun p =>
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) *
            ginibreOrderedGaussianKernelIntegrand (m - 2) p +
          ginibreOrderedGaussianSignedIntegrand m p by
    funext p
    unfold ginibreOrderedGaussianKernelIntegrand
      ginibreOrderedGaussianSignedIntegrand
    rw [ginibreCharacteristicProductKernel_eq_sub_two_add_tail]
    ring]
  rw [integral_add
    ((integrableOn_ginibreOrderedGaussianKernelIntegrand (m - 2)).const_mul
      ((m : ℝ) * ((m - 1 : ℕ) : ℝ)))
    ((integrable_ginibreOrderedGaussianSignedIntegrand m).integrableOn),
    integral_const_mul]
  rfl

/-- Evaluated difference form used by the pair-expectation recurrence. -/
theorem ginibreOrderedGaussianKernelMoment_sub_eq (m : ℕ) :
    ginibreOrderedGaussianKernelMoment m -
      (m : ℝ) * ((m - 1 : ℕ) : ℝ) *
        ginibreOrderedGaussianKernelMoment (m - 2) =
      -Real.Gamma ((m : ℝ) + 1 / 2) / Real.pi := by
  rw [ginibreOrderedGaussianKernelMoment_eq_sub_two_add_signedMoment,
    ginibreOrderedGaussianSignedMoment_eq]
  ring

end

end NumStability
