/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreDimensionTwo
import NumStability.Algorithms.TestMatrices.Higham28GinibreRecurrence
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedExpectation
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedGaussian
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedKernel
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Higham Chapter 28: closing the Ginibre formula from a two-step shift

The signed two-incidence calculation naturally produces a two-dimensional
shift of the genuine expected real-eigenvalue count.  This file isolates the
pure induction that turns that shift, together with the already proved one-
and two-dimensional base cases, into the finite formula and its limit.
-/

namespace NumStability

open Filter

noncomputable section

/-- Product of the two Corollary 3.1 normalizations in the signed pair
transfer, simplified to the coefficient of the closed-form two-step shift. -/
theorem two_mul_ginibreCorollary31Factor_product_div_pi (m : ℕ) :
    2 * (ginibreCorollary31Factor (m + 2) *
      ginibreCorollary31Factor (m + 1)) / Real.pi =
      Real.sqrt (2 / Real.pi) / Real.Gamma ((m : ℝ) + 1) := by
  have hdup0 := Real.Gamma_mul_Gamma_add_half (((m : ℝ) + 1) / 2)
  have hdup :
      Real.Gamma (((m : ℝ) + 1) / 2) *
          Real.Gamma (((m : ℝ) + 2) / 2) =
        Real.Gamma ((m : ℝ) + 1) *
          Real.rpow 2 (-(m : ℝ)) * Real.sqrt Real.pi := by
    calc
      Real.Gamma (((m : ℝ) + 1) / 2) *
          Real.Gamma (((m : ℝ) + 2) / 2) =
          Real.Gamma (((m : ℝ) + 1) / 2) *
            Real.Gamma (((m : ℝ) + 1) / 2 + 1 / 2) := by
              congr 2 <;> ring
      _ = Real.Gamma (2 * (((m : ℝ) + 1) / 2)) *
          Real.rpow 2 (1 - 2 * (((m : ℝ) + 1) / 2)) *
            Real.sqrt Real.pi := hdup0
      _ = _ := by
        rw [show 2 * (((m : ℝ) + 1) / 2) = (m : ℝ) + 1 by ring]
        rw [show 1 - ((m : ℝ) + 1) = -(m : ℝ) by ring]
  have hG1 : Real.Gamma (((m : ℝ) + 1) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hG2 : Real.Gamma (((m : ℝ) + 2) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hGm : Real.Gamma ((m : ℝ) + 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have hsqrtPiSq : Real.sqrt Real.pi ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_nonneg
  have hsqrtTwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsqrtTwoSq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hpow1 : Real.rpow 2 (((m : ℝ) + 1) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hpow2 : Real.rpow 2 ((m : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hpowNeg : Real.rpow 2 (-(m : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hpow :
      Real.rpow 2 (((m : ℝ) + 1) / 2) *
          Real.rpow 2 ((m : ℝ) / 2) *
            Real.rpow 2 (-(m : ℝ)) = Real.sqrt 2 := by
    change (2 : ℝ) ^ (((m : ℝ) + 1) / 2) *
        (2 : ℝ) ^ ((m : ℝ) / 2) *
          (2 : ℝ) ^ (-(m : ℝ)) = Real.sqrt 2
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show (((m : ℝ) + 1) / 2 + (m : ℝ) / 2 + -(m : ℝ)) =
      1 / 2 by ring]
    rw [← Real.sqrt_eq_rpow]
  have hsqrtRatio : Real.sqrt (2 / Real.pi) =
      Real.sqrt 2 / Real.sqrt Real.pi := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  unfold ginibreCorollary31Factor
  push_cast
  rw [show ((m : ℝ) + 2 - 1) / 2 = ((m : ℝ) + 1) / 2 by ring]
  rw [show ((m : ℝ) + 1 - 1) / 2 = (m : ℝ) / 2 by ring]
  rw [show ((m : ℝ) + 2) / 2 = ((m : ℝ) + 2) / 2 by rfl]
  rw [show ((m : ℝ) + 1) / 2 = ((m : ℝ) + 1) / 2 by rfl]
  rw [hsqrtRatio]
  field_simp [hG1, hG2, hGm, hsqrtPi, hsqrtTwo, hpow1, hpow2,
    hpowNeg, ne_of_gt Real.pi_pos]
  have hsqrtPiCube : Real.sqrt Real.pi ^ 3 =
      Real.pi * Real.sqrt Real.pi := by
    rw [show (3 : ℕ) = 2 + 1 by omega, pow_succ, hsqrtPiSq]
  have hrhs :
      Real.rpow 2 (((m : ℝ) + 1) / 2) *
          Real.Gamma (((m : ℝ) + 2) / 2) *
          Real.rpow 2 ((m : ℝ) / 2) *
          Real.Gamma (((m : ℝ) + 1) / 2) * Real.pi * Real.sqrt 2 =
        (Real.rpow 2 (((m : ℝ) + 1) / 2) *
          Real.rpow 2 ((m : ℝ) / 2) *
          Real.rpow 2 (-(m : ℝ))) *
            Real.Gamma ((m : ℝ) + 1) * Real.sqrt Real.pi *
              Real.pi * Real.sqrt 2 := by
    calc
      Real.rpow 2 (((m : ℝ) + 1) / 2) *
          Real.Gamma (((m : ℝ) + 2) / 2) *
          Real.rpow 2 ((m : ℝ) / 2) *
          Real.Gamma (((m : ℝ) + 1) / 2) * Real.pi * Real.sqrt 2 =
          (Real.rpow 2 (((m : ℝ) + 1) / 2) *
            Real.rpow 2 ((m : ℝ) / 2)) *
              (Real.Gamma (((m : ℝ) + 1) / 2) *
                Real.Gamma (((m : ℝ) + 2) / 2)) *
                  Real.pi * Real.sqrt 2 := by ring
      _ = (Real.rpow 2 (((m : ℝ) + 1) / 2) *
            Real.rpow 2 ((m : ℝ) / 2)) *
              (Real.Gamma ((m : ℝ) + 1) *
                Real.rpow 2 (-(m : ℝ)) * Real.sqrt Real.pi) *
                  Real.pi * Real.sqrt 2 := by rw [hdup]
      _ = _ := by ring
  rw [hrhs, hpow, hsqrtPiCube]
  rw [show Real.sqrt 2 * Real.Gamma ((m : ℝ) + 1) *
      Real.sqrt Real.pi * Real.pi * Real.sqrt 2 =
      Real.sqrt 2 ^ 2 * Real.Gamma ((m : ℝ) + 1) *
        Real.sqrt Real.pi * Real.pi by ring]
  rw [hsqrtTwoSq]
  ring

/-- After inserting the scalar signed Gaussian moment, the pair-transfer
coefficient is exactly the two-step increment of the finite closed form. -/
theorem neg_two_mul_corollary31_product_mul_signedMoment_eq_closedForm_shift
    (m : ℕ) (hm : 0 < m) :
    -2 * ((ginibreCorollary31Factor (m + 2) *
        ginibreCorollary31Factor (m + 1)) *
      (-Real.Gamma ((m : ℝ) + 1 / 2) / Real.pi)) =
      realGinibreExpectedCountClosedForm (m + 2) -
        realGinibreExpectedCountClosedForm m := by
  have hcoef := two_mul_ginibreCorollary31Factor_product_div_pi m
  calc
    -2 * ((ginibreCorollary31Factor (m + 2) *
        ginibreCorollary31Factor (m + 1)) *
      (-Real.Gamma ((m : ℝ) + 1 / 2) / Real.pi)) =
        (2 * (ginibreCorollary31Factor (m + 2) *
          ginibreCorollary31Factor (m + 1)) / Real.pi) *
            Real.Gamma ((m : ℝ) + 1 / 2) := by ring
    _ = (Real.sqrt (2 / Real.pi) / Real.Gamma ((m : ℝ) + 1)) *
          Real.Gamma ((m : ℝ) + 1 / 2) := by rw [hcoef]
    _ = Real.sqrt (2 / Real.pi) *
          (Real.Gamma ((m : ℝ) + 1 / 2) /
            Real.Gamma ((m : ℝ) + 1)) := by ring
    _ = realGinibreExpectedCountClosedForm (m + 2) -
          realGinibreExpectedCountClosedForm m :=
      (realGinibreExpectedCountClosedForm_shift_two m hm).symm

/-- Product form of the two-step normalization recurrence. -/
theorem ginibreCorollary31Factor_product_shift_two
    (m : ℕ) (hm : 1 < m) :
    ginibreCorollary31Factor m * ginibreCorollary31Factor (m - 1) =
      (m : ℝ) * ((m - 1 : ℕ) : ℝ) *
        (ginibreCorollary31Factor (m + 2) *
          ginibreCorollary31Factor (m + 1)) := by
  have hm0 : 0 < m := by omega
  have hm10 : 0 < m - 1 := by omega
  rw [ginibreCorollary31Factor_shift_two m hm0,
    ginibreCorollary31Factor_shift_two (m - 1) hm10]
  rw [show m - 1 + 2 = m + 1 by omega]
  ring

/-- A dimensionwise signed-pair kernel transfer implies the exact pair shift
needed by the final recurrence. -/
theorem signedPairShift_of_kernelTransfer
    (htransfer : ∀ n : ℕ, 2 ≤ n →
      expectedGinibreAlternatingPairCount n =
        (ginibreCorollary31Factor n *
          ginibreCorollary31Factor (n - 1)) *
            ginibreOrderedGaussianKernelMoment (n - 2)) :
    ∀ m : ℕ, 0 < m →
      expectedGinibreAlternatingPairCount (m + 2) -
          expectedGinibreAlternatingPairCount m =
        (ginibreCorollary31Factor (m + 2) *
          ginibreCorollary31Factor (m + 1)) *
            ginibreOrderedGaussianSignedMoment m := by
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    have h3 := htransfer 3 (by omega)
    norm_num at h3
    have hk :=
      ginibreOrderedGaussianKernelMoment_eq_sub_two_add_signedMoment 1
    norm_num at hk
    rw [expectedGinibreAlternatingPairCount_one, h3, hk]
    ring
  · have hm2 : 1 < m := by omega
    have hhigh := htransfer (m + 2) (by omega)
    have hlow := htransfer m (by omega)
    rw [show m + 2 - 1 = m + 1 by omega,
      show m + 2 - 2 = m by omega] at hhigh
    have hcoef := ginibreCorollary31Factor_product_shift_two m hm2
    have hkernel :=
      ginibreOrderedGaussianKernelMoment_eq_sub_two_add_signedMoment m
    calc
      expectedGinibreAlternatingPairCount (m + 2) -
          expectedGinibreAlternatingPairCount m =
          (ginibreCorollary31Factor (m + 2) *
              ginibreCorollary31Factor (m + 1)) *
              ginibreOrderedGaussianKernelMoment m -
            (ginibreCorollary31Factor m *
              ginibreCorollary31Factor (m - 1)) *
              ginibreOrderedGaussianKernelMoment (m - 2) := by
        rw [hhigh, hlow]
      _ = (ginibreCorollary31Factor (m + 2) *
            ginibreCorollary31Factor (m + 1)) *
          (ginibreOrderedGaussianKernelMoment m -
            (m : ℝ) * ((m - 1 : ℕ) : ℝ) *
              ginibreOrderedGaussianKernelMoment (m - 2)) := by
        rw [hcoef]
        ring
      _ = (ginibreCorollary31Factor (m + 2) *
            ginibreCorollary31Factor (m + 1)) *
          ginibreOrderedGaussianSignedMoment m := by
        rw [hkernel]
        ring

/-- Any genuine expected-count recurrence matching the closed-form two-step
shift implies the finite real-Ginibre expectation formula in every positive
dimension. -/
theorem realGinibreFiniteExpectationFormula_of_shift
    (hshift : ∀ m : ℕ, 0 < m →
      expectedRealEigenvalueCount (m + 2) -
          expectedRealEigenvalueCount m =
        realGinibreExpectedCountClosedForm (m + 2) -
          realGinibreExpectedCountClosedForm m) :
    RealGinibreFiniteExpectationFormula := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn1 : n = 1
      · subst n
        exact expectedRealEigenvalueCount_eq_closedForm_one
      by_cases hn2 : n = 2
      · subst n
        exact expectedRealEigenvalueCount_eq_closedForm_two
      have hn3 : 3 ≤ n := by omega
      let m := n - 2
      have hmpos : 0 < m := by
        dsimp [m]
        omega
      have hmlt : m < n := by
        dsimp [m]
        omega
      have hmadd : m + 2 = n := by
        dsimp [m]
        omega
      have hprev := ih m hmlt hmpos
      have hstep := hshift m hmpos
      rw [hmadd] at hstep
      linarith

/-- The same genuine two-step shift immediately yields Higham's normalized
real-Ginibre limit. -/
theorem realGinibreExpectedCountLimit_of_shift
    (hshift : ∀ m : ℕ, 0 < m →
      expectedRealEigenvalueCount (m + 2) -
          expectedRealEigenvalueCount m =
        realGinibreExpectedCountClosedForm (m + 2) -
          realGinibreExpectedCountClosedForm m) :
    RealGinibreExpectedCountLimit :=
  realGinibreExpectedCountLimit_of_finiteExpectationFormula
    (realGinibreFiniteExpectationFormula_of_shift hshift)

/-- Recurrence-facing endpoint: once the iterated signed-incidence theorem
identifies the shift of the pair expectation with the ordered scalar moment,
the genuine finite expectation formula follows with no further assumptions. -/
theorem realGinibreFiniteExpectationFormula_of_signedPairShift
    (hpair : ∀ m : ℕ, 0 < m →
      expectedGinibreAlternatingPairCount (m + 2) -
          expectedGinibreAlternatingPairCount m =
        (ginibreCorollary31Factor (m + 2) *
          ginibreCorollary31Factor (m + 1)) *
            ginibreOrderedGaussianSignedMoment m) :
    RealGinibreFiniteExpectationFormula := by
  apply realGinibreFiniteExpectationFormula_of_shift
  intro m hm
  rw [expectedRealEigenvalueCount_shift_eq_neg_two_mul_pair_shift]
  rw [hpair m hm, ginibreOrderedGaussianSignedMoment_eq]
  exact
    neg_two_mul_corollary31_product_mul_signedMoment_eq_closedForm_shift m hm

/-- The identical pair-shift endpoint also yields Higham's normalized limit. -/
theorem realGinibreExpectedCountLimit_of_signedPairShift
    (hpair : ∀ m : ℕ, 0 < m →
      expectedGinibreAlternatingPairCount (m + 2) -
          expectedGinibreAlternatingPairCount m =
        (ginibreCorollary31Factor (m + 2) *
          ginibreCorollary31Factor (m + 1)) *
            ginibreOrderedGaussianSignedMoment m) :
    RealGinibreExpectedCountLimit :=
  realGinibreExpectedCountLimit_of_finiteExpectationFormula
    (realGinibreFiniteExpectationFormula_of_signedPairShift hpair)

end

end NumStability
