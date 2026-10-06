/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Probability
import NumStability.Algorithms.TestMatrices.Higham28Asymptotics
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Higham Chapter 28: the real-Ginibre closed-form asymptotic

This file isolates the analytic part of the real-Ginibre expected-real-root
calculation.  The equality between the matrix integral in
`expectedRealEigenvalueCount` and this closed form is the separate
random-matrix (Kac--Rice/coarea) producer.
-/

namespace NumStability

open Filter Asymptotics Polynomial MeasureTheory

local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- A real characteristic polynomial has at most `n` real roots, counted
with algebraic multiplicity. -/
theorem realEigenvalueCount_le (n : ℕ) (A : RSqMat n) :
    realEigenvalueCount n A ≤ n := by
  unfold realEigenvalueCount
  exact (Polynomial.card_roots' (Matrix.charpoly A)).trans_eq (by simp)

/-- Once measurability of the root count is supplied, boundedness makes its
integrability under the normalized real-Ginibre law automatic. -/
theorem integrable_realEigenvalueCount_of_aestronglyMeasurable
    (n : ℕ)
    (hmeas : AEStronglyMeasurable
      (fun A : RSqMat n => (realEigenvalueCount n A : ℝ))
      (realGinibreMeasure n)) :
    Integrable
      (fun A : RSqMat n => (realEigenvalueCount n A : ℝ))
      (realGinibreMeasure n) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  apply Integrable.of_bound hmeas n
  filter_upwards with A
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast realEigenvalueCount_le n A

/-- The exact finite-dimensional expression of Edelman--Kostlan--Shub for
the expected number of real roots of an `n x n` real Ginibre matrix.  Its
identification with `expectedRealEigenvalueCount` is intentionally kept as a
separate theorem surface. -/
noncomputable def realGinibreExpectedCountClosedForm (n : ℕ) : ℝ :=
  1 / 2 +
    Real.sqrt (2 / Real.pi) *
      (Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma (n : ℝ)) *
      (₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ))

/-- At positive integers, the Gamma ratio in the real-Ginibre formula is a
central-binomial expression. -/
theorem realGinibre_gammaRatio_eq_centralBinom (n : ℕ) (hn : 0 < n) :
    Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma (n : ℝ) =
      Real.sqrt Real.pi * (n : ℝ) * (Nat.centralBinom n : ℝ) /
        (4 : ℝ) ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hcentral :
      (Nat.centralBinom (k + 1) : ℝ) =
        (((2 * (k + 1)).factorial : ℝ) /
          (((k + 1).factorial : ℝ) ^ 2)) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    simpa [two_mul, pow_two] using
      (Nat.cast_add_choose ℝ (a := k + 1) (b := k + 1))
  have hdoubleNat :
      (2 * (k + 1)).factorial =
        2 ^ (k + 1) * (k + 1).factorial *
          Nat.doubleFactorial (2 * (k + 1) - 1) := by
    have hfac := Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
    have heven := Nat.doubleFactorial_two_mul (k + 1)
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    rw [hfac]
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, heven]
    congr 2
  have hdouble :
      ((2 * (k + 1)).factorial : ℝ) =
        (2 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) *
          (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) := by
    exact_mod_cast hdoubleNat
  rw [Real.Gamma_nat_add_half]
  have hgamma : Real.Gamma ((k + 1 : ℕ) : ℝ) = (k.factorial : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using Real.Gamma_nat_eq_factorial k
  rw [hgamma, hcentral, hdouble]
  have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hskfac : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
  have hpow2 : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have hpow4 : (4 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have hdf : (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) ≠ 0 := by
    positivity
  rw [show (4 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1)) ^ 2 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_two]]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- The half-step Gamma ratio occurring in the finite real-Ginibre formula
has its expected square-root asymptotic. -/
theorem realGinibre_gammaRatio_div_sqrt_tendsto_one :
    Tendsto
      (fun n : ℕ =>
        (Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma (n : ℝ)) /
          Real.sqrt n)
      atTop (nhds 1) := by
  have hden : ∀ᶠ n : ℕ in atTop,
      (4 : ℝ) ^ n / Real.sqrt (Real.pi * n) ≠ 0 := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hratio :
      Tendsto
        ((fun n : ℕ => (Nat.centralBinom n : ℝ)) /
          (fun n : ℕ => (4 : ℝ) ^ n / Real.sqrt (Real.pi * n)))
        atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hden).mp
      pascalCentralBinomial_isEquivalent
  apply hratio.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  rw [Pi.div_apply, realGinibre_gammaRatio_eq_centralBinom n hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
  have hpow : (4 : ℝ) ^ n ≠ 0 := by positivity
  rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = n := by
    rw [Real.sq_sqrt (le_of_lt hnR)]
  field_simp
  nlinarith [hsqrt_sq]

/-- The `k`th scalar term in the hypergeometric factor of the real-Ginibre
finite formula. -/
noncomputable def ginibreHypergeometricTerm (n k : ℕ) : ℝ :=
  ((k.factorial : ℝ)⁻¹ * (ascPochhammer ℝ k).eval 1 *
      (ascPochhammer ℝ k).eval (-1 / 2) *
      ((ascPochhammer ℝ k).eval (n : ℝ))⁻¹) *
    (1 / 2 : ℝ) ^ k

/-- Expansion of the real-Ginibre hypergeometric factor into its defining
power series. -/
theorem realGinibre_hypergeometric_eq_tsum (n : ℕ) :
    ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ) =
      ∑' k : ℕ, ginibreHypergeometricTerm n k := by
  simpa [ginibreHypergeometricTerm, smul_eq_mul] using
    congrFun
      (ordinaryHypergeometric_eq_tsum
        (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ))
      (1 / 2 : ℝ)

/-- Cancellation of the `(1)_k/k!` factor in each Ginibre term. -/
theorem ginibreHypergeometricTerm_eq (n k : ℕ) :
    ginibreHypergeometricTerm n k =
      (ascPochhammer ℝ k).eval (-1 / 2) *
        ((ascPochhammer ℝ k).eval (n : ℝ))⁻¹ *
        (1 / 2 : ℝ) ^ k := by
  simp [ginibreHypergeometricTerm, ascPochhammer_eval_one,
    Nat.factorial_ne_zero]

@[simp]
theorem ginibreHypergeometricTerm_zero (n : ℕ) :
    ginibreHypergeometricTerm n 0 = 1 := by
  simp [ginibreHypergeometricTerm]

/-- Successive Ginibre hypergeometric terms differ by the elementary ratio
`(k - 1/2)/(n+k) * 1/2`. -/
theorem ginibreHypergeometricTerm_succ (n k : ℕ) :
    ginibreHypergeometricTerm n (k + 1) =
      ginibreHypergeometricTerm n k *
        ((k : ℝ) - 1 / 2) * ((n : ℝ) + k)⁻¹ * (1 / 2) := by
  rw [ginibreHypergeometricTerm_eq, ginibreHypergeometricTerm_eq]
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, pow_succ]
  rw [mul_inv_rev]
  ring

/-- The first nonconstant term is `-1/(4n)`. -/
theorem ginibreHypergeometricTerm_one (n : ℕ) (hn : 0 < n) :
    ginibreHypergeometricTerm n 1 = -(1 / (4 * n : ℝ)) := by
  rw [ginibreHypergeometricTerm_eq]
  simp
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

private theorem ginibre_abs_sub_half_le_add (n k : ℕ) (hn : 0 < n) :
    |(k : ℝ) - 1 / 2| ≤ (n : ℝ) + k := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (0 : ℝ) ≤ k := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- For positive dimension, the absolute values of successive terms contract
by at least a factor `1/2`. -/
theorem abs_ginibreHypergeometricTerm_succ_le_half
    (n k : ℕ) (hn : 0 < n) :
    |ginibreHypergeometricTerm n (k + 1)| ≤
      |ginibreHypergeometricTerm n k| * (1 / 2 : ℝ) := by
  rw [ginibreHypergeometricTerm_succ]
  simp only [abs_mul, abs_inv]
  have hden : (0 : ℝ) < (n : ℝ) + k := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hratio :
      |(k : ℝ) - 1 / 2| * |(n : ℝ) + k|⁻¹ ≤ 1 := by
    rw [abs_of_pos hden]
    exact mul_inv_le_one_of_le₀
      (ginibre_abs_sub_half_le_add n k hn) (le_of_lt hden)
  have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [hhalf]
  calc
    |ginibreHypergeometricTerm n k| * |(k : ℝ) - 1 / 2| *
          |(n : ℝ) + k|⁻¹ * (1 / 2) =
        |ginibreHypergeometricTerm n k| *
          (|(k : ℝ) - 1 / 2| * |(n : ℝ) + k|⁻¹) * (1 / 2) := by
            ring
    _ ≤ |ginibreHypergeometricTerm n k| * 1 * (1 / 2) := by
      gcongr
    _ = |ginibreHypergeometricTerm n k| * (1 / 2) := by ring

/-- Explicit geometric majorant for every nonconstant hypergeometric term. -/
theorem abs_ginibreHypergeometricTerm_succ_le
    (n k : ℕ) (hn : 0 < n) :
    |ginibreHypergeometricTerm n (k + 1)| ≤
      (1 / (4 * n : ℝ)) * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero =>
      rw [ginibreHypergeometricTerm_one n hn]
      simp only [abs_neg, pow_zero, mul_one]
      rw [abs_of_nonneg]
      positivity
  | succ k ih =>
      calc
        |ginibreHypergeometricTerm n (k + 1 + 1)| ≤
            |ginibreHypergeometricTerm n (k + 1)| * (1 / 2 : ℝ) :=
          abs_ginibreHypergeometricTerm_succ_le_half n (k + 1) hn
        _ ≤ ((1 / (4 * n : ℝ)) * (1 / 2 : ℝ) ^ k) * (1 / 2) := by
          gcongr
        _ = (1 / (4 * n : ℝ)) * (1 / 2 : ℝ) ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- The entire nonconstant hypergeometric tail is bounded by `1/(2n)`.
This quantitative estimate is stronger than the convergence needed below. -/
theorem abs_realGinibre_hypergeometric_sub_one_le
    (n : ℕ) (hn : 0 < n) :
    |₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ) - 1| ≤
      1 / (2 * n : ℝ) := by
  let c : ℝ := 1 / (4 * n : ℝ)
  have hmajor : Summable (fun k : ℕ => c * (1 / 2 : ℝ) ^ k) :=
    summable_geometric_two.mul_left c
  have hbound : ∀ k : ℕ,
      ‖ginibreHypergeometricTerm n (k + 1)‖ ≤
        c * (1 / 2 : ℝ) ^ k := by
    intro k
    simpa [Real.norm_eq_abs, c] using
      abs_ginibreHypergeometricTerm_succ_le n k hn
  have htail : Summable (fun k : ℕ => ginibreHypergeometricTerm n (k + 1)) :=
    hmajor.of_norm_bounded hbound
  have hfull : Summable (fun k : ℕ => ginibreHypergeometricTerm n k) := by
    apply (summable_nat_add_iff 1).1
    simpa using htail
  have hsplit :
      (∑' k : ℕ, ginibreHypergeometricTerm n k) =
        1 + ∑' k : ℕ, ginibreHypergeometricTerm n (k + 1) := by
    simpa using (hfull.sum_add_tsum_nat_add 1).symm
  rw [realGinibre_hypergeometric_eq_tsum, hsplit]
  have htailBound :
      ‖∑' k : ℕ, ginibreHypergeometricTerm n (k + 1)‖ ≤
        ∑' k : ℕ, c * (1 / 2 : ℝ) ^ k :=
    tsum_of_norm_bounded hmajor.hasSum hbound
  have hsumMajor :
      (∑' k : ℕ, c * (1 / 2 : ℝ) ^ k) = c * 2 := by
    rw [tsum_mul_left, tsum_geometric_two]
  rw [show 1 + (∑' k : ℕ, ginibreHypergeometricTerm n (k + 1)) - 1 =
      ∑' k : ℕ, ginibreHypergeometricTerm n (k + 1) by ring]
  rw [Real.norm_eq_abs, hsumMajor] at htailBound
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp [c] at htailBound
  convert htailBound using 1
  field_simp
  norm_num

/-- The hypergeometric correction in the exact finite-`n` formula tends to
one. -/
theorem realGinibre_hypergeometric_tendsto_one :
    Tendsto
      (fun n : ℕ =>
        ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ))
      atTop (nhds 1) := by
  have hmajor :
      Tendsto (fun n : ℕ => 1 / (2 * n : ℝ)) atTop (nhds 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ) using 1
    funext n
    simp [div_eq_mul_inv, mul_inv_rev]
    ring
  apply tendsto_iff_dist_tendsto_zero.2
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hmajor
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  rw [Real.dist_eq]
  exact abs_realGinibre_hypergeometric_sub_one_le n (by omega)

/-- The exact finite-dimensional closed form has the real-Ginibre
`sqrt(2n/pi)` asymptotic. -/
theorem realGinibreExpectedCountClosedForm_limit :
    Tendsto
      (fun n : ℕ => realGinibreExpectedCountClosedForm n / Real.sqrt n)
      atTop (nhds (Real.sqrt (2 / Real.pi))) := by
  have hsqrtTop :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hconstant :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) / Real.sqrt n)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsqrtTop
  have hproduct :
      Tendsto
        (fun n : ℕ =>
          ((Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma (n : ℝ)) /
              Real.sqrt n) *
            ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ))
        atTop (nhds 1) := by
    simpa using realGinibre_gammaRatio_div_sqrt_tendsto_one.mul
      realGinibre_hypergeometric_tendsto_one
  have hscaled :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (2 / Real.pi) *
            (((Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma (n : ℝ)) /
                Real.sqrt n) *
              ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ)))
        atTop (nhds (Real.sqrt (2 / Real.pi))) := by
    simpa using hproduct.const_mul (Real.sqrt (2 / Real.pi))
  have hadd := hconstant.add hscaled
  convert hadd using 1
  · funext n
    unfold realGinibreExpectedCountClosedForm
    ring
  · simp

/-- The exact remaining random-matrix producer: the matrix integral of the
real-root count equals the Edelman--Kostlan--Shub finite formula in every
positive dimension.  This proposition is kept separate from the analytic
closed-form theorem above because its proof requires the Kac--Rice/coarea
and Jacobian calculation. -/
def RealGinibreFiniteExpectationFormula : Prop :=
  ∀ n : ℕ, 0 < n →
    expectedRealEigenvalueCount n = realGinibreExpectedCountClosedForm n

/-- With the analytic asymptotic now discharged locally, only the precise
finite expectation formula is needed to conclude Higham's Ginibre limit. -/
theorem realGinibreExpectedCountLimit_of_finiteExpectationFormula
    (hfinite : RealGinibreFiniteExpectationFormula) :
    RealGinibreExpectedCountLimit := by
  unfold RealGinibreExpectedCountLimit
  apply realGinibreExpectedCountClosedForm_limit.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  rw [hfinite n (by omega)]

end NumStability
