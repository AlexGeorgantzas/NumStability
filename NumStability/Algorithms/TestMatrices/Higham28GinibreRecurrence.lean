/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreIntegral
import Mathlib.Analysis.Analytic.Binomial

/-! # Higham Chapter 28: scalar Ginibre recurrence and the one-dimensional case

The finite real-Ginibre closed form contains the scalar hypergeometric factor
`₂F₁ 1 (-1 / 2) n (1 / 2)`.  Its defining series admits an elementary
two-step telescope.  This file proves that telescope, the resulting recurrence
for `realGinibreExpectedCountClosedForm`, and the genuine finite-expectation
formula in dimension one.

The recurrence here is entirely about the proposed scalar closed form.  It
does not assume, and should not be confused with, a recurrence for the random
matrix expectation itself.
-/

namespace NumStability

open Filter Asymptotics Polynomial MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private theorem realGinibre_hypergeometric_one_rpow :
    ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (1 : ℝ) (1 / 2 : ℝ) =
      (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := by
  rw [ordinaryHypergeometric]
  rw [← ordinaryHypergeometricSeries_symm]
  have hcoeff : ∀ k : ℕ, (k : ℝ) ≠ -(1 : ℝ) := by
    intro k hk
    have : (0 : ℝ) ≤ k := by positivity
    linarith
  have hseries := binomialSeries_eq_ordinaryHypergeometricSeries
    (𝔸 := ℝ) (a := (1 / 2 : ℝ)) (b := (1 : ℝ)) hcoeff
  have hball : (-1 / 2 : ℝ) ∈ Metric.eball 0 (1 : ℝ≥0∞) := by
    simp [Metric.mem_eball, enorm_eq_nnnorm]
  have hbin := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero
    (a := (1 / 2 : ℝ))).sum hball
  rw [show (0 : ℝ) + (-1 / 2) = -1 / 2 by ring] at hbin
  have hsum :
      (binomialSeries ℝ (1 / 2 : ℝ)).sum (-1 / 2 : ℝ) =
        (ordinaryHypergeometricSeries ℝ (-(1 / 2 : ℝ)) 1 1).sum
          (1 / 2 : ℝ) := by
    rw [hseries]
    unfold FormalMultilinearSeries.sum
    apply tsum_congr
    intro n
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    congr 1
    funext i
    simp
    norm_num
  convert hsum.symm.trans hbin.symm using 1 <;> ring

/-- The scalar hypergeometric factor at `n = 1`, obtained from the binomial
series for `(1 + x)^(1/2)` at `x = -1/2`. -/
theorem realGinibre_hypergeometric_one :
    ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (1 : ℝ) (1 / 2 : ℝ) =
      Real.sqrt (1 / 2 : ℝ) := by
  rw [realGinibre_hypergeometric_one_rpow, Real.sqrt_eq_rpow]

/-- The proposed finite-dimensional closed form has value one in dimension
one. -/
theorem realGinibreExpectedCountClosedForm_one :
    realGinibreExpectedCountClosedForm 1 = 1 := by
  rw [realGinibreExpectedCountClosedForm,
    realGinibre_gammaRatio_eq_centralBinom 1 (by norm_num)]
  norm_num only [Nat.cast_one, pow_one]
  have hh : ₂F₁ (1 : ℝ) (-(1 / 2 : ℝ)) (1 : ℝ) (1 / 2 : ℝ) =
      Real.sqrt (1 / 2 : ℝ) := by
    convert realGinibre_hypergeometric_one using 1 <;> ring
  rw [hh]
  norm_num [Nat.centralBinom]
  have hspi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  norm_num

/-- Shifting the lower hypergeometric parameter by two multiplies each scalar
series coefficient by an explicit rational factor. -/
theorem ginibreHypergeometricTerm_shift_two (m k : ℕ) (hm : 0 < m) :
    ginibreHypergeometricTerm (m + 2) k =
      ginibreHypergeometricTerm m k *
        ((m : ℝ) * (m + 1) /
          (((m : ℝ) + k) * ((m : ℝ) + k + 1))) := by
  induction k with
  | zero =>
      rw [ginibreHypergeometricTerm_zero,
        ginibreHypergeometricTerm_zero]
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
  | succ k ih =>
      rw [ginibreHypergeometricTerm_succ,
        ginibreHypergeometricTerm_succ, ih]
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
      have hmk : (m : ℝ) + k ≠ 0 := by positivity
      have hmks : (m : ℝ) + k + 1 ≠ 0 := by positivity
      have hmks2 : (m : ℝ) + k + 2 ≠ 0 := by positivity
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
      field_simp
      ring

/-- The certificate whose consecutive difference is the shifted-series
coefficient difference. -/
noncomputable def ginibreHypergeometricTelescopeTerm (m k : ℕ) : ℝ :=
  (((2 : ℝ) * k - 1) / ((m : ℝ) + k)) *
    ginibreHypergeometricTerm m k

/-- Termwise telescoping identity behind the two-step hypergeometric
recurrence. -/
theorem ginibreHypergeometricTerm_shift_two_telescope
    (m k : ℕ) (hm : 0 < m) :
    (((m : ℝ) + 1 / 2) * ((m : ℝ) + 3 / 2) /
        ((m : ℝ) * ((m : ℝ) + 1))) *
          ginibreHypergeometricTerm (m + 2) k -
        ginibreHypergeometricTerm m k =
      ginibreHypergeometricTelescopeTerm m (k + 1) -
        ginibreHypergeometricTelescopeTerm m k := by
  rw [ginibreHypergeometricTerm_shift_two m k hm]
  unfold ginibreHypergeometricTelescopeTerm
  rw [ginibreHypergeometricTerm_succ]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hmk : (m : ℝ) + k ≠ 0 := by positivity
  have hmks : (m : ℝ) + k + 1 ≠ 0 := by positivity
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
  field_simp
  ring

/-- Absolute summability of the scalar hypergeometric series for every
positive lower parameter. -/
theorem summable_ginibreHypergeometricTerm (m : ℕ) (hm : 0 < m) :
    Summable (fun k : ℕ => ginibreHypergeometricTerm m k) := by
  let c : ℝ := 1 / (4 * m : ℝ)
  have hmajor : Summable (fun k : ℕ => c * (1 / 2 : ℝ) ^ k) :=
    summable_geometric_two.mul_left c
  have htail : Summable (fun k : ℕ => ginibreHypergeometricTerm m (k + 1)) := by
    apply hmajor.of_norm_bounded
    intro k
    simpa [Real.norm_eq_abs, c] using
      abs_ginibreHypergeometricTerm_succ_le m k hm
  apply (summable_nat_add_iff 1).1
  simpa using htail

private theorem abs_ginibreHypergeometricTelescopeCoefficient_le_two
    (m k : ℕ) (hm : 0 < m) :
    |(((2 : ℝ) * k - 1) / ((m : ℝ) + k))| ≤ 2 := by
  have hden : (0 : ℝ) < (m : ℝ) + k := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  rw [abs_le]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkR : (0 : ℝ) ≤ k := by positivity
  constructor <;> linarith

private theorem summable_ginibreHypergeometricTelescopeTerm
    (m : ℕ) (hm : 0 < m) :
    Summable (ginibreHypergeometricTelescopeTerm m) := by
  have ht := summable_ginibreHypergeometricTerm m hm
  apply (ht.norm.mul_left 2).of_norm_bounded
  intro k
  unfold ginibreHypergeometricTelescopeTerm
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |((2 : ℝ) * ↑k - 1) / (↑m + ↑k)| *
          |ginibreHypergeometricTerm m k| ≤
        2 * |ginibreHypergeometricTerm m k| := by
      gcongr
      exact abs_ginibreHypergeometricTelescopeCoefficient_le_two m k hm
    _ = 2 * ‖ginibreHypergeometricTerm m k‖ := by
      rw [Real.norm_eq_abs]

private theorem hasSum_ginibreHypergeometricTelescopeDifference
    (m : ℕ) (hm : 0 < m) :
    HasSum
      (fun k : ℕ => ginibreHypergeometricTelescopeTerm m (k + 1) -
        ginibreHypergeometricTelescopeTerm m k)
      (1 / (m : ℝ)) := by
  let U : ℕ → ℝ := ginibreHypergeometricTelescopeTerm m
  have hU : Summable U := summable_ginibreHypergeometricTelescopeTerm m hm
  have hUshift : Summable (fun k : ℕ => U (k + 1)) := by
    simpa using (summable_nat_add_iff 1).2 hU
  have hdiff : Summable (fun k : ℕ => U (k + 1) - U k) :=
    hUshift.sub hU
  apply (hasSum_iff_tendsto_nat_of_summable_norm hdiff.norm).2
  have hpartial : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, (U (k + 1) - U k)) = U N - U 0 := by
    intro N
    calc
      (∑ k ∈ Finset.range N, (U (k + 1) - U k)) =
          ∑ k ∈ Finset.range N, ((-U k) - (-U (k + 1))) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = -U 0 - (-U N) := Finset.sum_range_sub' (fun k => -U k) N
      _ = U N - U 0 := by ring
  simp_rw [hpartial]
  have hlim : Tendsto (fun N => U N - U 0) atTop (nhds (0 - U 0)) :=
    hU.tendsto_atTop_zero.sub tendsto_const_nhds
  have hU0 : 0 - U 0 = 1 / (m : ℝ) := by
    dsimp [U, ginibreHypergeometricTelescopeTerm]
    rw [ginibreHypergeometricTerm_zero]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    norm_num only [Nat.cast_zero, mul_zero, sub_zero, zero_sub, add_zero, mul_one]
    field_simp
  simpa [hU0] using hlim

/-- Two-step recurrence for the scalar hypergeometric factor in the finite
real-Ginibre formula. -/
theorem realGinibre_hypergeometric_shift_two (m : ℕ) (hm : 0 < m) :
    (((m : ℝ) + 1 / 2) * ((m : ℝ) + 3 / 2) /
        ((m : ℝ) * ((m : ℝ) + 1))) *
          ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) ((m + 2 : ℕ) : ℝ) (1 / 2 : ℝ) -
        ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (m : ℝ) (1 / 2 : ℝ) =
      1 / (m : ℝ) := by
  rw [realGinibre_hypergeometric_eq_tsum,
    realGinibre_hypergeometric_eq_tsum]
  let a : ℝ := ((m : ℝ) + 1 / 2) * ((m : ℝ) + 3 / 2) /
    ((m : ℝ) * ((m : ℝ) + 1))
  have h2 := summable_ginibreHypergeometricTerm (m + 2) (by omega)
  have hmS := summable_ginibreHypergeometricTerm m hm
  have hleft : HasSum
      (fun k : ℕ => a * ginibreHypergeometricTerm (m + 2) k -
        ginibreHypergeometricTerm m k)
      (a * (∑' k : ℕ, ginibreHypergeometricTerm (m + 2) k) -
        ∑' k : ℕ, ginibreHypergeometricTerm m k) :=
    (HasSum.mul_left a h2.hasSum).sub hmS.hasSum
  have hright : HasSum
      (fun k : ℕ => a * ginibreHypergeometricTerm (m + 2) k -
        ginibreHypergeometricTerm m k)
      (1 / (m : ℝ)) := by
    apply (hasSum_ginibreHypergeometricTelescopeDifference m hm).congr_fun
    intro k
    dsimp [a]
    exact ginibreHypergeometricTerm_shift_two_telescope m k hm
  change a * (∑' k : ℕ, ginibreHypergeometricTerm (m + 2) k) -
      (∑' k : ℕ, ginibreHypergeometricTerm m k) = 1 / (m : ℝ)
  exact hleft.unique hright

/-- The proposed finite-dimensional real-Ginibre closed form gains one
explicit Gamma-ratio term when its dimension is increased by two. -/
theorem realGinibreExpectedCountClosedForm_shift_two
    (m : ℕ) (hm : 0 < m) :
    realGinibreExpectedCountClosedForm (m + 2) -
        realGinibreExpectedCountClosedForm m =
      Real.sqrt (2 / Real.pi) *
        (Real.Gamma ((m : ℝ) + 1 / 2) /
          Real.Gamma ((m : ℝ) + 1)) := by
  let a : ℝ := ((m : ℝ) + 1 / 2) * ((m : ℝ) + 3 / 2) /
    ((m : ℝ) * ((m : ℝ) + 1))
  let H₂ : ℝ := ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) ((m + 2 : ℕ) : ℝ) (1 / 2 : ℝ)
  let H₀ : ℝ := ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (m : ℝ) (1 / 2 : ℝ)
  have hhyper : a * H₂ - H₀ = 1 / (m : ℝ) := by
    exact realGinibre_hypergeometric_shift_two m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hmhalf : (m : ℝ) + 1 / 2 ≠ 0 := by positivity
  have hmthreehalf : (m : ℝ) + 3 / 2 ≠ 0 := by positivity
  have hgamma_m1 :
      Real.Gamma ((m : ℝ) + 1) = (m : ℝ) * Real.Gamma (m : ℝ) :=
    Real.Gamma_add_one hm0
  have hgamma_m2 :
      Real.Gamma ((m : ℝ) + 2) =
        ((m : ℝ) + 1) * ((m : ℝ) * Real.Gamma (m : ℝ)) := by
    calc
      Real.Gamma ((m : ℝ) + 2) =
          Real.Gamma (((m : ℝ) + 1) + 1) := by congr 1 <;> ring
      _ = ((m : ℝ) + 1) * Real.Gamma ((m : ℝ) + 1) := by
        rw [Real.Gamma_add_one]
        positivity
      _ = _ := by rw [hgamma_m1]
  have hgamma_half2 :
      Real.Gamma ((m : ℝ) + 2 + 1 / 2) =
        ((m : ℝ) + 3 / 2) * (((m : ℝ) + 1 / 2) *
          Real.Gamma ((m : ℝ) + 1 / 2)) := by
    calc
      Real.Gamma ((m : ℝ) + 2 + 1 / 2) =
          Real.Gamma (((m : ℝ) + 3 / 2) + 1) := by congr 1 <;> ring
      _ = ((m : ℝ) + 3 / 2) * Real.Gamma ((m : ℝ) + 3 / 2) := by
        rw [Real.Gamma_add_one hmthreehalf]
      _ = ((m : ℝ) + 3 / 2) *
          (((m : ℝ) + 1 / 2) * Real.Gamma ((m : ℝ) + 1 / 2)) := by
        rw [show (m : ℝ) + 3 / 2 = ((m : ℝ) + 1 / 2) + 1 by ring,
          Real.Gamma_add_one hmhalf]
  have hratio2 :
      Real.Gamma ((m : ℝ) + 2 + 1 / 2) / Real.Gamma ((m : ℝ) + 2) =
        (Real.Gamma ((m : ℝ) + 1 / 2) / Real.Gamma (m : ℝ)) * a := by
    rw [hgamma_half2, hgamma_m2]
    dsimp [a]
    have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
    have hGm : Real.Gamma (m : ℝ) ≠ 0 :=
      ne_of_gt (Real.Gamma_pos_of_pos hmR)
    field_simp
  have hratio1 :
      (Real.Gamma ((m : ℝ) + 1 / 2) / Real.Gamma (m : ℝ)) *
          (1 / (m : ℝ)) =
        Real.Gamma ((m : ℝ) + 1 / 2) / Real.Gamma ((m : ℝ) + 1) := by
    rw [hgamma_m1]
    have hGm : Real.Gamma (m : ℝ) ≠ 0 :=
      ne_of_gt (Real.Gamma_pos_of_pos hmR)
    field_simp
  unfold realGinibreExpectedCountClosedForm
  change
    (1 / 2 + Real.sqrt (2 / Real.pi) *
        (Real.Gamma (((m + 2 : ℕ) : ℝ) + 1 / 2) /
          Real.Gamma ((m + 2 : ℕ) : ℝ)) * H₂) -
      (1 / 2 + Real.sqrt (2 / Real.pi) *
        (Real.Gamma ((m : ℝ) + 1 / 2) / Real.Gamma (m : ℝ)) * H₀) = _
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  rw [hratio2]
  calc
    (1 / 2 + Real.sqrt (2 / Real.pi) *
          ((Real.Gamma ((m : ℝ) + 1 / 2) / Real.Gamma (m : ℝ)) * a) * H₂) -
        (1 / 2 + Real.sqrt (2 / Real.pi) *
          (Real.Gamma ((m : ℝ) + 1 / 2) / Real.Gamma (m : ℝ)) * H₀) =
      Real.sqrt (2 / Real.pi) *
        (Real.Gamma ((m : ℝ) + 1 / 2) / Real.Gamma (m : ℝ)) *
          (a * H₂ - H₀) := by ring
    _ = Real.sqrt (2 / Real.pi) *
        (Real.Gamma ((m : ℝ) + 1 / 2) / Real.Gamma (m : ℝ)) *
          (1 / (m : ℝ)) := by rw [hhyper]
    _ = Real.sqrt (2 / Real.pi) *
        (Real.Gamma ((m : ℝ) + 1 / 2) /
          Real.Gamma ((m : ℝ) + 1)) := by
      rw [mul_assoc, hratio1]

/-- Every real `1 × 1` matrix has exactly one algebraic real eigenvalue. -/
theorem realEigenvalueCount_one (A : RSqMat 1) :
    realEigenvalueCount 1 A = 1 := by
  unfold realEigenvalueCount
  rw [show Matrix.charpoly A = Polynomial.X - Polynomial.C (A 0 0) by
    rw [Matrix.charpoly]
    simp]
  rw [Polynomial.roots_X_sub_C]
  simp

/-- The standard real-Ginibre expected real-eigenvalue count is exactly one
in dimension one. -/
theorem expectedRealEigenvalueCount_one :
    expectedRealEigenvalueCount 1 = 1 := by
  unfold expectedRealEigenvalueCount
  simp_rw [realEigenvalueCount_one]
  simp only [integral_const, one_smul, measureReal_def,
    realGinibreMeasure_univ, ENNReal.toReal_one]
  norm_num

/-- The finite real-Ginibre expectation formula holds unconditionally in
dimension one. -/
theorem expectedRealEigenvalueCount_eq_closedForm_one :
    expectedRealEigenvalueCount 1 = realGinibreExpectedCountClosedForm 1 := by
  rw [expectedRealEigenvalueCount_one,
    realGinibreExpectedCountClosedForm_one]

end NumStability
