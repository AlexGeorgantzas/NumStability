import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import Mathlib.Analysis.SpecialFunctions.Stirling
import NumStability.Analysis.TestMatrices.Hilbert.Asymptotics
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Asymptotics.Asymptotics
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter26.IntervalArithmetic.ExactOperations
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreExpectationGlue
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreRecurrence
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.ProductLaw
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreParity

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28Ginibre, NumStability.Algorithms.TestMatrices.Higham28GinibreExpectationGlue, NumStability.Algorithms.TestMatrices.Higham28GinibreParity, NumStability.Algorithms.TestMatrices.Higham28GinibreRecurrence under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open Filter Asymptotics Polynomial MeasureTheory

private local instance instMeasurableSpaceRSqMat_2_relocated_ClosedFormAsymptotics (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

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

namespace NumStability

open Filter Asymptotics Polynomial MeasureTheory ProbabilityTheory

open scoped ENNReal BigOperators

local instance instMeasurableSpaceRSqMat_4 (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

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

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

/-- The normalized determinant-moment increment is exactly the two-step
increment of the finite real-Ginibre closed form. -/
theorem ginibreCorollary31Factor_mul_increment_eq_closedForm_shift
    (m : ℕ) (hm : 0 < m) :
    ginibreCorollary31Factor (m + 2) *
        ginibreAbsoluteCharacteristicMomentIncrement (m + 1) =
      realGinibreExpectedCountClosedForm (m + 2) -
        realGinibreExpectedCountClosedForm m := by
  rw [ginibreCorollary31Factor_mul_increment (m + 1) (Nat.zero_lt_succ m)]
  push_cast
  rw [show (m : ℝ) + 1 - 1 / 2 = (m : ℝ) + 1 / 2 by ring]
  exact (realGinibreExpectedCountClosedForm_shift_two m hm).symm

end NumStability

end

namespace NumStability

open Filter Asymptotics Polynomial MeasureTheory ProbabilityTheory

open scoped ENNReal BigOperators

private theorem hasSum_real_binomialSeries
    (a x : ℝ) (hx : |x| < 1) :
    HasSum (fun k : ℕ => Ring.choose a k * x ^ k) ((1 + x) ^ a) := by
  have hs := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum
    (show x ∈ Metric.eball (0 : ℝ) 1 by
      simpa [enorm_eq_nnnorm, Real.norm_eq_abs] using hx)
  simpa [binomialSeries, mul_comm] using hs

private theorem ringChoose_succ_mul (a : ℝ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * Ring.choose a (k + 1) =
      (a - k) * Ring.choose a k := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  rw [descPochhammer_succ_right, Polynomial.smeval_mul]
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast]
  rw [Nat.factorial_succ]
  push_cast
  have hk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  simp [nsmul_eq_mul]

/-- The `n = 2` hypergeometric coefficient is a shifted coefficient of the
binomial series with exponent `3/2`. -/
theorem ginibreHypergeometricTerm_two_eq_binomialTail (k : ℕ) :
    ginibreHypergeometricTerm 2 k =
      -(4 / 3 : ℝ) *
        (Ring.choose (3 / 2 : ℝ) (k + 1) * (-1 / 2 : ℝ) ^ (k + 1)) := by
  induction k with
  | zero =>
      simp [ginibreHypergeometricTerm_zero]
      norm_num
  | succ k ih =>
      rw [ginibreHypergeometricTerm_succ, ih]
      rw [show k + 1 + 1 = k + 2 by omega]
      rw [pow_succ]
      have hchoose := ringChoose_succ_mul (3 / 2 : ℝ) (k + 1)
      push_cast at hchoose ⊢
      have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
      have hchoose' :
          Ring.choose (3 / 2 : ℝ) (k + 2) =
            ((1 / 2 : ℝ) - k) * Ring.choose (3 / 2 : ℝ) (k + 1) /
              ((k : ℝ) + 2) := by
        apply (eq_div_iff hk2).2
        rw [mul_comm]
        convert hchoose using 1 <;> ring
      rw [hchoose']
      rw [show (-1 / 2 : ℝ) ^ (k + 2) =
        (-1 / 2 : ℝ) ^ k * (-1 / 2 : ℝ) ^ 2 by rw [pow_add]]
      field_simp
      ring

/-- Exact scalar hypergeometric value in dimension two. -/
theorem realGinibre_hypergeometric_two :
    ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (2 : ℝ) (1 / 2 : ℝ) =
      (4 / 3 : ℝ) * (1 - (1 / 2 : ℝ) ^ (3 / 2 : ℝ)) := by
  let b : ℕ → ℝ := fun k =>
    Ring.choose (3 / 2 : ℝ) k * (-1 / 2 : ℝ) ^ k
  have hb : HasSum b ((1 + (-1 / 2 : ℝ)) ^ (3 / 2 : ℝ)) := by
    simpa only [b] using
      hasSum_real_binomialSeries (3 / 2 : ℝ) (-1 / 2 : ℝ) (by norm_num)
  have hsplit :
      (∑' k : ℕ, b k) = b 0 + ∑' k : ℕ, b (k + 1) := by
    simpa using (hb.summable.sum_add_tsum_nat_add 1).symm
  have htail :
      (∑' k : ℕ, b (k + 1)) =
        (1 / 2 : ℝ) ^ (3 / 2 : ℝ) - 1 := by
    rw [hb.tsum_eq] at hsplit
    have hb0 : b 0 = 1 := by simp [b]
    rw [hb0] at hsplit
    norm_num at hsplit ⊢
    linarith
  calc
    ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (2 : ℝ) (1 / 2 : ℝ) =
        ∑' k : ℕ, ginibreHypergeometricTerm 2 k := by
          convert realGinibre_hypergeometric_eq_tsum 2 using 1
    _ = ∑' k : ℕ, -(4 / 3 : ℝ) * b (k + 1) := by
      apply tsum_congr
      intro k
      simpa only [b] using ginibreHypergeometricTerm_two_eq_binomialTail k
    _ = -(4 / 3 : ℝ) * ∑' k : ℕ, b (k + 1) := by
      rw [tsum_mul_left]
    _ = (4 / 3 : ℝ) * (1 - (1 / 2 : ℝ) ^ (3 / 2 : ℝ)) := by
      rw [htail]
      ring

private theorem one_half_rpow_three_halves :
    (1 / 2 : ℝ) ^ (3 / 2 : ℝ) =
      (1 / 2 : ℝ) * Real.sqrt (1 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

private theorem sqrt_two_mul_sqrt_one_half :
    Real.sqrt 2 * Real.sqrt (1 / 2 : ℝ) = 1 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem sqrt_two_mul_one_half_rpow_three_halves :
    Real.sqrt 2 * (1 / 2 : ℝ) ^ (3 / 2 : ℝ) = 1 / 2 := by
  rw [one_half_rpow_three_halves]
  calc
    Real.sqrt 2 * ((1 / 2 : ℝ) * Real.sqrt (1 / 2 : ℝ)) =
        (1 / 2 : ℝ) * (Real.sqrt 2 * Real.sqrt (1 / 2 : ℝ)) := by ring
    _ = 1 / 2 := by rw [sqrt_two_mul_sqrt_one_half]; ring

private theorem sqrt_two_div_pi_mul_sqrt_pi :
    Real.sqrt (2 / Real.pi) * Real.sqrt Real.pi = Real.sqrt 2 := by
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
  congr 1
  field_simp [ne_of_gt Real.pi_pos]

private theorem realGamma_five_halves_div_two :
    Real.Gamma (2 + 1 / 2 : ℝ) / Real.Gamma 2 =
      (3 / 4 : ℝ) * Real.sqrt Real.pi := by
  rw [show (2 + 1 / 2 : ℝ) = (1 / 2 + 1) + 1 by ring]
  rw [Real.Gamma_add_one (by norm_num : (1 / 2 + 1 : ℝ) ≠ 0)]
  rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [Real.Gamma_one_half_eq]
  have hgammaTwo : Real.Gamma (2 : ℝ) = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  rw [hgammaTwo]
  ring

/-- Exact two-dimensional base value for the finite real-Ginibre closed form. -/
theorem realGinibreExpectedCountClosedForm_two :
    realGinibreExpectedCountClosedForm 2 = Real.sqrt 2 := by
  unfold realGinibreExpectedCountClosedForm
  norm_num only [Nat.cast_ofNat]
  rw [show (-(1 / 2) : ℝ) = (-1 / 2 : ℝ) by ring]
  rw [realGinibre_hypergeometric_two]
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by ring]
  rw [realGamma_five_halves_div_two]
  rw [show Real.sqrt (2 / Real.pi) * ((3 / 4 : ℝ) * Real.sqrt Real.pi) *
      ((4 / 3 : ℝ) * (1 - (1 / 2 : ℝ) ^ (3 / 2 : ℝ))) =
      (Real.sqrt (2 / Real.pi) * Real.sqrt Real.pi) *
        (1 - (1 / 2 : ℝ) ^ (3 / 2 : ℝ)) by ring]
  rw [sqrt_two_div_pi_mul_sqrt_pi]
  rw [mul_sub, mul_one, sqrt_two_mul_one_half_rpow_three_halves]
  ring

@[simp]
theorem realGinibreParityIncrement_zero :
    realGinibreParityIncrement 0 = Real.sqrt 2 := by
  rw [realGinibreParityIncrement]
  norm_num only [Nat.cast_zero, zero_add]
  rw [Real.Gamma_one_half_eq]
  have hgammaOne : Real.Gamma (1 : ℝ) = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 0
  rw [hgammaOne, div_one, sqrt_two_div_pi_mul_sqrt_pi]

private theorem realGinibreExpectedCountClosedForm_add_increment
    (m : ℕ) (hm : 0 < m) :
    realGinibreExpectedCountClosedForm (m + 2) =
      realGinibreExpectedCountClosedForm m + realGinibreParityIncrement m := by
  have h := realGinibreExpectedCountClosedForm_shift_two m hm
  rw [realGinibreParityIncrement]
  linarith

/-- Hypergeometric-free finite sum for every odd dimension. -/
theorem realGinibreExpectedCountClosedForm_odd_finiteSum (r : ℕ) :
    realGinibreExpectedCountClosedForm (2 * r + 1) =
      1 + ∑ j ∈ Finset.range r, realGinibreParityIncrement (2 * j + 1) := by
  induction r with
  | zero =>
      simpa using realGinibreExpectedCountClosedForm_one
  | succ r ih =>
      rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega]
      rw [realGinibreExpectedCountClosedForm_add_increment (2 * r + 1) (by omega)]
      rw [ih, Finset.sum_range_succ]
      ring

/-- Hypergeometric-free finite sum for every positive even dimension.  The
`j = 0` summand is the exact two-dimensional base value `sqrt 2`. -/
theorem realGinibreExpectedCountClosedForm_even_finiteSum (r : ℕ) :
    realGinibreExpectedCountClosedForm (2 * r + 2) =
      ∑ j ∈ Finset.range (r + 1), realGinibreParityIncrement (2 * j) := by
  induction r with
  | zero =>
      simp [realGinibreExpectedCountClosedForm_two]
  | succ r ih =>
      calc
        realGinibreExpectedCountClosedForm (2 * (r + 1) + 2) =
            realGinibreExpectedCountClosedForm (2 * r + 2) +
              realGinibreParityIncrement (2 * r + 2) := by
                rw [show 2 * (r + 1) + 2 = (2 * r + 2) + 2 by omega]
                exact realGinibreExpectedCountClosedForm_add_increment
                  (2 * r + 2) (by omega)
        _ = (∑ j ∈ Finset.range (r + 1), realGinibreParityIncrement (2 * j)) +
              realGinibreParityIncrement (2 * r + 2) := by rw [ih]
        _ = ∑ j ∈ Finset.range ((r + 1) + 1),
              realGinibreParityIncrement (2 * j) := by
                conv_rhs => rw [Finset.sum_range_succ]
                congr 2

/-- Expanded odd-parity Gamma sum, with no auxiliary recurrence notation. -/
theorem realGinibreExpectedCountClosedForm_odd_gammaSum (r : ℕ) :
    realGinibreExpectedCountClosedForm (2 * r + 1) =
      1 + ∑ j ∈ Finset.range r,
        Real.sqrt (2 / Real.pi) *
          (Real.Gamma (((2 * j + 1 : ℕ) : ℝ) + 1 / 2) /
            Real.Gamma (((2 * j + 1 : ℕ) : ℝ) + 1)) := by
  simpa only [realGinibreParityIncrement] using
    realGinibreExpectedCountClosedForm_odd_finiteSum r

/-- Expanded positive even-parity Gamma sum, with no auxiliary recurrence
notation. -/
theorem realGinibreExpectedCountClosedForm_even_gammaSum (r : ℕ) :
    realGinibreExpectedCountClosedForm (2 * r + 2) =
      ∑ j ∈ Finset.range (r + 1),
        Real.sqrt (2 / Real.pi) *
          (Real.Gamma (((2 * j : ℕ) : ℝ) + 1 / 2) /
            Real.Gamma (((2 * j : ℕ) : ℝ) + 1)) := by
  simpa only [realGinibreParityIncrement] using
    realGinibreExpectedCountClosedForm_even_finiteSum r

end NumStability
