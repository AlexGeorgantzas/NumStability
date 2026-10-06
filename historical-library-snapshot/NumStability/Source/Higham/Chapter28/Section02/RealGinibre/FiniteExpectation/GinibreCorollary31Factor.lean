import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Probability.Gaussian.AbsoluteMoment
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreDeterminantMoment

/-!
# Chapter28 Section02 RealGinibre FiniteExpectation GinibreCorollary31Factor

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreCorollary31Factor` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped BigOperators

/-- The standard real Gaussian density at zero. -/
theorem gaussianPDFReal_zero_one_zero :
    gaussianPDFReal 0 1 0 = 1 / Real.sqrt (2 * Real.pi) := by
  simp [gaussianPDFReal]

/-- The transverse Gaussian normalization times the projective-chart
normalization is the universal Corollary 3.1 factor. -/
theorem gaussianZeroPow_mul_projectiveConstant (n : ℕ) :
    (gaussianPDFReal 0 1 0) ^ n *
        (Real.pi ^ (((n : ℝ) + 1) / 2) /
          Real.Gamma (((n : ℝ) + 1) / 2)) =
      ginibreCorollary31Factor (n + 1) := by
  rw [gaussianPDFReal_zero_one_zero]
  unfold ginibreCorollary31Factor
  push_cast
  have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 htwoPi)
  have hden : Real.sqrt (2 * Real.pi) ^ n =
      (2 : ℝ) ^ ((n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2) := by
    calc
      Real.sqrt (2 * Real.pi) ^ n =
          ((2 * Real.pi) ^ (1 / 2 : ℝ)) ^ n := by
        rw [Real.sqrt_eq_rpow]
      _ = ((2 * Real.pi) ^ (1 / 2 : ℝ)) ^ (n : ℝ) := by
        rw [Real.rpow_natCast]
      _ = (2 * Real.pi) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
        rw [Real.rpow_mul htwoPi.le]
      _ = (2 * Real.pi) ^ ((n : ℝ) / 2) := by
        congr 1
        ring
      _ = (2 : ℝ) ^ ((n : ℝ) / 2) *
          Real.pi ^ ((n : ℝ) / 2) := by
        rw [Real.mul_rpow (by norm_num) Real.pi_nonneg]
  have hnum : Real.pi ^ (((n : ℝ) + 1) / 2) =
      Real.pi ^ ((n : ℝ) / 2) * Real.sqrt Real.pi := by
    calc
      Real.pi ^ (((n : ℝ) + 1) / 2) =
          Real.pi ^ ((n : ℝ) / 2 + 1 / 2) := by
        congr 1
        ring
      _ = Real.pi ^ ((n : ℝ) / 2) * Real.pi ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_add Real.pi_pos]
      _ = _ := by rw [Real.sqrt_eq_rpow]
  rw [div_pow, one_pow, hden, hnum]
  have hpow2 : (2 : ℝ) ^ ((n : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hpowPi : Real.pi ^ ((n : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have hG : Real.Gamma (((n : ℝ) + 1) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  field_simp [hpow2, hpowPi, hG, hsqrt]
  congr 1
  ring

end NumStability

end
