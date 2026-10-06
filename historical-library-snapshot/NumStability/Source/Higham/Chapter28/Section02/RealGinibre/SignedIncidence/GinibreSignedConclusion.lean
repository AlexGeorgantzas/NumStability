import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Sym.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Probability.Gaussian.AbsoluteMoment
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreDeterminantMoment

/-!
# Chapter28 Section02 RealGinibre SignedIncidence GinibreSignedConclusion

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreSignedConclusion` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open Filter

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

end NumStability

end
