import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Sym.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Probability.Gaussian.AbsoluteMoment
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreDeterminantMoment

/-!
# Chapter28 Section02 RealGinibre FiniteExpectation GinibreExpectationGlue

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreExpectationGlue` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

/-- Multiplying the determinant-moment increment by the Corollary 3.1
normalization produces the Gamma-ratio increment in the expected-count
recurrence. -/
theorem ginibreCorollary31Factor_mul_increment (m : ℕ) (hm : 0 < m) :
    ginibreCorollary31Factor (m + 1) *
        ginibreAbsoluteCharacteristicMomentIncrement m =
      Real.sqrt (2 / Real.pi) *
        (Real.Gamma ((m : ℝ) - 1 / 2) / Real.Gamma (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hGm : Real.Gamma (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos hmR)
  have hGhalf : Real.Gamma ((m : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hGhalf' : Real.Gamma ((m : ℝ) / 2 + 1 / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have hpow : Real.rpow 2 ((3 - (m : ℝ)) / 2) /
        Real.rpow 2 ((m : ℝ) / 2) =
      Real.sqrt 2 * Real.rpow 2 (1 - (m : ℝ)) := by
    change (2 : ℝ) ^ ((3 - (m : ℝ)) / 2) /
        (2 : ℝ) ^ ((m : ℝ) / 2) =
      Real.sqrt 2 * (2 : ℝ) ^ (1 - (m : ℝ))
    calc
      (2 : ℝ) ^ ((3 - (m : ℝ)) / 2) /
          (2 : ℝ) ^ ((m : ℝ) / 2) =
          (2 : ℝ) ^ (((3 - (m : ℝ)) / 2) - ((m : ℝ) / 2)) :=
        (Real.rpow_sub (by norm_num : (0 : ℝ) < 2) _ _).symm
      _ = (2 : ℝ) ^ ((1 / 2 : ℝ) + (1 - (m : ℝ))) := by
        congr 1
        ring
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 - (m : ℝ)) := by
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
      _ = Real.sqrt 2 * (2 : ℝ) ^ (1 - (m : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
  have hdup := Real.Gamma_mul_Gamma_add_half ((m : ℝ) / 2)
  have htwo : 2 * ((m : ℝ) / 2) = (m : ℝ) := by ring
  rw [htwo] at hdup
  change Real.Gamma ((m : ℝ) / 2) *
      Real.Gamma ((m : ℝ) / 2 + 1 / 2) =
    Real.Gamma (m : ℝ) * Real.rpow 2 (1 - (m : ℝ)) *
      Real.sqrt Real.pi at hdup
  have hsqrtRatio : Real.sqrt (2 / Real.pi) =
      Real.sqrt 2 / Real.sqrt Real.pi := by
    rw [Real.sqrt_div (by positivity : 0 ≤ (2 : ℝ))]
  unfold ginibreCorollary31Factor
  unfold ginibreAbsoluteCharacteristicMomentIncrement
  push_cast
  rw [show ((m : ℝ) + 1 - 1) / 2 = (m : ℝ) / 2 by ring]
  rw [show ((m : ℝ) + 1) / 2 = (m : ℝ) / 2 + 1 / 2 by ring]
  rw [hsqrtRatio]
  have hpow0 : Real.rpow 2 ((m : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hpow1 : Real.rpow 2 (1 - (m : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hmge : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hGshift : Real.Gamma ((m : ℝ) - 1 / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  field_simp [hGm, hGhalf, hGhalf', hsqrtPi, hpow0, hpow1, hGshift]
  rw [show ((m : ℝ) * 2 - 1) / 2 = (m : ℝ) - 1 / 2 by ring]
  rw [show ((m : ℝ) + 1) / 2 = (m : ℝ) / 2 + 1 / 2 by ring]
  have hpowCross : Real.rpow 2 ((3 - (m : ℝ)) / 2) =
      Real.sqrt 2 * Real.rpow 2 (1 - (m : ℝ)) *
        Real.rpow 2 ((m : ℝ) / 2) :=
    (div_eq_iff hpow0).mp hpow
  calc
    Real.sqrt Real.pi * Real.rpow 2 ((3 - (m : ℝ)) / 2) *
          Real.Gamma ((m : ℝ) - 1 / 2) * Real.Gamma (m : ℝ) =
        Real.sqrt 2 * Real.rpow 2 ((m : ℝ) / 2) *
          Real.Gamma ((m : ℝ) - 1 / 2) *
            (Real.Gamma (m : ℝ) * Real.rpow 2 (1 - (m : ℝ)) *
              Real.sqrt Real.pi) := by
      rw [hpowCross]
      ring
    _ = Real.sqrt 2 * Real.rpow 2 ((m : ℝ) / 2) *
          Real.Gamma ((m : ℝ) - 1 / 2) *
            (Real.Gamma ((m : ℝ) / 2) *
              Real.Gamma ((m : ℝ) / 2 + 1 / 2)) := by
      rw [hdup]
    _ = Real.rpow 2 ((m : ℝ) / 2) *
          Real.Gamma ((m : ℝ) / 2 + 1 / 2) *
          Real.Gamma ((m : ℝ) - 1 / 2) *
          Real.Gamma ((m : ℝ) / 2) * Real.sqrt 2 := by
      ring

end NumStability

end
