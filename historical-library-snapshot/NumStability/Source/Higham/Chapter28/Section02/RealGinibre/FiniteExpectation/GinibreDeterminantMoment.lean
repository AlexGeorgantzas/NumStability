import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Probability.Gaussian.AbsoluteMoment

/-!
# Chapter28 Section02 RealGinibre FiniteExpectation GinibreDeterminantMoment

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

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

end NumStability

end
