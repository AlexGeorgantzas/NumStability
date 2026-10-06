import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter28 Section02 RealGinibre ProbabilityLaw GinibreJointDensity

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreJointDensity` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

/-- Integrability of the finite standard-Gaussian vector density. -/
theorem integrable_standardGaussianVectorDensity (n : ℕ) :
    Integrable (fun z : Fin n → ℝ =>
      ∏ i : Fin n, gaussianPDFReal 0 1 (z i)) :=
  Integrable.fintype_prod (fun _ : Fin n =>
    integrable_gaussianPDFReal 0 1)

/-- The product density of a finite standard-Gaussian vector has ordinary
Lebesgue integral one. -/
theorem integral_standardGaussianVectorDensity_eq_one (n : ℕ) :
    (∫ z : Fin n → ℝ,
      ∏ i : Fin n, gaussianPDFReal 0 1 (z i)) = 1 := by
  rw [integral_fintype_prod_volume_eq_prod]
  simp [integral_gaussianPDFReal_eq_one]

end NumStability

end
