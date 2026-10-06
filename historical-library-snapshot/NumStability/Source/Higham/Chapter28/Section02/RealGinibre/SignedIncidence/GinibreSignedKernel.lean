import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedGaussian
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedScalar

/-!
# Chapter28 Section02 RealGinibre SignedIncidence GinibreSignedKernel

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreSignedKernel` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory Set

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

end NumStability

end
