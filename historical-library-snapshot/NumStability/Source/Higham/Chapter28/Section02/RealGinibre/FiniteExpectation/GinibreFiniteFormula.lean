import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
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
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.Instances.Matrix
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Probability.Gaussian.AbsoluteMoment
import NumStability.Analysis.Probability.Haar.HomogeneousSpaceUniqueness
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreCharacteristicProduct
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedGaussian

/-!
# Chapter28 Section02 RealGinibre FiniteExpectation GinibreFiniteFormula

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreFiniteFormula` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory Set Filter

/-- The value of the matrix characteristic-product moment at coincident
spectral parameters; equals `𝔼 det(B - u I)^2`. -/
def ch28gf_charProdVal (n : ℕ) (u : ℝ) : ℝ :=
  (n.factorial : ℝ) * ∑ k ∈ Finset.range (n + 1), (u * u) ^ k / (k.factorial : ℝ)

theorem ch28gf_charProdVal_nonneg (n : ℕ) (u : ℝ) :
    0 ≤ ch28gf_charProdVal n u := by
  unfold ch28gf_charProdVal
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro k hk
  exact div_nonneg (pow_nonneg (mul_self_nonneg u) k) (by positivity)

/-- Every even monomial is integrable under the standard Gaussian. -/
theorem ch28gf_integrable_mulSelf_pow (k : ℕ) :
    Integrable (fun u : ℝ => (u * u) ^ k) (gaussianReal 0 1) := by
  have h : (fun u : ℝ => (u * u) ^ k) = fun u : ℝ => u ^ (2 * k) := by
    funext u
    rw [show u * u = u ^ 2 from (pow_two u).symm, ← pow_mul]
  rw [h]
  exact integrable_standardGaussian_pow_all (2 * k)

/-- The coincident characteristic-product value is integrable in the spectral
parameter. -/
theorem ch28gf_integrable_charProdVal (n : ℕ) :
    Integrable (fun u : ℝ => ch28gf_charProdVal n u) (gaussianReal 0 1) := by
  unfold ch28gf_charProdVal
  apply Integrable.const_mul
  apply integrable_finset_sum
  intro k hk
  exact (ch28gf_integrable_mulSelf_pow k).div_const _

/-- Elementary scalar bound `|t| ≤ (1 + t²)/2`. -/
theorem ch28gf_abs_le_one_add_sq (t : ℝ) : |t| ≤ (1 + t ^ 2) / 2 := by
  nlinarith [sq_nonneg (|t| - 1), sq_abs t, abs_nonneg t]

theorem ch28gf_measurable_charProdVal (n : ℕ) :
    Measurable (fun u : ℝ => ch28gf_charProdVal n u) := by
  unfold ch28gf_charProdVal
  fun_prop

/-- `u² · charProd` is integrable in the spectral parameter. -/
theorem ch28gf_integrable_sq_mul_charProdVal (n : ℕ) :
    Integrable (fun u : ℝ => u ^ 2 * ch28gf_charProdVal n u) (gaussianReal 0 1) := by
  have hfun : (fun u : ℝ => u ^ 2 * ch28gf_charProdVal n u) =
      fun u : ℝ => (n.factorial : ℝ) *
        ∑ k ∈ Finset.range (n + 1), (u * u) ^ (k + 1) / (k.factorial : ℝ) := by
    funext u
    unfold ch28gf_charProdVal
    rw [← mul_assoc, mul_comm (u ^ 2) (n.factorial : ℝ), mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ (u * u) k]
    ring
  rw [hfun]
  apply Integrable.const_mul
  apply integrable_finset_sum
  intro k hk
  exact (ch28gf_integrable_mulSelf_pow (k + 1)).div_const _

/-- Scalar bound `|u| ≤ 1 + u²`. -/
theorem ch28gf_abs_le_one_add_sq' (u : ℝ) : |u| ≤ 1 + u ^ 2 := by
  nlinarith [sq_abs u, sq_nonneg (|u| - 1), abs_nonneg u]

/-- The `(|u|+|x|)/2` weight times the characteristic-product value is
integrable. -/
theorem ch28gf_integrable_hw (n : ℕ) (x : ℝ) :
    Integrable (fun u : ℝ => (|u| + |x|) / 2 * ch28gf_charProdVal n u)
      (gaussianReal 0 1) := by
  have hdom : Integrable
      (fun u : ℝ => (1 + |x|) / 2 * ch28gf_charProdVal n u +
        1 / 2 * (u ^ 2 * ch28gf_charProdVal n u)) (gaussianReal 0 1) :=
    ((ch28gf_integrable_charProdVal n).const_mul ((1 + |x|) / 2)).add
      ((ch28gf_integrable_sq_mul_charProdVal n).const_mul (1 / 2))
  have hfm : Measurable
      (fun u : ℝ => (|u| + |x|) / 2 * ch28gf_charProdVal n u) :=
    (by fun_prop : Measurable (fun u : ℝ => (|u| + |x|) / 2)).mul
      (ch28gf_measurable_charProdVal n)
  apply hdom.mono' hfm.aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (by positivity) (ch28gf_charProdVal_nonneg n u))]
  have hcp : 0 ≤ ch28gf_charProdVal n u := ch28gf_charProdVal_nonneg n u
  have hu : |u| ≤ 1 + u ^ 2 := ch28gf_abs_le_one_add_sq' u
  have key : 0 ≤ (1 + u ^ 2 - |u|) * ch28gf_charProdVal n u :=
    mul_nonneg (by linarith) hcp
  nlinarith [key, hcp]

/-- The `(|u|+|x|)/2` weight is integrable. -/
theorem ch28gf_integrable_absWgt (x : ℝ) :
    Integrable (fun u : ℝ => (|u| + |x|) / 2) (gaussianReal 0 1) := by
  letI : IsFiniteMeasure (gaussianReal 0 1) := inferInstance
  exact ((integrable_standardGaussian_id.abs).add (integrable_const |x|)).div_const 2

end NumStability

end
