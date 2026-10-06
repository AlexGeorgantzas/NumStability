import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Probability.Gaussian.AbsoluteMoment
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.GinibreMeasure

/-!
# Chapter28 Section02 RealGinibre ProbabilityLaw GinibreTraceDensity

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28GinibreTraceDensity` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

/-- The sum of squares of all entries of a real square matrix. -/
def ginibreMatrixSq (n : ℕ) (A : RSqMat n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2

/-- The quadratic form in the marginal law of `A - λI`. -/
def ginibreTraceQuadratic (n : ℕ) (B : RSqMat n) : ℝ :=
  ginibreMatrixSq n B - (Matrix.trace B) ^ 2 / (n + 1 : ℝ)

/-- Completing the square in the independent scalar Gaussian shift. -/
theorem ginibre_shift_completeSquare (n : ℕ) (B : RSqMat n) (x : ℝ) :
    ginibreMatrixSq n (B + x • (1 : RSqMat n)) + x ^ 2 =
      ginibreTraceQuadratic n B +
        (n + 1 : ℝ) * (x + Matrix.trace B / (n + 1 : ℝ)) ^ 2 := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hcross :
      (∑ i : Fin n, ∑ j : Fin n, B i j * (1 : RSqMat n) i j) = Matrix.trace B := by
    classical
    simp [Matrix.trace, Matrix.one_apply]
  have hone :
      (∑ i : Fin n, ∑ j : Fin n, ((1 : RSqMat n) i j) ^ 2) = (n : ℝ) := by
    classical
    simp [Matrix.one_apply]
  have hcross' :
      (∑ i : Fin n, ∑ j : Fin n,
        2 * x * (B i j * (1 : RSqMat n) i j)) = 2 * x * Matrix.trace B := by
    simp_rw [← Finset.mul_sum]
    rw [hcross]
  have hone' :
      (∑ i : Fin n, ∑ j : Fin n,
        x ^ 2 * ((1 : RSqMat n) i j) ^ 2) = x ^ 2 * n := by
    simp_rw [← Finset.mul_sum]
    rw [hone]
  unfold ginibreTraceQuadratic
  unfold ginibreMatrixSq
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    show (B i j + x * (1 : RSqMat n) i j) ^ 2 =
      B i j ^ 2 + 2 * x * (B i j * (1 : RSqMat n) i j) +
        x ^ 2 * ((1 : RSqMat n) i j) ^ 2 by ring))]
  simp_rw [Finset.sum_add_distrib]
  rw [hcross', hone']
  field_simp
  ring

/-- Orthogonal projection onto the traceless matrix hyperplane. -/
def ginibreTracelessPart (n : ℕ) (B : RSqMat n) : RSqMat n :=
  B - (Matrix.trace B / (n : ℝ)) • (1 : RSqMat n)

theorem trace_ginibreTracelessPart (n : ℕ) (hn : 0 < n) (B : RSqMat n) :
    Matrix.trace (ginibreTracelessPart n B) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [ginibreTracelessPart, Matrix.trace]
  field_simp
  ring

/-- The trace-correlated precision splits orthogonally into a standard
traceless part and a one-dimensional trace of variance `n(n+1)`. -/
theorem ginibreTraceQuadratic_eq_traceless_add_trace (n : ℕ) (hn : 0 < n)
    (B : RSqMat n) :
    ginibreTraceQuadratic n B =
      ginibreMatrixSq n (ginibreTracelessPart n B) +
        Matrix.trace B ^ 2 / ((n : ℝ) * (n + 1 : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn10 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hs := ginibre_shift_completeSquare n B
    (-(Matrix.trace B / (n : ℝ)))
  have hmat : B + (-(Matrix.trace B / (n : ℝ))) • (1 : RSqMat n) =
      ginibreTracelessPart n B := by
    unfold ginibreTracelessPart
    ext i j
    simp [sub_eq_add_neg]
  rw [hmat] at hs
  field_simp at hs ⊢
  ring_nf at hs ⊢
  nlinarith

/-- Closed exponential form of the standard real-Ginibre density. -/
theorem realGinibreDensityReal_eq_exp (n : ℕ) (A : RSqMat n) :
    realGinibreDensityReal n A =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ (n * n) *
        Real.exp (-(ginibreMatrixSq n A) / 2) := by
  unfold realGinibreDensityReal ginibreMatrixSq
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  simp_rw [Finset.prod_mul_distrib]
  simp_rw [← Real.exp_sum]
  congr 1
  · simp [pow_mul]
  · congr 1
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    congr with i
    rw [← Finset.sum_neg_distrib, Finset.sum_div]

/-- Translation does not alter the elementary one-dimensional Gaussian integral. -/
theorem integral_exp_neg_mul_add_sq (b a : ℝ) :
    (∫ x : ℝ, Real.exp (-b * (x + a) ^ 2)) = Real.sqrt (Real.pi / b) := by
  rw [integral_add_right_eq_self (fun x : ℝ => Real.exp (-b * x ^ 2)) a]
  exact integral_gaussian b

theorem inv_sqrt_two_pi_mul_shiftGaussianIntegral (n : ℕ) :
    (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / ((n + 1 : ℝ) / 2)) =
      (Real.sqrt (n + 1 : ℝ))⁻¹ := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  rw [show Real.pi / ((n + 1 : ℝ) / 2) =
      (2 * Real.pi) / (n + 1 : ℝ) by field_simp]
  rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

/-- The exact marginal density of a Ginibre matrix minus an independent
standard scalar Gaussian times the identity. -/
noncomputable def ginibreTraceCorrelatedDensityReal (n : ℕ) (B : RSqMat n) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ (n * n) *
    (Real.exp (-(ginibreTraceQuadratic n B) / 2) /
      Real.sqrt (n + 1 : ℝ))

theorem ginibreTraceCorrelatedDensityReal_pos (n : ℕ) (B : RSqMat n) :
    0 < ginibreTraceCorrelatedDensityReal n B := by
  unfold ginibreTraceCorrelatedDensityReal
  positivity

/-- Factorization of the correlated exponential into independent traceless
and scalar-trace factors. -/
theorem ginibreTraceCorrelatedDensityReal_factor_traceless (n : ℕ) (hn : 0 < n)
    (B : RSqMat n) :
    ginibreTraceCorrelatedDensityReal n B =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ (n * n) *
        ((Real.exp (-(ginibreMatrixSq n (ginibreTracelessPart n B)) / 2) *
            Real.exp (-(Matrix.trace B ^ 2) /
              (2 * (n : ℝ) * (n + 1 : ℝ)))) /
          Real.sqrt (n + 1 : ℝ)) := by
  unfold ginibreTraceCorrelatedDensityReal
  rw [ginibreTraceQuadratic_eq_traceless_add_trace n hn B]
  rw [show -(ginibreMatrixSq n (ginibreTracelessPart n B) +
          Matrix.trace B ^ 2 / ((n : ℝ) * (n + 1 : ℝ))) / 2 =
        -(ginibreMatrixSq n (ginibreTracelessPart n B)) / 2 +
          -(Matrix.trace B ^ 2) / (2 * (n : ℝ) * (n + 1 : ℝ)) by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hn10 : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring]
  rw [Real.exp_add]

theorem ginibreShiftJointDensity_eq (n : ℕ) (B : RSqMat n) (x : ℝ) :
    realGinibreDensityReal n (B + x • (1 : RSqMat n)) *
        gaussianPDFReal 0 1 x =
      (((Real.sqrt (2 * Real.pi))⁻¹ ^ (n * n + 1) *
          Real.exp (-(ginibreTraceQuadratic n B) / 2)) *
        Real.exp (-((n + 1 : ℝ) / 2) *
          (x + Matrix.trace B / (n + 1 : ℝ)) ^ 2)) := by
  rw [realGinibreDensityReal_eq_exp]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [show (Real.sqrt (2 * Real.pi))⁻¹ ^ (n * n) *
      Real.exp (-(ginibreMatrixSq n (B + x • (1 : RSqMat n))) / 2) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) =
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ (n * n) *
        (Real.sqrt (2 * Real.pi))⁻¹) *
        (Real.exp (-(ginibreMatrixSq n (B + x • (1 : RSqMat n))) / 2) *
          Real.exp (-(x ^ 2) / 2)) by ring]
  rw [← Real.exp_add]
  rw [show -(ginibreMatrixSq n (B + x • (1 : RSqMat n))) / 2 +
      (-(x ^ 2) / 2) =
        -(ginibreTraceQuadratic n B) / 2 +
          -((n + 1 : ℝ) / 2) *
            (x + Matrix.trace B / (n + 1 : ℝ)) ^ 2 by
    linarith [ginibre_shift_completeSquare n B x]]
  rw [Real.exp_add, pow_succ']
  ring

theorem integrable_ginibreShiftJointDensity (n : ℕ) (B : RSqMat n) :
    Integrable (fun x : ℝ =>
      realGinibreDensityReal n (B + x • (1 : RSqMat n)) *
        gaussianPDFReal 0 1 x) := by
  rw [show (fun x : ℝ =>
      realGinibreDensityReal n (B + x • (1 : RSqMat n)) *
        gaussianPDFReal 0 1 x) =
      fun x : ℝ =>
        (((Real.sqrt (2 * Real.pi))⁻¹ ^ (n * n + 1) *
            Real.exp (-(ginibreTraceQuadratic n B) / 2)) *
          Real.exp (-((n + 1 : ℝ) / 2) *
            (x + Matrix.trace B / (n + 1 : ℝ)) ^ 2)) by
    funext x
    exact ginibreShiftJointDensity_eq n B x]
  exact ((integrable_exp_neg_mul_sq (by positivity :
      (0 : ℝ) < (n + 1 : ℝ) / 2)).comp_add_right
        (Matrix.trace B / (n + 1 : ℝ))).const_mul _

/-- Integrating the shifted joint Gaussian density over the scalar gives the
trace-correlated density, including its `1 / sqrt (n+1)` normalization. -/
theorem integral_ginibreShiftJointDensity (n : ℕ) (B : RSqMat n) :
    (∫ x : ℝ,
        realGinibreDensityReal n (B + x • (1 : RSqMat n)) *
          gaussianPDFReal 0 1 x) =
      ginibreTraceCorrelatedDensityReal n B := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  let q : ℝ := ginibreTraceQuadratic n B
  let a : ℝ := Matrix.trace B / (n + 1 : ℝ)
  let b : ℝ := (n + 1 : ℝ) / 2
  have hpoint :
      (fun x : ℝ =>
        realGinibreDensityReal n (B + x • (1 : RSqMat n)) *
          gaussianPDFReal 0 1 x) =
      fun x : ℝ =>
        (c ^ (n * n + 1) * Real.exp (-q / 2)) *
          Real.exp (-b * (x + a) ^ 2) := by
    funext x
    simpa only [c, q, b] using ginibreShiftJointDensity_eq n B x
  rw [hpoint, integral_const_mul, integral_exp_neg_mul_add_sq]
  unfold ginibreTraceCorrelatedDensityReal
  simp only [c, q, b]
  rw [pow_succ']
  rw [show (Real.sqrt (2 * Real.pi))⁻¹ *
      (Real.sqrt (2 * Real.pi))⁻¹ ^ (n * n) *
        Real.exp (-ginibreTraceQuadratic n B / 2) *
          Real.sqrt (Real.pi / ((n + 1 : ℝ) / 2)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ (n * n) *
        Real.exp (-ginibreTraceQuadratic n B / 2) *
          ((Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi / ((n + 1 : ℝ) / 2)) ) by ring]
  rw [inv_sqrt_two_pi_mul_shiftGaussianIntegral]
  ring

theorem lintegral_ginibreShiftJointDensity (n : ℕ) (B : RSqMat n) :
    (∫⁻ x : ℝ, ENNReal.ofReal
      (realGinibreDensityReal n (B + x • (1 : RSqMat n)) *
        gaussianPDFReal 0 1 x)) =
      ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_ginibreShiftJointDensity n B)
    (ae_of_all _ fun x => mul_nonneg
      (le_of_lt (realGinibreDensityReal_pos n _))
      (gaussianPDFReal_nonneg 0 1 x))]
  rw [integral_ginibreShiftJointDensity]

/-- The unit-Jacobian shear implementing `B = A - xI`. -/
def ginibreShiftShear (n : ℕ) (p : RSqMat n × ℝ) : RSqMat n × ℝ :=
  (p.1 - p.2 • (1 : RSqMat n), p.2)

/-- The inverse shear, implementing `A = B + xI`. -/
def ginibreUnshiftShear (n : ℕ) (p : RSqMat n × ℝ) : RSqMat n × ℝ :=
  (p.1 + p.2 • (1 : RSqMat n), p.2)

theorem ginibreShiftShear_leftInverse (n : ℕ) :
    Function.LeftInverse (ginibreUnshiftShear n) (ginibreShiftShear n) := by
  intro p
  ext <;> simp [ginibreShiftShear, ginibreUnshiftShear]

theorem ginibreShiftShear_rightInverse (n : ℕ) :
    Function.RightInverse (ginibreUnshiftShear n) (ginibreShiftShear n) := by
  intro p
  ext <;> simp [ginibreShiftShear, ginibreUnshiftShear]

end NumStability

end
