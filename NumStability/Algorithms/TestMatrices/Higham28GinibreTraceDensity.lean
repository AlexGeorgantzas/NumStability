/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment
import NumStability.Algorithms.TestMatrices.Higham28GinibreMeasure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! # Higham Chapter 28: trace-correlated determinant density

This file performs the unconditional Gaussian change of variables
`B = A - x I` in the absolute characteristic determinant moment.  The shear
is proved to preserve matrix-by-scalar Lebesgue measure.  Completing the
scalar square and integrating it gives the exact marginal density

`(sqrt (2π))⁻¹^(n*n) * exp (-(‖B‖_F² - (tr B)²/(n+1))/2) / sqrt (n+1)`.

Both `lintegral` and ordinary-integral forms are connected directly to
`realGinibreAbsoluteCharacteristicMoment`; no determinant recurrence or
finite-dimensional expectation formula is assumed.  The quadratic form is
also factored into its traceless and scalar-trace directions.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

private local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi
private local instance (n : ℕ) : OpensMeasurableSpace (RSqMat n) :=
  Pi.opensMeasurableSpace
private local instance (n : ℕ) : BorelSpace (RSqMat n) := Pi.borelSpace

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

theorem measurable_ginibreTraceCorrelatedDensityReal (n : ℕ) :
    Measurable (ginibreTraceCorrelatedDensityReal n) := by
  unfold ginibreTraceCorrelatedDensityReal ginibreTraceQuadratic ginibreMatrixSq
  fun_prop

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

private local instance ginibreLebesgueSigmaFinite (n : ℕ) :
    SigmaFinite (realGinibreLebesgueMeasure n) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume)))
  infer_instance

private local instance ginibreLebesgueIsAddRightInvariant (n : ℕ) :
    (realGinibreLebesgueMeasure n).IsAddRightInvariant := by
  change Measure.IsAddRightInvariant (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => volume)))
  infer_instance

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

theorem measurable_ginibreShiftShear (n : ℕ) : Measurable (ginibreShiftShear n) := by
  apply Measurable.prodMk _ measurable_snd
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hij : Measurable (fun A : RSqMat n => A i j) := by fun_prop
  exact (hij.comp measurable_fst).sub
    (measurable_snd.mul measurable_const)

theorem measurable_ginibreUnshiftShear (n : ℕ) : Measurable (ginibreUnshiftShear n) := by
  apply Measurable.prodMk _ measurable_snd
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hij : Measurable (fun A : RSqMat n => A i j) := by fun_prop
  exact (hij.comp measurable_fst).add
    (measurable_snd.mul measurable_const)

/-- The affine substitution has Jacobian one, expressed intrinsically as
preservation of matrix-by-scalar Lebesgue measure. -/
theorem measurePreserving_ginibreShiftShear (n : ℕ) :
    MeasurePreserving (ginibreShiftShear n)
      ((realGinibreLebesgueMeasure n).prod volume)
      ((realGinibreLebesgueMeasure n).prod volume) := by
  let μ := realGinibreLebesgueMeasure n
  have htranslate : ∀ x : ℝ,
      Measure.map (fun A : RSqMat n => A - x • (1 : RSqMat n)) μ = μ := by
    intro x
    simpa [sub_eq_add_neg] using
      (map_add_right_eq_self μ (-(x • (1 : RSqMat n))))
  have hskewMeas : Measurable
      (Function.uncurry
        (fun x : ℝ => fun A : RSqMat n => A - x • (1 : RSqMat n))) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    have hij : Measurable (fun A : RSqMat n => A i j) := by fun_prop
    exact (hij.comp measurable_snd).sub
      (measurable_fst.mul measurable_const)
  have hskew : MeasurePreserving
      (fun p : ℝ × RSqMat n => (p.1, p.2 - p.1 • (1 : RSqMat n)))
      (volume.prod μ) (volume.prod μ) :=
    (MeasurePreserving.id volume).skew_product hskewMeas
      (ae_of_all _ htranslate)
  have h := (Measure.measurePreserving_swap (μ := volume) (ν := μ)).comp
    (hskew.comp (Measure.measurePreserving_swap (μ := μ) (ν := volume)))
  simpa [μ, ginibreShiftShear, Function.comp_def] using h

/-- Nonnegative-integral version of the absolute characteristic moment. -/
noncomputable def realGinibreAbsoluteCharacteristicMomentLIntegral (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ p : RSqMat n × ℝ,
    ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det|
    ∂(realGinibreMeasure n).prod (gaussianReal 0 1)

theorem measurable_abs_det_ginibreShiftReal (n : ℕ) :
    Measurable (fun p : RSqMat n × ℝ =>
      |(p.1 - p.2 • (1 : RSqMat n)).det|) := by
  apply Measurable.abs
  simp_rw [Matrix.det_apply]
  apply Finset.measurable_sum
  intro σ hσ
  apply Measurable.const_smul
  apply Finset.measurable_prod
  intro i hi
  have hij : Measurable (fun A : RSqMat n => A (σ i) i) := by fun_prop
  exact (hij.comp measurable_fst).sub (measurable_snd.mul measurable_const)

theorem measurable_abs_det_ginibreShift (n : ℕ) :
    Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det|) :=
  (measurable_abs_det_ginibreShiftReal n).ennreal_ofReal

theorem measurable_abs_det_matrixReal (n : ℕ) :
    Measurable (fun A : RSqMat n => |A.det|) :=
  continuous_id.matrix_det.abs.measurable

theorem measurable_abs_det_matrix (n : ℕ) :
    Measurable (fun A : RSqMat n => ENNReal.ofReal |A.det|) := by
  exact (measurable_abs_det_matrixReal n).ennreal_ofReal

/-- The ordinary expectation is the real value of its nonnegative integral.
This is unconditional: Mathlib's conventions agree even in the nonintegrable
case (`integral = 0` and `ENNReal.toReal ∞ = 0`). -/
theorem realGinibreAbsoluteCharacteristicMoment_eq_toReal_lintegral (n : ℕ) :
    realGinibreAbsoluteCharacteristicMoment n =
      (realGinibreAbsoluteCharacteristicMomentLIntegral n).toReal := by
  unfold realGinibreAbsoluteCharacteristicMoment
  unfold realGinibreAbsoluteCharacteristicMomentLIntegral
  exact integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun p => abs_nonneg _)
    (measurable_abs_det_ginibreShiftReal n).aestronglyMeasurable

theorem realGinibreAbsoluteCharacteristicMomentLIntegral_eq_jointDensity
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMomentLIntegral n =
      ∫⁻ p : RSqMat n × ℝ,
        ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
          ENNReal.ofReal
            (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2)
        ∂(realGinibreLebesgueMeasure n).prod volume := by
  unfold realGinibreAbsoluteCharacteristicMomentLIntegral
  rw [realGinibreMeasure_eq_withDensity]
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [prod_withDensity
    (measurable_realGinibreDensityReal n).ennreal_ofReal
    (measurable_gaussianPDF 0 1)]
  have hdensity : Measurable (fun z : RSqMat n × ℝ =>
      ENNReal.ofReal (realGinibreDensityReal n z.1) * gaussianPDF 0 1 z.2) :=
    (((measurable_realGinibreDensityReal n).ennreal_ofReal.comp measurable_fst).mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd))
  rw [lintegral_withDensity_eq_lintegral_mul _ hdensity
    (measurable_abs_det_ginibreShift n)]
  apply lintegral_congr
  intro p
  simp only [Pi.mul_apply, gaussianPDF]
  rw [ENNReal.ofReal_mul (le_of_lt (realGinibreDensityReal_pos n p.1))]
  ring

theorem realGinibreAbsoluteCharacteristicMomentLIntegral_eq_shiftedJointDensity
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMomentLIntegral n =
      ∫⁻ p : RSqMat n × ℝ,
        ENNReal.ofReal |p.1.det| *
          ENNReal.ofReal
            (realGinibreDensityReal n
                (p.1 + p.2 • (1 : RSqMat n)) *
              gaussianPDFReal 0 1 p.2)
        ∂(realGinibreLebesgueMeasure n).prod volume := by
  rw [realGinibreAbsoluteCharacteristicMomentLIntegral_eq_jointDensity]
  let G : RSqMat n × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal |p.1.det| *
      ENNReal.ofReal
        (realGinibreDensityReal n (p.1 + p.2 • (1 : RSqMat n)) *
          gaussianPDFReal 0 1 p.2)
  have hdet : Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal |p.1.det|) := by
    exact (measurable_abs_det_matrix n).comp measurable_fst
  have hjoint : Measurable (fun p : RSqMat n × ℝ =>
      ENNReal.ofReal
        (realGinibreDensityReal n (p.1 + p.2 • (1 : RSqMat n)) *
          gaussianPDFReal 0 1 p.2)) := by
    apply Measurable.ennreal_ofReal
    exact ((measurable_realGinibreDensityReal n).comp
      (measurable_fst.comp (measurable_ginibreUnshiftShear n))).mul
        ((measurable_gaussianPDFReal 0 1).comp measurable_snd)
  have hG : Measurable G := hdet.mul hjoint
  calc
    (∫⁻ p : RSqMat n × ℝ,
        ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
          ENNReal.ofReal
            (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2)
        ∂(realGinibreLebesgueMeasure n).prod volume) =
      ∫⁻ p, G (ginibreShiftShear n p)
        ∂(realGinibreLebesgueMeasure n).prod volume := by
          apply lintegral_congr
          intro p
          change ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
              ENNReal.ofReal
                (realGinibreDensityReal n p.1 * gaussianPDFReal 0 1 p.2) =
            ENNReal.ofReal |(p.1 - p.2 • (1 : RSqMat n)).det| *
              ENNReal.ofReal
                (realGinibreDensityReal n
                    ((p.1 - p.2 • (1 : RSqMat n)) +
                      p.2 • (1 : RSqMat n)) *
                  gaussianPDFReal 0 1 p.2)
          rw [sub_add_cancel]
    _ = ∫⁻ p, G p ∂(realGinibreLebesgueMeasure n).prod volume :=
      (measurePreserving_ginibreShiftShear n).lintegral_comp hG

/-- The unconditional change-of-variables identity: the absolute
characteristic moment is the determinant integral against the exact
trace-correlated Gaussian density. -/
theorem realGinibreAbsoluteCharacteristicMomentLIntegral_eq_traceDensity
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMomentLIntegral n =
      ∫⁻ B : RSqMat n,
        ENNReal.ofReal |B.det| *
          ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
        ∂realGinibreLebesgueMeasure n := by
  rw [realGinibreAbsoluteCharacteristicMomentLIntegral_eq_shiftedJointDensity]
  let d : RSqMat n → ℝ≥0∞ := fun B => ENNReal.ofReal |B.det|
  let j : RSqMat n × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal
      (realGinibreDensityReal n (p.1 + p.2 • (1 : RSqMat n)) *
        gaussianPDFReal 0 1 p.2)
  have hd : Measurable d := by
    simpa only [d] using measurable_abs_det_matrix n
  have hj : Measurable j := by
    apply Measurable.ennreal_ofReal
    exact ((measurable_realGinibreDensityReal n).comp
      (measurable_fst.comp (measurable_ginibreUnshiftShear n))).mul
        ((measurable_gaussianPDFReal 0 1).comp measurable_snd)
  change (∫⁻ p : RSqMat n × ℝ, d p.1 * j p
      ∂(realGinibreLebesgueMeasure n).prod volume) =
    ∫⁻ B : RSqMat n, d B *
      ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
      ∂realGinibreLebesgueMeasure n
  rw [lintegral_prod (fun p : RSqMat n × ℝ => d p.1 * j p)
    ((hd.comp measurable_fst).mul hj).aemeasurable]
  apply lintegral_congr
  intro B
  have hinner : Measurable (fun x : ℝ => j (B, x)) :=
    hj.comp (measurable_const.prodMk measurable_id)
  change (∫⁻ x : ℝ, d B * j (B, x)) =
    d B * ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
  rw [lintegral_const_mul _ hinner]
  change d B * (∫⁻ x : ℝ, ENNReal.ofReal
      (realGinibreDensityReal n (B + x • (1 : RSqMat n)) *
        gaussianPDFReal 0 1 x)) = _
  rw [lintegral_ginibreShiftJointDensity]

/-- Ordinary-integral form of the same unconditional identity, directly
connected to `realGinibreAbsoluteCharacteristicMoment`. -/
theorem realGinibreAbsoluteCharacteristicMoment_eq_traceDensityIntegral
    (n : ℕ) :
    realGinibreAbsoluteCharacteristicMoment n =
      ∫ B : RSqMat n,
        |B.det| * ginibreTraceCorrelatedDensityReal n B
        ∂realGinibreLebesgueMeasure n := by
  calc
    realGinibreAbsoluteCharacteristicMoment n =
        (realGinibreAbsoluteCharacteristicMomentLIntegral n).toReal :=
      realGinibreAbsoluteCharacteristicMoment_eq_toReal_lintegral n
    _ = (∫⁻ B : RSqMat n,
          ENNReal.ofReal |B.det| *
            ENNReal.ofReal (ginibreTraceCorrelatedDensityReal n B)
          ∂realGinibreLebesgueMeasure n).toReal := by
      rw [realGinibreAbsoluteCharacteristicMomentLIntegral_eq_traceDensity]
    _ = (∫⁻ B : RSqMat n,
          ENNReal.ofReal
            (|B.det| * ginibreTraceCorrelatedDensityReal n B)
          ∂realGinibreLebesgueMeasure n).toReal := by
      congr 1
      apply lintegral_congr
      intro B
      rw [ENNReal.ofReal_mul (abs_nonneg B.det)]
    _ = ∫ B : RSqMat n,
          |B.det| * ginibreTraceCorrelatedDensityReal n B
          ∂realGinibreLebesgueMeasure n := by
      symm
      exact integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun B => mul_nonneg (abs_nonneg _)
          (le_of_lt (ginibreTraceCorrelatedDensityReal_pos n B)))
        ((measurable_abs_det_matrixReal n).mul
          (measurable_ginibreTraceCorrelatedDensityReal n)).aestronglyMeasurable

end
end NumStability
