/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment
import NumStability.Algorithms.TestMatrices.Higham28GinibreDimensionTwo
import NumStability.Algorithms.TestMatrices.Higham28GinibreTraceDensity

/-! # Higham Chapter 28: absolute-determinant recurrence infrastructure

This file develops unconditional finite-dimensional identities for the
trace-correlated determinant moment.  In dimension two an explicit orthogonal
change of five independent Gaussian coordinates puts the determinant into the
quadratic normal form

`(3x₀² + x₁² - x₂² - x₃²) / 2`.

The transformation and its exact preservation of the joint Ginibre--scalar
Gaussian law are proved here.  The analytic evaluation of the resulting
normal-form integral is developed below.
-/

namespace NumStability

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

set_option maxHeartbeats 800000

private local instance ginibreAbsoluteDetRecurrenceMeasurableSpace (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private local instance ginibreAbsoluteDetRecurrenceSigmaFinite (n : ℕ) :
    SigmaFinite (realGinibreMeasure n) := by
  change SigmaFinite (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
  infer_instance

private theorem ginibre_natRawCast_one {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 1 = (1 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_zero {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 0 = (0 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_three {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 3 = (3 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_two {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 2 = (2 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_six {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 6 = (6 : R) := by
  simp [Nat.rawCast]

private theorem ginibre_natRawCast_twelve {R : Type*} [AddMonoidWithOne R] :
    Nat.rawCast 12 = (12 : R) := by
  simp [Nat.rawCast]

/-! ## An all-dimensional trace-stretch reduction -/

/-- Stretch only the scalar-trace direction of a matrix by `sqrt (n+1)`.
The trace-correlated quadratic form becomes the ordinary Frobenius square
under this map. -/
noncomputable def ginibreTraceStretch (n : ℕ) (A : RSqMat n) : RSqMat n :=
  ginibreTracelessPart n A +
    (Real.sqrt (n + 1 : ℝ) * Matrix.trace A / (n : ℝ)) •
      (1 : RSqMat n)

/-- Orthogonal decomposition of a matrix into its traceless part and its
scalar-trace direction. -/
theorem ginibreMatrixSq_eq_traceless_add_trace (n : ℕ) (hn : 0 < n)
    (A : RSqMat n) :
    ginibreMatrixSq n A =
      ginibreMatrixSq n (ginibreTracelessPart n A) +
        Matrix.trace A ^ 2 / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn10 : (n + 1 : ℝ) ≠ 0 := by positivity
  have h := ginibreTraceQuadratic_eq_traceless_add_trace n hn A
  unfold ginibreTraceQuadratic at h
  field_simp [hn0, hn10] at h ⊢
  nlinarith

/-- The trace-stretch has the advertised action on the trace coordinate. -/
theorem trace_ginibreTraceStretch (n : ℕ) (hn : 0 < n) (A : RSqMat n) :
    Matrix.trace (ginibreTraceStretch n A) =
      Real.sqrt (n + 1 : ℝ) * Matrix.trace A := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold ginibreTraceStretch
  rw [Matrix.trace_add, trace_ginibreTracelessPart n hn A,
    Matrix.trace_smul, Matrix.trace_one]
  simp only [zero_add, Fintype.card_fin, smul_eq_mul]
  field_simp [hn0]

/-- Stretching the trace coordinate leaves the traceless projection fixed. -/
theorem ginibreTracelessPart_traceStretch (n : ℕ) (hn : 0 < n)
    (A : RSqMat n) :
    ginibreTracelessPart n (ginibreTraceStretch n A) =
      ginibreTracelessPart n A := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [ginibreTracelessPart]
  rw [trace_ginibreTraceStretch n hn A]
  unfold ginibreTraceStretch
  exact add_sub_cancel_right _ _

/-- The trace-correlated precision is exactly the ordinary matrix square
after trace stretching.  This is the dimension-independent analytic core of
the density change of variables. -/
theorem ginibreTraceQuadratic_traceStretch (n : ℕ) (hn : 0 < n)
    (A : RSqMat n) :
    ginibreTraceQuadratic n (ginibreTraceStretch n A) =
      ginibreMatrixSq n A := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn10 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hsqrt : Real.sqrt (n + 1 : ℝ) ^ 2 = (n + 1 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  calc
    ginibreTraceQuadratic n (ginibreTraceStretch n A) =
        ginibreMatrixSq n (ginibreTracelessPart n A) +
          (Real.sqrt (n + 1 : ℝ) * Matrix.trace A) ^ 2 /
            ((n : ℝ) * (n + 1 : ℝ)) := by
      rw [ginibreTraceQuadratic_eq_traceless_add_trace n hn,
        ginibreTracelessPart_traceStretch n hn,
        trace_ginibreTraceStretch n hn]
    _ = ginibreMatrixSq n (ginibreTracelessPart n A) +
          Matrix.trace A ^ 2 / (n : ℝ) := by
      congr 1
      field_simp [hn0, hn10]
      nlinarith
    _ = ginibreMatrixSq n A :=
      (ginibreMatrixSq_eq_traceless_add_trace n hn A).symm

/-- Pointwise cancellation between the Jacobian factor of the trace stretch
and the normalization in the trace-correlated density. -/
theorem ginibreTraceCorrelatedDensity_traceStretch_mul_sqrt
    (n : ℕ) (hn : 0 < n) (A : RSqMat n) :
    ginibreTraceCorrelatedDensityReal n (ginibreTraceStretch n A) *
        Real.sqrt (n + 1 : ℝ) =
      realGinibreDensityReal n A := by
  rw [realGinibreDensityReal_eq_exp]
  unfold ginibreTraceCorrelatedDensityReal
  rw [ginibreTraceQuadratic_traceStretch n hn A]
  have hsqrt : Real.sqrt (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hsqrt]

/-! ## Gaussian coordinate splitting -/

/-- Measurable equivalence splitting a vector indexed by `Fin (m+n)` into
its first `m` and last `n` coordinates. -/
def ginibreGaussianVectorSplitEquiv (m n : ℕ) :
    (Fin (m + n) → ℝ) ≃ᵐ (Fin m → ℝ) × (Fin n → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) => ℝ)
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))).symm |>.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ))

/-- Split a vector indexed by `Fin (m+n)` into its first `m` and last `n`
coordinates. -/
def ginibreGaussianVectorSplit (m n : ℕ) (x : Fin (m + n) → ℝ) :
    (Fin m → ℝ) × (Fin n → ℝ) :=
  ginibreGaussianVectorSplitEquiv m n x

theorem measurable_ginibreGaussianVectorSplit (m n : ℕ) :
    Measurable (ginibreGaussianVectorSplit m n) := by
  unfold ginibreGaussianVectorSplit
  fun_prop

/-- Independent standard Gaussian coordinates split into independent standard
Gaussian blocks. -/
theorem measurePreserving_ginibreGaussianVectorSplit (m n : ℕ) :
    MeasurePreserving (ginibreGaussianVectorSplit m n)
      (standardGaussianVectorMeasure (m + n))
      ((standardGaussianVectorMeasure m).prod
        (standardGaussianVectorMeasure n)) := by
  let μ : Fin (m + n) → Measure ℝ := fun _ => gaussianReal 0 1
  let e : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  have hreindex := (measurePreserving_piCongrLeft μ e).symm
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) e)
  have hsplit := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin m ⊕ Fin n => gaussianReal 0 1)
  have h := hsplit.comp hreindex
  simpa only [μ, e, standardGaussianVectorMeasure,
    ginibreGaussianVectorSplit, ginibreGaussianVectorSplitEquiv,
    Function.comp_apply] using h

/-! ## The five-coordinate orthogonal normal form -/

noncomputable def ginibreAbsDetScaleTwo : ℝ := Real.sqrt 2 / 2
noncomputable def ginibreAbsDetScaleThree : ℝ := Real.sqrt 3 / 3
noncomputable def ginibreAbsDetScaleSix : ℝ := Real.sqrt 6 / 6

theorem ginibreAbsDetScaleTwo_sq : ginibreAbsDetScaleTwo ^ 2 = 1 / 2 := by
  unfold ginibreAbsDetScaleTwo
  have h : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  nlinarith

theorem ginibreAbsDetScaleThree_sq : ginibreAbsDetScaleThree ^ 2 = 1 / 3 := by
  unfold ginibreAbsDetScaleThree
  have h : Real.sqrt 3 ^ 2 = (3 : ℝ) := by norm_num
  nlinarith

theorem ginibreAbsDetScaleSix_sq : ginibreAbsDetScaleSix ^ 2 = 1 / 6 := by
  unfold ginibreAbsDetScaleSix
  have h : Real.sqrt 6 ^ 2 = (6 : ℝ) := by norm_num
  nlinarith

/-- Orthogonal coordinates adapted to a `2×2` characteristic determinant.
The source order is `(a₀₀,a₀₁,a₁₀,a₁₁,λ)`. -/
noncomputable def ginibreAbsDetTwoRotationMatrix : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ginibreAbsDetScaleSix, 0, 0, ginibreAbsDetScaleSix,
        -2 * ginibreAbsDetScaleSix;
     0, ginibreAbsDetScaleTwo, -ginibreAbsDetScaleTwo, 0, 0;
     ginibreAbsDetScaleTwo, 0, 0, -ginibreAbsDetScaleTwo, 0;
     0, ginibreAbsDetScaleTwo, ginibreAbsDetScaleTwo, 0, 0;
     ginibreAbsDetScaleThree, 0, 0, ginibreAbsDetScaleThree,
        ginibreAbsDetScaleThree]

noncomputable def ginibreAbsDetTwoRotationOrthogonal :
    Matrix.orthogonalGroup (Fin 5) ℝ :=
  ⟨ginibreAbsDetTwoRotationMatrix, by
    have h2 := ginibreAbsDetScaleTwo_sq
    have h3 := ginibreAbsDetScaleThree_sq
    have h6 := ginibreAbsDetScaleSix_sq
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ginibreAbsDetTwoRotationMatrix, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply] <;>
      nlinarith⟩

/-- Flatten a `2×2` matrix and its independent scalar shift into five
coordinates. -/
def ginibreAbsDetTwoEntryVector (p : RSqMat 2 × ℝ) : Fin 5 → ℝ :=
  ![p.1 0 0, p.1 0 1, p.1 1 0, p.1 1 1, p.2]

theorem measurable_ginibreAbsDetTwoEntryVector :
    Measurable ginibreAbsDetTwoEntryVector := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp [ginibreAbsDetTwoEntryVector] <;> fun_prop

theorem ginibreAbsDetTwoEntryVector_eq_splitInverse
    (p : RSqMat 2 × ℝ) :
    ginibreAbsDetTwoEntryVector p =
      (ginibreGaussianVectorSplitEquiv 4 1).symm
        (ginibreTwoEntryVector p.1, fun _ => p.2) := by
  ext i
  fin_cases i <;> rfl

/-- The flattened matrix entries and scalar shift are exactly five independent
standard real Gaussians. -/
theorem measurePreserving_ginibreAbsDetTwoEntryVector :
    MeasurePreserving ginibreAbsDetTwoEntryVector
      ((realGinibreMeasure 2).prod (gaussianReal 0 1))
      (standardGaussianVectorMeasure 5) := by
  let hA : MeasurePreserving ginibreTwoEntryVector
      (realGinibreMeasure 2) (standardGaussianVectorMeasure 4) :=
    ⟨measurable_ginibreTwoEntryVector,
      realGinibreMeasure_two_map_ginibreTwoEntryVector⟩
  let hscalar : MeasurePreserving (fun x : ℝ => fun _ : Fin 1 => x)
      (gaussianReal 0 1) (standardGaussianVectorMeasure 1) := by
    refine ⟨by fun_prop, ?_⟩
    unfold standardGaussianVectorMeasure
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
    have hpre : (fun x : ℝ => fun _ : Fin 1 => x) ⁻¹' (Set.univ.pi s) = s 0 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
      constructor
      · intro h
        exact h 0
      · intro hx i
        fin_cases i
        exact hx
    rw [hpre]
    simp
  have hprod := hA.prod hscalar
  have hjoin := (measurePreserving_ginibreGaussianVectorSplit 4 1).symm
    (ginibreGaussianVectorSplitEquiv 4 1)
  have h := hjoin.comp hprod
  convert h using 1
  funext p
  simpa only [Function.comp_apply, Prod.map_apply] using
    ginibreAbsDetTwoEntryVector_eq_splitInverse p

/-- Absolute determinant in the orthogonal Gaussian normal coordinates. -/
def ginibreAbsDetTwoNormalForm (x : Fin 5 → ℝ) : ℝ :=
  |(3 * x 0 ^ 2 + x 1 ^ 2 - x 2 ^ 2 - x 3 ^ 2) / 2|

theorem measurable_ginibreAbsDetTwoNormalForm :
    Measurable ginibreAbsDetTwoNormalForm := by
  unfold ginibreAbsDetTwoNormalForm
  fun_prop

theorem ginibreAbsDetTwoRotation_apply_zero (p : RSqMat 2 × ℝ) :
    Matrix.mulVec ginibreAbsDetTwoRotationMatrix
        (ginibreAbsDetTwoEntryVector p) 0 =
      ginibreAbsDetScaleSix * (p.1 0 0 + p.1 1 1 - 2 * p.2) := by
  simp [ginibreAbsDetTwoRotationMatrix, ginibreAbsDetTwoEntryVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem ginibreAbsDetTwoRotation_apply_one (p : RSqMat 2 × ℝ) :
    Matrix.mulVec ginibreAbsDetTwoRotationMatrix
        (ginibreAbsDetTwoEntryVector p) 1 =
      ginibreAbsDetScaleTwo * (p.1 0 1 - p.1 1 0) := by
  simp [ginibreAbsDetTwoRotationMatrix, ginibreAbsDetTwoEntryVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem ginibreAbsDetTwoRotation_apply_two (p : RSqMat 2 × ℝ) :
    Matrix.mulVec ginibreAbsDetTwoRotationMatrix
        (ginibreAbsDetTwoEntryVector p) 2 =
      ginibreAbsDetScaleTwo * (p.1 0 0 - p.1 1 1) := by
  simp [ginibreAbsDetTwoRotationMatrix, ginibreAbsDetTwoEntryVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem ginibreAbsDetTwoRotation_apply_three (p : RSqMat 2 × ℝ) :
    Matrix.mulVec ginibreAbsDetTwoRotationMatrix
        (ginibreAbsDetTwoEntryVector p) 3 =
      ginibreAbsDetScaleTwo * (p.1 0 1 + p.1 1 0) := by
  simp [ginibreAbsDetTwoRotationMatrix, ginibreAbsDetTwoEntryVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The orthogonal transformation converts the shifted determinant exactly
to the four-square normal form. -/
theorem abs_det_two_eq_normalForm_rotation (p : RSqMat 2 × ℝ) :
    |(p.1 - p.2 • (1 : RSqMat 2)).det| =
      ginibreAbsDetTwoNormalForm
        (Matrix.mulVec ginibreAbsDetTwoRotationMatrix
          (ginibreAbsDetTwoEntryVector p)) := by
  have h2 := ginibreAbsDetScaleTwo_sq
  have h6 := ginibreAbsDetScaleSix_sq
  rw [show (p.1 - p.2 • (1 : RSqMat 2)).det =
      (p.1 0 0 - p.2) * (p.1 1 1 - p.2) -
        p.1 0 1 * p.1 1 0 by
    simp [Matrix.det_fin_two, Matrix.one_apply]]
  unfold ginibreAbsDetTwoNormalForm
  rw [ginibreAbsDetTwoRotation_apply_zero,
    ginibreAbsDetTwoRotation_apply_one,
    ginibreAbsDetTwoRotation_apply_two,
    ginibreAbsDetTwoRotation_apply_three]
  apply congrArg abs
  simp only [mul_pow, h2, h6]
  ring

/-- The joint absolute determinant is reduced unconditionally to the standard
five-dimensional Gaussian normal-form integral. -/
theorem realGinibreAbsoluteCharacteristicMoment_two_eq_normalFormIntegral :
    realGinibreAbsoluteCharacteristicMoment 2 =
      ∫ x : Fin 5 → ℝ, ginibreAbsDetTwoNormalForm x
        ∂standardGaussianVectorMeasure 5 := by
  let μ := (realGinibreMeasure 2).prod (gaussianReal 0 1)
  let T : (Fin 5 → ℝ) → (Fin 5 → ℝ) := fun x =>
    Matrix.mulVec ginibreAbsDetTwoRotationMatrix x
  have hT : Measurable T := by fun_prop
  have hflat := measurePreserving_ginibreAbsDetTwoEntryVector
  have hrot : (standardGaussianVectorMeasure 5).map T =
      standardGaussianVectorMeasure 5 :=
    standardGaussianVectorMeasure_map_orthogonalGroup 5
      ginibreAbsDetTwoRotationOrthogonal
  unfold realGinibreAbsoluteCharacteristicMoment
  calc
    (∫ p : RSqMat 2 × ℝ, |(p.1 - p.2 • (1 : RSqMat 2)).det| ∂μ) =
        ∫ p : RSqMat 2 × ℝ,
          ginibreAbsDetTwoNormalForm (T (ginibreAbsDetTwoEntryVector p)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with p
      exact abs_det_two_eq_normalForm_rotation p
    _ = ∫ x : Fin 5 → ℝ, ginibreAbsDetTwoNormalForm (T x)
          ∂standardGaussianVectorMeasure 5 := by
      have hmap := integral_map
        measurable_ginibreAbsDetTwoEntryVector.aemeasurable
        ((measurable_ginibreAbsDetTwoNormalForm.comp hT).aestronglyMeasurable)
        (μ := μ)
      rw [hflat.map_eq] at hmap
      simpa only [Function.comp_apply] using hmap.symm
    _ = ∫ x : Fin 5 → ℝ, ginibreAbsDetTwoNormalForm x
          ∂(standardGaussianVectorMeasure 5).map T := by
      symm
      exact integral_map hT.aemeasurable
        measurable_ginibreAbsDetTwoNormalForm.aestronglyMeasurable
    _ = _ := by rw [hrot]

/-! ## Elementary radial integrals for the two-dimensional evaluation -/

/-- Cubic Gaussian radial tails are integrable on every nonnegative ray. -/
theorem integrableOn_Ioi_cube_mul_exp_neg_sq_div_two
    (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun r : ℝ => r ^ 3 * Real.exp (-(r ^ 2) / 2)) (Ioi a) := by
  have hbase : IntegrableOn
      (fun r : ℝ => r ^ (3 : ℝ) * Real.exp (-(1 / 2) * r ^ 2))
      (Ioi a) :=
    (integrable_rpow_mul_exp_neg_mul_sq
      (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (-1 : ℝ) < 3 by norm_num)).integrableOn
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro r hr
  change r ^ (3 : ℝ) * Real.exp (-(1 / 2) * r ^ 2) =
    r ^ (3 : ℕ) * Real.exp (-r ^ 2 / 2)
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
  rw [Real.rpow_natCast]
  congr 2 <;> try ring

/-- Cubic companion to the elementary Gaussian radial-tail integral. -/
theorem integral_Ioi_cube_mul_exp_neg_sq_div_two
    (a : ℝ) (ha : 0 ≤ a) :
    ∫ r in Ioi a, r ^ 3 * Real.exp (-(r ^ 2) / 2) =
      (a ^ 2 + 2) * Real.exp (-(a ^ 2) / 2) := by
  let F : ℝ → ℝ := fun r =>
    -(r ^ 2 + 2) * Real.exp (-(r ^ 2) / 2)
  have hderiv : ∀ r : ℝ, HasDerivAt F
      (r ^ 3 * Real.exp (-(r ^ 2) / 2)) r := by
    intro r
    convert (((hasDerivAt_pow 2 r).add_const 2).neg.mul
      (((hasDerivAt_pow 2 r).neg.div_const 2).exp)) using 1 <;>
      norm_num [F] <;> ring
  have hint : IntegrableOn
      (fun r : ℝ => r ^ 3 * Real.exp (-(r ^ 2) / 2)) (Ioi a) :=
    integrableOn_Ioi_cube_mul_exp_neg_sq_div_two a ha
  have hu : Tendsto (fun r : ℝ => r ^ 2 / 2) atTop atTop := by
    have hp : Tendsto (fun r : ℝ => r ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
    convert hp.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 1
    funext r
    ring
  have hpow0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hu
  have hpow1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hu
  have hlim : Tendsto F atTop (nhds 0) := by
    have hsum := hpow1.add hpow0
    convert (hsum.const_mul (-2 : ℝ)) using 1
    · funext r
      simp only [F, Function.comp_apply, pow_zero, pow_one, one_mul]
      ring
    · congr 1 <;> norm_num
  calc
    (∫ r in Ioi a, r ^ 3 * Real.exp (-(r ^ 2) / 2)) =
        0 - F a := integral_Ioi_of_hasDerivAt_of_tendsto'
          (fun r _ => hderiv r) hint hlim
    _ = (a ^ 2 + 2) * Real.exp (-(a ^ 2) / 2) := by
      simp only [F, zero_sub, neg_mul, neg_neg]

/-- The excess of the cubic radial tail over `a²` times the linear radial
tail is exactly twice the Gaussian tail. -/
theorem integral_Ioi_sq_sub_mul_exp_neg_sq_div_two
    (a : ℝ) (ha : 0 ≤ a) :
    ∫ r in Ioi a, (r ^ 2 - a ^ 2) * r * Real.exp (-(r ^ 2) / 2) =
      2 * Real.exp (-(a ^ 2) / 2) := by
  have hcube := integrableOn_Ioi_cube_mul_exp_neg_sq_div_two a ha
  have hlin : IntegrableOn
      (fun r : ℝ => r * Real.exp (-(r ^ 2) / 2)) (Ioi a) := by
    have h : IntegrableOn
        (fun r : ℝ => r * Real.exp (-(1 / 2) * r ^ 2)) (Ioi a) :=
      (integrable_mul_exp_neg_mul_sq
        (show (0 : ℝ) < 1 / 2 by norm_num)).integrableOn
    apply h.congr_fun _ measurableSet_Ioi
    intro r hr
    congr 2
    ring
  have hconst : IntegrableOn
      (fun r : ℝ => a ^ 2 * (r * Real.exp (-(r ^ 2) / 2))) (Ioi a) :=
    hlin.const_mul _
  calc
    (∫ r in Ioi a, (r ^ 2 - a ^ 2) * r * Real.exp (-(r ^ 2) / 2)) =
        ∫ r in Ioi a,
          r ^ 3 * Real.exp (-(r ^ 2) / 2) -
            a ^ 2 * (r * Real.exp (-(r ^ 2) / 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      ring
    _ = (∫ r in Ioi a, r ^ 3 * Real.exp (-(r ^ 2) / 2)) -
          ∫ r in Ioi a, a ^ 2 * (r * Real.exp (-(r ^ 2) / 2)) := by
      exact integral_sub hcube hconst
    _ = (∫ r in Ioi a, r ^ 3 * Real.exp (-(r ^ 2) / 2)) -
          a ^ 2 * ∫ r in Ioi a, r * Real.exp (-(r ^ 2) / 2) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [integral_Ioi_cube_mul_exp_neg_sq_div_two a ha,
        integral_Ioi_mul_exp_neg_sq_div_two]
      ring

/-- Exact one-dimensional radial absolute-value integral. -/
theorem integral_Ioi_abs_sub_sq_mul_exp_neg_sq_div_two
    (s : ℝ) (hs : 0 ≤ s) :
    ∫ r in Ioi (0 : ℝ), |s - r ^ 2| * r * Real.exp (-(r ^ 2) / 2) =
      s - 2 + 4 * Real.exp (-s / 2) := by
  let a : ℝ := Real.sqrt s
  let base : ℝ → ℝ := fun r =>
    (s - r ^ 2) * r * Real.exp (-(r ^ 2) / 2)
  let excess : ℝ → ℝ := fun r =>
    2 * ((r ^ 2 - s) * r * Real.exp (-(r ^ 2) / 2))
  have ha : 0 ≤ a := Real.sqrt_nonneg s
  have ha_sq : a ^ 2 = s := by
    exact Real.sq_sqrt hs
  have hlin : IntegrableOn
      (fun r : ℝ => r * Real.exp (-(r ^ 2) / 2)) (Ioi (0 : ℝ)) := by
    have h : IntegrableOn
        (fun r : ℝ => r * Real.exp (-(1 / 2) * r ^ 2))
        (Ioi (0 : ℝ)) :=
      (integrable_mul_exp_neg_mul_sq
        (show (0 : ℝ) < 1 / 2 by norm_num)).integrableOn
    apply h.congr_fun _ measurableSet_Ioi
    intro r hr
    congr 2
    ring
  have hcube := integrableOn_Ioi_cube_mul_exp_neg_sq_div_two 0 (le_refl 0)
  have hbase : IntegrableOn base (Ioi (0 : ℝ)) := by
    have hsLin : IntegrableOn
        (fun r : ℝ => s * (r * Real.exp (-(r ^ 2) / 2))) (Ioi (0 : ℝ)) :=
      hlin.const_mul _
    have hsub : IntegrableOn
        (fun r : ℝ => s * (r * Real.exp (-(r ^ 2) / 2)) -
          r ^ 3 * Real.exp (-(r ^ 2) / 2)) (Ioi (0 : ℝ)) :=
      hsLin.sub hcube
    apply hsub.congr_fun _ measurableSet_Ioi
    intro r hr
    simp only [base]
    ring
  have hexcessRay : IntegrableOn excess (Ioi a) := by
    have htail : IntegrableOn
        (fun r : ℝ => (r ^ 2 - a ^ 2) * r * Real.exp (-(r ^ 2) / 2))
        (Ioi a) := by
      have hc := integrableOn_Ioi_cube_mul_exp_neg_sq_div_two a ha
      have hl : IntegrableOn
          (fun r : ℝ => a ^ 2 * (r * Real.exp (-(r ^ 2) / 2)))
          (Ioi a) := by
        have hl0 : IntegrableOn
            (fun r : ℝ => r * Real.exp (-(1 / 2) * r ^ 2)) (Ioi a) :=
          (integrable_mul_exp_neg_mul_sq
            (show (0 : ℝ) < 1 / 2 by norm_num)).integrableOn
        have hl1 : IntegrableOn
            (fun r : ℝ => r * Real.exp (-(r ^ 2) / 2)) (Ioi a) := by
          apply hl0.congr_fun _ measurableSet_Ioi
          intro r hr
          congr 2
          ring
        exact hl1.const_mul _
      have hsub : IntegrableOn
          (fun r : ℝ => r ^ 3 * Real.exp (-(r ^ 2) / 2) -
            a ^ 2 * (r * Real.exp (-(r ^ 2) / 2))) (Ioi a) :=
        hc.sub hl
      apply hsub.congr_fun _ measurableSet_Ioi
      intro r hr
      ring
    have hmul : IntegrableOn
        (fun r : ℝ => 2 *
          ((r ^ 2 - a ^ 2) * r * Real.exp (-(r ^ 2) / 2))) (Ioi a) :=
      htail.const_mul 2
    apply hmul.congr_fun _ measurableSet_Ioi
    intro r hr
    simp only [excess, ha_sq]
  have hpoint : ∀ r ∈ Ioi (0 : ℝ),
      |s - r ^ 2| * r * Real.exp (-(r ^ 2) / 2) =
        base r + (Ioi a).indicator excess r := by
    intro r hr
    by_cases har : a < r
    · have hrs : s ≤ r ^ 2 := by nlinarith [ha_sq]
      simp [Set.indicator, mem_Ioi, har,
        abs_of_nonpos (sub_nonpos.mpr hrs), base, excess]
      ring
    · have hra : r ≤ a := le_of_not_gt har
      have hprod : 0 ≤ (a - r) * (a + r) :=
        mul_nonneg (sub_nonneg.mpr hra)
          (add_nonneg ha (le_of_lt hr))
      have hrs : r ^ 2 ≤ s := by nlinarith [ha_sq, hprod]
      simp [Set.indicator, mem_Ioi, har,
        abs_of_nonneg (sub_nonneg.mpr hrs), base]
  have hinter : Ioi (0 : ℝ) ∩ Ioi a = Ioi a := by
    ext r
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨ha.trans_lt h, h⟩
  calc
    (∫ r in Ioi (0 : ℝ), |s - r ^ 2| * r * Real.exp (-(r ^ 2) / 2)) =
        ∫ r in Ioi (0 : ℝ), base r + (Ioi a).indicator excess r := by
      exact setIntegral_congr_fun measurableSet_Ioi hpoint
    _ = (∫ r in Ioi (0 : ℝ), base r) +
          ∫ r in Ioi (0 : ℝ), (Ioi a).indicator excess r := by
      exact integral_add hbase
        ((hexcessRay.integrable_indicator measurableSet_Ioi).integrableOn)
    _ = (∫ r in Ioi (0 : ℝ), base r) + ∫ r in Ioi a, excess r := by
      rw [setIntegral_indicator measurableSet_Ioi, hinter]
    _ = (s - 2) + 2 *
          (∫ r in Ioi a,
            (r ^ 2 - a ^ 2) * r * Real.exp (-(r ^ 2) / 2)) := by
      congr 1
      · simp only [base]
        calc
          (∫ r in Ioi (0 : ℝ),
              (s - r ^ 2) * r * Real.exp (-(r ^ 2) / 2)) =
              s * (∫ r in Ioi (0 : ℝ),
                r * Real.exp (-(r ^ 2) / 2)) -
                ∫ r in Ioi (0 : ℝ),
                  r ^ 3 * Real.exp (-(r ^ 2) / 2) := by
            rw [← integral_const_mul]
            rw [← integral_sub (hlin.const_mul s) hcube]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro r hr
            ring
          _ = s - 2 := by
            rw [integral_Ioi_mul_exp_neg_sq_div_two,
              integral_Ioi_cube_mul_exp_neg_sq_div_two 0 (le_refl 0)]
            have hexpZero : Real.exp (-((0 : ℝ) ^ 2) / 2) = 1 := by
              convert Real.exp_zero using 1 <;> ring_nf <;> rfl
            rw [hexpZero]
            ring_nf
      · simp only [excess, ha_sq]
        rw [integral_const_mul]
    _ = _ := by
      rw [integral_Ioi_sq_sub_mul_exp_neg_sq_div_two a ha, ha_sq]
      ring

/-- The absolute radial difference against two independent standard Gaussian
coordinates.  This is the analytic inner integral in the exact `2 × 2`
Ginibre determinant normal form. -/
theorem integral_abs_sub_sq_add_sq_gaussianPDFReal_prod
    (s : ℝ) (hs : 0 ≤ s) :
    (∫ p : ℝ × ℝ,
        |s - (p.1 ^ 2 + p.2 ^ 2)| *
          (gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2)) =
      s - 2 + 4 * Real.exp (-s / 2) := by
  let d : ℝ × ℝ → ℝ := fun p =>
    |s - (p.1 ^ 2 + p.2 ^ 2)| *
      (gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2)
  let g : ℝ → ℝ := fun r =>
    |s - r ^ 2| * (r / (2 * Real.pi) * Real.exp (-(r ^ 2) / 2))
  change (∫ p : ℝ × ℝ, d p) = _
  rw [← integral_comp_polarCoord_symm]
  have hpolar :
      (∫ p in polarCoord.target, p.1 • d (polarCoord.symm p)) =
        ∫ p in polarCoord.target, g p.1 := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    have hsq :
        (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
      simp only [polarCoord_symm_apply]
      calc
        (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 =
            p.1 ^ 2 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
        _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
    change p.1 *
        (|s - ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2)| *
          (gaussianPDFReal 0 1 (polarCoord.symm p).1 *
            gaussianPDFReal 0 1 (polarCoord.symm p).2)) = g p.1
    rw [hsq]
    rw [show p.1 *
        (|s - p.1 ^ 2| *
          (gaussianPDFReal 0 1 (polarCoord.symm p).1 *
            gaussianPDFReal 0 1 (polarCoord.symm p).2)) =
        |s - p.1 ^ 2| *
          (p.1 * (gaussianPDFReal 0 1 (polarCoord.symm p).1 *
            gaussianPDFReal 0 1 (polarCoord.symm p).2)) by ring]
    rw [show p.1 *
        (gaussianPDFReal 0 1 (polarCoord.symm p).1 *
          gaussianPDFReal 0 1 (polarCoord.symm p).2) =
        p.1 / (2 * Real.pi) * Real.exp (-(p.1 ^ 2) / 2) by
      simpa only [polarCoord_symm_apply] using
        gaussianPDFReal_zero_one_prod_polar p.1 p.2]
  rw [hpolar, polarCoord_target]
  have hprod :
      (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, g p.1) =
        (∫ r in Ioi (0 : ℝ), g r) *
          ∫ theta in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    simpa only [mul_one] using
      (setIntegral_prod_mul g (fun _ : ℝ => (1 : ℝ))
        (Ioi (0 : ℝ)) (Ioo (-Real.pi) Real.pi))
  rw [hprod]
  have hrad :
      (∫ r in Ioi (0 : ℝ), g r) =
        (2 * Real.pi)⁻¹ * (s - 2 + 4 * Real.exp (-s / 2)) := by
    rw [show (∫ r in Ioi (0 : ℝ), g r) =
        (2 * Real.pi)⁻¹ *
          ∫ r in Ioi (0 : ℝ),
            |s - r ^ 2| * r * Real.exp (-(r ^ 2) / 2) by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      simp only [g, div_eq_mul_inv]
      ring]
    rw [integral_Ioi_abs_sub_sq_mul_exp_neg_sq_div_two s hs]
  rw [hrad]
  have htheta : (∫ theta in Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
    simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
      univ_inter]
    rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    simp [smul_eq_mul]
    ring
  rw [htheta]
  field_simp [ne_of_gt Real.pi_pos]

end
end NumStability
