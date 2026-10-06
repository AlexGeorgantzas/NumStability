/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreMeasure
import NumStability.Algorithms.TestMatrices.Higham28GaussianOrthogonal
import NumStability.Algorithms.TestMatrices.Higham28GinibreParity
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # The exact two-dimensional real-Ginibre expectation

This file evaluates the genuine matrix expectation in dimension two.  The
proof reduces the real-root count to the sign of the quadratic discriminant,
uses an explicit orthogonal change of the four iid Gaussian entries, and
evaluates the resulting circular-cone probability by polar coordinates.
-/

namespace NumStability

open Filter MeasureTheory Polynomial ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable section

local instance (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- The ordinary discriminant of the characteristic polynomial of a real
`2 × 2` matrix, written directly in its entries. -/
def realGinibreTwoDiscriminant (A : RSqMat 2) : ℝ :=
  (A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 * A 1 0

theorem realGinibreTwoDiscriminant_eq_trace_det (A : RSqMat 2) :
    realGinibreTwoDiscriminant A = A.trace ^ 2 - 4 * A.det := by
  simp [realGinibreTwoDiscriminant, Matrix.trace_fin_two,
    Matrix.det_fin_two]
  ring

theorem realGinibreTwo_charpoly_eval (A : RSqMat 2) (x : ℝ) :
    A.charpoly.eval x = x ^ 2 - A.trace * x + A.det := by
  rw [Matrix.charpoly_fin_two]
  simp

theorem realGinibreTwo_charpoly_degree (A : RSqMat 2) :
    A.charpoly.degree = 2 := by
  simpa using Matrix.charpoly_degree_eq_dim A

/-- A nonnegative discriminant makes the real characteristic polynomial
split completely, including the repeated-root boundary. -/
theorem realGinibreTwo_charpoly_splits_of_discriminant_nonneg
    (A : RSqMat 2) (hD : 0 ≤ realGinibreTwoDiscriminant A) :
    A.charpoly.Splits := by
  let s := Real.sqrt (realGinibreTwoDiscriminant A)
  let x := (A.trace + s) / 2
  apply Polynomial.Splits.of_degree_eq_two (x := x)
    (realGinibreTwo_charpoly_degree A)
  rw [realGinibreTwo_charpoly_eval]
  have hs : s ^ 2 = realGinibreTwoDiscriminant A := by
    dsimp [s]
    exact Real.sq_sqrt hD
  rw [realGinibreTwoDiscriminant_eq_trace_det] at hs
  dsimp [x]
  nlinarith

/-- A negative discriminant rules out every real root. -/
theorem realGinibreTwo_charpoly_not_isRoot_of_discriminant_neg
    (A : RSqMat 2) (hD : realGinibreTwoDiscriminant A < 0) (x : ℝ) :
    ¬ A.charpoly.IsRoot x := by
  intro hx
  have heval : x ^ 2 - A.trace * x + A.det = 0 := by
    rw [← realGinibreTwo_charpoly_eval]
    exact hx
  have hsq : discrim (1 : ℝ) (-A.trace) A.det =
      (2 * x - A.trace) ^ 2 := by
    simpa [sub_eq_add_neg] using
      (discrim_eq_sq_of_quadratic_eq_zero
        (a := (1 : ℝ)) (b := -A.trace) (c := A.det) (x := x) (by
          nlinarith [heval]))
  have hdisc : discrim (1 : ℝ) (-A.trace) A.det =
      realGinibreTwoDiscriminant A := by
    rw [realGinibreTwoDiscriminant_eq_trace_det]
    simp [discrim]
  rw [hdisc] at hsq
  nlinarith [sq_nonneg (2 * x - A.trace)]

/-- Every real `2 × 2` matrix has either two algebraic real eigenvalues or
none, according to the sign of its characteristic discriminant. -/
theorem realEigenvalueCount_two_eq_ite (A : RSqMat 2) :
    realEigenvalueCount 2 A =
      if 0 ≤ realGinibreTwoDiscriminant A then 2 else 0 := by
  unfold realEigenvalueCount
  split_ifs with hD
  · have hs := realGinibreTwo_charpoly_splits_of_discriminant_nonneg A hD
    rw [← hs.natDegree_eq_card_roots]
    simpa using A.charpoly_natDegree_eq_dim
  · have hneg : realGinibreTwoDiscriminant A < 0 := lt_of_not_ge hD
    have hzero : A.charpoly.roots = 0 := by
      rw [Polynomial.roots_eq_zero_iff_isRoot_eq_bot A.charpoly_monic.ne_zero]
      ext x
      change A.charpoly.IsRoot x ↔ False
      constructor
      · exact realGinibreTwo_charpoly_not_isRoot_of_discriminant_neg A hneg x
      · intro h
        contradiction
    rw [hzero]
    rfl

/-- The elementary radial tail integral used in the cone calculation. -/
theorem integral_Ioi_mul_exp_neg_sq_div_two (a : ℝ) :
    ∫ r in Ioi a, r * Real.exp (-(r ^ 2) / 2) =
      Real.exp (-(a ^ 2) / 2) := by
  let F : ℝ → ℝ := fun r => -Real.exp (-(r ^ 2) / 2)
  have hderiv : ∀ r : ℝ, HasDerivAt F
      (r * Real.exp (-(r ^ 2) / 2)) r := by
    intro r
    convert (((hasDerivAt_pow 2 r).neg.div_const 2).exp.neg) using 1 <;>
      norm_num [F] <;> ring
  have hint : IntegrableOn (fun r : ℝ =>
      r * Real.exp (-(r ^ 2) / 2)) (Ioi a) := by
    have hbase : IntegrableOn
        (fun r : ℝ => r * Real.exp (-(1 / 2) * r ^ 2)) (Ioi a) :=
      (integrable_mul_exp_neg_mul_sq (show (0 : ℝ) < 1 / 2 by norm_num)).integrableOn
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro r hr
    congr 2
    ring_nf
  have hlim : Tendsto F atTop (nhds 0) := by
    have hsq : Tendsto (fun r : ℝ => -(r ^ 2) / 2) atTop atBot := by
      convert (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg
        (show (-1 / 2 : ℝ) < 0 by norm_num) using 1 <;> ring
    simpa [F] using (Real.tendsto_exp_atBot.comp hsq).neg
  simpa [F] using integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r _ => hderiv r) hint hlim

/-- Outside of a centered circle of radius `a` in two real coordinates. -/
def gaussianPairRadialTail (a : ℝ) : Set (ℝ × ℝ) :=
  {p | a ^ 2 ≤ p.1 ^ 2 + p.2 ^ 2}

theorem measurableSet_gaussianPairRadialTail (a : ℝ) :
    MeasurableSet (gaussianPairRadialTail a) := by
  exact measurableSet_le measurable_const
    ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2))

/-- Convert a measurable event under two independent standard Gaussians to
the corresponding ordinary density integral. -/
theorem gaussianReal_prod_real_apply (s : Set (ℝ × ℝ))
    (hs : MeasurableSet s) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real s =
      ∫ p in s,
        gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2 := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [prod_withDensity
    (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
  rw [measureReal_def, withDensity_apply _ hs]
  rw [← integral_toReal (f := fun p : ℝ × ℝ =>
      gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2)
    (μ := (volume.prod volume).restrict s)
    (((measurable_gaussianPDF 0 1).comp measurable_fst).mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd) |>.aemeasurable)
    (ae_of_all _ fun p => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top)]
  apply integral_congr_ae
  filter_upwards with p
  simp [toReal_gaussianPDF]

theorem gaussianPDFReal_zero_one_prod_polar (r theta : ℝ) :
    r * (gaussianPDFReal 0 1 (r * Real.cos theta) *
      gaussianPDFReal 0 1 (r * Real.sin theta)) =
      r / (2 * Real.pi) * Real.exp (-(r ^ 2) / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [show r *
      ((Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(r * Real.cos theta) ^ 2 / 2) *
        ((Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(r * Real.sin theta) ^ 2 / 2))) =
      r * (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (-(r * Real.cos theta) ^ 2 / 2) *
          Real.exp (-(r * Real.sin theta) ^ 2 / 2)) by ring]
  rw [← Real.exp_add]
  have harg :
      (-(r * Real.cos theta) ^ 2 / 2 +
        -(r * Real.sin theta) ^ 2 / 2) = -(r ^ 2) / 2 := by
    calc
      _ = -(r ^ 2) * (Real.cos theta ^ 2 + Real.sin theta ^ 2) / 2 := by
        ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
  rw [harg]
  have hsqrt : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hcoeff : (Real.sqrt (2 * Real.pi))⁻¹ *
      (Real.sqrt (2 * Real.pi))⁻¹ = (2 * Real.pi)⁻¹ := by
    rw [← mul_inv, ← pow_two, hsqrt]
  rw [show r * (Real.sqrt (2 * Real.pi))⁻¹ *
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(r ^ 2) / 2) =
      r * ((Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.sqrt (2 * Real.pi))⁻¹) *
          Real.exp (-(r ^ 2) / 2) by ring]
  rw [hcoeff]
  rfl

theorem integral_gaussianPDFReal_prod_radialTail
    (a : ℝ) (ha : 0 ≤ a) :
    ∫ p in gaussianPairRadialTail a,
        gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2 =
      Real.exp (-(a ^ 2) / 2) := by
  let d : ℝ × ℝ → ℝ := fun p =>
    gaussianPDFReal 0 1 p.1 * gaussianPDFReal 0 1 p.2
  let g : ℝ → ℝ := fun r =>
    r / (2 * Real.pi) * Real.exp (-(r ^ 2) / 2)
  rw [← integral_indicator (measurableSet_gaussianPairRadialTail a)]
  rw [← integral_comp_polarCoord_symm]
  have hpolar :
      (∫ p in polarCoord.target,
          p.1 • (gaussianPairRadialTail a).indicator d (polarCoord.symm p)) =
        ∫ p in polarCoord.target, (if a ≤ p.1 then g p.1 else 0) := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    have hr : 0 < p.1 := hp.1
    have hsq :
        (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
      simp only [polarCoord_symm_apply]
      calc
        (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 =
            p.1 ^ 2 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
        _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
    have htail : polarCoord.symm p ∈ gaussianPairRadialTail a ↔ a ≤ p.1 := by
      rw [gaussianPairRadialTail, mem_setOf_eq, hsq]
      constructor
      · intro h
        nlinarith [sq_nonneg (p.1 - a)]
      · intro h
        nlinarith
    change p.1 • (gaussianPairRadialTail a).indicator d (polarCoord.symm p) =
      (if a ≤ p.1 then g p.1 else 0)
    by_cases h : a ≤ p.1
    · rw [if_pos h, indicator_of_mem (htail.mpr h)]
      change p.1 * d (polarCoord.symm p) = g p.1
      simpa [d, g, polarCoord_symm_apply] using
        gaussianPDFReal_zero_one_prod_polar p.1 p.2
    · rw [if_neg h, Set.indicator_of_notMem (fun hm => h (htail.mp hm))]
      simp
  rw [hpolar]
  rw [polarCoord_target]
  have hprod :
      (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          (if a ≤ p.1 then g p.1 else 0)) =
        (∫ r in Ioi (0 : ℝ), if a ≤ r then g r else 0) *
          ∫ theta in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    simpa only [mul_one] using
      (setIntegral_prod_mul
        (fun r : ℝ => if a ≤ r then g r else 0)
        (fun _ : ℝ => (1 : ℝ)) (Ioi (0 : ℝ))
        (Ioo (-Real.pi) Real.pi))
  rw [hprod]
  have hrad :
      (∫ r in Ioi (0 : ℝ), if a ≤ r then g r else 0) =
        ∫ r in Ici a, g r := by
    have hfun : (fun r : ℝ => if a ≤ r then g r else 0) =
        (Ici a).indicator g := by
      funext r
      simp only [indicator, mem_Ici]
    rw [hfun, setIntegral_indicator measurableSet_Ici]
    rcases ha.eq_or_lt with rfl | ha_pos
    · have hset : Ioi (0 : ℝ) ∩ Ici 0 = Ioi 0 := by
        ext r
        simp only [mem_inter_iff, mem_Ioi, mem_Ici]
        constructor
        · exact fun h => h.1
        · intro h
          exact ⟨h, h.le⟩
      rw [hset]
      exact (integral_Ici_eq_integral_Ioi (f := g) (x := (0 : ℝ))).symm
    · have hset : Ioi (0 : ℝ) ∩ Ici a = Ici a := by
        ext r
        simp only [mem_inter_iff, mem_Ioi, mem_Ici]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨ha_pos.trans_le h, h⟩
      rw [hset]
  rw [hrad]
  rw [integral_Ici_eq_integral_Ioi]
  have hrad_eval : (∫ r in Ioi a, g r) =
      (2 * Real.pi)⁻¹ * Real.exp (-(a ^ 2) / 2) := by
    rw [show (∫ r in Ioi a, g r) =
        (2 * Real.pi)⁻¹ *
          ∫ r in Ioi a, r * Real.exp (-(r ^ 2) / 2) by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      simp [g, div_eq_mul_inv]
      ring]
    rw [integral_Ioi_mul_exp_neg_sq_div_two]
  rw [hrad_eval]
  have htheta : (∫ theta in Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
    simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
      univ_inter]
    rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    simp [smul_eq_mul]
    ring
  rw [htheta]
  field_simp [ne_of_gt Real.pi_pos]

theorem gaussianReal_prod_radialTail_real
    (a : ℝ) (ha : 0 ≤ a) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
        (gaussianPairRadialTail a) =
      Real.exp (-(a ^ 2) / 2) := by
  rw [gaussianReal_prod_real_apply _ (measurableSet_gaussianPairRadialTail a)]
  exact integral_gaussianPDFReal_prod_radialTail a ha

def gaussianVectorTwoRadialTail (a : ℝ) : Set (Fin 2 → ℝ) :=
  {x | a ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2}

theorem measurableSet_gaussianVectorTwoRadialTail (a : ℝ) :
    MeasurableSet (gaussianVectorTwoRadialTail a) := by
  exact measurableSet_le measurable_const
    (((measurable_pi_apply 0).pow_const 2).add
      ((measurable_pi_apply 1).pow_const 2))

theorem standardGaussianVectorMeasure_two_radialTail_real
    (a : ℝ) (ha : 0 ≤ a) :
    (standardGaussianVectorMeasure 2).real
        (gaussianVectorTwoRadialTail a) =
      Real.exp (-(a ^ 2) / 2) := by
  let e : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.finTwoArrow
  have hpre : e ⁻¹' gaussianPairRadialTail a =
      gaussianVectorTwoRadialTail a := by
    ext x
    simp [e, gaussianPairRadialTail, gaussianVectorTwoRadialTail,
      MeasurableEquiv.finTwoArrow_apply]
  calc
    (standardGaussianVectorMeasure 2).real
        (gaussianVectorTwoRadialTail a) =
        (standardGaussianVectorMeasure 2).real
          (e ⁻¹' gaussianPairRadialTail a) := by rw [hpre]
    _ = ((standardGaussianVectorMeasure 2).map e).real
          (gaussianPairRadialTail a) := by
      rw [map_measureReal_apply e.measurable
        (measurableSet_gaussianPairRadialTail a)]
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
          (gaussianPairRadialTail a) := by
      rw [show (standardGaussianVectorMeasure 2).map e =
          (gaussianReal 0 1).prod (gaussianReal 0 1) by
        exact (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq]
    _ = _ := gaussianReal_prod_radialTail_real a ha

def gaussianConeProduct : Set (ℝ × (Fin 2 → ℝ)) :=
  {p | p.1 ^ 2 ≤ p.2 0 ^ 2 + p.2 1 ^ 2}

theorem measurableSet_gaussianConeProduct :
    MeasurableSet gaussianConeProduct := by
  exact measurableSet_le (measurable_fst.pow_const 2)
    (((((measurable_pi_apply 0).comp measurable_snd).pow_const 2).add
      (((measurable_pi_apply 1).comp measurable_snd).pow_const 2)))

theorem gaussianConeProduct_real_eq_integral :
    ((gaussianReal 0 1).prod (standardGaussianVectorMeasure 2)).real
        gaussianConeProduct =
      ∫ z : ℝ, Real.exp (-(z ^ 2) / 2) ∂gaussianReal 0 1 := by
  rw [measureReal_def, Measure.prod_apply measurableSet_gaussianConeProduct]
  rw [← integral_toReal
    (f := fun z : ℝ => (standardGaussianVectorMeasure 2)
      ((fun x : Fin 2 → ℝ => (z, x)) ⁻¹' gaussianConeProduct))
    (μ := gaussianReal 0 1)
    ((measurable_measure_prodMk_left measurableSet_gaussianConeProduct).aemeasurable)
    (ae_of_all _ fun z => measure_lt_top _ _)]
  apply integral_congr_ae
  filter_upwards with z
  rw [show (fun x : Fin 2 → ℝ => (z, x)) ⁻¹' gaussianConeProduct =
      gaussianVectorTwoRadialTail |z| by
    ext x
    simp only [gaussianConeProduct, gaussianVectorTwoRadialTail, mem_preimage,
      mem_setOf_eq]
    rw [sq_abs]]
  rw [← measureReal_def]
  simpa [sq_abs] using
    standardGaussianVectorMeasure_two_radialTail_real |z| (abs_nonneg z)

theorem integral_exp_neg_sq_div_two_gaussianReal :
    (∫ z : ℝ, Real.exp (-(z ^ 2) / 2) ∂gaussianReal 0 1) =
      Real.sqrt 2 / 2 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul]
  rw [show (fun z : ℝ =>
      gaussianPDFReal 0 1 z * Real.exp (-(z ^ 2) / 2)) =
      fun z => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 : ℝ) * z ^ 2) by
    funext z
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [show (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) *
        Real.exp (-z ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (-z ^ 2 / 2) * Real.exp (-z ^ 2 / 2)) by ring]
    rw [← Real.exp_add]
    congr 1
    ring]
  rw [integral_const_mul, integral_gaussian]
  norm_num
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  field_simp [hsqrtpi, hsqrt2]
  nlinarith

theorem gaussianConeProduct_real :
    ((gaussianReal 0 1).prod (standardGaussianVectorMeasure 2)).real
        gaussianConeProduct = Real.sqrt 2 / 2 := by
  rw [gaussianConeProduct_real_eq_integral,
    integral_exp_neg_sq_div_two_gaussianReal]

def gaussianVectorConeThree : Set (Fin 3 → ℝ) :=
  {x | x 2 ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2}

theorem measurableSet_gaussianVectorConeThree :
    MeasurableSet gaussianVectorConeThree := by
  exact measurableSet_le ((measurable_pi_apply 2).pow_const 2)
    (((measurable_pi_apply 0).pow_const 2).add
      ((measurable_pi_apply 1).pow_const 2))

theorem standardGaussianVectorMeasure_three_cone_real :
    (standardGaussianVectorMeasure 3).real gaussianVectorConeThree =
      Real.sqrt 2 / 2 := by
  let e : (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  have hpre : e ⁻¹' gaussianConeProduct = gaussianVectorConeThree := by
    ext x
    simp [e, gaussianConeProduct, gaussianVectorConeThree,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth_last, Fin.init]
    have h0 : Fin.removeNth (2 : Fin 3) x (0 : Fin 2) = x 0 := by
      rw [Fin.removeNth_apply]
      congr 1
    have h1 : Fin.removeNth (2 : Fin 3) x (1 : Fin 2) = x 1 := by
      rw [Fin.removeNth_apply]
      congr 1
    rw [h0, h1]
  calc
    (standardGaussianVectorMeasure 3).real gaussianVectorConeThree =
        (standardGaussianVectorMeasure 3).real
          (e ⁻¹' gaussianConeProduct) := by rw [hpre]
    _ = ((standardGaussianVectorMeasure 3).map e).real
          gaussianConeProduct := by
      rw [map_measureReal_apply e.measurable measurableSet_gaussianConeProduct]
    _ = ((gaussianReal 0 1).prod
          (standardGaussianVectorMeasure 2)).real gaussianConeProduct := by
      rw [show (standardGaussianVectorMeasure 3).map e =
          (gaussianReal 0 1).prod (standardGaussianVectorMeasure 2) by
        exact (measurePreserving_piFinSuccAbove
          (fun _ : Fin 3 => gaussianReal 0 1) (Fin.last 2)).map_eq]
    _ = _ := gaussianConeProduct_real

noncomputable def ginibreTwoRotationScale : ℝ := Real.sqrt 2 / 2

theorem ginibreTwoRotationScale_sq : ginibreTwoRotationScale ^ 2 = 1 / 2 := by
  unfold ginibreTwoRotationScale
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
  nlinarith

noncomputable def ginibreTwoRotationMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ginibreTwoRotationScale, 0, 0, -ginibreTwoRotationScale;
     0, ginibreTwoRotationScale, ginibreTwoRotationScale, 0;
     0, ginibreTwoRotationScale, -ginibreTwoRotationScale, 0;
     ginibreTwoRotationScale, 0, 0, ginibreTwoRotationScale]

noncomputable def ginibreTwoRotationOrthogonal :
    Matrix.orthogonalGroup (Fin 4) ℝ :=
  ⟨ginibreTwoRotationMatrix, by
    have hs := ginibreTwoRotationScale_sq
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ginibreTwoRotationMatrix, Matrix.mul_apply,
        Fin.sum_univ_succ, Matrix.one_apply] <;>
      nlinarith⟩

def gaussianVectorConeFour : Set (Fin 4 → ℝ) :=
  {x | x 2 ^ 2 ≤ x 0 ^ 2 + x 1 ^ 2}

theorem measurableSet_gaussianVectorConeFour :
    MeasurableSet gaussianVectorConeFour := by
  exact measurableSet_le ((measurable_pi_apply 2).pow_const 2)
    (((measurable_pi_apply 0).pow_const 2).add
      ((measurable_pi_apply 1).pow_const 2))

theorem standardGaussianVectorMeasure_four_cone_real :
    (standardGaussianVectorMeasure 4).real gaussianVectorConeFour =
      Real.sqrt 2 / 2 := by
  let e : (Fin 4 → ℝ) ≃ᵐ (ℝ × (Fin 3 → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) (Fin.last 3)
  let target : Set (ℝ × (Fin 3 → ℝ)) :=
    Set.univ ×ˢ gaussianVectorConeThree
  have htarget : MeasurableSet target :=
    MeasurableSet.univ.prod measurableSet_gaussianVectorConeThree
  have hpre : e ⁻¹' target = gaussianVectorConeFour := by
    ext x
    simp [e, target, gaussianVectorConeThree, gaussianVectorConeFour,
      MeasurableEquiv.piFinSuccAbove_apply]
    have h0 : Fin.removeNth (3 : Fin 4) x (0 : Fin 3) = x 0 := by
      rw [Fin.removeNth_apply]
      congr 1
    have h1 : Fin.removeNth (3 : Fin 4) x (1 : Fin 3) = x 1 := by
      rw [Fin.removeNth_apply]
      congr 1
    have h2 : Fin.removeNth (3 : Fin 4) x (2 : Fin 3) = x 2 := by
      rw [Fin.removeNth_apply]
      congr 1
    rw [h0, h1, h2]
  calc
    (standardGaussianVectorMeasure 4).real gaussianVectorConeFour =
        (standardGaussianVectorMeasure 4).real (e ⁻¹' target) := by
      rw [hpre]
    _ = ((standardGaussianVectorMeasure 4).map e).real target := by
      rw [map_measureReal_apply e.measurable htarget]
    _ = ((gaussianReal 0 1).prod
          (standardGaussianVectorMeasure 3)).real target := by
      rw [show (standardGaussianVectorMeasure 4).map e =
          (gaussianReal 0 1).prod (standardGaussianVectorMeasure 3) by
        exact (measurePreserving_piFinSuccAbove
          (fun _ : Fin 4 => gaussianReal 0 1) (Fin.last 3)).map_eq]
    _ = (gaussianReal 0 1).real Set.univ *
          (standardGaussianVectorMeasure 3).real gaussianVectorConeThree := by
      exact measureReal_prod_prod Set.univ gaussianVectorConeThree
    _ = _ := by
      rw [standardGaussianVectorMeasure_three_cone_real]
      simp

def ginibreVectorDiscriminantEvent : Set (Fin 4 → ℝ) :=
  {x | 0 ≤ (x 0 - x 3) ^ 2 + 4 * x 1 * x 2}

theorem measurableSet_ginibreVectorDiscriminantEvent :
    MeasurableSet ginibreVectorDiscriminantEvent := by
  exact measurableSet_le measurable_const
    (((((measurable_pi_apply 0).sub (measurable_pi_apply 3)).pow_const 2).add
      ((measurable_const.mul (measurable_pi_apply 1)).mul
        (measurable_pi_apply 2))))

theorem ginibreTwoRotation_preimage_cone :
    (fun x : Fin 4 → ℝ =>
      Matrix.mulVec ginibreTwoRotationMatrix x) ⁻¹'
        gaussianVectorConeFour =
      ginibreVectorDiscriminantEvent := by
  ext x
  have hs := ginibreTwoRotationScale_sq
  simp only [gaussianVectorConeFour, ginibreVectorDiscriminantEvent,
    mem_preimage, mem_setOf_eq]
  simp [ginibreTwoRotationMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring_nf
  rw [hs]
  norm_num
  constructor <;> intro h <;> nlinarith

theorem standardGaussianVectorMeasure_four_discriminant_real :
    (standardGaussianVectorMeasure 4).real ginibreVectorDiscriminantEvent =
      Real.sqrt 2 / 2 := by
  let T : (Fin 4 → ℝ) → (Fin 4 → ℝ) := fun x =>
    Matrix.mulVec ginibreTwoRotationMatrix x
  have hT : Measurable T := by fun_prop
  calc
    (standardGaussianVectorMeasure 4).real ginibreVectorDiscriminantEvent =
        (standardGaussianVectorMeasure 4).real
          (T ⁻¹' gaussianVectorConeFour) := by
      rw [ginibreTwoRotation_preimage_cone]
    _ = ((standardGaussianVectorMeasure 4).map T).real
          gaussianVectorConeFour := by
      rw [map_measureReal_apply hT measurableSet_gaussianVectorConeFour]
    _ = (standardGaussianVectorMeasure 4).real
          gaussianVectorConeFour := by
      rw [show (standardGaussianVectorMeasure 4).map T =
          standardGaussianVectorMeasure 4 by
        exact standardGaussianVectorMeasure_map_orthogonalGroup 4
          ginibreTwoRotationOrthogonal]
    _ = _ := standardGaussianVectorMeasure_four_cone_real

/-- Flatten the four entries of a `2 × 2` matrix in row-major order. -/
def ginibreTwoEntryVector (A : RSqMat 2) : Fin 4 → ℝ :=
  fun k =>
    let p := finProdFinEquiv.symm k
    A p.1 p.2

theorem measurable_ginibreTwoEntryVector :
    Measurable ginibreTwoEntryVector := by
  unfold ginibreTwoEntryVector
  fun_prop

/-- Flattening the nested real-Ginibre product measure gives the explicit
four-dimensional standard Gaussian product measure. -/
theorem realGinibreMeasure_two_map_ginibreTwoEntryVector :
    (realGinibreMeasure 2).map ginibreTwoEntryVector =
      standardGaussianVectorMeasure 4 := by
  unfold realGinibreMeasure standardGaussianVectorMeasure
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_ginibreTwoEntryVector
    (MeasurableSet.univ_pi hs)]
  have hpre : ginibreTwoEntryVector ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i : Fin 2 =>
        Set.univ.pi (fun j : Fin 2 => s (finProdFinEquiv (i, j)))) := by
    ext A
    simp only [mem_preimage, Set.mem_pi]
    constructor
    · intro h i hi j hj
      simpa [ginibreTwoEntryVector] using
        h (finProdFinEquiv (i, j)) (by simp)
    · intro h k hk
      let p : Fin 2 × Fin 2 :=
        (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm k
      have hk := h p.1 (by simp) p.2 (by simp)
      have hp : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) p = k := by
        exact (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).apply_symm_apply k
      change A p.1 p.2 ∈ s k
      change A p.1 p.2 ∈ s (finProdFinEquiv (p.1, p.2)) at hk
      have heta : (p.1, p.2) = p := Prod.eta p
      rw [heta, hp] at hk
      exact hk
  rw [hpre]
  calc
    (Measure.pi (fun _ : Fin 2 =>
        Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)))
        (Set.univ.pi (fun i : Fin 2 =>
          Set.univ.pi (fun j : Fin 2 => s (finProdFinEquiv (i, j))))) =
      ∏ i : Fin 2, (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1))
        (Set.univ.pi (fun j : Fin 2 => s (finProdFinEquiv (i, j)))) := by
          exact Measure.pi_pi _ _
    _ = ∏ i : Fin 2, ∏ j : Fin 2,
        gaussianReal 0 1 (s (finProdFinEquiv (i, j))) := by
          congr 1
          funext i
          exact Measure.pi_pi _ _
    _ = ∏ k : Fin 4, gaussianReal 0 1 (s k) := by
      rw [← Fintype.prod_prod_type']
      exact Fintype.prod_equiv finProdFinEquiv
        (fun p : Fin 2 × Fin 2 => gaussianReal 0 1 (s (finProdFinEquiv p)))
        (fun k : Fin 4 => gaussianReal 0 1 (s k))
        (fun p => by simp)

/-- The measurable set of real `2 × 2` matrices whose characteristic
polynomial has nonnegative discriminant. -/
def realGinibreTwoNonnegativeDiscriminantSet : Set (RSqMat 2) :=
  {A | 0 ≤ realGinibreTwoDiscriminant A}

theorem measurableSet_realGinibreTwoNonnegativeDiscriminantSet :
    MeasurableSet realGinibreTwoNonnegativeDiscriminantSet := by
  unfold realGinibreTwoNonnegativeDiscriminantSet
  apply measurableSet_le measurable_const
  unfold realGinibreTwoDiscriminant
  fun_prop

theorem ginibreTwoEntryVector_preimage_discriminantEvent :
    ginibreTwoEntryVector ⁻¹' ginibreVectorDiscriminantEvent =
      realGinibreTwoNonnegativeDiscriminantSet := by
  have h0 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 0 = (0, 0) := by
    decide
  have h1 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 1 = (0, 1) := by
    decide
  have h2 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 2 = (1, 0) := by
    decide
  have h3 : (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm 3 = (1, 1) := by
    decide
  ext A
  simp only [mem_preimage, ginibreVectorDiscriminantEvent,
    realGinibreTwoNonnegativeDiscriminantSet, mem_setOf_eq,
    ginibreTwoEntryVector]
  rw [h0, h1, h2, h3]
  simp [realGinibreTwoDiscriminant]

/-- The exact probability that a real `2 × 2` Ginibre matrix has
nonnegative characteristic discriminant. -/
theorem realGinibreMeasure_two_discriminant_nonnegative_real :
    (realGinibreMeasure 2).real
        realGinibreTwoNonnegativeDiscriminantSet =
      Real.sqrt 2 / 2 := by
  calc
    (realGinibreMeasure 2).real
        realGinibreTwoNonnegativeDiscriminantSet =
        (realGinibreMeasure 2).real
          (ginibreTwoEntryVector ⁻¹' ginibreVectorDiscriminantEvent) := by
      rw [ginibreTwoEntryVector_preimage_discriminantEvent]
    _ = ((realGinibreMeasure 2).map ginibreTwoEntryVector).real
          ginibreVectorDiscriminantEvent := by
      rw [map_measureReal_apply measurable_ginibreTwoEntryVector
        measurableSet_ginibreVectorDiscriminantEvent]
    _ = (standardGaussianVectorMeasure 4).real
          ginibreVectorDiscriminantEvent := by
      rw [realGinibreMeasure_two_map_ginibreTwoEntryVector]
    _ = _ := standardGaussianVectorMeasure_four_discriminant_real

/-- The genuine matrix expectation in dimension two. -/
theorem expectedRealEigenvalueCount_two :
    expectedRealEigenvalueCount 2 = Real.sqrt 2 := by
  unfold expectedRealEigenvalueCount
  have hfun : (fun A : RSqMat 2 => (realEigenvalueCount 2 A : ℝ)) =
      realGinibreTwoNonnegativeDiscriminantSet.indicator
        (fun _ : RSqMat 2 => (2 : ℝ)) := by
    funext A
    rw [realEigenvalueCount_two_eq_ite]
    by_cases hD : 0 ≤ realGinibreTwoDiscriminant A
    · simp [realGinibreTwoNonnegativeDiscriminantSet, hD]
    · simp [realGinibreTwoNonnegativeDiscriminantSet, hD]
  rw [hfun, integral_indicator_const (2 : ℝ)
    measurableSet_realGinibreTwoNonnegativeDiscriminantSet]
  rw [realGinibreMeasure_two_discriminant_nonnegative_real]
  simp [smul_eq_mul]

/-- Dimension two of the finite real-Ginibre expectation formula, now as an
equality between the genuine expectation and the closed form. -/
theorem expectedRealEigenvalueCount_eq_closedForm_two :
    expectedRealEigenvalueCount 2 =
      realGinibreExpectedCountClosedForm 2 := by
  rw [expectedRealEigenvalueCount_two,
    realGinibreExpectedCountClosedForm_two]

end

end NumStability
