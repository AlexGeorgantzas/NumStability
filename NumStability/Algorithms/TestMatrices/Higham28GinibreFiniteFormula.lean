/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedConclusion
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedKernel
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedIncidence

/-! # Higham Chapter 28: closing the finite real-Ginibre expectation formula

This file discharges the last gate-blocker of Chapter 28, row 28-P3.  The
Edelman--Kostlan--Shub incidence chain reduces the finite expected
real-eigenvalue count to a two-step *signed pair shift*, and the signed
incidence formula was applied twice in `Higham28GinibreSignedIncidence`,
producing:

* a first transfer `expectedGinibreAlternatingPairCount (n+1)
    = ginibreCorollary31Factor (n+1) * ginibreSignedOneRootMoment n`; and
* a *fixed-parameter* second transfer, for each external spectral value `x`,
  `∫ A, det (A - x•1) * alt(below (A,x)) = ginibreCorollary31Factor (m+1)
    * ginibreSignedTwoRootSlice m x`, conditional only on the natural
  integrability of the shifted determinant.

What was missing was the *measure-theoretic assembly*: integrating the
fixed-parameter transfer over the external Gaussian coordinate and moving the
inner matrix integral through the two scalar Gaussians (Fubini), then closing
the resulting two-scalar integral with the already-proven characteristic
product moment.  This file supplies that assembly unconditionally, obtaining

`ginibreSignedOneRootMoment (m+1)
   = ginibreCorollary31Factor (m+1) * ginibreOrderedGaussianKernelMoment m`,

feeds it through `signedPairShift_of_kernelTransfer` and
`realGinibreFiniteExpectationFormula_of_signedPairShift`, and thereby proves
`RealGinibreFiniteExpectationFormula` for every positive dimension, hence the
premise-free `RealGinibreExpectedCountLimit`.

The only genuinely new analytic content is joint integrability of the
polynomial determinant integrands over the product Gaussian laws, which is
handled by a Tonelli / characteristic-product bound.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory Set Filter

noncomputable section

local instance ch28gfMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-! ## Measurability and the characteristic-product value -/

/-- Joint measurability of the signed shifted determinant. -/
theorem ch28gf_measurable_det_shift (n : ℕ) :
    Measurable (fun p : RSqMat n × ℝ =>
      (p.1 - p.2 • (1 : RSqMat n)).det) := by
  simp_rw [Matrix.det_apply]
  apply Finset.measurable_sum
  intro σ hσ
  apply Measurable.const_smul
  apply Finset.measurable_prod
  intro i hi
  have hij : Measurable (fun A : RSqMat n => A (σ i) i) := by fun_prop
  exact (hij.comp measurable_fst).sub (measurable_snd.mul measurable_const)

/-- Matrix-only shifted determinant measurability, at a fixed spectral
parameter. -/
theorem ch28gf_measurable_det_shift_matrix (n : ℕ) (x : ℝ) :
    Measurable (fun A : RSqMat n => (A - x • (1 : RSqMat n)).det) :=
  (ch28gf_measurable_det_shift n).comp (measurable_id.prodMk measurable_const)

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

/-- The coincident matrix moment equals `𝔼 det(B - u I)^2`. -/
theorem ch28gf_integral_detSq_eq (n : ℕ) (u : ℝ) :
    (∫ B : RSqMat n, (B - u • (1 : RSqMat n)).det ^ 2
      ∂realGinibreMeasure n) = ch28gf_charProdVal n u := by
  rw [ch28gf_charProdVal, ← integral_realGinibre_det_sub_smul_one_mul_det_sub_smul_one n u u]
  apply integral_congr_ae
  filter_upwards with B
  rw [pow_two]

/-- The coincident matrix moment integrand is integrable over the matrix. -/
theorem ch28gf_integrable_detSq_matrix (n : ℕ) (u : ℝ) :
    Integrable (fun B : RSqMat n => (B - u • (1 : RSqMat n)).det ^ 2)
      (realGinibreMeasure n) := by
  apply (integrable_realGinibre_det_sub_smul_one_mul_det_sub_smul_one n u u).congr
  filter_upwards with B
  rw [pow_two]

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

/-! ## The crux: joint integrability over the product Gaussian law -/

/-- Joint integrability of a nonnegative scalar weight times the squared
shifted determinant, over the product real-Ginibre / Gaussian law.  Proved by
Tonelli, evaluating the inner matrix integral with the characteristic-product
moment.  The hypothesis is only the (polynomial) integrability of the weight
against the coincident characteristic-product value. -/
theorem ch28gf_integrable_wgt_detSq (n : ℕ) (w : ℝ → ℝ)
    (hw_meas : Measurable w) (hw_nonneg : ∀ u, 0 ≤ w u)
    (hw_int : Integrable (fun u => w u * ch28gf_charProdVal n u) (gaussianReal 0 1)) :
    Integrable
      (fun p : RSqMat n × ℝ => w p.2 * (p.1 - p.2 • (1 : RSqMat n)).det ^ 2)
      ((realGinibreMeasure n).prod (gaussianReal 0 1)) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  have hmeas : Measurable
      (fun p : RSqMat n × ℝ => w p.2 * (p.1 - p.2 • (1 : RSqMat n)).det ^ 2) :=
    (hw_meas.comp measurable_snd).mul ((ch28gf_measurable_det_shift n).pow_const 2)
  have hnn : ∀ p : RSqMat n × ℝ,
      0 ≤ w p.2 * (p.1 - p.2 • (1 : RSqMat n)).det ^ 2 :=
    fun p => mul_nonneg (hw_nonneg _) (sq_nonneg _)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    (∫⁻ p : RSqMat n × ℝ,
        ENNReal.ofReal ‖w p.2 * (p.1 - p.2 • (1 : RSqMat n)).det ^ 2‖
        ∂(realGinibreMeasure n).prod (gaussianReal 0 1))
        = ∫⁻ p : RSqMat n × ℝ,
            ENNReal.ofReal (w p.2 * (p.1 - p.2 • (1 : RSqMat n)).det ^ 2)
          ∂(realGinibreMeasure n).prod (gaussianReal 0 1) := by
          apply lintegral_congr
          intro p
          rw [Real.norm_eq_abs, abs_of_nonneg (hnn p)]
    _ = ∫⁻ u : ℝ, ∫⁻ B : RSqMat n,
            ENNReal.ofReal (w u * (B - u • (1 : RSqMat n)).det ^ 2)
          ∂realGinibreMeasure n ∂gaussianReal 0 1 :=
          lintegral_prod_symm' _ hmeas.ennreal_ofReal
    _ = ∫⁻ u : ℝ, ENNReal.ofReal (w u * ch28gf_charProdVal n u)
          ∂gaussianReal 0 1 := by
          apply lintegral_congr
          intro u
          rw [← ofReal_integral_eq_lintegral_ofReal
                ((ch28gf_integrable_detSq_matrix n u).const_mul (w u))
                (ae_of_all _ (fun B => mul_nonneg (hw_nonneg u) (sq_nonneg _)))]
          rw [integral_const_mul, ch28gf_integral_detSq_eq]
    _ = ENNReal.ofReal
          (∫ u : ℝ, w u * ch28gf_charProdVal n u ∂gaussianReal 0 1) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hw_int
                (ae_of_all _ (fun u =>
                  mul_nonneg (hw_nonneg u) (ch28gf_charProdVal_nonneg n u)))]
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The single shifted determinant is integrable over the real-Ginibre law,
unconditionally.  This discharges the sole hypothesis of the fixed-parameter
second incidence transfer. -/
theorem ch28gf_integrable_det_shift_matrix (n : ℕ) (x : ℝ) :
    Integrable (fun A : RSqMat n => (A - x • (1 : RSqMat n)).det)
      (realGinibreMeasure n) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  have hdom : Integrable
      (fun A : RSqMat n => (1 + (A - x • (1 : RSqMat n)).det ^ 2) / 2)
      (realGinibreMeasure n) :=
    (((integrable_const (1 : ℝ)).add
      (ch28gf_integrable_detSq_matrix n x)).div_const 2)
  apply hdom.mono' (ch28gf_measurable_det_shift_matrix n x).aestronglyMeasurable
  filter_upwards with A
  rw [Real.norm_eq_abs]
  exact ch28gf_abs_le_one_add_sq _

/-! ## First assembly: the signed one-root moment as an integrated slice -/

/-- Joint integrability of the signed one-root moment integrand over the
product real-Ginibre / Gaussian law. -/
theorem ch28gf_integrable_oneRootIntegrand (n : ℕ) :
    Integrable
      (fun p : RSqMat n × ℝ =>
        (p.1 - p.2 • (1 : RSqMat n)).det *
          ginibreAlternatingCount (realEigenvalueBelowCount p))
      ((realGinibreMeasure n).prod (gaussianReal 0 1)) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  have hdetSq : Integrable
      (fun p : RSqMat n × ℝ => (p.1 - p.2 • (1 : RSqMat n)).det ^ 2)
      ((realGinibreMeasure n).prod (gaussianReal 0 1)) := by
    have h := ch28gf_integrable_wgt_detSq n (fun _ => 1) measurable_const
      (fun _ => zero_le_one) (by simpa using ch28gf_integrable_charProdVal n)
    simpa using h
  have hdom : Integrable
      (fun p : RSqMat n × ℝ =>
        (n : ℝ) * ((1 + (p.1 - p.2 • (1 : RSqMat n)).det ^ 2) / 2))
      ((realGinibreMeasure n).prod (gaussianReal 0 1)) :=
    (((integrable_const (1 : ℝ)).add hdetSq).div_const 2).const_mul (n : ℝ)
  have hmeas : Measurable
      (fun p : RSqMat n × ℝ =>
        (p.1 - p.2 • (1 : RSqMat n)).det *
          ginibreAlternatingCount (realEigenvalueBelowCount p)) :=
    (ch28gf_measurable_det_shift n).mul
      ((measurable_of_countable (fun r : ℕ => ginibreAlternatingCount r)).comp
        (measurable_realEigenvalueBelowCount n))
  apply hdom.mono' hmeas.aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_mul]
  have halt : |ginibreAlternatingCount (realEigenvalueBelowCount p)| ≤ (n : ℝ) :=
    (abs_ginibreAlternatingCount_le _).trans
      (by exact_mod_cast realEigenvalueBelowCount_le p)
  have hdetabs : |(p.1 - p.2 • (1 : RSqMat n)).det| ≤
      (1 + (p.1 - p.2 • (1 : RSqMat n)).det ^ 2) / 2 :=
    ch28gf_abs_le_one_add_sq _
  have hnn : (0 : ℝ) ≤ (1 + (p.1 - p.2 • (1 : RSqMat n)).det ^ 2) / 2 := by positivity
  calc
    |(p.1 - p.2 • (1 : RSqMat n)).det| *
        |ginibreAlternatingCount (realEigenvalueBelowCount p)|
        ≤ ((1 + (p.1 - p.2 • (1 : RSqMat n)).det ^ 2) / 2) * (n : ℝ) := by
          apply mul_le_mul hdetabs halt (abs_nonneg _) hnn
    _ = (n : ℝ) * ((1 + (p.1 - p.2 • (1 : RSqMat n)).det ^ 2) / 2) := by ring

/-- **First assembly.** The signed one-root moment in dimension `m+1` is the
Corollary-3.1 normalization times the Gaussian integral of the signed two-root
slice.  Combines the fixed-parameter second incidence transfer (whose
integrability hypothesis is now discharged) with Fubini. -/
theorem ch28gf_oneRootMoment_eq_factor_mul_integral_slice (m : ℕ) :
    ginibreSignedOneRootMoment (m + 1) =
      ginibreCorollary31Factor (m + 1) *
        ∫ x : ℝ, ginibreSignedTwoRootSlice m x ∂gaussianReal 0 1 := by
  letI : IsFiniteMeasure (realGinibreMeasure (m + 1)) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  have hstep : ∀ x : ℝ,
      (∫ A : RSqMat (m + 1),
        (A - x • (1 : RSqMat (m + 1))).det *
          ginibreAlternatingCount (realEigenvalueBelowCount (A, x))
        ∂realGinibreMeasure (m + 1)) =
        ginibreCorollary31Factor (m + 1) * ginibreSignedTwoRootSlice m x :=
    fun x => integral_realGinibre_det_mul_alternatingBelow_eq_factor_mul_slice
      m x (ch28gf_integrable_det_shift_matrix (m + 1) x)
  calc
    ginibreSignedOneRootMoment (m + 1)
        = ∫ p : RSqMat (m + 1) × ℝ,
            (p.1 - p.2 • (1 : RSqMat (m + 1))).det *
              ginibreAlternatingCount (realEigenvalueBelowCount p)
            ∂(realGinibreMeasure (m + 1)).prod (gaussianReal 0 1) := rfl
    _ = ∫ x : ℝ, ∫ A : RSqMat (m + 1),
          (A - x • (1 : RSqMat (m + 1))).det *
            ginibreAlternatingCount (realEigenvalueBelowCount (A, x))
          ∂realGinibreMeasure (m + 1) ∂gaussianReal 0 1 :=
        integral_prod_symm _ (ch28gf_integrable_oneRootIntegrand (m + 1))
    _ = ∫ x : ℝ,
          ginibreCorollary31Factor (m + 1) * ginibreSignedTwoRootSlice m x
          ∂gaussianReal 0 1 := by
          apply integral_congr_ae
          filter_upwards with x
          exact hstep x
    _ = ginibreCorollary31Factor (m + 1) *
          ∫ x : ℝ, ginibreSignedTwoRootSlice m x ∂gaussianReal 0 1 :=
        integral_const_mul _ _

/-! ## Second assembly: the integrated slice as the kernel moment -/

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

/-- Joint integrability of the signed two-root slice integrand, at a fixed
external spectral value `x`. -/
theorem ch28gf_integrable_sliceIntegrand (m : ℕ) (x : ℝ) :
    Integrable
      (fun p : RSqMat m × ℝ =>
        if p.2 < x then
          (p.2 - x) * (p.1 - p.2 • (1 : RSqMat m)).det *
            (p.1 - x • (1 : RSqMat m)).det
        else 0)
      ((realGinibreMeasure m).prod (gaussianReal 0 1)) := by
  have hD1 : Integrable
      (fun p : RSqMat m × ℝ =>
        (|p.2| + |x|) / 2 * (p.1 - p.2 • (1 : RSqMat m)).det ^ 2)
      ((realGinibreMeasure m).prod (gaussianReal 0 1)) :=
    ch28gf_integrable_wgt_detSq m (fun u => (|u| + |x|) / 2) (by fun_prop)
      (fun u => by positivity) (ch28gf_integrable_hw m x)
  have hD2 : Integrable
      (fun p : RSqMat m × ℝ =>
        (p.1 - x • (1 : RSqMat m)).det ^ 2 * ((|p.2| + |x|) / 2))
      ((realGinibreMeasure m).prod (gaussianReal 0 1)) :=
    (ch28gf_integrable_detSq_matrix m x).mul_prod (ch28gf_integrable_absWgt x)
  have hmeas : Measurable
      (fun p : RSqMat m × ℝ =>
        if p.2 < x then
          (p.2 - x) * (p.1 - p.2 • (1 : RSqMat m)).det *
            (p.1 - x • (1 : RSqMat m)).det
        else 0) := by
    apply Measurable.ite (measurableSet_lt measurable_snd measurable_const)
    · exact ((measurable_snd.sub measurable_const).mul
        (ch28gf_measurable_det_shift m)).mul
          ((ch28gf_measurable_det_shift_matrix m x).comp measurable_fst)
    · exact measurable_const
  apply (hD1.add hD2).mono' hmeas.aestronglyMeasurable
  filter_upwards with p
  simp only [Pi.add_apply]
  by_cases hux : p.2 < x
  · rw [if_pos hux, Real.norm_eq_abs, abs_mul, abs_mul,
      ← sq_abs (p.1 - p.2 • (1 : RSqMat m)).det,
      ← sq_abs (p.1 - x • (1 : RSqMat m)).det]
    have h1 : |p.2 - x| ≤ |p.2| + |x| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le p.2 x
    have hab : |(p.1 - p.2 • (1 : RSqMat m)).det| *
        |(p.1 - x • (1 : RSqMat m)).det| ≤
        (|(p.1 - p.2 • (1 : RSqMat m)).det| ^ 2 +
          |(p.1 - x • (1 : RSqMat m)).det| ^ 2) / 2 := by
      nlinarith [sq_nonneg (|(p.1 - p.2 • (1 : RSqMat m)).det| -
        |(p.1 - x • (1 : RSqMat m)).det|)]
    have hw0 : (0 : ℝ) ≤ |p.2| + |x| := by positivity
    have habpos : (0 : ℝ) ≤ |(p.1 - p.2 • (1 : RSqMat m)).det| *
        |(p.1 - x • (1 : RSqMat m)).det| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      |p.2 - x| * |(p.1 - p.2 • (1 : RSqMat m)).det| *
          |(p.1 - x • (1 : RSqMat m)).det|
          = |p.2 - x| * (|(p.1 - p.2 • (1 : RSqMat m)).det| *
              |(p.1 - x • (1 : RSqMat m)).det|) := by ring
      _ ≤ (|p.2| + |x|) * (|(p.1 - p.2 • (1 : RSqMat m)).det| *
              |(p.1 - x • (1 : RSqMat m)).det|) :=
          mul_le_mul_of_nonneg_right h1 habpos
      _ ≤ (|p.2| + |x|) * ((|(p.1 - p.2 • (1 : RSqMat m)).det| ^ 2 +
              |(p.1 - x • (1 : RSqMat m)).det| ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hab hw0
      _ = (|p.2| + |x|) / 2 * |(p.1 - p.2 • (1 : RSqMat m)).det| ^ 2 +
            |(p.1 - x • (1 : RSqMat m)).det| ^ 2 * ((|p.2| + |x|) / 2) := by ring
  · rw [if_neg hux, norm_zero]
    have h1 : (0 : ℝ) ≤ (|p.2| + |x|) / 2 * (p.1 - p.2 • (1 : RSqMat m)).det ^ 2 := by
      positivity
    have h2 : (0 : ℝ) ≤ (p.1 - x • (1 : RSqMat m)).det ^ 2 * ((|p.2| + |x|) / 2) := by
      positivity
    linarith

/-- The matrix characteristic-product integral equals the kernel evaluated at
the product of the two spectral parameters, in incidence orientation. -/
theorem ch28gf_integral_detShift_prod_eq_kernel (m : ℕ) (u x : ℝ) :
    (∫ B : RSqMat m,
        (B - u • (1 : RSqMat m)).det * (B - x • (1 : RSqMat m)).det
      ∂realGinibreMeasure m) = ginibreCharacteristicProductKernel m (u * x) := by
  rw [integral_realGinibre_det_sub_smul_one_mul_det_sub_smul_one,
    ginibreCharacteristicProductKernel]

/-- The signed two-root slice at external value `x`, after integrating out the
matrix with the characteristic-product moment. -/
theorem ch28gf_slice_eq (m : ℕ) (x : ℝ) :
    ginibreSignedTwoRootSlice m x =
      ∫ u : ℝ,
        (if u < x then (u - x) * ginibreCharacteristicProductKernel m (u * x)
          else 0)
        ∂gaussianReal 0 1 := by
  letI : IsFiniteMeasure (realGinibreMeasure m) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  rw [ginibreSignedTwoRootSlice,
    integral_prod_symm _ (ch28gf_integrable_sliceIntegrand m x)]
  apply integral_congr_ae
  filter_upwards with u
  by_cases huc : u < x
  · rw [if_pos huc]
    calc
      (∫ B : RSqMat m,
          (if u < x then
            (u - x) * (B - u • (1 : RSqMat m)).det *
              (B - x • (1 : RSqMat m)).det
          else 0) ∂realGinibreMeasure m)
          = ∫ B : RSqMat m,
              (u - x) * ((B - u • (1 : RSqMat m)).det *
                (B - x • (1 : RSqMat m)).det) ∂realGinibreMeasure m := by
            apply integral_congr_ae
            filter_upwards with B
            rw [if_pos huc]
            ring
      _ = (u - x) * ∫ B : RSqMat m,
            (B - u • (1 : RSqMat m)).det * (B - x • (1 : RSqMat m)).det
            ∂realGinibreMeasure m := integral_const_mul _ _
      _ = (u - x) * ginibreCharacteristicProductKernel m (u * x) := by
            rw [ch28gf_integral_detShift_prod_eq_kernel]
  · rw [if_neg huc]
    rw [show (fun B : RSqMat m =>
        (if u < x then
          (u - x) * (B - u • (1 : RSqMat m)).det *
            (B - x • (1 : RSqMat m)).det
        else 0)) = fun _ => (0 : ℝ) from by
      funext B; exact if_neg huc]
    rw [integral_zero]

/-- **Second assembly.** The Gaussian integral of the signed two-root slice is
the ordered characteristic-product kernel moment. -/
theorem ch28gf_integral_slice_eq_kernelMoment (m : ℕ) :
    (∫ x : ℝ, ginibreSignedTwoRootSlice m x ∂gaussianReal 0 1) =
      ginibreOrderedGaussianKernelMoment m := by
  have hGeq : ∀ q : ℝ × ℝ,
      (if q.1 < q.2 then
        (q.1 - q.2) * ginibreCharacteristicProductKernel m (q.1 * q.2) else 0) =
        ginibreOrderedGaussianRegion.indicator
          (ginibreOrderedGaussianKernelIntegrand m) q := by
    intro q
    simp only [ginibreOrderedGaussianKernelIntegrand, ginibreOrderedGaussianRegion,
      Set.indicator_apply, Set.mem_setOf_eq]
  have hH : Integrable
      (fun q : ℝ × ℝ =>
        if q.1 < q.2 then
          (q.1 - q.2) * ginibreCharacteristicProductKernel m (q.1 * q.2) else 0)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    apply ((integrable_ginibreOrderedGaussianKernelIntegrand m).indicator
      measurableSet_ginibreOrderedGaussianRegion).congr
    filter_upwards with q
    exact (hGeq q).symm
  calc
    (∫ x : ℝ, ginibreSignedTwoRootSlice m x ∂gaussianReal 0 1)
        = ∫ x : ℝ, ∫ u : ℝ,
            (if u < x then
              (u - x) * ginibreCharacteristicProductKernel m (u * x) else 0)
            ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
          apply integral_congr_ae
          filter_upwards with x
          exact ch28gf_slice_eq m x
    _ = ∫ q : ℝ × ℝ,
          (if q.1 < q.2 then
            (q.1 - q.2) * ginibreCharacteristicProductKernel m (q.1 * q.2)
            else 0)
          ∂(gaussianReal 0 1).prod (gaussianReal 0 1) :=
        (integral_prod_symm _ hH).symm
    _ = ∫ q : ℝ × ℝ in ginibreOrderedGaussianRegion,
          ginibreOrderedGaussianKernelIntegrand m q
          ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
          rw [← integral_indicator measurableSet_ginibreOrderedGaussianRegion]
          apply integral_congr_ae
          filter_upwards with q
          exact hGeq q
    _ = ginibreOrderedGaussianKernelMoment m := rfl

/-! ## The second incidence transfer and the finite expectation formula -/

/-- **The integrated second incidence transfer.**  The signed one-root moment
in dimension `m+1` equals the Corollary-3.1 normalization times the ordered
characteristic-product kernel moment in dimension `m`.  This is the identity
whose absence was the sole gate-blocker of Chapter 28. -/
theorem ch28gf_oneRootMoment_eq_factor_mul_kernelMoment (m : ℕ) :
    ginibreSignedOneRootMoment (m + 1) =
      ginibreCorollary31Factor (m + 1) * ginibreOrderedGaussianKernelMoment m := by
  rw [ch28gf_oneRootMoment_eq_factor_mul_integral_slice m,
    ch28gf_integral_slice_eq_kernelMoment m]

/-- The kernel-transfer hypothesis of `signedPairShift_of_kernelTransfer`,
now proved unconditionally. -/
theorem ch28gf_kernelTransfer :
    ∀ n : ℕ, 2 ≤ n →
      expectedGinibreAlternatingPairCount n =
        ginibreCorollary31Factor n * ginibreCorollary31Factor (n - 1) *
          ginibreOrderedGaussianKernelMoment (n - 2) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [expectedGinibreAlternatingPairCount_succ_eq_factor_mul_oneRootMoment,
    ch28gf_oneRootMoment_eq_factor_mul_kernelMoment]
  have h1 : j + 1 + 1 - 1 = j + 1 := by omega
  have h2 : j + 1 + 1 - 2 = j := by omega
  rw [h1, h2]
  ring

/-- **Row 28-P3, closed.**  The finite Edelman--Kostlan--Shub real-Ginibre
expected-real-eigenvalue formula holds in every positive dimension,
unconditionally. -/
theorem ch28gf_realGinibreFiniteExpectationFormula :
    RealGinibreFiniteExpectationFormula :=
  realGinibreFiniteExpectationFormula_of_signedPairShift
    (signedPairShift_of_kernelTransfer ch28gf_kernelTransfer)

/-- Explicit unfolded form: the matrix integral of the real-eigenvalue count
equals the closed form in every positive dimension. -/
theorem ch28gf_expectedRealEigenvalueCount_eq_closedForm (n : ℕ) (hn : 0 < n) :
    expectedRealEigenvalueCount n = realGinibreExpectedCountClosedForm n :=
  ch28gf_realGinibreFiniteExpectationFormula n hn

/-- **Higham, 2nd ed., p. 517.**  The premise-free real-Ginibre limit
`E_n / √n → √(2/π)`. -/
theorem ch28gf_realGinibreExpectedCountLimit :
    RealGinibreExpectedCountLimit :=
  realGinibreExpectedCountLimit_of_finiteExpectationFormula
    ch28gf_realGinibreFiniteExpectationFormula

/-- **Higham, 2nd ed., p. 517.**  The printed consequence that the expected
proportion of real eigenvalues tends to zero. -/
theorem ch28gf_realGinibreExpectedProportionLimit :
    Tendsto (fun n : ℕ => expectedRealEigenvalueCount n / (n : ℝ))
      atTop (nhds 0) := by
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hmain :
      Tendsto
        (fun n : ℕ => expectedRealEigenvalueCount n / Real.sqrt n)
        atTop (nhds (Real.sqrt (2 / Real.pi))) :=
    ch28gf_realGinibreExpectedCountLimit
  have hproduct := hmain.mul hinv
  convert hproduct using 1
  · funext n
    by_cases hn : n = 0
    · subst n
      simp
    · have hnpos : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hnroot : (n : ℝ) = Real.sqrt n * Real.sqrt n :=
        (Real.mul_self_sqrt hnpos.le).symm
      calc
        expectedRealEigenvalueCount n / (n : ℝ) =
            expectedRealEigenvalueCount n / (Real.sqrt n * Real.sqrt n) :=
          congrArg (fun d : ℝ => expectedRealEigenvalueCount n / d) hnroot
        _ = (expectedRealEigenvalueCount n / Real.sqrt n) *
            (Real.sqrt n)⁻¹ := by
          simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
  · simp

end

end NumStability
