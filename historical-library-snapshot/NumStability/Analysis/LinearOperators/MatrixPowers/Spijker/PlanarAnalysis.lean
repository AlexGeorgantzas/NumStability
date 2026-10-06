import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarAlgebra
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ProjectionIntegral

/-!
# Analysis.LinearOperators.MatrixPowers.Spijker.PlanarAnalysis

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

/-
# The analytic closure of Spijker's planar projection argument

This file proves the two real-analysis facts isolated by
`SpijkerPlanarAnalyticBridge`:

* the projection-average identity, by Fubini and the scalar integral
  `integral |Re (exp (-i theta) w)| = 4 * norm w`;
* the one-dimensional Banach-indicatrix estimate, by a finite layer-cake
  argument on every partition, followed by the standard bounded-variation
  control of the integral of the derivative.

Consequently the sharp rational arc-length estimate, and hence the exact
`SpijkerArcLengthBound` needed by the Kreiss proof, are unconditional.
-/






namespace NumStability

open scoped Real Topology ComplexConjugate ENNReal
open Complex Polynomial Set MeasureTheory

noncomputable section

/-! ## Projection average -/

lemma hasDerivAt_spijkerProjectedCurve
    {gamma : Real -> Complex} {t theta : Real} (hgamma : DifferentiableAt Real gamma t) :
    HasDerivAt (spijkerProjectedCurve gamma theta)
      (spijkerRealProjection (spijkerProjectionDirection theta) (deriv gamma t)) t := by
  have hmul : HasDerivAt
      (fun s : Real => spijkerProjectionDirection theta * gamma s)
      (spijkerProjectionDirection theta * deriv gamma t) t := by
    exact hgamma.hasDerivAt.const_mul (spijkerProjectionDirection theta)
  have hre := Complex.reCLM.hasFDerivAt.comp t hmul.hasFDerivAt
  simpa [spijkerProjectedCurve, spijkerRealProjection] using hre.hasDerivAt

lemma deriv_spijkerProjectedCurve
    {gamma : Real -> Complex} {t theta : Real} (hgamma : DifferentiableAt Real gamma t) :
    deriv (spijkerProjectedCurve gamma theta) t =
      spijkerRealProjection (spijkerProjectionDirection theta) (deriv gamma t) :=
  (hasDerivAt_spijkerProjectedCurve hgamma).deriv

def spijkerProjectionIntegrand (gamma : Real -> Complex) (theta t : Real) : Real :=
  |spijkerRealProjection (spijkerProjectionDirection theta) (deriv gamma t)|

lemma continuous_spijkerProjectionDirection :
    Continuous spijkerProjectionDirection := by
  unfold spijkerProjectionDirection circleMap
  fun_prop

lemma continuous_uncurry_spijkerProjectionIntegrand
    {gamma : Real -> Complex} (hgamma : ContDiff Real 1 gamma) :
    Continuous (Function.uncurry (spijkerProjectionIntegrand gamma)) := by
  have hdir : Continuous
      (fun p : Real × Real => spijkerProjectionDirection p.1) :=
    continuous_spijkerProjectionDirection.comp continuous_fst
  have hderiv : Continuous (fun p : Real × Real => deriv gamma p.2) :=
    hgamma.continuous_deriv_one.comp continuous_snd
  have hmul : Continuous
      (fun p : Real × Real => spijkerProjectionDirection p.1 * deriv gamma p.2) :=
    hdir.mul hderiv
  have hre : Continuous
      (fun p : Real × Real =>
        (spijkerProjectionDirection p.1 * deriv gamma p.2).re) := by
    simpa [Function.comp_def] using Complex.reCLM.continuous.comp hmul
  simpa [spijkerProjectionIntegrand, spijkerRealProjection,
    Function.uncurry] using hre.abs

lemma integrable_spijkerProjectionIntegrand_prod
    {gamma : Real -> Complex} (hgamma : ContDiff Real 1 gamma) :
    Integrable (Function.uncurry (spijkerProjectionIntegrand gamma))
      ((volume.restrict (Set.Ioc (0 : Real) (2 * Real.pi))).prod
        (volume.restrict (Set.Ioc (0 : Real) (2 * Real.pi)))) := by
  have hcont := continuous_uncurry_spijkerProjectionIntegrand hgamma
  have hcompact : IsCompact
      (Set.Icc (0 : Real) (2 * Real.pi) ×ˢ
        Set.Icc (0 : Real) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hIcc : IntegrableOn
      (Function.uncurry (spijkerProjectionIntegrand gamma))
      (Set.Icc (0 : Real) (2 * Real.pi) ×ˢ
        Set.Icc (0 : Real) (2 * Real.pi)) (volume.prod volume) :=
    hcont.continuousOn.integrableOn_compact hcompact
  have hIoc : IntegrableOn
      (Function.uncurry (spijkerProjectionIntegrand gamma))
      (Set.Ioc (0 : Real) (2 * Real.pi) ×ˢ
        Set.Ioc (0 : Real) (2 * Real.pi)) (volume.prod volume) :=
    hIcc.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simpa only [IntegrableOn, ← Measure.prod_restrict] using hIoc

lemma spijkerProjectedVariation_eq_setIntegral
    {gamma : Real -> Complex} (hgamma : ContDiff Real 1 gamma) (theta : Real) :
    spijkerProjectedVariation gamma theta =
      integral (volume.restrict (Set.Ioc (0 : Real) (2 * Real.pi)))
        (fun t => spijkerProjectionIntegrand gamma theta t) := by
  rw [spijkerProjectedVariation,
    intervalIntegral.integral_of_le (by positivity : (0 : Real) <= 2 * Real.pi)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _ht
  change |deriv (spijkerProjectedCurve gamma theta) t| =
    spijkerProjectionIntegrand gamma theta t
  rw [deriv_spijkerProjectedCurve (hgamma.differentiable (by norm_num) t)]
  rfl

lemma spijkerProjectedVariation_intervalIntegrable
    {gamma : Real -> Complex} (hgamma : ContDiff Real 1 gamma) :
    IntervalIntegrable (spijkerProjectedVariation gamma) volume
      0 (2 * Real.pi) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by positivity : (0 : Real) <= 2 * Real.pi)]
  have houter := (integrable_spijkerProjectionIntegrand_prod hgamma).integral_prod_left
  rw [IntegrableOn]
  apply houter.congr
  exact Filter.Eventually.of_forall fun theta => by
    rw [spijkerProjectedVariation_eq_setIntegral hgamma]
    rfl

lemma spijkerProjectionIntegrand_integral_swap
    {gamma : Real -> Complex} (hgamma : ContDiff Real 1 gamma) :
    (integral (volume.restrict (Set.Ioc (0 : Real) (2 * Real.pi)))
      (spijkerProjectedVariation gamma)) =
      integral (volume.restrict (Set.Ioc (0 : Real) (2 * Real.pi)))
        (fun t => integral (volume.restrict (Set.Ioc (0 : Real) (2 * Real.pi)))
          (fun theta => spijkerProjectionIntegrand gamma theta t)) := by
  have hswap := MeasureTheory.integral_integral_swap
    (integrable_spijkerProjectionIntegrand_prod hgamma)
  have hvariation : spijkerProjectedVariation gamma =
      fun theta => integral (volume.restrict (Set.Ioc (0 : Real) (2 * Real.pi)))
        (fun t => spijkerProjectionIntegrand gamma theta t) := by
    funext theta
    exact spijkerProjectedVariation_eq_setIntegral hgamma theta
  rw [hvariation]
  exact hswap

lemma intervalIntegral_spijkerProjectionIntegrand (gamma : Real -> Complex) (t : Real) :
    (integral (volume.restrict (Set.Ioc (0 : Real) (2 * Real.pi)))
      (fun theta => spijkerProjectionIntegrand gamma theta t)) =
      4 * norm (deriv gamma t) := by
  rw [← intervalIntegral.integral_of_le
    (by positivity : (0 : Real) <= 2 * Real.pi)]
  simpa [spijkerProjectionIntegrand, spijkerRealProjection,
    spijkerProjectionDirection, circleMap] using
    intervalIntegral_abs_re_exp_neg_mul_I_mul (deriv gamma t)

theorem spijker_projection_average
    (gamma : Real -> Complex) (hgamma : ContDiff Real 1 gamma) :
    IntervalIntegrable (spijkerProjectedVariation gamma) volume
        0 (2 * Real.pi) ∧
      (integral (volume.restrict (Set.Ioc (0 : Real) (2 * Real.pi)))
        (fun t => norm (deriv gamma t))) =
        (1 / 4 : Real) *
          integral (volume.restrict (Set.Ioc (0 : Real) (2 * Real.pi)))
            (spijkerProjectedVariation gamma) := by
  refine ⟨spijkerProjectedVariation_intervalIntegrable hgamma, ?_⟩
  rw [spijkerProjectionIntegrand_integral_swap hgamma]
  simp_rw [intervalIntegral_spijkerProjectionIntegrand gamma]
  rw [integral_const_mul]
  ring

/-! ## The finite layer-cake estimate -/

























































































































































































































































































































































































































theorem spijker_projection_average_interval
    (gamma : Real → Complex) (hgamma : ContDiff Real 1 gamma) :
    IntervalIntegrable (spijkerProjectedVariation gamma) volume
        0 (2 * Real.pi) ∧
      (∫ t : Real in 0..2 * Real.pi, ‖deriv gamma t‖) =
        (1 / 4 : Real) *
          ∫ theta : Real in 0..2 * Real.pi,
            spijkerProjectedVariation gamma theta := by
  simpa only [intervalIntegral.integral_of_le Real.two_pi_pos.le] using
    spijker_projection_average gamma hgamma






















/-! ## Resolvent specialization -/























end
end NumStability
