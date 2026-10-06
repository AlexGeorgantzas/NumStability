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

import NumStability.Analysis.MatrixPowersSpijkerPlanar
import NumStability.Analysis.SpijkerProjectionIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

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

private def spijkerLevelInterval
    (F : Real -> Real) (u : Nat -> Real) (i : Nat) : Set Real :=
  Set.uIoc (F (u i)) (F (u (i + 1)))

private lemma exists_spijkerPartitionCrossing
    {F : Real -> Real} (hF : Continuous F) {u : Nat -> Real} (hu : Monotone u)
    {i : Nat} {x : Real}
    (hx : x ∈ spijkerLevelInterval F u i)
    (hleft : x ≠ F (u i)) (hright : x ≠ F (u (i + 1))) :
    ∃ t ∈ Set.Ioo (u i) (u (i + 1)), F t = x := by
  have hui : u i ≤ u (i + 1) := hu (Nat.le_succ i)
  have hcont : ContinuousOn F (Set.Icc (u i) (u (i + 1))) := hF.continuousOn
  rcases le_total (F (u i)) (F (u (i + 1))) with hval | hval
  · have hx' : x ∈ Set.Ioo (F (u i)) (F (u (i + 1))) := by
      rw [spijkerLevelInterval, Set.uIoc_of_le hval] at hx
      exact ⟨hx.1, lt_of_le_of_ne hx.2 hright⟩
    simpa only [Set.mem_image] using intermediate_value_Ioo hui hcont hx'
  · have hx' : x ∈ Set.Ioo (F (u (i + 1))) (F (u i)) := by
      rw [spijkerLevelInterval, Set.uIoc_of_ge hval] at hx
      exact ⟨hx.1, lt_of_le_of_ne hx.2 hleft⟩
    simpa only [Set.mem_image] using intermediate_value_Ioo' hui hcont hx'

private def spijkerPartitionEndpointValues
    (F : Real → Real) (u : Nat → Real) (n : Nat) : Finset Real :=
  (Finset.range (n + 1)).image (fun i => F (u i))

private def spijkerActiveIncrements
    (F : Real → Real) (u : Nat → Real) (n : Nat) (x : Real) : Finset Nat :=
  by
    classical
    exact (Finset.range n).filter (fun i => x ∈ spijkerLevelInterval F u i)

private lemma spijkerActiveIncrements_card_le_of_crossing_bound
    {F : Real → Real} (hF : Continuous F) (m n : Nat)
    {u : Nat → Real} (hu : Monotone u)
    (huIcc : ∀ i, u i ∈ Set.Icc (0 : Real) (2 * Real.pi))
    (hcrossing : ∀ x : Real,
      (∃ t ∈ Set.Ico (0 : Real) (2 * Real.pi), F t ≠ x) →
      ∀ s : Finset Real,
        (∀ t ∈ s, t ∈ Set.Ico (0 : Real) (2 * Real.pi)) →
        (∀ t ∈ s, F t = x) →
        s.card ≤ m)
    {x : Real} (hxend : x ∉ spijkerPartitionEndpointValues F u n) :
    (spijkerActiveIncrements F u n x).card ≤ m := by
  classical
  let active := spijkerActiveIncrements F u n x
  have hleft : ∀ i ∈ active, x ≠ F (u i) := by
    intro i hi hxi
    apply hxend
    rw [spijkerPartitionEndpointValues, hxi]
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, rfl⟩
    have hiActive : i ∈ spijkerActiveIncrements F u n x := by
      simpa only [active] using hi
    have hi' : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hiActive).1
    exact Finset.mem_range.mpr (hi'.trans (Nat.lt_succ_self n))
  have hright : ∀ i ∈ active, x ≠ F (u (i + 1)) := by
    intro i hi hxi
    apply hxend
    rw [spijkerPartitionEndpointValues, hxi]
    apply Finset.mem_image.mpr
    refine ⟨i + 1, ?_, rfl⟩
    have hiActive : i ∈ spijkerActiveIncrements F u n x := by
      simpa only [active] using hi
    have hi' : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hiActive).1
    exact Finset.mem_range.mpr (Nat.add_lt_add_right hi' 1)
  have hroot_exists : ∀ i, i ∈ active →
      ∃ t ∈ Set.Ioo (u i) (u (i + 1)), F t = x := by
    intro i hi
    have hiActive : i ∈ spijkerActiveIncrements F u n x := by
      simpa only [active] using hi
    apply exists_spijkerPartitionCrossing hF hu
    · exact (Finset.mem_filter.mp hiActive).2
    · exact hleft i hi
    · exact hright i hi
  let root : Nat → Real := fun i =>
    if hi : i ∈ active then Classical.choose (hroot_exists i hi) else u i
  have hroot_mem : ∀ i ∈ active, root i ∈ Set.Ioo (u i) (u (i + 1)) := by
    intro i hi
    simpa only [root, dif_pos hi] using (Classical.choose_spec (hroot_exists i hi)).1
  have hroot_eq : ∀ i ∈ active, F (root i) = x := by
    intro i hi
    simpa only [root, dif_pos hi] using (Classical.choose_spec (hroot_exists i hi)).2
  have hroot_inj : Set.InjOn root (↑active : Set Nat) := by
    intro i hi j hj hij
    by_contra heq
    rcases lt_or_gt_of_ne heq with hijlt | hjilt
    · have hrij : root i < root j := calc
        root i < u (i + 1) := (hroot_mem i hi).2
        _ ≤ u j := hu (Nat.succ_le_iff.mpr hijlt)
        _ < root j := (hroot_mem j hj).1
      exact hrij.ne hij
    · have hrji : root j < root i := calc
        root j < u (j + 1) := (hroot_mem j hj).2
        _ ≤ u i := hu (Nat.succ_le_iff.mpr hjilt)
        _ < root i := (hroot_mem i hi).1
      exact hrji.ne hij.symm
  let roots : Finset Real := active.image root
  have hcard_roots : roots.card = active.card :=
    Finset.card_image_iff.mpr hroot_inj
  have hrootsI : ∀ t ∈ roots,
      t ∈ Set.Ico (0 : Real) (2 * Real.pi) := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    have hri := hroot_mem i hi
    exact ⟨((huIcc i).1.trans_lt hri.1).le,
      hri.2.trans_le (huIcc (i + 1)).2⟩
  have hrootsLevel : ∀ t ∈ roots, F t = x := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    exact hroot_eq i hi
  rcases active.eq_empty_or_nonempty with hactive | ⟨i, hi⟩
  · change active.card ≤ m
    simp [hactive]
  · have hvary : ∃ t ∈ Set.Ico (0 : Real) (2 * Real.pi), F t ≠ x := by
      refine ⟨u i, ?_, (hleft i hi).symm⟩
      have hri := hroot_mem i hi
      exact ⟨(huIcc i).1, hri.1.trans (hri.2.trans_le (huIcc (i + 1)).2)⟩
    have h := hcrossing x hvary roots hrootsI hrootsLevel
    simpa only [hcard_roots] using h

private def spijkerPartitionLevelMultiplicity
    (F : Real → Real) (u : Nat → Real) (n : Nat) (x : Real) : ENNReal :=
  ∑ i ∈ Finset.range n,
    (spijkerLevelInterval F u i).indicator (fun _ => (1 : ENNReal)) x

private lemma spijkerPartitionLevelMultiplicity_eq_card
    (F : Real → Real) (u : Nat → Real) (n : Nat) (x : Real) :
    spijkerPartitionLevelMultiplicity F u n x =
      ((spijkerActiveIncrements F u n x).card : ENNReal) := by
  classical
  unfold spijkerPartitionLevelMultiplicity spijkerActiveIncrements
  simp only [Set.indicator_apply]
  exact Finset.sum_boole
    (R := ENNReal) (fun i => x ∈ spijkerLevelInterval F u i) (Finset.range n)

private lemma spijkerPartitionLevelMultiplicity_le
    {F : Real → Real} (hF : Continuous F) (m n : Nat) (C : Real)
    {u : Nat → Real} (hu : Monotone u)
    (huIcc : ∀ i, u i ∈ Set.Icc (0 : Real) (2 * Real.pi))
    (hbound : ∀ t ∈ Set.Icc (0 : Real) (2 * Real.pi), |F t| ≤ C)
    (hcrossing : ∀ x : Real,
      (∃ t ∈ Set.Ico (0 : Real) (2 * Real.pi), F t ≠ x) →
      ∀ s : Finset Real,
        (∀ t ∈ s, t ∈ Set.Ico (0 : Real) (2 * Real.pi)) →
        (∀ t ∈ s, F t = x) →
        s.card ≤ m)
    {x : Real} (hxend : x ∉ spijkerPartitionEndpointValues F u n) :
    spijkerPartitionLevelMultiplicity F u n x ≤
      (Set.Icc (-C) C).indicator (fun _ => (m : ENNReal)) x := by
  classical
  rw [spijkerPartitionLevelMultiplicity_eq_card]
  let active := spijkerActiveIncrements F u n x
  rcases active.eq_empty_or_nonempty with hactive | ⟨i, hi⟩
  · simp [active, hactive]
  · have hiActive : i ∈ spijkerActiveIncrements F u n x := by
      simpa only [active] using hi
    have hxlevel : x ∈ spijkerLevelInterval F u i :=
      (Finset.mem_filter.mp hiActive).2
    have hi' : i < n := Finset.mem_range.mp (Finset.mem_filter.mp hiActive).1
    have hai := abs_le.mp (hbound (u i) (huIcc i))
    have hbi := abs_le.mp (hbound (u (i + 1)) (huIcc (i + 1)))
    have hxIoc : x ∈ Set.Ioc (min (F (u i)) (F (u (i + 1))))
        (max (F (u i)) (F (u (i + 1)))) := by
      simpa only [spijkerLevelInterval, Set.uIoc] using hxlevel
    have hxrange : x ∈ Set.Icc (-C) C := by
      constructor
      · exact (le_min hai.1 hbi.1).trans hxIoc.1.le
      · exact hxIoc.2.trans (max_le hai.2 hbi.2)
    rw [Set.indicator_of_mem hxrange]
    exact_mod_cast spijkerActiveIncrements_card_le_of_crossing_bound
      hF m n hu huIcc hcrossing hxend

private lemma measurable_spijkerPartitionLevelMultiplicity
    (F : Real → Real) (u : Nat → Real) (n : Nat) :
    Measurable (spijkerPartitionLevelMultiplicity F u n) := by
  classical
  unfold spijkerPartitionLevelMultiplicity
  apply Finset.measurable_sum
  intro i _hi
  exact measurable_const.indicator measurableSet_uIoc

private lemma lintegral_spijkerPartitionLevelMultiplicity
    (F : Real → Real) (u : Nat → Real) (n : Nat) :
    ∫⁻ x : Real, spijkerPartitionLevelMultiplicity F u n x =
      ∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i)) := by
  classical
  calc
    ∫⁻ x : Real, spijkerPartitionLevelMultiplicity F u n x =
        ∑ i ∈ Finset.range n,
          ∫⁻ x : Real,
            (spijkerLevelInterval F u i).indicator (fun _ => (1 : ENNReal)) x := by
      unfold spijkerPartitionLevelMultiplicity
      rw [lintegral_finset_sum]
      intro i _hi
      exact measurable_const.indicator measurableSet_uIoc
    _ = ∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      change (∫⁻ x : Real,
          (spijkerLevelInterval F u i).indicator (1 : Real → ENNReal) x) =
        edist (F (u (i + 1))) (F (u i))
      rw [spijkerLevelInterval]
      rw [MeasureTheory.lintegral_indicator_one measurableSet_uIoc]
      simp [Real.volume_uIoc, edist_dist, Real.dist_eq]

private lemma spijkerPartition_edist_sum_le
    {F : Real → Real} (hF : Continuous F) (m n : Nat) (C : Real)
    {u : Nat → Real} (hu : Monotone u)
    (huIcc : ∀ i, u i ∈ Set.Icc (0 : Real) (2 * Real.pi))
    (hbound : ∀ t ∈ Set.Icc (0 : Real) (2 * Real.pi), |F t| ≤ C)
    (hcrossing : ∀ x : Real,
      (∃ t ∈ Set.Ico (0 : Real) (2 * Real.pi), F t ≠ x) →
      ∀ s : Finset Real,
        (∀ t ∈ s, t ∈ Set.Ico (0 : Real) (2 * Real.pi)) →
        (∀ t ∈ s, F t = x) →
        s.card ≤ m) :
    (∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i))) ≤
      (m : ENNReal) * ENNReal.ofReal (2 * C) := by
  classical
  rw [← lintegral_spijkerPartitionLevelMultiplicity F u n]
  calc
    (∫⁻ x : Real, spijkerPartitionLevelMultiplicity F u n x) ≤
        ∫⁻ x : Real,
          (Set.Icc (-C) C).indicator (fun _ => (m : ENNReal)) x := by
      apply lintegral_mono_ae
      have hend : ∀ᵐ x : Real, x ∉ spijkerPartitionEndpointValues F u n := by
        simp only [ae_iff, not_not]
        exact Finset.measure_zero (spijkerPartitionEndpointValues F u n) volume
      filter_upwards [hend] with x hx
      exact spijkerPartitionLevelMultiplicity_le
        hF m n C hu huIcc hbound hcrossing hx
    _ = (m : ENNReal) * ENNReal.ofReal (2 * C) := by
      rw [MeasureTheory.lintegral_indicator_const measurableSet_Icc]
      rw [Real.volume_Icc]
      congr 2
      ring

private lemma spijker_eVariationOn_le
    {F : Real → Real} (hF : Continuous F) (m : Nat) (C : Real)
    (hbound : ∀ t ∈ Set.Icc (0 : Real) (2 * Real.pi), |F t| ≤ C)
    (hcrossing : ∀ x : Real,
      (∃ t ∈ Set.Ico (0 : Real) (2 * Real.pi), F t ≠ x) →
      ∀ s : Finset Real,
        (∀ t ∈ s, t ∈ Set.Ico (0 : Real) (2 * Real.pi)) →
        (∀ t ∈ s, F t = x) →
        s.card ≤ m) :
    eVariationOn F (Set.Icc (0 : Real) (2 * Real.pi)) ≤
      (m : ENNReal) * ENNReal.ofReal (2 * C) := by
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, ⟨u, hu, huIcc⟩⟩
  exact spijkerPartition_edist_sum_le hF m n C hu huIcc hbound hcrossing

private lemma integral_abs_deriv_le_eVariationOn
    {F : Real → Real} (hF : ContDiff Real 1 F)
    (hBV : BoundedVariationOn F (Set.Icc (0 : Real) (2 * Real.pi))) :
    (∫ t : Real in 0..2 * Real.pi, |deriv F t|) ≤
      (eVariationOn F (Set.Icc (0 : Real) (2 * Real.pi))).toReal := by
  let T : Real := 2 * Real.pi
  let s : Set Real := Set.Icc (0 : Real) T
  have hT : (0 : Real) ≤ T := Real.two_pi_pos.le
  have hloc : LocallyBoundedVariationOn F s := by
    simpa only [s, T] using hBV.locallyBoundedVariationOn
  let v : Real → Real := variationOnFromTo F s 0
  let p : Real → Real := fun x => v x + F x
  let q : Real → Real := fun x => v x - F x
  have hzero : (0 : Real) ∈ s := by simp [s, hT]
  have hTmem : T ∈ s := by simp [s, hT]
  have hvmono : MonotoneOn v s := by
    simpa only [v] using variationOnFromTo.monotoneOn hloc hzero
  have hqmono : MonotoneOn q s := by
    simpa only [q, v] using variationOnFromTo.sub_self_monotoneOn hloc hzero
  have hpmono : MonotoneOn p s := by
    intro x hx y hy hxy
    have hdist : F x - F y ≤ v y - v x := by
      calc
        F x - F y ≤ |F y - F x| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        _ = dist (F x) (F y) := by rw [Real.dist_eq, abs_sub_comm]
        _ ≤ variationOnFromTo F s x y := by
          rw [variationOnFromTo.eq_of_le F s hxy, dist_edist]
          apply ENNReal.toReal_mono (hloc x y hx hy)
          apply eVariationOn.edist_le F
          · exact ⟨hx, le_rfl, hxy⟩
          · exact ⟨hy, hxy, le_rfl⟩
        _ = v y - v x := by
          dsimp only [v]
          linarith [variationOnFromTo.add hloc hzero hx hy]
    dsimp only [p]
    linarith
  have hpInt : IntervalIntegrable (deriv p) volume 0 T := by
    apply MonotoneOn.intervalIntegrable_deriv
    simpa only [s, uIcc_of_le hT] using hpmono
  have hqInt : IntervalIntegrable (deriv q) volume 0 T := by
    apply MonotoneOn.intervalIntegrable_deriv
    simpa only [s, uIcc_of_le hT] using hqmono
  have hFabsInt : IntervalIntegrable (fun x => |deriv F x|) volume 0 T :=
    hF.continuous_deriv_one.abs.intervalIntegrable _ _
  have hpqInt : IntervalIntegrable
      (fun x => (deriv p x + deriv q x) / 2) volume 0 T := by
    simpa only [div_eq_mul_inv, mul_comm (2 : Real)⁻¹, ← mul_add] using
      (hpInt.add hqInt).const_mul ((2 : Real)⁻¹)
  have hpoint : (fun x => |deriv F x|) ≤ᵐ[volume.restrict s]
      (fun x => (deriv p x + deriv q x) / 2) := by
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    have hne0 : ∀ᵐ x : Real, x ≠ 0 := by simp [ae_iff, measure_singleton]
    have hneT : ∀ᵐ x : Real, x ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [hpmono.ae_differentiableWithinAt_of_mem,
      hqmono.ae_differentiableWithinAt_of_mem, hne0, hneT] with x hpx hqx hx0 hxT
    intro hxs
    have hxpos : 0 < x := lt_of_le_of_ne hxs.1 (Ne.symm hx0)
    have hxlt : x < T := lt_of_le_of_ne hxs.2 hxT
    have hsnhds : s ∈ 𝓝 x := Icc_mem_nhds hxpos hxlt
    have hpxAt : DifferentiableAt Real p x :=
      (hpx hxs).differentiableAt hsnhds
    have hqxAt : DifferentiableAt Real q x :=
      (hqx hxs).differentiableAt hsnhds
    have hpnonneg : 0 ≤ deriv p x := by
      rw [← derivWithin_of_mem_nhds hsnhds]
      exact hpmono.derivWithin_nonneg
    have hqnonneg : 0 ≤ deriv q x := by
      rw [← derivWithin_of_mem_nhds hsnhds]
      exact hqmono.derivWithin_nonneg
    have hid : (fun z => (p z - q z) / 2) = F := by
      funext z
      simp only [p, q]
      ring
    have hderiv : deriv F x = (deriv p x - deriv q x) / 2 := by
      have h := (hpxAt.hasDerivAt.sub hqxAt.hasDerivAt).div_const 2
      have hid' : (fun z => (p - q) z / 2) = F := by
        simpa only [Pi.sub_apply] using hid
      rw [hid'] at h
      exact h.deriv
    rw [hderiv]
    calc
      |(deriv p x - deriv q x) / 2| =
          |deriv p x - deriv q x| / 2 := by norm_num [abs_div]
      _ ≤ (|deriv p x| + |deriv q x|) / 2 := by
        gcongr
        exact abs_sub _ _
      _ = (deriv p x + deriv q x) / 2 := by
        rw [abs_of_nonneg hpnonneg, abs_of_nonneg hqnonneg]
  have hmonoInt :
      (∫ x : Real in 0..T, |deriv F x|) ≤
        ∫ x : Real in 0..T, (deriv p x + deriv q x) / 2 := by
    exact intervalIntegral.integral_mono_ae_restrict hT hFabsInt hpqInt hpoint
  have hpBound : (∫ x : Real in 0..T, deriv p x) ≤ p T - p 0 := by
    have hpmonoU : MonotoneOn p (Set.uIcc 0 T) := by
      simpa only [s, uIcc_of_le hT] using hpmono
    have hp0T : p 0 ≤ p T := hpmono hzero hTmem hT
    have hmem := hpmonoU.intervalIntegral_deriv_mem_uIcc
    rw [uIcc_of_le (sub_nonneg.mpr hp0T)] at hmem
    exact hmem.2
  have hqBound : (∫ x : Real in 0..T, deriv q x) ≤ q T - q 0 := by
    have hqmonoU : MonotoneOn q (Set.uIcc 0 T) := by
      simpa only [s, uIcc_of_le hT] using hqmono
    have hq0T : q 0 ≤ q T := hqmono hzero hTmem hT
    have hmem := hqmonoU.intervalIntegral_deriv_mem_uIcc
    rw [uIcc_of_le (sub_nonneg.mpr hq0T)] at hmem
    exact hmem.2
  have hv0 : v 0 = 0 := by
    exact variationOnFromTo.self F s 0
  have hvT : v T = (eVariationOn F s).toReal := by
    simp only [v]
    rw [variationOnFromTo.eq_of_le F s hT]
    simp only [s, Set.inter_self]
  calc
    (∫ t : Real in 0..2 * Real.pi, |deriv F t|) =
        ∫ t : Real in 0..T, |deriv F t| := by rfl
    _ ≤ ∫ x : Real in 0..T, (deriv p x + deriv q x) / 2 := hmonoInt
    _ = ((∫ x : Real in 0..T, deriv p x) +
          ∫ x : Real in 0..T, deriv q x) / 2 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add hpInt hqInt]
    _ ≤ ((p T - p 0) + (q T - q 0)) / 2 := by gcongr
    _ = (eVariationOn F (Set.Icc (0 : Real) (2 * Real.pi))).toReal := by
      simp only [p, q, hv0, hvT, s, T]
      ring

theorem spijker_crossing_variation
    (F : Real → Real) (m : Nat) (C : Real)
    (hF : ContDiff Real 1 F) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Set.Icc (0 : Real) (2 * Real.pi), |F t| ≤ C)
    (hcrossing : ∀ x : Real,
      (∃ t ∈ Set.Ico (0 : Real) (2 * Real.pi), F t ≠ x) →
      ∀ s : Finset Real,
        (∀ t ∈ s, t ∈ Set.Ico (0 : Real) (2 * Real.pi)) →
        (∀ t ∈ s, F t = x) →
        s.card ≤ m) :
    (∫ t : Real in 0..2 * Real.pi, |deriv F t|) ≤
      2 * (m : Real) * C := by
  have hvar := spijker_eVariationOn_le hF.continuous m C hbound hcrossing
  have hfinite : (m : ENNReal) * ENNReal.ofReal (2 * C) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) ENNReal.ofReal_ne_top
  have hBV : BoundedVariationOn F (Set.Icc (0 : Real) (2 * Real.pi)) := by
    exact ne_top_of_le_ne_top hfinite hvar
  calc
    (∫ t : Real in 0..2 * Real.pi, |deriv F t|) ≤
        (eVariationOn F (Set.Icc (0 : Real) (2 * Real.pi))).toReal :=
      integral_abs_deriv_le_eVariationOn hF hBV
    _ ≤ ((m : ENNReal) * ENNReal.ofReal (2 * C)).toReal :=
      ENNReal.toReal_mono hfinite hvar
    _ = 2 * (m : Real) * C := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * C)]
      ring

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

/-- Both analytic ingredients in Spijker's projection proof, with no
external proposition or target-shaped certificate. -/
def spijkerPlanarAnalyticBridge : SpijkerPlanarAnalyticBridge where
  projection_average := spijker_projection_average_interval
  crossing_variation := spijker_crossing_variation

/-- Sharp Spijker arc-length bound for every rational-order certificate
whose denominator is nonzero on the circle. -/
theorem RationalOrderCertificate.arcLength_le
    {n : Nat} {f : Complex → Complex} (cert : RationalOrderCertificate n f)
    (R C : Real) (hC : 0 ≤ C)
    (gamma : Real → Complex) (hgamma : gamma = fun t => f (circleMap 0 R t))
    (hgammaC1 : ContDiff Real 1 gamma)
    (hden : ∀ t ∈ Set.Ico (0 : Real) (2 * Real.pi),
      cert.denominator.eval (circleMap 0 R t) ≠ 0)
    (hbound : ∀ t ∈ Set.Icc (0 : Real) (2 * Real.pi), ‖gamma t‖ ≤ C) :
    (∫ t : Real in 0..2 * Real.pi, ‖deriv gamma t‖) ≤
      2 * Real.pi * n * C :=
  cert.arcLength_le_of_planar_analyticBridge
    spijkerPlanarAnalyticBridge R C hC gamma hgamma hgammaC1 hden hbound

/-! ## Resolvent specialization -/

/-- The source-honest exterior-circle `SpijkerArcLengthBound` is a theorem,
not an external assumption.  Pole-freeness is supplied by `hK` and recorded
by the rational certificate's denominator theorem. -/
theorem spijkerArcLengthBound_proved (n : ℕ) [Nonempty (Fin n)] :
    SpijkerArcLengthBound n := by
  intro A u v K R C hK hR hC hbound
  have hRpos : 0 < R := zero_lt_one.trans hR
  let cert := spijkerResolventCoefficient_rationalOrderCertificate A u v
  apply cert.arcLength_le R C hC
    (spijkerResolventCoefficientCurve A u v R) rfl
  · rw [contDiff_one_iff_deriv]
    exact ⟨fun theta =>
        spijkerResolventCoefficientCurve_differentiableAt A u v hK hR theta,
      spijkerResolventCoefficientCurve_deriv_continuous A u v hK hR⟩
  · intro t ht
    apply spijkerResolventCoefficient_certificate_denominator_ne_on_exteriorCircle
      A u v hK hR
    simp [norm_circleMap_zero, abs_of_pos hRpos]
  · intro t ht
    apply hbound
    simp [norm_circleMap_zero, abs_of_pos hRpos]

end
end NumStability
