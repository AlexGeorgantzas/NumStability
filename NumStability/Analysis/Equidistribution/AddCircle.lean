/-
SPDX-License-Identifier: MIT
-/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.UniformOn

noncomputable section

open scoped BigOperators ENNReal NNReal Topology ComplexConjugate
open Filter Set MeasureTheory ProbabilityTheory TopologicalSpace ContinuousMap

namespace NumStability

/-!
# Equidistribution on the additive circle

Finite uniform orbit measures on the unit additive circle, their convergence
to Haar probability for infinite-order rotations, and the resulting frequency
laws for balls and half-open arcs.
-/

instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def finUniformProbability (N : ℕ) : ProbabilityMeasure (Fin (N + 1)) :=
  ⟨uniformOn Set.univ, inferInstance⟩

def empiricalProbability (a : AddCircle (1 : ℝ)) (N : ℕ) :
    ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  (finUniformProbability N).map
    (Measurable.aemeasurable (measurable_of_finite fun i : Fin (N + 1) ↦ i.val • a))

def haarProbability : ProbabilityMeasure (AddCircle (1 : ℝ)) :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

lemma integral_finUniformProbability (N : ℕ) (f : Fin (N + 1) → ℂ) :
    ∫ i, f i ∂(finUniformProbability N : Measure (Fin (N + 1))) =
      ((N + 1 : ℕ) : ℂ)⁻¹ * ∑ i, f i := by
  have hmeasure :
      (finUniformProbability N : Measure (Fin (N + 1))) =
        (((N + 1 : ℕ) : ℝ≥0∞)⁻¹) • Measure.count := by
    ext s hs
    rw [show (finUniformProbability N : Measure (Fin (N + 1))) =
        uniformOn Set.univ by rfl,
      ProbabilityTheory.uniformOn_univ]
    simp [Measure.smul_apply, ENNReal.div_eq_inv_mul]
  rw [hmeasure, integral_smul_measure, integral_count]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  change (((((N + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * ∑ a, f a =
    (((N + 1 : ℕ) : ℂ)⁻¹) * ∑ a, f a
  rw [Complex.ofReal_inv]
  have hcast : ((((N + 1 : ℕ) : ℝ) : ℂ)) = ((N + 1 : ℕ) : ℂ) := by
    norm_cast
  rw [hcast]

lemma integral_empiricalProbability (a : AddCircle (1 : ℝ)) (N : ℕ)
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    ∫ x, f x ∂(empiricalProbability a N : Measure (AddCircle (1 : ℝ))) =
      ((N + 1 : ℕ) : ℂ)⁻¹ * ∑ i : Fin (N + 1), f (i.val • a) := by
  rw [empiricalProbability, ProbabilityMeasure.toMeasure_map,
    integral_map (Measurable.aemeasurable (measurable_of_finite
      fun i : Fin (N + 1) ↦ i.val • a))]
  · exact integral_finUniformProbability N _
  · exact (map_continuous f).aestronglyMeasurable

lemma fourier_nsmul (h : ℤ) (a : AddCircle (1 : ℝ)) (k : ℕ) :
    fourier h (k • a) = fourier h a ^ k := by
  simp only [fourier_apply, smul_comm h k a, AddCircle.toCircle_nsmul,
    Circle.coe_pow]

lemma fourier_ne_one_of_infinite_addOrder
    {a : AddCircle (1 : ℝ)} (ha : addOrderOf a = 0) {h : ℤ} (hh : h ≠ 0) :
    fourier h a ≠ 1 := by
  intro heq
  have hz : h • a = 0 := by
    apply AddCircle.injective_toCircle (by norm_num)
    simpa [fourier_apply] using heq
  have hdvd : (addOrderOf a : ℤ) ∣ h :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
  rw [ha] at hdvd
  exact hh (zero_dvd_iff.mp hdvd)

lemma integral_fourier (h : ℤ) :
    ∫ x : AddCircle (1 : ℝ), fourier h x ∂AddCircle.haarAddCircle =
      if h = 0 then 1 else 0 := by
  split_ifs with hh
  · simp [hh]
  · convert integral_eq_zero_of_add_right_eq_neg
        (μ := AddCircle.haarAddCircle)
        (fourier_add_half_inv_index (T := (1 : ℝ)) hh (by norm_num))

lemma fourier_geom_sum_norm_bounded
    {a : AddCircle (1 : ℝ)} (ha : addOrderOf a = 0) {h : ℤ} (hh : h ≠ 0) :
    IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1), fourier h a ^ k) := by
  let z : ℂ := fourier h a
  have hz : z ≠ 1 := fourier_ne_one_of_infinite_addOrder ha hh
  have hznorm : ‖z‖ = 1 := by
    simp [z, fourier_apply]
  refine Filter.isBoundedUnder_of ⟨2 / ‖z - 1‖, ?_⟩
  intro N
  rw [Function.comp_apply, geom_sum_eq hz, norm_div]
  have hnum : ‖z ^ (N + 1) - 1‖ ≤ 2 := by
    calc
      ‖z ^ (N + 1) - 1‖ ≤ ‖z ^ (N + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hznorm]
  exact div_le_div_of_nonneg_right hnum (norm_nonneg _)

lemma tendsto_fourier_average
    {a : AddCircle (1 : ℝ)} (ha : addOrderOf a = 0) (h : ℤ) :
    Tendsto
      (fun N : ℕ ↦
        ((N + 1 : ℕ) : ℂ)⁻¹ *
          ∑ i : Fin (N + 1), fourier h (i.val • a))
      atTop (𝓝 (if h = 0 then 1 else 0)) := by
  by_cases hh : h = 0
  · subst h
    have heq :
        (fun N : ℕ ↦
          ((N + 1 : ℕ) : ℂ)⁻¹ *
            ∑ i : Fin (N + 1), fourier (T := (1 : ℝ)) 0 (i.val • a)) =
          fun _ ↦ (1 : ℂ) := by
      funext N
      have hne : (((N + 1 : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero N
      simp only [fourier_zero, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ hne
    rw [heq]
    exact tendsto_const_nhds
  have hzero :
      Tendsto
        (fun N : ℕ ↦
          ((N + 1 : ℕ) : ℂ)⁻¹ *
            ∑ k ∈ Finset.range (N + 1), fourier h a ^ k)
        atTop (𝓝 0) := by
    have hinv : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℂ)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))
    have hbounded := fourier_geom_sum_norm_bounded ha hh
    simpa [smul_eq_mul] using
      (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hinv hbounded)
  simp only [hh, if_false]
  simpa only [fourier_nsmul, Fin.sum_univ_eq_sum_range] using hzero

lemma tendsto_integral_empirical_fourier
    {a : AddCircle (1 : ℝ)} (ha : addOrderOf a = 0) (h : ℤ) :
    Tendsto
      (fun N : ℕ ↦ ∫ x, fourier (T := (1 : ℝ)) h x
        ∂(empiricalProbability a N : Measure (AddCircle (1 : ℝ))))
      atTop
      (𝓝 (∫ x, fourier (T := (1 : ℝ)) h x
        ∂(AddCircle.haarAddCircle (T := (1 : ℝ))))) := by
  simp_rw [integral_empiricalProbability]
  rw [integral_fourier]
  exact tendsto_fourier_average ha h

lemma norm_integral_sub_le_norm
    {μ : Measure (AddCircle (1 : ℝ))} [IsProbabilityMeasure μ]
    (f g : C(AddCircle (1 : ℝ), ℂ)) :
    ‖(∫ x, f x ∂μ) - ∫ x, g x ∂μ‖ ≤ ‖f - g‖ := by
  have hfint : Integrable f μ := by
    refine ⟨f.continuous.measurable.aestronglyMeasurable, ?_⟩
    exact HasFiniteIntegral.of_bounded
      (Eventually.of_forall fun x ↦ f.norm_coe_le_norm x)
  have hgint : Integrable g μ := by
    refine ⟨g.continuous.measurable.aestronglyMeasurable, ?_⟩
    exact HasFiniteIntegral.of_bounded
      (Eventually.of_forall fun x ↦ g.norm_coe_le_norm x)
  rw [← integral_sub hfint hgint]
  have h := norm_integral_le_of_norm_le_const
    (μ := μ) (f := fun x ↦ f x - g x) (C := ‖f - g‖)
    (Eventually.of_forall fun x ↦ (f - g).norm_coe_le_norm x)
  simpa using h

lemma tendsto_integral_empirical_span_fourier
    {a : AddCircle (1 : ℝ)} (ha : addOrderOf a = 0)
    (f : C(AddCircle (1 : ℝ), ℂ))
    (hf : f ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ))))) :
    Tendsto
      (fun N : ℕ ↦ ∫ x, f x
        ∂(empiricalProbability a N : Measure (AddCircle (1 : ℝ))))
      atTop (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle)) := by
  refine Submodule.span_induction (p := fun f _ ↦
    Tendsto
      (fun N : ℕ ↦ ∫ x, f x
        ∂(empiricalProbability a N : Measure (AddCircle (1 : ℝ))))
      atTop (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle))) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨h, rfl⟩
    exact tendsto_integral_empirical_fourier ha h
  · simp
  · intro f g _ _ hf hg
    have hfint (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ] :
        Integrable f μ := by
      refine ⟨f.continuous.measurable.aestronglyMeasurable, ?_⟩
      exact HasFiniteIntegral.of_bounded
        (Eventually.of_forall fun x ↦ f.norm_coe_le_norm x)
    have hgint (μ : Measure (AddCircle (1 : ℝ))) [IsProbabilityMeasure μ] :
        Integrable g μ := by
      refine ⟨g.continuous.measurable.aestronglyMeasurable, ?_⟩
      exact HasFiniteIntegral.of_bounded
        (Eventually.of_forall fun x ↦ g.norm_coe_le_norm x)
    have hseq :
        (fun N : ℕ ↦ ∫ x, (f + g) x
          ∂(empiricalProbability a N : Measure (AddCircle (1 : ℝ)))) =
          fun N : ℕ ↦
            (∫ x, f x ∂(empiricalProbability a N : Measure (AddCircle (1 : ℝ)))) +
              ∫ x, g x ∂(empiricalProbability a N : Measure (AddCircle (1 : ℝ))) := by
      funext N
      exact integral_add
        (hfint (empiricalProbability a N : Measure (AddCircle (1 : ℝ))))
        (hgint (empiricalProbability a N : Measure (AddCircle (1 : ℝ))))
    have hlim :
        (∫ x, (f + g) x ∂(AddCircle.haarAddCircle (T := (1 : ℝ)))) =
          (∫ x, f x ∂(AddCircle.haarAddCircle (T := (1 : ℝ)))) +
            ∫ x, g x ∂(AddCircle.haarAddCircle (T := (1 : ℝ))) :=
      integral_add
        (hfint (AddCircle.haarAddCircle (T := (1 : ℝ))))
        (hgint (AddCircle.haarAddCircle (T := (1 : ℝ))))
    rw [hseq, hlim]
    exact hf.add hg
  · intro c f _ hf
    have hseq :
        (fun N : ℕ ↦ ∫ x, (c • f) x
          ∂(empiricalProbability a N : Measure (AddCircle (1 : ℝ)))) =
          fun N : ℕ ↦ c •
            ∫ x, f x ∂(empiricalProbability a N : Measure (AddCircle (1 : ℝ))) := by
      funext N
      simpa [smul_eq_mul] using
        (MeasureTheory.integral_const_mul c (fun x ↦ f x))
    have hlim :
        (∫ x, (c • f) x ∂(AddCircle.haarAddCircle (T := (1 : ℝ)))) =
          c • ∫ x, f x ∂(AddCircle.haarAddCircle (T := (1 : ℝ))) :=
      by simpa [smul_eq_mul] using
        (MeasureTheory.integral_const_mul c (fun x ↦ f x))
    rw [hseq, hlim]
    simpa [smul_eq_mul] using (tendsto_const_nhds (x := c)).mul hf

lemma tendsto_integral_empirical_continuous
    {a : AddCircle (1 : ℝ)} (ha : addOrderOf a = 0)
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto
      (fun N : ℕ ↦ ∫ x, f x
        ∂(empiricalProbability a N : Measure (AddCircle (1 : ℝ))))
      atTop (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle)) := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  have hfmem :
      f ∈ (Submodule.span ℂ
        (Set.range (fourier (T := (1 : ℝ))))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  have hfmem' :
      f ∈ closure (↑(Submodule.span ℂ
        (Set.range (fourier (T := (1 : ℝ))))) : Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hfmem
  have hfmetric := Metric.mem_closure_iff.mp hfmem'
  obtain ⟨g, hgspan, hfg⟩ := hfmetric (ε / 4) (by positivity)
  have hg := tendsto_integral_empirical_span_fourier ha g hgspan
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hg) (ε / 4) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hleft :
      dist
          (∫ x, f x ∂(empiricalProbability a n : Measure (AddCircle (1 : ℝ))))
          (∫ x, g x ∂(empiricalProbability a n : Measure (AddCircle (1 : ℝ)))) <
        ε / 4 := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (norm_integral_sub_le_norm f g) (by simpa [dist_eq_norm] using hfg)
  have hright :
      dist (∫ x, g x ∂AddCircle.haarAddCircle)
          (∫ x, f x ∂AddCircle.haarAddCircle) < ε / 4 := by
    rw [dist_eq_norm]
    have hle := norm_integral_sub_le_norm g f
      (μ := AddCircle.haarAddCircle)
    exact lt_of_le_of_lt hle (by simpa [dist_eq_norm, norm_sub_rev] using hfg)
  calc
    dist
        (∫ x, f x ∂(empiricalProbability a n : Measure (AddCircle (1 : ℝ))))
        (∫ x, f x ∂AddCircle.haarAddCircle) ≤
      dist
          (∫ x, f x ∂(empiricalProbability a n : Measure (AddCircle (1 : ℝ))))
          (∫ x, g x ∂(empiricalProbability a n : Measure (AddCircle (1 : ℝ)))) +
        dist
          (∫ x, g x ∂(empiricalProbability a n : Measure (AddCircle (1 : ℝ))))
          (∫ x, g x ∂AddCircle.haarAddCircle) +
        dist (∫ x, g x ∂AddCircle.haarAddCircle)
          (∫ x, f x ∂AddCircle.haarAddCircle) := by
            exact dist_triangle4 _ _ _ _
    _ < ε / 4 + ε / 4 + ε / 4 :=
      add_lt_add (add_lt_add hleft (hN n hn)) hright
    _ < ε := by linarith

theorem empiricalProbability_tendsto_haar
    {a : AddCircle (1 : ℝ)} (ha : addOrderOf a = 0) :
    Tendsto (empiricalProbability a) atTop (𝓝 haarProbability) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  simpa [haarProbability] using
    tendsto_integral_empirical_continuous ha f.toContinuousMap

lemma haar_eq_volume_unit :
    AddCircle.haarAddCircle (T := (1 : ℝ)) =
      (volume : Measure (AddCircle (1 : ℝ))) := by
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm

lemma volume_sphere_eq_zero (c : AddCircle (1 : ℝ)) (r : ℝ) :
    (volume : Measure (AddCircle (1 : ℝ))) (Metric.sphere c r) = 0 := by
  have hae :
      Metric.closedBall c r \ Metric.ball c r =ᵐ[
        (volume : Measure (AddCircle (1 : ℝ)))]
        (∅ : Set (AddCircle (1 : ℝ))) := by
    filter_upwards [(AddCircle.closedBall_ae_eq_ball (x := c) (ε := r))] with x hx
    apply propext
    constructor
    · rintro ⟨hclosed, hnotBall⟩
      exact (hnotBall (hx.mp hclosed)).elim
    · intro hfalse
      exact hfalse.elim
  rw [← Metric.closedBall_diff_ball, ← ae_eq_empty]
  exact hae

lemma haar_frontier_ball_eq_zero (c : AddCircle (1 : ℝ)) (r : ℝ) :
    AddCircle.haarAddCircle (frontier (Metric.ball c r)) = 0 := by
  rw [haar_eq_volume_unit]
  exact measure_mono_null Metric.frontier_ball_subset_sphere
    (volume_sphere_eq_zero c r)

lemma haar_ball_eq_of_two_mul_le_one
    (c : AddCircle (1 : ℝ)) {r : ℝ} (_hr : 0 ≤ r) (hr1 : 2 * r ≤ 1) :
    AddCircle.haarAddCircle (Metric.ball c r) = ENNReal.ofReal (2 * r) := by
  rw [haar_eq_volume_unit]
  calc
    volume (Metric.ball c r) = volume (Metric.closedBall c r) :=
      measure_congr AddCircle.closedBall_ae_eq_ball.symm
    _ = ENNReal.ofReal (min 1 (2 * r)) :=
      AddCircle.volume_closedBall (T := (1 : ℝ)) r
    _ = ENNReal.ofReal (2 * r) := by rw [min_eq_right hr1]

theorem empiricalProbability_ball_tendsto
    {a : AddCircle (1 : ℝ)} (ha : addOrderOf a = 0)
    (c : AddCircle (1 : ℝ)) {r : ℝ} (hr : 0 ≤ r) (hr1 : 2 * r ≤ 1) :
    Tendsto
      (fun N : ℕ ↦
        (empiricalProbability a N : Measure (AddCircle (1 : ℝ)))
          (Metric.ball c r))
      atTop (𝓝 (ENNReal.ofReal (2 * r))) := by
  have hweak := empiricalProbability_tendsto_haar ha
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hweak (E := Metric.ball c r) (by
      simpa [haarProbability] using haar_frontier_ball_eq_zero c r)
  simpa [haarProbability, haar_ball_eq_of_two_mul_le_one c hr hr1] using hport

lemma empiricalProbability_apply
    (a : AddCircle (1 : ℝ)) (N : ℕ) {E : Set (AddCircle (1 : ℝ))}
    (hE : MeasurableSet E) :
    (empiricalProbability a N : Measure (AddCircle (1 : ℝ))) E =
      (({i : Fin (N + 1) | i.val • a ∈ E}.ncard : ℕ) : ℝ≥0∞) /
        ((N + 1 : ℕ) : ℝ≥0∞) := by
  let f : Fin (N + 1) → AddCircle (1 : ℝ) := fun i ↦ i.val • a
  have hf : AEMeasurable f (finUniformProbability N) :=
    Measurable.aemeasurable (measurable_of_finite f)
  rw [empiricalProbability, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply_of_aemeasurable hf hE]
  rw [show (finUniformProbability N : Measure (Fin (N + 1))) =
      uniformOn Set.univ by rfl,
    ProbabilityTheory.uniformOn_univ]
  let S : Set (Fin (N + 1)) := f ⁻¹' E
  have hS : S.Finite := Set.toFinite S
  rw [show f ⁻¹' E = S by rfl, Measure.count_apply_finite S hS]
  have hcard : hS.toFinset.card = S.ncard :=
    (Set.ncard_eq_toFinset_card S hS).symm
  rw [hcard]
  rw [Fintype.card_fin]
  change
    ((S.ncard : ℕ) : ℝ≥0∞) / ((N + 1 : ℕ) : ℝ≥0∞) =
      (({i : Fin (N + 1) | i.val • a ∈ E}.ncard : ℕ) : ℝ≥0∞) /
        ((N + 1 : ℕ) : ℝ≥0∞)
  have hSe : S = {i : Fin (N + 1) | i.val • a ∈ E} := by
    rfl
  rw [hSe]

theorem orbit_ball_frequency_tendsto
    {a : AddCircle (1 : ℝ)} (ha : addOrderOf a = 0)
    (c : AddCircle (1 : ℝ)) {r : ℝ} (hr : 0 ≤ r) (hr1 : 2 * r ≤ 1) :
    Tendsto
      (fun N : ℕ ↦
        (({i : Fin (N + 1) | i.val • a ∈ Metric.ball c r}.ncard : ℕ) : ℝ≥0∞) /
          ((N + 1 : ℕ) : ℝ≥0∞))
      atTop (𝓝 (ENNReal.ofReal (2 * r))) := by
  simpa [empiricalProbability_apply a _ measurableSet_ball] using
    empiricalProbability_ball_tendsto ha c hr hr1

/-- A short interval on the real line, viewed modulo one, is the corresponding
metric ball on the unit additive circle.  The existential integer is the
choice of real lift of the circle point. -/
lemma mem_centered_ball_coe_iff_exists_int_sub_mem_Ioo
    {lo hi x : ℝ} (hlen : hi - lo ≤ 1) :
    (x : AddCircle (1 : ℝ)) ∈
        Metric.ball (((lo + hi) / 2 : ℝ) : AddCircle (1 : ℝ)) ((hi - lo) / 2) ↔
      ∃ e : ℤ, x - (e : ℝ) ∈ Ioo lo hi := by
  rw [Metric.mem_ball, dist_eq_norm, ← QuotientAddGroup.mk_sub]
  constructor
  · intro hx
    rw [AddCircle.norm_eq] at hx
    refine ⟨round (x - (lo + hi) / 2), ?_⟩
    simp only [inv_one, one_mul, mul_one] at hx
    rw [abs_lt] at hx
    constructor <;> linarith
  · rintro ⟨e, helo, hehi⟩
    have habs :
        |(x - (e : ℝ)) - (lo + hi) / 2| < (hi - lo) / 2 := by
      rw [abs_lt]
      constructor <;> linarith
    have hhalf : |(x - (e : ℝ)) - (lo + hi) / 2| ≤ (1 : ℝ) / 2 := by
      exact (le_of_lt habs).trans (by linarith)
    have hcoe :
        ((x - (lo + hi) / 2 : ℝ) : AddCircle (1 : ℝ)) =
          (((x - (e : ℝ)) - (lo + hi) / 2 : ℝ) : AddCircle (1 : ℝ)) := by
      rw [show x - (lo + hi) / 2 =
          ((x - (e : ℝ)) - (lo + hi) / 2) + (e : ℝ) by ring,
        AddCircle.coe_add]
      simp
    rw [hcoe, (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
      (by simpa using hhalf)]
    exact habs

/-- Equality modulo one, expressed by an integer choice of lift. -/
lemma coe_eq_coe_iff_exists_int_sub_eq
    {x y : ℝ} :
    (x : AddCircle (1 : ℝ)) = (y : AddCircle (1 : ℝ)) ↔
      ∃ e : ℤ, x - (e : ℝ) = y := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    have he' : (e : ℝ) = x - y := by
      simpa [zsmul_eq_mul] using he
    linarith
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    have he' : (e : ℝ) = x - y := by
      linarith
    simpa [zsmul_eq_mul] using he'

/-- The half-open arc corresponding to `[lo, hi)` in a non-wrapping real
lift.  Adding the left endpoint to the open ball makes the convention agree
with the usual leading-digit convention. -/
def halfOpenArc (lo hi : ℝ) : Set (AddCircle (1 : ℝ)) :=
  Metric.ball (((lo + hi) / 2 : ℝ) : AddCircle (1 : ℝ)) ((hi - lo) / 2) ∪
    {((lo : ℝ) : AddCircle (1 : ℝ))}

lemma mem_halfOpenArc_coe_iff_exists_int_sub_mem_Ico
    {lo hi x : ℝ} (hlohi : lo < hi) (hlen : hi - lo ≤ 1) :
    (x : AddCircle (1 : ℝ)) ∈ halfOpenArc lo hi ↔
      ∃ e : ℤ, x - (e : ℝ) ∈ Ico lo hi := by
  rw [halfOpenArc, mem_union, mem_singleton_iff,
    mem_centered_ball_coe_iff_exists_int_sub_mem_Ioo hlen,
    coe_eq_coe_iff_exists_int_sub_eq]
  constructor
  · rintro (⟨e, helo, hehi⟩ | ⟨e, he⟩)
    · exact ⟨e, helo.le, hehi⟩
    · exact ⟨e, he.ge, he ▸ hlohi⟩
  · rintro ⟨e, helo, hehi⟩
    by_cases hstrict : lo < x - (e : ℝ)
    · exact Or.inl ⟨e, hstrict, hehi⟩
    · exact Or.inr ⟨e, le_antisymm (le_of_not_gt hstrict) helo⟩

lemma measurableSet_halfOpenArc (lo hi : ℝ) :
    MeasurableSet (halfOpenArc lo hi) := by
  exact measurableSet_ball.union (measurableSet_singleton _)

lemma haar_singleton_eq_zero (x : AddCircle (1 : ℝ)) :
    AddCircle.haarAddCircle ({x} : Set (AddCircle (1 : ℝ))) = 0 := by
  rw [haar_eq_volume_unit]
  simpa using volume_sphere_eq_zero x 0

lemma haar_frontier_singleton_eq_zero (x : AddCircle (1 : ℝ)) :
    AddCircle.haarAddCircle (frontier ({x} : Set (AddCircle (1 : ℝ)))) = 0 := by
  apply measure_mono_null frontier_subset_closure
  simpa using haar_singleton_eq_zero x

lemma haar_frontier_halfOpenArc_eq_zero (lo hi : ℝ) :
    AddCircle.haarAddCircle (frontier (halfOpenArc lo hi)) = 0 := by
  let c : AddCircle (1 : ℝ) := (((lo + hi) / 2 : ℝ) : AddCircle (1 : ℝ))
  let r : ℝ := (hi - lo) / 2
  have hsub :
      frontier (Metric.ball c r ∪ {((lo : ℝ) : AddCircle (1 : ℝ))}) ⊆
        frontier (Metric.ball c r) ∪
          frontier ({((lo : ℝ) : AddCircle (1 : ℝ))} : Set (AddCircle (1 : ℝ))) := by
    exact (frontier_union_subset _ _).trans
      (union_subset_union inter_subset_left inter_subset_right)
  rw [halfOpenArc]
  exact measure_mono_null hsub
    (measure_union_null (haar_frontier_ball_eq_zero c r)
      (haar_frontier_singleton_eq_zero ((lo : ℝ) : AddCircle (1 : ℝ))))

lemma haar_halfOpenArc_eq_of_two_mul_le_one
    (lo hi : ℝ) (hr : 0 ≤ (hi - lo) / 2) (hr1 : 2 * ((hi - lo) / 2) ≤ 1) :
    AddCircle.haarAddCircle (halfOpenArc lo hi) = ENNReal.ofReal (hi - lo) := by
  have hae :
      halfOpenArc lo hi =ᵐ[AddCircle.haarAddCircle]
        Metric.ball (((lo + hi) / 2 : ℝ) : AddCircle (1 : ℝ)) ((hi - lo) / 2) := by
    unfold halfOpenArc
    exact union_ae_eq_left_of_ae_eq_empty
      (ae_eq_empty.mpr (haar_singleton_eq_zero ((lo : ℝ) : AddCircle (1 : ℝ))))
  calc
    AddCircle.haarAddCircle (halfOpenArc lo hi) =
        AddCircle.haarAddCircle
          (Metric.ball (((lo + hi) / 2 : ℝ) : AddCircle (1 : ℝ)) ((hi - lo) / 2)) :=
      measure_congr hae
    _ = ENNReal.ofReal (2 * ((hi - lo) / 2)) :=
      haar_ball_eq_of_two_mul_le_one _ hr hr1
    _ = ENNReal.ofReal (hi - lo) := by
      congr 1
      ring

theorem empiricalProbability_halfOpenArc_tendsto
    {a : AddCircle (1 : ℝ)} (ha : addOrderOf a = 0)
    (lo hi : ℝ) (hr : 0 ≤ (hi - lo) / 2) (hr1 : 2 * ((hi - lo) / 2) ≤ 1) :
    Tendsto
      (fun N : ℕ ↦
        (empiricalProbability a N : Measure (AddCircle (1 : ℝ)))
          (halfOpenArc lo hi))
      atTop (𝓝 (ENNReal.ofReal (hi - lo))) := by
  have hweak := empiricalProbability_tendsto_haar ha
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hweak (E := halfOpenArc lo hi) (by
      simpa [haarProbability] using haar_frontier_halfOpenArc_eq_zero lo hi)
  simpa [haarProbability, haar_halfOpenArc_eq_of_two_mul_le_one lo hi hr hr1] using hport

theorem orbit_halfOpenArc_frequency_tendsto
    {a : AddCircle (1 : ℝ)} (ha : addOrderOf a = 0)
    (lo hi : ℝ) (hr : 0 ≤ (hi - lo) / 2) (hr1 : 2 * ((hi - lo) / 2) ≤ 1) :
    Tendsto
      (fun N : ℕ ↦
        (({i : Fin (N + 1) | i.val • a ∈ halfOpenArc lo hi}.ncard : ℕ) : ℝ≥0∞) /
          ((N + 1 : ℕ) : ℝ≥0∞))
      atTop (𝓝 (ENNReal.ofReal (hi - lo))) := by
  simpa [empiricalProbability_apply a _ (measurableSet_halfOpenArc lo hi)] using
    empiricalProbability_halfOpenArc_tendsto ha lo hi hr hr1

end NumStability
