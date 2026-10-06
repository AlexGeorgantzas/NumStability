import NumStability.Analysis.Conditioning.InversePerturbation

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal

/-! ## Ambient-radius normalization for Higham Theorem 6.4

The earlier `MixedInverseRelativeAmplificationRadiusSet` normalizes each
perturbation by its own relative size `d / a`.  Higham's printed definition
instead divides every perturbation inside the radius by the ambient relative
radius `rho`.  The declarations below model that literal normalization. -/

/-- Higham Theorem 6.4's literal ambient-radius feasible set.  Every admissible
perturbation satisfies `0 < d <= rho * a`, while its relative inverse change is
divided by the common ambient radius `rho`, not by `d / a`. -/
def MixedInverseAmbientRelativeAmplificationRadiusSet
    {n : ℕ} (να νβ : CVec n → ℝ) (A S : ComplexVectorMap n n)
    (a s rho : ℝ) : Set ℝ :=
  {q | ∃ D B : ComplexVectorMap n n, ∃ d e : ℝ,
    IsComplexVectorMapLinear D ∧
      0 < d ∧ d ≤ rho * a ∧ s * d < 1 ∧
        IsMixedSubordinateNormValue να νβ D d ∧
          (∀ x : CVec n, complexVectorMapAdd A D (B x) = x) ∧
            IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e ∧
              q = (e / s) / rho}

noncomputable def mixedInverseAmbientRelativeAmplificationRadiusSup
    {n : ℕ} (να νβ : CVec n → ℝ) (A S : ComplexVectorMap n n)
    (a s rho : ℝ) : ℝ :=
  sSup (MixedInverseAmbientRelativeAmplificationRadiusSet να νβ A S a s rho)

def IsSupMixedInverseAmbientRelativeAmplificationRadius
    {n : ℕ} (να νβ : CVec n → ℝ) (A S : ComplexVectorMap n n)
    (a s rho Q : ℝ) : Prop :=
  (∀ q : ℝ,
    q ∈ MixedInverseAmbientRelativeAmplificationRadiusSet να νβ A S a s rho →
      q ≤ Q) ∧
    ∀ U : ℝ,
      (∀ q : ℝ,
        q ∈ MixedInverseAmbientRelativeAmplificationRadiusSet
          να νβ A S a s rho → q ≤ U) →
        Q ≤ U

theorem mixedInverseAmbientRelativeAmplificationRadius_mem
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s rho d e : ℝ}
    (hDlin : IsComplexVectorMapLinear D)
    (hdpos : 0 < d) (hdradius : d ≤ rho * a) (hsmall : s * d < 1)
    (hD : IsMixedSubordinateNormValue να νβ D d)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e) :
    (e / s) / rho ∈
      MixedInverseAmbientRelativeAmplificationRadiusSet να νβ A S a s rho := by
  exact ⟨D, B, d, e, hDlin, hdpos, hdradius, hsmall, hD, hB_right, hdiff, rfl⟩

/-- Every ambient-radius value is bounded by the same endpoint resolvent
envelope as the self-normalized set.  The key extra step is
`(e/s)/rho <= (e/s)/(d/a)`, derived from `d/a <= rho`. -/
theorem mixedInverseAmbientRelativeAmplificationRadius_value_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho q : ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hradiusSmall : s * (rho * a) < 1)
    (hS : MixedSubordinateBound νβ να S s)
    (hq : q ∈
      MixedInverseAmbientRelativeAmplificationRadiusSet να νβ A S a s rho) :
    q ≤ a * s * (1 + (rho * a) * (s / (1 - s * (rho * a)))) := by
  obtain ⟨D, B, d, e, hDlin, hdpos, hdradius, hsmall,
    hD, hB_right, hdiff, rfl⟩ := hq
  have hB : MixedSubordinateBound νβ να B (s / (1 - s * d)) :=
    inversePerturbation_perturbedInverse_bound_of_small
      hα hSlin hS_left hB_right (le_of_lt hspos) hsmall hS hD.1
  have hself :
      (e / s) / (d / a) ≤
        a * s * (1 + d * (s / (1 - s * d))) :=
    inversePerturbation_relative_difference_ratio_le
      hα hSlin hDlin hS_left hB_right hapos hspos hdpos
      hS hD.1 hB hdiff
  have he0 : 0 ≤ e :=
    mixedSubordinateNormValue_nonneg_of_nonempty hn hβ hα hdiff
  have hbase0 : 0 ≤ e / s := div_nonneg he0 (le_of_lt hspos)
  have hdrelpos : 0 < d / a := div_pos hdpos hapos
  have hdrelle : d / a ≤ rho := by
    exact (div_le_iff₀ hapos).2 hdradius
  have hamb_self : (e / s) / rho ≤ (e / s) / (d / a) :=
    div_le_div_of_nonneg_left hbase0 hdrelpos hdrelle
  have hmono :
      d * (s / (1 - s * d)) ≤
        (rho * a) * (s / (1 - s * (rho * a))) :=
    resolventScale_mono_of_le_of_small hspos hdradius hsmall hradiusSmall
  have hinner :
      1 + d * (s / (1 - s * d)) ≤
        1 + (rho * a) * (s / (1 - s * (rho * a))) := by
    linarith
  have has0 : 0 ≤ a * s := mul_nonneg (le_of_lt hapos) (le_of_lt hspos)
  exact hamb_self.trans (hself.trans (mul_le_mul_of_nonneg_left hinner has0))

theorem mixedInverseAmbientRelativeAmplificationRadius_sup_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho Q : ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hradiusSmall : s * (rho * a) < 1)
    (hS : MixedSubordinateBound νβ να S s)
    (hQ : IsSupMixedInverseAmbientRelativeAmplificationRadius
      να νβ A S a s rho Q) :
    Q ≤ a * s * (1 + (rho * a) * (s / (1 - s * (rho * a)))) := by
  exact hQ.2 _ (fun q hq =>
    mixedInverseAmbientRelativeAmplificationRadius_value_le
      hn hα hβ hSlin hS_left hapos hspos hradiusSmall hS hq)

/-- A boundary perturbation `d = rho*a` has identical ambient and
self-normalized ratios, so the existing sharp first-order lower estimate
transfers without loss. -/
theorem exists_mixedInverseAmbientRelativeAmplificationRadius_lower_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s rho d b e c : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hboundary : d = rho * a) (hsmall : s * d < 1)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : IsMixedSubordinateNormValue να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d))
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c) :
    ∃ q : ℝ,
      q ∈ MixedInverseAmbientRelativeAmplificationRadiusSet
        να νβ A S a s rho ∧
        a * s * (1 - d * b) ≤ q := by
  have hdradius : d ≤ rho * a := le_of_eq hboundary
  have hrel : d / a = rho := by
    rw [hboundary]
    field_simp [ne_of_gt hapos]
  refine ⟨(e / s) / rho, ?_, ?_⟩
  · exact mixedInverseAmbientRelativeAmplificationRadius_mem
      hDlin hdpos hdradius hsmall hD hB_right hdiff
  · rw [← hrel]
    exact inversePerturbation_relative_difference_ratio_lower_le_of_linearized
      hα hSlin hDlin hS_left hB_right hapos hspos hdpos hS hD.1 hB
      hlin hdiff herr

theorem mixedInverseAmbientRelativeAmplificationRadius_sup_lower_le_of_linearized
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s rho d b e c Q : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hboundary : d = rho * a) (hsmall : s * d < 1)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : IsMixedSubordinateNormValue να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d))
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c)
    (hQ : IsSupMixedInverseAmbientRelativeAmplificationRadius
      να νβ A S a s rho Q) :
    a * s * (1 - d * b) ≤ Q := by
  obtain ⟨q, hq, hlq⟩ :=
    exists_mixedInverseAmbientRelativeAmplificationRadius_lower_bound
      hα hSlin hDlin hS_left hB_right hapos hspos hdpos hboundary
      hsmall hS hD hB hlin hdiff herr
  exact hlq.trans (hQ.1 q hq)

/-- Abstract ambient-radius squeeze.  The chosen sharp perturbation lies on
the radius boundary, so the lower estimate uses the same denominator as the
printed definition. -/
theorem mixedInverseAmbientRelativeAmplificationRadius_sup_tendsto_condition_of_linearized_witnesses
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D Bmap : ι → ComplexVectorMap n n} {a s B0 : ℝ}
    {rho d b e c Q : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hboundary : Filter.Eventually (fun i => d i = rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (Bmap i) (b i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hdiff : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapSub (Bmap i) S) (e i)) l)
    (hrem : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapAdd (complexVectorMapSub (Bmap i) S)
          (complexVectorMapComp S (complexVectorMapComp (D i) S))) (c i)) l)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseAmbientRelativeAmplificationRadius
        να νβ A S a s (rho i) (Q i)) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0))
    (hb_bound : Filter.Eventually (fun i => |b i| ≤ B0) l)
    (hB0 : 0 ≤ B0) :
    Filter.Tendsto Q l (nhds (a * s)) := by
  have hlower : Filter.Eventually
      (fun i => a * s * (1 - d i * b i) ≤ Q i) l := by
    filter_upwards [hDlin, hB_right, hdpos, hboundary, hsmall,
      hD, hB, hlin, hdiff, hrem, hQ] with
      i hDlin_i hB_right_i hdpos_i hboundary_i hsmall_i
      hD_i hB_i hlin_i hdiff_i hrem_i hQ_i
    exact mixedInverseAmbientRelativeAmplificationRadius_sup_lower_le_of_linearized
      hα hSlin hDlin_i hS_left hB_right_i hapos hspos hdpos_i
      hboundary_i hsmall_i hS hD_i hB_i hlin_i hdiff_i hrem_i hQ_i
  have hsmallRadius : Filter.Eventually (fun i => s * (rho i * a) < 1) l :=
    eventually_radius_resolvent_small_of_tendsto_zero hspos hrho
  have hupper : Filter.Eventually
      (fun i => Q i ≤
        a * s * (1 + (rho i * a) * (s / (1 - s * (rho i * a))))) l := by
    filter_upwards [hQ, hsmallRadius] with i hQ_i hsmall_i
    exact mixedInverseAmbientRelativeAmplificationRadius_sup_le
      hn hα hβ hSlin hS_left hapos hspos hsmall_i hS hQ_i
  have hvanish : Filter.Tendsto (fun i => a * s * d i * b i) l (nhds 0) :=
    tendsto_const_mul_of_tendsto_zero_of_eventually_abs_le
      (mul_pos hapos hspos) hB0 hd_tendsto hb_bound
  have hLowerTendsto :
      Filter.Tendsto (fun i => a * s * (1 - d i * b i)) l (nhds (a * s)) := by
    have hneg : Filter.Tendsto (fun i => -(a * s * d i * b i)) l (nhds 0) := by
      simpa using hvanish.neg
    have hadd :
        Filter.Tendsto
          (fun i => a * s + -(a * s * d i * b i)) l
          (nhds (a * s + 0)) :=
      tendsto_const_nhds.add hneg
    simpa [sub_eq_add_neg, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc]
      using hadd
  have hUpperTendsto :
      Filter.Tendsto
        (fun i => a * s * (1 + (rho i * a) * (s / (1 - s * (rho i * a)))))
        l (nhds (a * s)) :=
    mixedInverseRelativeAmplificationRadius_upperEnvelope_tendsto hapos hspos hrho
  exact tendsto_of_eventually_between_tendsto hLowerTendsto hUpperTendsto
    (by
      filter_upwards [hlower, hupper] with i hli hui
      exact ⟨hli, hui⟩)

theorem mixedInverseAmbientRelativeAmplificationRadius_nonempty_of_selfNormalized
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho : ℝ}
    (hne : (MixedInverseRelativeAmplificationRadiusSet
      να νβ A S a s rho).Nonempty) :
    (MixedInverseAmbientRelativeAmplificationRadiusSet
      να νβ A S a s rho).Nonempty := by
  obtain ⟨q, D, B, d, e, hDlin, hdpos, hdradius, hsmall,
    hD, hB_right, hdiff, _hq⟩ := hne
  exact ⟨(e / s) / rho, D, B, d, e, hDlin, hdpos, hdradius,
    hsmall, hD, hB_right, hdiff, rfl⟩

theorem mixedInverseAmbientRelativeAmplificationRadius_bddAbove_of_small
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho : ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hradiusSmall : s * (rho * a) < 1)
    (hS : MixedSubordinateBound νβ να S s) :
    BddAbove (MixedInverseAmbientRelativeAmplificationRadiusSet
      να νβ A S a s rho) := by
  refine ⟨a * s * (1 + (rho * a) * (s / (1 - s * (rho * a)))), ?_⟩
  intro q hq
  exact mixedInverseAmbientRelativeAmplificationRadius_value_le
    hn hα hβ hSlin hS_left hapos hspos hradiusSmall hS hq

theorem isSup_mixedInverseAmbientRelativeAmplificationRadiusSup
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho : ℝ}
    (hne : (MixedInverseAmbientRelativeAmplificationRadiusSet
      να νβ A S a s rho).Nonempty)
    (hbdd : BddAbove (MixedInverseAmbientRelativeAmplificationRadiusSet
      να νβ A S a s rho)) :
    IsSupMixedInverseAmbientRelativeAmplificationRadius να νβ A S a s rho
      (mixedInverseAmbientRelativeAmplificationRadiusSup
        να νβ A S a s rho) := by
  constructor
  · intro q hq
    simpa [mixedInverseAmbientRelativeAmplificationRadiusSup] using
      le_csSup hbdd hq
  · intro U hU
    simpa [mixedInverseAmbientRelativeAmplificationRadiusSup] using
      csSup_le hne hU

/-- Higham Theorem 6.4 with the printed ambient-radius normalization.  Along
any eventually positive relative radius `rho -> 0`, the actual supremum of
`(||B-S||/||S||) / rho` over `||D|| <= rho*||A||` tends to
`||A|| * ||S||`.  The sharp perturbation is chosen on the boundary
`d = rho*a`; perturbed right inverses and both first-order norm witnesses are
constructed internally. -/
theorem mixedInverseAmbientRelativeAmplificationRadiusSup_tendsto_conditionNumberProduct_of_positive_radii
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s : ℝ} {rho : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hAlin : IsComplexVectorMapLinear A)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hS : IsMixedSubordinateNormValue νβ να S s)
    (hrho_pos : Filter.Eventually (fun i => 0 < rho i) l)
    (hrho : Filter.Tendsto rho l (nhds 0)) :
    IsMixedConditionNumberProductValue να νβ A S (a * s) ∧
      Filter.Tendsto
        (fun i => mixedInverseAmbientRelativeAmplificationRadiusSup
          να νβ A S a s (rho i)) l (nhds (a * s)) := by
  classical
  let d : ι → ℝ := fun i => rho i * a
  have hdpos : Filter.Eventually (fun i => 0 < d i) l := by
    filter_upwards [hrho_pos] with i hi
    exact mul_pos hi hapos
  have hboundary : Filter.Eventually (fun i => d i = rho i * a) l :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have hd_tendsto : Filter.Tendsto d l (nhds 0) := by
    simpa [d] using hrho.mul_const a
  have hsmall : Filter.Eventually (fun i => s * d i < 1) l := by
    simpa [d] using
      (eventually_radius_resolvent_small_of_tendsto_zero
        (a := a) hspos hrho)
  obtain ⟨D, hDlin, hD, hlin⟩ :=
    exists_inverseSandwich_scaled_normValue_family_eq_square_mul
      hn hα hβ hSlin hS hspos hdpos
  let b : ι → ℝ := fun i => s / (1 - s * d i)
  let P : ι → ComplexVectorMap n n → Prop := fun i B =>
    IsComplexVectorMapLinear B ∧
      (∀ x : CVec n, complexVectorMapAdd A (D i) (B x) = x) ∧
        MixedSubordinateBound νβ να B (b i)
  have hex : Filter.Eventually (fun i => ∃ B : ComplexVectorMap n n, P i B) l := by
    filter_upwards [hDlin, hsmall, hD] with i hDlin_i hsmall_i hD_i
    simpa [P, b] using
      (exists_inversePerturbation_perturbedRightInverse_of_small
        hα hAlin hSlin hDlin_i hS_left (le_of_lt hspos)
        hsmall_i hS.1 hD_i.1)
  let Bmap : ι → ComplexVectorMap n n := fun i =>
    if h : ∃ B : ComplexVectorMap n n, P i B then Classical.choose h
    else fun _ => 0
  have hBprops : Filter.Eventually (fun i => P i (Bmap i)) l := by
    filter_upwards [hex] with i hi
    have hs := Classical.choose_spec hi
    have heq : Bmap i = Classical.choose hi := by
      dsimp [Bmap]
      rw [dif_pos hi]
    simpa [heq] using hs
  have hBlin : Filter.Eventually
      (fun i => IsComplexVectorMapLinear (Bmap i)) l := by
    filter_upwards [hBprops] with i hi
    exact hi.1
  have hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l := by
    filter_upwards [hBprops] with i hi
    exact hi.2.1
  have hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (Bmap i) (b i)) l := by
    filter_upwards [hBprops] with i hi
    exact hi.2.2
  obtain ⟨e, c, hdiff, hrem⟩ :=
    exists_inversePerturbation_difference_error_normValue_family
      hn hα hβ hSlin hS_left hspos hS.1 hDlin hBlin hB_right hdpos hD hB
  have hb_nonneg : Filter.Eventually (fun i => 0 ≤ b i) l := by
    filter_upwards [hsmall] with i hi
    have hden : 0 < 1 - s * d i := by linarith
    exact div_nonneg (le_of_lt hspos) (le_of_lt hden)
  have hb_bound : Filter.Eventually (fun i => |b i| ≤ 2 * s) l := by
    exact eventually_abs_le_two_mul_of_resolvent_bound_tendsto_zero
      hspos hd_tendsto hb_nonneg (Filter.Eventually.of_forall (fun _ => le_rfl))
  have hOldNonempty : Filter.Eventually
      (fun i => (MixedInverseRelativeAmplificationRadiusSet
        να νβ A S a s (rho i)).Nonempty) l :=
    eventually_mixedInverseRelativeAmplificationRadius_nonempty_of_small_perturbations
      hn hα hβ hAlin hSlin hS_left hspos hS.1 hDlin hdpos
      (by simpa [d] using hboundary.le) hsmall hD
  have hAmbientNonempty : Filter.Eventually
      (fun i => (MixedInverseAmbientRelativeAmplificationRadiusSet
        να νβ A S a s (rho i)).Nonempty) l := by
    filter_upwards [hOldNonempty] with i hi
    exact mixedInverseAmbientRelativeAmplificationRadius_nonempty_of_selfNormalized hi
  have hRadiusSmall : Filter.Eventually (fun i => s * (rho i * a) < 1) l :=
    eventually_radius_resolvent_small_of_tendsto_zero hspos hrho
  have hAmbientBdd : Filter.Eventually
      (fun i => BddAbove (MixedInverseAmbientRelativeAmplificationRadiusSet
        να νβ A S a s (rho i))) l := by
    filter_upwards [hRadiusSmall] with i hi
    exact mixedInverseAmbientRelativeAmplificationRadius_bddAbove_of_small
      hn hα hβ hSlin hS_left hapos hspos hi hS.1
  have hQ : Filter.Eventually
      (fun i => IsSupMixedInverseAmbientRelativeAmplificationRadius
        να νβ A S a s (rho i)
          (mixedInverseAmbientRelativeAmplificationRadiusSup
            να νβ A S a s (rho i))) l := by
    filter_upwards [hAmbientNonempty, hAmbientBdd] with i hne hbdd
    exact isSup_mixedInverseAmbientRelativeAmplificationRadiusSup hne hbdd
  refine ⟨mixedConditionNumberProductValue_norm_mul_inverse_norm hA hS, ?_⟩
  exact mixedInverseAmbientRelativeAmplificationRadius_sup_tendsto_condition_of_linearized_witnesses
    (D := D) (Bmap := Bmap) (d := d) (b := b) (e := e) (c := c)
    (Q := fun i => mixedInverseAmbientRelativeAmplificationRadiusSup
      να νβ A S a s (rho i))
    hn hα hβ hSlin hS_left hapos hspos hS.1 hDlin hB_right hdpos
    hboundary hsmall hD hB hlin hdiff hrem hQ hrho hd_tendsto hb_bound
    (by nlinarith [hspos])

end NumStability
