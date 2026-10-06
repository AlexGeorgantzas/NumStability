-- Analysis/VectorNorms/Interpolation.lean
--
-- Interpolation theory for finite complex-vector norms.

import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import NumStability.Analysis.VectorNorms.Basic

/-!
# Complex-vector norm interpolation

Develops finite-dimensional complex interpolation and Riesz--Thorin
infrastructure for the concrete vector `L^p` norms.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Endpoint-aware reciprocal exponent used for finite-dimensional `L^p`
    interpolation.  This is `1 / p` for finite positive `p`, and it gives
    `0` at `p = ∞`. -/
noncomputable def lpRecipExp (p : ℝ≥0∞) : ℝ :=
  (p⁻¹).toReal

@[simp]
lemma lpRecipExp_one : lpRecipExp 1 = 1 := by
  simp [lpRecipExp]

@[simp]
lemma lpRecipExp_top : lpRecipExp ∞ = 0 := by
  simp [lpRecipExp]

lemma lpRecipExp_ofReal {p : ℝ} (hp : 0 < p) :
    lpRecipExp (ENNReal.ofReal p) = p⁻¹ := by
  unfold lpRecipExp
  rw [← ENNReal.ofReal_inv_of_pos hp]
  exact ENNReal.toReal_ofReal (inv_nonneg.mpr (le_of_lt hp))

lemma lpRecipExp_nonneg (p : ℝ≥0∞) : 0 ≤ lpRecipExp p := by
  exact ENNReal.toReal_nonneg

lemma lpRecipExp_le_one {p : ℝ≥0∞} (hp : 1 ≤ p) :
    lpRecipExp p ≤ 1 := by
  have hp_ne_zero : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpinv_ne_top : p⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hp_ne_zero
  have hpinv_le_one : p⁻¹ ≤ (1 : ℝ≥0∞) := by
    simpa using (ENNReal.inv_le_inv.mpr hp)
  simpa [lpRecipExp] using
    (ENNReal.toReal_le_toReal hpinv_ne_top ENNReal.one_ne_top).2 hpinv_le_one

lemma lpRecipExp_eq_zero_iff {p : ℝ≥0∞} (hp : 1 ≤ p) :
    lpRecipExp p = 0 ↔ p = ∞ := by
  constructor
  · intro h
    have hcases : p⁻¹ = 0 ∨ p⁻¹ = ∞ := by
      simpa [lpRecipExp] using (ENNReal.toReal_eq_zero_iff p⁻¹).mp h
    cases hcases with
    | inl hzero =>
        exact ENNReal.inv_eq_zero.mp hzero
    | inr htop =>
        have hp_zero : p = 0 := ENNReal.inv_eq_top.mp htop
        have hnot : ¬ (1 : ℝ≥0∞) ≤ 0 := by norm_num
        have hle_zero : (1 : ℝ≥0∞) ≤ 0 := by
          rw [hp_zero] at hp
          exact hp
        exact False.elim (hnot hle_zero)
  · intro hp_top
    rw [hp_top]
    simp [lpRecipExp]

lemma lpRecipExp_eq_one_iff {p : ℝ≥0∞} :
    lpRecipExp p = 1 ↔ p = 1 := by
  constructor
  · intro h
    have hpinv : p⁻¹ = (1 : ℝ≥0∞) := by
      simpa [lpRecipExp] using (ENNReal.toReal_eq_one_iff p⁻¹).mp h
    have h := congrArg (fun x : ℝ≥0∞ => x⁻¹) hpinv
    simpa using h
  · intro hp
    simp [lpRecipExp, hp]

lemma lpRecipExp_injOn_Ici_one :
    Set.InjOn lpRecipExp (Set.Ici (1 : ℝ≥0∞)) := by
  intro p hp q hq hpq
  have hp_ne_zero : p ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hq_ne_zero : q ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hq)
  have hpinv_ne_top : p⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hp_ne_zero
  have hqinv_ne_top : q⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hq_ne_zero
  have hpinv_eq : p⁻¹ = q⁻¹ := by
    exact (ENNReal.toReal_eq_toReal_iff' hpinv_ne_top hqinv_ne_top).mp hpq
  have h := congrArg (fun x : ℝ≥0∞ => x⁻¹) hpinv_eq
  simpa using h

/-- A source exponent `p : ℝ≥0∞` with `1 ≤ p` is one of the two endpoints
    `1`, `∞`, or a finite real exponent strictly larger than `1`. -/
inductive LpEndpointFiniteExponentCase : ℝ≥0∞ → Prop where
  | one : LpEndpointFiniteExponentCase 1
  | finite {p : ℝ} (hp : 1 < p) :
      LpEndpointFiniteExponentCase (ENNReal.ofReal p)
  | top : LpEndpointFiniteExponentCase ∞

/-- Case split an endpoint-aware exponent with `1 ≤ p` into `1`, `∞`, or a
    finite real exponent `> 1`. -/
theorem LpEndpointFiniteExponentCase.of_one_le
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    LpEndpointFiniteExponentCase p := by
  by_cases hp_one : p = 1
  · rw [hp_one]
    exact LpEndpointFiniteExponentCase.one
  by_cases hp_top : p = ∞
  · rw [hp_top]
    exact LpEndpointFiniteExponentCase.top
  · have hp_gt_one : (1 : ℝ≥0∞) < p := by
      exact lt_of_le_of_ne hp (fun h => hp_one h.symm)
    have hp_real_gt_one : 1 < p.toReal := by
      simpa using
        ((ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp_gt_one)
    have hp_eq : p = ENNReal.ofReal p.toReal := by
      exact (ENNReal.ofReal_toReal hp_top).symm
    rw [hp_eq]
    exact LpEndpointFiniteExponentCase.finite hp_real_gt_one

/-- Exponent data for the finite-dimensional Riesz-Thorin interpolation row:
    `r` lies between `p₀` and `p₁` when reciprocal exponents are interpolated
    by `θ`. -/
structure LpInterpolationData (p₀ p₁ r : ℝ≥0∞) (θ : ℝ) : Prop where
  theta_nonneg : 0 ≤ θ
  theta_le_one : θ ≤ 1
  reciprocal_eq :
    lpRecipExp r = (1 - θ) * lpRecipExp p₀ + θ * lpRecipExp p₁

theorem LpInterpolationData.eq_left_of_theta_zero
    {p₀ p₁ r : ℝ≥0∞} {θ : ℝ}
    (hp₀ : 1 ≤ p₀) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ0 : θ = 0) :
    r = p₀ := by
  apply lpRecipExp_injOn_Ici_one hr hp₀
  rw [hθ.reciprocal_eq, hθ0]
  ring

theorem LpInterpolationData.eq_right_of_theta_one
    {p₀ p₁ r : ℝ≥0∞} {θ : ℝ}
    (hp₁ : 1 ≤ p₁) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ1 : θ = 1) :
    r = p₁ := by
  apply lpRecipExp_injOn_Ici_one hr hp₁
  rw [hθ.reciprocal_eq, hθ1]
  ring

theorem LpInterpolationData.endpoints_eq_one_of_strict_of_eq_one
    {p₀ p₁ r : ℝ≥0∞} {θ : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = 1) :
    p₀ = 1 ∧ p₁ = 1 := by
  let a := lpRecipExp p₀
  let b := lpRecipExp p₁
  have ha_le : a ≤ 1 := lpRecipExp_le_one hp₀
  have hb_le : b ≤ 1 := lpRecipExp_le_one hp₁
  have hrec : (1 - θ) * a + θ * b = 1 := by
    have hrrec : lpRecipExp r = 1 := by
      rw [hr]
      simp
    change (1 - θ) * lpRecipExp p₀ + θ * lpRecipExp p₁ = 1
    linarith [hθ.reciprocal_eq, hrrec]
  have ha : a = 1 := by
    by_contra hne
    have halt : a < 1 := lt_of_le_of_ne ha_le hne
    have hlt :
        (1 - θ) * a + θ * b <
          (1 - θ) * 1 + θ * 1 := by
      apply add_lt_add_of_lt_of_le
      · exact mul_lt_mul_of_pos_left halt (by linarith)
      · exact mul_le_mul_of_nonneg_left hb_le (le_of_lt hθ0)
    nlinarith
  have hb : b = 1 := by
    by_contra hne
    have hblt : b < 1 := lt_of_le_of_ne hb_le hne
    have hlt :
        (1 - θ) * a + θ * b <
          (1 - θ) * 1 + θ * 1 := by
      apply add_lt_add_of_le_of_lt
      · exact mul_le_mul_of_nonneg_left ha_le (by linarith)
      · exact mul_lt_mul_of_pos_left hblt hθ0
    nlinarith
  exact ⟨(lpRecipExp_eq_one_iff.mp ha), (lpRecipExp_eq_one_iff.mp hb)⟩

theorem LpInterpolationData.endpoints_eq_top_of_strict_of_eq_top
    {p₀ p₁ r : ℝ≥0∞} {θ : ℝ}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = ∞) :
    p₀ = ∞ ∧ p₁ = ∞ := by
  let a := lpRecipExp p₀
  let b := lpRecipExp p₁
  have ha_nonneg : 0 ≤ a := lpRecipExp_nonneg p₀
  have hb_nonneg : 0 ≤ b := lpRecipExp_nonneg p₁
  have hrec : (1 - θ) * a + θ * b = 0 := by
    have hrrec : lpRecipExp r = 0 := by
      rw [hr]
      simp
    change (1 - θ) * lpRecipExp p₀ + θ * lpRecipExp p₁ = 0
    linarith [hθ.reciprocal_eq, hrrec]
  have hleft_nonneg : 0 ≤ (1 - θ) * a :=
    mul_nonneg (by linarith) ha_nonneg
  have hright_nonneg : 0 ≤ θ * b :=
    mul_nonneg (le_of_lt hθ0) hb_nonneg
  have hleft_zero : (1 - θ) * a = 0 := by nlinarith
  have hright_zero : θ * b = 0 := by nlinarith
  have ha : a = 0 := by
    rcases mul_eq_zero.mp hleft_zero with hcoef | ha
    · linarith
    · exact ha
  have hb : b = 0 := by
    rcases mul_eq_zero.mp hright_zero with hcoef | hb
    · linarith
    · exact hb
  exact ⟨(lpRecipExp_eq_zero_iff hp₀).mp ha,
    (lpRecipExp_eq_zero_iff hp₁).mp hb⟩

/-- Two endpoint `1` source exponents cannot interpolate to a finite real target
    exponent strictly larger than `1`. -/
theorem LpInterpolationData.false_of_one_one_target_gt_one
    {r θ : ℝ} (hr : 1 < r)
    (hθ : LpInterpolationData 1 1 (ENNReal.ofReal r) θ) :
    False := by
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hrec := hθ.reciprocal_eq
  rw [lpRecipExp_one, lpRecipExp_ofReal hrpos] at hrec
  have hinv : r⁻¹ = 1 := by linarith
  have hr_eq_one : r = 1 := by
    have hmul := congrArg (fun x : ℝ => x * r) hinv
    have hone_eq_r : (1 : ℝ) = r := by
      simpa [hrpos.ne'] using hmul
    exact hone_eq_r.symm
  linarith

/-- Two endpoint `∞` source exponents cannot interpolate to a finite real target
    exponent strictly larger than `1`. -/
theorem LpInterpolationData.false_of_top_top_target_gt_one
    {r θ : ℝ} (hr : 1 < r)
    (hθ : LpInterpolationData ∞ ∞ (ENNReal.ofReal r) θ) :
    False := by
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hrec := hθ.reciprocal_eq
  rw [lpRecipExp_top, lpRecipExp_ofReal hrpos] at hrec
  have hinv : r⁻¹ = 0 := by linarith
  have hinv_pos : 0 < r⁻¹ := inv_pos.mpr hrpos
  linarith

/-- Local conjugacy predicate for endpoint-aware `L^p` exponents. -/
def LpConjugateExponents (p q : ℝ≥0∞) : Prop :=
  1 ≤ p ∧ 1 ≤ q ∧ lpRecipExp p + lpRecipExp q = 1

lemma LpConjugateExponents.one_top :
    LpConjugateExponents 1 ∞ := by
  refine ⟨le_rfl, le_top, ?_⟩
  simp

lemma LpConjugateExponents.top_one :
    LpConjugateExponents ∞ 1 := by
  refine ⟨le_top, le_rfl, ?_⟩
  simp

lemma LpConjugateExponents.ofReal_holderConjugate {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    LpConjugateExponents (ENNReal.ofReal p) (ENNReal.ofReal q) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.lt
  · rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.symm.lt
  · rw [lpRecipExp_ofReal hpq.pos, lpRecipExp_ofReal hpq.symm.pos]
    exact hpq.inv_add_inv_eq_one

lemma LpConjugateExponents.left_ge_one {p q : ℝ≥0∞}
    (hpq : LpConjugateExponents p q) :
    1 ≤ p := hpq.1

lemma LpConjugateExponents.right_ge_one {p q : ℝ≥0∞}
    (hpq : LpConjugateExponents p q) :
    1 ≤ q := hpq.2.1

lemma LpConjugateExponents.recip_right_eq_one_sub {p q : ℝ≥0∞}
    (hpq : LpConjugateExponents p q) :
    lpRecipExp q = 1 - lpRecipExp p := by
  linarith [hpq.2.2]

lemma LpConjugateExponents.recip_left_eq_one_sub {p q : ℝ≥0∞}
    (hpq : LpConjugateExponents p q) :
    lpRecipExp p = 1 - lpRecipExp q := by
  linarith [hpq.2.2]

theorem LpInterpolationData.conjugate
    {p₀ p₁ r q₀ q₁ q : ℝ≥0∞} {θ : ℝ}
    (hpq₀ : LpConjugateExponents p₀ q₀)
    (hpq₁ : LpConjugateExponents p₁ q₁)
    (hrq : LpConjugateExponents r q)
    (hθ : LpInterpolationData p₀ p₁ r θ) :
    LpInterpolationData q₀ q₁ q θ := by
  refine ⟨hθ.theta_nonneg, hθ.theta_le_one, ?_⟩
  have hq : lpRecipExp q = 1 - lpRecipExp r :=
    hrq.recip_right_eq_one_sub
  have hq₀ : lpRecipExp q₀ = 1 - lpRecipExp p₀ :=
    hpq₀.recip_right_eq_one_sub
  have hq₁ : lpRecipExp q₁ = 1 - lpRecipExp p₁ :=
    hpq₁.recip_right_eq_one_sub
  calc
    lpRecipExp q = 1 - lpRecipExp r := hq
    _ = 1 - ((1 - θ) * lpRecipExp p₀ + θ * lpRecipExp p₁) := by
      rw [hθ.reciprocal_eq]
    _ = (1 - θ) * (1 - lpRecipExp p₀) +
          θ * (1 - lpRecipExp p₁) := by
      ring
    _ = (1 - θ) * lpRecipExp q₀ + θ * lpRecipExp q₁ := by
      rw [hq₀, hq₁]

theorem LpInterpolationData.affineExponent_eq_one_ofReal
    {p₀ p₁ r : ℝ} {θ : ℝ}
    (hp₀ : 0 < p₀) (hp₁ : 0 < p₁) (hr : 0 < r)
    (hθ : LpInterpolationData
      (ENNReal.ofReal p₀) (ENNReal.ofReal p₁) (ENNReal.ofReal r) θ) :
    r * ((1 - θ) * p₀⁻¹ + θ * p₁⁻¹) = 1 := by
  have hrec := hθ.reciprocal_eq
  rw [lpRecipExp_ofReal hp₀, lpRecipExp_ofReal hp₁,
    lpRecipExp_ofReal hr] at hrec
  calc
    r * ((1 - θ) * p₀⁻¹ + θ * p₁⁻¹) = r * r⁻¹ := by
      rw [← hrec]
    _ = 1 := by
      field_simp [ne_of_gt hr]

/-- Endpoint-aware affine-exponent recovery when the left exponent is `1`. -/
theorem LpInterpolationData.affineExponent_eq_one_one_left_ofReal
    {p r θ : ℝ} (hp : 0 < p) (hr : 0 < r)
    (hθ : LpInterpolationData 1 (ENNReal.ofReal p) (ENNReal.ofReal r) θ) :
    r * ((1 - θ) * (1 : ℝ) + θ * p⁻¹) = 1 := by
  have hrec := hθ.reciprocal_eq
  rw [lpRecipExp_one, lpRecipExp_ofReal hp, lpRecipExp_ofReal hr] at hrec
  calc
    r * ((1 - θ) * (1 : ℝ) + θ * p⁻¹) = r * r⁻¹ := by
      rw [← hrec]
    _ = 1 := by
      field_simp [ne_of_gt hr]

/-- Endpoint-aware affine-exponent recovery when the left exponent is
    `infinity`. -/
theorem LpInterpolationData.affineExponent_eq_one_top_left_ofReal
    {p r θ : ℝ} (hp : 0 < p) (hr : 0 < r)
    (hθ : LpInterpolationData ∞ (ENNReal.ofReal p) (ENNReal.ofReal r) θ) :
    r * ((1 - θ) * (0 : ℝ) + θ * p⁻¹) = 1 := by
  have hrec := hθ.reciprocal_eq
  rw [lpRecipExp_top, lpRecipExp_ofReal hp, lpRecipExp_ofReal hr] at hrec
  calc
    r * ((1 - θ) * (0 : ℝ) + θ * p⁻¹) = r * r⁻¹ := by
      rw [← hrec]
    _ = 1 := by
      field_simp [ne_of_gt hr]

/-- Endpoint-aware affine-exponent recovery when the right exponent is `1`. -/
theorem LpInterpolationData.affineExponent_eq_one_one_right_ofReal
    {p r θ : ℝ} (hp : 0 < p) (hr : 0 < r)
    (hθ : LpInterpolationData (ENNReal.ofReal p) 1 (ENNReal.ofReal r) θ) :
    r * ((1 - θ) * p⁻¹ + θ * (1 : ℝ)) = 1 := by
  have hrec := hθ.reciprocal_eq
  rw [lpRecipExp_one, lpRecipExp_ofReal hp, lpRecipExp_ofReal hr] at hrec
  calc
    r * ((1 - θ) * p⁻¹ + θ * (1 : ℝ)) = r * r⁻¹ := by
      rw [← hrec]
    _ = 1 := by
      field_simp [ne_of_gt hr]

/-- Endpoint-aware affine-exponent recovery when the right exponent is
    `infinity`. -/
theorem LpInterpolationData.affineExponent_eq_one_top_right_ofReal
    {p r θ : ℝ} (hp : 0 < p) (hr : 0 < r)
    (hθ : LpInterpolationData (ENNReal.ofReal p) ∞ (ENNReal.ofReal r) θ) :
    r * ((1 - θ) * p⁻¹ + θ * (0 : ℝ)) = 1 := by
  have hrec := hθ.reciprocal_eq
  rw [lpRecipExp_top, lpRecipExp_ofReal hp, lpRecipExp_ofReal hr] at hrec
  calc
    r * ((1 - θ) * p⁻¹ + θ * (0 : ℝ)) = r * r⁻¹ := by
      rw [← hrec]
    _ = 1 := by
      field_simp [ne_of_gt hr]

/-- A phase with norm at most one that turns `z` into its absolute value. -/
noncomputable def complexUnitPhase (z : ℂ) : ℂ :=
  if z = 0 then 0 else z⁻¹ * (‖z‖ : ℂ)

lemma complexUnitPhase_norm_le_one (z : ℂ) :
    ‖complexUnitPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [complexUnitPhase, hz]
  · have hznorm_ne : ‖z‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hz
    calc
      ‖complexUnitPhase z‖ = ‖z⁻¹ * (‖z‖ : ℂ)‖ := by
        simp [complexUnitPhase, hz]
      _ = ‖z⁻¹‖ * ‖(‖z‖ : ℂ)‖ := norm_mul _ _
      _ = ‖z‖⁻¹ * ‖z‖ := by
        rw [norm_inv, Complex.norm_of_nonneg (norm_nonneg z)]
      _ = 1 := by
        field_simp [hznorm_ne]
      _ ≤ 1 := le_rfl

lemma mul_complexUnitPhase_eq_norm (z : ℂ) :
    z * complexUnitPhase z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp [complexUnitPhase, hz]
  · simp [complexUnitPhase, hz]

/-- Coordinate family used in the finite-dimensional Riesz-Thorin proof route.
    For a nonzero coordinate `a`, this is the analytic function
    `a * exp ((s - 1) log ||a||)`.  It equals `a` at exponent `1`, while its
    norm is `||a||^(Re s)`.  The zero coordinate is kept identically zero. -/
noncomputable def complexRieszThorinAnalyticCoord (a s : ℂ) : ℂ :=
  if a = 0 then 0 else a * Complex.exp ((s - 1) * (Real.log ‖a‖ : ℂ))

@[simp]
lemma complexRieszThorinAnalyticCoord_zero_left (s : ℂ) :
    complexRieszThorinAnalyticCoord 0 s = 0 := by
  simp [complexRieszThorinAnalyticCoord]

@[simp]
lemma complexRieszThorinAnalyticCoord_at_one (a : ℂ) :
    complexRieszThorinAnalyticCoord a 1 = a := by
  by_cases ha : a = 0
  · simp [complexRieszThorinAnalyticCoord, ha]
  · simp [complexRieszThorinAnalyticCoord, ha]

lemma complexRieszThorinAnalyticCoord_of_ne_zero {a s : ℂ} (ha : a ≠ 0) :
    complexRieszThorinAnalyticCoord a s =
      a * Complex.exp ((s - 1) * (Real.log ‖a‖ : ℂ)) := by
  simp [complexRieszThorinAnalyticCoord, ha]

/-- Norm formula for the Riesz-Thorin coordinate family.  This is the local
    algebraic calculation behind the boundary and closed-strip estimates in the
    future three-lines proof of equations (6.18)-(6.20). -/
lemma complexRieszThorinAnalyticCoord_norm_of_ne_zero {a s : ℂ} (ha : a ≠ 0) :
    ‖complexRieszThorinAnalyticCoord a s‖ = ‖a‖ ^ s.re := by
  have hnorm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  calc
    ‖complexRieszThorinAnalyticCoord a s‖ =
        ‖a * Complex.exp ((s - 1) * (Real.log ‖a‖ : ℂ))‖ := by
          simp [complexRieszThorinAnalyticCoord, ha]
    _ = ‖a‖ * Real.exp (((s - 1) * (Real.log ‖a‖ : ℂ)).re) := by
          rw [norm_mul, Complex.norm_exp]
    _ = ‖a‖ * Real.exp ((s.re - 1) * Real.log ‖a‖) := by
          congr 1
          simp [Complex.mul_re]
    _ = Real.exp (Real.log ‖a‖) * Real.exp ((s.re - 1) * Real.log ‖a‖) := by
          rw [Real.exp_log hnorm_pos]
    _ = Real.exp (s.re * Real.log ‖a‖) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ = ‖a‖ ^ s.re := by
          rw [Real.rpow_def_of_pos hnorm_pos]
          ring_nf

lemma complexRieszThorinAnalyticCoord_norm_le_one_of_norm_le_one_of_re_nonneg
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : 0 ≤ s.re) :
    ‖complexRieszThorinAnalyticCoord a s‖ ≤ 1 := by
  by_cases hzero : a = 0
  · simp [complexRieszThorinAnalyticCoord, hzero]
  · rw [complexRieszThorinAnalyticCoord_norm_of_ne_zero hzero]
    exact Real.rpow_le_one (norm_nonneg a) ha hs

lemma complexRieszThorinAnalyticCoord_differentiable (a : ℂ) :
    Differentiable ℂ (fun s : ℂ => complexRieszThorinAnalyticCoord a s) := by
  by_cases ha : a = 0
  · simp [complexRieszThorinAnalyticCoord, ha]
  · have hlin : Differentiable ℂ
        (fun s : ℂ => (s - 1) * (Real.log ‖a‖ : ℂ)) :=
      (differentiable_id.sub_const (1 : ℂ)).mul_const (Real.log ‖a‖ : ℂ)
    have hexp : Differentiable ℂ
        (fun s : ℂ => Complex.exp ((s - 1) * (Real.log ‖a‖ : ℂ))) :=
      hlin.cexp
    simpa [complexRieszThorinAnalyticCoord, ha] using hexp.const_mul a

lemma complexRieszThorinAnalyticCoord_diffContOnCl (a : ℂ) (s : Set ℂ) :
    DiffContOnCl ℂ (fun z : ℂ => complexRieszThorinAnalyticCoord a z) s :=
  (complexRieszThorinAnalyticCoord_differentiable a).diffContOnCl

/-- Affine complex exponent used for the scalar families in the Riesz-Thorin
    proof route.  If `scale = r.toReal`, `left = 1/p₀`, and `right = 1/p₁`,
    then the real part is the interpolated reciprocal exponent on vertical
    lines. -/
noncomputable def complexRieszThorinAffineExponent
    (scale left right : ℝ) (z : ℂ) : ℂ :=
  (scale : ℂ) * (((1 - z) * (left : ℂ)) + z * (right : ℂ))

lemma complexRieszThorinAffineExponent_differentiable
    (scale left right : ℝ) :
    Differentiable ℂ (fun z : ℂ =>
      complexRieszThorinAffineExponent scale left right z) := by
  have hleftTerm : Differentiable ℂ (fun z : ℂ => (1 - z) * (left : ℂ)) :=
    (differentiable_id.const_sub (1 : ℂ)).mul_const (left : ℂ)
  have hrightTerm : Differentiable ℂ (fun z : ℂ => z * (right : ℂ)) :=
    differentiable_id.mul_const (right : ℂ)
  simpa [complexRieszThorinAffineExponent] using
    (hleftTerm.add hrightTerm).const_mul (scale : ℂ)

lemma complexRieszThorinAffineExponent_diffContOnCl
    (scale left right : ℝ) (s : Set ℂ) :
    DiffContOnCl ℂ
      (fun z : ℂ => complexRieszThorinAffineExponent scale left right z) s :=
  (complexRieszThorinAffineExponent_differentiable scale left right).diffContOnCl

lemma complexRieszThorinAffineExponent_re
    (scale left right : ℝ) (z : ℂ) :
    (complexRieszThorinAffineExponent scale left right z).re =
      scale * ((1 - z.re) * left + z.re * right) := by
  simp [complexRieszThorinAffineExponent, Complex.mul_re]

lemma complexRieszThorinAffineExponent_re_of_re_zero
    {scale left right : ℝ} {z : ℂ} (hz : z.re = 0) :
    (complexRieszThorinAffineExponent scale left right z).re = scale * left := by
  rw [complexRieszThorinAffineExponent_re, hz]
  ring

lemma complexRieszThorinAffineExponent_re_of_re_one
    {scale left right : ℝ} {z : ℂ} (hz : z.re = 1) :
    (complexRieszThorinAffineExponent scale left right z).re = scale * right := by
  rw [complexRieszThorinAffineExponent_re, hz]
  ring

lemma complexRieszThorinAffineExponent_re_left_vertical
    (scale left right t : ℝ) :
    (complexRieszThorinAffineExponent scale left right (Complex.I * (t : ℂ))).re =
      scale * left := by
  exact complexRieszThorinAffineExponent_re_of_re_zero
    (scale := scale) (left := left) (right := right)
    (z := Complex.I * (t : ℂ)) (by simp)

lemma complexRieszThorinAffineExponent_re_right_vertical
    (scale left right t : ℝ) :
    (complexRieszThorinAffineExponent scale left right ((1 : ℂ) + Complex.I * (t : ℂ))).re =
      scale * right := by
  exact complexRieszThorinAffineExponent_re_of_re_one
    (scale := scale) (left := left) (right := right)
    (z := (1 : ℂ) + Complex.I * (t : ℂ)) (by simp)

lemma complexRieszThorinAffineExponent_at_real
    {scale left right θ target : ℝ}
    (h : scale * ((1 - θ) * left + θ * right) = target) :
    complexRieszThorinAffineExponent scale left right (θ : ℂ) =
      (target : ℂ) := by
  apply Complex.ext
  · simp [complexRieszThorinAffineExponent, h]
  · simp [complexRieszThorinAffineExponent]

lemma complexRieszThorinAffineExponent_at_real_one
    {scale left right θ : ℝ}
    (h : scale * ((1 - θ) * left + θ * right) = 1) :
    complexRieszThorinAffineExponent scale left right (θ : ℂ) = 1 := by
  simpa using
    (complexRieszThorinAffineExponent_at_real
      (scale := scale) (left := left) (right := right)
      (θ := θ) (target := 1) h)

lemma complexRieszThorinAffineExponent_re_nonneg_of_re_mem_Icc
    {scale left right : ℝ} {z : ℂ}
    (hscale : 0 ≤ scale) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    0 ≤ (complexRieszThorinAffineExponent scale left right z).re := by
  rw [complexRieszThorinAffineExponent_re]
  exact mul_nonneg hscale
    (add_nonneg
      (mul_nonneg (by linarith) hleft)
      (mul_nonneg hz0 hright))

/-- Coordinatewise vector family used in the finite-dimensional Riesz-Thorin
    proof route. -/
noncomputable def complexRieszThorinAnalyticVec {n : ℕ}
    (x : CVec n) (s : ℂ) : CVec n :=
  fun j => complexRieszThorinAnalyticCoord (x j) s

@[simp]
lemma complexRieszThorinAnalyticVec_at_one {n : ℕ} (x : CVec n) :
    complexRieszThorinAnalyticVec x 1 = x := by
  funext j
  simp [complexRieszThorinAnalyticVec]

lemma complexRieszThorinAnalyticVec_coord_differentiable
    {n : ℕ} (x : CVec n) (scale left right : ℝ) (j : Fin n) :
    Differentiable ℂ (fun z : ℂ =>
      complexRieszThorinAnalyticVec x
        (complexRieszThorinAffineExponent scale left right z) j) := by
  simpa [Function.comp, complexRieszThorinAnalyticVec] using
    (complexRieszThorinAnalyticCoord_differentiable (x j)).comp
      (complexRieszThorinAffineExponent_differentiable scale left right)

lemma complexRieszThorinAnalyticVec_coord_diffContOnCl
    {n : ℕ} (x : CVec n) (scale left right : ℝ) (j : Fin n) (s : Set ℂ) :
    DiffContOnCl ℂ
      (fun z : ℂ =>
        complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z) j) s :=
  (complexRieszThorinAnalyticVec_coord_differentiable x scale left right j).diffContOnCl

lemma complexRieszThorinAnalyticVec_at_affineExponent_real_one
    {n : ℕ} (x : CVec n) {scale left right θ : ℝ}
    (h : scale * ((1 - θ) * left + θ * right) = 1) :
    complexRieszThorinAnalyticVec x
      (complexRieszThorinAffineExponent scale left right (θ : ℂ)) = x := by
  rw [complexRieszThorinAffineExponent_at_real_one h]
  simp

@[simp]
lemma complexRieszThorinAnalyticVec_coord_zero_of_coord_zero
    {n : ℕ} {x : CVec n} {s : ℂ} {j : Fin n} (hxj : x j = 0) :
    complexRieszThorinAnalyticVec x s j = 0 := by
  simp [complexRieszThorinAnalyticVec, hxj]

lemma complexRieszThorinAnalyticVec_coord_norm_of_ne_zero
    {n : ℕ} {x : CVec n} {s : ℂ} {j : Fin n} (hxj : x j ≠ 0) :
    ‖complexRieszThorinAnalyticVec x s j‖ = ‖x j‖ ^ s.re := by
  exact complexRieszThorinAnalyticCoord_norm_of_ne_zero hxj

lemma complexRieszThorinAnalyticVec_coord_norm_affine_of_ne_zero
    {n : ℕ} {x : CVec n} {scale left right : ℝ} {z : ℂ} {j : Fin n}
    (hxj : x j ≠ 0) :
    ‖complexRieszThorinAnalyticVec x
        (complexRieszThorinAffineExponent scale left right z) j‖ =
      ‖x j‖ ^ (scale * ((1 - z.re) * left + z.re * right)) := by
  rw [complexRieszThorinAnalyticVec_coord_norm_of_ne_zero hxj,
    complexRieszThorinAffineExponent_re]

lemma complexRieszThorinAnalyticVec_coord_norm_affine_of_ne_zero_of_re_zero
    {n : ℕ} {x : CVec n} {scale left right : ℝ} {z : ℂ} {j : Fin n}
    (hxj : x j ≠ 0) (hz : z.re = 0) :
    ‖complexRieszThorinAnalyticVec x
        (complexRieszThorinAffineExponent scale left right z) j‖ =
      ‖x j‖ ^ (scale * left) := by
  rw [complexRieszThorinAnalyticVec_coord_norm_affine_of_ne_zero hxj]
  congr 1
  rw [hz]
  ring

lemma complexRieszThorinAnalyticVec_coord_norm_affine_of_ne_zero_of_re_one
    {n : ℕ} {x : CVec n} {scale left right : ℝ} {z : ℂ} {j : Fin n}
    (hxj : x j ≠ 0) (hz : z.re = 1) :
    ‖complexRieszThorinAnalyticVec x
        (complexRieszThorinAffineExponent scale left right z) j‖ =
      ‖x j‖ ^ (scale * right) := by
  rw [complexRieszThorinAnalyticVec_coord_norm_affine_of_ne_zero hxj]
  congr 1
  rw [hz]
  ring

lemma complexRieszThorinAnalyticVec_coord_norm_affine_left_vertical_of_ne_zero
    {n : ℕ} {x : CVec n} {scale left right t : ℝ} {j : Fin n}
    (hxj : x j ≠ 0) :
    ‖complexRieszThorinAnalyticVec x
        (complexRieszThorinAffineExponent scale left right (Complex.I * (t : ℂ))) j‖ =
      ‖x j‖ ^ (scale * left) := by
  exact complexRieszThorinAnalyticVec_coord_norm_affine_of_ne_zero_of_re_zero
    (scale := scale) (left := left) (right := right)
    (z := Complex.I * (t : ℂ)) hxj (by simp)

lemma complexRieszThorinAnalyticVec_coord_norm_affine_right_vertical_of_ne_zero
    {n : ℕ} {x : CVec n} {scale left right t : ℝ} {j : Fin n}
    (hxj : x j ≠ 0) :
    ‖complexRieszThorinAnalyticVec x
        (complexRieszThorinAffineExponent scale left right ((1 : ℂ) + Complex.I * (t : ℂ))) j‖ =
      ‖x j‖ ^ (scale * right) := by
  exact complexRieszThorinAnalyticVec_coord_norm_affine_of_ne_zero_of_re_one
    (scale := scale) (left := left) (right := right)
    (z := (1 : ℂ) + Complex.I * (t : ℂ)) hxj (by simp)

lemma complexRieszThorinAnalyticVec_sum_norm_rpow_affine_of_re_zero
    {n : ℕ} {x : CVec n} {p scale left right target : ℝ} {z : ℂ}
    (hp : 0 < p) (htarget_pos : 0 < target) (hz : z.re = 0)
    (hpow : (scale * left) * p = target) :
    (∑ j : Fin n,
        ‖complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z) j‖ ^ p) =
      ∑ j : Fin n, ‖x j‖ ^ target := by
  classical
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hxj : x j = 0
  · simp [complexRieszThorinAnalyticVec, hxj, Real.zero_rpow hp.ne',
      Real.zero_rpow htarget_pos.ne']
  · rw [complexRieszThorinAnalyticVec_coord_norm_affine_of_ne_zero_of_re_zero hxj hz]
    rw [← Real.rpow_mul (norm_nonneg (x j)) (scale * left) p]
    rw [hpow]

lemma complexRieszThorinAnalyticVec_sum_norm_rpow_affine_of_re_one
    {n : ℕ} {x : CVec n} {p scale left right target : ℝ} {z : ℂ}
    (hp : 0 < p) (htarget_pos : 0 < target) (hz : z.re = 1)
    (hpow : (scale * right) * p = target) :
    (∑ j : Fin n,
        ‖complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z) j‖ ^ p) =
      ∑ j : Fin n, ‖x j‖ ^ target := by
  classical
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hxj : x j = 0
  · simp [complexRieszThorinAnalyticVec, hxj, Real.zero_rpow hp.ne',
      Real.zero_rpow htarget_pos.ne']
  · rw [complexRieszThorinAnalyticVec_coord_norm_affine_of_ne_zero_of_re_one hxj hz]
    rw [← Real.rpow_mul (norm_nonneg (x j)) (scale * right) p]
    rw [hpow]

lemma complexRieszThorinAnalyticVec_lpNorm_rpow_affine_of_re_zero
    {n : ℕ} {x : CVec n} {p scale left right target : ℝ} {z : ℂ}
    (hp : 0 < p) (htarget_pos : 0 < target) (hz : z.re = 0)
    (hpow : (scale * left) * p = target) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z)) ^ p =
      ∑ j : Fin n, ‖x j‖ ^ target := by
  rw [complexVecLpNorm_rpow_eq_sum_rpow hp]
  exact complexRieszThorinAnalyticVec_sum_norm_rpow_affine_of_re_zero
    (x := x) (right := right) hp htarget_pos hz hpow

lemma complexRieszThorinAnalyticVec_lpNorm_rpow_affine_of_re_one
    {n : ℕ} {x : CVec n} {p scale left right target : ℝ} {z : ℂ}
    (hp : 0 < p) (htarget_pos : 0 < target) (hz : z.re = 1)
    (hpow : (scale * right) * p = target) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z)) ^ p =
      ∑ j : Fin n, ‖x j‖ ^ target := by
  rw [complexVecLpNorm_rpow_eq_sum_rpow hp]
  exact complexRieszThorinAnalyticVec_sum_norm_rpow_affine_of_re_one
    (x := x) (left := left) hp htarget_pos hz hpow

lemma complexRieszThorinAnalyticVec_lpNorm_rpow_affine_eq_lpNorm_rpow_of_re_zero
    {n : ℕ} {x : CVec n} {p scale left right target : ℝ} {z : ℂ}
    (hp : 0 < p) (htarget_pos : 0 < target) (hz : z.re = 0)
    (hpow : (scale * left) * p = target) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z)) ^ p =
      complexVecLpNorm (ENNReal.ofReal target) x ^ target := by
  rw [complexRieszThorinAnalyticVec_lpNorm_rpow_affine_of_re_zero
    hp htarget_pos hz hpow]
  rw [complexVecLpNorm_rpow_eq_sum_rpow htarget_pos]

lemma complexRieszThorinAnalyticVec_lpNorm_rpow_affine_eq_lpNorm_rpow_of_re_one
    {n : ℕ} {x : CVec n} {p scale left right target : ℝ} {z : ℂ}
    (hp : 0 < p) (htarget_pos : 0 < target) (hz : z.re = 1)
    (hpow : (scale * right) * p = target) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z)) ^ p =
      complexVecLpNorm (ENNReal.ofReal target) x ^ target := by
  rw [complexRieszThorinAnalyticVec_lpNorm_rpow_affine_of_re_one
    hp htarget_pos hz hpow]
  rw [complexVecLpNorm_rpow_eq_sum_rpow htarget_pos]

lemma complexVecLpNorm_ofReal_nonneg {n : ℕ} {p : ℝ} (hp : 0 < p)
    (x : CVec n) :
    0 ≤ complexVecLpNorm (ENNReal.ofReal p) x := by
  rw [complexVecLpNorm_ofReal_eq_sum_rpow hp x]
  exact Real.rpow_nonneg
    (Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (x i)) p))
    p⁻¹

lemma complexVecLpNorm_le_one_of_rpow_le_one {n : ℕ} {p : ℝ}
    (hp : 0 < p) (x : CVec n)
    (hpow : complexVecLpNorm (ENNReal.ofReal p) x ^ p ≤ 1) :
    complexVecLpNorm (ENNReal.ofReal p) x ≤ 1 := by
  have hnorm_nonneg : 0 ≤ complexVecLpNorm (ENNReal.ofReal p) x :=
    complexVecLpNorm_ofReal_nonneg hp x
  have hpow' :
      complexVecLpNorm (ENNReal.ofReal p) x ^ p ≤ (1 : ℝ) ^ p := by
    simpa using hpow
  exact (Real.rpow_le_rpow_iff hnorm_nonneg zero_le_one hp).mp hpow'

lemma complexRieszThorinAnalyticVec_lpNorm_affine_le_one_of_re_zero
    {n : ℕ} {x : CVec n} {p scale left right target : ℝ} {z : ℂ}
    (hp : 0 < p) (htarget_pos : 0 < target) (hz : z.re = 0)
    (hpow : (scale * left) * p = target)
    (hx : complexVecLpNorm (ENNReal.ofReal target) x ≤ 1) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z)) ≤ 1 := by
  apply complexVecLpNorm_le_one_of_rpow_le_one hp
  rw [complexRieszThorinAnalyticVec_lpNorm_rpow_affine_eq_lpNorm_rpow_of_re_zero
    hp htarget_pos hz hpow]
  exact Real.rpow_le_one
    (complexVecLpNorm_ofReal_nonneg htarget_pos x)
    hx (le_of_lt htarget_pos)

lemma complexRieszThorinAnalyticVec_lpNorm_affine_le_one_of_re_one
    {n : ℕ} {x : CVec n} {p scale left right target : ℝ} {z : ℂ}
    (hp : 0 < p) (htarget_pos : 0 < target) (hz : z.re = 1)
    (hpow : (scale * right) * p = target)
    (hx : complexVecLpNorm (ENNReal.ofReal target) x ≤ 1) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z)) ≤ 1 := by
  apply complexVecLpNorm_le_one_of_rpow_le_one hp
  rw [complexRieszThorinAnalyticVec_lpNorm_rpow_affine_eq_lpNorm_rpow_of_re_one
    hp htarget_pos hz hpow]
  exact Real.rpow_le_one
    (complexVecLpNorm_ofReal_nonneg htarget_pos x)
    hx (le_of_lt htarget_pos)

lemma complexRieszThorinAnalyticVec_lpNorm_affine_left_vertical_le_one
    {n : ℕ} {x : CVec n} {p scale left right target t : ℝ}
    (hp : 0 < p) (htarget_pos : 0 < target)
    (hpow : (scale * left) * p = target)
    (hx : complexVecLpNorm (ENNReal.ofReal target) x ≤ 1) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right (Complex.I * (t : ℂ)))) ≤ 1 := by
  exact complexRieszThorinAnalyticVec_lpNorm_affine_le_one_of_re_zero
    (right := right) hp htarget_pos (by simp) hpow hx

lemma complexRieszThorinAnalyticVec_lpNorm_affine_right_vertical_le_one
    {n : ℕ} {x : CVec n} {p scale left right target t : ℝ}
    (hp : 0 < p) (htarget_pos : 0 < target)
    (hpow : (scale * right) * p = target)
    (hx : complexVecLpNorm (ENNReal.ofReal target) x ≤ 1) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right
            ((1 : ℂ) + Complex.I * (t : ℂ)))) ≤ 1 := by
  exact complexRieszThorinAnalyticVec_lpNorm_affine_le_one_of_re_one
    (left := left) hp htarget_pos (by simp) hpow hx

lemma complexRieszThorinAnalyticVec_coord_norm_le_one
    {n : ℕ} {x : CVec n} {s : ℂ}
    (hx : ∀ j : Fin n, ‖x j‖ ≤ 1) (hs : 0 ≤ s.re) (j : Fin n) :
    ‖complexRieszThorinAnalyticVec x s j‖ ≤ 1 := by
  exact complexRieszThorinAnalyticCoord_norm_le_one_of_norm_le_one_of_re_nonneg
    (hx j) hs

lemma complexRieszThorinAnalyticVec_coord_norm_le_one_of_affineExponent_re_mem_Icc
    {n : ℕ} {x : CVec n} {scale left right : ℝ} {z : ℂ}
    (hx : ∀ j : Fin n, ‖x j‖ ≤ 1)
    (hscale : 0 ≤ scale) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (j : Fin n) :
    ‖complexRieszThorinAnalyticVec x
        (complexRieszThorinAffineExponent scale left right z) j‖ ≤ 1 := by
  exact complexRieszThorinAnalyticVec_coord_norm_le_one hx
    (complexRieszThorinAffineExponent_re_nonneg_of_re_mem_Icc
      hscale hleft hright hz0 hz1) j

lemma complexRieszThorinAnalyticVec_infNorm_affine_le_one_of_re_zero
    {n : ℕ} {x : CVec n} {scale right target : ℝ} {z : ℂ}
    [Fact (1 ≤ ENNReal.ofReal target)]
    (hscale : 0 ≤ scale) (hright : 0 ≤ right) (hz : z.re = 0)
    (hx : complexVecLpNorm (ENNReal.ofReal target) x ≤ 1) :
    complexVecInfNorm
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale 0 right z)) ≤ 1 := by
  apply complexVecInfNorm_le_of_coord_le _ zero_le_one
  intro j
  exact complexRieszThorinAnalyticVec_coord_norm_le_one_of_affineExponent_re_mem_Icc
    (x := x) (scale := scale) (left := 0) (right := right) (z := z)
    (fun k => complexVecLpNorm_coord_le_one_of_le_one
      (ENNReal.ofReal target) hx k)
    hscale (by norm_num) hright
    (by simp [hz])
    (by simp [hz]) j

/-- A nonnegative `L^p` unit-ball witness that attains the finite `L^q` norm
    in the `NNReal` Hölder duality theorem. -/
lemma exists_nnreal_lp_normer {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (a : CVec n) :
    ∃ g : Fin n → NNReal,
      (∑ j : Fin n, g j ^ p) ≤ 1 ∧
        (∑ j : Fin n, ‖a j‖₊ * g j) =
          (∑ j : Fin n, ‖a j‖₊ ^ q) ^ (1 / q) := by
  classical
  have hmax :=
    NNReal.isGreatest_Lp (s := Finset.univ)
      (f := fun j : Fin n => ‖a j‖₊) hpq.symm
  rcases hmax.1 with ⟨g, hg_unit, hvalue⟩
  refine ⟨g, ?_, ?_⟩
  · simpa using hg_unit
  · simpa using hvalue

/-- Finite complex `L^p` duality attains the row `L^q` norm on the `L^p`
    unit ball, for finite conjugate exponents. -/
theorem complexVecLpNorm_exists_rowNormingVector {n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (a : CVec n) :
    ∃ x : CVec n,
      complexVecLpNorm (ENNReal.ofReal p) x ≤ 1 ∧
        ‖∑ j : Fin n, a j * x j‖ = complexVecLpNorm (ENNReal.ofReal q) a := by
  classical
  obtain ⟨g, hg_unit, hvalue⟩ := exists_nnreal_lp_normer hpq a
  let x : CVec n := fun j => complexUnitPhase (a j) * ((g j : ℝ) : ℂ)
  refine ⟨x, ?_, ?_⟩
  · have hg_real : (∑ j : Fin n, (g j : ℝ) ^ p) ≤ 1 := by
      have hg_cast : ((∑ j : Fin n, g j ^ p : NNReal) : ℝ) ≤ 1 := by
        exact_mod_cast hg_unit
      simpa [NNReal.coe_rpow] using hg_cast
    have hx_coord : ∀ j : Fin n, ‖x j‖ ≤ (g j : ℝ) := by
      intro j
      dsimp [x]
      calc
        ‖complexUnitPhase (a j) * ((g j : ℝ) : ℂ)‖
            = ‖complexUnitPhase (a j)‖ * (g j : ℝ) := by
                rw [norm_mul, Complex.norm_of_nonneg (NNReal.coe_nonneg (g j))]
        _ ≤ 1 * (g j : ℝ) :=
            mul_le_mul_of_nonneg_right
              (complexUnitPhase_norm_le_one (a j)) (NNReal.coe_nonneg (g j))
        _ = (g j : ℝ) := one_mul _
    have hxsum : (∑ j : Fin n, ‖x j‖ ^ p) ≤ 1 := by
      calc
        (∑ j : Fin n, ‖x j‖ ^ p)
            ≤ ∑ j : Fin n, (g j : ℝ) ^ p := by
                apply Finset.sum_le_sum
                intro j _hj
                exact Real.rpow_le_rpow (norm_nonneg (x j)) (hx_coord j) hpq.nonneg
        _ ≤ 1 := hg_real
    have hp_toReal : (ENNReal.ofReal p).toReal = p :=
      ENNReal.toReal_ofReal hpq.nonneg
    have hxsum_nonneg : 0 ≤ (∑ j : Fin n, ‖x j‖ ^ p) := by
      apply Finset.sum_nonneg
      intro j _hj
      exact Real.rpow_nonneg (norm_nonneg (x j)) p
    unfold complexVecLpNorm
    rw [PiLp.norm_eq_sum]
    · rw [hp_toReal]
      exact Real.rpow_le_one hxsum_nonneg hxsum (one_div_pos.mpr hpq.pos).le
    · rw [hp_toReal]
      exact hpq.pos
  · have hvalue_real :
        (∑ j : Fin n, ‖a j‖ * (g j : ℝ)) =
          (∑ j : Fin n, ‖a j‖ ^ q) ^ (1 / q) := by
      have hvalue_cast :=
        congrArg (fun t : NNReal => (t : ℝ)) hvalue
      simpa [NNReal.coe_rpow] using hvalue_cast
    have hq_toReal : (ENNReal.ofReal q).toReal = q :=
      ENNReal.toReal_ofReal hpq.symm.nonneg
    have hqnorm_eq :
        complexVecLpNorm (ENNReal.ofReal q) a =
          (∑ j : Fin n, ‖a j‖ ^ q) ^ (1 / q) := by
      unfold complexVecLpNorm
      rw [PiLp.norm_eq_sum]
      · rw [hq_toReal]
      · rw [hq_toReal]
        exact hpq.symm.pos
    have hrow :
        (∑ j : Fin n, a j * x j) =
          ((∑ j : Fin n, ‖a j‖ * (g j : ℝ) : ℝ) : ℂ) := by
      calc
        (∑ j : Fin n, a j * x j)
            = ∑ j : Fin n, ((‖a j‖ * (g j : ℝ) : ℝ) : ℂ) := by
                apply Finset.sum_congr rfl
                intro j _hj
                dsimp [x]
                calc
                  a j * (complexUnitPhase (a j) * ((g j : ℝ) : ℂ))
                      = (a j * complexUnitPhase (a j)) * ((g j : ℝ) : ℂ) := by ring
                  _ = (‖a j‖ : ℂ) * ((g j : ℝ) : ℂ) := by
                      rw [mul_complexUnitPhase_eq_norm]
                  _ = ((‖a j‖ * (g j : ℝ) : ℝ) : ℂ) := by norm_num
        _ = ((∑ j : Fin n, ‖a j‖ * (g j : ℝ) : ℝ) : ℂ) := by
            norm_num
    have hrow_exact :
        (∑ j : Fin n, a j * x j) =
          (complexVecLpNorm (ENNReal.ofReal q) a : ℂ) := by
      rw [hrow, hqnorm_eq, ← hvalue_real]
    rw [hrow_exact]
    exact Complex.norm_of_nonneg
      (by
        rw [hqnorm_eq]
        exact Real.rpow_nonneg
          (Finset.sum_nonneg (fun j _hj => Real.rpow_nonneg (norm_nonneg (a j)) q))
          (1 / q))

/-- Any nonnegative row-functional bound for the finite complex `L^p` norm is
    at least the row's `L^q` norm. This is the lower-bound half of finite
    `L^p`/`L^q` duality. -/
theorem complexVecLpNorm_le_of_rowFunctional_bound {n : ℕ} {p q e : ℝ}
    (hpq : p.HolderConjugate q) (a : CVec n) (he_nonneg : 0 ≤ e)
    (hbound : ∀ x : CVec n,
      ‖∑ j : Fin n, a j * x j‖ ≤ e * complexVecLpNorm (ENNReal.ofReal p) x) :
    complexVecLpNorm (ENNReal.ofReal q) a ≤ e := by
  obtain ⟨x, hxnorm, hrow⟩ := complexVecLpNorm_exists_rowNormingVector hpq a
  calc
    complexVecLpNorm (ENNReal.ofReal q) a = ‖∑ j : Fin n, a j * x j‖ := hrow.symm
    _ ≤ e * complexVecLpNorm (ENNReal.ofReal p) x := hbound x
    _ ≤ e * 1 := mul_le_mul_of_nonneg_left hxnorm he_nonneg
    _ = e := by ring
end NumStability
