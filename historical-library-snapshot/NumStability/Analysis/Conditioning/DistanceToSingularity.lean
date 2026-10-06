-- Analysis/Conditioning/DistanceToSingularity.lean
--
-- Normwise distance-to-singularity results.

import NumStability.Analysis.MatrixNorms.Attainment

/-!
# Distance to singularity

Characterizes distance to singularity through inverse norms and explicit
rank-one perturbations in finite-dimensional complex spaces.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


set_option linter.unusedTactic false in
/-- Theorem 6.5 lower-bound foundation: if `A + Δ` is singular and `Ainv`
    is a left inverse of `A`, then any mixed subordinate bound `d` for `Δ`
    satisfies the reciprocal condition-number lower bound
    `(a * s)⁻¹ <= d / a`, where `a` is the norm value of `A` and `s` is an
    upper bound for `Ainv`. -/
theorem singular_perturbation_inv_condition_le_relative_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv Δ : ComplexVectorMap n n}
    {a s d : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a) (hs : 0 < s)
    (hAinv_left : ∀ x : CVec n, Ainv (A x) = x)
    (hAinv_bound : MixedSubordinateBound νβ να Ainv s)
    (hΔ_bound : MixedSubordinateBound να νβ Δ d)
    (hsing : IsSingularComplexVectorMap (complexVectorMapAdd A Δ)) :
    (a * s)⁻¹ ≤ d / a := by
  -- Preserve frozen auxiliary names across the semantic module split.
  run_tac do
    let ngen ← Lean.getDeclNGen
    Lean.setDeclNGen { ngen with idx := 2 }
  obtain ⟨x, hxne, hxsing⟩ := hsing
  have hxnorm_ne : να x ≠ 0 := by
    intro hxzero
    exact hxne ((hα.eq_zero_iff x).mp hxzero)
  have hxnorm_pos : 0 < να x := lt_of_le_of_ne (hα.nonneg x) (Ne.symm hxnorm_ne)
  have hA_eq_neg : A x = complexVecSMul (-1 : ℂ) (Δ x) := by
    ext i
    have hcoord := congrFun hxsing i
    simp [complexVectorMapAdd, complexVecAdd, complexVecSMul] at hcoord ⊢
    exact eq_neg_of_add_eq_zero_left hcoord
  have hx_eq : x = Ainv (complexVecSMul (-1 : ℂ) (Δ x)) := by
    calc
      x = Ainv (A x) := (hAinv_left x).symm
      _ = Ainv (complexVecSMul (-1 : ℂ) (Δ x)) := by rw [hA_eq_neg]
  have hnorm_le : να x ≤ (s * d) * να x := by
    calc
      να x = να (Ainv (complexVecSMul (-1 : ℂ) (Δ x))) := congrArg να hx_eq
      _ ≤ s * νβ (complexVecSMul (-1 : ℂ) (Δ x)) :=
        hAinv_bound (complexVecSMul (-1 : ℂ) (Δ x))
      _ = s * νβ (Δ x) := by
        rw [hβ.smul (-1 : ℂ) (Δ x)]
        norm_num
      _ ≤ s * (d * να x) :=
        mul_le_mul_of_nonneg_left (hΔ_bound x) (le_of_lt hs)
      _ = (s * d) * να x := by ring
  have hone_le : 1 ≤ s * d := by
    exact le_of_mul_le_mul_right (by simpa [one_mul] using hnorm_le) hxnorm_pos
  have haspos : 0 < a * s := mul_pos ha hs
  rw [inv_le_iff_one_le_mul₀ haspos]
  calc
    1 ≤ s * d := hone_le
    _ = (d / a) * (a * s) := by field_simp [ne_of_gt ha]

/-- Theorem 6.5 upper-bound foundation: from a positive mixed subordinate value
    `s` for a right inverse `Ainv`, construct a perturbation `Δ` with mixed
    subordinate value `s⁻¹` such that `A + Δ` is singular. -/
theorem exists_singular_perturbation_attaining_inverse_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hA_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) (hspos : 0 < s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ s⁻¹ ∧
          IsSingularComplexVectorMap (complexVectorMapAdd A Δ) := by
  obtain ⟨y, hy, hAinvy⟩ :=
    exists_unit_vector_attaining_mixedSubordinateNormValue hβ hα hAinv_lin hAinv hspos
  let x : CVec n := Ainv y
  let xunit : CVec n := complexVecSMul (((s⁻¹ : ℝ) : ℂ)) x
  have hsinv_pos : 0 < s⁻¹ := inv_pos.mpr hspos
  have hxunit : να xunit = 1 := by
    dsimp [xunit, x]
    rw [hα.smul, Complex.norm_of_nonneg (le_of_lt hsinv_pos), hAinvy]
    field_simp [ne_of_gt hspos]
  let negy : CVec n := complexVecSMul (-1 : ℂ) y
  have hnegy : νβ negy = 1 := by
    dsimp [negy]
    rw [hβ.smul, hy]
    norm_num
  obtain ⟨B, hBlin, hBval, hBxunit⟩ :=
    exists_rankOne_isMixedSubordinateNormValue_one hα hβ hxunit hnegy
  let Δ : ComplexVectorMap n n := complexVectorMapSMul (((s⁻¹ : ℝ) : ℂ)) B
  refine ⟨Δ, ?_, ?_, ?_⟩
  · exact complexVectorMapSMul_linear (((s⁻¹ : ℝ) : ℂ)) hBlin
  · have hscaled :=
      mixedSubordinateNormValue_smul_real_pos hβ hsinv_pos hBval
    simpa [Δ] using hscaled
  · refine ⟨x, ?_, ?_⟩
    · intro hxzero
      have hxnorm_zero : να x = 0 := (hα.eq_zero_iff x).mpr hxzero
      change να (Ainv y) = 0 at hxnorm_zero
      rw [hAinvy] at hxnorm_zero
      exact (ne_of_gt hspos) hxnorm_zero
    · have hΔx : Δ x = negy := by
        have hmap := hBlin.map_smul (((s⁻¹ : ℝ) : ℂ)) x
        change B (complexVecSMul (((s⁻¹ : ℝ) : ℂ)) x) =
          complexVecSMul (((s⁻¹ : ℝ) : ℂ)) (B x) at hmap
        change complexVecSMul (((s⁻¹ : ℝ) : ℂ)) (B x) = negy
        rw [← hmap]
        simpa [xunit] using hBxunit
      ext i
      simp [complexVectorMapAdd, complexVecAdd, hA_right y, x, hΔx, negy,
        complexVecSMul]

/-- Relative form of the attaining perturbation in the local Theorem 6.5 model:
    if `a > 0` is the mixed subordinate value of `A`, the constructed singular
    perturbation has relative size `(a * s)⁻¹`. -/
theorem exists_singular_perturbation_attaining_relative_inverse_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a)
    (hA_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) (hspos : 0 < s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ s⁻¹ ∧
          IsSingularComplexVectorMap (complexVectorMapAdd A Δ) ∧
            s⁻¹ / a = (a * s)⁻¹ := by
  obtain ⟨Δ, hΔlin, hΔval, hsing⟩ :=
    exists_singular_perturbation_attaining_inverse_bound hα hβ hA_right
      hAinv_lin hAinv hspos
  refine ⟨Δ, hΔlin, hΔval, hsing, ?_⟩
  field_simp [ne_of_gt ha, ne_of_gt hspos]

/-- Local predicate for the relative mixed distance from `A` to singularity.
    The value `a` records the mixed subordinate value of `A`; `ρ` is a least
    relative perturbation size, and the infimum is represented by an explicit
    attaining linear perturbation. -/
def IsMixedRelativeSingularDistanceValue
    {n : ℕ} (να νβ : CVec n → ℝ) (A : ComplexVectorMap n n)
    (a ρ : ℝ) : Prop :=
  IsMixedSubordinateNormValue να νβ A a ∧
    (∀ (Δ : ComplexVectorMap n n) (d : ℝ),
      IsComplexVectorMapLinear Δ →
        IsMixedSubordinateNormValue να νβ Δ d →
          IsSingularComplexVectorMap (complexVectorMapAdd A Δ) →
            ρ ≤ d / a) ∧
    ∃ Δ : ComplexVectorMap n n, ∃ d : ℝ,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ d ∧
          IsSingularComplexVectorMap (complexVectorMapAdd A Δ) ∧ d / a = ρ

/-- Candidate relative distances `||ΔA||_{α,β} / ||A||_{α,β}` for singular
    perturbations in the local mixed least-bound model. -/
def MixedRelativeSingularDistanceSet
    {n : ℕ} (να νβ : CVec n → ℝ) (A : ComplexVectorMap n n)
    (a : ℝ) : Set ℝ :=
  {ρ | ∃ Δ : ComplexVectorMap n n, ∃ d : ℝ,
    IsComplexVectorMapLinear Δ ∧
      IsMixedSubordinateNormValue να νβ Δ d ∧
        IsSingularComplexVectorMap (complexVectorMapAdd A Δ) ∧ ρ = d / a}

/-- Source-facing local `min` form of the relative distance to singularity. -/
def IsMinimumMixedRelativeSingularDistance
    {n : ℕ} (να νβ : CVec n → ℝ) (A : ComplexVectorMap n n)
    (a ρ : ℝ) : Prop :=
  ρ ∈ MixedRelativeSingularDistanceSet να νβ A a ∧
    ∀ r : ℝ, r ∈ MixedRelativeSingularDistanceSet να νβ A a → ρ ≤ r

/-- Product-form mixed condition number value in the local least-bound model.
    This records the right-hand side of Higham equation (6.8); it is not yet
    the perturbation-limit definition from the first half of Theorem 6.4. -/
def IsMixedConditionNumberProductValue
    {n : ℕ} (να νβ : CVec n → ℝ) (A Ainv : ComplexVectorMap n n)
    (κ : ℝ) : Prop :=
  ∃ a s : ℝ,
    IsMixedSubordinateNormValue να νβ A a ∧
      IsMixedSubordinateNormValue νβ να Ainv s ∧ κ = a * s

theorem mixedConditionNumberProductValue_norm_mul_inverse_norm
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {a s : ℝ} (hA : IsMixedSubordinateNormValue να νβ A a)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) :
    IsMixedConditionNumberProductValue να νβ A Ainv (a * s) := by
  exact ⟨a, s, hA, hAinv, rfl⟩

/-- Problem 6.6, local quotient form: the product condition number can be
    written as the maximum gain of `A` divided by the minimum gain of `A`. -/
theorem mixedConditionNumberProductValue_eq_max_div_min_image_ratio
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hn : 0 < n) (hAlin : IsComplexVectorMapLinear A)
    (hAinv_left : ∀ x : CVec n, Ainv (A x) = x)
    (hAinv_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) (hspos : 0 < s) :
    ∃ μ : ℝ,
      IsMaxMixedNonzeroImageRatioValue να νβ A a ∧
        IsMinMixedNonzeroImageRatioValue να νβ A μ ∧
          IsMixedConditionNumberProductValue να νβ A Ainv (a / μ) := by
  refine ⟨s⁻¹, ?_, ?_, ?_⟩
  · exact isMaxMixedNonzeroImageRatioValue_of_isMaxMixedUnitImageNormValue
      hα hβ hAlin
      (isMaxMixedUnitImageNormValue_of_mixedSubordinateNormValue_nonempty
        hα hβ hn hAlin hA)
  · exact isMinMixedNonzeroImageRatioValue_inv_of_inverseNormValue
      hα hβ hAinv_left hAinv_right hAinv_lin hAinv hspos
  · have hquot : a / s⁻¹ = a * s := by
      field_simp [ne_of_gt hspos]
    rw [hquot]
    exact mixedConditionNumberProductValue_norm_mul_inverse_norm hA hAinv

/-- Concrete-matrix wrapper for Problem 6.6 using the repository's two-sided
    inverse predicate. -/
theorem complexMatrix_conditionNumberProductValue_eq_max_div_min_image_ratio
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : CMatrix n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hn : 0 < n) (hAinv_inv : IsComplexMatrixInverse A Ainv)
    (hA : IsMixedSubordinateMatrixNormValue να νβ A a)
    (hAinv : IsMixedSubordinateMatrixNormValue νβ να Ainv s)
    (hspos : 0 < s) :
    ∃ μ : ℝ,
      IsMaxMixedSubordinateMatrixRatioValue να νβ A a ∧
        IsMinMixedSubordinateMatrixRatioValue να νβ A μ ∧
          IsMixedConditionNumberProductValue να νβ
            (complexMatrixVecMul A) (complexMatrixVecMul Ainv) (a / μ) := by
  simpa [IsMaxMixedSubordinateMatrixRatioValue,
    IsMinMixedSubordinateMatrixRatioValue, IsMixedSubordinateMatrixNormValue] using
    (mixedConditionNumberProductValue_eq_max_div_min_image_ratio
      (A := complexMatrixVecMul A) (Ainv := complexMatrixVecMul Ainv)
      hα hβ hn (complexMatrixVecMul_linear A)
      hAinv_inv.1 hAinv_inv.2 (complexMatrixVecMul_linear Ainv)
      hA hAinv hspos)

theorem isMinimumMixedRelativeSingularDistance_of_value
    {n : ℕ} {να νβ : CVec n → ℝ} {A : ComplexVectorMap n n}
    {a ρ : ℝ} (hρ : IsMixedRelativeSingularDistanceValue να νβ A a ρ) :
    IsMinimumMixedRelativeSingularDistance να νβ A a ρ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨Δ, d, hΔlin, hΔval, hsing, hrel⟩ := hρ.2.2
    exact ⟨Δ, d, hΔlin, hΔval, hsing, hrel.symm⟩
  · intro r hr
    obtain ⟨Δ, d, hΔlin, hΔval, hsing, hr⟩ := hr
    rw [hr]
    exact hρ.2.1 Δ d hΔlin hΔval hsing

/-- Local Theorem 6.5 model: for an invertible source-facing map `A`, if
    `a = ||A||_{α,β}` and `s = ||A⁻¹||_{β,α}` in the local least-bound model,
    then the attained relative distance to singularity is `(a*s)⁻¹`. -/
theorem mixedRelativeSingularDistanceValue_eq_inv_norm_mul_inverse_norm
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a) (hs : 0 < s)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hAinv_left : ∀ x : CVec n, Ainv (A x) = x)
    (hAinv_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) :
    IsMixedRelativeSingularDistanceValue να νβ A a ((a * s)⁻¹) := by
  refine ⟨hA, ?_, ?_⟩
  · intro Δ d _hΔlin hΔval hsing
    exact singular_perturbation_inv_condition_le_relative_bound hα hβ ha hs
      hAinv_left hAinv.1 hΔval.1 hsing
  · obtain ⟨Δ, hΔlin, hΔval, hsing, hrel⟩ :=
      exists_singular_perturbation_attaining_relative_inverse_bound hα hβ ha
        hAinv_right hAinv_lin hAinv hs
    exact ⟨Δ, s⁻¹, hΔlin, hΔval, hsing, hrel⟩

/-- Local source-facing `min` version of Theorem 6.5: the minimum relative
    singular perturbation size is `(||A||_{α,β} ||A⁻¹||_{β,α})⁻¹` in the
    local least-bound model. -/
theorem mixedRelativeSingularDistance_min_eq_inv_norm_mul_inverse_norm
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a) (hs : 0 < s)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hAinv_left : ∀ x : CVec n, Ainv (A x) = x)
    (hAinv_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) :
    IsMinimumMixedRelativeSingularDistance να νβ A a ((a * s)⁻¹) := by
  exact isMinimumMixedRelativeSingularDistance_of_value
    (mixedRelativeSingularDistanceValue_eq_inv_norm_mul_inverse_norm hα hβ
      ha hs hA hAinv_left hAinv_right hAinv_lin hAinv)

/-- Local source-facing reciprocal condition-number form of Theorem 6.5:
    for the product-form condition-number value `κ = ||A||_{α,β} ||A⁻¹||_{β,α}`,
    the relative distance-to-singularity minimum is `κ⁻¹`. -/
theorem mixedRelativeSingularDistance_min_eq_inv_conditionNumberProduct
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a) (hs : 0 < s)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hAinv_left : ∀ x : CVec n, Ainv (A x) = x)
    (hAinv_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue να νβ A Ainv κ ∧
        IsMinimumMixedRelativeSingularDistance να νβ A a κ⁻¹ := by
  refine ⟨a * s, mixedConditionNumberProductValue_norm_mul_inverse_norm hA hAinv, ?_⟩
  exact mixedRelativeSingularDistance_min_eq_inv_norm_mul_inverse_norm hα hβ
    ha hs hA hAinv_left hAinv_right hAinv_lin hAinv

/-- Concrete-matrix version of Theorem 6.5: for a two-sided inverse `Ainv`,
    the relative distance from `A` to singularity is
    `(||A||_{α,β} * ||Ainv||_{β,α})⁻¹` in the local mixed least-bound model. -/
theorem complexMatrix_relativeSingularDistance_min_eq_inv_norm_mul_inverse_norm
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : CMatrix n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a) (hs : 0 < s)
    (hAinv_inv : IsComplexMatrixInverse A Ainv)
    (hA : IsMixedSubordinateMatrixNormValue να νβ A a)
    (hAinv : IsMixedSubordinateMatrixNormValue νβ να Ainv s) :
    IsMinimumMixedRelativeSingularDistance να νβ (complexMatrixVecMul A) a
      ((a * s)⁻¹) := by
  simpa [IsMixedSubordinateMatrixNormValue] using
    (mixedRelativeSingularDistance_min_eq_inv_norm_mul_inverse_norm
      (A := complexMatrixVecMul A) (Ainv := complexMatrixVecMul Ainv)
      hα hβ ha hs hA hAinv_inv.1 hAinv_inv.2
      (complexMatrixVecMul_linear Ainv) hAinv)

/-- Concrete-matrix reciprocal condition-number form of Theorem 6.5.  This is
    the source-facing matrix wrapper around the local Gastinel-Kahan theorem. -/
theorem complexMatrix_relativeSingularDistance_min_eq_inv_conditionNumberProduct
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : CMatrix n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (ha : 0 < a) (hs : 0 < s)
    (hAinv_inv : IsComplexMatrixInverse A Ainv)
    (hA : IsMixedSubordinateMatrixNormValue να νβ A a)
    (hAinv : IsMixedSubordinateMatrixNormValue νβ να Ainv s) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue να νβ
        (complexMatrixVecMul A) (complexMatrixVecMul Ainv) κ ∧
        IsMinimumMixedRelativeSingularDistance να νβ
          (complexMatrixVecMul A) a κ⁻¹ := by
  refine ⟨a * s, ?_, ?_⟩
  · exact mixedConditionNumberProductValue_norm_mul_inverse_norm hA hAinv
  · exact complexMatrix_relativeSingularDistance_min_eq_inv_norm_mul_inverse_norm
      hα hβ ha hs hAinv_inv hA hAinv

/-- Equation (6.9), upper-bound skeleton: if `S` has mixed subordinate value
    `s` as a `β -> α` map and `Δ` has `α -> β` bound `1`, then
    `S ∘ Δ ∘ S` has `β -> α` bound `s^2`. -/
theorem mixedSubordinate_inverseSandwich_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {S Δ : ComplexVectorMap n n} {s : ℝ}
    (hs0 : 0 ≤ s)
    (hS : IsMixedSubordinateNormValue νβ να S s)
    (hΔ : MixedSubordinateBound να νβ Δ 1) :
    MixedSubordinateBound νβ να
      (complexVectorMapComp S (complexVectorMapComp Δ S)) (s ^ 2) := by
  have hDS : MixedSubordinateBound νβ νβ (complexVectorMapComp Δ S) (1 * s) :=
    mixedSubordinateBound_comp (by norm_num) hΔ hS.1
  have hSDS : MixedSubordinateBound νβ να
      (complexVectorMapComp S (complexVectorMapComp Δ S)) (s * (1 * s)) :=
    mixedSubordinateBound_comp hs0 hS.1 hDS
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hSDS

/-- Equation (6.9), upper-bound value form for the local least-bound predicate. -/
theorem mixedSubordinate_inverseSandwich_value_le
    {n : ℕ} {να νβ : CVec n → ℝ} {S Δ : ComplexVectorMap n n} {s c : ℝ}
    (hs0 : 0 ≤ s)
    (hS : IsMixedSubordinateNormValue νβ να S s)
    (hΔ : MixedSubordinateBound να νβ Δ 1)
    (hcomp : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp Δ S)) c) :
    c ≤ s ^ 2 :=
  hcomp.2 (s ^ 2) (mixedSubordinate_inverseSandwich_bound hs0 hS hΔ)

/-- Equation (6.9), lower-bound construction under an explicit norm-attainment
    witness for `S`: if `νβ y = 1` and `να (S y) = s`, then some unit mixed
    perturbation `Δ` makes the sandwich attain `s^2` at `y`. -/
theorem exists_inverseSandwich_attains_square
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S) (hspos : 0 < s)
    {y : CVec n} (hy : νβ y = 1) (hSy : να (S y) = s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ 1 ∧
          να (complexVectorMapComp S (complexVectorMapComp Δ S) y) = s ^ 2 := by
  let x : CVec n := complexVecSMul (((s⁻¹ : ℝ) : ℂ)) (S y)
  have hs_nonneg : 0 ≤ s := le_of_lt hspos
  have hsinv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs_nonneg
  have hx : να x = 1 := by
    dsimp [x]
    rw [hα.smul, Complex.norm_of_nonneg hsinv_nonneg, hSy]
    field_simp [ne_of_gt hspos]
  have hsinv_mul : (s : ℂ) * (((s⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul]
    norm_num [mul_inv_cancel₀ (ne_of_gt hspos)]
  have hSy_eq : S y = complexVecSMul (s : ℂ) x := by
    ext i
    dsimp [x, complexVecSMul]
    rw [← mul_assoc, hsinv_mul, one_mul]
  obtain ⟨Δ, hΔlin, hΔval, hΔx⟩ :=
    exists_rankOne_isMixedSubordinateNormValue_one hα hβ hx hy
  refine ⟨Δ, hΔlin, hΔval, ?_⟩
  have hΔSy : Δ (S y) = complexVecSMul (s : ℂ) y := by
    rw [hSy_eq, hΔlin.map_smul, hΔx]
  have hSand :
      complexVectorMapComp S (complexVectorMapComp Δ S) y =
        complexVecSMul (s : ℂ) (S y) := by
    simp [complexVectorMapComp, hΔSy, hSlin.map_smul]
  calc
    να (complexVectorMapComp S (complexVectorMapComp Δ S) y)
        = να (complexVecSMul (s : ℂ) (S y)) := by rw [hSand]
    _ = ‖(s : ℂ)‖ * να (S y) := hα.smul (s : ℂ) (S y)
    _ = s * s := by rw [Complex.norm_of_nonneg hs_nonneg, hSy]
    _ = s ^ 2 := by ring

/-- Equation (6.9), lower-bound value form under explicit norm attainment. -/
theorem exists_inverseSandwich_value_ge_square
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S) (hspos : 0 < s)
    {y : CVec n} (hy : νβ y = 1) (hSy : να (S y) = s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ 1 ∧
          ∀ c : ℝ,
            IsMixedSubordinateNormValue νβ να
              (complexVectorMapComp S (complexVectorMapComp Δ S)) c →
              s ^ 2 ≤ c := by
  obtain ⟨Δ, hΔlin, hΔval, hattain⟩ :=
    exists_inverseSandwich_attains_square hα hβ hSlin hspos hy hSy
  refine ⟨Δ, hΔlin, hΔval, ?_⟩
  intro c hcomp
  have h := hcomp.1 y
  rw [hattain, hy] at h
  simpa using h

/-- Equation (6.9), packaged equality route under explicit norm attainment:
    some unit mixed perturbation `Δ` makes the sandwich norm value exactly
    `s^2`, and all unit mixed perturbations are bounded above by `s^2`. -/
theorem exists_inverseSandwich_value_eq_square_of_attained
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS : IsMixedSubordinateNormValue νβ να S s) (hspos : 0 < s)
    {y : CVec n} (hy : νβ y = 1) (hSy : να (S y) = s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ 1 ∧
          ∀ c : ℝ,
            IsMixedSubordinateNormValue νβ να
              (complexVectorMapComp S (complexVectorMapComp Δ S)) c →
              c = s ^ 2 := by
  obtain ⟨Δ, hΔlin, hΔval, hlower⟩ :=
    exists_inverseSandwich_value_ge_square hα hβ hSlin hspos hy hSy
  refine ⟨Δ, hΔlin, hΔval, ?_⟩
  intro c hcomp
  apply le_antisymm
  · exact mixedSubordinate_inverseSandwich_value_le (le_of_lt hspos) hS hΔval.1 hcomp
  · exact hlower c hcomp

/-- Equation (6.9), packaged equality route with the finite-dimensional
    norm-attainment step discharged from the positive mixed subordinate value
    of `S`. -/
theorem exists_inverseSandwich_value_eq_square
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS : IsMixedSubordinateNormValue νβ να S s) (hspos : 0 < s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ 1 ∧
          ∀ c : ℝ,
            IsMixedSubordinateNormValue νβ να
              (complexVectorMapComp S (complexVectorMapComp Δ S)) c →
              c = s ^ 2 := by
  obtain ⟨y, hy, hSy⟩ :=
    exists_unit_vector_attaining_mixedSubordinateNormValue hβ hα hSlin hS hspos
  exact exists_inverseSandwich_value_eq_square_of_attained
    hα hβ hSlin hS hspos hy hSy

/-- Equation (6.9), existence form for the local least-bound predicate:
    some unit mixed perturbation `Δ` makes the composed sandwich
    `S ∘ Δ ∘ S` have mixed subordinate norm value exactly `s^2`. -/
theorem exists_inverseSandwich_normValue_eq_square
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s : ℝ}
    (hn : 0 < n) (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS : IsMixedSubordinateNormValue νβ να S s) (hspos : 0 < s) :
    ∃ Δ : ComplexVectorMap n n,
      IsComplexVectorMapLinear Δ ∧
        IsMixedSubordinateNormValue να νβ Δ 1 ∧
          IsMixedSubordinateNormValue νβ να
            (complexVectorMapComp S (complexVectorMapComp Δ S)) (s ^ 2) := by
  obtain ⟨Δ, hΔlin, hΔval, heq⟩ :=
    exists_inverseSandwich_value_eq_square hα hβ hSlin hS hspos
  let T : ComplexVectorMap n n :=
    complexVectorMapComp S (complexVectorMapComp Δ S)
  have hTlin : IsComplexVectorMapLinear T :=
    complexVectorMapComp_linear hSlin (complexVectorMapComp_linear hΔlin hSlin)
  have hTbound : MixedSubordinateBound νβ να T (s ^ 2) :=
    mixedSubordinate_inverseSandwich_bound (le_of_lt hspos) hS hΔval.1
  obtain ⟨c, hc⟩ :=
    exists_mixedSubordinateNormValue_of_bound_nonempty
      (n := n) (m := n) (να := νβ) (νβ := να) hn hβ hα hTlin hTbound
  refine ⟨Δ, hΔlin, hΔval, ?_⟩
  simpa [T, heq c hc] using hc

/-- Scaled form of equation (6.9), tailored for the lower squeeze in the
    inverse perturbation proof: for every positive perturbation size `d`, some
    `α -> β` perturbation has value `d` and makes `S ∘ D ∘ S` have value
    `s^2 * d`. -/
theorem exists_inverseSandwich_scaled_normValue_eq_square_mul
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s d : ℝ}
    (hn : 0 < n) (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS : IsMixedSubordinateNormValue νβ να S s)
    (hspos : 0 < s) (hdpos : 0 < d) :
    ∃ D : ComplexVectorMap n n,
      IsComplexVectorMapLinear D ∧
        IsMixedSubordinateNormValue να νβ D d ∧
          IsMixedSubordinateNormValue νβ να
            (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d) := by
  obtain ⟨Δ, hΔlin, hΔval, hSand⟩ :=
    exists_inverseSandwich_normValue_eq_square hn hα hβ hSlin hS hspos
  let D : ComplexVectorMap n n := complexVectorMapSMul (d : ℂ) Δ
  have hDlin : IsComplexVectorMapLinear D :=
    complexVectorMapSMul_linear (d : ℂ) hΔlin
  have hDval : IsMixedSubordinateNormValue να νβ D d := by
    have hraw := mixedSubordinateNormValue_smul_real_pos hβ hdpos hΔval
    simpa [D] using hraw
  have hmap :
      complexVectorMapComp S (complexVectorMapComp D S) =
        complexVectorMapSMul (d : ℂ)
          (complexVectorMapComp S (complexVectorMapComp Δ S)) := by
    funext x
    simp [D, complexVectorMapComp, complexVectorMapSMul, hSlin.map_smul]
  have hSandScaled :
      IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp D S)) (d * s ^ 2) := by
    have hraw := mixedSubordinateNormValue_smul_real_pos hα hdpos hSand
    simpa [hmap] using hraw
  refine ⟨D, hDlin, hDval, ?_⟩
  simpa [mul_comm, mul_left_comm, mul_assoc] using hSandScaled

/-- Indexed form of the scaled inverse-sandwich witness.  If the perturbation
    scales `d_i` are eventually positive, then there is a chosen perturbation
    family `D_i` such that, eventually, `D_i` is linear, has mixed subordinate
    norm value `d_i`, and the linearized sandwich `S ∘ D_i ∘ S` has value
    `s^2*d_i`.

    This packages the source-facing lower-witness family required by the
    radius-limit squeeze; it does not yet construct perturbed right inverses for
    `A + D_i`. -/
theorem exists_inverseSandwich_scaled_normValue_family_eq_square_mul
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s : ℝ}
    {d : ι → ℝ}
    (hn : 0 < n) (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS : IsMixedSubordinateNormValue νβ να S s)
    (hspos : 0 < s)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l) :
    ∃ D : ι → ComplexVectorMap n n,
      Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l ∧
        Filter.Eventually
          (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l ∧
          Filter.Eventually
            (fun i => IsMixedSubordinateNormValue νβ να
              (complexVectorMapComp S (complexVectorMapComp (D i) S))
              (s ^ 2 * d i)) l := by
  let D : ι → ComplexVectorMap n n := fun i =>
    if hi : 0 < d i then
      Classical.choose
        (exists_inverseSandwich_scaled_normValue_eq_square_mul
          hn hα hβ hSlin hS hspos hi)
    else
      fun _ => 0
  refine ⟨D, ?_, ?_, ?_⟩
  · filter_upwards [hdpos] with i hi
    have hspec :=
      Classical.choose_spec
        (exists_inverseSandwich_scaled_normValue_eq_square_mul
          hn hα hβ hSlin hS hspos hi)
    simpa [D, hi] using hspec.1
  · filter_upwards [hdpos] with i hi
    have hspec :=
      Classical.choose_spec
        (exists_inverseSandwich_scaled_normValue_eq_square_mul
          hn hα hβ hSlin hS hspos hi)
    simpa [D, hi] using hspec.2.1
  · filter_upwards [hdpos] with i hi
    have hspec :=
      Classical.choose_spec
        (exists_inverseSandwich_scaled_normValue_eq_square_mul
          hn hα hβ hSlin hS hspos hi)
    simpa [D, hi] using hspec.2.2

/-- Candidate unit-image values for the inverse-map derivative sandwich
    `S ∘ Δ ∘ S`, where `Δ` has mixed subordinate value `1` and the source
    vector has `νβ`-norm `1`.  This is the local max-form bridge for the
    sharp linearized inverse-condition derivative in Theorem 6.4. -/
def MixedInverseSandwichUnitImageSet
    {n : ℕ} (να νβ : CVec n → ℝ) (S : ComplexVectorMap n n) : Set ℝ :=
  {r | ∃ Δ : ComplexVectorMap n n, ∃ y : CVec n,
    IsComplexVectorMapLinear Δ ∧
      IsMixedSubordinateNormValue να νβ Δ 1 ∧
        νβ y = 1 ∧
          r = να (complexVectorMapComp S (complexVectorMapComp Δ S) y)}

/-- Source-facing maximum predicate for the unit-image values of
    `S ∘ Δ ∘ S`. -/
def IsMaxMixedInverseSandwichUnitImageValue
    {n : ℕ} (να νβ : CVec n → ℝ) (S : ComplexVectorMap n n)
    (c : ℝ) : Prop :=
  c ∈ MixedInverseSandwichUnitImageSet να νβ S ∧
    ∀ r : ℝ, r ∈ MixedInverseSandwichUnitImageSet να νβ S → r ≤ c

/-- Equation (6.9), max-form derivative bridge: among unit mixed
    perturbations `Δ` and unit source vectors, `S ∘ Δ ∘ S` has maximum output
    value `s^2`. -/
theorem mixedInverseSandwichUnitImageValue_max_eq_square
    {n : ℕ} {να νβ : CVec n → ℝ} {S : ComplexVectorMap n n} {s : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS : IsMixedSubordinateNormValue νβ να S s) (hspos : 0 < s) :
    IsMaxMixedInverseSandwichUnitImageValue να νβ S (s ^ 2) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy, hSy⟩ :=
      exists_unit_vector_attaining_mixedSubordinateNormValue hβ hα hSlin hS hspos
    obtain ⟨Δ, hΔlin, hΔval, hattain⟩ :=
      exists_inverseSandwich_attains_square hα hβ hSlin hspos hy hSy
    exact ⟨Δ, y, hΔlin, hΔval, hy, hattain.symm⟩
  · intro r hr
    obtain ⟨Δ, y, _hΔlin, hΔval, hy, hr_eq⟩ := hr
    rw [hr_eq]
    have hbound :
        MixedSubordinateBound νβ να
          (complexVectorMapComp S (complexVectorMapComp Δ S)) (s ^ 2) :=
      mixedSubordinate_inverseSandwich_bound (le_of_lt hspos) hS hΔval.1
    have h := hbound y
    rw [hy] at h
    simpa using h

/-- Local linearized inverse-condition value: the max derivative factor is
    `s^2`, and relative scaling by `||A|| / ||S||` gives
    `(a / s) * s^2`.  This deliberately records only the linearized piece of
    Theorem 6.4, not the remaining nonlinear perturbation-limit `sSup`. -/
def IsMixedInverseLinearizedConditionValue
    {n : ℕ} (να νβ : CVec n → ℝ) (A S : ComplexVectorMap n n)
    (a s κ : ℝ) : Prop :=
  IsMixedSubordinateNormValue να νβ A a ∧
    IsMixedSubordinateNormValue νβ να S s ∧
      IsMaxMixedInverseSandwichUnitImageValue να νβ S (s ^ 2) ∧
        κ = (a / s) * s ^ 2

/-- The linearized inverse-condition value simplifies to the product-form
    condition number `||A||_{α,β} * ||S||_{β,α}`. -/
theorem mixedInverseLinearizedConditionValue_eq_norm_mul_inverse_norm
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hS : IsMixedSubordinateNormValue νβ να S s) (hspos : 0 < s) :
    IsMixedInverseLinearizedConditionValue να νβ A S a s (a * s) := by
  refine ⟨hA, hS,
    mixedInverseSandwichUnitImageValue_max_eq_square hα hβ hSlin hS hspos, ?_⟩
  field_simp [ne_of_gt hspos]

/-- Product-form packaging of the local linearized inverse-condition value,
    reusing the Chapter 6 condition-number product predicate. -/
theorem mixedInverseLinearizedConditionValue_eq_conditionNumberProduct
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s : ℝ} (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hS : IsMixedSubordinateNormValue νβ να S s) (hspos : 0 < s) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue να νβ A S κ ∧
        IsMixedInverseLinearizedConditionValue να νβ A S a s κ := by
  exact ⟨a * s, mixedConditionNumberProductValue_norm_mul_inverse_norm hA hS,
    mixedInverseLinearizedConditionValue_eq_norm_mul_inverse_norm
      hα hβ hSlin hA hS hspos⟩
end NumStability
