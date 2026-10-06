-- Analysis/OperatorNorms/Basic.lean
--
-- Abstract subordinate norms for finite complex-linear operators.

import NumStability.Analysis.LinearOperators.Basic

/-!
# Mixed subordinate operator norms

Defines mixed subordinate operator-norm values and bounds, together with the
algebraic comparison lemmas used by concrete matrix norms.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Predicate form of a mixed subordinate norm upper bound:
    `νβ (T x) <= c * να x` for all source vectors. -/
def MixedSubordinateBound {n m : ℕ} (να : CVec n → ℝ) (νβ : CVec m → ℝ)
    (T : ComplexVectorMap n m) (c : ℝ) : Prop :=
  ∀ x : CVec n, νβ (T x) ≤ c * να x

/-- A value of the mixed subordinate norm, represented as the least admissible
    bound.  This avoids committing to the Chapter 6 `max`/`sup` matrix-norm
    machinery before that source-facing API is fixed. -/
def IsMixedSubordinateNormValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (T : ComplexVectorMap n m) (c : ℝ) : Prop :=
  MixedSubordinateBound να νβ T c ∧
    ∀ d : ℝ, MixedSubordinateBound να νβ T d → c ≤ d

/-- A mixed subordinate upper bound is nonnegative when the source norm has a
    unit vector.  This map-level form is used by the perturbation-limit
    condition-number layer, where the perturbed inverse is not always packaged
    as a concrete matrix map. -/
lemma mixedSubordinateBound_nonneg_of_nonempty
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hn : 0 < n) (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {T : ComplexVectorMap n m} {c : ℝ}
    (hT : MixedSubordinateBound να νβ T c) :
    0 ≤ c := by
  obtain ⟨u, hu⟩ := exists_unit_complexVectorNorm hα hn
  have h := hT u
  rw [hu, mul_one] at h
  exact (hβ.nonneg (T u)).trans h

/-- A local mixed subordinate norm value is nonnegative for nonempty source
    dimension. -/
lemma mixedSubordinateNormValue_nonneg_of_nonempty
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hn : 0 < n) (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {T : ComplexVectorMap n m} {c : ℝ}
    (hT : IsMixedSubordinateNormValue να νβ T c) :
    0 ≤ c :=
  mixedSubordinateBound_nonneg_of_nonempty hn hα hβ hT.1

/-- Source-facing eigenvalue-modulus set for a square source map.
    This is the local carrier for the spectral radius in Higham Problem 6.7:
    every member is `|λ|` for a nonzero eigenvector. -/
def ComplexVectorMapEigenvalueModulusSet {n : ℕ}
    (T : ComplexVectorMap n n) : Set ℝ :=
  {r | ∃ (lam : ℂ) (x : CVec n),
    x ≠ 0 ∧ T x = complexVecSMul lam x ∧ r = ‖lam‖}

/-- Predicate form of a maximum spectral modulus for a square source map. -/
def IsMaxComplexVectorMapEigenvalueModulus {n : ℕ}
    (T : ComplexVectorMap n n) (ρ : ℝ) : Prop :=
  ρ ∈ ComplexVectorMapEigenvalueModulusSet T ∧
    ∀ r : ℝ, r ∈ ComplexVectorMapEigenvalueModulusSet T → r ≤ ρ

/-- Higham Problem 6.7, map-level form: every eigenvalue modulus is bounded by
    any local mixed subordinate norm value built from the same vector norm on
    source and target. -/
theorem eigenvalueModulus_le_mixedSubordinateNormValue
    {n : ℕ} {ν : CVec n → ℝ} {T : ComplexVectorMap n n} {c r : ℝ}
    (hν : IsComplexVectorNorm ν)
    (hT : IsMixedSubordinateNormValue ν ν T c)
    (hr : r ∈ ComplexVectorMapEigenvalueModulusSet T) :
    r ≤ c := by
  rcases hr with ⟨lam, x, hxne, hTx, rfl⟩
  have hxnorm_ne : ν x ≠ 0 := by
    intro hxzero
    exact hxne ((hν.eq_zero_iff x).mp hxzero)
  have hxnorm_pos : 0 < ν x :=
    lt_of_le_of_ne (hν.nonneg x) (Ne.symm hxnorm_ne)
  have hbound := hT.1 x
  rw [hTx, hν.smul] at hbound
  nlinarith

/-- Higham Problem 6.7, maximum-modulus form: a locally represented spectral
    radius is bounded by any consistent/subordinate norm value. -/
theorem maxEigenvalueModulus_le_mixedSubordinateNormValue
    {n : ℕ} {ν : CVec n → ℝ} {T : ComplexVectorMap n n} {c ρ : ℝ}
    (hν : IsComplexVectorNorm ν)
    (hT : IsMixedSubordinateNormValue ν ν T c)
    (hρ : IsMaxComplexVectorMapEigenvalueModulus T ρ) :
    ρ ≤ c :=
  eigenvalueModulus_le_mixedSubordinateNormValue hν hT hρ.1

/-- If a finite-dimensional source-facing linear map has any mixed subordinate
    upper bound, then it has a local least mixed subordinate norm value.  This
    map-level wrapper is the dependency needed when the Chapter 6 perturbation
    map is assembled directly as a composition rather than as a concrete
    matrix-vector multiplication. -/
theorem exists_mixedSubordinateNormValue_of_bound_nonempty
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hn : 0 < n) (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {T : ComplexVectorMap n m} (hTlin : IsComplexVectorMapLinear T) {C : ℝ}
    (hbound : MixedSubordinateBound να νβ T C) :
    ∃ c : ℝ, IsMixedSubordinateNormValue να νβ T c := by
  let instSrcNAG : NormedAddCommGroup (NormedCVec n να) :=
    NormedCVec.normedAddCommGroup hα
  letI : NormedAddCommGroup (NormedCVec n να) := instSrcNAG
  let instSrcModule : Module ℂ (NormedCVec n να) :=
    (NormedCVec.equiv n να).module ℂ
  letI : Module ℂ (NormedCVec n να) := instSrcModule
  let instSrcNS : NormedSpace ℂ (NormedCVec n να) :=
    NormedSpace.ofCore (𝕜 := ℂ) (NormedCVec.normedSpaceCore hα)
  letI : NormedSpace ℂ (NormedCVec n να) := instSrcNS
  let instTgtNAG : NormedAddCommGroup (NormedCVec m νβ) :=
    NormedCVec.normedAddCommGroup hβ
  letI : NormedAddCommGroup (NormedCVec m νβ) := instTgtNAG
  let instTgtModule : Module ℂ (NormedCVec m νβ) :=
    (NormedCVec.equiv m νβ).module ℂ
  letI : Module ℂ (NormedCVec m νβ) := instTgtModule
  let instTgtNS : NormedSpace ℂ (NormedCVec m νβ) :=
    NormedSpace.ofCore (𝕜 := ℂ) (NormedCVec.normedSpaceCore hβ)
  letI : NormedSpace ℂ (NormedCVec m νβ) := instTgtNS
  let instSrcFin : FiniteDimensional ℂ (NormedCVec n να) := by
    let e : CVec n ≃ₗ[ℂ] NormedCVec n να :=
      { toFun := fun x => ⟨x⟩
        invFun := NormedCVec.val
        left_inv := by intro x; rfl
        right_inv := by intro x; cases x; rfl
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
    exact LinearEquiv.finiteDimensional e
  letI : FiniteDimensional ℂ (NormedCVec n να) := instSrcFin
  let L : NormedCVec n να →ₗ[ℂ] NormedCVec m νβ :=
    { toFun := fun x => ⟨T x.val⟩
      map_add' := by
        intro x y
        apply NormedCVec.ext
        have h := hTlin.map_add x.val y.val
        simpa [complexVecAdd] using h
      map_smul' := by
        intro a x
        apply NormedCVec.ext
        have h := hTlin.map_smul a x.val
        simpa [complexVecSMul] using h }
  have hLbound : ∀ x : NormedCVec n να, ‖L x‖ ≤ C * ‖x‖ := by
    intro x
    simpa [L, NormedCVec.norm_eq] using hbound x.val
  let f : NormedCVec n να →L[ℂ] NormedCVec m νβ :=
    L.mkContinuous C hLbound
  refine ⟨‖f‖, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x
    have h := f.le_opNorm (⟨x⟩ : NormedCVec n να)
    simpa [f, L, NormedCVec.norm_eq] using h
  · intro d hd
    have hd_nonneg : 0 ≤ d := by
      obtain ⟨u, hu⟩ := exists_unit_complexVectorNorm hα hn
      have hu_pos : 0 < να u := by
        rw [hu]
        norm_num
      have hdu : νβ (T u) ≤ d * να u := hd u
      have hprod_nonneg : 0 ≤ d * να u :=
        (hβ.nonneg (T u)).trans hdu
      have hprod_nonneg' : 0 ≤ να u * d := by
        simpa [mul_comm] using hprod_nonneg
      exact nonneg_of_mul_nonneg_right hprod_nonneg' hu_pos
    apply ContinuousLinearMap.opNorm_le_bound f hd_nonneg
    intro x
    simpa [f, L, NormedCVec.norm_eq] using hd x.val

/-- Triangle inequality for local mixed subordinate upper bounds. This is a
    reusable algebraic ingredient for perturbation remainders such as
    `(A + Δ)⁻¹ - A⁻¹ + A⁻¹ Δ A⁻¹`. -/
theorem mixedSubordinateBound_add {n m : ℕ}
    {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ)
    {A B : ComplexVectorMap n m} {a b : ℝ}
    (hA : MixedSubordinateBound να νβ A a)
    (hB : MixedSubordinateBound να νβ B b) :
    MixedSubordinateBound να νβ (complexVectorMapAdd A B) (a + b) := by
  intro x
  calc
    νβ (complexVectorMapAdd A B x) ≤ νβ (A x) + νβ (B x) := by
      simpa [complexVectorMapAdd] using hβ.add_le (A x) (B x)
    _ ≤ a * να x + b * να x := add_le_add (hA x) (hB x)
    _ = (a + b) * να x := by ring

/-- Complex scalar multiplication of a local mixed subordinate upper bound. -/
theorem mixedSubordinateBound_smul {n m : ℕ}
    {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) (z : ℂ)
    {A : ComplexVectorMap n m} {a : ℝ}
    (hA : MixedSubordinateBound να νβ A a) :
    MixedSubordinateBound να νβ (complexVectorMapSMul z A) (‖z‖ * a) := by
  intro x
  calc
    νβ (complexVectorMapSMul z A x) = ‖z‖ * νβ (A x) := by
      simp [complexVectorMapSMul, hβ.smul]
    _ ≤ ‖z‖ * (a * να x) :=
      mul_le_mul_of_nonneg_left (hA x) (norm_nonneg z)
    _ = (‖z‖ * a) * να x := by ring

/-- Negation preserves a local mixed subordinate upper bound. -/
theorem mixedSubordinateBound_neg {n m : ℕ}
    {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ)
    {A : ComplexVectorMap n m} {a : ℝ}
    (hA : MixedSubordinateBound να νβ A a) :
    MixedSubordinateBound να νβ (complexVectorMapNeg A) a := by
  simpa [complexVectorMapNeg] using
    (mixedSubordinateBound_smul (να := να) (νβ := νβ) hβ (-1 : ℂ) hA)

/-- Subtraction is bounded by the sum of the two local mixed subordinate upper
    bounds. -/
theorem mixedSubordinateBound_sub {n m : ℕ}
    {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ)
    {A B : ComplexVectorMap n m} {a b : ℝ}
    (hA : MixedSubordinateBound να νβ A a)
    (hB : MixedSubordinateBound να νβ B b) :
    MixedSubordinateBound να νβ (complexVectorMapSub A B) (a + b) := by
  simpa [complexVectorMapSub] using
    (mixedSubordinateBound_add (να := να) (νβ := νβ) hβ hA
      (mixedSubordinateBound_neg (να := να) (νβ := νβ) hβ hB))

/-- Least-value comparison for a pointwise sum of maps. -/
theorem mixedSubordinateNormValue_add_le {n m : ℕ}
    {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ)
    {A B : ComplexVectorMap n m} {a b c : ℝ}
    (hadd : IsMixedSubordinateNormValue να νβ (complexVectorMapAdd A B) c)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hB : IsMixedSubordinateNormValue να νβ B b) :
    c ≤ a + b :=
  hadd.2 (a + b) (mixedSubordinateBound_add hβ hA.1 hB.1)

/-- Least-value comparison for complex scalar multiplication of maps. -/
theorem mixedSubordinateNormValue_smul_le {n m : ℕ}
    {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) (z : ℂ)
    {A : ComplexVectorMap n m} {a c : ℝ}
    (hsmul : IsMixedSubordinateNormValue να νβ (complexVectorMapSMul z A) c)
    (hA : IsMixedSubordinateNormValue να νβ A a) :
    c ≤ ‖z‖ * a :=
  hsmul.2 (‖z‖ * a) (mixedSubordinateBound_smul hβ z hA.1)

/-- Least-value comparison for a pointwise difference of maps. -/
theorem mixedSubordinateNormValue_sub_le {n m : ℕ}
    {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ)
    {A B : ComplexVectorMap n m} {a b c : ℝ}
    (hsub : IsMixedSubordinateNormValue να νβ (complexVectorMapSub A B) c)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hB : IsMixedSubordinateNormValue να νβ B b) :
    c ≤ a + b :=
  hsub.2 (a + b) (mixedSubordinateBound_sub hβ hA.1 hB.1)

/-- Reverse-triangle helper for local least mixed subordinate values.  If
    `T = U + V`, then the value of `V` is at most the value of `T` plus the
    value of `U`. -/
theorem mixedSubordinateNormValue_right_le_add_of_add_eq {n m : ℕ}
    {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ)
    {T U V : ComplexVectorMap n m} {t u v : ℝ}
    (hadd : T = complexVectorMapAdd U V)
    (hT : IsMixedSubordinateNormValue να νβ T t)
    (hU : IsMixedSubordinateNormValue να νβ U u)
    (hV : IsMixedSubordinateNormValue να νβ V v) :
    v ≤ t + u := by
  have hVsub : IsMixedSubordinateNormValue να νβ (complexVectorMapSub T U) v := by
    have hsub_eq : complexVectorMapSub T U = V := by
      rw [hadd]
      funext x
      ext i
      simp [complexVectorMapSub, complexVectorMapAdd, complexVectorMapNeg,
        complexVectorMapSMul, complexVecAdd, complexVecSMul]
    simpa [hsub_eq] using hV
  exact mixedSubordinateNormValue_sub_le hβ hVsub hT hU

/-- Symmetric reverse-triangle helper for local least mixed subordinate values.
    If `T = U + V`, then the value of `U` is at most the value of `T` plus the
    value of `V`. -/
theorem mixedSubordinateNormValue_left_le_add_of_add_eq {n m : ℕ}
    {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ)
    {T U V : ComplexVectorMap n m} {t u v : ℝ}
    (hadd : T = complexVectorMapAdd U V)
    (hT : IsMixedSubordinateNormValue να νβ T t)
    (hU : IsMixedSubordinateNormValue να νβ U u)
    (hV : IsMixedSubordinateNormValue να νβ V v) :
    u ≤ t + v := by
  have hUsub : IsMixedSubordinateNormValue να νβ (complexVectorMapSub T V) u := by
    have hsub_eq : complexVectorMapSub T V = U := by
      rw [hadd]
      funext x
      ext i
      simp [complexVectorMapSub, complexVectorMapAdd, complexVectorMapNeg,
        complexVectorMapSMul, complexVecAdd, complexVecSMul]
    simpa [hsub_eq] using hU
  exact mixedSubordinateNormValue_sub_le hβ hUsub hT hV

/-- Higham equation (6.7), bound form: composing an `α -> γ` map with a
    `γ -> β` map gives the product bound. -/
theorem mixedSubordinateBound_comp {n m k : ℕ}
    {να : CVec n → ℝ} {νγ : CVec m → ℝ} {νβ : CVec k → ℝ}
    {A : ComplexVectorMap m k} {B : ComplexVectorMap n m} {a b : ℝ}
    (ha0 : 0 ≤ a) (hA : MixedSubordinateBound νγ νβ A a)
    (hB : MixedSubordinateBound να νγ B b) :
    MixedSubordinateBound να νβ (complexVectorMapComp A B) (a * b) := by
  intro x
  calc
    νβ (complexVectorMapComp A B x) ≤ a * νγ (B x) := hA (B x)
    _ ≤ a * (b * να x) := mul_le_mul_of_nonneg_left (hB x) ha0
    _ = (a * b) * να x := by ring

/-- Higham equation (6.7), value form for the local least-bound predicate. -/
theorem mixedSubordinateNormValue_comp_le {n m k : ℕ}
    {να : CVec n → ℝ} {νγ : CVec m → ℝ} {νβ : CVec k → ℝ}
    {A : ComplexVectorMap m k} {B : ComplexVectorMap n m} {a b c : ℝ}
    (ha0 : 0 ≤ a)
    (hcomp : IsMixedSubordinateNormValue να νβ (complexVectorMapComp A B) c)
    (hA : IsMixedSubordinateNormValue νγ νβ A a)
    (hB : IsMixedSubordinateNormValue να νγ B b) :
    c ≤ a * b :=
  hcomp.2 (a * b) (mixedSubordinateBound_comp ha0 hA.1 hB.1)

set_option linter.unusedTactic false in
/-- Scaling a map by a positive real scalar scales its local mixed subordinate
    norm value by the same scalar. -/
theorem mixedSubordinateNormValue_smul_real_pos
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) {T : ComplexVectorMap n m} {c r : ℝ}
    (hrpos : 0 < r) (hT : IsMixedSubordinateNormValue να νβ T c) :
    IsMixedSubordinateNormValue να νβ (complexVectorMapSMul (r : ℂ) T) (r * c) := by
  -- Preserve frozen auxiliary names across the semantic module split.
  run_tac do
    let ngen ← Lean.getDeclNGen
    Lean.setDeclNGen { ngen with idx := 2 }
  refine ⟨?_, ?_⟩
  · intro v
    calc
      νβ (complexVectorMapSMul (r : ℂ) T v)
          = r * νβ (T v) := by
            rw [complexVectorMapSMul, hβ.smul, Complex.norm_of_nonneg (le_of_lt hrpos)]
      _ ≤ r * (c * να v) := mul_le_mul_of_nonneg_left (hT.1 v) (le_of_lt hrpos)
      _ = (r * c) * να v := by ring
  · intro d hd
    have hbound : MixedSubordinateBound να νβ T (d / r) := by
      intro v
      have h := hd v
      rw [complexVectorMapSMul, hβ.smul, Complex.norm_of_nonneg (le_of_lt hrpos)] at h
      have hdiv : νβ (T v) ≤ (d * να v) / r := by
        exact (le_div_iff₀ hrpos).mpr (by simpa [mul_comm] using h)
      calc
        νβ (T v) ≤ (d * να v) / r := hdiv
        _ = (d / r) * να v := by ring
    have hc_le : c ≤ d / r := hT.2 (d / r) hbound
    calc
      r * c ≤ r * (d / r) := mul_le_mul_of_nonneg_left hc_le (le_of_lt hrpos)
      _ = d := by field_simp [ne_of_gt hrpos]
end NumStability
