-- Analysis/OperatorNorms/Attainment.lean
--
-- Attainment of finite-dimensional subordinate operator norms.

import NumStability.Analysis.OperatorNorms.Basic
import NumStability.Analysis.VectorNorms.Duality

/-!
# Operator-norm attainment

Proves extremizer and exact-value results for subordinate operator norms from
finite-dimensional compactness and vector-norm duality.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- A continuous linear map on a finite-dimensional complex normed space
    attains its operator norm on the unit sphere whenever its norm is positive. -/
theorem exists_unit_vector_norm_apply_eq_opNorm_finiteDimensional
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E →L[ℂ] F) (hfpos : 0 < ‖f‖) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖f x‖ = ‖f‖ := by
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  cases subsingleton_or_nontrivial E with
  | inl hsub =>
      letI : Subsingleton E := hsub
      have hfzero : f = 0 := by
        ext x
        have hx : x = 0 := Subsingleton.elim x 0
        simp [hx]
      rw [hfzero, norm_zero] at hfpos
      exact False.elim (lt_irrefl _ hfpos)
  | inr hnon =>
      letI : Nontrivial E := hnon
      haveI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
      let s : Set E := Metric.sphere (0 : E) 1
      have hscompact : IsCompact s := by
        dsimp [s]
        exact isCompact_sphere (0 : E) 1
      have hsne : s.Nonempty := by
        dsimp [s]
        exact (NormedSpace.sphere_nonempty (E := E) (x := (0 : E)) (r := 1)).mpr
          zero_le_one
      have hcont : ContinuousOn (fun x : E => ‖f x‖) s :=
        (continuous_norm.comp f.continuous).continuousOn
      obtain ⟨x, hxs, hsSup, _hxmax⟩ :=
        hscompact.exists_sSup_image_eq_and_ge hsne hcont
      refine ⟨x, ?_, ?_⟩
      · simpa [s, Metric.mem_sphere, dist_eq_norm] using hxs
      · have hxnorm : ‖x‖ = 1 := by
          simpa [s, Metric.mem_sphere, dist_eq_norm] using hxs
        have hle : ‖f x‖ ≤ ‖f‖ := by
          simpa [hxnorm] using f.le_opNorm x
        apply le_antisymm hle
        have hsSupNorm := f.sSup_sphere_eq_norm
        exact le_of_eq <| by
          calc
            ‖f‖ = sSup ((fun x : E => ‖f x‖) '' s) := by
              simpa [s] using hsSupNorm.symm
            _ = ‖f x‖ := hsSup

/-- Values attained by a linear map on the `α`-unit sphere, measured in the
    `β`-norm.  This is the source-facing `max_{||x||_α = 1} ||T x||_β`
    carrier for equations (6.5)-(6.6). -/
def MixedUnitImageNormSet {n m : ℕ} (να : CVec n → ℝ) (νβ : CVec m → ℝ)
    (T : ComplexVectorMap n m) : Set ℝ :=
  {r | ∃ x : CVec n, να x = 1 ∧ r = νβ (T x)}

/-- Predicate form of the maximum of `||T x||_β` on the `α`-unit sphere. -/
def IsMaxMixedUnitImageNormValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (T : ComplexVectorMap n m) (c : ℝ) : Prop :=
  c ∈ MixedUnitImageNormSet να νβ T ∧
    ∀ r : ℝ, r ∈ MixedUnitImageNormSet να νβ T → r ≤ c

/-- Values `||T x||_β / ||x||_α` attained by nonzero source vectors. -/
def MixedNonzeroImageRatioSet {n m : ℕ} (να : CVec n → ℝ) (νβ : CVec m → ℝ)
    (T : ComplexVectorMap n m) : Set ℝ :=
  {r | ∃ x : CVec n, x ≠ 0 ∧ r = νβ (T x) / να x}

/-- Predicate form of the maximum of `||T x||_β / ||x||_α` over nonzero
    source vectors, the first max form in Higham equation (6.5). -/
def IsMaxMixedNonzeroImageRatioValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (T : ComplexVectorMap n m) (c : ℝ) : Prop :=
  c ∈ MixedNonzeroImageRatioSet να νβ T ∧
    ∀ r : ℝ, r ∈ MixedNonzeroImageRatioSet να νβ T → r ≤ c

/-- Predicate form of the minimum of `||T x||_β / ||x||_α` over nonzero
    source vectors.  This is the denominator in Higham Problem 6.6. -/
def IsMinMixedNonzeroImageRatioValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (T : ComplexVectorMap n m) (c : ℝ) : Prop :=
  c ∈ MixedNonzeroImageRatioSet να νβ T ∧
    ∀ r : ℝ, r ∈ MixedNonzeroImageRatioSet να νβ T → c ≤ r

/-- Real scalar pairings `Re φ(T x)` with a source-unit vector and a
    target-dual-unit functional.  This is the local functional replacement for
    the `Re y^* A x` numerator in Higham Problem 6.3. -/
def MixedDualUnitPairingRealSet {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (T : ComplexVectorMap n m) : Set ℝ :=
  {r | ∃ (x : CVec n) (φ : CVec m → ℂ),
    να x = 1 ∧ IsDualFunctionalNormValue νβ φ 1 ∧ r = Complex.re (φ (T x))}

/-- Predicate form of the maximum dual-unit real pairing in Problem 6.3. -/
def IsMaxMixedDualUnitPairingRealValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (T : ComplexVectorMap n m) (c : ℝ) : Prop :=
  c ∈ MixedDualUnitPairingRealSet να νβ T ∧
    ∀ r : ℝ, r ∈ MixedDualUnitPairingRealSet να νβ T → r ≤ c

theorem isMixedSubordinateNormValue_of_isMaxMixedUnitImageNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {T : ComplexVectorMap n m} {c : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hTlin : IsComplexVectorMapLinear T)
    (hmax : IsMaxMixedUnitImageNormValue να νβ T c) :
    IsMixedSubordinateNormValue να νβ T c := by
  refine ⟨?_, ?_⟩
  · intro x
    by_cases hxzero : x = 0
    · have hTxzero : T x = 0 := by
        rw [hxzero]
        exact hTlin.map_zero
      have hleft : νβ (T x) = 0 := (hβ.eq_zero_iff (T x)).mpr hTxzero
      have hright : c * να x = 0 := by
        have hxnorm : να x = 0 := (hα.eq_zero_iff x).mpr hxzero
        rw [hxnorm, mul_zero]
      rw [hleft, hright]
    · have hxnorm_ne : να x ≠ 0 := by
        intro hxnorm
        exact hxzero ((hα.eq_zero_iff x).mp hxnorm)
      have hxnorm_pos : 0 < να x :=
        lt_of_le_of_ne (hα.nonneg x) (Ne.symm hxnorm_ne)
      let u : CVec n := complexVecSMul (((να x)⁻¹ : ℝ) : ℂ) x
      have hinv_nonneg : 0 ≤ (να x)⁻¹ := inv_nonneg.mpr (hα.nonneg x)
      have hu_unit : να u = 1 := by
        dsimp [u]
        rw [hα.smul, Complex.norm_of_nonneg hinv_nonneg]
        field_simp [ne_of_gt hxnorm_pos]
      have humem : νβ (T u) ∈ MixedUnitImageNormSet να νβ T :=
        ⟨u, hu_unit, rfl⟩
      have hmax_le : νβ (T u) ≤ c := hmax.2 (νβ (T u)) humem
      have hscaled_abs : |να x|⁻¹ * νβ (T x) ≤ c := by
        simpa [u, hTlin.map_smul, hβ.smul] using hmax_le
      have hscaled : (να x)⁻¹ * νβ (T x) ≤ c := by
        simpa [abs_of_nonneg (hα.nonneg x)] using hscaled_abs
      have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt hxnorm_pos)
      calc
        νβ (T x) = να x * ((να x)⁻¹ * νβ (T x)) := by
          field_simp [ne_of_gt hxnorm_pos]
        _ ≤ να x * c := hmul
        _ = c * να x := by ring
  · intro d hd
    obtain ⟨x, hxunit, hc⟩ := hmax.1
    have hdx := hd x
    rw [hxunit, mul_one] at hdx
    rw [hc]
    exact hdx

theorem isMaxMixedNonzeroImageRatioValue_of_isMaxMixedUnitImageNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {T : ComplexVectorMap n m} {c : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hTlin : IsComplexVectorMapLinear T)
    (hmax : IsMaxMixedUnitImageNormValue να νβ T c) :
    IsMaxMixedNonzeroImageRatioValue να νβ T c := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxunit, hc⟩ := hmax.1
    have hxne : x ≠ 0 := by
      intro hxzero
      have hxnorm : να x = 0 := (hα.eq_zero_iff x).mpr hxzero
      rw [hxunit] at hxnorm
      norm_num at hxnorm
    refine ⟨x, hxne, ?_⟩
    rw [hc, hxunit]
    ring
  · intro r hr
    obtain ⟨x, hxne, hr⟩ := hr
    have hxnorm_ne : να x ≠ 0 := by
      intro hxnorm
      exact hxne ((hα.eq_zero_iff x).mp hxnorm)
    have hxnorm_pos : 0 < να x :=
      lt_of_le_of_ne (hα.nonneg x) (Ne.symm hxnorm_ne)
    let u : CVec n := complexVecSMul (((να x)⁻¹ : ℝ) : ℂ) x
    have hinv_nonneg : 0 ≤ (να x)⁻¹ := inv_nonneg.mpr (hα.nonneg x)
    have hu_unit : να u = 1 := by
      dsimp [u]
      rw [hα.smul, Complex.norm_of_nonneg hinv_nonneg]
      field_simp [ne_of_gt hxnorm_pos]
    have humem : νβ (T u) ∈ MixedUnitImageNormSet να νβ T :=
      ⟨u, hu_unit, rfl⟩
    have hmax_le : νβ (T u) ≤ c := hmax.2 (νβ (T u)) humem
    have hscaled_abs : |να x|⁻¹ * νβ (T x) ≤ c := by
      simpa [u, hTlin.map_smul, hβ.smul] using hmax_le
    have hscaled : (να x)⁻¹ * νβ (T x) ≤ c := by
      simpa [abs_of_nonneg (hα.nonneg x)] using hscaled_abs
    rw [hr]
    calc
      νβ (T x) / να x = (να x)⁻¹ * νβ (T x) := by ring
      _ ≤ c := hscaled

theorem isMaxMixedUnitImageNormValue_of_isMaxMixedNonzeroImageRatioValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {T : ComplexVectorMap n m} {c : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hTlin : IsComplexVectorMapLinear T)
    (hmax : IsMaxMixedNonzeroImageRatioValue να νβ T c) :
    IsMaxMixedUnitImageNormValue να νβ T c := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxne, hc⟩ := hmax.1
    have hxnorm_ne : να x ≠ 0 := by
      intro hxnorm
      exact hxne ((hα.eq_zero_iff x).mp hxnorm)
    have hxnorm_pos : 0 < να x :=
      lt_of_le_of_ne (hα.nonneg x) (Ne.symm hxnorm_ne)
    let u : CVec n := complexVecSMul (((να x)⁻¹ : ℝ) : ℂ) x
    have hinv_nonneg : 0 ≤ (να x)⁻¹ := inv_nonneg.mpr (hα.nonneg x)
    have hu_unit : να u = 1 := by
      dsimp [u]
      rw [hα.smul, Complex.norm_of_nonneg hinv_nonneg]
      field_simp [ne_of_gt hxnorm_pos]
    refine ⟨u, hu_unit, ?_⟩
    have hu_norm_abs :
        νβ (T u) = |να x|⁻¹ * νβ (T x) := by
      simp [u, hTlin.map_smul, hβ.smul]
    have hu_norm : νβ (T u) = (να x)⁻¹ * νβ (T x) := by
      simpa [abs_of_nonneg (hα.nonneg x)] using hu_norm_abs
    rw [hu_norm, hc]
    ring
  · intro r hr
    obtain ⟨x, hxunit, hr⟩ := hr
    have hxne : x ≠ 0 := by
      intro hxzero
      have hxnorm : να x = 0 := (hα.eq_zero_iff x).mpr hxzero
      rw [hxunit] at hxnorm
      norm_num at hxnorm
    have hratio_mem : νβ (T x) / να x ∈ MixedNonzeroImageRatioSet να νβ T :=
      ⟨x, hxne, rfl⟩
    have hratio_le := hmax.2 (νβ (T x) / να x) hratio_mem
    rw [hr]
    rw [hxunit, div_one] at hratio_le
    exact hratio_le

theorem isMaxMixedNonzeroImageRatioValue_iff_unitImageNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {T : ComplexVectorMap n m} {c : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hTlin : IsComplexVectorMapLinear T) :
    IsMaxMixedNonzeroImageRatioValue να νβ T c ↔
      IsMaxMixedUnitImageNormValue να νβ T c := by
  constructor
  · exact isMaxMixedUnitImageNormValue_of_isMaxMixedNonzeroImageRatioValue
      hα hβ hTlin
  · exact isMaxMixedNonzeroImageRatioValue_of_isMaxMixedUnitImageNormValue
      hα hβ hTlin

/-- In finite dimensions, a positive least mixed subordinate bound is attained
    by some unit source vector.  This closes the compactness/norm-attainment
    step needed in Higham's proof of equation (6.10) for the local
    source-facing least-bound predicate. -/
theorem exists_unit_vector_attaining_mixedSubordinateNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {T : ComplexVectorMap n m} (hTlin : IsComplexVectorMapLinear T)
    {c : ℝ} (hTval : IsMixedSubordinateNormValue να νβ T c)
    (hcpos : 0 < c) :
    ∃ x : CVec n, να x = 1 ∧ νβ (T x) = c := by
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
  have hLbound : ∀ x : NormedCVec n να, ‖L x‖ ≤ c * ‖x‖ := by
    intro x
    exact hTval.1 x.val
  let f : NormedCVec n να →L[ℂ] NormedCVec m νβ :=
    L.mkContinuous c hLbound
  have hf_norm_le : ‖f‖ ≤ c :=
    LinearMap.mkContinuous_norm_le L (le_of_lt hcpos) hLbound
  have hbound_op : MixedSubordinateBound να νβ T ‖f‖ := by
    intro x
    have h := f.le_opNorm (⟨x⟩ : NormedCVec n να)
    simpa [f, L, NormedCVec.norm_eq] using h
  have hc_le_norm : c ≤ ‖f‖ := hTval.2 ‖f‖ hbound_op
  have hfnorm : ‖f‖ = c := le_antisymm hf_norm_le hc_le_norm
  have hfpos : 0 < ‖f‖ := by
    rw [hfnorm]
    exact hcpos
  obtain ⟨x, hxnorm, hfxnorm⟩ :=
    @exists_unit_vector_norm_apply_eq_opNorm_finiteDimensional
      (NormedCVec n να) (NormedCVec m νβ)
      instSrcNAG instSrcNS instSrcFin instTgtNAG instTgtNS f hfpos
  refine ⟨x.val, ?_, ?_⟩
  · simpa [NormedCVec.norm_eq] using hxnorm
  · have hfx : ‖f x‖ = c := hfxnorm.trans hfnorm
    simpa [f, L, NormedCVec.norm_eq] using hfx

/-- View a complex linear functional as a source-facing map into `C^1`. -/
noncomputable def dualFunctionalAsVectorMap {n : ℕ} (φ : CVec n → ℂ) :
    ComplexVectorMap n 1 :=
  fun v _ => φ v

lemma dualFunctionalAsVectorMap_linear {n : ℕ} {φ : CVec n → ℂ}
    (hφ : IsComplexLinearForm φ) :
    IsComplexVectorMapLinear (dualFunctionalAsVectorMap φ) := by
  constructor
  · intro x y
    ext i
    simp [dualFunctionalAsVectorMap, complexVecAdd, hφ.map_add]
  · intro a x
    ext i
    simp [dualFunctionalAsVectorMap, complexVecSMul, hφ.map_smul]

lemma complexVecOneNorm_dualFunctionalAsVectorMap_apply
    {n : ℕ} (φ : CVec n → ℂ) (x : CVec n) :
    complexVecOneNorm (dualFunctionalAsVectorMap φ x) = ‖φ x‖ := by
  unfold complexVecOneNorm dualFunctionalAsVectorMap
  simp

/-- A dual functional least-bound value is the same as a mixed subordinate
    least-bound value for the associated map into `C^1`. -/
theorem dualFunctional_as_mixedSubordinateNormValue
    {n : ℕ} {ν : CVec n → ℝ} {φ : CVec n → ℂ} {d : ℝ}
    (hφd : IsDualFunctionalNormValue ν φ d) :
    IsComplexVectorMapLinear (dualFunctionalAsVectorMap φ) ∧
      IsMixedSubordinateNormValue ν complexVecOneNorm
        (dualFunctionalAsVectorMap φ) d := by
  refine ⟨dualFunctionalAsVectorMap_linear hφd.linear, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x
    simpa [complexVecOneNorm_dualFunctionalAsVectorMap_apply] using hφd.bound x
  · intro e he
    apply hφd.least e
    intro x
    simpa [complexVecOneNorm_dualFunctionalAsVectorMap_apply] using he x

/-- Positive dual least-bound values attain the source-facing unit-vector
    maximum in equation (6.2). -/
theorem isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue_pos
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    {φ : CVec n → ℂ} {d : ℝ}
    (hφd : IsDualFunctionalNormValue ν φ d) (hdpos : 0 < d) :
    IsMaxDualUnitFunctionalNormValue ν φ d := by
  have hβ : IsComplexVectorNorm (complexVecOneNorm (n := 1)) :=
    complexVecOneNorm_isComplexVectorNorm
  obtain ⟨hTlin, hTval⟩ := dualFunctional_as_mixedSubordinateNormValue hφd
  obtain ⟨x, hxunit, hTx⟩ :=
    exists_unit_vector_attaining_mixedSubordinateNormValue
      hν hβ hTlin hTval hdpos
  refine ⟨?_, ?_⟩
  · refine ⟨x, hxunit, ?_⟩
    exact hTx.symm.trans (complexVecOneNorm_dualFunctionalAsVectorMap_apply φ x)
  · intro r hr
    obtain ⟨x, hxunit, hr⟩ := hr
    rw [hr]
    have h := hφd.bound x
    rwa [hxunit, mul_one] at h

/-- The zero dual least-bound case still attains the unit-vector maximum when
    the source dimension is nonempty: every unit value is zero. -/
theorem isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue_zero
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν) (hn : 0 < n)
    {φ : CVec n → ℂ}
    (hφd : IsDualFunctionalNormValue ν φ 0) :
    IsMaxDualUnitFunctionalNormValue ν φ 0 := by
  obtain ⟨u, hu_unit⟩ := exists_unit_complexVectorNorm hν hn
  have hφu_le_zero : ‖φ u‖ ≤ 0 := by
    have h := hφd.bound u
    simpa [hu_unit] using h
  have hφu_zero : ‖φ u‖ = 0 :=
    le_antisymm hφu_le_zero (norm_nonneg (φ u))
  refine ⟨?_, ?_⟩
  · exact ⟨u, hu_unit, hφu_zero.symm⟩
  · intro r hr
    obtain ⟨x, hxunit, hr⟩ := hr
    rw [hr]
    have h := hφd.bound x
    rwa [hxunit, mul_one] at h

/-- Nonempty-dimensional form of equation (6.2): every local dual least-bound
    value is the maximum over unit vectors. -/
theorem isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν) (hn : 0 < n)
    {φ : CVec n → ℂ} {d : ℝ}
    (hφd : IsDualFunctionalNormValue ν φ d) :
    IsMaxDualUnitFunctionalNormValue ν φ d := by
  have hdnonneg := dualFunctionalNormValue_nonneg_of_nonempty hν hn hφd
  rcases lt_or_eq_of_le hdnonneg with hdpos | hdzero
  · exact isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue_pos hν hφd hdpos
  · subst hdzero
    exact isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue_zero hν hn hφd

/-- Nonempty-dimensional form of equation (6.2): every local dual least-bound
    value is also the maximum of the nonzero-vector ratio. -/
theorem isMaxDualNonzeroFunctionalRatioValue_of_dualFunctionalNormValue
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν) (hn : 0 < n)
    {φ : CVec n → ℂ} {d : ℝ}
    (hφd : IsDualFunctionalNormValue ν φ d) :
    IsMaxDualNonzeroFunctionalRatioValue ν φ d := by
  exact isMaxDualNonzeroFunctionalRatioValue_of_isMaxDualUnitFunctionalNormValue
    hν hφd.linear
    (isMaxDualUnitFunctionalNormValue_of_dualFunctionalNormValue hν hn hφd)

/-- Source-facing maximum form of equations (6.5)-(6.6): a positive least
    mixed subordinate value is attained as the maximum of `||T x||_β` over
    `||x||_α = 1`. -/
theorem isMaxMixedUnitImageNormValue_of_mixedSubordinateNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {T : ComplexVectorMap n m} (hTlin : IsComplexVectorMapLinear T)
    {c : ℝ} (hTval : IsMixedSubordinateNormValue να νβ T c)
    (hcpos : 0 < c) :
    IsMaxMixedUnitImageNormValue να νβ T c := by
  obtain ⟨x, hxunit, hTx⟩ :=
    exists_unit_vector_attaining_mixedSubordinateNormValue hα hβ hTlin hTval hcpos
  refine ⟨?_, ?_⟩
  · exact ⟨x, hxunit, hTx.symm⟩
  · intro r hr
    obtain ⟨y, hyunit, hr⟩ := hr
    rw [hr]
    have hbound := hTval.1 y
    rwa [hyunit, mul_one] at hbound

/-- Nonempty-domain form of equations (6.5)-(6.6): a local least mixed
    subordinate value is the maximum on the source unit sphere.  The positive
    case uses finite-dimensional norm attainment; the zero case uses any unit
    vector and the least-bound inequality. -/
theorem isMaxMixedUnitImageNormValue_of_mixedSubordinateNormValue_nonempty
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hn : 0 < n) {T : ComplexVectorMap n m}
    (hTlin : IsComplexVectorMapLinear T) {c : ℝ}
    (hTval : IsMixedSubordinateNormValue να νβ T c) :
    IsMaxMixedUnitImageNormValue να νβ T c := by
  by_cases hcpos : 0 < c
  · exact isMaxMixedUnitImageNormValue_of_mixedSubordinateNormValue
      hα hβ hTlin hTval hcpos
  · have hcnonneg : 0 ≤ c := by
      obtain ⟨u, hu⟩ := exists_unit_complexVectorNorm hα hn
      have hbound := hTval.1 u
      rw [hu, mul_one] at hbound
      exact (hβ.nonneg (T u)).trans hbound
    have hc : c = 0 := le_antisymm (le_of_not_gt hcpos) hcnonneg
    obtain ⟨u, hu⟩ := exists_unit_complexVectorNorm hα hn
    refine ⟨?_, ?_⟩
    · have hbound := hTval.1 u
      rw [hu, hc, zero_mul] at hbound
      have hzero : νβ (T u) = 0 :=
        le_antisymm hbound (hβ.nonneg (T u))
      exact ⟨u, hu, hc.trans hzero.symm⟩
    · intro r hr
      obtain ⟨x, hxunit, hr⟩ := hr
      rw [hr, hc]
      have hbound := hTval.1 x
      rwa [hxunit, hc, zero_mul] at hbound

/-- Problem 6.6 inverse/minimum-gain bridge: if `Ainv` is a two-sided inverse
    of `A` and has local mixed norm value `s`, then the minimum of
    `||A x||_β / ||x||_α` over nonzero vectors is `s⁻¹`. -/
theorem isMinMixedNonzeroImageRatioValue_inv_of_inverseNormValue
    {n : ℕ} {να νβ : CVec n → ℝ} {A Ainv : ComplexVectorMap n n} {s : ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hAinv_left : ∀ x : CVec n, Ainv (A x) = x)
    (hAinv_right : ∀ y : CVec n, A (Ainv y) = y)
    (hAinv_lin : IsComplexVectorMapLinear Ainv)
    (hAinv : IsMixedSubordinateNormValue νβ να Ainv s) (hspos : 0 < s) :
    IsMinMixedNonzeroImageRatioValue να νβ A s⁻¹ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hyunit, hAinvy⟩ :=
      exists_unit_vector_attaining_mixedSubordinateNormValue
        hβ hα hAinv_lin hAinv hspos
    let x : CVec n := Ainv y
    have hxnorm : να x = s := by
      simpa [x] using hAinvy
    have hxne : x ≠ 0 := by
      intro hxzero
      have hxnorm_zero : να x = 0 := (hα.eq_zero_iff x).mpr hxzero
      rw [hxnorm] at hxnorm_zero
      exact (ne_of_gt hspos) hxnorm_zero
    refine ⟨x, hxne, ?_⟩
    have hAx : A x = y := by
      simpa [x] using hAinv_right y
    rw [hAx, hyunit, hxnorm, one_div]
  · intro r hr
    obtain ⟨x, hxne, rfl⟩ := hr
    have hxnorm_ne : να x ≠ 0 := by
      intro hxnorm
      exact hxne ((hα.eq_zero_iff x).mp hxnorm)
    have hxnorm_pos : 0 < να x :=
      lt_of_le_of_ne (hα.nonneg x) (Ne.symm hxnorm_ne)
    have hbound := hAinv.1 (A x)
    rw [hAinv_left x] at hbound
    have hmul : s⁻¹ * να x ≤ νβ (A x) := by
      have h :=
        mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr hspos))
      calc
        s⁻¹ * να x ≤ s⁻¹ * (s * νβ (A x)) := h
        _ = νβ (A x) := by field_simp [ne_of_gt hspos]
    rw [le_div_iff₀ hxnorm_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Problem 6.3, functional form of the dual characterization of a
    subordinate norm: a local mixed norm value is the maximum of
    `Re φ(T x)` over source-unit `x` and target-dual-unit functionals `φ`. -/
theorem isMaxMixedDualUnitPairingRealValue_of_mixedSubordinateNormValue_nonempty
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hn : 0 < n) (hm : 0 < m) {T : ComplexVectorMap n m}
    (hTlin : IsComplexVectorMapLinear T) {c : ℝ}
    (hTval : IsMixedSubordinateNormValue να νβ T c) :
    IsMaxMixedDualUnitPairingRealValue να νβ T c := by
  refine ⟨?_, ?_⟩
  · by_cases hcpos : 0 < c
    · obtain ⟨x, hxunit, hTxnorm⟩ :=
        exists_unit_vector_attaining_mixedSubordinateNormValue
          hα hβ hTlin hTval hcpos
      let y : CVec m := complexVecSMul (((c⁻¹ : ℝ) : ℂ)) (T x)
      have hcinv_nonneg : 0 ≤ c⁻¹ := inv_nonneg.mpr (le_of_lt hcpos)
      have hyunit : νβ y = 1 := by
        dsimp [y]
        rw [hβ.smul, Complex.norm_of_nonneg hcinv_nonneg, hTxnorm]
        field_simp [ne_of_gt hcpos]
      obtain ⟨φ, hφ, hφy⟩ :=
        exists_dualFunctionalNormValue_one_of_unit_vector hβ hyunit
      refine ⟨x, φ, hxunit, hφ, ?_⟩
      have hscale : (((c⁻¹ : ℝ) : ℂ)) * φ (T x) = 1 := by
        have hmap := hφ.linear.map_smul (((c⁻¹ : ℝ) : ℂ)) (T x)
        have hmap' : φ y = (((c⁻¹ : ℝ) : ℂ)) * φ (T x) := by
          simpa [y] using hmap
        exact hmap'.symm.trans hφy
      have hφTx : φ (T x) = (c : ℂ) := by
        have hc_mul_inv : (c : ℂ) * (((c⁻¹ : ℝ) : ℂ)) = 1 := by
          rw [← Complex.ofReal_mul]
          norm_num [mul_inv_cancel₀ (ne_of_gt hcpos)]
        calc
          φ (T x) = (c : ℂ) * ((((c⁻¹ : ℝ) : ℂ)) * φ (T x)) := by
            rw [← mul_assoc, hc_mul_inv, one_mul]
          _ = (c : ℂ) := by rw [hscale, mul_one]
      rw [hφTx]
      simp
    · have hcnonneg : 0 ≤ c :=
        mixedSubordinateNormValue_nonneg_of_nonempty hn hα hβ hTval
      have hc : c = 0 := le_antisymm (le_of_not_gt hcpos) hcnonneg
      obtain ⟨x, hxunit⟩ := exists_unit_complexVectorNorm hα hn
      obtain ⟨y, hyunit⟩ := exists_unit_complexVectorNorm hβ hm
      obtain ⟨φ, hφ, _hφy⟩ :=
        exists_dualFunctionalNormValue_one_of_unit_vector hβ hyunit
      have hTx_zero : T x = 0 := by
        have hbound := hTval.1 x
        rw [hxunit, hc, zero_mul] at hbound
        exact (hβ.eq_zero_iff (T x)).mp
          (le_antisymm hbound (hβ.nonneg (T x)))
      refine ⟨x, φ, hxunit, hφ, ?_⟩
      rw [hc, hTx_zero, hφ.linear.map_zero]
      simp
  · intro r hr
    obtain ⟨x, φ, hxunit, hφ, rfl⟩ := hr
    have hφ_bound := hφ.bound (T x)
    have hT_bound := hTval.1 x
    have hnorm_le : ‖φ (T x)‖ ≤ c := by
      calc
        ‖φ (T x)‖ ≤ 1 * νβ (T x) := hφ_bound
        _ = νβ (T x) := one_mul _
        _ ≤ c * να x := hT_bound
        _ = c := by rw [hxunit, mul_one]
    exact (Complex.re_le_norm (φ (T x))).trans hnorm_le

/-- Rank-one operator `v ↦ φ(v) y`. -/
noncomputable def rankOneOperator {n m : ℕ} (φ : CVec n → ℂ) (y : CVec m) :
    ComplexVectorMap n m :=
  fun v j => φ v * y j

lemma rankOneOperator_linear {n m : ℕ} {φ : CVec n → ℂ} {y : CVec m}
    (hφ : IsComplexLinearForm φ) :
    IsComplexVectorMapLinear (rankOneOperator φ y) := by
  constructor
  · intro u v
    ext j
    simp [rankOneOperator, complexVecAdd, hφ.map_add]
    ring
  · intro a v
    ext j
    simp [rankOneOperator, complexVecSMul, hφ.map_smul, mul_assoc]

lemma rankOneOperator_apply_norm {n m : ℕ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) (φ : CVec n → ℂ) (y : CVec m)
    (v : CVec n) :
    νβ (rankOneOperator φ y v) = ‖φ v‖ * νβ y := by
  exact hβ.smul (φ v) y

/-- Rank-one mixed subordinate norm formula, in the local least-bound model:
    if `φ` has dual functional norm value `d`, then `v ↦ φ(v)y` has mixed
    subordinate norm value `νβ y * d`, provided the target vector has positive
    `β`-norm.  This is the source-facing functional version of Problem 6.2. -/
theorem rankOneOperator_isMixedSubordinateNormValue_of_dualFunctionalNormValue
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) {φ : CVec n → ℂ} {y : CVec m} {d : ℝ}
    (hφ : IsDualFunctionalNormValue να φ d) (hypos : 0 < νβ y) :
    IsComplexVectorMapLinear (rankOneOperator φ y) ∧
      IsMixedSubordinateNormValue να νβ (rankOneOperator φ y) (νβ y * d) := by
  refine ⟨rankOneOperator_linear hφ.linear, ?_⟩
  refine ⟨?_, ?_⟩
  · intro v
    have hy_nonneg : 0 ≤ νβ y := le_of_lt hypos
    calc
      νβ (rankOneOperator φ y v) = ‖φ v‖ * νβ y :=
        rankOneOperator_apply_norm hβ φ y v
      _ ≤ (d * να v) * νβ y :=
        mul_le_mul_of_nonneg_right (hφ.bound v) hy_nonneg
      _ = (νβ y * d) * να v := by ring
  · intro c hc
    have hdual_bound : DualFunctionalBound να φ (c / νβ y) := by
      intro v
      have h := hc v
      rw [rankOneOperator_apply_norm hβ φ y v] at h
      have hdiv : ‖φ v‖ ≤ (c * να v) / νβ y :=
        (le_div_iff₀ hypos).mpr h
      calc
        ‖φ v‖ ≤ (c * να v) / νβ y := hdiv
        _ = (c / νβ y) * να v := by ring
    have hd_le : d ≤ c / νβ y := hφ.least (c / νβ y) hdual_bound
    calc
      νβ y * d ≤ νβ y * (c / νβ y) :=
        mul_le_mul_of_nonneg_left hd_le (le_of_lt hypos)
      _ = c := by field_simp [ne_of_gt hypos]

lemma rankOneOperator_apply_of_norming_value {n m : ℕ} (φ : CVec n → ℂ)
    (x : CVec n) (y : CVec m) (hφx : φ x = 1) :
    rankOneOperator φ y x = y := by
  ext j
  simp [rankOneOperator, hφx]

lemma mixedSubordinateNormValue_one_of_bound_attained {n m : ℕ}
    {να : CVec n → ℝ} {νβ : CVec m → ℝ} {T : ComplexVectorMap n m}
    {x : CVec n} (hx : να x = 1) (hTx : νβ (T x) = 1)
    (hbound : MixedSubordinateBound να νβ T 1) :
    IsMixedSubordinateNormValue να νβ T 1 := by
  refine ⟨hbound, ?_⟩
  intro d hd
  have h := hd x
  rw [hTx, hx] at h
  simpa using h

/-- Higham, 2nd ed., Chapter 6, Lemma 6.3 foundation:
    given a unit source vector with a norming functional and a unit target
    vector, the rank-one operator `v ↦ φ(v)y` maps the source vector to the
    target vector and has mixed subordinate norm value `1`.

    The following existence theorem discharges the norming-functional hypothesis
    for unit vectors using the Hahn-Banach bridge above. -/
theorem rankOne_isMixedSubordinateNormValue_one_of_normingFunctional
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hβ : IsComplexVectorNorm νβ) {x : CVec n} {y : CVec m}
    {φ : CVec n → ℂ} (hx : να x = 1) (hy : νβ y = 1)
    (hφ : IsNormingFunctionalAt να x φ) :
    IsMixedSubordinateNormValue να νβ (rankOneOperator φ y) 1 ∧
      rankOneOperator φ y x = y := by
  have hmap : rankOneOperator φ y x = y :=
    rankOneOperator_apply_of_norming_value φ x y hφ.value
  have hbound : MixedSubordinateBound να νβ (rankOneOperator φ y) 1 := by
    intro v
    calc
      νβ (rankOneOperator φ y v) = ‖φ v‖ * νβ y :=
        rankOneOperator_apply_norm hβ φ y v
      _ = ‖φ v‖ := by rw [hy, mul_one]
      _ ≤ να v := hφ.bound v
      _ = 1 * να v := by ring
  exact ⟨mixedSubordinateNormValue_one_of_bound_attained hx (by rw [hmap, hy]) hbound,
    hmap⟩

/-- Higham, 2nd ed., Chapter 6, Lemma 6.3 foundation:
    for any unit source vector `x` and unit target vector `y`, there is a
    rank-one map with mixed subordinate norm value `1` that maps `x` to `y`. -/
theorem exists_rankOne_isMixedSubordinateNormValue_one
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {x : CVec n} {y : CVec m} (hx : να x = 1) (hy : νβ y = 1) :
    ∃ T : ComplexVectorMap n m,
      IsComplexVectorMapLinear T ∧
        IsMixedSubordinateNormValue να νβ T 1 ∧ T x = y := by
  obtain ⟨φ, hφ⟩ := NormedCVec.exists_normingFunctionalAt_of_unit_vector hα hx
  have hmain :=
    rankOne_isMixedSubordinateNormValue_one_of_normingFunctional hβ hx hy hφ
  exact ⟨rankOneOperator φ y, rankOneOperator_linear hφ.linear, hmain⟩
end NumStability
