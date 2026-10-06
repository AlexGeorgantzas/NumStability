-- Analysis/VectorNorms/Duality.lean
--
-- Dual complex-vector norms and support functionals.

import Mathlib.Analysis.Normed.Module.HahnBanach
import NumStability.Analysis.VectorNorms.Basic

/-!
# Complex-vector norm duality

Defines dual-norm constructions and proves finite-dimensional duality and
supporting-functional results, using Hahn--Banach where required.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


-- ============================================================
-- Dual functional norm foundation
-- ============================================================

/-- Abstract complex linear functional on `C^n`, in the explicit vector
    operations used by this source-facing file. -/
structure IsComplexLinearForm {n : ℕ} (φ : CVec n → ℂ) : Prop where
  map_add : ∀ x y : CVec n, φ (complexVecAdd x y) = φ x + φ y
  map_smul : ∀ (a : ℂ) (x : CVec n), φ (complexVecSMul a x) = a * φ x

lemma IsComplexLinearForm.map_zero {n : ℕ} {φ : CVec n → ℂ}
    (hφ : IsComplexLinearForm φ) : φ 0 = 0 := by
  have h := hφ.map_smul (0 : ℂ) (0 : CVec n)
  have hleft : complexVecSMul (0 : ℂ) (0 : CVec n) = 0 := by
    ext i
    simp [complexVecSMul]
  rw [hleft] at h
  simpa using h

lemma IsComplexLinearForm.apply_sum {n : ℕ} {φ : CVec n → ℂ}
    (hφ : IsComplexLinearForm φ) (s : Finset (Fin n)) (a : Fin n → ℂ)
    (v : Fin n → CVec n) :
    φ (fun i : Fin n => Finset.sum s fun j => a j * v j i) =
      Finset.sum s fun j => a j * φ (v j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change φ (0 : CVec n) = 0
      exact hφ.map_zero
  | insert j s hjs ih =>
      have hsplit :
          (fun i : Fin n => Finset.sum (insert j s) fun k => a k * v k i) =
            complexVecAdd (complexVecSMul (a j) (v j))
              (fun i : Fin n => Finset.sum s fun k => a k * v k i) := by
        ext i
        simp [Finset.sum_insert hjs, complexVecAdd, complexVecSMul]
      rw [hsplit, hφ.map_add, hφ.map_smul, ih, Finset.sum_insert hjs]

lemma IsComplexLinearForm.apply_eq_sum_basis {n : ℕ} {φ : CVec n → ℂ}
    (hφ : IsComplexLinearForm φ) (x : CVec n) :
    φ x = ∑ j : Fin n, x j * φ (standardBasisCVec j) := by
  have hdecomp :
      (fun i : Fin n => ∑ j : Fin n, x j * standardBasisCVec j i) = x :=
    sum_smul_standardBasisCVec x
  calc
    φ x = φ (fun i : Fin n => ∑ j : Fin n, x j * standardBasisCVec j i) := by
      rw [hdecomp]
    _ = ∑ j : Fin n, x j * φ (standardBasisCVec j) := by
      simpa using hφ.apply_sum Finset.univ x standardBasisCVec

/-- A norming functional for `x`: it is complex-linear, bounded by the norm,
    and attains the value `1` at `x`.  This is the local hypothesis supplied by
    the dual-norm-attainment step in Higham, equation (6.3). -/
structure IsNormingFunctionalAt {n : ℕ} (ν : CVec n → ℝ) (x : CVec n)
    (φ : CVec n → ℂ) : Prop where
  linear : IsComplexLinearForm φ
  bound : ∀ v : CVec n, ‖φ v‖ ≤ ν v
  value : φ x = 1

/-- A functional has dual-norm upper bound `d` with respect to the source
    vector norm `ν`. -/
def DualFunctionalBound {n : ℕ} (ν : CVec n → ℝ) (φ : CVec n → ℂ)
    (d : ℝ) : Prop :=
  ∀ v : CVec n, ‖φ v‖ ≤ d * ν v

/-- Least-bound predicate for the dual norm of a complex linear functional.
    This is the functional analogue of `IsMixedSubordinateNormValue` and is
    used for the rank-one subordinate norm identity in Problem 6.2. -/
structure IsDualFunctionalNormValue {n : ℕ} (ν : CVec n → ℝ)
    (φ : CVec n → ℂ) (d : ℝ) : Prop where
  linear : IsComplexLinearForm φ
  bound : DualFunctionalBound ν φ d
  least : ∀ e : ℝ, DualFunctionalBound ν φ e → d ≤ e

/-- Values `|φ x|` attained by a linear functional on the unit sphere. -/
def DualUnitFunctionalNormSet {n : ℕ} (ν : CVec n → ℝ)
    (φ : CVec n → ℂ) : Set ℝ :=
  {r | ∃ x : CVec n, ν x = 1 ∧ r = ‖φ x‖}

/-- Maximum form of the dual functional norm over unit vectors. -/
def IsMaxDualUnitFunctionalNormValue {n : ℕ} (ν : CVec n → ℝ)
    (φ : CVec n → ℂ) (d : ℝ) : Prop :=
  d ∈ DualUnitFunctionalNormSet ν φ ∧
    ∀ r : ℝ, r ∈ DualUnitFunctionalNormSet ν φ → r ≤ d

/-- Values `|φ x| / ||x||` attained by a linear functional on nonzero vectors. -/
def DualNonzeroFunctionalRatioSet {n : ℕ} (ν : CVec n → ℝ)
    (φ : CVec n → ℂ) : Set ℝ :=
  {r | ∃ x : CVec n, x ≠ 0 ∧ r = ‖φ x‖ / ν x}

/-- Maximum form of the dual functional norm over nonzero-vector ratios. -/
def IsMaxDualNonzeroFunctionalRatioValue {n : ℕ} (ν : CVec n → ℝ)
    (φ : CVec n → ℂ) (d : ℝ) : Prop :=
  d ∈ DualNonzeroFunctionalRatioSet ν φ ∧
    ∀ r : ℝ, r ∈ DualNonzeroFunctionalRatioSet ν φ → r ≤ d

theorem isDualFunctionalNormValue_of_isMaxDualUnitFunctionalNormValue
    {n : ℕ} {ν : CVec n → ℝ} {φ : CVec n → ℂ} {d : ℝ}
    (hν : IsComplexVectorNorm ν) (hφ : IsComplexLinearForm φ)
    (hmax : IsMaxDualUnitFunctionalNormValue ν φ d) :
    IsDualFunctionalNormValue ν φ d := by
  refine ⟨hφ, ?_, ?_⟩
  · intro x
    by_cases hxzero : x = 0
    · have hleft : ‖φ x‖ = 0 := by
        rw [hxzero, hφ.map_zero, norm_zero]
      have hright : d * ν x = 0 := by
        have hxnorm : ν x = 0 := (hν.eq_zero_iff x).mpr hxzero
        rw [hxnorm, mul_zero]
      rw [hleft, hright]
    · have hxnorm_ne : ν x ≠ 0 := by
        intro hxnorm
        exact hxzero ((hν.eq_zero_iff x).mp hxnorm)
      have hxnorm_pos : 0 < ν x :=
        lt_of_le_of_ne (hν.nonneg x) (Ne.symm hxnorm_ne)
      let u : CVec n := complexVecSMul (((ν x)⁻¹ : ℝ) : ℂ) x
      have hinv_nonneg : 0 ≤ (ν x)⁻¹ := inv_nonneg.mpr (hν.nonneg x)
      have hu_unit : ν u = 1 := by
        dsimp [u]
        rw [hν.smul, Complex.norm_of_nonneg hinv_nonneg]
        field_simp [ne_of_gt hxnorm_pos]
      have humem : ‖φ u‖ ∈ DualUnitFunctionalNormSet ν φ :=
        ⟨u, hu_unit, rfl⟩
      have hmax_le : ‖φ u‖ ≤ d := hmax.2 ‖φ u‖ humem
      have hscaled_abs : |ν x|⁻¹ * ‖φ x‖ ≤ d := by
        simpa [u, hφ.map_smul] using hmax_le
      have hscaled : (ν x)⁻¹ * ‖φ x‖ ≤ d := by
        simpa [abs_of_nonneg (hν.nonneg x)] using hscaled_abs
      have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt hxnorm_pos)
      calc
        ‖φ x‖ = ν x * ((ν x)⁻¹ * ‖φ x‖) := by
          field_simp [ne_of_gt hxnorm_pos]
        _ ≤ ν x * d := hmul
        _ = d * ν x := by ring
  · intro e he
    obtain ⟨x, hxunit, hd⟩ := hmax.1
    have hex := he x
    rw [hxunit, mul_one] at hex
    rw [hd]
    exact hex

theorem isMaxDualNonzeroFunctionalRatioValue_of_isMaxDualUnitFunctionalNormValue
    {n : ℕ} {ν : CVec n → ℝ} {φ : CVec n → ℂ} {d : ℝ}
    (hν : IsComplexVectorNorm ν) (hφ : IsComplexLinearForm φ)
    (hmax : IsMaxDualUnitFunctionalNormValue ν φ d) :
    IsMaxDualNonzeroFunctionalRatioValue ν φ d := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxunit, hd⟩ := hmax.1
    have hxne : x ≠ 0 := by
      intro hxzero
      have hxnorm : ν x = 0 := (hν.eq_zero_iff x).mpr hxzero
      rw [hxunit] at hxnorm
      norm_num at hxnorm
    refine ⟨x, hxne, ?_⟩
    rw [hd, hxunit]
    ring
  · intro r hr
    obtain ⟨x, hxne, hr⟩ := hr
    have hxnorm_ne : ν x ≠ 0 := by
      intro hxnorm
      exact hxne ((hν.eq_zero_iff x).mp hxnorm)
    have hxnorm_pos : 0 < ν x :=
      lt_of_le_of_ne (hν.nonneg x) (Ne.symm hxnorm_ne)
    let u : CVec n := complexVecSMul (((ν x)⁻¹ : ℝ) : ℂ) x
    have hinv_nonneg : 0 ≤ (ν x)⁻¹ := inv_nonneg.mpr (hν.nonneg x)
    have hu_unit : ν u = 1 := by
      dsimp [u]
      rw [hν.smul, Complex.norm_of_nonneg hinv_nonneg]
      field_simp [ne_of_gt hxnorm_pos]
    have humem : ‖φ u‖ ∈ DualUnitFunctionalNormSet ν φ :=
      ⟨u, hu_unit, rfl⟩
    have hmax_le : ‖φ u‖ ≤ d := hmax.2 ‖φ u‖ humem
    have hscaled_abs : |ν x|⁻¹ * ‖φ x‖ ≤ d := by
      simpa [u, hφ.map_smul] using hmax_le
    have hscaled : (ν x)⁻¹ * ‖φ x‖ ≤ d := by
      simpa [abs_of_nonneg (hν.nonneg x)] using hscaled_abs
    rw [hr]
    calc
      ‖φ x‖ / ν x = (ν x)⁻¹ * ‖φ x‖ := by ring
      _ ≤ d := hscaled

theorem isMaxDualUnitFunctionalNormValue_of_isMaxDualNonzeroFunctionalRatioValue
    {n : ℕ} {ν : CVec n → ℝ} {φ : CVec n → ℂ} {d : ℝ}
    (hν : IsComplexVectorNorm ν) (hφ : IsComplexLinearForm φ)
    (hmax : IsMaxDualNonzeroFunctionalRatioValue ν φ d) :
    IsMaxDualUnitFunctionalNormValue ν φ d := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hxne, hd⟩ := hmax.1
    have hxnorm_ne : ν x ≠ 0 := by
      intro hxnorm
      exact hxne ((hν.eq_zero_iff x).mp hxnorm)
    have hxnorm_pos : 0 < ν x :=
      lt_of_le_of_ne (hν.nonneg x) (Ne.symm hxnorm_ne)
    let u : CVec n := complexVecSMul (((ν x)⁻¹ : ℝ) : ℂ) x
    have hinv_nonneg : 0 ≤ (ν x)⁻¹ := inv_nonneg.mpr (hν.nonneg x)
    have hu_unit : ν u = 1 := by
      dsimp [u]
      rw [hν.smul, Complex.norm_of_nonneg hinv_nonneg]
      field_simp [ne_of_gt hxnorm_pos]
    refine ⟨u, hu_unit, ?_⟩
    have hu_norm_abs : ‖φ u‖ = |ν x|⁻¹ * ‖φ x‖ := by
      simp [u, hφ.map_smul]
    have hu_norm : ‖φ u‖ = (ν x)⁻¹ * ‖φ x‖ := by
      simpa [abs_of_nonneg (hν.nonneg x)] using hu_norm_abs
    rw [hu_norm, hd]
    ring
  · intro r hr
    obtain ⟨x, hxunit, hr⟩ := hr
    have hxne : x ≠ 0 := by
      intro hxzero
      have hxnorm : ν x = 0 := (hν.eq_zero_iff x).mpr hxzero
      rw [hxunit] at hxnorm
      norm_num at hxnorm
    have hratio_mem : ‖φ x‖ / ν x ∈ DualNonzeroFunctionalRatioSet ν φ :=
      ⟨x, hxne, rfl⟩
    have hratio_le := hmax.2 (‖φ x‖ / ν x) hratio_mem
    rw [hr]
    rw [hxunit, div_one] at hratio_le
    exact hratio_le

theorem isMaxDualNonzeroFunctionalRatioValue_iff_unitValue
    {n : ℕ} {ν : CVec n → ℝ} {φ : CVec n → ℂ} {d : ℝ}
    (hν : IsComplexVectorNorm ν) (hφ : IsComplexLinearForm φ) :
    IsMaxDualNonzeroFunctionalRatioValue ν φ d ↔
      IsMaxDualUnitFunctionalNormValue ν φ d := by
  constructor
  · exact isMaxDualUnitFunctionalNormValue_of_isMaxDualNonzeroFunctionalRatioValue
      hν hφ
  · exact isMaxDualNonzeroFunctionalRatioValue_of_isMaxDualUnitFunctionalNormValue
      hν hφ

lemma dualFunctionalNormValue_nonneg_of_nonempty
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν) (hn : 0 < n)
    {φ : CVec n → ℂ} {d : ℝ}
    (hφd : IsDualFunctionalNormValue ν φ d) :
    0 ≤ d := by
  obtain ⟨u, hu_unit⟩ := exists_unit_complexVectorNorm hν hn
  have hbound := hφd.bound u
  rw [hu_unit, mul_one] at hbound
  exact le_trans (norm_nonneg (φ u)) hbound
namespace NormedCVec

variable {n : ℕ} {ν : CVec n → ℝ}


/-- Hahn-Banach norming functional for a unit vector in the abstract norm `ν`. -/
theorem exists_normingFunctionalAt_of_unit_vector (hν : IsComplexVectorNorm ν)
    {x : CVec n} (hx : ν x = 1) :
    ∃ φ : CVec n → ℂ, IsNormingFunctionalAt ν x φ := by
  letI : NormedAddCommGroup (NormedCVec n ν) := normedAddCommGroup hν
  letI : Module ℂ (NormedCVec n ν) :=
    (NormedCVec.equiv n ν).module ℂ
  letI : NormedSpace ℂ (NormedCVec n ν) :=
    NormedSpace.ofCore (𝕜 := ℂ) (normedSpaceCore hν)
  let x' : NormedCVec n ν := ⟨x⟩
  have hxnorm : ‖x'‖ ≠ 0 := by
    change ν x ≠ 0
    rw [hx]
    norm_num
  obtain ⟨g, hg_norm, hgx⟩ := exists_dual_vector ℂ x' hxnorm
  refine ⟨fun v => g ⟨v⟩, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro u v
      change g ⟨complexVecAdd u v⟩ = g ⟨u⟩ + g ⟨v⟩
      have hwrap : (⟨complexVecAdd u v⟩ : NormedCVec n ν) =
          (⟨u⟩ : NormedCVec n ν) + (⟨v⟩ : NormedCVec n ν) := by
        ext i
        rfl
      rw [hwrap]
      exact map_add g ⟨u⟩ ⟨v⟩
    · intro a v
      change g ⟨complexVecSMul a v⟩ = a * g ⟨v⟩
      have hwrap : (⟨complexVecSMul a v⟩ : NormedCVec n ν) =
          a • (⟨v⟩ : NormedCVec n ν) := by
        ext i
        simp [complexVecSMul]
      rw [hwrap]
      exact map_smul g a ⟨v⟩
  · intro v
    have hle := g.le_opNorm (⟨v⟩ : NormedCVec n ν)
    rw [hg_norm] at hle
    change ‖g ⟨v⟩‖ ≤ 1 * ν v at hle
    simpa using hle
  · change g ⟨x⟩ = 1
    change g x' = ((ν x : ℝ) : ℂ) at hgx
    dsimp [x'] at hgx
    rw [hx] at hgx
    simpa using hgx

end NormedCVec


/-- A norming functional at a unit vector has dual functional norm value `1`.
    This records the least-bound form of Higham's equation (6.3). -/
theorem isDualFunctionalNormValue_one_of_normingFunctionalAt
    {n : ℕ} {ν : CVec n → ℝ} {x : CVec n} {φ : CVec n → ℂ}
    (hx : ν x = 1) (hφ : IsNormingFunctionalAt ν x φ) :
    IsDualFunctionalNormValue ν φ 1 := by
  refine ⟨hφ.linear, ?_, ?_⟩
  · intro v
    simpa using hφ.bound v
  · intro e he
    have h := he x
    rw [hφ.value, norm_one, hx] at h
    simpa using h

/-- Hahn-Banach produces a unit dual functional norm value for every unit vector
    in an abstract source-facing complex vector norm. -/
theorem exists_dualFunctionalNormValue_one_of_unit_vector
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    {x : CVec n} (hx : ν x = 1) :
    ∃ φ : CVec n → ℂ, IsDualFunctionalNormValue ν φ 1 ∧ φ x = 1 := by
  obtain ⟨φ, hφ⟩ := NormedCVec.exists_normingFunctionalAt_of_unit_vector hν hx
  exact ⟨φ, isDualFunctionalNormValue_one_of_normingFunctionalAt hx hφ, hφ.value⟩

set_option linter.unusedTactic false in
/-- Hahn-Banach produces a unit dual functional that attains the norm of any
    positive-norm vector in an abstract source-facing complex vector norm. -/
theorem exists_dualFunctionalNormValue_one_of_pos_vector
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν)
    {y : CVec n} (hy : 0 < ν y) :
    ∃ φ : CVec n → ℂ, IsDualFunctionalNormValue ν φ 1 ∧
      φ y = (ν y : ℂ) := by
  -- Preserve frozen auxiliary names across the semantic module split.
  run_tac do
    let ngen ← Lean.getDeclNGen
    Lean.setDeclNGen { ngen with idx := 2 }
  let u : CVec n := complexVecSMul (((ν y)⁻¹ : ℝ) : ℂ) y
  have hu : ν u = 1 := by
    dsimp [u]
    rw [hν.smul, Complex.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hy))]
    field_simp [ne_of_gt hy]
  obtain ⟨φ, hφ, hφu⟩ := exists_dualFunctionalNormValue_one_of_unit_vector hν hu
  refine ⟨φ, hφ, ?_⟩
  have hy_repr : y = complexVecSMul ((ν y : ℝ) : ℂ) u := by
    ext i
    simp [u, complexVecSMul]
    field_simp [ne_of_gt hy]
  have hy_eval : φ y = φ (complexVecSMul ((ν y : ℝ) : ℂ) u) := by
    exact congrArg φ hy_repr
  calc
    φ y = φ (complexVecSMul ((ν y : ℝ) : ℂ) u) := hy_eval
    _ = (((ν y : ℝ) : ℂ)) * φ u := hφ.linear.map_smul (((ν y : ℝ) : ℂ)) u
    _ = (ν y : ℂ) := by rw [hφu, mul_one]

/-- For nonempty dimension, the complex vector 1-norm is attained by a unit
    infinity-norm phase vector in the dual pairing. -/
lemma exists_unit_infNorm_pairing_oneNorm {n : ℕ} (hn : 0 < n) (z : CVec n) :
    ∃ v : CVec n,
      complexVecInfNorm v = 1 ∧
        ‖∑ i : Fin n, star (v i) * z i‖ = complexVecOneNorm z := by
  classical
  choose c hc using fun i : Fin n => Complex.exists_norm_eq_mul_self (z i)
  let v : CVec n := fun i => star (c i)
  refine ⟨v, ?_, ?_⟩
  · apply le_antisymm
    · apply complexVecInfNorm_le_of_coord_le _ zero_le_one
      intro i
      simp [v, (hc i).1]
    · let j0 : Fin n := ⟨0, hn⟩
      have hcoord := complexVecInfNorm_coord_le v j0
      have hvj : ‖v j0‖ = 1 := by simp [v, (hc j0).1]
      simpa [hvj] using hcoord
  · have hpair :
        (∑ i : Fin n, star (v i) * z i) =
          ((∑ i : Fin n, ‖z i‖) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hi := (hc i).2
      rw [hi]
      simp [v]
    have hsum_nonneg : 0 ≤ ∑ i : Fin n, ‖z i‖ :=
      Finset.sum_nonneg (fun i _ => norm_nonneg (z i))
    rw [hpair]
    simpa [complexVecOneNorm] using Complex.norm_of_nonneg hsum_nonneg
end NumStability
