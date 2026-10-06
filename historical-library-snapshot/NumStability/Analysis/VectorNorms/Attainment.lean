-- Analysis/VectorNorms/Attainment.lean
--
-- Finite-dimensional attainment results for complex-vector norms.

import NumStability.Analysis.VectorNorms.Basic

/-!
# Complex-vector norm attainment

Packages compactness and extremizer results showing that the relevant
finite-dimensional vector-norm suprema are attained.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Ratios `νnum x / νden x` over nonzero vectors.  This is the finite
    vector-norm ratio carrier used in Higham equation (6.14). -/
def VectorNormRatioSet {n : ℕ} (νnum νden : CVec n → ℝ) : Set ℝ :=
  {r | ∃ x : CVec n, x ≠ 0 ∧ r = νnum x / νden x}

/-- Maximum value of vector-norm ratios over nonzero vectors. -/
def IsMaxVectorNormRatioValue {n : ℕ} (νnum νden : CVec n → ℝ)
    (c : ℝ) : Prop :=
  c ∈ VectorNormRatioSet νnum νden ∧
    ∀ r : ℝ, r ∈ VectorNormRatioSet νnum νden → r ≤ c

lemma isMaxVectorNormRatioValue_nonneg {n : ℕ} {νnum νden : CVec n → ℝ}
    (hnum : IsComplexVectorNorm νnum) (hden : IsComplexVectorNorm νden)
    {c : ℝ} (hmax : IsMaxVectorNormRatioValue νnum νden c) :
    0 ≤ c := by
  obtain ⟨x, hxne, hc⟩ := hmax.1
  rw [hc]
  exact div_nonneg (hnum.nonneg x) (hden.nonneg x)

lemma isMaxVectorNormRatioValue_pos {n : ℕ} {νnum νden : CVec n → ℝ}
    (hnum : IsComplexVectorNorm νnum) (hden : IsComplexVectorNorm νden)
    {c : ℝ} (hmax : IsMaxVectorNormRatioValue νnum νden c) :
    0 < c := by
  obtain ⟨x, hxne, hc⟩ := hmax.1
  have hnum_pos : 0 < νnum x := by
    have hne : νnum x ≠ 0 := by
      intro hx
      exact hxne ((hnum.eq_zero_iff x).mp hx)
    exact lt_of_le_of_ne (hnum.nonneg x) (Ne.symm hne)
  have hden_pos : 0 < νden x := by
    have hne : νden x ≠ 0 := by
      intro hx
      exact hxne ((hden.eq_zero_iff x).mp hx)
    exact lt_of_le_of_ne (hden.nonneg x) (Ne.symm hne)
  rw [hc]
  exact div_pos hnum_pos hden_pos

lemma vectorNorm_le_mul_of_isMaxVectorNormRatioValue
    {n : ℕ} {νnum νden : CVec n → ℝ}
    (hnum : IsComplexVectorNorm νnum) (hden : IsComplexVectorNorm νden)
    {c : ℝ} (hmax : IsMaxVectorNormRatioValue νnum νden c)
    (x : CVec n) :
    νnum x ≤ c * νden x := by
  by_cases hxzero : x = 0
  · have hnum_zero : νnum x = 0 := by
      rw [hxzero]
      exact (hnum.eq_zero_iff 0).mpr rfl
    have hden_zero : νden x = 0 := by
      rw [hxzero]
      exact (hden.eq_zero_iff 0).mpr rfl
    rw [hnum_zero, hden_zero, mul_zero]
  · have hden_pos : 0 < νden x := by
      have hne : νden x ≠ 0 := by
        intro hx
        exact hxzero ((hden.eq_zero_iff x).mp hx)
      exact lt_of_le_of_ne (hden.nonneg x) (Ne.symm hne)
    have hmem : νnum x / νden x ∈ VectorNormRatioSet νnum νden :=
      ⟨x, hxzero, rfl⟩
    have hle := hmax.2 (νnum x / νden x) hmem
    rw [div_le_iff₀ hden_pos] at hle
    exact hle

/-- Sharp finite vector-ratio maximum for the monotone half of Higham
    equation (6.4): if `1 <= q <= p`, then
    `max_{x != 0} ||x||_p / ||x||_q = 1`. -/
theorem complexVecLpNorm_ratio_max_one_of_exponent_le
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    IsMaxVectorNormRatioValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal q)) 1 := by
  have hp : 1 ≤ p := hq.trans hqp
  haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  haveI hqFact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hq⟩
  let j : Fin n := ⟨0, hn⟩
  refine ⟨?_, ?_⟩
  · refine ⟨standardBasisCVec j, standardBasisCVec_ne_zero j, ?_⟩
    simp [complexVecLpNorm_standardBasisCVec]
  · intro r hr
    obtain ⟨x, hxne, hr_eq⟩ := hr
    have hνq : IsComplexVectorNorm
        (complexVecLpNorm (n := n) (ENNReal.ofReal q)) :=
      complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal q)
    have hden_pos : 0 < complexVecLpNorm (ENNReal.ofReal q) x := by
      have hne : complexVecLpNorm (ENNReal.ofReal q) x ≠ 0 := by
        intro hx
        exact hxne ((hνq.eq_zero_iff x).mp hx)
      exact lt_of_le_of_ne (hνq.nonneg x) (Ne.symm hne)
    have hle := complexVecLpNorm_le_complexVecLpNorm_of_exponent_le hq hqp x
    rw [hr_eq]
    rw [div_le_iff₀ hden_pos]
    simpa using hle

/-- Sharp finite vector-ratio maximum for the cardinal half of Higham
    equation (6.4): if `1 <= q <= p`, then
    `max_{x != 0} ||x||_q / ||x||_p = n^(1/q - 1/p)`. -/
theorem complexVecLpNorm_ratio_max_card_rpow_of_exponent_le
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hq : 1 ≤ q) (hqp : q ≤ p) :
    IsMaxVectorNormRatioValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal q))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      ((n : ℝ) ^ (q⁻¹ - p⁻¹)) := by
  have hp : 1 ≤ p := hq.trans hqp
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hbase_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · refine ⟨(fun _ : Fin n => (1 : ℂ)), complexVecConstOne_ne_zero hn, ?_⟩
    rw [complexVecLpNorm_const_one_ofReal hq_pos,
      complexVecLpNorm_const_one_ofReal hp_pos]
    exact Real.rpow_sub hbase_pos q⁻¹ p⁻¹
  · intro r hr
    obtain ⟨x, hxne, hr_eq⟩ := hr
    have hνp : IsComplexVectorNorm
        (complexVecLpNorm (n := n) (ENNReal.ofReal p)) := by
      haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
        rw [ENNReal.one_le_ofReal]
        exact hp⟩
      exact complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
    have hden_pos : 0 < complexVecLpNorm (ENNReal.ofReal p) x := by
      have hne : complexVecLpNorm (ENNReal.ofReal p) x ≠ 0 := by
        intro hx
        exact hxne ((hνp.eq_zero_iff x).mp hx)
      exact lt_of_le_of_ne (hνp.nonneg x) (Ne.symm hne)
    have hle :=
      complexVecLpNorm_le_card_rpow_mul_complexVecLpNorm_of_exponent_le hq hqp x
    rw [hr_eq]
    rw [div_le_iff₀ hden_pos]
    simpa using hle
end NumStability
