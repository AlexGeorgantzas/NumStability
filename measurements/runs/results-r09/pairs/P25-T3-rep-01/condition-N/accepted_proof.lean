import HighamBench.P25Definitions

namespace HighamBench

open scoped BigOperators Topology

private lemma p25_seriesBound_of_pow_le
    {E : Type*} [NormedRing E] [NormOneClass E]
    [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (r : ℝ)
    (hs : Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k))
    (hpow : ∀ k : ℕ, c k ≠ 0 → ‖A ^ k‖ ≤ r ^ k) :
    P25SeriesBound c A r := by
  have hterm : ∀ k : ℕ, ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k := by
    intro k
    by_cases hk : c k = 0
    · simp [hk]
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hpow k hk) (norm_nonneg _)
  constructor
  · exact Summable.of_norm_bounded hs hterm
  · exact tsum_of_norm_bounded hs.hasSum hterm

private lemma p25_norm_pow_le_of_add
    {E : Type*} [NormedRing E] [NormOneClass E]
    (A : E) (r : ℝ) (hr : 0 ≤ r)
    (a b m n k : ℕ) (hk : k = a * m + b * n)
    (ha : ‖A ^ a‖ ≤ r ^ a) (hb : ‖A ^ b‖ ≤ r ^ b) :
    ‖A ^ k‖ ≤ r ^ k := by
  have ham : ‖(A ^ a) ^ m‖ ≤ (r ^ a) ^ m :=
    (norm_pow_le (A ^ a) m).trans
      (pow_le_pow_left₀ (norm_nonneg (A ^ a)) ha m)
  have hbn : ‖(A ^ b) ^ n‖ ≤ (r ^ b) ^ n :=
    (norm_pow_le (A ^ b) n).trans
      (pow_le_pow_left₀ (norm_nonneg (A ^ b)) hb n)
  calc
    ‖A ^ k‖ = ‖(A ^ a) ^ m * (A ^ b) ^ n‖ := by
      rw [hk, pow_add, pow_mul, pow_mul]
    _ ≤ ‖(A ^ a) ^ m‖ * ‖(A ^ b) ^ n‖ := norm_mul_le _ _
    _ ≤ (r ^ a) ^ m * (r ^ b) ^ n :=
      mul_le_mul ham hbn (norm_nonneg _) (by positivity)
    _ = r ^ k := by rw [hk, pow_add, pow_mul, pow_mul]

private lemma p25_coin_representation (p k : ℕ) (hp : 0 < p)
    (hk : p * (p - 1) ≤ k) :
    ∃ m n : ℕ, k = p * m + (p + 1) * n := by
  let q := k / p
  let s := k % p
  have hq : p - 1 ≤ q := by
    apply (Nat.le_div_iff_mul_le hp).2
    simpa [Nat.mul_comm] using hk
  have hslt : s < p := Nat.mod_lt k hp
  have hs : s ≤ p - 1 := by omega
  have hsq : s ≤ q := hs.trans hq
  refine ⟨q - s, s, ?_⟩
  have hsum : s + (q - s) = q := Nat.add_sub_of_le hsq
  calc
    k = p * q + s := (Nat.div_add_mod k p).symm
    _ = p * (s + (q - s)) + s := by rw [hsum]
    _ = p * (q - s) + (p + 1) * s := by ring

/-- P25-T3: the ordinary and even power-series bounds of Theorem 4.2. -/
theorem p25_t3_theorem4_2
    {E : Type*} [NormedRing E] [NormOneClass E]
    [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (p ℓ : ℕ) (hp : 0 < p)
    (hcutoff : ∀ k < ℓ, c k = 0) :
    (∀ r : ℝ, 0 ≤ r → p * (p - 1) ≤ ℓ →
      ‖A ^ p‖ ≤ r ^ p →
      ‖A ^ (p + 1)‖ ≤ r ^ (p + 1) →
      Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k) →
      P25SeriesBound c A r) ∧
    ((∀ k : ℕ, ¬Even k → c k = 0) →
      ∀ r : ℝ, 0 ≤ r → 2 * p * (p - 1) ≤ ℓ →
        ‖A ^ (2 * p)‖ ≤ r ^ (2 * p) →
        ‖A ^ (2 * (p + 1))‖ ≤ r ^ (2 * (p + 1)) →
        Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k) →
        P25SeriesBound c A r) := by
  -- PROOF_START P25-T3-H001
  constructor
  · intro r hr hℓ hap hap1 hs
    apply p25_seriesBound_of_pow_le c A r hs
    intro k hck
    have hkℓ : ℓ ≤ k := by
      by_contra hnot
      exact hck (hcutoff k (by omega))
    obtain ⟨m, n, hrep⟩ :=
      p25_coin_representation p k hp ((hℓ.trans hkℓ))
    exact p25_norm_pow_le_of_add A r hr p (p + 1) m n k hrep hap hap1
  · intro heven r hr hℓ ha2p ha2p2 hs
    apply p25_seriesBound_of_pow_le c A r hs
    intro k hck
    have hkℓ : ℓ ≤ k := by
      by_contra hnot
      exact hck (hcutoff k (by omega))
    have hklarge : 2 * (p * (p - 1)) ≤ k := by
      simpa [mul_assoc] using hℓ.trans hkℓ
    have hkeven : Even k := by
      by_contra hnot
      exact hck (heven k hnot)
    obtain ⟨j, hj⟩ := hkeven
    have hkj : k = 2 * j := by omega
    have hjlarge : p * (p - 1) ≤ j := by omega
    obtain ⟨m, n, hjrep⟩ := p25_coin_representation p j hp hjlarge
    have hrep : k = (2 * p) * m + (2 * (p + 1)) * n := by
      rw [hkj, hjrep]
      ring
    exact p25_norm_pow_le_of_add A r hr (2 * p) (2 * (p + 1)) m n k
      hrep ha2p ha2p2

end HighamBench
