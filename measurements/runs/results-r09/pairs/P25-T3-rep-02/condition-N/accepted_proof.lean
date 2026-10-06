import HighamBench.P25Definitions

namespace HighamBench

open scoped BigOperators Topology

private lemma p25_nat_decompose (p k : ℕ) (hp : 0 < p)
    (hk : p * (p - 1) ≤ k) :
    ∃ m n : ℕ, k = p * m + (p + 1) * n := by
  let q := k / p
  let s := k % p
  have hq : p - 1 ≤ q := by
    apply (Nat.le_div_iff_mul_le hp).2
    simpa [q, Nat.mul_comm] using hk
  have hslt : s < p := by
    exact Nat.mod_lt k hp
  have hsq : s ≤ q := by omega
  refine ⟨q - s, s, ?_⟩
  have hdiv : k = p * q + s := by
    exact (Nat.div_add_mod k p).symm
  calc
    k = p * q + s := hdiv
    _ = p * ((q - s) + s) + s := by rw [Nat.sub_add_cancel hsq]
    _ = p * (q - s) + (p + 1) * s := by
      simp [Nat.mul_add, Nat.add_mul, add_assoc]

private lemma p25_norm_pow_le_of_decompose
    {E : Type*} [NormedRing E] [NormOneClass E]
    (A : E) (r : ℝ) (a b m n k : ℕ) (hr : 0 ≤ r)
    (ha : ‖A ^ a‖ ≤ r ^ a) (hb : ‖A ^ b‖ ≤ r ^ b)
    (hk : k = a * m + b * n) :
    ‖A ^ k‖ ≤ r ^ k := by
  have ham : ‖(A ^ a) ^ m‖ ≤ (r ^ a) ^ m :=
    (norm_pow_le (A ^ a) m).trans (pow_le_pow_left₀ (norm_nonneg _) ha m)
  have hbn : ‖(A ^ b) ^ n‖ ≤ (r ^ b) ^ n :=
    (norm_pow_le (A ^ b) n).trans (pow_le_pow_left₀ (norm_nonneg _) hb n)
  rw [hk, pow_add, pow_mul, pow_mul]
  calc
    ‖(A ^ a) ^ m * (A ^ b) ^ n‖ ≤
        ‖(A ^ a) ^ m‖ * ‖(A ^ b) ^ n‖ := norm_mul_le _ _
    _ ≤ (r ^ a) ^ m * (r ^ b) ^ n :=
      mul_le_mul ham hbn (norm_nonneg _) (pow_nonneg (pow_nonneg hr _) _)
    _ = r ^ (a * m + b * n) := by simp [pow_add, pow_mul]

private lemma p25_series_bound_of_pow_le
    {E : Type*} [NormedRing E] [NormOneClass E]
    [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (r : ℝ)
    (hs : Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k))
    (hpow : ∀ k : ℕ, c k ≠ 0 → ‖A ^ k‖ ≤ r ^ k) :
    P25SeriesBound c A r := by
  have hmajor : ∀ k : ℕ, ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k := by
    intro k
    by_cases hc : c k = 0
    · simp [hc]
    · simpa only [norm_smul] using
        mul_le_mul_of_nonneg_left (hpow k hc) (norm_nonneg (c k))
  refine ⟨hs.of_norm_bounded hmajor, ?_⟩
  exact tsum_of_norm_bounded hs.hasSum hmajor

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
  · intro r hr hthreshold hap hap1 hs
    apply p25_series_bound_of_pow_le c A r hs
    intro k hck
    have hkℓ : ℓ ≤ k := by
      by_contra hk
      exact hck (hcutoff k (Nat.lt_of_not_ge hk))
    obtain ⟨m, n, hkmn⟩ :=
      p25_nat_decompose p k hp (hthreshold.trans hkℓ)
    exact p25_norm_pow_le_of_decompose A r p (p + 1) m n k
      hr hap hap1 hkmn
  · intro heven r hr hthreshold h2p h2p2 hs
    apply p25_series_bound_of_pow_le c A r hs
    intro k hck
    have hkℓ : ℓ ≤ k := by
      by_contra hk
      exact hck (hcutoff k (Nat.lt_of_not_ge hk))
    have hkeven : Even k := by
      by_contra hk
      exact hck (heven k hk)
    rcases hkeven with ⟨j, hj⟩
    have hjthreshold : p * (p - 1) ≤ j := by
      have hkthreshold := hthreshold.trans hkℓ
      have htwo : 2 * (p * (p - 1)) ≤ 2 * j := by
        calc
          2 * (p * (p - 1)) = 2 * p * (p - 1) := by simp [mul_assoc]
          _ ≤ k := hkthreshold
          _ = 2 * j := by simpa only [two_mul] using hj
      exact le_of_mul_le_mul_left htwo (by norm_num)
    obtain ⟨m, n, hjmn⟩ := p25_nat_decompose p j hp hjthreshold
    have hkmn : j + j = (2 * p) * m + (2 * (p + 1)) * n := by
      calc
        j + j = 2 * j := (two_mul j).symm
        _ = 2 * (p * m + (p + 1) * n) := by rw [hjmn]
        _ = (2 * p) * m + (2 * (p + 1)) * n := by ring
    simpa only [hj] using
      p25_norm_pow_le_of_decompose A r (2 * p) (2 * (p + 1)) m n (j + j)
        hr h2p h2p2 hkmn

end HighamBench
