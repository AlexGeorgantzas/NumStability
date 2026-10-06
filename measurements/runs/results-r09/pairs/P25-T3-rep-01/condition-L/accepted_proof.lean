import HighamBench.P25Definitions

namespace HighamBench

open scoped BigOperators Topology

private lemma p25_coin_decomp {p k : ℕ} (hp : 0 < p)
    (hk : p * (p - 1) ≤ k) :
    ∃ a b : ℕ, k = p * a + (p + 1) * b := by
  have hq : p - 1 ≤ k / p := by
    rw [Nat.le_div_iff_mul_le hp]
    simpa [Nat.mul_comm] using hk
  have hb : k % p ≤ p - 1 := by
    have := Nat.mod_lt k hp
    omega
  have hbq : k % p ≤ k / p := hb.trans hq
  refine ⟨k / p - k % p, k % p, ?_⟩
  calc
    k = p * (k / p) + k % p := by
      simpa using (Nat.div_add_mod k p).symm
    _ = p * (k / p - k % p) + (p + 1) * (k % p) := by
      rw [Nat.add_mul, one_mul, ← Nat.add_assoc, ← Nat.mul_add,
        Nat.sub_add_cancel hbq]

private lemma p25_power_bound_two
    {E : Type*} [NormedRing E] [NormOneClass E]
    (A : E) (m n a b k : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hk : k = m * a + n * b)
    (hm : ‖A ^ m‖ ≤ r ^ m) (hn : ‖A ^ n‖ ≤ r ^ n) :
    ‖A ^ k‖ ≤ r ^ k := by
  subst k
  calc
    ‖A ^ (m * a + n * b)‖ = ‖(A ^ m) ^ a * (A ^ n) ^ b‖ := by
      rw [pow_add, pow_mul, pow_mul]
    _ ≤ ‖(A ^ m) ^ a‖ * ‖(A ^ n) ^ b‖ := norm_mul_le _ _
    _ ≤ ‖A ^ m‖ ^ a * ‖A ^ n‖ ^ b := by
      gcongr <;> apply norm_pow_le
    _ ≤ (r ^ m) ^ a * (r ^ n) ^ b := by
      gcongr
    _ = r ^ (m * a + n * b) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]

private lemma p25_series_bound_of_power_le
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
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hpow k hc) (norm_nonneg _)
  have hnorm : Summable (fun k : ℕ ↦ ‖c k • A ^ k‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hmajor hs
  refine ⟨Summable.of_norm hnorm, ?_⟩
  unfold p25SeriesValue p25AbsoluteSeries
  calc
    ‖∑' k : ℕ, c k • A ^ k‖ ≤ ∑' k : ℕ, ‖c k • A ^ k‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, ‖c k‖ * r ^ k := hnorm.tsum_le_tsum hmajor hs

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
  · intro r hr hlarge hAp hAp1 hs
    apply p25_series_bound_of_power_le c A r hs
    intro k hck
    have hkℓ : ℓ ≤ k := by
      by_contra hk
      exact hck (hcutoff k (Nat.lt_of_not_ge hk))
    obtain ⟨a, b, hab⟩ :=
      p25_coin_decomp hp (hlarge.trans hkℓ)
    exact p25_power_bound_two A p (p + 1) a b k r hr hab hAp hAp1
  · intro heven r hr hlarge hA2p hA2p2 hs
    apply p25_series_bound_of_power_le c A r hs
    intro k hck
    have hkℓ : ℓ ≤ k := by
      by_contra hk
      exact hck (hcutoff k (Nat.lt_of_not_ge hk))
    have hklarge : 2 * p * (p - 1) ≤ k := hlarge.trans hkℓ
    have hkeven : Even k := by
      by_contra hkodd
      exact hck (heven k hkodd)
    obtain ⟨j, hj⟩ := even_iff_exists_two_mul.mp hkeven
    have hjlarge : p * (p - 1) ≤ j := by
      have hdouble : 2 * (p * (p - 1)) ≤ 2 * j := by
        calc
          2 * (p * (p - 1)) = 2 * p * (p - 1) := by
            rw [Nat.mul_assoc]
          _ ≤ k := hklarge
          _ = 2 * j := hj
      omega
    obtain ⟨a, b, hab⟩ := p25_coin_decomp hp hjlarge
    apply p25_power_bound_two A (2 * p) (2 * (p + 1)) a b k r hr
    · calc
        k = 2 * j := hj
        _ = (2 * p) * a + (2 * (p + 1)) * b := by
          rw [hab]
          ring
    · exact hA2p
    · exact hA2p2

end HighamBench
