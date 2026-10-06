import HighamBench.P25Definitions

namespace HighamBench

open scoped BigOperators Topology

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
  have index_decomposition :
      ∀ k : ℕ, p * (p - 1) ≤ k →
        ∃ m n : ℕ, k = p * m + (p + 1) * n := by
    intro k hk
    let q := k / p
    let s := k % p
    have hq : p - 1 ≤ q := by
      apply (Nat.le_div_iff_mul_le hp).2
      simpa [mul_comm] using hk
    have hs : s < p := Nat.mod_lt k hp
    have hsq : s ≤ q := by omega
    have hmul : p * s ≤ p * q := Nat.mul_le_mul_left p hsq
    refine ⟨q - s, s, ?_⟩
    have hdiv : s + p * q = k := by
      simpa [q, s] using Nat.mod_add_div k p
    calc
      k = s + p * q := hdiv.symm
      _ = p * (q - s) + (p + 1) * s := by
        rw [Nat.mul_sub_left_distrib, add_mul]
        omega

  have norm_power_bound :
      ∀ (B : E) (s : ℝ) (k : ℕ), 0 ≤ s →
        p * (p - 1) ≤ k →
        ‖B ^ p‖ ≤ s ^ p →
        ‖B ^ (p + 1)‖ ≤ s ^ (p + 1) →
        ‖B ^ k‖ ≤ s ^ k := by
    intro B s k hs hk hBp hBq
    obtain ⟨m, n, rfl⟩ := index_decomposition k hk
    calc
      ‖B ^ (p * m + (p + 1) * n)‖ =
          ‖(B ^ p) ^ m * (B ^ (p + 1)) ^ n‖ := by
            rw [pow_add, pow_mul, pow_mul]
      _ ≤ ‖(B ^ p) ^ m‖ * ‖(B ^ (p + 1)) ^ n‖ := norm_mul_le _ _
      _ ≤ ‖B ^ p‖ ^ m * ‖B ^ (p + 1)‖ ^ n := by
            exact mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
              (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      _ ≤ (s ^ p) ^ m * (s ^ (p + 1)) ^ n := by
            exact mul_le_mul
              (pow_le_pow_left₀ (norm_nonneg _) hBp m)
              (pow_le_pow_left₀ (norm_nonneg _) hBq n)
              (pow_nonneg (norm_nonneg _) _)
              (pow_nonneg (pow_nonneg hs _) _)
      _ = s ^ (p * m + (p + 1) * n) := by
            rw [← pow_mul, ← pow_mul, ← pow_add]

  have series_bound_of_power_bound :
      ∀ (r : ℝ), 0 ≤ r →
        (∀ k : ℕ, c k ≠ 0 → ‖A ^ k‖ ≤ r ^ k) →
        Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k) →
        P25SeriesBound c A r := by
    intro r hr hpower hs
    have hterm : ∀ k : ℕ,
        ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k := by
      intro k
      by_cases hck : c k = 0
      · simp [hck]
      · simpa only [norm_smul] using
          mul_le_mul_of_nonneg_left (hpower k hck) (norm_nonneg (c k))
    have hnorm : Summable (fun k : ℕ ↦ ‖c k • A ^ k‖) :=
      Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hterm hs
    refine ⟨Summable.of_norm hnorm, ?_⟩
    calc
      ‖p25SeriesValue c A‖ ≤ ∑' k : ℕ, ‖c k • A ^ k‖ :=
        norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' k : ℕ, ‖c k‖ * r ^ k :=
        Summable.tsum_le_tsum hterm hnorm hs
      _ = p25AbsoluteSeries c r := rfl

  constructor
  · intro r hr hthreshold hAp hAp1 hs
    apply series_bound_of_power_bound r hr ?_ hs
    intro k hck
    have hkell : ℓ ≤ k := by
      by_contra hnot
      have hklt : k < ℓ := Nat.lt_of_not_ge hnot
      exact hck (hcutoff k hklt)
    exact norm_power_bound A r k hr
      (hthreshold.trans hkell) hAp hAp1
  · intro heven r hr hthreshold hA2p hA2p2 hs
    apply series_bound_of_power_bound r hr ?_ hs
    intro k hck
    have hkell : ℓ ≤ k := by
      by_contra hnot
      have hklt : k < ℓ := Nat.lt_of_not_ge hnot
      exact hck (hcutoff k hklt)
    have hkeven : Even k := by
      by_contra hkodd
      exact hck (heven k hkodd)
    obtain ⟨j, rfl⟩ := even_iff_exists_two_mul.mp hkeven
    have hj : p * (p - 1) ≤ j := by
      have htwice : 2 * (p * (p - 1)) ≤ 2 * j := by
        simpa only [mul_assoc] using hthreshold.trans hkell
      exact Nat.le_of_mul_le_mul_left htwice (by omega)
    have hfirst : ‖(A ^ 2) ^ p‖ ≤ (r ^ 2) ^ p := by
      simpa only [← pow_mul] using hA2p
    have hsecond : ‖(A ^ 2) ^ (p + 1)‖ ≤ (r ^ 2) ^ (p + 1) := by
      simpa only [← pow_mul] using hA2p2
    have hbound := norm_power_bound (A ^ 2) (r ^ 2) j
      (sq_nonneg r) hj hfirst hsecond
    simpa only [← pow_mul] using hbound

end HighamBench
