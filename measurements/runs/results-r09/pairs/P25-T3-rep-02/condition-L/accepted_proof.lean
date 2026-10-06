import HighamBench.P25Definitions

namespace HighamBench

open scoped BigOperators Topology

private lemma p25_nat_decomposition (p k : ℕ) (hp : 0 < p)
    (hk : p * (p - 1) ≤ k) :
    ∃ m n : ℕ, k = p * m + (p + 1) * n := by
  let q := k / p
  let s := k % p
  have hslt : s < p := by
    exact Nat.mod_lt k hp
  have hpq : p - 1 ≤ q := by
    dsimp [q]
    apply (Nat.le_div_iff_mul_le hp).2
    simpa [Nat.mul_comm] using hk
  have hsq : s ≤ q := by omega
  have hmul : p * s ≤ p * q := Nat.mul_le_mul_left p hsq
  refine ⟨q - s, s, ?_⟩
  symm
  calc
    p * (q - s) + (p + 1) * s =
        (p * q - p * s) + (p * s + s) := by
          rw [Nat.mul_sub_left_distrib, Nat.add_mul]
          simp
    _ = p * q + s := by
      rw [← Nat.add_assoc, Nat.sub_add_cancel hmul]
    _ = k := by
      simpa [q, s, Nat.mul_comm] using (Nat.div_add_mod k p)

private lemma p25_norm_pow_le_of_decomposition
    {E : Type*} [NormedRing E] [NormOneClass E]
    (A : E) (r : ℝ) (hr : 0 ≤ r)
    (a b m n : ℕ)
    (ha : ‖A ^ a‖ ≤ r ^ a) (hb : ‖A ^ b‖ ≤ r ^ b) :
    ‖A ^ (a * m + b * n)‖ ≤ r ^ (a * m + b * n) := by
  rw [pow_add, pow_add, pow_mul, pow_mul, pow_mul, pow_mul]
  calc
    ‖(A ^ a) ^ m * (A ^ b) ^ n‖ ≤
        ‖(A ^ a) ^ m‖ * ‖(A ^ b) ^ n‖ := norm_mul_le _ _
    _ ≤ ‖A ^ a‖ ^ m * ‖A ^ b‖ ^ n := by
      gcongr
      · exact norm_pow_le _ _
      · exact norm_pow_le _ _
    _ ≤ (r ^ a) ^ m * (r ^ b) ^ n := by
      exact mul_le_mul
        (pow_le_pow_left₀ (norm_nonneg _) ha m)
        (pow_le_pow_left₀ (norm_nonneg _) hb n)
        (pow_nonneg (norm_nonneg _) n) (pow_nonneg (pow_nonneg hr a) m)

private lemma p25_series_bound_of_termwise
    {E : Type*} [NormedRing E] [NormOneClass E]
    [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (r : ℝ)
    (hsum : Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k))
    (hterm : ∀ k : ℕ, ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k) :
    P25SeriesBound c A r := by
  have hseries : Summable (fun k : ℕ ↦ c k • A ^ k) :=
    hsum.of_norm_bounded hterm
  have hnorm : Summable (fun k : ℕ ↦ ‖c k • A ^ k‖) := by
    apply hsum.of_norm_bounded
    intro k
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hterm k
  refine ⟨hseries, ?_⟩
  calc
    ‖p25SeriesValue c A‖ = ‖∑' k : ℕ, c k • A ^ k‖ := rfl
    _ ≤ ∑' k : ℕ, ‖c k • A ^ k‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, ‖c k‖ * r ^ k := hnorm.tsum_le_tsum hterm hsum
    _ = p25AbsoluteSeries c r := rfl

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
  · intro r hr hthreshold hpbound hsuccbound hsum
    apply p25_series_bound_of_termwise c A r hsum
    intro k
    rw [norm_smul]
    by_cases hk : k < ℓ
    · simp [hcutoff k hk]
    · have hlk : ℓ ≤ k := Nat.le_of_not_gt hk
      have hpk : p * (p - 1) ≤ k := hthreshold.trans hlk
      obtain ⟨m, n, hdecomp⟩ := p25_nat_decomposition p k hp hpk
      have hpow : ‖A ^ k‖ ≤ r ^ k := by
        simpa only [hdecomp] using
          (p25_norm_pow_le_of_decomposition A r hr p (p + 1) m n
            hpbound hsuccbound)
      exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
  · intro heven r hr hthreshold hpbound hsuccbound hsum
    apply p25_series_bound_of_termwise c A r hsum
    intro k
    rw [norm_smul]
    by_cases hk : k < ℓ
    · simp [hcutoff k hk]
    · by_cases hkeven : Even k
      · obtain ⟨j, hj⟩ := hkeven
        have hlk : ℓ ≤ k := Nat.le_of_not_gt hk
        have htwopk : 2 * p * (p - 1) ≤ k := hthreshold.trans hlk
        have hjlarge : p * (p - 1) ≤ j := by
          rw [hj] at htwopk
          have hdouble : 2 * (p * (p - 1)) ≤ 2 * j := by
            simpa [Nat.mul_assoc, two_mul, Nat.add_mul] using htwopk
          omega
        obtain ⟨m, n, hdecomp⟩ := p25_nat_decomposition p j hp hjlarge
        have hkdecomp :
            k = (2 * p) * m + (2 * (p + 1)) * n := by
          rw [hj, hdecomp]
          ring
        have hpow : ‖A ^ k‖ ≤ r ^ k := by
          simpa only [hkdecomp] using
            (p25_norm_pow_le_of_decomposition A r hr
              (2 * p) (2 * (p + 1)) m n hpbound hsuccbound)
        exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      · simp [heven k hkeven]

end HighamBench
