import HighamBench.P25Definitions

namespace HighamBench

open scoped BigOperators Topology

private lemma p25_large_eq_add_mul (p k : ℕ) (hp : 0 < p)
    (hk : p * (p - 1) ≤ k) :
    ∃ m n : ℕ, k = p * m + (p + 1) * n := by
  have hq : p - 1 ≤ k / p := (Nat.le_div_iff_mul_le hp).2 (by
    simpa [Nat.mul_comm] using hk)
  have hr : k % p ≤ p - 1 := by
    have := Nat.mod_lt k hp
    omega
  have hrq : k % p ≤ k / p := hr.trans hq
  refine ⟨k / p - k % p, k % p, ?_⟩
  symm
  calc
    p * (k / p - k % p) + (p + 1) * (k % p) =
        p * (k / p - k % p) + p * (k % p) + k % p := by
          simp [Nat.add_mul, Nat.add_assoc]
    _ = p * ((k / p - k % p) + k % p) + k % p := by
          rw [Nat.mul_add]
    _ = p * (k / p) + k % p := by rw [Nat.sub_add_cancel hrq]
    _ = k := Nat.div_add_mod k p

private lemma p25_norm_pow_le_of_add_mul
    {E : Type*} [NormedRing E] [NormOneClass E]
    (A : E) (r : ℝ) (hr : 0 ≤ r)
    (a b m n k : ℕ) (hk : k = a * m + b * n)
    (ha : ‖A ^ a‖ ≤ r ^ a) (hb : ‖A ^ b‖ ≤ r ^ b) :
    ‖A ^ k‖ ≤ r ^ k := by
  subst k
  calc
    ‖A ^ (a * m + b * n)‖ = ‖A ^ (a * m) * A ^ (b * n)‖ := by rw [pow_add]
    _ ≤ ‖A ^ (a * m)‖ * ‖A ^ (b * n)‖ := norm_mul_le _ _
    _ = ‖(A ^ a) ^ m‖ * ‖(A ^ b) ^ n‖ := by rw [pow_mul, pow_mul]
    _ ≤ ‖A ^ a‖ ^ m * ‖A ^ b‖ ^ n :=
      mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    _ ≤ (r ^ a) ^ m * (r ^ b) ^ n :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha _)
        (pow_le_pow_left₀ (norm_nonneg _) hb _) (pow_nonneg (norm_nonneg _) _)
        (pow_nonneg (pow_nonneg hr _) _)
    _ = r ^ (a * m + b * n) := by rw [← pow_mul, ← pow_mul, ← pow_add]

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
  · intro r hr hlarge hap hap1 hsum
    have hterm : ∀ k : ℕ, ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k := by
      intro k
      by_cases hk : k < ℓ
      · rw [hcutoff k hk]
        simp
      · have hklarge : p * (p - 1) ≤ k := hlarge.trans (Nat.le_of_not_gt hk)
        obtain ⟨m, n, hmn⟩ := p25_large_eq_add_mul p k hp hklarge
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left
          (p25_norm_pow_le_of_add_mul A r hr p (p + 1) m n k hmn hap hap1)
          (norm_nonneg _)
    have hsnorm : Summable (fun k : ℕ ↦ ‖c k • A ^ k‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hsum
    have hsseries : Summable (fun k : ℕ ↦ c k • A ^ k) :=
      hsum.of_norm_bounded hterm
    refine ⟨hsseries, ?_⟩
    exact (norm_tsum_le_tsum_norm hsnorm).trans (hsnorm.tsum_le_tsum hterm hsum)
  · intro heven r hr hlarge hap hap1 hsum
    have hterm : ∀ k : ℕ, ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k := by
      intro k
      by_cases hk : k < ℓ
      · rw [hcutoff k hk]
        simp
      · by_cases hck : c k = 0
        · simp [hck]
        · have hkEven : Even k := by
            by_contra hkOdd
            exact hck (heven k hkOdd)
          obtain ⟨j, hj⟩ := even_iff_exists_two_mul.mp hkEven
          have hklarge : 2 * p * (p - 1) ≤ k :=
            hlarge.trans (Nat.le_of_not_gt hk)
          have hjlarge : p * (p - 1) ≤ j := by
            have htwice : 2 * (p * (p - 1)) ≤ 2 * j := by
              simpa [Nat.mul_assoc, hj] using hklarge
            omega
          obtain ⟨m, n, hmn⟩ := p25_large_eq_add_mul p j hp hjlarge
          have hkrep : k = (2 * p) * m + (2 * (p + 1)) * n := by
            calc
              k = 2 * j := hj
              _ = 2 * (p * m + (p + 1) * n) := by rw [hmn]
              _ = (2 * p) * m + (2 * (p + 1)) * n := by
                ring
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left
            (p25_norm_pow_le_of_add_mul A r hr (2 * p) (2 * (p + 1)) m n k
              hkrep hap hap1)
            (norm_nonneg _)
    have hsnorm : Summable (fun k : ℕ ↦ ‖c k • A ^ k‖) :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hsum
    have hsseries : Summable (fun k : ℕ ↦ c k • A ^ k) :=
      hsum.of_norm_bounded hterm
    refine ⟨hsseries, ?_⟩
    exact (norm_tsum_le_tsum_norm hsnorm).trans (hsnorm.tsum_le_tsum hterm hsum)

end HighamBench
