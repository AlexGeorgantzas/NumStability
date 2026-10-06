import HighamBench.P34Definitions

namespace HighamBench

lemma p34LowerShift_add_eq_of
    (n : ℕ) (x y u v : ℕ → ℝ)
    (h : ∀ i, i < n → x i + y i = u i + v i) :
    p34LowerShift n x + p34LowerShift n y =
      p34LowerShift n u + p34LowerShift n v := by
  ext i j
  by_cases hij : i.val = j.val + 1
  · have hj : j.val < n := by omega
    simp [p34LowerShift, hij, h j.val hj]
  · simp [p34LowerShift, hij]

lemma p34LowerShift_mul_eq_of
    (n : ℕ) (x y u v : ℕ → ℝ)
    (h : ∀ i, i + 1 < n → x (i + 1) * y i = u (i + 1) * v i) :
    p34LowerShift n x * p34LowerShift n y =
      p34LowerShift n u * p34LowerShift n v := by
  classical
  ext i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hik : i.val = k.val + 1
  · by_cases hkj : k.val = j.val + 1
    · have hj : j.val + 1 < n := by omega
      simpa [p34LowerShift, hik, hkj] using h j.val hj
    · simp [p34LowerShift, hik, hkj]
  · simp [p34LowerShift, hik]

lemma p34UnitLowerBidiagonal_mul_eq_of
    (n : ℕ) (x y u v : ℕ → ℝ)
    (hadd : ∀ i, i < n → x i + y i = u i + v i)
    (hmul : ∀ i, i + 1 < n → x (i + 1) * y i = u (i + 1) * v i) :
    p34UnitLowerBidiagonal n x * p34UnitLowerBidiagonal n y =
      p34UnitLowerBidiagonal n u * p34UnitLowerBidiagonal n v := by
  have ha := p34LowerShift_add_eq_of n x y u v hadd
  have hm := p34LowerShift_mul_eq_of n x y u v hmul
  simp only [p34UnitLowerBidiagonal]
  calc
    (1 + p34LowerShift n x) * (1 + p34LowerShift n y) =
        1 + (p34LowerShift n x + p34LowerShift n y) +
          p34LowerShift n x * p34LowerShift n y := by noncomm_ring
    _ = 1 + (p34LowerShift n u + p34LowerShift n v) +
          p34LowerShift n u * p34LowerShift n v := by rw [ha, hm]
    _ = (1 + p34LowerShift n u) * (1 + p34LowerShift n v) := by
      noncomm_ring

/-- P34-T3: Lemma 4.1 and the structural guarantees of Algorithm 4.1. -/
theorem p34_t3_dqd2_refactorization
    (n q : ℕ) (b c : ℕ → ℝ)
    (hn : 0 < n) (hqpos : 0 < q) (hqn : q ≤ n)
    (hb : ∀ i, i < n → 0 ≤ b i)
    (hc : ∀ i, i < n → 0 ≤ c i)
    (hbefore : ∀ i, 0 < i → i < q → 0 < b i)
    (hzero : ∀ i, i + 1 < n → c i = 0 → b (i + 1) = 0)
    (hstop : q < n → b q = 0) :
    (∀ i, i < n → 0 ≤ p34DqdB q b c i) ∧
    (∀ i, i < n → 0 ≤ p34DqdC q b c i) ∧
    p34DqdB q b c 0 = 0 ∧
    p34UnitLowerBidiagonal n (p34DqdB q b c) *
        p34UnitLowerBidiagonal n (p34DqdC q b c) =
      p34UnitLowerBidiagonal n b * p34UnitLowerBidiagonal n c ∧
    (∀ i, 0 < i → i < n →
      (p34DqdB q b c i = 0 ↔ b i = 0)) ∧
    (∀ i, i < n → p34DqdC q b c i = 0 → c i = 0) ∧
    (∀ i, i < n → c i = 0 → p34DqdC q b c i ≠ 0 → i + 1 = q) ∧
    (∀ i, q ≤ i →
      p34DqdB q b c i = b i ∧ p34DqdC q b c i = c i) ∧
    4 * q ≤ 4 * n := by
  -- PROOF_START P34-T3-H001
  have hcp : ∀ i, i + 1 < q → 0 < c i := by
    intro i hiq
    have hin : i + 1 < n := lt_of_lt_of_le hiq hqn
    have hbpos : 0 < b (i + 1) := hbefore (i + 1) (by omega) hiq
    have hcne : c i ≠ 0 := by
      intro hci
      exact (ne_of_gt hbpos) (hzero i hin hci)
    exact lt_of_le_of_ne (hc i (by omega)) (Ne.symm hcne)
  have hd : ∀ i, i < q → 0 ≤ p34DqdD b c i := by
    intro i
    induction i with
    | zero =>
        intro hi
        simpa [p34DqdD] using hb 0 (by omega)
    | succ i ih =>
        intro hi
        have hdi : 0 ≤ p34DqdD b c i := ih (by omega)
        have hci : 0 < c i := hcp i hi
        have hbi : 0 ≤ b (i + 1) := hb (i + 1) (by omega)
        simp only [p34DqdD]
        positivity
  have hden : ∀ i, i + 1 < q → 0 < c i + p34DqdD b c i := by
    intro i hiq
    exact add_pos_of_pos_of_nonneg (hcp i hiq) (hd i (by omega))
  have hBnonneg : ∀ i, i < n → 0 ≤ p34DqdB q b c i := by
    intro i hin
    cases i with
    | zero => simp [p34DqdB]
    | succ i =>
        by_cases hiq : i + 1 < q
        · simp only [p34DqdB, if_pos hiq]
          exact div_nonneg
            (mul_nonneg (hb (i + 1) hin) (hc i (by omega)))
            (le_of_lt (hden i hiq))
        · simpa [p34DqdB, hiq] using hb (i + 1) hin
  have hCnonneg : ∀ i, i < n → 0 ≤ p34DqdC q b c i := by
    intro i hin
    by_cases hiq : i < q
    · rw [p34DqdC, if_pos hiq]
      exact add_nonneg (hc i hin) (hd i hiq)
    · simpa [p34DqdC, hiq] using hc i hin
  have hadd : ∀ i, i < n →
      p34DqdB q b c i + p34DqdC q b c i = b i + c i := by
    intro i hin
    cases i with
    | zero =>
        simp [p34DqdB, p34DqdC, p34DqdD, hqpos]
        <;> ring
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hne : c i + p34DqdD b c i ≠ 0 := ne_of_gt (hden i hiq)
          simp only [p34DqdB, if_pos hiq, p34DqdC, p34DqdD]
          field_simp [hne]
          <;> ring
        · simp [p34DqdB, p34DqdC, hiq]
  have hmul : ∀ i, i + 1 < n →
      p34DqdB q b c (i + 1) * p34DqdC q b c i =
        b (i + 1) * c i := by
    intro i hin
    by_cases hiq : i + 1 < q
    · have hiq0 : i < q := by omega
      have hne : c i + p34DqdD b c i ≠ 0 := ne_of_gt (hden i hiq)
      simp only [p34DqdB, if_pos hiq, p34DqdC, if_pos hiq0]
      field_simp
    · by_cases hiq0 : i < q
      · have heq : i + 1 = q := by omega
        have hbzero : b (i + 1) = 0 := by
          rw [heq]
          exact hstop (by omega)
        simp [p34DqdB, p34DqdC, hiq, hiq0, hbzero]
      · simp [p34DqdB, p34DqdC, hiq, hiq0]
  refine ⟨hBnonneg, hCnonneg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [p34DqdB]
  · exact p34UnitLowerBidiagonal_mul_eq_of n
      (p34DqdB q b c) (p34DqdC q b c) b c hadd hmul
  · intro i hipos hin
    cases i with
    | zero => omega
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hbpos : 0 < b (i + 1) := hbefore (i + 1) (by omega) hiq
          have hb'pos : 0 < p34DqdB q b c (i + 1) := by
            simp only [p34DqdB, if_pos hiq]
            exact div_pos (mul_pos hbpos (hcp i hiq)) (hden i hiq)
          exact ⟨fun hz => (ne_of_gt hb'pos hz).elim,
            fun hz => (ne_of_gt hbpos hz).elim⟩
        · simp [p34DqdB, hiq]
  · intro i hin hci
    by_cases hiq : i < q
    · have hdi : 0 ≤ p34DqdD b c i := hd i hiq
      have hci0 : 0 ≤ c i := hc i hin
      simp only [p34DqdC, if_pos hiq] at hci
      linarith
    · simpa [p34DqdC, hiq] using hci
  · intro i hin hci hnew
    by_cases hiq : i < q
    · by_contra hne
      have hiq' : i + 1 < q := by omega
      have hbzero : b (i + 1) = 0 :=
        hzero i (lt_of_lt_of_le hiq' hqn) hci
      exact (ne_of_gt (hbefore (i + 1) (by omega) hiq')) hbzero
    · exfalso
      apply hnew
      simp [p34DqdC, hiq, hci]
  · intro i hiq
    constructor
    · cases i with
      | zero => omega
      | succ i => simp [p34DqdB, not_lt_of_ge hiq]
    · simp [p34DqdC, not_lt_of_ge hiq]
  · omega

end HighamBench
