import HighamBench.P34Definitions

namespace HighamBench

private lemma p34_lowerShift_add_eq
    (n : ℕ) (x y b c : ℕ → ℝ)
    (h : ∀ i, i < n → x i + y i = b i + c i) :
    p34LowerShift n x + p34LowerShift n y =
      p34LowerShift n b + p34LowerShift n c := by
  ext i j
  by_cases hij : i.val = j.val + 1
  · have hj : j.val < n := by omega
    simpa [p34LowerShift, hij] using h j.val hj
  · simp [p34LowerShift, hij]

private lemma p34_lowerShift_mul_eq
    (n : ℕ) (x y b c : ℕ → ℝ)
    (h : ∀ i, i + 1 < n → x (i + 1) * y i = b (i + 1) * c i) :
    p34LowerShift n x * p34LowerShift n y =
      p34LowerShift n b * p34LowerShift n c := by
  ext i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : i.val = k.val + 1
  · by_cases hkj : k.val = j.val + 1
    · have hj : j.val + 1 < n := by omega
      simpa [p34LowerShift, hik, hkj] using h j.val hj
    · simp [p34LowerShift, hik, hkj]
  · simp [p34LowerShift, hik]

private lemma p34_unitLowerBidiagonal_mul_eq
    (n : ℕ) (x y b c : ℕ → ℝ)
    (hadd : ∀ i, i < n → x i + y i = b i + c i)
    (hmul : ∀ i, i + 1 < n → x (i + 1) * y i = b (i + 1) * c i) :
    p34UnitLowerBidiagonal n x * p34UnitLowerBidiagonal n y =
      p34UnitLowerBidiagonal n b * p34UnitLowerBidiagonal n c := by
  have ha := p34_lowerShift_add_eq n x y b c hadd
  have hm := p34_lowerShift_mul_eq n x y b c hmul
  simp only [p34UnitLowerBidiagonal]
  calc
    (1 + p34LowerShift n x) * (1 + p34LowerShift n y) =
        1 + (p34LowerShift n x + p34LowerShift n y) +
          p34LowerShift n x * p34LowerShift n y := by noncomm_ring
    _ = 1 + (p34LowerShift n b + p34LowerShift n c) +
          p34LowerShift n b * p34LowerShift n c := by rw [ha, hm]
    _ = (1 + p34LowerShift n b) * (1 + p34LowerShift n c) := by
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
  have hd_nonneg : ∀ i, i < q → 0 ≤ p34DqdD b c i := by
    intro i
    induction i with
    | zero =>
        intro _
        simpa [p34DqdD] using hb 0 hn
    | succ i ih =>
        intro hiq
        rw [p34DqdD]
        exact div_nonneg
          (mul_nonneg (hb (i + 1) (by omega)) (ih (by omega)))
          (add_nonneg (hc i (by omega)) (ih (by omega)))
  have hc_before_pos : ∀ i, i + 1 < q → 0 < c i := by
    intro i hiq
    have hc0 : 0 ≤ c i := hc i (by omega)
    have hcne : c i ≠ 0 := by
      intro hci
      have hbi := hzero i (by omega) hci
      exact (ne_of_gt (hbefore (i + 1) (by omega) hiq)) hbi
    exact lt_of_le_of_ne hc0 (Ne.symm hcne)
  have hadd : ∀ i, i < n →
      p34DqdB q b c i + p34DqdC q b c i = b i + c i := by
    intro i hin
    cases i with
    | zero =>
        simp [p34DqdB, p34DqdC, p34DqdD, hqpos]
        ring
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hden : c i + p34DqdD b c i ≠ 0 := ne_of_gt <|
            add_pos_of_pos_of_nonneg (hc_before_pos i hiq)
              (hd_nonneg i (by omega))
          simp [p34DqdB, p34DqdC, p34DqdD, hiq]
          field_simp [hden]
          <;> ring
        · simp [p34DqdB, p34DqdC, hiq]
  have hmul : ∀ i, i + 1 < n →
      p34DqdB q b c (i + 1) * p34DqdC q b c i =
        b (i + 1) * c i := by
    intro i hin
    by_cases hiq : i + 1 < q
    · have hiq' : i < q := by omega
      have hden : c i + p34DqdD b c i ≠ 0 := ne_of_gt <|
        add_pos_of_pos_of_nonneg (hc_before_pos i hiq)
          (hd_nonneg i hiq')
      simp [p34DqdB, p34DqdC, hiq, hiq']
      field_simp [hden]
    · by_cases hiq' : i < q
      · have hiqeq : i + 1 = q := by omega
        have hbnext : b (i + 1) = 0 := by
          rw [hiqeq]
          exact hstop (by omega)
        simp [p34DqdB, p34DqdC, hiq, hiq', hbnext]
      · simp [p34DqdB, p34DqdC, hiq, hiq']
  have hB_nonneg : ∀ i, i < n → 0 ≤ p34DqdB q b c i := by
    intro i hin
    cases i with
    | zero => simp [p34DqdB]
    | succ i =>
        by_cases hiq : i + 1 < q
        · rw [p34DqdB, if_pos hiq]
          exact div_nonneg
            (mul_nonneg (hb (i + 1) hin) (hc i (by omega)))
            (add_nonneg (hc i (by omega)) (hd_nonneg i (by omega)))
        · simpa [p34DqdB, hiq] using hb (i + 1) hin
  have hC_nonneg : ∀ i, i < n → 0 ≤ p34DqdC q b c i := by
    intro i hin
    by_cases hiq : i < q
    · rw [p34DqdC, if_pos hiq]
      exact add_nonneg (hc i hin) (hd_nonneg i hiq)
    · simpa [p34DqdC, hiq] using hc i hin
  refine ⟨hB_nonneg, hC_nonneg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact p34_unitLowerBidiagonal_mul_eq n _ _ b c hadd hmul
  · intro i hipos hin
    cases i with
    | zero => omega
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hbpos : 0 < b (i + 1) := hbefore (i + 1) (by omega) hiq
          have hcpos : 0 < c i := hc_before_pos i hiq
          have hdpos : 0 < c i + p34DqdD b c i :=
            add_pos_of_pos_of_nonneg hcpos (hd_nonneg i (by omega))
          rw [p34DqdB, if_pos hiq]
          exact iff_of_false
            (ne_of_gt (div_pos (mul_pos hbpos hcpos) hdpos))
            (ne_of_gt hbpos)
        · simp [p34DqdB, hiq]
  · intro i hin hci
    by_cases hiq : i < q
    · rw [p34DqdC, if_pos hiq] at hci
      have hci0 := hc i hin
      have hdi0 := hd_nonneg i hiq
      linarith
    · simpa [p34DqdC, hiq] using hci
  · intro i hin hci hchanged
    by_cases hiq : i < q
    · have hnlt : ¬ i + 1 < q := by
        intro hiq1
        have hbi := hzero i (by omega) hci
        exact (ne_of_gt (hbefore (i + 1) (by omega) hiq1)) hbi
      omega
    · exfalso
      apply hchanged
      simp [p34DqdC, hiq, hci]
  · intro i hqi
    have hiq : ¬ i < q := by omega
    constructor
    · cases i with
      | zero => omega
      | succ i => simp [p34DqdB, hiq]
    · simp [p34DqdC, hiq]
  · omega

end HighamBench
