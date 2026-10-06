import HighamBench.P34Definitions

namespace HighamBench

lemma p34_lowerShift_mul_apply (n : ℕ) (b c : ℕ → ℝ)
    (i j : Fin (n + 1)) :
    (p34LowerShift n b * p34LowerShift n c) i j =
      if i.val = j.val + 2 then b (j.val + 1) * c j.val else 0 := by
  rw [Matrix.mul_apply]
  by_cases hij : i.val = j.val + 2
  · let k : Fin (n + 1) := ⟨j.val + 1, by omega⟩
    rw [Finset.sum_eq_single k]
    · simp [p34LowerShift, k, hij]
    · intro x hx hxk
      simp only [p34LowerShift]
      by_cases hxj : x.val = j.val + 1
      · exfalso
        apply hxk
        apply Fin.ext
        exact hxj
      · simp [hxj]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro x hx
      simp only [p34LowerShift]
      by_cases hix : i.val = x.val + 1
      · simp [hix, show x.val ≠ j.val + 1 by omega]
      · simp [hix]

lemma p34_unitLowerBidiagonal_mul_eq_of_coefficients
    (n : ℕ) (b₁ c₁ b₂ c₂ : ℕ → ℝ)
    (hsum : ∀ i, i < n → b₁ i + c₁ i = b₂ i + c₂ i)
    (hprod : ∀ i, i + 1 < n → b₁ (i + 1) * c₁ i = b₂ (i + 1) * c₂ i) :
    p34UnitLowerBidiagonal n b₁ * p34UnitLowerBidiagonal n c₁ =
      p34UnitLowerBidiagonal n b₂ * p34UnitLowerBidiagonal n c₂ := by
  ext i j
  simp only [p34UnitLowerBidiagonal, add_mul, mul_add, one_mul, mul_one]
  simp only [Matrix.add_apply]
  rw [p34_lowerShift_mul_apply, p34_lowerShift_mul_apply]
  simp only [p34LowerShift]
  by_cases h₁ : i.val = j.val + 1
  · have hj : j.val < n := by omega
    have h₂ : i.val ≠ j.val + 2 := by omega
    simp only [if_pos h₁, if_neg h₂, add_zero]
    linarith [hsum j.val hj]
  · by_cases h₂ : i.val = j.val + 2
    · have hj : j.val + 1 < n := by omega
      simp [h₁, h₂, hprod j.val hj]
    · simp [h₁, h₂]

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
  have hd_nonneg : ∀ i, i < n → 0 ≤ p34DqdD b c i := by
    intro i
    induction i with
    | zero =>
        intro hi
        simpa [p34DqdD] using hb 0 hi
    | succ i ih =>
        intro hi
        rw [p34DqdD]
        exact div_nonneg
          (mul_nonneg (hb (i + 1) hi) (ih (by omega)))
          (add_nonneg (hc i (by omega)) (ih (by omega)))
  have hc_pos_before : ∀ i, i + 1 < q → 0 < c i := by
    intro i hi
    have hin : i + 1 < n := lt_of_lt_of_le hi hqn
    have hci : c i ≠ 0 := by
      intro hci
      have hbzero := hzero i hin hci
      have hbpos := hbefore (i + 1) (by omega) hi
      linarith
    exact lt_of_le_of_ne (hc i (by omega)) (Ne.symm hci)
  have hden_pos : ∀ i, i + 1 < q → 0 < c i + p34DqdD b c i := by
    intro i hi
    have hin : i < n := by omega
    exact add_pos_of_pos_of_nonneg (hc_pos_before i hi) (hd_nonneg i hin)
  have hb_add_d : ∀ i, i < q →
      p34DqdB q b c i + p34DqdD b c i = b i := by
    intro i hi
    cases i with
    | zero => simp [p34DqdB, p34DqdD]
    | succ i =>
        rw [p34DqdB, if_pos hi, p34DqdD]
        have hne : c i + p34DqdD b c i ≠ 0 :=
          ne_of_gt (hden_pos i hi)
        field_simp
  have hb_nonneg : ∀ i, i < n → 0 ≤ p34DqdB q b c i := by
    intro i hi
    cases i with
    | zero => simp [p34DqdB]
    | succ i =>
        rw [p34DqdB]
        split_ifs with hiq
        · exact div_nonneg
            (mul_nonneg (hb (i + 1) hi) (hc i (by omega)))
            (add_nonneg (hc i (by omega)) (hd_nonneg i (by omega)))
        · exact hb (i + 1) hi
  have hc_nonneg : ∀ i, i < n → 0 ≤ p34DqdC q b c i := by
    intro i hi
    simp only [p34DqdC]
    split_ifs
    · exact add_nonneg (hc i hi) (hd_nonneg i hi)
    · exact hc i hi
  have hb_zero_iff : ∀ i, 0 < i → i < n →
      (p34DqdB q b c i = 0 ↔ b i = 0) := by
    intro i hip hin
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    rw [p34DqdB]
    by_cases hiq : i + 1 < q
    · rw [if_pos hiq]
      have hbpos : 0 < b (i + 1) := hbefore (i + 1) (by omega) hiq
      have hcpos : 0 < c i := hc_pos_before i hiq
      have hden : 0 < c i + p34DqdD b c i := hden_pos i hiq
      constructor
      · intro hz
        have : 0 < b (i + 1) * c i / (c i + p34DqdD b c i) :=
          div_pos (mul_pos hbpos hcpos) hden
        linarith
      · intro hz
        linarith
    · simp [hiq]
  have hc_zero_imp : ∀ i, i < n → p34DqdC q b c i = 0 → c i = 0 := by
    intro i hin hz
    simp only [p34DqdC] at hz
    split_ifs at hz with hiq
    · have hci := hc i hin
      have hdi := hd_nonneg i hin
      linarith
    · exact hz
  have hc_new_zero : ∀ i, i < n → c i = 0 →
      p34DqdC q b c i ≠ 0 → i + 1 = q := by
    intro i hin hci hnew
    have hiq : i < q := by
      by_contra hiq
      have : p34DqdC q b c i = c i := by
        simp [p34DqdC, Nat.not_lt.mp hiq]
      exact hnew (this.trans hci)
    by_contra hne
    have hil : i + 1 < q := by omega
    have hbzero : b (i + 1) = 0 :=
      hzero i (lt_of_lt_of_le hil hqn) hci
    have hbpos : 0 < b (i + 1) := hbefore (i + 1) (by omega) hil
    linarith
  have htail : ∀ i, q ≤ i →
      p34DqdB q b c i = b i ∧ p34DqdC q b c i = c i := by
    intro i hi
    have hip : 0 < i := lt_of_lt_of_le hqpos hi
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    constructor
    · simp [p34DqdB, show ¬i + 1 < q by omega]
    · simp [p34DqdC, show ¬i + 1 < q by omega]
  have hsum : ∀ i, i < n →
      p34DqdB q b c i + p34DqdC q b c i = b i + c i := by
    intro i hin
    by_cases hiq : i < q
    · rw [show p34DqdC q b c i = c i + p34DqdD b c i by
        simp [p34DqdC, hiq]]
      linarith [hb_add_d i hiq]
    · obtain ⟨hb_eq, hc_eq⟩ := htail i (Nat.le_of_not_gt hiq)
      rw [hb_eq, hc_eq]
  have hprod : ∀ i, i + 1 < n →
      p34DqdB q b c (i + 1) * p34DqdC q b c i = b (i + 1) * c i := by
    intro i hin
    by_cases hil : i + 1 < q
    · rw [show p34DqdB q b c (i + 1) =
          b (i + 1) * c i / (c i + p34DqdD b c i) by
          simp [p34DqdB, hil]]
      have hiq : i < q := by omega
      rw [show p34DqdC q b c i = c i + p34DqdD b c i by
          simp [p34DqdC, hiq]]
      exact div_mul_cancel₀ _ (ne_of_gt (hden_pos i hil))
    · by_cases heq : i + 1 = q
      · have hbq : b q = 0 := hstop (by omega)
        simp [p34DqdB, p34DqdC, hil, heq, hbq]
      · have hqi : q ≤ i := by omega
        obtain ⟨hb_eq, hc_eq⟩ := htail i hqi
        have hb_next : p34DqdB q b c (i + 1) = b (i + 1) :=
          (htail (i + 1) (by omega)).1
        rw [hc_eq, hb_next]
  refine ⟨hb_nonneg, hc_nonneg, ?_, ?_, hb_zero_iff, hc_zero_imp,
    hc_new_zero, htail, ?_⟩
  · simp [p34DqdB]
  · exact p34_unitLowerBidiagonal_mul_eq_of_coefficients n _ _ _ _ hsum hprod
  · omega

end HighamBench
