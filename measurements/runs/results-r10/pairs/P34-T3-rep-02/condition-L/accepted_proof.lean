import HighamBench.P34Definitions

namespace HighamBench

private lemma p34LowerShift_add_congr
    (n : ℕ) (x y u v : ℕ → ℝ)
    (h : ∀ i, i < n → x i + y i = u i + v i) :
    p34LowerShift n x + p34LowerShift n y =
      p34LowerShift n u + p34LowerShift n v := by
  ext i j
  change
    (if i.val = j.val + 1 then x j.val else 0) +
        (if i.val = j.val + 1 then y j.val else 0) =
      (if i.val = j.val + 1 then u j.val else 0) +
        (if i.val = j.val + 1 then v j.val else 0)
  by_cases hij : i.val = j.val + 1
  · simpa [hij] using h j.val (by omega)
  · simp [hij]

private lemma p34LowerShift_mul_congr
    (n : ℕ) (x y u v : ℕ → ℝ)
    (h : ∀ i j, i < n → i = j + 1 → x i * y j = u i * v j) :
    p34LowerShift n x * p34LowerShift n y =
      p34LowerShift n u * p34LowerShift n v := by
  ext i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hik : i.val = k.val + 1
  · by_cases hkj : k.val = j.val + 1
    · simp only [p34LowerShift, hik, hkj, if_true]
      simpa [hkj] using h k.val j.val (by omega) hkj
    · simp [p34LowerShift, hik, hkj]
  · simp [p34LowerShift, hik]

private lemma p34UnitLowerBidiagonal_mul_congr
    (n : ℕ) (x y u v : ℕ → ℝ)
    (hadd : ∀ i, i < n → x i + y i = u i + v i)
    (hmul : ∀ i j, i < n → i = j + 1 → x i * y j = u i * v j) :
    p34UnitLowerBidiagonal n x * p34UnitLowerBidiagonal n y =
      p34UnitLowerBidiagonal n u * p34UnitLowerBidiagonal n v := by
  have ha := p34LowerShift_add_congr n x y u v hadd
  have hm := p34LowerShift_mul_congr n x y u v hmul
  unfold p34UnitLowerBidiagonal
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
  have hd_nonneg : ∀ i, i < n → 0 ≤ p34DqdD b c i := by
    intro i hi
    induction i with
    | zero =>
        simpa [p34DqdD] using hb 0 hi
    | succ i ih =>
        rw [p34DqdD]
        exact div_nonneg
          (mul_nonneg (hb (i + 1) hi) (ih (by omega)))
          (add_nonneg (hc i (by omega)) (ih (by omega)))
  have hc_before_pos : ∀ i, i + 1 < q → 0 < c i := by
    intro i hi
    have hin : i + 1 < n := lt_of_lt_of_le hi hqn
    have hbpos : 0 < b (i + 1) := hbefore (i + 1) (by omega) hi
    have hcne : c i ≠ 0 := by
      intro hci
      have := hzero i hin hci
      linarith
    exact lt_of_le_of_ne (hc i (by omega)) (Ne.symm hcne)
  have hden_pos : ∀ i, i + 1 < q → 0 < c i + p34DqdD b c i := by
    intro i hi
    exact add_pos_of_pos_of_nonneg (hc_before_pos i hi)
      (hd_nonneg i (by omega))
  have hsum_succ : ∀ i, i + 1 < q →
      p34DqdB q b c (i + 1) + p34DqdD b c (i + 1) = b (i + 1) := by
    intro i hi
    rw [p34DqdB, if_pos hi, p34DqdD]
    field_simp [ne_of_gt (hden_pos i hi)]
    <;> ring
  have hsubdiag_sum : ∀ i, i < n →
      p34DqdB q b c i + p34DqdC q b c i = b i + c i := by
    intro i hi
    cases i with
    | zero =>
        simp [p34DqdB, p34DqdC, p34DqdD, hqpos, add_comm]
    | succ i =>
        by_cases hiq : i + 1 < q
        · rw [p34DqdC, if_pos (by omega)]
          linarith [hsum_succ i hiq]
        · simp [p34DqdB, p34DqdC, hiq, show ¬i + 1 < q from hiq]
  have hsubdiag_mul : ∀ i j, i < n → i = j + 1 →
      p34DqdB q b c i * p34DqdC q b c j = b i * c j := by
    intro i j hi hij
    subst i
    by_cases hjq : j + 1 < q
    · have hjlt : j < q := by omega
      rw [p34DqdB, if_pos hjq, p34DqdC, if_pos hjlt]
      field_simp [ne_of_gt (hden_pos j hjq)]
      <;> ring
    · rw [p34DqdB, if_neg hjq]
      by_cases hj : j < q
      · have heq : j + 1 = q := by omega
        have hbq : b (j + 1) = 0 := by
          rw [heq]
          exact hstop (by omega)
        rw [p34DqdC, if_pos hj, hbq]
        ring
      · rw [p34DqdC, if_neg hj]
  have hB_nonneg : ∀ i, i < n → 0 ≤ p34DqdB q b c i := by
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
  have hC_nonneg : ∀ i, i < n → 0 ≤ p34DqdC q b c i := by
    intro i hi
    rw [p34DqdC]
    split_ifs
    · exact add_nonneg (hc i hi) (hd_nonneg i hi)
    · exact hc i hi
  refine ⟨hB_nonneg, hC_nonneg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [p34DqdB]
  · exact p34UnitLowerBidiagonal_mul_congr n (p34DqdB q b c)
      (p34DqdC q b c) b c hsubdiag_sum hsubdiag_mul
  · intro i hipos hin
    cases i with
    | zero => omega
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hbp : 0 < b (i + 1) := hbefore (i + 1) (by omega) hiq
          have hBp : 0 < p34DqdB q b c (i + 1) := by
            rw [p34DqdB, if_pos hiq]
            exact div_pos (mul_pos hbp (hc_before_pos i hiq)) (hden_pos i hiq)
          constructor <;> intro hz <;> linarith
        · simp [p34DqdB, hiq]
  · intro i hi hCi
    rw [p34DqdC] at hCi
    by_cases hiq : i < q
    · rw [if_pos hiq] at hCi
      nlinarith [hc i hi, hd_nonneg i hi]
    · rw [if_neg hiq] at hCi
      exact hCi
  · intro i hi hci hCine
    have hiq : i < q := by
      by_contra hnot
      have : p34DqdC q b c i = c i := by
        simp [p34DqdC, hnot]
      exact hCine (this.trans hci)
    have hnlt : ¬i + 1 < q := by
      intro hlt
      have hib : b (i + 1) = 0 := hzero i (by omega) hci
      have hibpos : 0 < b (i + 1) := hbefore (i + 1) (by omega) hlt
      linarith
    omega
  · intro i hqi
    have hi0 : i ≠ 0 := by omega
    cases i with
    | zero => contradiction
    | succ i =>
        simp [p34DqdB, p34DqdC, show ¬i + 1 < q by omega]
  · omega

end HighamBench
