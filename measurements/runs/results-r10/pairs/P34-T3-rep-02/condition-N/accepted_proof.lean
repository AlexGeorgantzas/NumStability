import HighamBench.P34Definitions

namespace HighamBench

private lemma p34LowerShift_congr
    (n : ℕ) (x y : ℕ → ℝ)
    (h : ∀ i, i < n → x i = y i) :
    p34LowerShift n x = p34LowerShift n y := by
  ext i j
  simp only [p34LowerShift]
  by_cases hij : i.val = j.val + 1
  · rw [if_pos hij, if_pos hij]
    apply h
    omega
  · simp [hij]

private lemma p34LowerShift_mul_congr
    (n : ℕ) (x y x' y' : ℕ → ℝ)
    (h : ∀ i, i + 1 < n → x (i + 1) * y i = x' (i + 1) * y' i) :
    p34LowerShift n x * p34LowerShift n y =
      p34LowerShift n x' * p34LowerShift n y' := by
  ext i j
  simp only [Matrix.mul_apply, p34LowerShift]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hik : i.val = k.val + 1
  · by_cases hkj : k.val = j.val + 1
    · simp only [if_pos hik, if_pos hkj]
      rw [hkj]
      exact h j.val (by omega)
    · simp [hik, hkj]
  · simp [hik]

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
  have hc_pos : ∀ i, i + 1 < q → 0 < c i := by
    intro i hi
    have hci := hc i (by omega)
    have hbi := hbefore (i + 1) (by omega) hi
    by_contra hnci
    have hci0 : c i = 0 := le_antisymm (le_of_not_gt hnci) hci
    have := hzero i (by omega) hci0
    linarith
  have hden_pos : ∀ i, i + 1 < q → 0 < c i + p34DqdD b c i := by
    intro i hi
    exact add_pos_of_pos_of_nonneg (hc_pos i hi) (hd_nonneg i (by omega))
  have hB_nonneg : ∀ i, i < n → 0 ≤ p34DqdB q b c i := by
    intro i hi
    cases i with
    | zero => simp [p34DqdB]
    | succ i =>
        rw [p34DqdB]
        by_cases hiq : i + 1 < q
        · rw [if_pos hiq]
          exact div_nonneg
            (mul_nonneg (hb (i + 1) hi) (hc i (by omega)))
            (le_of_lt (hden_pos i hiq))
        · rw [if_neg hiq]
          exact hb (i + 1) hi
  have hC_nonneg : ∀ i, i < n → 0 ≤ p34DqdC q b c i := by
    intro i hi
    by_cases hiq : i < q
    · rw [p34DqdC, if_pos hiq]
      exact add_nonneg (hc i hi) (hd_nonneg i hi)
    · rw [p34DqdC, if_neg hiq]
      exact hc i hi
  have htail : ∀ i, q ≤ i →
      p34DqdB q b c i = b i ∧ p34DqdC q b c i = c i := by
    intro i hi
    constructor
    · cases i with
      | zero => omega
      | succ i => simp [p34DqdB, Nat.not_lt_of_ge hi]
    · simp [p34DqdC, Nat.not_lt_of_ge hi]
  have hsum : ∀ i, i < n →
      p34DqdB q b c i + p34DqdC q b c i = b i + c i := by
    intro i hi
    cases i with
    | zero =>
        simp [p34DqdB, p34DqdC, p34DqdD, hqpos]
        ring
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hne : c i + p34DqdD b c i ≠ 0 :=
            ne_of_gt (hden_pos i hiq)
          simp only [p34DqdB, p34DqdC, if_pos hiq, p34DqdD]
          field_simp [hne]
          <;> ring
        · simp [p34DqdB, p34DqdC, hiq]
  have hprod : ∀ i, i + 1 < n →
      p34DqdB q b c (i + 1) * p34DqdC q b c i = b (i + 1) * c i := by
    intro i hi
    by_cases hiq : i + 1 < q
    · have hilq : i < q := by omega
      have hne : c i + p34DqdD b c i ≠ 0 :=
        ne_of_gt (hden_pos i hiq)
      simp only [p34DqdB, p34DqdC, if_pos hiq, if_pos hilq]
      field_simp [hne]
    · have hqle : q ≤ i + 1 := Nat.le_of_not_gt hiq
      by_cases hqi : q ≤ i
      · have hilq : ¬i < q := Nat.not_lt_of_ge hqi
        simp [p34DqdB, p34DqdC, hiq, hilq]
      · have hilq : i < q := Nat.lt_of_not_ge hqi
        have heq : i + 1 = q := by omega
        have hb0 : b (i + 1) = 0 := by
          rw [heq]
          exact hstop (by omega)
        simp [p34DqdB, p34DqdC, hiq, hilq, hb0]
  have hmat :
      p34UnitLowerBidiagonal n (p34DqdB q b c) *
          p34UnitLowerBidiagonal n (p34DqdC q b c) =
        p34UnitLowerBidiagonal n b * p34UnitLowerBidiagonal n c := by
    have hshiftsum :
        p34LowerShift n (p34DqdB q b c) +
            p34LowerShift n (p34DqdC q b c) =
          p34LowerShift n b + p34LowerShift n c := by
      ext i j
      simp only [p34LowerShift, Matrix.add_apply]
      by_cases hij : i.val = j.val + 1
      · simp only [if_pos hij]
        have hs := hsum j.val (by omega)
        exact hs
      · simp [hij]
    have hshiftmul := p34LowerShift_mul_congr n
      (p34DqdB q b c) (p34DqdC q b c) b c hprod
    simp only [p34UnitLowerBidiagonal]
    simp only [add_mul, mul_add, one_mul, mul_one]
    rw [hshiftmul]
    calc
      (1 + p34LowerShift n (p34DqdB q b c)) +
            (p34LowerShift n (p34DqdC q b c) +
              p34LowerShift n b * p34LowerShift n c) =
          (1 + (p34LowerShift n (p34DqdB q b c) +
            p34LowerShift n (p34DqdC q b c))) +
              p34LowerShift n b * p34LowerShift n c := by abel
      _ = (1 + (p34LowerShift n b + p34LowerShift n c)) +
              p34LowerShift n b * p34LowerShift n c := by rw [hshiftsum]
      _ = (1 + p34LowerShift n b) +
            (p34LowerShift n c + p34LowerShift n b * p34LowerShift n c) := by
              abel
  have hB_zero : ∀ i, 0 < i → i < n →
      (p34DqdB q b c i = 0 ↔ b i = 0) := by
    intro i hi0 hin
    by_cases hiq : i < q
    · cases i with
      | zero => omega
      | succ k =>
          have hbpos := hbefore (k + 1) (by omega) hiq
          have hcpos := hc_pos k hiq
          have hbp : 0 < p34DqdB q b c (k + 1) := by
            rw [p34DqdB, if_pos hiq]
            exact div_pos (mul_pos hbpos hcpos) (hden_pos k hiq)
          constructor <;> intro hz <;> linarith
    · exact (htail i (Nat.le_of_not_gt hiq)).1 ▸ Iff.rfl
  have hC_zero : ∀ i, i < n → p34DqdC q b c i = 0 → c i = 0 := by
    intro i hin hz
    by_cases hiq : i < q
    · rw [p34DqdC, if_pos hiq] at hz
      have hci := hc i hin
      have hdi := hd_nonneg i hin
      linarith
    · simpa [p34DqdC, hiq] using hz
  have hC_exception : ∀ i, i < n → c i = 0 →
      p34DqdC q b c i ≠ 0 → i + 1 = q := by
    intro i hin hci hne
    have hiq : i < q := by
      by_contra hniq
      have hqi : q ≤ i := Nat.le_of_not_gt hniq
      exact hne ((htail i hqi).2.trans hci)
    have hle : i + 1 ≤ q := by omega
    by_contra hneq
    have hlt : i + 1 < q := lt_of_le_of_ne hle hneq
    have hb0 := hzero i (by omega) hci
    have hbp := hbefore (i + 1) (by omega) hlt
    linarith
  refine ⟨hB_nonneg, hC_nonneg, ?_, hmat, hB_zero, hC_zero,
    hC_exception, htail, ?_⟩
  · simp [p34DqdB]
  · omega

end HighamBench
