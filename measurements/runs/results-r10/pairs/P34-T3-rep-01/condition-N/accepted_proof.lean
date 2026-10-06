import HighamBench.P34Definitions

namespace HighamBench

private lemma p34_unitLowerBidiagonal_mul_congr
    (n : ℕ) (a b c d : ℕ → ℝ)
    (hsum : ∀ i, i < n → a i + b i = c i + d i)
    (hprod : ∀ i, 0 < i → i < n → a i * b (i - 1) = c i * d (i - 1)) :
    p34UnitLowerBidiagonal n a * p34UnitLowerBidiagonal n b =
      p34UnitLowerBidiagonal n c * p34UnitLowerBidiagonal n d := by
  have hadd : p34LowerShift n a + p34LowerShift n b =
      p34LowerShift n c + p34LowerShift n d := by
    ext i j
    by_cases hij : i.val = j.val + 1
    · change (if i.val = j.val + 1 then a j.val else 0) +
          (if i.val = j.val + 1 then b j.val else 0) =
        (if i.val = j.val + 1 then c j.val else 0) +
          (if i.val = j.val + 1 then d j.val else 0)
      simpa [hij] using hsum j.val (by omega)
    · simp [p34LowerShift, hij]
  have hmul : p34LowerShift n a * p34LowerShift n b =
      p34LowerShift n c * p34LowerShift n d := by
    ext i j
    simp only [Matrix.mul_apply, p34LowerShift]
    by_cases hj : j.val < n
    · let k : Fin (n + 1) := ⟨j.val + 1, by omega⟩
      rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
      · by_cases hij : i.val = j.val + 2
        · simp [k, hij]
          simpa only [Nat.add_sub_cancel] using
            hprod (j.val + 1) (by omega) (by omega)
        · simp [k, hij]
      · intro x _ hxk
        have hx : x.val ≠ j.val + 1 := by
          intro heq
          apply hxk
          apply Fin.ext
          simpa [k] using heq
        simp [hx]
      · simp
      · intro x _ hxk
        have hx : x.val ≠ j.val + 1 := by
          intro heq
          apply hxk
          apply Fin.ext
          simpa [k] using heq
        simp [hx]
      · simp
    · have hjmax : j.val = n := by omega
      have hx : ∀ x : Fin (n + 1), x.val ≠ n + 1 := by
        intro x
        omega
      simp [hjmax, hx]
  simp only [p34UnitLowerBidiagonal]
  calc
    (1 + p34LowerShift n a) * (1 + p34LowerShift n b) =
        1 + (p34LowerShift n a + p34LowerShift n b) +
          p34LowerShift n a * p34LowerShift n b := by noncomm_ring
    _ = 1 + (p34LowerShift n c + p34LowerShift n d) +
          p34LowerShift n c * p34LowerShift n d := by rw [hadd, hmul]
    _ = (1 + p34LowerShift n c) * (1 + p34LowerShift n d) := by
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
    intro i
    induction i with
    | zero =>
        intro hi
        simpa [p34DqdD] using hb 0 hi
    | succ i ih =>
        intro hi
        rw [p34DqdD]
        exact div_nonneg
          (mul_nonneg (hb (i + 1) (by omega)) (ih (by omega)))
          (add_nonneg (hc i (by omega)) (ih (by omega)))
  have hc_before : ∀ i, i + 1 < q → 0 < c i := by
    intro i hiq
    have hci : 0 ≤ c i := hc i (by omega)
    have hbip : 0 < b (i + 1) := hbefore (i + 1) (by omega) hiq
    by_contra hnot
    have hciz : c i = 0 := le_antisymm (le_of_not_gt hnot) hci
    have hbz : b (i + 1) = 0 := hzero i (by omega) hciz
    linarith
  have hdenom : ∀ i, i + 1 < q → 0 < c i + p34DqdD b c i := by
    intro i hiq
    exact add_pos_of_pos_of_nonneg (hc_before i hiq)
      (hd_nonneg i (by omega))
  have hsum : ∀ i, i < n →
      p34DqdB q b c i + p34DqdC q b c i = b i + c i := by
    intro i hi
    cases i with
    | zero =>
        simp [p34DqdB, p34DqdC, p34DqdD, hqpos]
        <;> ring
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hne : c i + p34DqdD b c i ≠ 0 :=
            ne_of_gt (hdenom i hiq)
          rw [p34DqdB, p34DqdC]
          simp only [if_pos hiq, p34DqdD]
          field_simp [hne]
          <;> ring
        · simp [p34DqdB, p34DqdC, hiq]
  have hprod : ∀ i, 0 < i → i < n →
      p34DqdB q b c i * p34DqdC q b c (i - 1) =
        b i * c (i - 1) := by
    intro i hipos hi
    cases i with
    | zero => omega
    | succ i =>
        simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
        by_cases hiq : i + 1 < q
        · have hne : c i + p34DqdD b c i ≠ 0 :=
            ne_of_gt (hdenom i hiq)
          simp only [p34DqdB, if_pos hiq, p34DqdC,
            if_pos (show i < q by omega)]
          field_simp [hne]
        · have hqle : q ≤ i + 1 := by omega
          by_cases heq : i + 1 = q
          · have hbz : b (i + 1) = 0 := by
              rw [heq]
              exact hstop (by omega)
            simp [p34DqdB, hiq, hbz]
          · have hqlei : q ≤ i := by omega
            simp [p34DqdB, p34DqdC, hiq, not_lt_of_ge hqlei]
  have hB_nonneg : ∀ i, i < n → 0 ≤ p34DqdB q b c i := by
    intro i hi
    cases i with
    | zero => simp [p34DqdB]
    | succ i =>
        by_cases hiq : i + 1 < q
        · rw [p34DqdB, if_pos hiq]
          exact div_nonneg
            (mul_nonneg (hb (i + 1) (by omega)) (hc i (by omega)))
            (le_of_lt (hdenom i hiq))
        · simpa [p34DqdB, hiq] using hb (i + 1) (by omega)
  have hC_nonneg : ∀ i, i < n → 0 ≤ p34DqdC q b c i := by
    intro i hi
    by_cases hiq : i < q
    · rw [p34DqdC, if_pos hiq]
      exact add_nonneg (hc i hi) (hd_nonneg i hi)
    · simpa [p34DqdC, hiq] using hc i hi
  have hB_zero : ∀ i, 0 < i → i < n →
      (p34DqdB q b c i = 0 ↔ b i = 0) := by
    intro i hipos hi
    cases i with
    | zero => omega
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hbip : 0 < b (i + 1) :=
            hbefore (i + 1) (by omega) hiq
          have hBip : 0 < p34DqdB q b c (i + 1) := by
            rw [p34DqdB, if_pos hiq]
            exact div_pos (mul_pos hbip (hc_before i hiq)) (hdenom i hiq)
          constructor <;> intro hz <;> linarith
        · simp [p34DqdB, hiq]
  have hC_zero : ∀ i, i < n → p34DqdC q b c i = 0 → c i = 0 := by
    intro i hi hCi
    by_cases hiq : i < q
    · have hadd : c i + p34DqdD b c i = 0 := by
        simpa [p34DqdC, hiq] using hCi
      linarith [hc i hi, hd_nonneg i hi]
    · simpa [p34DqdC, hiq] using hCi
  have hC_new : ∀ i, i < n → c i = 0 →
      p34DqdC q b c i ≠ 0 → i + 1 = q := by
    intro i hi hci hCine
    by_cases hiq : i < q
    · by_cases heq : i + 1 = q
      · exact heq
      · have hiq' : i + 1 < q := by omega
        have hbz : b (i + 1) = 0 := hzero i (by omega) hci
        have hbpos : 0 < b (i + 1) :=
          hbefore (i + 1) (by omega) hiq'
        linarith
    · exfalso
      apply hCine
      simpa [p34DqdC, hiq] using hci
  have htail : ∀ i, q ≤ i →
      p34DqdB q b c i = b i ∧ p34DqdC q b c i = c i := by
    intro i hqi
    constructor
    · cases i with
      | zero => omega
      | succ i => simp [p34DqdB, not_lt_of_ge hqi]
    · simp [p34DqdC, not_lt_of_ge hqi]
  refine ⟨hB_nonneg, hC_nonneg, ?_, ?_, hB_zero, hC_zero, hC_new,
    htail, ?_⟩
  · simp [p34DqdB]
  · exact p34_unitLowerBidiagonal_mul_congr n
      (p34DqdB q b c) (p34DqdC q b c) b c hsum hprod
  · omega

end HighamBench
