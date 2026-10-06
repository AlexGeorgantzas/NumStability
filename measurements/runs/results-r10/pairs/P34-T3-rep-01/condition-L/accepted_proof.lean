import HighamBench.P34Definitions

namespace HighamBench

lemma p34LowerShift_mul_apply (n : ℕ) (x y : ℕ → ℝ)
    (i j : Fin (n + 1)) :
    (p34LowerShift n x * p34LowerShift n y) i j =
      if i.val = j.val + 2 then x (j.val + 1) * y j.val else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hij : i.val = j.val + 2
  · rw [if_pos hij]
    have hj1 : j.val + 1 < n + 1 := by omega
    let k : Fin (n + 1) := ⟨j.val + 1, hj1⟩
    rw [Finset.sum_eq_single k]
    · have hik : i.val = k.val + 1 := by simp [k]; omega
      simp [p34LowerShift, hik, k]
    · intro l _ hlk
      simp only [p34LowerShift]
      by_cases hil : i.val = l.val + 1
      · rw [if_pos hil]
        have hlj : l.val ≠ j.val + 1 := by
          intro hval
          apply hlk
          apply Fin.ext
          simp [k, hval]
        simp [hlj]
      · simp [hil]
    · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    simp only [p34LowerShift]
    by_cases hik : i.val = k.val + 1
    · rw [if_pos hik]
      by_cases hkj : k.val = j.val + 1
      · exfalso
        apply hij
        omega
      · simp [hkj]
    · simp [hik]

lemma p34UnitLowerBidiagonal_mul_eq (n : ℕ)
    (x y b c : ℕ → ℝ)
    (hsum : ∀ i, i < n → x i + y i = b i + c i)
    (hprod : ∀ i, i + 1 < n → x (i + 1) * y i = b (i + 1) * c i) :
    p34UnitLowerBidiagonal n x * p34UnitLowerBidiagonal n y =
      p34UnitLowerBidiagonal n b * p34UnitLowerBidiagonal n c := by
  have hs : p34LowerShift n x + p34LowerShift n y =
      p34LowerShift n b + p34LowerShift n c := by
    ext i j
    simp only [Matrix.add_apply]
    by_cases hij : i.val = j.val + 1
    · simp [p34LowerShift, hij, hsum j.val (by omega)]
    · simp [p34LowerShift, hij]
  have hp : p34LowerShift n x * p34LowerShift n y =
      p34LowerShift n b * p34LowerShift n c := by
    ext i j
    simp only [p34LowerShift_mul_apply]
    by_cases hij : i.val = j.val + 2
    · simp [hij, hprod j.val (by omega)]
    · simp [hij]
  unfold p34UnitLowerBidiagonal
  calc
    (1 + p34LowerShift n x) * (1 + p34LowerShift n y) =
        1 + (p34LowerShift n x + p34LowerShift n y) +
          p34LowerShift n x * p34LowerShift n y := by noncomm_ring
    _ = 1 + (p34LowerShift n b + p34LowerShift n c) +
          p34LowerShift n b * p34LowerShift n c := by rw [hs, hp]
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
    intro i hi
    induction i with
    | zero =>
        simp only [p34DqdD]
        exact hb 0 (by omega)
    | succ i ih =>
        simp only [p34DqdD]
        exact div_nonneg
          (mul_nonneg (hb (i + 1) (by omega)) (ih (by omega)))
          (add_nonneg (hc i (by omega)) (ih (by omega)))
  have hc_pos : ∀ i, i + 1 < q → 0 < c i := by
    intro i hi
    have hci : 0 ≤ c i := hc i (by omega)
    have hcne : c i ≠ 0 := by
      intro hcz
      have hbz : b (i + 1) = 0 := hzero i (by omega) hcz
      have hbp : 0 < b (i + 1) := hbefore (i + 1) (by omega) hi
      linarith
    exact lt_of_le_of_ne hci (Ne.symm hcne)
  have hden_pos : ∀ i, i + 1 < q → 0 < c i + p34DqdD b c i := by
    intro i hi
    exact add_pos_of_pos_of_nonneg (hc_pos i hi) (hd_nonneg i (by omega))
  have hbalance : ∀ i, i < q →
      p34DqdB q b c i + p34DqdD b c i = b i := by
    intro i hi
    cases i with
    | zero => simp [p34DqdB, p34DqdD]
    | succ i =>
        simp only [p34DqdB, if_pos hi, p34DqdD]
        have hne : c i + p34DqdD b c i ≠ 0 :=
          ne_of_gt (hden_pos i hi)
        field_simp
  have hunchanged : ∀ i, q ≤ i →
      p34DqdB q b c i = b i ∧ p34DqdC q b c i = c i := by
    intro i hqi
    constructor
    · cases i with
      | zero => omega
      | succ i => simp [p34DqdB, not_lt_of_ge hqi]
    · simp [p34DqdC, not_lt_of_ge hqi]
  have hsum : ∀ i, i < n →
      p34DqdB q b c i + p34DqdC q b c i = b i + c i := by
    intro i hin
    by_cases hiq : i < q
    · rw [p34DqdC, if_pos hiq]
      calc
        p34DqdB q b c i + (c i + p34DqdD b c i) =
            (p34DqdB q b c i + p34DqdD b c i) + c i := by ring
        _ = b i + c i := by rw [hbalance i hiq]
    · obtain ⟨hbi, hci⟩ := hunchanged i (Nat.le_of_not_gt hiq)
      rw [hbi, hci]
  have hprod : ∀ i, i + 1 < n →
      p34DqdB q b c (i + 1) * p34DqdC q b c i =
        b (i + 1) * c i := by
    intro i hin
    by_cases hip : i + 1 < q
    · have hiq : i < q := by omega
      simp only [p34DqdB, if_pos hip, p34DqdC, if_pos hiq]
      have hne : c i + p34DqdD b c i ≠ 0 :=
        ne_of_gt (hden_pos i hip)
      field_simp
    · by_cases hqi : q ≤ i
      · obtain ⟨hbi, -⟩ := hunchanged (i + 1) (by omega)
        obtain ⟨-, hci⟩ := hunchanged i hqi
        rw [hbi, hci]
      · have hiq : i + 1 = q := by omega
        have hbz : b (i + 1) = 0 := by
          rw [hiq]
          exact hstop (by omega)
        have hbi := (hunchanged (i + 1) (by omega)).1
        rw [hbi, hbz]
        simp
  have hB_nonneg : ∀ i, i < n → 0 ≤ p34DqdB q b c i := by
    intro i hin
    cases i with
    | zero => simp [p34DqdB]
    | succ i =>
        by_cases hiq : i + 1 < q
        · simp only [p34DqdB, if_pos hiq]
          exact div_nonneg
            (mul_nonneg (hb (i + 1) hin) (hc i (by omega)))
            (add_nonneg (hc i (by omega)) (hd_nonneg i (by omega)))
        · simp [p34DqdB, hiq, hb (i + 1) hin]
  have hC_nonneg : ∀ i, i < n → 0 ≤ p34DqdC q b c i := by
    intro i hin
    by_cases hiq : i < q
    · simp only [p34DqdC, if_pos hiq]
      exact add_nonneg (hc i hin) (hd_nonneg i hiq)
    · simp [p34DqdC, hiq, hc i hin]
  have hB_zero : ∀ i, 0 < i → i < n →
      (p34DqdB q b c i = 0 ↔ b i = 0) := by
    intro i hipos hin
    cases i with
    | zero => omega
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hbp : 0 < b (i + 1) := hbefore (i + 1) (by omega) hiq
          have hnewp : 0 < p34DqdB q b c (i + 1) := by
            simp only [p34DqdB, if_pos hiq]
            exact div_pos (mul_pos hbp (hc_pos i hiq)) (hden_pos i hiq)
          constructor
          · intro hz
            exact False.elim ((ne_of_gt hnewp) hz)
          · intro hz
            exact False.elim ((ne_of_gt hbp) hz)
        · simp [p34DqdB, hiq]
  have hC_zero : ∀ i, i < n → p34DqdC q b c i = 0 → c i = 0 := by
    intro i hin hz
    by_cases hiq : i < q
    · simp only [p34DqdC, if_pos hiq] at hz
      have hci := hc i hin
      have hdi := hd_nonneg i hiq
      linarith
    · simpa [p34DqdC, hiq] using hz
  have hnew_C_zero : ∀ i, i < n → c i = 0 →
      p34DqdC q b c i ≠ 0 → i + 1 = q := by
    intro i hin hci hnew
    have hiq : i < q := by
      by_contra hnot
      apply hnew
      rw [(hunchanged i (Nat.le_of_not_gt hnot)).2, hci]
    have hnlt : ¬ i + 1 < q := by
      intro hlt
      have hbz := hzero i (by omega) hci
      have hbp := hbefore (i + 1) (by omega) hlt
      linarith
    omega
  refine ⟨hB_nonneg, hC_nonneg, ?_, ?_, hB_zero, hC_zero,
    hnew_C_zero, hunchanged, ?_⟩
  · simp [p34DqdB]
  · exact p34UnitLowerBidiagonal_mul_eq n _ _ _ _ hsum hprod
  · omega

end HighamBench
