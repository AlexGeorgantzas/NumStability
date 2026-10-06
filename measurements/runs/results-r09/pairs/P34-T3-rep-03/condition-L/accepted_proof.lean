import HighamBench.P34Definitions

namespace HighamBench

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
  have hcpos : ∀ i, i + 1 < q → 0 < c i := by
    intro i hiq
    have hin : i + 1 < n := lt_of_lt_of_le hiq hqn
    have hbpos : 0 < b (i + 1) := hbefore (i + 1) (by omega) hiq
    rcases lt_or_eq_of_le (hc i (by omega)) with hci | hci
    · exact hci
    · exact False.elim ((ne_of_gt hbpos) (hzero i hin hci.symm))
  have hdnonneg : ∀ i, i < q → 0 ≤ p34DqdD b c i := by
    intro i hiq
    induction i with
    | zero =>
        simpa [p34DqdD] using hb 0 (lt_of_lt_of_le hiq hqn)
    | succ i ih =>
        have hiq' : i < q := by omega
        have hin : i < n := lt_of_lt_of_le hiq' hqn
        have hisn : i + 1 < n := lt_of_lt_of_le hiq hqn
        rw [p34DqdD]
        exact div_nonneg
          (mul_nonneg (hb (i + 1) hisn) (ih hiq'))
          (add_nonneg (hc i hin) (ih hiq'))
  have hdenpos : ∀ i, i + 1 < q → 0 < c i + p34DqdD b c i := by
    intro i hiq
    have hd := hdnonneg i (by omega)
    have hcp := hcpos i hiq
    linarith
  have hsum : ∀ i, i < n →
      p34DqdB q b c i + p34DqdC q b c i = b i + c i := by
    intro i hin
    cases i with
    | zero =>
        simp [p34DqdB, p34DqdC, p34DqdD, hqpos]
        ring
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hne : c i + p34DqdD b c i ≠ 0 :=
            (hdenpos i hiq).ne'
          rw [p34DqdB, if_pos hiq, p34DqdC, if_pos hiq, p34DqdD]
          field_simp
          <;> ring
        · simp [p34DqdB, p34DqdC, hiq]
  have hprod : ∀ i, i + 1 < n →
      p34DqdB q b c (i + 1) * p34DqdC q b c i =
        b (i + 1) * c i := by
    intro i hin
    by_cases hiq : i + 1 < q
    · have hne : c i + p34DqdD b c i ≠ 0 :=
        (hdenpos i hiq).ne'
      have hiq' : i < q := by omega
      rw [p34DqdB, if_pos hiq, p34DqdC, if_pos hiq']
      field_simp
    · have hqle : q ≤ i + 1 := by omega
      by_cases hiq' : i < q
      · have heq : i + 1 = q := by omega
        have hbzero : b (i + 1) = 0 := by
          rw [heq]
          exact hstop (by omega)
        simp [p34DqdB, p34DqdC, hiq, hiq', hbzero]
      · simp [p34DqdB, p34DqdC, hiq, hiq']
  have hbnonneg : ∀ i, i < n → 0 ≤ p34DqdB q b c i := by
    intro i hin
    cases i with
    | zero => simp [p34DqdB]
    | succ i =>
        by_cases hiq : i + 1 < q
        · rw [p34DqdB, if_pos hiq]
          exact div_nonneg
            (mul_nonneg (hb (i + 1) hin) (hc i (by omega)))
            (le_of_lt (hdenpos i hiq))
        · simpa [p34DqdB, hiq] using hb (i + 1) hin
  have hcnonneg : ∀ i, i < n → 0 ≤ p34DqdC q b c i := by
    intro i hin
    by_cases hiq : i < q
    · rw [p34DqdC, if_pos hiq]
      exact add_nonneg (hc i hin) (hdnonneg i hiq)
    · simpa [p34DqdC, hiq] using hc i hin
  have hbzeros : ∀ i, 0 < i → i < n →
      (p34DqdB q b c i = 0 ↔ b i = 0) := by
    intro i hipos hin
    cases i with
    | zero => omega
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hbpos : 0 < b (i + 1) := hbefore (i + 1) (by omega) hiq
          have hcp : 0 < c i := hcpos i hiq
          have hbp : 0 < p34DqdB q b c (i + 1) := by
            rw [p34DqdB, if_pos hiq]
            exact div_pos (mul_pos hbpos hcp) (hdenpos i hiq)
          constructor
          · intro hz
            exact False.elim ((ne_of_gt hbp) hz)
          · intro hz
            exact False.elim ((ne_of_gt hbpos) hz)
        · simp [p34DqdB, hiq]
  have hczero : ∀ i, i < n → p34DqdC q b c i = 0 → c i = 0 := by
    intro i hin hz
    by_cases hiq : i < q
    · rw [p34DqdC, if_pos hiq] at hz
      have hci := hc i hin
      have hdi := hdnonneg i hiq
      linarith
    · simpa [p34DqdC, hiq] using hz
  have hcnew : ∀ i, i < n → c i = 0 →
      p34DqdC q b c i ≠ 0 → i + 1 = q := by
    intro i hin hci hcne
    by_cases hiq : i < q
    · have hle : i + 1 ≤ q := by omega
      apply le_antisymm hle
      by_contra hnot
      have hlt : i + 1 < q := by omega
      exact (ne_of_gt (hcpos i hlt)) hci
    · have : p34DqdC q b c i = 0 := by
        simp [p34DqdC, hiq, hci]
      exact False.elim (hcne this)
  have htail : ∀ i, q ≤ i →
      p34DqdB q b c i = b i ∧ p34DqdC q b c i = c i := by
    intro i hi
    cases i with
    | zero => omega
    | succ i =>
        constructor <;> simp [p34DqdB, p34DqdC, not_lt_of_ge hi]
  have hshift :
      p34LowerShift n (p34DqdB q b c) +
          p34LowerShift n (p34DqdC q b c) =
        p34LowerShift n b + p34LowerShift n c := by
    ext i j
    by_cases hij : i.val = j.val + 1
    · have hjn : j.val < n := by omega
      simp [p34LowerShift, hij, hsum j.val hjn]
    · simp [p34LowerShift, hij]
  have hshiftprod :
      p34LowerShift n (p34DqdB q b c) *
          p34LowerShift n (p34DqdC q b c) =
        p34LowerShift n b * p34LowerShift n c := by
    ext i j
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hik : i.val = k.val + 1
    · by_cases hkj : k.val = j.val + 1
      · have hjn : j.val + 1 < n := by omega
        simpa [p34LowerShift, hik, hkj] using hprod j.val hjn
      · simp [p34LowerShift, hik, hkj]
    · simp [p34LowerShift, hik]
  have hmatrix :
      p34UnitLowerBidiagonal n (p34DqdB q b c) *
          p34UnitLowerBidiagonal n (p34DqdC q b c) =
        p34UnitLowerBidiagonal n b * p34UnitLowerBidiagonal n c := by
    rw [p34UnitLowerBidiagonal, p34UnitLowerBidiagonal,
      p34UnitLowerBidiagonal, p34UnitLowerBidiagonal]
    calc
      (1 + p34LowerShift n (p34DqdB q b c)) *
          (1 + p34LowerShift n (p34DqdC q b c)) =
          1 + (p34LowerShift n (p34DqdB q b c) +
            p34LowerShift n (p34DqdC q b c)) +
            p34LowerShift n (p34DqdB q b c) *
              p34LowerShift n (p34DqdC q b c) := by noncomm_ring
      _ = 1 + (p34LowerShift n b + p34LowerShift n c) +
            p34LowerShift n b * p34LowerShift n c := by rw [hshift, hshiftprod]
      _ = (1 + p34LowerShift n b) * (1 + p34LowerShift n c) := by
        noncomm_ring
  refine ⟨hbnonneg, hcnonneg, ?_, hmatrix, hbzeros, hczero, hcnew, htail, ?_⟩
  · simp [p34DqdB]
  · omega

end HighamBench
