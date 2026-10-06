import HighamBench.P34Definitions

namespace HighamBench

lemma p34_lowerShift_mul_apply
    (n : ℕ) (x y : ℕ → ℝ) (i j : Fin (n + 1)) :
    (p34LowerShift n x * p34LowerShift n y) i j =
      if h : j.val + 1 < n + 1 then
        if i.val = j.val + 2 then x (j.val + 1) * y j.val else 0
      else 0 := by
  classical
  rw [Matrix.mul_apply]
  split_ifs with hj hi
  · let k : Fin (n + 1) := ⟨j.val + 1, hj⟩
    rw [Finset.sum_eq_single k]
    · simp [p34LowerShift, k, hi]
    · intro z hz hzk
      have hzval : z.val ≠ j.val + 1 := by
        intro hzval
        apply hzk
        apply Fin.ext
        simpa [k] using hzval
      simp [p34LowerShift, hzval]
    · simp
  · let k : Fin (n + 1) := ⟨j.val + 1, hj⟩
    rw [Finset.sum_eq_single k]
    · simp [p34LowerShift, k, hi]
    · intro z hz hzk
      have hzval : z.val ≠ j.val + 1 := by
        intro hzval
        apply hzk
        apply Fin.ext
        simpa [k] using hzval
      simp [p34LowerShift, hzval]
    · simp
  · apply Finset.sum_eq_zero
    intro k hk
    have hkval : k.val ≠ j.val + 1 := by
      intro hkval
      omega
    simp [p34LowerShift, hkval]

lemma p34_unitLowerBidiagonal_mul_eq
    (n : ℕ) (x y u v : ℕ → ℝ)
    (hsub : ∀ i, i < n → x i + y i = u i + v i)
    (hsub2 : ∀ i, i + 1 < n → x (i + 1) * y i = u (i + 1) * v i) :
    p34UnitLowerBidiagonal n x * p34UnitLowerBidiagonal n y =
      p34UnitLowerBidiagonal n u * p34UnitLowerBidiagonal n v := by
  rw [p34UnitLowerBidiagonal, p34UnitLowerBidiagonal,
    p34UnitLowerBidiagonal, p34UnitLowerBidiagonal]
  have hx :
      (1 + p34LowerShift n x) * (1 + p34LowerShift n y) =
        1 + p34LowerShift n x + p34LowerShift n y +
          p34LowerShift n x * p34LowerShift n y := by
    noncomm_ring
  have hu :
      (1 + p34LowerShift n u) * (1 + p34LowerShift n v) =
        1 + p34LowerShift n u + p34LowerShift n v +
          p34LowerShift n u * p34LowerShift n v := by
    noncomm_ring
  rw [hx, hu]
  ext i j
  simp only [Matrix.add_apply]
  rw [p34_lowerShift_mul_apply, p34_lowerShift_mul_apply]
  by_cases h1 : i.val = j.val + 1
  · have hjn : j.val < n := by omega
    have h2 : i.val ≠ j.val + 2 := by omega
    simp [p34LowerShift, h1, h2]
    linarith [hsub j.val hjn]
  · by_cases h2 : i.val = j.val + 2
    · have hjn : j.val + 1 < n := by omega
      simp [p34LowerShift, h1, h2, hsub2 j.val hjn]
    · simp [p34LowerShift, h1, h2]

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
  have hD : ∀ i, i < n → 0 ≤ p34DqdD b c i := by
    intro i hi
    induction i with
    | zero =>
        simpa [p34DqdD] using hb 0 hi
    | succ i ih =>
        rw [p34DqdD]
        exact div_nonneg
          (mul_nonneg (hb (i + 1) hi) (ih (by omega)))
          (add_nonneg (hc i (by omega)) (ih (by omega)))
  have hcpos : ∀ i, i + 1 < q → 0 < c i := by
    intro i hi
    have hin : i + 1 < n := lt_of_lt_of_le hi hqn
    have hcne : c i ≠ 0 := by
      intro hci
      have hz := hzero i hin hci
      have hp := hbefore (i + 1) (by omega) hi
      linarith
    exact lt_of_le_of_ne (hc i (by omega)) (Ne.symm hcne)
  have hdenom : ∀ i, i + 1 < q → 0 < c i + p34DqdD b c i := by
    intro i hi
    exact add_pos_of_pos_of_nonneg (hcpos i hi)
      (hD i (by omega))
  have hBnonneg : ∀ i, i < n → 0 ≤ p34DqdB q b c i := by
    intro i hi
    cases i with
    | zero => simp [p34DqdB]
    | succ i =>
        simp only [p34DqdB]
        split_ifs with hiq
        · exact div_nonneg
            (mul_nonneg (hb (i + 1) hi) (hc i (by omega)))
            (add_nonneg (hc i (by omega)) (hD i (by omega)))
        · exact hb (i + 1) hi
  have hCnonneg : ∀ i, i < n → 0 ≤ p34DqdC q b c i := by
    intro i hi
    simp only [p34DqdC]
    split_ifs
    · exact add_nonneg (hc i hi) (hD i hi)
    · exact hc i hi
  have hsum : ∀ i, i < n →
      p34DqdB q b c i + p34DqdC q b c i = b i + c i := by
    intro i hi
    cases i with
    | zero =>
        simp [p34DqdB, p34DqdC, p34DqdD, hqpos]
        ring
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hdne : c i + p34DqdD b c i ≠ 0 :=
            ne_of_gt (hdenom i hiq)
          simp only [p34DqdB, p34DqdC, if_pos hiq, p34DqdD]
          field_simp [hdne]
          <;> ring
        · simp [p34DqdB, p34DqdC, hiq]
  have hprod : ∀ i, i + 1 < n →
      p34DqdB q b c (i + 1) * p34DqdC q b c i =
        b (i + 1) * c i := by
    intro i hi
    by_cases hiq : i < q
    · by_cases hinext : i + 1 < q
      · have hdne : c i + p34DqdD b c i ≠ 0 :=
          ne_of_gt (hdenom i hinext)
        simp only [p34DqdB, p34DqdC, if_pos hinext, if_pos hiq]
        field_simp [hdne]
      · have heq : i + 1 = q := by omega
        have hbzero : b (i + 1) = 0 := by
          rw [heq]
          exact hstop (by omega)
        simp [p34DqdB, p34DqdC, hinext, hiq, hbzero]
    · have hinext : ¬ i + 1 < q := by omega
      simp [p34DqdB, p34DqdC, hiq, hinext]
  refine ⟨hBnonneg, hCnonneg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [p34DqdB]
  · exact p34_unitLowerBidiagonal_mul_eq n
      (p34DqdB q b c) (p34DqdC q b c) b c hsum hprod
  · intro i hipos hin
    cases i with
    | zero => omega
    | succ i =>
        by_cases hiq : i + 1 < q
        · have hp : 0 < b (i + 1) := hbefore (i + 1) (by omega) hiq
          have hcp : 0 < c i := hcpos i hiq
          have hdp : 0 < c i + p34DqdD b c i := hdenom i hiq
          have hbp : 0 < b (i + 1) * c i /
              (c i + p34DqdD b c i) := div_pos (mul_pos hp hcp) hdp
          simp only [p34DqdB, if_pos hiq]
          constructor <;> intro hz <;> linarith
        · simp [p34DqdB, hiq]
  · intro i hin hczero
    by_cases hiq : i < q
    · simp only [p34DqdC, if_pos hiq] at hczero
      have hd := hD i hin
      have hc' := hc i hin
      linarith
    · simpa [p34DqdC, hiq] using hczero
  · intro i hin hczer hnonzero
    by_cases hiq : i < q
    · have hnlt : ¬ i + 1 < q := by
        intro hlt
        have hz := hzero i (lt_of_lt_of_le hlt hqn) hczer
        have hp := hbefore (i + 1) (by omega) hlt
        linarith
      omega
    · exfalso
      apply hnonzero
      simp [p34DqdC, hiq, hczer]
  · intro i hi
    cases i with
    | zero => omega
    | succ i =>
        have hiq : ¬ i + 1 < q := by omega
        simp [p34DqdB, p34DqdC, hiq]
  · omega

end HighamBench
