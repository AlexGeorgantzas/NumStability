import HighamBench.P36Definitions

namespace HighamBench

open scoped BigOperators NNReal


lemma p36_test_scalar_term {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ≥0) (a : ℝ≥0) (r m q : ℕ) (i j : Fin n) :
    (B ^ r * (a • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ m *
        (q : Matrix (Fin n) (Fin n) ℝ≥0)) i j =
      (q : ℝ≥0) * a ^ m * (B ^ r) i j := by
  simp [Matrix.mul_apply, Matrix.natCast_apply, smul_pow, mul_comm, mul_left_comm,
    mul_assoc]

lemma p36_test_binomial {n k : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ≥0) (a : ℝ≥0) (i j : Fin n) :
    ((B + a • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * a ^ (k - r) * (B ^ r) i j := by
  have hc : Commute B (a • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) := by
    show B * (a • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) =
      (a • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) * B
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hc.add_pow]
  rw [Matrix.sum_apply]
  change (∑ r ∈ Finset.range (k + 1),
      (B ^ r * (a • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ (k - r) *
        (Nat.choose k r : Matrix (Fin n) (Fin n) ℝ≥0)) i j) = _
  apply Finset.sum_congr rfl
  intro r hr
  exact p36_test_scalar_term B a r (k - r) (Nat.choose k r) i j

lemma p36_test_strictUpper_pow_apply {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ≥0)
    (hB : ∀ i j, j.val ≤ i.val → B i j = 0) (m : ℕ) :
    ∀ i j, j.val < i.val + m → (B ^ m) i j = 0 := by
  induction m with
  | zero =>
      intro i j hji
      have hij : i ≠ j := by
        intro hij
        subst j
        omega
      rw [pow_zero, Matrix.one_apply_ne hij]
  | succ m ih =>
      intro i j hji
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro t ht
      by_cases hit : t.val < i.val + m
      · rw [ih i t hit, zero_mul]
      · have himt : i.val + m ≤ t.val := Nat.not_lt.mp hit
        have hjt : j.val ≤ t.val := by omega
        rw [hB t j hjt, mul_zero]

lemma p36_test_truncated_binomial {n k : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ≥0) (a : ℝ≥0)
    (hB : ∀ i j, j.val ≤ i.val → B i j = 0) (i j : Fin n) :
    ((B + a • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        if r < n then
          (Nat.choose k r : ℝ≥0) * a ^ (k - r) * (B ^ r) i j
        else 0 := by
  rw [p36_test_binomial B a i j]
  apply Finset.sum_congr rfl
  intro r hrange
  by_cases hrn : r < n
  · simp [hrn]
  · have hjir : j.val < i.val + r := by
      have hjn := j.isLt
      omega
    have hz := p36_test_strictUpper_pow_apply B hB r i j hjir
    simp [hrn, hz]

lemma p36_test_abs_add_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∀ i j, p36AbsMatrix (A + B) i j ≤
      (p36AbsMatrix A + p36AbsMatrix B) i j := by
  intro i j
  exact nnnorm_add_le (A i j) (B i j)

lemma p36_test_abs_mul_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    ∀ i j, p36AbsMatrix (A * B) i j ≤
      (p36AbsMatrix A * p36AbsMatrix B) i j := by
  intro i j
  simp only [p36AbsMatrix, Matrix.mul_apply]
  calc
    ‖∑ x, A i x * B x j‖₊ ≤ ∑ x, ‖A i x * B x j‖₊ :=
      nnnorm_sum_le Finset.univ (fun x ↦ A i x * B x j)
    _ = ∑ x, ‖A i x‖₊ * ‖B x j‖₊ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact nnnorm_mul (A i x) (B x j)

lemma p36_test_matrix_mul_mono {n : ℕ}
    (A B C E : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAC : ∀ i j, A i j ≤ C i j) (hBE : ∀ i j, B i j ≤ E i j) :
    ∀ i j, (A * B) i j ≤ (C * E) i j := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul (hAC i x) (hBE x j) (zero_le _) (zero_le _)

lemma p36_test_abs_pow_le_pow {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAM : ∀ i j, p36AbsMatrix A i j ≤ M i j) :
    ∀ k i j, p36AbsMatrix (A ^ k) i j ≤ (M ^ k) i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      by_cases hij : i = j
      · subst j
        simp [p36AbsMatrix, Matrix.one_apply]
      · simp [p36AbsMatrix, Matrix.one_apply, hij]
  | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact le_trans (p36_test_abs_mul_le (A ^ k) A i j)
        (p36_test_matrix_mul_mono _ _ _ _ (ih) hAM i j)

/-- P36-T3: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p36_t3_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p36StrictUpper N) :
    ∀ i j, p36AbsMatrix ((D + N) ^ k) i j ≤
      p36PowerMajorant k δ N i j := by
  -- PROOF_START P36-T3-H001
  have hBN : ∀ i j, j.val ≤ i.val → p36AbsMatrix N i j = 0 := by
    intro i j hji
    simp [p36AbsMatrix, hN i j hji]
  have hbase : ∀ i j, p36AbsMatrix (D + N) i j ≤
      (p36AbsMatrix N +
        δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) i j := by
    intro i j
    calc
      p36AbsMatrix (D + N) i j ≤
          p36AbsMatrix D i j + p36AbsMatrix N i j :=
        p36_test_abs_add_le D N i j
      _ ≤ (if i = j then δ else 0) + p36AbsMatrix N i j :=
        add_le_add (hD i j) (le_refl _)
      _ = (p36AbsMatrix N +
          δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) i j := by
        simp [Matrix.one_apply, add_comm]
  intro i j
  calc
    p36AbsMatrix ((D + N) ^ k) i j ≤
        ((p36AbsMatrix N +
          δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ k) i j :=
      p36_test_abs_pow_le_pow (D + N) _ hbase k i j
    _ = p36PowerMajorant k δ N i j := by
      simpa [p36PowerMajorant] using
        (p36_test_truncated_binomial (p36AbsMatrix N) δ hBN i j)

end HighamBench
