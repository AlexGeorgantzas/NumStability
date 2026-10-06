import HighamBench.P36Definitions

namespace HighamBench

open scoped BigOperators NNReal

private lemma p36_abs_mul_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p36AbsMatrix (A * B) i j ≤
      (p36AbsMatrix A * p36AbsMatrix B) i j := by
  rw [p36AbsMatrix, Matrix.mul_apply, Matrix.mul_apply]
  refine (nnnorm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun a _ ↦ by
    simp only [nnnorm_mul, p36AbsMatrix]
    exact le_rfl

private lemma p36_abs_pow_le_pow_abs {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : ∀ k i j,
    p36AbsMatrix (A ^ k) i j ≤ (p36AbsMatrix A ^ k) i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      simp only [pow_zero, p36AbsMatrix, Matrix.one_apply]
      split <;> simp
  | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      refine (p36_abs_mul_le (A ^ k) A i j).trans ?_
      rw [Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_le_sum fun a _ ↦
        mul_le_mul (ih i a) le_rfl (zero_le _) (zero_le _)

private lemma p36_matrix_pow_mono {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ≥0)
    (h : ∀ i j, A i j ≤ B i j) : ∀ k i j,
    (A ^ k) i j ≤ (B ^ k) i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact le_rfl
  | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_le_sum fun a _ ↦
        mul_le_mul (ih i a) (h a j) (zero_le _) (zero_le _)

private lemma p36_abs_add_majorized {n : ℕ}
    (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0) : ∀ i j,
    p36AbsMatrix (D + N) i j ≤
      (δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0) + p36AbsMatrix N) i j := by
  intro i j
  refine (nnnorm_add_le (D i j) (N i j)).trans ?_
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  simp only [smul_eq_mul, p36AbsMatrix]
  calc
    ‖D i j‖₊ + ‖N i j‖₊ ≤
        (if i = j then δ else 0) + ‖N i j‖₊ :=
      add_le_add (hD i j) le_rfl
    _ = (δ * if i = j then 1 else 0) + ‖N i j‖₊ := by
      split <;> simp_all

private lemma p36_strict_upper_pow_entry_zero {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ≥0)
    (hB : ∀ i j, j.val ≤ i.val → B i j = 0) : ∀ r i j,
    j.val < i.val + r → (B ^ r) i j = 0 := by
  intro r
  induction r with
  | zero =>
      intro i j hij
      rw [pow_zero, Matrix.one_apply]
      have hne : i ≠ j := by
        intro h
        subst j
        omega
      simp [hne]
  | succ r ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro a ha
      by_cases hia : a.val < i.val + r
      · rw [ih i a hia, zero_mul]
      · have haj : j.val ≤ a.val := by omega
        rw [hB a j haj, mul_zero]

private lemma p36_strict_upper_pow_eq_zero {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ≥0)
    (hB : ∀ i j, j.val ≤ i.val → B i j = 0)
    {r : ℕ} (hr : n ≤ r) : B ^ r = 0 := by
  apply Matrix.ext
  intro i j
  apply p36_strict_upper_pow_entry_zero B hB r i j
  omega

private lemma p36_abs_strict_upper {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : p36StrictUpper N) :
    ∀ i j, j.val ≤ i.val → p36AbsMatrix N i j = 0 := by
  intro i j hij
  simp [p36AbsMatrix, hN i j hij]

private lemma p36_scalar_binomial_entry {n k : ℕ} (δ : ℝ≥0)
    (B : Matrix (Fin n) (Fin n) ℝ≥0) (i j : Fin n) :
    ((δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0) + B) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (B ^ r) i j := by
  have hcomm : Commute B (δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) :=
    (Commute.one_right B).smul_right δ
  rw [add_comm]
  rw [hcomm.add_pow]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  rw [smul_pow, one_pow]
  simp [Matrix.mul_apply, Matrix.natCast_apply, mul_assoc, mul_comm, mul_left_comm]

/-- P36-T3: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p36_t3_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p36StrictUpper N) :
    ∀ i j, p36AbsMatrix ((D + N) ^ k) i j ≤
      p36PowerMajorant k δ N i j := by
  -- PROOF_START P36-T3-H001
  intro i j
  let B : Matrix (Fin n) (Fin n) ℝ≥0 := p36AbsMatrix N
  let S : Matrix (Fin n) (Fin n) ℝ≥0 := δ • 1 + B
  calc
    p36AbsMatrix ((D + N) ^ k) i j ≤
        (p36AbsMatrix (D + N) ^ k) i j :=
      p36_abs_pow_le_pow_abs (D + N) k i j
    _ ≤ (S ^ k) i j := by
      apply p36_matrix_pow_mono
      intro a b
      exact p36_abs_add_majorized D N δ hD a b
    _ = ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (B ^ r) i j := by
      exact p36_scalar_binomial_entry δ B i j
    _ = p36PowerMajorant k δ N i j := by
      rw [p36PowerMajorant]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hrn : r < n
      · simp only [hrn, if_pos]
        rfl
      · have hpow : B ^ r = 0 :=
          p36_strict_upper_pow_eq_zero B
            (by
              intro a b hab
              exact p36_abs_strict_upper N hN a b hab)
            (Nat.le_of_not_gt hrn)
        simp [hrn, hpow]

end HighamBench
