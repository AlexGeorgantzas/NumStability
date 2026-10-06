import HighamBench.P36Definitions

namespace HighamBench

open scoped BigOperators NNReal

private lemma p36_t3_matrix_mul_mono {n : ℕ}
    {A B C E : Matrix (Fin n) (Fin n) ℝ≥0}
    (hAC : ∀ i j, A i j ≤ C i j) (hBE : ∀ i j, B i j ≤ E i j) :
    ∀ i j, (A * B) i j ≤ (C * E) i j := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul (hAC i x) (hBE x j) (zero_le _) (zero_le _)

private lemma p36_t3_abs_mul_le {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ∀ i j, p36AbsMatrix (X * Y) i j ≤
      (p36AbsMatrix X * p36AbsMatrix Y) i j := by
  intro i j
  simp only [p36AbsMatrix, Matrix.mul_apply]
  simpa only [nnnorm_mul] using
    (nnnorm_sum_le Finset.univ (fun x ↦ X i x * Y x j))

private lemma p36_t3_abs_pow_le {n k : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ∀ i j, p36AbsMatrix (X ^ k) i j ≤ ((p36AbsMatrix X) ^ k) i j := by
  induction k with
  | zero =>
      intro i j
      by_cases h : i = j <;> simp [p36AbsMatrix, Matrix.one_apply, h]
  | succ k ih =>
      intro i j
      calc
        p36AbsMatrix (X ^ (k + 1)) i j = p36AbsMatrix (X ^ k * X) i j := by
          rw [pow_succ]
        _ ≤ (p36AbsMatrix (X ^ k) * p36AbsMatrix X) i j :=
          p36_t3_abs_mul_le _ _ i j
        _ ≤ ((p36AbsMatrix X) ^ k * p36AbsMatrix X) i j :=
          p36_t3_matrix_mul_mono ih (fun _ _ ↦ le_rfl) i j
        _ = ((p36AbsMatrix X) ^ (k + 1)) i j := by rw [pow_succ]

private lemma p36_t3_matrix_pow_mono {n k : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ≥0}
    (hAB : ∀ i j, A i j ≤ B i j) : ∀ i j, (A ^ k) i j ≤ (B ^ k) i j := by
  induction k with
  | zero =>
      intro i j
      exact le_rfl
  | succ k ih =>
      simpa only [pow_succ] using p36_t3_matrix_mul_mono ih hAB

private lemma p36_t3_strict_upper_pow_support {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ≥0)
    (hA : ∀ i j, j.val ≤ i.val → A i j = 0) :
    ∀ r i j, j.val < i.val + r → (A ^ r) i j = 0 := by
  intro r
  induction r with
  | zero =>
      intro i j hij
      by_cases h : i = j
      · subst j
        omega
      · simp [Matrix.one_apply, h]
  | succ r ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hxi : x.val < i.val + r
      · rw [ih i x hxi, zero_mul]
      · have hjx : j.val ≤ x.val := by omega
        rw [hA x j hjx, mul_zero]

private lemma p36_t3_scalar_binomial_apply {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ≥0) (δ : ℝ≥0) (i j : Fin n) :
    (((δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) + A) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (A ^ r) i j := by
  rw [add_comm, ((Commute.one_right A).smul_right δ).add_pow]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  simp [smul_pow, Matrix.mul_apply, Matrix.natCast_apply, mul_comm, mul_assoc]

/-- P36-T3: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p36_t3_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p36StrictUpper N) :
    ∀ i j, p36AbsMatrix ((D + N) ^ k) i j ≤
      p36PowerMajorant k δ N i j := by
  -- PROOF_START P36-T3-H001
  let A : Matrix (Fin n) (Fin n) ℝ≥0 := p36AbsMatrix N
  let B : Matrix (Fin n) (Fin n) ℝ≥0 := δ • 1
  have hA : ∀ i j, j.val ≤ i.val → A i j = 0 := by
    intro i j hji
    simp [A, p36AbsMatrix, hN i j hji]
  have hApow : ∀ r, n ≤ r → A ^ r = 0 := by
    intro r hnr
    funext i j
    apply p36_t3_strict_upper_pow_support A hA r i j
    omega
  have hbase : ∀ i j, p36AbsMatrix (D + N) i j ≤ (B + A) i j := by
    intro i j
    calc
      p36AbsMatrix (D + N) i j ≤ p36AbsMatrix D i j + p36AbsMatrix N i j :=
        nnnorm_add_le (D i j) (N i j)
      _ ≤ (if i = j then δ else 0) + p36AbsMatrix N i j :=
        add_le_add (hD i j) le_rfl
      _ = (B + A) i j := by
        simp [A, B, Matrix.one_apply, p36AbsMatrix]
  intro i j
  calc
    p36AbsMatrix ((D + N) ^ k) i j
        ≤ ((p36AbsMatrix (D + N)) ^ k) i j := p36_t3_abs_pow_le _ i j
    _ ≤ ((B + A) ^ k) i j := p36_t3_matrix_pow_mono hbase i j
    _ = p36PowerMajorant k δ N i j := by
      rw [p36_t3_scalar_binomial_apply A δ i j]
      simp only [p36PowerMajorant]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hrn : r < n
      · simp [hrn, A]
      · have hz : A ^ r = 0 := hApow r (Nat.le_of_not_gt hrn)
        simp [hrn, hz]

end HighamBench
