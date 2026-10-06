import HighamBench.P36Definitions

namespace HighamBench

open scoped BigOperators NNReal

private lemma p36_abs_mul_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p36AbsMatrix (A * B) i j ≤
      (p36AbsMatrix A * p36AbsMatrix B) i j := by
  rw [p36AbsMatrix, Matrix.mul_apply, Matrix.mul_apply]
  simpa [p36AbsMatrix] using
    (nnnorm_sum_le Finset.univ (fun x ↦ A i x * B x j))

private lemma p36_matrix_mul_mono {n : ℕ}
    {A B C E : Matrix (Fin n) (Fin n) ℝ≥0}
    (hAC : ∀ i j, A i j ≤ C i j) (hBE : ∀ i j, B i j ≤ E i j) :
    ∀ i j, (A * B) i j ≤ (C * E) i j := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun x _ ↦
    mul_le_mul (hAC i x) (hBE x j) (zero_le _) (zero_le _)

private lemma p36_abs_pow_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (M : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAM : ∀ i j, p36AbsMatrix A i j ≤ M i j) :
    ∀ k i j, p36AbsMatrix (A ^ k) i j ≤ (M ^ k) i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      simp only [pow_zero, p36AbsMatrix, Matrix.one_apply]
      split <;> simp
  | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact le_trans (p36_abs_mul_le (A ^ k) A i j)
        (p36_matrix_mul_mono ih hAM i j)

private lemma p36_strict_upper_pow_entry_zero {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ≥0)
    (hA : ∀ i j, j.val ≤ i.val → A i j = 0) (i j : Fin n)
    (hij : j.val < i.val + r) :
    (A ^ r) i j = 0 := by
  induction r generalizing i j with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      split
      · rename_i h
        subst j
        omega
      · rfl
  | succ r ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : x.val < i.val + r
      · simp [ih i x hx]
      · have hjx : j.val ≤ x.val := by omega
        simp [hA x j hjx]

private lemma p36_abs_strict_upper {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : p36StrictUpper N) :
    ∀ i j, j.val ≤ i.val → p36AbsMatrix N i j = 0 := by
  intro i j hij
  simp [p36AbsMatrix, hN i j hij]

private lemma p36_abs_pow_eq_zero_of_ge {n r : ℕ}
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : p36StrictUpper N)
    (hr : n ≤ r) (i j : Fin n) :
    (p36AbsMatrix N ^ r) i j = 0 := by
  apply p36_strict_upper_pow_entry_zero (p36AbsMatrix N)
    (p36_abs_strict_upper N hN) i j
  omega

/-- P36-T3: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p36_t3_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p36StrictUpper N) :
    ∀ i j, p36AbsMatrix ((D + N) ^ k) i j ≤
      p36PowerMajorant k δ N i j := by
  -- PROOF_START P36-T3-H001
  intro i j
  let U : Matrix (Fin n) (Fin n) ℝ≥0 := p36AbsMatrix N
  let S : Matrix (Fin n) (Fin n) ℝ≥0 := δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)
  have hbase : ∀ a b, p36AbsMatrix (D + N) a b ≤ (S + U) a b := by
    intro a b
    calc
      p36AbsMatrix (D + N) a b ≤
          p36AbsMatrix D a b + p36AbsMatrix N a b := by
            exact nnnorm_add_le (D a b) (N a b)
      _ ≤ (if a = b then δ else 0) + p36AbsMatrix N a b :=
        add_le_add (hD a b) le_rfl
      _ = (S + U) a b := by
        simp [S, U, Matrix.one_apply]
  have hpow : p36AbsMatrix ((D + N) ^ k) i j ≤ ((S + U) ^ k) i j :=
    p36_abs_pow_le (D + N) (S + U) hbase k i j
  have hcomm : Commute U S := by
    rw [commute_iff_eq]
    simp [S]
  have hbin := congrFun (congrFun (hcomm.add_pow k) i) j
  have hSpow : ∀ q : ℕ, S ^ q = δ ^ q • (1 : Matrix (Fin n) (Fin n) ℝ≥0) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [pow_succ, ih]
        simp [S, pow_succ, smul_smul, mul_comm]
  have hfull : ((S + U) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (U ^ r) i j := by
    rw [add_comm S U, hcomm.add_pow]
    simp only [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro r hr
    have hcast : (↑(Nat.choose k r) : Matrix (Fin n) (Fin n) ℝ≥0) =
        (Nat.choose k r : ℝ≥0) • (1 : Matrix (Fin n) (Fin n) ℝ≥0) := by
      ext a b
      simp [Matrix.natCast_apply, Matrix.one_apply]
    rw [hSpow]
    rw [hcast]
    simp [mul_comm, mul_left_comm, mul_assoc]
  calc
    p36AbsMatrix ((D + N) ^ k) i j ≤ ((S + U) ^ k) i j := hpow
    _ = ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (U ^ r) i j := hfull
    _ = p36PowerMajorant k δ N i j := by
      simp only [p36PowerMajorant, U]
      apply Finset.sum_congr rfl
      intro r hr
      split_ifs with hrn
      · rfl
      · have hnr : n ≤ r := Nat.le_of_not_gt hrn
        rw [p36_abs_pow_eq_zero_of_ge N hN hnr i j]
        simp

end HighamBench
