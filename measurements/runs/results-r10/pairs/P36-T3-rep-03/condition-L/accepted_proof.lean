import HighamBench.P36Definitions

namespace HighamBench

open scoped BigOperators NNReal

private lemma p36_abs_mul_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p36AbsMatrix (A * B) i j ≤
      (p36AbsMatrix A * p36AbsMatrix B) i j := by
  simp only [p36AbsMatrix]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    ‖∑ x, A i x * B x j‖₊ ≤ ∑ x, ‖A i x * B x j‖₊ :=
      nnnorm_sum_le Finset.univ _
    _ = ∑ x, ‖A i x‖₊ * ‖B x j‖₊ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact nnnorm_mul _ _

private lemma p36_nnreal_matrix_mul_mono {n : ℕ}
    (A B C E : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAC : ∀ i j, A i j ≤ C i j)
    (hBE : ∀ i j, B i j ≤ E i j) :
    ∀ i j, (A * B) i j ≤ (C * E) i j := by
  intro i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul (hAC i x) (hBE x j) (zero_le _) (zero_le _)

private lemma p36_strictUpper_abs {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : p36StrictUpper N) :
    ∀ i j, j.val ≤ i.val → p36AbsMatrix N i j = 0 := by
  intro i j hji
  simp [p36AbsMatrix, hN i j hji]

private lemma p36_strictUpper_pow_entry_zero {n r : ℕ}
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
      intro x hx
      by_cases hxi : x.val < i.val + r
      · rw [ih i x hxi, zero_mul]
      · have hjx : j.val ≤ x.val := by omega
        rw [hA x j hjx, mul_zero]

private lemma p36_strictUpper_pow_eq_zero_of_dim_le {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ≥0)
    (hA : ∀ i j, j.val ≤ i.val → A i j = 0) (hr : n ≤ r) :
    A ^ r = 0 := by
  apply Matrix.ext
  intro i j
  exact p36_strictUpper_pow_entry_zero A hA i j (by
    have hj : j.val < n := j.isLt
    omega)

private lemma p36_abs_pow_le {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAM : ∀ i j, p36AbsMatrix A i j ≤ M i j) :
    ∀ i j, p36AbsMatrix (A ^ k) i j ≤ (M ^ k) i j := by
  induction k with
  | zero =>
      intro i j
      by_cases hij : i = j <;> simp [p36AbsMatrix, Matrix.one_apply, hij]
  | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact (p36_abs_mul_le (A ^ k) A i j).trans
        (p36_nnreal_matrix_mul_mono
          (p36AbsMatrix (A ^ k)) (p36AbsMatrix A) (M ^ k) M ih hAM i j)

private lemma p36_scalar_pow {n r : ℕ} (a : ℝ≥0) :
    (Matrix.scalar (Fin n) a) ^ r = Matrix.scalar (Fin n) (a ^ r) := by
  induction r with
  | zero =>
      apply Matrix.ext
      intro i j
      simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  | succ r ih =>
      rw [pow_succ, ih]
      apply Matrix.ext
      intro i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_mul,
        pow_succ]

private lemma p36_natCast_matrix {n : ℕ} (m : ℕ) :
    (m : Matrix (Fin n) (Fin n) ℝ≥0) =
      Matrix.scalar (Fin n) (m : ℝ≥0) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, hij]

/-- P36-T3: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p36_t3_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p36StrictUpper N) :
    ∀ i j, p36AbsMatrix ((D + N) ^ k) i j ≤
      p36PowerMajorant k δ N i j := by
  -- PROOF_START P36-T3-H001
  let U : Matrix (Fin n) (Fin n) ℝ≥0 := p36AbsMatrix N
  let S : Matrix (Fin n) (Fin n) ℝ≥0 := Matrix.scalar (Fin n) δ
  have hDN : ∀ i j, p36AbsMatrix (D + N) i j ≤ (S + U) i j := by
    intro i j
    calc
      p36AbsMatrix (D + N) i j ≤ ‖D i j‖₊ + ‖N i j‖₊ :=
        nnnorm_add_le _ _
      _ ≤ (if i = j then δ else 0) + ‖N i j‖₊ :=
        add_le_add (hD i j) le_rfl
      _ = (S + U) i j := by
        simp [S, U, Matrix.scalar_apply, Matrix.diagonal_apply, p36AbsMatrix]
  have hpow : ∀ i j,
      p36AbsMatrix ((D + N) ^ k) i j ≤ ((S + U) ^ k) i j :=
    p36_abs_pow_le (D + N) (S + U) hDN
  intro i j
  apply (hpow i j).trans_eq
  have hcomm : Commute S U :=
    Matrix.scalar_commute δ (fun x => mul_comm δ x) U
  rw [add_comm S U, hcomm.symm.add_pow]
  simp only [Matrix.sum_apply]
  unfold p36PowerMajorant
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hrn : r < n
  · simp only [hrn, if_true]
    change
      (U ^ r * (Matrix.scalar (Fin n) δ) ^ (k - r) *
        (Nat.choose k r : Matrix (Fin n) (Fin n) ℝ≥0)) i j =
      (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (U ^ r) i j
    rw [p36_scalar_pow, p36_natCast_matrix,
      Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.mul_diagonal, Matrix.mul_diagonal]
    ac_rfl
  · simp only [hrn, if_false]
    have hnr : n ≤ r := by omega
    have hzero : U ^ r = 0 :=
      p36_strictUpper_pow_eq_zero_of_dim_le U
        (by simpa [U] using p36_strictUpper_abs N hN) hnr
    simp [hzero]

end HighamBench
