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
    simp only [p36AbsMatrix]
    exact le_of_eq (nnnorm_mul (A i a) (B a j))

private lemma p36_strictUpper_abs_pow_apply_eq_zero {n r : ℕ}
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : p36StrictUpper N)
    (i j : Fin n) (hij : j.val < i.val + r) :
    (p36AbsMatrix N ^ r) i j = 0 := by
  induction r generalizing i j with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      split
      · omega
      · rfl
  | succ r ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : a.val < i.val + r
      · rw [ih i a ha, zero_mul]
      · have hja : j.val ≤ a.val := by omega
        have hzero : p36AbsMatrix N a j = 0 := by
          simp [p36AbsMatrix, hN a j hja]
        rw [hzero, mul_zero]

private lemma p36_strictUpper_abs_pow_eq_zero {n r : ℕ}
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : p36StrictUpper N)
    (hr : n ≤ r) :
    p36AbsMatrix N ^ r = 0 := by
  funext i j
  exact p36_strictUpper_abs_pow_apply_eq_zero N hN i j (by omega)

private lemma p36_matrix_mul_mono {n : ℕ}
    (A B C E : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAC : ∀ i j, A i j ≤ C i j) (hBE : ∀ i j, B i j ≤ E i j)
    (i j : Fin n) :
    (A * B) i j ≤ (C * E) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun a _ ↦ mul_le_mul' (hAC i a) (hBE a j)

private lemma p36_abs_pow_le_pow {n : ℕ}
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
        simp [p36AbsMatrix]
      · simp [p36AbsMatrix, hij]
  | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact (p36_abs_mul_le (A ^ k) A i j).trans
        (p36_matrix_mul_mono _ _ _ _ ih hAM i j)

private lemma p36_abs_add_le_scalar_add_abs {n : ℕ}
    (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0) :
    ∀ i j, p36AbsMatrix (D + N) i j ≤
      (Matrix.scalar (Fin n) δ + p36AbsMatrix N) i j := by
  intro i j
  calc
    p36AbsMatrix (D + N) i j = ‖D i j + N i j‖₊ := rfl
    _ ≤ ‖D i j‖₊ + ‖N i j‖₊ := nnnorm_add_le _ _
    _ ≤ (if i = j then δ else 0) + ‖N i j‖₊ :=
      add_le_add (hD i j) le_rfl
    _ = (Matrix.scalar (Fin n) δ + p36AbsMatrix N) i j := by
      by_cases hij : i = j
      · subst j
        simp [p36AbsMatrix]
      · simp [p36AbsMatrix, hij]

private lemma p36_scalar_add_pow_apply {n k : ℕ}
    (δ : ℝ≥0) (B : Matrix (Fin n) (Fin n) ℝ≥0) (i j : Fin n) :
    ((Matrix.scalar (Fin n) δ + B) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (B ^ r) i j := by
  let S : Matrix (Fin n) (Fin n) ℝ≥0 := Matrix.scalar (Fin n) δ
  have hcomm : Commute B S :=
    Matrix.scalar_commute δ (fun x ↦ Commute.all δ x) B |>.symm
  change ((S + B) ^ k) i j = _
  rw [add_comm S B, hcomm.add_pow]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  have hSpow : S ^ (k - r) = Matrix.scalar (Fin n) (δ ^ (k - r)) := by
    exact (map_pow (Matrix.scalar (Fin n)) δ (k - r)).symm
  rw [hSpow]
  change
    (B ^ r * Matrix.diagonal (fun _ : Fin n ↦ δ ^ (k - r)) *
      Matrix.diagonal (fun _ : Fin n ↦ (Nat.choose k r : ℝ≥0))) i j = _
  simp only [Matrix.mul_diagonal]
  ring

/-- P36-T3: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p36_t3_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p36StrictUpper N) :
    ∀ i j, p36AbsMatrix ((D + N) ^ k) i j ≤
      p36PowerMajorant k δ N i j := by
  -- PROOF_START P36-T3-H001
  intro i j
  calc
    p36AbsMatrix ((D + N) ^ k) i j ≤
        ((Matrix.scalar (Fin n) δ + p36AbsMatrix N) ^ k) i j :=
      p36_abs_pow_le_pow (D + N)
        (Matrix.scalar (Fin n) δ + p36AbsMatrix N)
        (p36_abs_add_le_scalar_add_abs D N δ hD) k i j
    _ = ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) *
          (p36AbsMatrix N ^ r) i j :=
      p36_scalar_add_pow_apply δ (p36AbsMatrix N) i j
    _ = p36PowerMajorant k δ N i j := by
      rw [p36PowerMajorant]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hrn : r < n
      · simp [hrn]
      · have hpow : p36AbsMatrix N ^ r = 0 :=
          p36_strictUpper_abs_pow_eq_zero N hN (Nat.le_of_not_gt hrn)
        simp [hrn, hpow]

end HighamBench
