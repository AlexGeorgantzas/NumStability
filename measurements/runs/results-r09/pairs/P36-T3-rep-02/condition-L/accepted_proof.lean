import HighamBench.P36Definitions

namespace HighamBench

open scoped BigOperators NNReal

private lemma p36_abs_mul_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p36AbsMatrix (A * B) i j ≤
      (p36AbsMatrix A * p36AbsMatrix B) i j := by
  rw [p36AbsMatrix, Matrix.mul_apply, Matrix.mul_apply]
  calc
    ‖∑ x, A i x * B x j‖₊ ≤ ∑ x, ‖A i x * B x j‖₊ :=
      nnnorm_sum_le Finset.univ (fun x ↦ A i x * B x j)
    _ = ∑ x, ‖A i x‖₊ * ‖B x j‖₊ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [nnnorm_mul]

private lemma p36_nnreal_mul_mono {n : ℕ}
    {A B C E : Matrix (Fin n) (Fin n) ℝ≥0}
    (hAC : ∀ i j, A i j ≤ C i j) (hBE : ∀ i j, B i j ≤ E i j)
    (i j : Fin n) : (A * B) i j ≤ (C * E) i j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_le_sum fun x _ ↦
    mul_le_mul (hAC i x) (hBE x j) (zero_le _) (zero_le _)

private lemma p36_strictUpper_pow_apply_eq_zero {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℝ≥0}
    (hB : ∀ i j, j.val ≤ i.val → B i j = 0) (m : ℕ) :
    ∀ i j, j.val < i.val + m → (B ^ m) i j = 0 := by
  induction m with
  | zero =>
      intro i j hji
      have hij : i ≠ j := fun h ↦ by
        rw [h] at hji
        exact (Nat.lt_irrefl _ hji)
      rw [pow_zero, Matrix.one_apply_ne hij]
  | succ p ih =>
      intro i j hji
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun x hx ↦ ?_
      by_cases hxi : x.val < i.val + p
      · rw [ih i x hxi, zero_mul]
      · have hjx : j.val ≤ x.val := by omega
        rw [hB x j hjx, mul_zero]

private lemma p36_abs_pow_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAS : ∀ i j, p36AbsMatrix A i j ≤ S i j) (k : ℕ) :
    ∀ i j, p36AbsMatrix (A ^ k) i j ≤ (S ^ k) i j := by
  induction k with
  | zero =>
      intro i j
      by_cases hij : i = j
      · simp [p36AbsMatrix, Matrix.one_apply, hij]
      · simp [p36AbsMatrix, Matrix.one_apply, hij]
  | succ m ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact (p36_abs_mul_le (A ^ m) A i j).trans
        (p36_nnreal_mul_mono ih hAS i j)

private lemma p36_scalar_add_pow_apply {n k : ℕ}
    (δ : ℝ≥0) (B : Matrix (Fin n) (Fin n) ℝ≥0) (i j : Fin n) :
    ((δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0) + B) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (B ^ r) i j := by
  have hcomm : Commute (δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) B := by
    rw [Matrix.smul_one_eq_diagonal]
    apply Matrix.ext
    intro a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    exact mul_comm _ _
  calc
    ((δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0) + B) ^ k) i j =
        (∑ m ∈ Finset.range (k + 1),
          (δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ m * B ^ (k - m) *
            (Nat.choose k m : Matrix (Fin n) (Fin n) ℝ≥0)) i j := by
          rw [hcomm.add_pow]
    _ = ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (B ^ r) i j := by
      rw [Matrix.sum_apply]
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_range] at hr
      have hidx : k + 1 - 1 - r = k - r := by omega
      rw [hidx]
      have hsub : k - (k - r) = r := by omega
      rw [hsub, Nat.choose_symm (by omega : r ≤ k)]
      rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_pow, Matrix.mul_assoc,
        Matrix.diagonal_mul]
      change δ ^ (k - r) *
          ((B ^ r * Matrix.diagonal
            (fun _ : Fin n ↦ (Nat.choose k r : ℝ≥0))) i j) = _
      rw [Matrix.mul_diagonal]
      ac_rfl

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
  have hmajorizes : ∀ a b, p36AbsMatrix (D + N) a b ≤ S a b := by
    intro a b
    calc
      p36AbsMatrix (D + N) a b = ‖D a b + N a b‖₊ := by
        rfl
      _ ≤ ‖D a b‖₊ + ‖N a b‖₊ := nnnorm_add_le _ _
      _ ≤ (if a = b then δ else 0) + ‖N a b‖₊ :=
        add_le_add (hD a b) le_rfl
      _ = S a b := by
        by_cases hab : a = b
        · simp [S, B, p36AbsMatrix, Matrix.one_apply, hab]
        · simp [S, B, p36AbsMatrix, Matrix.one_apply, hab]
  have hB : ∀ a b, b.val ≤ a.val → B a b = 0 := by
    intro a b hba
    simp [B, p36AbsMatrix, hN a b hba]
  calc
    p36AbsMatrix ((D + N) ^ k) i j ≤ (S ^ k) i j :=
      p36_abs_pow_le (D + N) S hmajorizes k i j
    _ = ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (B ^ r) i j :=
      p36_scalar_add_pow_apply δ B i j
    _ = p36PowerMajorant k δ N i j := by
      rw [p36PowerMajorant]
      apply Finset.sum_congr rfl
      intro r hrange
      by_cases hrn : r < n
      · rw [if_pos hrn]
      · rw [if_neg hrn]
        have hzero : (B ^ r) i j = 0 :=
          p36_strictUpper_pow_apply_eq_zero hB r i j (by
            have hj : j.val < n := j.isLt
            have hnr : n ≤ r := Nat.not_lt.mp hrn
            omega)
        rw [hzero, mul_zero]

end HighamBench
