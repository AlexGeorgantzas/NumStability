import HighamBench.P36Definitions

namespace HighamBench

open scoped BigOperators NNReal

private lemma p36_abs_pow_le {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℝ≥0)
    (hXB : ∀ i j, p36AbsMatrix X i j ≤ B i j) :
    ∀ k i j, p36AbsMatrix (X ^ k) i j ≤ (B ^ k) i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      by_cases hij : i = j <;>
        simp [p36AbsMatrix, Matrix.one_apply, hij]
  | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      change ‖(X ^ k * X) i j‖₊ ≤ (B ^ k * B) i j
      rw [Matrix.mul_apply, Matrix.mul_apply]
      calc
        _ ≤ ∑ x, ‖(X ^ k) i x * X x j‖₊ := nnnorm_sum_le _ _
        _ = ∑ x, p36AbsMatrix (X ^ k) i x * p36AbsMatrix X x j := by
          simp [p36AbsMatrix]
        _ ≤ ∑ x, (B ^ k) i x * B x j := by
          gcongr with x
          · exact ih i x
          · exact hXB x j

private lemma p36_abs_strictUpper_pow_eq_zero {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : p36StrictUpper N) :
    ∀ r (i j : Fin n), j.val < i.val + r →
      (p36AbsMatrix N ^ r) i j = 0 := by
  intro r
  induction r with
  | zero =>
      intro i j hij
      simp only [pow_zero, Matrix.one_apply]
      split
      · omega
      · rfl
  | succ r ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hxi : x.val < i.val + r
      · rw [ih i x hxi, zero_mul]
      · have hjx : j.val ≤ x.val := by omega
        rw [show p36AbsMatrix N x j = 0 by
          simp [p36AbsMatrix, hN x j hjx]]
        exact mul_zero _

/-- P36-T3: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p36_t3_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p36StrictUpper N) :
    ∀ i j, p36AbsMatrix ((D + N) ^ k) i j ≤
      p36PowerMajorant k δ N i j := by
  -- PROOF_START P36-T3-H001
  let A : Matrix (Fin n) (Fin n) ℝ≥0 := p36AbsMatrix N
  let S : Matrix (Fin n) (Fin n) ℝ≥0 := δ • 1
  have hbase : ∀ i j, p36AbsMatrix (D + N) i j ≤ (A + S) i j := by
    intro i j
    calc
      p36AbsMatrix (D + N) i j ≤ ‖D i j‖₊ + ‖N i j‖₊ := by
        simpa [p36AbsMatrix] using nnnorm_add_le (D i j) (N i j)
      _ ≤ (if i = j then δ else 0) + ‖N i j‖₊ := by
        gcongr
        exact hD i j
      _ = (A + S) i j := by
        simp [A, S, p36AbsMatrix, Matrix.one_apply, add_comm]
  intro i j
  calc
    p36AbsMatrix ((D + N) ^ k) i j ≤ ((A + S) ^ k) i j :=
      p36_abs_pow_le (D + N) (A + S) hbase k i j
    _ = p36PowerMajorant k δ N i j := by
      have hcomm : Commute A S := by
        change A * S = S * A
        simp [S, Matrix.mul_smul, Matrix.smul_mul]
      rw [hcomm.add_pow]
      unfold p36PowerMajorant
      rw [Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hrn : r < n
      · simp [hrn, A, S, smul_pow, Matrix.mul_apply, Matrix.natCast_apply,
          mul_comm, mul_left_comm, mul_assoc]
      · have hrge : n ≤ r := by omega
        have hzero : (p36AbsMatrix N ^ r) i j = 0 := by
          apply p36_abs_strictUpper_pow_eq_zero N hN r i j
          have hj : j.val < n := j.isLt
          omega
        simp [hrn, A, S, smul_pow, Matrix.mul_apply, Matrix.natCast_apply,
          hzero, mul_comm, mul_left_comm, mul_assoc]

end HighamBench
