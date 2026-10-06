import HighamBench.P36Definitions

namespace HighamBench

open scoped BigOperators NNReal

private lemma p36_abs_mul_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p36AbsMatrix (A * B) i j ≤
      (p36AbsMatrix A * p36AbsMatrix B) i j := by
  change ‖(A * B) i j‖₊ ≤ _
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact (nnnorm_sum_le _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [p36AbsMatrix, nnnorm_mul])

private lemma p36_strict_upper_pow_entry_zero {n : ℕ} {R : Type*}
    [Semiring R] (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, j.val ≤ i.val → A i j = 0) :
    ∀ (r : ℕ) (i j : Fin n), j.val < i.val + r → (A ^ r) i j = 0 := by
  intro r
  induction r with
  | zero =>
      intro i j hij
      have hne : i ≠ j := by omega
      simp [Matrix.one_apply, hne]
  | succ r ihr =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hix : x.val < i.val + r
      · rw [ihr i x hix, zero_mul]
      · have hjx : j.val ≤ x.val := by omega
        rw [hA x j hjx, mul_zero]

private lemma p36_strict_upper_nilpotent {n : ℕ} {R : Type*}
    [Semiring R] (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, j.val ≤ i.val → A i j = 0) :
    A ^ n = 0 := by
  ext i j
  apply p36_strict_upper_pow_entry_zero A hA n i j
  omega

private lemma p36_abs_pow_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAB : ∀ i j, p36AbsMatrix A i j ≤ B i j) :
    ∀ (r : ℕ) (i j : Fin n),
      p36AbsMatrix (A ^ r) i j ≤ (B ^ r) i j := by
  intro r
  induction r with
  | zero =>
      intro i j
      by_cases hij : i = j
      · subst j
        simp [p36AbsMatrix]
      · simp [p36AbsMatrix, hij]
  | succ r ihr =>
      intro i j
      rw [pow_succ, pow_succ]
      calc
        p36AbsMatrix (A ^ r * A) i j ≤
            (p36AbsMatrix (A ^ r) * p36AbsMatrix A) i j :=
          p36_abs_mul_le _ _ _ _
        _ ≤ (B ^ r * B) i j := by
          simp only [Matrix.mul_apply]
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul (ihr i x) (hAB x j) (zero_le _) (zero_le _)

private lemma p36_scalar_add_pow_apply {n : ℕ}
    (k : ℕ) (δ : ℝ≥0) (A : Matrix (Fin n) (Fin n) ℝ≥0) (i j : Fin n) :
    ((δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0) + A) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (A ^ r) i j := by
  rw [add_comm (δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) A]
  rw [((Commute.one_right A).smul_right δ).add_pow]
  simp only [Matrix.sum_apply]
  have hcast (m : ℕ) : (m : Matrix (Fin n) (Fin n) ℝ≥0) =
      (m : ℝ≥0) • 1 := by
    ext a b
    simp [Matrix.natCast_apply, Matrix.one_apply]
  apply Finset.sum_congr rfl
  intro r hr
  rw [smul_pow, hcast]
  simp only [one_pow, Matrix.mul_smul, Matrix.mul_one]
  simp [mul_comm, mul_assoc]

/-- P36-T3: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p36_t3_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p36StrictUpper N) :
    ∀ i j, p36AbsMatrix ((D + N) ^ k) i j ≤
      p36PowerMajorant k δ N i j := by
  -- PROOF_START P36-T3-H001
  intro i j
  let A : Matrix (Fin n) (Fin n) ℝ≥0 := p36AbsMatrix N
  let B : Matrix (Fin n) (Fin n) ℝ≥0 := δ • 1 + A
  have hDN : ∀ a b, p36AbsMatrix (D + N) a b ≤ B a b := by
    intro a b
    calc
      p36AbsMatrix (D + N) a b ≤
          p36AbsMatrix D a b + p36AbsMatrix N a b := by
        exact nnnorm_add_le (D a b) (N a b)
      _ ≤ B a b := by
        simpa [A, B, p36AbsMatrix, Matrix.one_apply] using
          add_le_add (hD a b) (le_refl (p36AbsMatrix N a b))
  have hA : ∀ a b, b.val ≤ a.val → A a b = 0 := by
    intro a b hab
    simp [A, p36AbsMatrix, hN a b hab]
  have hnil : A ^ n = 0 := p36_strict_upper_nilpotent A hA
  calc
    p36AbsMatrix ((D + N) ^ k) i j ≤ (B ^ k) i j :=
      p36_abs_pow_le (D + N) B hDN k i j
    _ = ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (A ^ r) i j := by
      exact p36_scalar_add_pow_apply k δ A i j
    _ = p36PowerMajorant k δ N i j := by
      unfold p36PowerMajorant
      apply Finset.sum_congr rfl
      intro r hrange
      by_cases hrn : r < n
      · simp [hrn, A]
      · have hnr : n ≤ r := Nat.le_of_not_gt hrn
        have hpow : A ^ r = 0 := pow_eq_zero_of_le hnr hnil
        simp [hrn, hpow]

end HighamBench
