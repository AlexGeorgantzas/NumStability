import HighamBench.P23Definitions
import NumStability.Algorithms.MatMul

namespace HighamBench

open scoped BigOperators

/-- View the two operations used by the P23 model as a full library floating-point
model.  The unused operations can be interpreted exactly. -/
noncomputable def p23FPModelToFPModel (fp : P23FPModel) :
    NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fp.fl_mul
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring
  model_mul := fp.model_mul
  model_div := by
    intro x y _hy
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring
  model_sqrt := by
    intro x _hx
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

private lemma p23GammaValid_mono {u : ℝ} (hu : 0 ≤ u) {a b : ℕ}
    (hab : a ≤ b) (hb : P23GammaValid u b) : P23GammaValid u a := by
  unfold P23GammaValid at hb ⊢
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hab' hu) hb

private lemma p23RoundedMatMul_error_bound
    (fp : P23FPModel) (n : ℕ) (A B : P23Matrix n)
    (hvalid : P23GammaValid fp.u n) :
    ∀ i j,
      |p23RoundedMatMul fp A B i j - p23MatMul A B i j| ≤
        p23Gamma fp.u n * p23MatMul (p23AbsMatrix A) (p23AbsMatrix B) i j := by
  intro i j
  simpa [p23FPModelToFPModel, p23RoundedMatMul, p23RoundedDotProduct,
    p23MatMul, p23AbsMatrix, p23Gamma, P23GammaValid,
    NumStability.fl_matMul, NumStability.fl_matVec,
    NumStability.fl_dotProduct, NumStability.gamma,
    NumStability.gammaValid] using
      (NumStability.matMul_error_bound (p23FPModelToFPModel fp) n n n A B
        (by simpa [p23FPModelToFPModel, NumStability.gammaValid] using hvalid) i j)

private lemma p23PowerSteps_abs_nonneg (n k : ℕ) (X : P23Matrix n) :
    ∀ i j, 0 ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  induction k with
  | zero =>
      intro i j
      exact abs_nonneg _
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul]
      exact Finset.sum_nonneg (fun r _ =>
        mul_nonneg (ih i r) (abs_nonneg _))

private lemma p23PowerSteps_abs_le (n k : ℕ) (X : P23Matrix n) :
    ∀ i j,
      |p23PowerSteps X k i j| ≤
        p23PowerSteps (p23AbsMatrix X) k i j := by
  induction k with
  | zero =>
      intro i j
      rfl
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps, p23MatMul]
      calc
        |∑ r : Fin n, p23PowerSteps X k i r * X r j| ≤
            ∑ r : Fin n, |p23PowerSteps X k i r * X r j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ r : Fin n, |p23PowerSteps X k i r| * |X r j| := by
          apply Finset.sum_congr rfl
          intro r _
          rw [abs_mul]
        _ ≤ ∑ r : Fin n,
            p23PowerSteps (p23AbsMatrix X) k i r * |X r j| := by
          apply Finset.sum_le_sum
          intro r _
          exact mul_le_mul_of_nonneg_right (ih i r) (abs_nonneg _)

/-- P23-T1: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p23_t1_lemma_2_2
    (fp : P23FPModel) (n k : ℕ) (X : P23Matrix n)
    (hvalid : P23GammaValid fp.u (k * n)) :
    ∀ i j,
      |p23RoundedPowerSteps fp X k i j - p23PowerSteps X k i j| ≤
        p23Gamma fp.u (k * n) * p23PowerSteps (p23AbsMatrix X) k i j := by
  -- PROOF_START P23-T1-H001
  induction k with
  | zero =>
      intro i j
      simp [p23RoundedPowerSteps, p23PowerSteps, p23Gamma]
  | succ k ih =>
      have hk_le : k * n ≤ (k + 1) * n :=
        Nat.mul_le_mul_right n (Nat.le_succ k)
      have hn_le : n ≤ (k + 1) * n := by
        calc
          n = 1 * n := by simp
          _ ≤ (k + 1) * n := Nat.mul_le_mul_right n (Nat.succ_le_succ (Nat.zero_le k))
      have hvalid_k : P23GammaValid fp.u (k * n) :=
        p23GammaValid_mono fp.u_nonneg hk_le hvalid
      have hvalid_n : P23GammaValid fp.u n :=
        p23GammaValid_mono fp.u_nonneg hn_le hvalid
      have hgamma_k : 0 ≤ p23Gamma fp.u (k * n) := by
        simpa [p23Gamma, p23FPModelToFPModel, NumStability.gamma] using
          (NumStability.gamma_nonneg (n := k * n) (p23FPModelToFPModel fp)
            (by simpa [p23FPModelToFPModel, NumStability.gammaValid,
                P23GammaValid] using hvalid_k))
      have hgamma_n : 0 ≤ p23Gamma fp.u n := by
        simpa [p23Gamma, p23FPModelToFPModel, NumStability.gamma] using
          (NumStability.gamma_nonneg (n := n) (p23FPModelToFPModel fp)
            (by simpa [p23FPModelToFPModel, NumStability.gammaValid,
                P23GammaValid] using hvalid_n))
      have hgamma_sum :
          p23Gamma fp.u (k * n) + p23Gamma fp.u n +
              p23Gamma fp.u (k * n) * p23Gamma fp.u n ≤
            p23Gamma fp.u (k * n + n) := by
        simpa [p23Gamma, p23FPModelToFPModel, NumStability.gamma] using
          (NumStability.gamma_sum_le (p23FPModelToFPModel fp) (k * n) n
            (by
              simpa [Nat.succ_mul, p23FPModelToFPModel,
                NumStability.gammaValid, P23GammaValid] using hvalid))
      intro i j
      let R : P23Matrix n := p23RoundedPowerSteps fp X k
      let P : P23Matrix n := p23PowerSteps X k
      let Q : P23Matrix n := p23PowerSteps (p23AbsMatrix X) k
      have hR : ∀ a b, |R a b| ≤ (1 + p23Gamma fp.u (k * n)) * Q a b := by
        intro a b
        calc
          |R a b| = |(R a b - P a b) + P a b| := by ring_nf
          _ ≤ |R a b - P a b| + |P a b| := abs_add_le _ _
          _ ≤ p23Gamma fp.u (k * n) * Q a b + Q a b :=
            add_le_add (by simpa [R, P, Q] using ih hvalid_k a b)
              (by simpa [P, Q] using p23PowerSteps_abs_le n k X a b)
          _ = (1 + p23Gamma fp.u (k * n)) * Q a b := by ring
      have hmajorant :
          p23MatMul (p23AbsMatrix R) (p23AbsMatrix X) i j ≤
            (1 + p23Gamma fp.u (k * n)) *
              p23MatMul Q (p23AbsMatrix X) i j := by
        simp only [p23MatMul, p23AbsMatrix]
        calc
          (∑ r : Fin n, |R i r| * |X r j|) ≤
              ∑ r : Fin n,
                ((1 + p23Gamma fp.u (k * n)) * Q i r) * |X r j| := by
            apply Finset.sum_le_sum
            intro r _
            exact mul_le_mul_of_nonneg_right (hR i r) (abs_nonneg _)
          _ = (1 + p23Gamma fp.u (k * n)) *
              ∑ r : Fin n, Q i r * |X r j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r _
            ring
      have hlocal :
          |p23RoundedMatMul fp R X i j - p23MatMul R X i j| ≤
            p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) *
              p23MatMul Q (p23AbsMatrix X) i j := by
        calc
          |p23RoundedMatMul fp R X i j - p23MatMul R X i j| ≤
              p23Gamma fp.u n *
                p23MatMul (p23AbsMatrix R) (p23AbsMatrix X) i j :=
            p23RoundedMatMul_error_bound fp n R X hvalid_n i j
          _ ≤ p23Gamma fp.u n *
              ((1 + p23Gamma fp.u (k * n)) *
                p23MatMul Q (p23AbsMatrix X) i j) :=
            mul_le_mul_of_nonneg_left hmajorant hgamma_n
          _ = p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) *
                p23MatMul Q (p23AbsMatrix X) i j := by ring
      have hprop :
          |p23MatMul R X i j - p23MatMul P X i j| ≤
            p23Gamma fp.u (k * n) *
              p23MatMul Q (p23AbsMatrix X) i j := by
        simp only [p23MatMul]
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ r : Fin n, (R i r * X r j - P i r * X r j)| ≤
              ∑ r : Fin n, |R i r * X r j - P i r * X r j| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ r : Fin n, |R i r - P i r| * |X r j| := by
            apply Finset.sum_congr rfl
            intro r _
            rw [← sub_mul, abs_mul]
          _ ≤ ∑ r : Fin n,
              (p23Gamma fp.u (k * n) * Q i r) * |X r j| := by
            apply Finset.sum_le_sum
            intro r _
            exact mul_le_mul_of_nonneg_right
              (by simpa [R, P, Q] using ih hvalid_k i r) (abs_nonneg _)
          _ = p23Gamma fp.u (k * n) *
              ∑ r : Fin n, Q i r * |X r j| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r _
            ring
      have hQnext : 0 ≤ p23MatMul Q (p23AbsMatrix X) i j := by
        simp only [p23MatMul, p23AbsMatrix]
        exact Finset.sum_nonneg (fun r _ =>
          mul_nonneg (by simpa [Q] using p23PowerSteps_abs_nonneg n k X i r)
            (abs_nonneg _))
      change
        |p23RoundedMatMul fp R X i j - p23MatMul P X i j| ≤
          p23Gamma fp.u ((k + 1) * n) *
            p23MatMul Q (p23AbsMatrix X) i j
      calc
        |p23RoundedMatMul fp R X i j - p23MatMul P X i j| ≤
            |p23RoundedMatMul fp R X i j - p23MatMul R X i j| +
              |p23MatMul R X i j - p23MatMul P X i j| := by
          calc
            _ = |(p23RoundedMatMul fp R X i j - p23MatMul R X i j) +
                  (p23MatMul R X i j - p23MatMul P X i j)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        _ ≤
            (p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
              p23Gamma fp.u (k * n)) *
                p23MatMul Q (p23AbsMatrix X) i j := by
          calc
            _ ≤
                p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) *
                    p23MatMul Q (p23AbsMatrix X) i j +
                  p23Gamma fp.u (k * n) *
                    p23MatMul Q (p23AbsMatrix X) i j := add_le_add hlocal hprop
            _ = _ := by ring
        _ ≤ p23Gamma fp.u (k * n + n) *
              p23MatMul Q (p23AbsMatrix X) i j := by
          apply mul_le_mul_of_nonneg_right _ hQnext
          convert hgamma_sum using 1 <;> ring
        _ = p23Gamma fp.u ((k + 1) * n) *
              p23MatMul Q (p23AbsMatrix X) i j := by
          rw [Nat.succ_mul]

end HighamBench
