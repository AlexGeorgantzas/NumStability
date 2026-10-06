import HighamBench.P23Definitions
import NumStability.Algorithms.MatMul

namespace HighamBench

open scoped BigOperators

noncomputable def p23AsFPModel (fp : P23FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fp.fl_mul
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

lemma p23RoundedMatMul_error_bound
    (fp : P23FPModel) (n : ℕ) (A B : P23Matrix n)
    (hvalid : P23GammaValid fp.u n) :
    ∀ i j,
      |p23RoundedMatMul fp A B i j - p23MatMul A B i j| ≤
        p23Gamma fp.u n * p23MatMul (p23AbsMatrix A) (p23AbsMatrix B) i j := by
  simpa [p23RoundedMatMul, p23RoundedDotProduct, p23MatMul,
    p23AbsMatrix, p23AsFPModel, NumStability.fl_matMul,
    NumStability.fl_matVec, NumStability.fl_dotProduct,
    NumStability.gamma, NumStability.gammaValid, p23Gamma, P23GammaValid] using
    (NumStability.matMul_error_bound (p23AsFPModel fp) n n n A B hvalid)

lemma p23GammaValid_mono (fp : P23FPModel) {a b : ℕ}
    (hab : a ≤ b) (hb : P23GammaValid fp.u b) :
    P23GammaValid fp.u a := by
  exact NumStability.gammaValid_mono (p23AsFPModel fp) hab hb

lemma p23Gamma_nonneg (fp : P23FPModel) {a : ℕ}
    (ha : P23GammaValid fp.u a) : 0 ≤ p23Gamma fp.u a := by
  simpa [p23Gamma, p23AsFPModel, NumStability.gamma] using
    (NumStability.gamma_nonneg (p23AsFPModel fp) ha)

lemma p23Gamma_sum_le (fp : P23FPModel) (a b : ℕ)
    (hab : P23GammaValid fp.u (a + b)) :
    p23Gamma fp.u a + p23Gamma fp.u b +
        p23Gamma fp.u a * p23Gamma fp.u b ≤
      p23Gamma fp.u (a + b) := by
  simpa [p23Gamma, p23AsFPModel, NumStability.gamma] using
    (NumStability.gamma_sum_le (p23AsFPModel fp) a b hab)

lemma p23MatMul_nonneg {n : ℕ} (A B : P23Matrix n)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    ∀ i j, 0 ≤ p23MatMul A B i j := by
  intro i j
  exact Finset.sum_nonneg (fun q _ => mul_nonneg (hA i q) (hB q j))

lemma p23MatMul_mono_left {n : ℕ} (A C B : P23Matrix n)
    (hAC : ∀ i j, A i j ≤ C i j) (hB : ∀ i j, 0 ≤ B i j) :
    ∀ i j, p23MatMul A B i j ≤ p23MatMul C B i j := by
  intro i j
  exact Finset.sum_le_sum (fun q _ =>
    mul_le_mul_of_nonneg_right (hAC i q) (hB q j))

lemma p23AbsMatMul_le {n : ℕ} (A B : P23Matrix n) :
    ∀ i j,
      |p23MatMul A B i j| ≤
        p23MatMul (p23AbsMatrix A) (p23AbsMatrix B) i j := by
  intro i j
  calc
    |∑ q : Fin n, A i q * B q j| ≤
        ∑ q : Fin n, |A i q * B q j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q : Fin n, |A i q| * |B q j| := by
      apply Finset.sum_congr rfl
      intro q _
      rw [abs_mul]

lemma p23AbsPower_nonneg {n : ℕ} (X : P23Matrix n) :
    ∀ k i j, 0 ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact abs_nonneg _
  | succ k ih =>
      exact p23MatMul_nonneg _ _ ih (fun i j => abs_nonneg _)

lemma p23Power_abs_le {n : ℕ} (X : P23Matrix n) :
    ∀ k i j,
      |p23PowerSteps X k i j| ≤
        p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact le_rfl
  | succ k ih =>
      intro i j
      calc
        |p23PowerSteps X (k + 1) i j| ≤
            p23MatMul (p23AbsMatrix (p23PowerSteps X k))
              (p23AbsMatrix X) i j := by
          simpa [p23PowerSteps] using p23AbsMatMul_le (p23PowerSteps X k) X i j
        _ ≤ p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
          simpa [p23PowerSteps] using
            p23MatMul_mono_left
              (p23AbsMatrix (p23PowerSteps X k))
              (p23PowerSteps (p23AbsMatrix X) k)
              (p23AbsMatrix X) ih (fun i j => abs_nonneg _) i j

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
      have hvalid_add : P23GammaValid fp.u (k * n + n) := by
        simpa [Nat.succ_mul] using hvalid
      have hvalid_prev : P23GammaValid fp.u (k * n) :=
        p23GammaValid_mono fp (Nat.le_add_right (k * n) n) hvalid_add
      have hvalid_n : P23GammaValid fp.u n :=
        p23GammaValid_mono fp (Nat.le_add_left n (k * n)) hvalid_add
      have ih' := ih hvalid_prev
      have hgamma_n : 0 ≤ p23Gamma fp.u n :=
        p23Gamma_nonneg fp hvalid_n
      have hgamma_sum :
          p23Gamma fp.u (k * n) + p23Gamma fp.u n +
              p23Gamma fp.u (k * n) * p23Gamma fp.u n ≤
            p23Gamma fp.u (k * n + n) :=
        p23Gamma_sum_le fp (k * n) n hvalid_add
      intro i j
      have hrounded_abs : ∀ a b,
          |p23RoundedPowerSteps fp X k a b| ≤
            (1 + p23Gamma fp.u (k * n)) *
              p23PowerSteps (p23AbsMatrix X) k a b := by
        intro a b
        calc
          |p23RoundedPowerSteps fp X k a b| =
              |(p23RoundedPowerSteps fp X k a b -
                  p23PowerSteps X k a b) + p23PowerSteps X k a b| := by
            congr 1
            ring
          _ ≤
              |p23RoundedPowerSteps fp X k a b - p23PowerSteps X k a b| +
                |p23PowerSteps X k a b| := abs_add_le _ _
          _ ≤
              p23Gamma fp.u (k * n) *
                  p23PowerSteps (p23AbsMatrix X) k a b +
                p23PowerSteps (p23AbsMatrix X) k a b :=
            add_le_add (ih' a b) (p23Power_abs_le X k a b)
          _ = (1 + p23Gamma fp.u (k * n)) *
                p23PowerSteps (p23AbsMatrix X) k a b := by ring
      have hmajorant :
          p23MatMul
                (p23AbsMatrix (p23RoundedPowerSteps fp X k))
                (p23AbsMatrix X) i j ≤
            (1 + p23Gamma fp.u (k * n)) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        calc
          p23MatMul
                (p23AbsMatrix (p23RoundedPowerSteps fp X k))
                (p23AbsMatrix X) i j ≤
              p23MatMul
                (fun a b => (1 + p23Gamma fp.u (k * n)) *
                  p23PowerSteps (p23AbsMatrix X) k a b)
                (p23AbsMatrix X) i j := by
            apply p23MatMul_mono_left
            · intro a b
              exact hrounded_abs a b
            · intro a b
              exact abs_nonneg _
          _ = (1 + p23Gamma fp.u (k * n)) *
                p23MatMul (p23PowerSteps (p23AbsMatrix X) k)
                  (p23AbsMatrix X) i j := by
            simp only [p23MatMul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            ring
          _ = (1 + p23Gamma fp.u (k * n)) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
            rfl
      have hpropagation :
          |p23MatMul (p23RoundedPowerSteps fp X k) X i j -
              p23MatMul (p23PowerSteps X k) X i j| ≤
            p23Gamma fp.u (k * n) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        calc
          |p23MatMul (p23RoundedPowerSteps fp X k) X i j -
              p23MatMul (p23PowerSteps X k) X i j| =
              |p23MatMul
                (fun a b => p23RoundedPowerSteps fp X k a b -
                  p23PowerSteps X k a b) X i j| := by
            congr 1
            simp only [p23MatMul]
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro q _
            ring
          _ ≤ p23MatMul
                (p23AbsMatrix
                  (fun a b => p23RoundedPowerSteps fp X k a b -
                    p23PowerSteps X k a b))
                (p23AbsMatrix X) i j :=
            p23AbsMatMul_le _ _ i j
          _ ≤ p23MatMul
                (fun a b => p23Gamma fp.u (k * n) *
                  p23PowerSteps (p23AbsMatrix X) k a b)
                (p23AbsMatrix X) i j := by
            apply p23MatMul_mono_left
            · intro a b
              exact ih' a b
            · intro a b
              exact abs_nonneg _
          _ = p23Gamma fp.u (k * n) *
                p23MatMul (p23PowerSteps (p23AbsMatrix X) k)
                  (p23AbsMatrix X) i j := by
            simp only [p23MatMul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            ring
          _ = p23Gamma fp.u (k * n) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
            rfl
      have hlocal := p23RoundedMatMul_error_bound fp n
        (p23RoundedPowerSteps fp X k) X hvalid_n i j
      calc
        |p23RoundedPowerSteps fp X (k + 1) i j -
            p23PowerSteps X (k + 1) i j| =
            |(p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X i j -
                p23MatMul (p23RoundedPowerSteps fp X k) X i j) +
              (p23MatMul (p23RoundedPowerSteps fp X k) X i j -
                p23MatMul (p23PowerSteps X k) X i j)| := by
          congr 1
          simp only [p23RoundedPowerSteps, p23PowerSteps]
          ring
        _ ≤
            |p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X i j -
                p23MatMul (p23RoundedPowerSteps fp X k) X i j| +
              |p23MatMul (p23RoundedPowerSteps fp X k) X i j -
                p23MatMul (p23PowerSteps X k) X i j| := abs_add_le _ _
        _ ≤ p23Gamma fp.u n *
                p23MatMul
                  (p23AbsMatrix (p23RoundedPowerSteps fp X k))
                  (p23AbsMatrix X) i j +
              p23Gamma fp.u (k * n) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j :=
          add_le_add hlocal hpropagation
        _ ≤ p23Gamma fp.u n *
                ((1 + p23Gamma fp.u (k * n)) *
                  p23PowerSteps (p23AbsMatrix X) (k + 1) i j) +
              p23Gamma fp.u (k * n) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j :=
          add_le_add
            (mul_le_mul_of_nonneg_left hmajorant hgamma_n) le_rfl
        _ = (p23Gamma fp.u (k * n) + p23Gamma fp.u n +
                p23Gamma fp.u (k * n) * p23Gamma fp.u n) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by ring
        _ ≤ p23Gamma fp.u (k * n + n) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j :=
          mul_le_mul_of_nonneg_right hgamma_sum
            (p23AbsPower_nonneg X (k + 1) i j)
        _ = p23Gamma fp.u ((k + 1) * n) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
          rw [Nat.succ_mul]

end HighamBench
