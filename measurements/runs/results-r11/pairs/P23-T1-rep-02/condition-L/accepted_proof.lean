import HighamBench.P23Definitions
import NumStability.Algorithms.MatMul

namespace HighamBench

noncomputable def p23FPProxy (fp : P23FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := fp.model_mul
  model_div := by
    intro x y hy
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x hx
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

private lemma p23RoundedMatMul_error_bound
    (fp : P23FPModel) (n : ℕ) (A B : P23Matrix n)
    (hn : P23GammaValid fp.u n) :
    ∀ i j,
      |p23RoundedMatMul fp A B i j - p23MatMul A B i j| ≤
        p23Gamma fp.u n * p23MatMul (p23AbsMatrix A) (p23AbsMatrix B) i j := by
  intro i j
  simpa [p23RoundedMatMul, p23RoundedDotProduct, p23MatMul, p23AbsMatrix,
    p23Gamma, P23GammaValid, p23FPProxy, NumStability.fl_matMul,
    NumStability.fl_matVec, NumStability.fl_dotProduct,
    NumStability.gamma, NumStability.gammaValid] using
    (NumStability.matMul_error_bound (p23FPProxy fp) n n n A B hn i j)

private lemma p23PowerSteps_abs_nonneg {n : ℕ} (X : P23Matrix n) :
    ∀ k i j, 0 ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact abs_nonneg _
  | succ k ih =>
      intro i j
      change 0 ≤ ∑ a : Fin n,
        p23PowerSteps (p23AbsMatrix X) k i a * |X a j|
      exact Finset.sum_nonneg (fun a _ => mul_nonneg (ih i a) (abs_nonneg _))

private lemma p23PowerSteps_abs_le {n : ℕ} (X : P23Matrix n) :
    ∀ k i j,
      |p23PowerSteps X k i j| ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact le_rfl
  | succ k ih =>
      intro i j
      calc
        |p23PowerSteps X (k + 1) i j| =
            |∑ a : Fin n, p23PowerSteps X k i a * X a j| := by
              rfl
        _ ≤ ∑ a : Fin n, |p23PowerSteps X k i a * X a j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ a : Fin n, |p23PowerSteps X k i a| * |X a j| := by
          apply Finset.sum_congr rfl
          intro a _
          rw [abs_mul]
        _ ≤ ∑ a : Fin n,
              p23PowerSteps (p23AbsMatrix X) k i a * |X a j| := by
          apply Finset.sum_le_sum
          intro a _
          exact mul_le_mul_of_nonneg_right (ih i a) (abs_nonneg _)
        _ = p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
          rfl

private lemma p23Gamma_nonneg (fp : P23FPModel) {m : ℕ}
    (hm : P23GammaValid fp.u m) : 0 ≤ p23Gamma fp.u m := by
  simpa [p23Gamma, P23GammaValid, p23FPProxy, NumStability.gamma,
    NumStability.gammaValid] using
    (NumStability.gamma_nonneg (p23FPProxy fp) hm)

private lemma p23GammaValid_mono (fp : P23FPModel) {a b : ℕ}
    (hab : a ≤ b) (hb : P23GammaValid fp.u b) :
    P23GammaValid fp.u a := by
  simpa [P23GammaValid, p23FPProxy, NumStability.gammaValid] using
    (NumStability.gammaValid_mono (p23FPProxy fp) hab hb)

private lemma p23Gamma_sum_le (fp : P23FPModel) (a b : ℕ)
    (hab : P23GammaValid fp.u (a + b)) :
    p23Gamma fp.u a + p23Gamma fp.u b +
        p23Gamma fp.u a * p23Gamma fp.u b ≤
      p23Gamma fp.u (a + b) := by
  simpa [p23Gamma, P23GammaValid, p23FPProxy, NumStability.gamma,
    NumStability.gammaValid] using
    (NumStability.gamma_sum_le (p23FPProxy fp) a b hab)

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
      intro i j
      have hk_le : k * n ≤ (k + 1) * n :=
        Nat.mul_le_mul_right n (Nat.le_succ k)
      have hn_le : n ≤ (k + 1) * n := by
        rw [Nat.succ_mul]
        exact Nat.le_add_left n (k * n)
      have hkvalid : P23GammaValid fp.u (k * n) :=
        p23GammaValid_mono fp hk_le hvalid
      have hnvalid : P23GammaValid fp.u n :=
        p23GammaValid_mono fp hn_le hvalid
      have hgamma_n : 0 ≤ p23Gamma fp.u n :=
        p23Gamma_nonneg fp hnvalid
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
          _ ≤ |p23RoundedPowerSteps fp X k a b -
                    p23PowerSteps X k a b| +
                  |p23PowerSteps X k a b| := abs_add_le _ _
          _ ≤ p23Gamma fp.u (k * n) *
                    p23PowerSteps (p23AbsMatrix X) k a b +
                  p23PowerSteps (p23AbsMatrix X) k a b :=
                add_le_add (ih hkvalid a b) (p23PowerSteps_abs_le X k a b)
          _ = (1 + p23Gamma fp.u (k * n)) *
                p23PowerSteps (p23AbsMatrix X) k a b := by ring
      have hmajor :
          p23MatMul
              (p23AbsMatrix (p23RoundedPowerSteps fp X k))
              (p23AbsMatrix X) i j ≤
            (1 + p23Gamma fp.u (k * n)) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        calc
          p23MatMul
                (p23AbsMatrix (p23RoundedPowerSteps fp X k))
                (p23AbsMatrix X) i j =
              ∑ a : Fin n,
                |p23RoundedPowerSteps fp X k i a| * |X a j| := by rfl
          _ ≤ ∑ a : Fin n,
                ((1 + p23Gamma fp.u (k * n)) *
                    p23PowerSteps (p23AbsMatrix X) k i a) * |X a j| := by
              apply Finset.sum_le_sum
              intro a _
              exact mul_le_mul_of_nonneg_right (hrounded_abs i a) (abs_nonneg _)
          _ = (1 + p23Gamma fp.u (k * n)) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
              change (∑ a : Fin n,
                  ((1 + p23Gamma fp.u (k * n)) *
                    p23PowerSteps (p23AbsMatrix X) k i a) * |X a j|) =
                (1 + p23Gamma fp.u (k * n)) *
                  (∑ a : Fin n,
                    p23PowerSteps (p23AbsMatrix X) k i a * |X a j|)
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              ring
      have hlocal :
          |p23RoundedPowerSteps fp X (k + 1) i j -
              p23MatMul (p23RoundedPowerSteps fp X k) X i j| ≤
            p23Gamma fp.u n *
              ((1 + p23Gamma fp.u (k * n)) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j) := by
        calc
          |p23RoundedPowerSteps fp X (k + 1) i j -
              p23MatMul (p23RoundedPowerSteps fp X k) X i j| ≤
              p23Gamma fp.u n *
                p23MatMul
                  (p23AbsMatrix (p23RoundedPowerSteps fp X k))
                  (p23AbsMatrix X) i j := by
                exact p23RoundedMatMul_error_bound fp n
                  (p23RoundedPowerSteps fp X k) X hnvalid i j
          _ ≤ p23Gamma fp.u n *
              ((1 + p23Gamma fp.u (k * n)) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j) :=
              mul_le_mul_of_nonneg_left hmajor hgamma_n
      have hprop :
          |p23MatMul (p23RoundedPowerSteps fp X k) X i j -
              p23MatMul (p23PowerSteps X k) X i j| ≤
            p23Gamma fp.u (k * n) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
        calc
          |p23MatMul (p23RoundedPowerSteps fp X k) X i j -
              p23MatMul (p23PowerSteps X k) X i j| =
              |∑ a : Fin n,
                (p23RoundedPowerSteps fp X k i a -
                  p23PowerSteps X k i a) * X a j| := by
                congr 1
                simp only [p23MatMul]
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro a _
                ring
          _ ≤ ∑ a : Fin n,
                |(p23RoundedPowerSteps fp X k i a -
                  p23PowerSteps X k i a) * X a j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a : Fin n,
                |p23RoundedPowerSteps fp X k i a -
                  p23PowerSteps X k i a| * |X a j| := by
              apply Finset.sum_congr rfl
              intro a _
              rw [abs_mul]
          _ ≤ ∑ a : Fin n,
                (p23Gamma fp.u (k * n) *
                  p23PowerSteps (p23AbsMatrix X) k i a) * |X a j| := by
              apply Finset.sum_le_sum
              intro a _
              exact mul_le_mul_of_nonneg_right (ih hkvalid i a) (abs_nonneg _)
          _ = p23Gamma fp.u (k * n) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
              change (∑ a : Fin n,
                  (p23Gamma fp.u (k * n) *
                    p23PowerSteps (p23AbsMatrix X) k i a) * |X a j|) =
                p23Gamma fp.u (k * n) *
                  (∑ a : Fin n,
                    p23PowerSteps (p23AbsMatrix X) k i a * |X a j|)
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              ring
      have hsumvalid : P23GammaValid fp.u (k * n + n) := by
        simpa [Nat.succ_mul] using hvalid
      have hcoeff :
          p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
              p23Gamma fp.u (k * n) ≤
            p23Gamma fp.u ((k + 1) * n) := by
        calc
          p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
                p23Gamma fp.u (k * n) =
              p23Gamma fp.u (k * n) + p23Gamma fp.u n +
                p23Gamma fp.u (k * n) * p23Gamma fp.u n := by ring
          _ ≤ p23Gamma fp.u (k * n + n) :=
            p23Gamma_sum_le fp (k * n) n hsumvalid
          _ = p23Gamma fp.u ((k + 1) * n) := by rw [Nat.succ_mul]
      have hnext_nonneg :
          0 ≤ p23PowerSteps (p23AbsMatrix X) (k + 1) i j :=
        p23PowerSteps_abs_nonneg X (k + 1) i j
      calc
        |p23RoundedPowerSteps fp X (k + 1) i j -
            p23PowerSteps X (k + 1) i j| ≤
          |p23RoundedPowerSteps fp X (k + 1) i j -
              p23MatMul (p23RoundedPowerSteps fp X k) X i j| +
            |p23MatMul (p23RoundedPowerSteps fp X k) X i j -
              p23PowerSteps X (k + 1) i j| := by
                exact abs_sub_le _ _ _
        _ ≤ p23Gamma fp.u n *
                ((1 + p23Gamma fp.u (k * n)) *
                  p23PowerSteps (p23AbsMatrix X) (k + 1) i j) +
              p23Gamma fp.u (k * n) *
                p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by
              exact add_le_add hlocal hprop
        _ = (p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
                p23Gamma fp.u (k * n)) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j := by ring
        _ ≤ p23Gamma fp.u ((k + 1) * n) *
              p23PowerSteps (p23AbsMatrix X) (k + 1) i j :=
            mul_le_mul_of_nonneg_right hcoeff hnext_nonneg

end HighamBench
