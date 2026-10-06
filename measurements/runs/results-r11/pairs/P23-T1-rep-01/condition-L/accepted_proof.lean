import HighamBench.P23Definitions
import Mathlib.Tactic
import NumStability.Algorithms.DotProduct

namespace HighamBench

open scoped BigOperators

/-- Regard the two-operation model used in this problem as a full model by
making all of the unused operations exact. -/
noncomputable def p23ToFPModel (fp : P23FPModel) : NumStability.FPModel where
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

private lemma p23GammaValid_mono (fp : P23FPModel) {a b : ℕ}
    (hab : a ≤ b) (hb : P23GammaValid fp.u b) :
    P23GammaValid fp.u a := by
  simpa [P23GammaValid, p23ToFPModel] using
    (NumStability.gammaValid_mono (p23ToFPModel fp) hab hb)

private lemma p23Gamma_nonneg (fp : P23FPModel) {a : ℕ}
    (ha : P23GammaValid fp.u a) : 0 ≤ p23Gamma fp.u a := by
  simpa [p23Gamma, p23ToFPModel, NumStability.gamma] using
    (NumStability.gamma_nonneg (p23ToFPModel fp) ha)

private lemma p23Gamma_sum_le (fp : P23FPModel) (a b : ℕ)
    (hab : P23GammaValid fp.u (a + b)) :
    p23Gamma fp.u a + p23Gamma fp.u b +
        p23Gamma fp.u a * p23Gamma fp.u b ≤
      p23Gamma fp.u (a + b) := by
  simpa [p23Gamma, p23ToFPModel, NumStability.gamma] using
    (NumStability.gamma_sum_le (p23ToFPModel fp) a b hab)

private lemma p23RoundedDotProduct_error_bound
    (fp : P23FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hn : P23GammaValid fp.u n) :
    |p23RoundedDotProduct fp n x y - ∑ a : Fin n, x a * y a| ≤
      p23Gamma fp.u n * ∑ a : Fin n, |x a| * |y a| := by
  simpa [p23RoundedDotProduct, p23Gamma, p23ToFPModel,
    NumStability.fl_dotProduct, NumStability.gamma] using
    (NumStability.dotProduct_error_bound (p23ToFPModel fp) n x y hn)

/-- Taking componentwise absolute values before forming a matrix power gives
a componentwise majorant of the exact power. -/
private lemma p23PowerSteps_abs_le (n k : ℕ) (X : P23Matrix n) :
    ∀ i j,
      |p23PowerSteps X k i j| ≤
        p23PowerSteps (p23AbsMatrix X) k i j := by
  induction k with
  | zero =>
      intro i j
      simp [p23PowerSteps, p23AbsMatrix]
  | succ k ih =>
      intro i j
      simp only [p23PowerSteps]
      change
        |∑ a : Fin n, p23PowerSteps X k i a * X a j| ≤
          ∑ a : Fin n,
            p23PowerSteps (p23AbsMatrix X) k i a * |X a j|
      calc
        |∑ a : Fin n, p23PowerSteps X k i a * X a j|
            ≤ ∑ a : Fin n, |p23PowerSteps X k i a * X a j| :=
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

/-- P23-T1: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p23_t1_lemma_2_2
    (fp : P23FPModel) (n k : ℕ) (X : P23Matrix n)
    (hvalid : P23GammaValid fp.u (k * n)) :
    ∀ i j,
      |p23RoundedPowerSteps fp X k i j - p23PowerSteps X k i j| ≤
        p23Gamma fp.u (k * n) * p23PowerSteps (p23AbsMatrix X) k i j := by
  -- PROOF_START P23-T1-H001
  revert hvalid
  induction k with
  | zero =>
      intro _ i j
      simp [p23RoundedPowerSteps, p23PowerSteps, p23Gamma]
  | succ k ih =>
      intro hvalid i j
      have hk_le : k * n ≤ (k + 1) * n := by
        exact Nat.mul_le_mul_right n (Nat.le_succ k)
      have hn_le : n ≤ (k + 1) * n := by
        rw [Nat.succ_mul, Nat.add_comm]
        exact Nat.le_add_right n (k * n)
      have hkvalid : P23GammaValid fp.u (k * n) :=
        p23GammaValid_mono fp hk_le hvalid
      have hnvalid : P23GammaValid fp.u n :=
        p23GammaValid_mono fp hn_le hvalid
      have hgk : 0 ≤ p23Gamma fp.u (k * n) :=
        p23Gamma_nonneg fp hkvalid
      have hgn : 0 ≤ p23Gamma fp.u n :=
        p23Gamma_nonneg fp hnvalid
      have hmajor : ∀ a : Fin n,
          0 ≤ p23PowerSteps (p23AbsMatrix X) k i a := by
        intro a
        exact le_trans (abs_nonneg _) (p23PowerSteps_abs_le n k X i a)
      have hrounded_major : ∀ a : Fin n,
          |p23RoundedPowerSteps fp X k i a| ≤
            (1 + p23Gamma fp.u (k * n)) *
              p23PowerSteps (p23AbsMatrix X) k i a := by
        intro a
        calc
          |p23RoundedPowerSteps fp X k i a|
              ≤ |p23RoundedPowerSteps fp X k i a -
                    p23PowerSteps X k i a| +
                  |p23PowerSteps X k i a| := by
                convert abs_add_le
                  (p23RoundedPowerSteps fp X k i a - p23PowerSteps X k i a)
                  (p23PowerSteps X k i a) using 1 <;> ring
          _ ≤ p23Gamma fp.u (k * n) *
                  p23PowerSteps (p23AbsMatrix X) k i a +
                p23PowerSteps (p23AbsMatrix X) k i a :=
              add_le_add (ih hkvalid i a) (p23PowerSteps_abs_le n k X i a)
          _ = (1 + p23Gamma fp.u (k * n)) *
                p23PowerSteps (p23AbsMatrix X) k i a := by ring
      let M : ℝ := ∑ a : Fin n,
        p23PowerSteps (p23AbsMatrix X) k i a * |X a j|
      have hM : 0 ≤ M := by
        dsimp [M]
        exact Finset.sum_nonneg fun a _ =>
          mul_nonneg (hmajor a) (abs_nonneg _)
      have hround :
          |p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X i j -
              p23MatMul (p23RoundedPowerSteps fp X k) X i j| ≤
            p23Gamma fp.u n *
              (1 + p23Gamma fp.u (k * n)) * M := by
        have hdot := p23RoundedDotProduct_error_bound fp n
          (p23RoundedPowerSteps fp X k i) (fun a => X a j) hnvalid
        have hsum :
            (∑ a : Fin n,
                |p23RoundedPowerSteps fp X k i a| * |X a j|) ≤
              (1 + p23Gamma fp.u (k * n)) * M := by
          calc
            (∑ a : Fin n,
                |p23RoundedPowerSteps fp X k i a| * |X a j|)
                ≤ ∑ a : Fin n,
                    ((1 + p23Gamma fp.u (k * n)) *
                      p23PowerSteps (p23AbsMatrix X) k i a) * |X a j| := by
                  apply Finset.sum_le_sum
                  intro a _
                  exact mul_le_mul_of_nonneg_right
                    (hrounded_major a) (abs_nonneg _)
            _ = (1 + p23Gamma fp.u (k * n)) * M := by
                  dsimp [M]
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro a _
                  ring
        calc
          |p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X i j -
              p23MatMul (p23RoundedPowerSteps fp X k) X i j|
              ≤ p23Gamma fp.u n *
                  ∑ a : Fin n,
                    |p23RoundedPowerSteps fp X k i a| * |X a j| := by
                simpa [p23RoundedMatMul, p23MatMul] using hdot
          _ ≤ p23Gamma fp.u n *
                ((1 + p23Gamma fp.u (k * n)) * M) :=
              mul_le_mul_of_nonneg_left hsum hgn
          _ = p23Gamma fp.u n *
                (1 + p23Gamma fp.u (k * n)) * M := by ring
      have hprop :
          |p23MatMul (p23RoundedPowerSteps fp X k) X i j -
              p23MatMul (p23PowerSteps X k) X i j| ≤
            p23Gamma fp.u (k * n) * M := by
        change
          |∑ a : Fin n, p23RoundedPowerSteps fp X k i a * X a j -
              ∑ a : Fin n, p23PowerSteps X k i a * X a j| ≤ _
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ a : Fin n,
              (p23RoundedPowerSteps fp X k i a * X a j -
                p23PowerSteps X k i a * X a j)|
              ≤ ∑ a : Fin n,
                  |p23RoundedPowerSteps fp X k i a * X a j -
                    p23PowerSteps X k i a * X a j| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ a : Fin n,
                |p23RoundedPowerSteps fp X k i a -
                  p23PowerSteps X k i a| * |X a j| := by
              apply Finset.sum_congr rfl
              intro a _
              rw [← sub_mul, abs_mul]
          _ ≤ ∑ a : Fin n,
                (p23Gamma fp.u (k * n) *
                  p23PowerSteps (p23AbsMatrix X) k i a) * |X a j| := by
              apply Finset.sum_le_sum
              intro a _
              exact mul_le_mul_of_nonneg_right (ih hkvalid i a) (abs_nonneg _)
          _ = p23Gamma fp.u (k * n) * M := by
              dsimp [M]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              ring
      have hcoef :
          p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
              p23Gamma fp.u (k * n) ≤
            p23Gamma fp.u ((k + 1) * n) := by
        have hs := p23Gamma_sum_le fp (k * n) n (by
          simpa [Nat.succ_mul] using hvalid)
        calc
          p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
                p23Gamma fp.u (k * n)
              = p23Gamma fp.u (k * n) + p23Gamma fp.u n +
                  p23Gamma fp.u (k * n) * p23Gamma fp.u n := by ring
          _ ≤ p23Gamma fp.u (k * n + n) := hs
          _ = p23Gamma fp.u ((k + 1) * n) := by rw [Nat.succ_mul]
      simp only [p23RoundedPowerSteps, p23PowerSteps]
      calc
        |p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X i j -
            p23MatMul (p23PowerSteps X k) X i j|
            ≤ |p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X i j -
                  p23MatMul (p23RoundedPowerSteps fp X k) X i j| +
                |p23MatMul (p23RoundedPowerSteps fp X k) X i j -
                  p23MatMul (p23PowerSteps X k) X i j| := by
              rw [show
                p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X i j -
                    p23MatMul (p23PowerSteps X k) X i j =
                  (p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X i j -
                    p23MatMul (p23RoundedPowerSteps fp X k) X i j) +
                  (p23MatMul (p23RoundedPowerSteps fp X k) X i j -
                    p23MatMul (p23PowerSteps X k) X i j) by ring]
              exact abs_add_le _ _
        _ ≤ p23Gamma fp.u n *
                (1 + p23Gamma fp.u (k * n)) * M +
              p23Gamma fp.u (k * n) * M := add_le_add hround hprop
        _ = (p23Gamma fp.u n * (1 + p23Gamma fp.u (k * n)) +
                p23Gamma fp.u (k * n)) * M := by ring
        _ ≤ p23Gamma fp.u ((k + 1) * n) * M :=
              mul_le_mul_of_nonneg_right hcoef hM
        _ = p23Gamma fp.u ((k + 1) * n) *
              p23MatMul (p23PowerSteps (p23AbsMatrix X) k)
                (p23AbsMatrix X) i j := by
              rfl

end HighamBench
