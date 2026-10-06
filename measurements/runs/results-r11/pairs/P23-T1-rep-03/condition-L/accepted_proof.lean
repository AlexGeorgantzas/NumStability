import HighamBench.P23Definitions
import NumStability.Algorithms.MatMul

namespace HighamBench

open scoped BigOperators

/-- Regard the operations used in P23 as the corresponding part of the
full floating-point model from NumStability.  The unused operations are taken
to be exact. -/
noncomputable def p23FPModelToNumStability (fp : P23FPModel) :
    NumStability.FPModel where
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
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg
  model_mul := fp.model_mul
  model_div := by
    intro x y _hy
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg
  model_sqrt := by
    intro x _hx
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg

/-- Exact powers are componentwise dominated by powers of the componentwise
absolute-value matrix. -/
lemma p23PowerSteps_abs_le {n : ℕ} (X : P23Matrix n) :
    ∀ k i j,
      |p23PowerSteps X k i j| ≤
        p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      rfl
  | succ k ih =>
      intro i j
      rw [p23PowerSteps, p23PowerSteps]
      unfold p23MatMul
      calc
        |∑ l : Fin n, p23PowerSteps X k i l * X l j|
            ≤ ∑ l : Fin n, |p23PowerSteps X k i l * X l j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ l : Fin n, |p23PowerSteps X k i l| * |X l j| := by
              apply Finset.sum_congr rfl
              intro l _
              exact abs_mul _ _
        _ ≤ ∑ l : Fin n,
              p23PowerSteps (p23AbsMatrix X) k i l * |X l j| := by
              apply Finset.sum_le_sum
              intro l _
              exact mul_le_mul_of_nonneg_right (ih i l) (abs_nonneg _)
        _ = ∑ l : Fin n,
              p23PowerSteps (p23AbsMatrix X) k i l *
                p23AbsMatrix X l j := rfl

/-- Powers of a componentwise absolute-value matrix are componentwise
nonnegative. -/
lemma p23PowerSteps_abs_nonneg {n : ℕ} (X : P23Matrix n) :
    ∀ k i j, 0 ≤ p23PowerSteps (p23AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact abs_nonneg _
  | succ k ih =>
      intro i j
      rw [p23PowerSteps]
      unfold p23MatMul
      exact Finset.sum_nonneg (fun l _ =>
        mul_nonneg (ih i l) (abs_nonneg _))

/-- P23-T1: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p23_t1_lemma_2_2
    (fp : P23FPModel) (n k : ℕ) (X : P23Matrix n)
    (hvalid : P23GammaValid fp.u (k * n)) :
    ∀ i j,
      |p23RoundedPowerSteps fp X k i j - p23PowerSteps X k i j| ≤
        p23Gamma fp.u (k * n) * p23PowerSteps (p23AbsMatrix X) k i j := by
  -- PROOF_START P23-T1-H001
  let nfp : NumStability.FPModel := p23FPModelToNumStability fp
  revert hvalid
  induction k with
  | zero =>
      intro _hvalid i j
      simp [p23RoundedPowerSteps, p23PowerSteps, p23Gamma]
  | succ k ih =>
      intro hvalid i j
      have hvalidNS : NumStability.gammaValid nfp ((k + 1) * n) := by
        simpa [NumStability.gammaValid, P23GammaValid, nfp,
          p23FPModelToNumStability] using hvalid
      have hn_le : n ≤ (k + 1) * n := by
        simpa using
          (Nat.mul_le_mul_right n (Nat.succ_le_succ (Nat.zero_le k)))
      have hk_le : k * n ≤ (k + 1) * n := by
        exact Nat.mul_le_mul_right n (Nat.le_succ k)
      have hnvalid : NumStability.gammaValid nfp n :=
        NumStability.gammaValid_mono nfp hn_le hvalidNS
      have hkvalidNS : NumStability.gammaValid nfp (k * n) :=
        NumStability.gammaValid_mono nfp hk_le hvalidNS
      have hkvalid : P23GammaValid fp.u (k * n) := by
        simpa [NumStability.gammaValid, P23GammaValid, nfp,
          p23FPModelToNumStability] using hkvalidNS
      have ih' := ih hkvalid
      let R : P23Matrix n := p23RoundedPowerSteps fp X k
      let P : P23Matrix n := p23PowerSteps X k
      let Q : P23Matrix n := p23PowerSteps (p23AbsMatrix X) k
      let gn : ℝ := p23Gamma fp.u n
      let gk : ℝ := p23Gamma fp.u (k * n)
      have hgn : 0 ≤ gn := by
        simpa [gn, p23Gamma, NumStability.gamma, nfp,
          p23FPModelToNumStability] using
            (NumStability.gamma_nonneg nfp hnvalid)
      have hgk : 0 ≤ gk := by
        simpa [gk, p23Gamma, NumStability.gamma, nfp,
          p23FPModelToNumStability] using
            (NumStability.gamma_nonneg nfp hkvalidNS)
      have hQ : ∀ a b, 0 ≤ Q a b := by
        intro a b
        exact p23PowerSteps_abs_nonneg X k a b
      have hP : ∀ a b, |P a b| ≤ Q a b := by
        intro a b
        exact p23PowerSteps_abs_le X k a b
      have hR : ∀ a b, |R a b| ≤ (1 + gk) * Q a b := by
        intro a b
        calc
          |R a b| ≤ |R a b - P a b| + |P a b| := by
            have h := abs_add_le (R a b - P a b) (P a b)
            convert h using 1 <;> ring
          _ ≤ gk * Q a b + Q a b :=
            add_le_add (by simpa [R, P, Q, gk] using ih' a b) (hP a b)
          _ = (1 + gk) * Q a b := by ring
      have hlocal :
          |p23RoundedMatMul fp R X i j - p23MatMul R X i j| ≤
            gn * ∑ l : Fin n, |R i l| * |X l j| := by
        have h := NumStability.matMul_error_bound nfp n n n R X hnvalid i j
        simpa [p23RoundedMatMul, p23RoundedDotProduct, p23MatMul,
          NumStability.fl_matMul, NumStability.fl_matVec,
          NumStability.fl_dotProduct, gn, p23Gamma, NumStability.gamma,
          nfp, p23FPModelToNumStability] using h
      have hroundMajorant :
          gn * (∑ l : Fin n, |R i l| * |X l j|) ≤
            gn * ((1 + gk) * p23MatMul Q (p23AbsMatrix X) i j) := by
        apply mul_le_mul_of_nonneg_left _ hgn
        calc
          ∑ l : Fin n, |R i l| * |X l j|
              ≤ ∑ l : Fin n, ((1 + gk) * Q i l) * |X l j| := by
                apply Finset.sum_le_sum
                intro l _
                exact mul_le_mul_of_nonneg_right (hR i l) (abs_nonneg _)
          _ = (1 + gk) * p23MatMul Q (p23AbsMatrix X) i j := by
                unfold p23MatMul p23AbsMatrix
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro l _
                ring
      have hprop :
          |p23MatMul R X i j - p23MatMul P X i j| ≤
            gk * p23MatMul Q (p23AbsMatrix X) i j := by
        unfold p23MatMul
        calc
          |∑ l : Fin n, R i l * X l j - ∑ l : Fin n, P i l * X l j|
              = |∑ l : Fin n, (R i l - P i l) * X l j| := by
                  congr 1
                  rw [← Finset.sum_sub_distrib]
                  apply Finset.sum_congr rfl
                  intro l _
                  ring
          _ ≤ ∑ l : Fin n, |(R i l - P i l) * X l j| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ l : Fin n, |R i l - P i l| * |X l j| := by
                apply Finset.sum_congr rfl
                intro l _
                exact abs_mul _ _
          _ ≤ ∑ l : Fin n, (gk * Q i l) * |X l j| := by
                apply Finset.sum_le_sum
                intro l _
                exact mul_le_mul_of_nonneg_right
                  (by simpa [R, P, Q, gk] using ih' i l) (abs_nonneg _)
          _ = gk * (∑ l : Fin n, Q i l * |X l j|) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro l _
                ring
          _ = gk * (∑ l : Fin n, Q i l * p23AbsMatrix X l j) := rfl
      have hgamma :
          gn + gk + gn * gk ≤ p23Gamma fp.u ((k + 1) * n) := by
        have hsum := NumStability.gamma_sum_le nfp (k * n) n (by
          simpa [Nat.succ_mul] using hvalidNS)
        calc
          gn + gk + gn * gk = gk + gn + gk * gn := by ring
          _ ≤ p23Gamma fp.u ((k + 1) * n) := by
            simpa [gn, gk, p23Gamma, NumStability.gamma, nfp,
              p23FPModelToNumStability, Nat.succ_mul] using hsum
      have hQnext :
          0 ≤ p23MatMul Q (p23AbsMatrix X) i j := by
        unfold p23MatMul
        exact Finset.sum_nonneg (fun l _ =>
          mul_nonneg (hQ i l) (abs_nonneg _))
      rw [p23RoundedPowerSteps, p23PowerSteps]
      change
        |p23RoundedMatMul fp R X i j - p23MatMul P X i j| ≤
          p23Gamma fp.u ((k + 1) * n) *
            p23MatMul Q (p23AbsMatrix X) i j
      calc
        |p23RoundedMatMul fp R X i j - p23MatMul P X i j|
            ≤ |p23RoundedMatMul fp R X i j - p23MatMul R X i j| +
                |p23MatMul R X i j - p23MatMul P X i j| := by
                  have h := abs_add_le
                    (p23RoundedMatMul fp R X i j - p23MatMul R X i j)
                    (p23MatMul R X i j - p23MatMul P X i j)
                  convert h using 1 <;> ring
        _ ≤ gn * ((1 + gk) * p23MatMul Q (p23AbsMatrix X) i j) +
              gk * p23MatMul Q (p23AbsMatrix X) i j :=
                add_le_add (le_trans hlocal hroundMajorant) hprop
        _ = (gn + gk + gn * gk) *
              p23MatMul Q (p23AbsMatrix X) i j := by ring
        _ ≤ p23Gamma fp.u ((k + 1) * n) *
              p23MatMul Q (p23AbsMatrix X) i j :=
                mul_le_mul_of_nonneg_right hgamma hQnext

end HighamBench
