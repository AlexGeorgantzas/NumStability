import HighamBench.P26Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace HighamBench

theorem p26_t1_lemma_3_2
    (fp : P26FPModel) (m n : ℕ)
    (X : P26Matrix m n) (R : P26Matrix n n) (xNorm : ℝ)
    (hdiag : ∀ i, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hvalid : P26GammaValid fp.u n)
    (hxNorm : 0 ≤ xNorm)
    (hperturb : P26RowPerturbationsControlled fp X R xNorm)
    (hQFrob : p26FrobNorm (p26RoundedQ fp X R) ≤
      Real.sqrt (3 * (n : ℝ))) :
    p26FrobNorm
        (p26Residual (p26RoundedQ fp X R) R X) ≤
      2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
  -- PROOF_START P26-T1-H001
  let nfp : NumStability.FPModel :=
    { u := fp.u
      u_nonneg := fp.u_nonneg
      fl_add := fp.fl_add
      fl_sub := fp.fl_sub
      fl_mul := fp.fl_mul
      fl_div := fp.fl_div
      fl_sqrt := Real.sqrt
      fl_add_zero := fp.fl_add_zero
      model_add := fp.model_add
      model_sub := fp.model_sub
      model_mul := fp.model_mul
      model_div := fp.model_div
      model_sqrt := by
        intro y hy
        refine ⟨0, ?_, ?_⟩
        · simpa using fp.u_nonneg
        · ring }
  have hsteps (L : P26Matrix n n) (b : Fin n → ℝ) :
      ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
        p26ForwardSubSteps fp n L b k hk x =
          NumStability.fl_forwardSub_steps nfp n L b k hk x := by
    intro k
    induction k with
    | zero =>
        intro hk x
        rfl
    | succ k ih =>
        intro hk x
        rw [p26ForwardSubSteps, NumStability.fl_forwardSub_steps]
        dsimp only [nfp]
        apply ih
  have hrow : ∀ i : Fin m,
      p26VecNorm (p26Residual (p26RoundedQ fp X R) R X i) ≤
        ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm) *
          p26VecNorm (p26RoundedQ fp X R i) := by
    intro i
    obtain ⟨deltaL, hdeltaL, heq⟩ :=
      NumStability.forwardSub_backward_error nfp n (p26Transpose R) (X i)
        (by simpa [p26Transpose] using hdiag)
        (by
          intro k j hkj
          exact hupper j k hkj)
        (by simpa [NumStability.gammaValid, P26GammaValid, nfp] using hvalid)
    apply hperturb i deltaL
    · intro k j
      simpa [p26Gamma, NumStability.gamma, nfp] using hdeltaL k j
    · intro k
      simpa only [p26RoundedQ, p26ForwardSub, NumStability.fl_forwardSub,
        hsteps] using heq k

  let c : ℝ := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) (Real.sqrt_nonneg _))
        fp.u_nonneg)
      hxNorm
  have hvec_nonneg (i : Fin m) :
      0 ≤ p26VecNorm (p26Residual (p26RoundedQ fp X R) R X i) := by
    exact Real.sqrt_nonneg _
  have hqvec_nonneg (i : Fin m) :
      0 ≤ p26VecNorm (p26RoundedQ fp X R i) := by
    exact Real.sqrt_nonneg _
  have hsquares :
      p26FrobNormSq (p26Residual (p26RoundedQ fp X R) R X) ≤
        c ^ 2 * p26FrobNormSq (p26RoundedQ fp X R) := by
    unfold p26FrobNormSq
    calc
      ∑ i : Fin m, p26VecNormSq
          (p26Residual (p26RoundedQ fp X R) R X i) =
          ∑ i : Fin m,
            p26VecNorm (p26Residual (p26RoundedQ fp X R) R X i) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [p26VecNorm, Real.sq_sqrt]
              unfold p26VecNormSq
              positivity
      _ ≤ ∑ i : Fin m, (c * p26VecNorm (p26RoundedQ fp X R i)) ^ 2 := by
              apply Finset.sum_le_sum
              intro i hi
              apply (sq_le_sq₀ (hvec_nonneg i)
                (mul_nonneg hc (hqvec_nonneg i))).2
              simpa only [c] using hrow i
      _ = c ^ 2 * ∑ i : Fin m,
            p26VecNormSq (p26RoundedQ fp X R i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [p26VecNorm]
              calc
                (c * Real.sqrt (p26VecNormSq (p26RoundedQ fp X R i))) ^ 2 =
                    c ^ 2 * Real.sqrt (p26VecNormSq (p26RoundedQ fp X R i)) ^ 2 := by
                      ring
                _ = c ^ 2 * p26VecNormSq (p26RoundedQ fp X R i) := by
                  rw [Real.sq_sqrt]
                  unfold p26VecNormSq
                  positivity
  have hfrob :
      p26FrobNorm (p26Residual (p26RoundedQ fp X R) R X) ≤
        c * p26FrobNorm (p26RoundedQ fp X R) := by
    unfold p26FrobNorm
    rw [← Real.sqrt_sq hc]
    rw [← Real.sqrt_mul (sq_nonneg c)]
    exact Real.sqrt_le_sqrt hsquares
  have hsqrt_product : Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ)) =
      (n : ℝ) * Real.sqrt 3 := by
    rw [show (3 : ℝ) * n = n * 3 by ring, Real.sqrt_mul (Nat.cast_nonneg n)]
    rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  have hsqrt3 : (11 : ℝ) / 10 * Real.sqrt 3 ≤ 2 := by
    have hs3 : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
    have hs3sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by norm_num
    nlinarith
  calc
    p26FrobNorm (p26Residual (p26RoundedQ fp X R) R X) ≤
        c * p26FrobNorm (p26RoundedQ fp X R) := hfrob
    _ ≤ c * Real.sqrt (3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hQFrob hc
    _ = ((11 : ℝ) / 10 * Real.sqrt 3) *
        ((n : ℝ) ^ 2 * fp.u * xNorm) := by
      dsimp [c]
      calc
        (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm *
            Real.sqrt (3 * (n : ℝ)) =
            ((11 : ℝ) / 10 * (n : ℝ) * fp.u * xNorm) *
              (Real.sqrt n * Real.sqrt (3 * (n : ℝ))) := by ring
        _ = ((11 : ℝ) / 10 * Real.sqrt 3) *
            ((n : ℝ) ^ 2 * fp.u * xNorm) := by
          rw [hsqrt_product]
          ring
    _ ≤ 2 * ((n : ℝ) ^ 2 * fp.u * xNorm) := by
      apply mul_le_mul_of_nonneg_right hsqrt3
      exact mul_nonneg (mul_nonneg (sq_nonneg _) fp.u_nonneg) hxNorm
    _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by ring

end HighamBench
