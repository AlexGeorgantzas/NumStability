import HighamBench.P26Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace HighamBench

noncomputable def p26AsFPModel (fp : P26FPModel) : NumStability.FPModel where
  u := fp.u
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
    intro x hx
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

lemma p26ForwardSubSteps_asFPModel (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) :
    p26ForwardSubSteps fp n L b k hk x =
      NumStability.fl_forwardSub_steps (p26AsFPModel fp) n L b k hk x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      simp only [p26ForwardSubSteps, NumStability.fl_forwardSub_steps]
      apply ih

lemma p26ForwardSub_asFPModel (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ) :
    p26ForwardSub fp n L b =
      NumStability.fl_forwardSub (p26AsFPModel fp) n L b := by
  exact p26ForwardSubSteps_asFPModel fp n L b n (le_refl n) (fun _ => 0)

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
  have hrow : ∀ i : Fin m,
      p26VecNorm (p26Residual (p26RoundedQ fp X R) R X i) ≤
        ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm) *
          p26VecNorm (p26RoundedQ fp X R i) := by
    intro i
    obtain ⟨deltaL, hdeltaL, heq⟩ :=
      NumStability.forwardSub_backward_error (p26AsFPModel fp) n
        (p26Transpose R) (X i)
        (by simpa [p26Transpose] using hdiag)
        (by
          intro k j hkj
          exact hupper j k hkj)
        (by exact hvalid)
    apply hperturb i deltaL
    · simpa [p26Gamma, NumStability.gamma, p26AsFPModel] using hdeltaL
    · simpa [p26RoundedQ, p26ForwardSub_asFPModel] using heq
  let c : ℝ :=
    (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (by positivity))
          (Real.sqrt_nonneg _))
        fp.u_nonneg)
      hxNorm
  have hvec_nonneg : ∀ (A : P26Matrix m n) (i : Fin m),
      0 ≤ p26VecNormSq (A i) := by
    intro A i
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq_row : ∀ i : Fin m,
      p26VecNormSq (p26Residual (p26RoundedQ fp X R) R X i) ≤
        c ^ 2 * p26VecNormSq (p26RoundedQ fp X R i) := by
    intro i
    have hi := hrow i
    change p26VecNorm
        (p26Residual (p26RoundedQ fp X R) R X i) ≤
      c * p26VecNorm (p26RoundedQ fp X R i) at hi
    have hleft := Real.sq_sqrt
      (hvec_nonneg (p26Residual (p26RoundedQ fp X R) R X) i)
    have hright := Real.sq_sqrt
      (hvec_nonneg (p26RoundedQ fp X R) i)
    have hsqrt_left : 0 ≤ Real.sqrt
        (p26VecNormSq
          (p26Residual (p26RoundedQ fp X R) R X i)) :=
      Real.sqrt_nonneg _
    have hsqrt_right : 0 ≤ Real.sqrt
        (p26VecNormSq (p26RoundedQ fp X R i)) :=
      Real.sqrt_nonneg _
    unfold p26VecNorm at hi
    nlinarith
  have hsq :
      p26FrobNormSq (p26Residual (p26RoundedQ fp X R) R X) ≤
        c ^ 2 * p26FrobNormSq (p26RoundedQ fp X R) := by
    unfold p26FrobNormSq
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hsq_row i)
  have hQsq_nonneg : 0 ≤ p26FrobNormSq (p26RoundedQ fp X R) := by
    unfold p26FrobNormSq
    exact Finset.sum_nonneg (fun i _ => hvec_nonneg _ i)
  have hfrob_c :
      p26FrobNorm (p26Residual (p26RoundedQ fp X R) R X) ≤
        c * p26FrobNorm (p26RoundedQ fp X R) := by
    unfold p26FrobNorm
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · calc
        p26FrobNormSq (p26Residual (p26RoundedQ fp X R) R X) ≤
            c ^ 2 * p26FrobNormSq (p26RoundedQ fp X R) := hsq
        _ = (c * Real.sqrt
              (p26FrobNormSq (p26RoundedQ fp X R))) ^ 2 := by
            conv_lhs =>
              rw [← Real.sq_sqrt hQsq_nonneg]
            ring
  have hfrob_sqrt :
      p26FrobNorm (p26Residual (p26RoundedQ fp X R) R X) ≤
        c * Real.sqrt (3 * (n : ℝ)) :=
    le_trans hfrob_c (mul_le_mul_of_nonneg_left hQFrob hc)
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hsqrt_three : Real.sqrt (3 : ℝ) ≤ 20 / 11 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num
  have hsqrt_product :
      Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ)) =
        Real.sqrt 3 * (n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      Real.sqrt (n : ℝ) * (Real.sqrt 3 * Real.sqrt (n : ℝ)) =
          Real.sqrt 3 *
            (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
      _ = Real.sqrt 3 * (n : ℝ) := by
        rw [Real.mul_self_sqrt hn_nonneg]
  have hconstant : (11 : ℝ) / 10 * Real.sqrt 3 ≤ 2 := by
    nlinarith
  have hscale_nonneg :
      0 ≤ (n : ℝ) ^ 2 * fp.u * xNorm := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) fp.u_nonneg) hxNorm
  apply le_trans hfrob_sqrt
  dsimp [c]
  have hmul := mul_le_mul_of_nonneg_right hconstant hscale_nonneg
  calc
    (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt (n : ℝ) * fp.u * xNorm *
          Real.sqrt (3 * (n : ℝ)) =
        (11 : ℝ) / 10 * (n : ℝ) *
          (Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ))) *
            fp.u * xNorm := by ring
    _ =
        ((11 : ℝ) / 10 * Real.sqrt 3) *
          ((n : ℝ) ^ 2 * fp.u * xNorm) := by
            rw [hsqrt_product]
            ring
    _ ≤ 2 * ((n : ℝ) ^ 2 * fp.u * xNorm) := hmul
    _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by ring

end HighamBench
