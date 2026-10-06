import HighamBench.P26Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace HighamBench

open scoped BigOperators

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
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

lemma p26ForwardSubSteps_eq_fl_forwardSub_steps
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n)
    (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) :
    p26ForwardSubSteps fp n L b k hk x =
      NumStability.fl_forwardSub_steps (p26AsFPModel fp) n L b k hk x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      unfold p26ForwardSubSteps NumStability.fl_forwardSub_steps
      simp only [p26AsFPModel]
      apply ih

lemma p26ForwardSub_eq_fl_forwardSub
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n)
    (b : Fin n → ℝ) :
    p26ForwardSub fp n L b =
      NumStability.fl_forwardSub (p26AsFPModel fp) n L b := by
  unfold p26ForwardSub NumStability.fl_forwardSub
  exact p26ForwardSubSteps_eq_fl_forwardSub_steps fp n L b n (le_refl n) _

lemma p26VecNorm_sq {n : ℕ} (v : Fin n → ℝ) :
    p26VecNorm v ^ 2 = p26VecNormSq v := by
  rw [p26VecNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma p26FrobNorm_sq {m n : ℕ} (A : P26Matrix m n) :
    p26FrobNorm A ^ 2 = p26FrobNormSq A := by
  rw [p26FrobNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

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
  let Q := p26RoundedQ fp X R
  let c : ℝ := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hc : 0 ≤ c := by
    dsimp [c]
    have hcoef : (0 : ℝ) ≤ 11 / 10 := by norm_num
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hcoef (by positivity))
        (Real.sqrt_nonneg _)) fp.u_nonneg) hxNorm
  have hrow : ∀ i : Fin m,
      p26VecNorm (p26Residual Q R X i) ≤ c * p26VecNorm (Q i) := by
    intro i
    let nfp := p26AsFPModel fp
    obtain ⟨deltaL, hdeltaL, hsystem⟩ :=
      NumStability.forwardSub_backward_error nfp n (p26Transpose R) (X i)
        (by simpa [p26Transpose] using hdiag)
        (by
          intro k j hkj
          exact hupper j k hkj)
        (by simpa [NumStability.gammaValid, P26GammaValid, nfp, p26AsFPModel]
          using hvalid)
    apply hperturb i deltaL
    · intro k j
      simpa [p26Gamma, NumStability.gamma, p26Transpose, nfp, p26AsFPModel]
        using hdeltaL k j
    · intro k
      simpa [Q, p26RoundedQ, p26ForwardSub_eq_fl_forwardSub,
        nfp] using hsystem k
  have hsum :
      p26FrobNormSq (p26Residual Q R X) ≤ c ^ 2 * p26FrobNormSq Q := by
    unfold p26FrobNormSq
    calc
      ∑ i : Fin m, p26VecNormSq (p26Residual Q R X i) ≤
          ∑ i : Fin m, c ^ 2 * p26VecNormSq (Q i) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [← p26VecNorm_sq, ← p26VecNorm_sq]
            have hr0 : 0 ≤ p26VecNorm (p26Residual Q R X i) :=
              Real.sqrt_nonneg _
            have hq0 : 0 ≤ p26VecNorm (Q i) := Real.sqrt_nonneg _
            nlinarith [hrow i, sq_nonneg
              (p26VecNorm (p26Residual Q R X i) - c * p26VecNorm (Q i))]
      _ = c ^ 2 * ∑ i : Fin m, p26VecNormSq (Q i) := by
            rw [Finset.mul_sum]
  have hFrob :
      p26FrobNorm (p26Residual Q R X) ≤ c * p26FrobNorm Q := by
    have hr0 : 0 ≤ p26FrobNorm (p26Residual Q R X) := Real.sqrt_nonneg _
    have hq0 : 0 ≤ p26FrobNorm Q := Real.sqrt_nonneg _
    rw [← p26FrobNorm_sq, ← p26FrobNorm_sq] at hsum
    by_contra hnot
    have hgt : c * p26FrobNorm Q < p26FrobNorm (p26Residual Q R X) :=
      lt_of_not_ge hnot
    have hp : 0 <
        (p26FrobNorm (p26Residual Q R X) - c * p26FrobNorm Q) *
        (p26FrobNorm (p26Residual Q R X) + c * p26FrobNorm Q) := by
      apply mul_pos
      · exact sub_pos.mpr hgt
      · nlinarith [mul_nonneg hc hq0]
    nlinarith
  have hQ : p26FrobNorm Q ≤ Real.sqrt (3 * (n : ℝ)) := by
    simpa [Q] using hQFrob
  have hpre :
      p26FrobNorm (p26Residual Q R X) ≤ c * Real.sqrt (3 * (n : ℝ)) :=
    hFrob.trans (mul_le_mul_of_nonneg_left hQ hc)
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hsqrtn0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrt3n0 : 0 ≤ Real.sqrt (3 * (n : ℝ)) := Real.sqrt_nonneg _
  have hsqrtn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hn0
  have hsqrt3n : Real.sqrt (3 * (n : ℝ)) ^ 2 = 3 * (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hconstant :
      (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n *
          Real.sqrt (3 * (n : ℝ)) ≤ 2 * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg
      (2 * (n : ℝ) - (11 : ℝ) / 10 * Real.sqrt n *
        Real.sqrt (3 * (n : ℝ)))]
  have hscaled := mul_le_mul_of_nonneg_right hconstant
    (mul_nonneg fp.u_nonneg hxNorm)
  change p26FrobNorm (p26Residual Q R X) ≤ _
  calc
    p26FrobNorm (p26Residual Q R X) ≤
        c * Real.sqrt (3 * (n : ℝ)) := hpre
    _ ≤ 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
      dsimp [c]
      nlinarith

end HighamBench
