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
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg

private lemma p26ForwardSubSteps_eq_library (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p26ForwardSubSteps fp n L b k hk x =
        NumStability.fl_forwardSub_steps (p26AsFPModel fp) n L b k hk x := by
  intro k
  induction k with
  | zero =>
      intro hk x
      rfl
  | succ k ih =>
      intro hk x
      simp only [p26ForwardSubSteps, NumStability.fl_forwardSub_steps,
        p26AsFPModel]
      apply ih

private lemma p26ForwardSub_eq_library (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ) :
    p26ForwardSub fp n L b =
      NumStability.fl_forwardSub (p26AsFPModel fp) n L b := by
  apply p26ForwardSubSteps_eq_library

private lemma p26VecNormSq_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ p26VecNormSq x := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private lemma p26VecNorm_sq {n : ℕ} (x : Fin n → ℝ) :
    p26VecNorm x ^ 2 = p26VecNormSq x := by
  exact Real.sq_sqrt (p26VecNormSq_nonneg x)

private lemma p26FrobNormSq_nonneg {m n : ℕ} (A : P26Matrix m n) :
    0 ≤ p26FrobNormSq A := by
  exact Finset.sum_nonneg (fun _ _ => p26VecNormSq_nonneg _)

private lemma p26FrobNorm_sq {m n : ℕ} (A : P26Matrix m n) :
    p26FrobNorm A ^ 2 = p26FrobNormSq A := by
  exact Real.sq_sqrt (p26FrobNormSq_nonneg A)

private lemma p26FrobNorm_le_mul_of_rows {m n : ℕ}
    (A B : P26Matrix m n) (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ i, p26VecNorm (A i) ≤ c * p26VecNorm (B i)) :
    p26FrobNorm A ≤ c * p26FrobNorm B := by
  have hrowSq : ∀ i, p26VecNormSq (A i) ≤ c ^ 2 * p26VecNormSq (B i) := by
    intro i
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hc (Real.sqrt_nonneg _))).mpr (hrow i)
    rw [Real.sq_sqrt (p26VecNormSq_nonneg (A i)), mul_pow,
      Real.sq_sqrt (p26VecNormSq_nonneg (B i))] at hs
    exact hs
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg hc (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (p26FrobNormSq_nonneg A), mul_pow,
    Real.sq_sqrt (p26FrobNormSq_nonneg B)]
  change (∑ i : Fin m, p26VecNormSq (A i)) ≤
    c ^ 2 * ∑ i : Fin m, p26VecNormSq (B i)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hrowSq i)

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
  let fp' := p26AsFPModel fp
  have hvalid' : NumStability.gammaValid fp' n := by
    simpa [fp', p26AsFPModel, P26GammaValid, NumStability.gammaValid] using hvalid
  have hdiag' : ∀ i, p26Transpose R i i ≠ 0 := by
    intro i
    simpa [p26Transpose] using hdiag i
  have hlower' : ∀ i j : Fin n, i.val < j.val → p26Transpose R i j = 0 := by
    intro i j hij
    simpa [p26Transpose] using hupper j i hij
  have hrow : ∀ i : Fin m,
      p26VecNorm (p26Residual (p26RoundedQ fp X R) R X i) ≤
        ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm) *
          p26VecNorm (p26RoundedQ fp X R i) := by
    intro i
    obtain ⟨deltaL, hdeltaL, heq⟩ :=
      NumStability.forwardSub_backward_error fp' n (p26Transpose R) (X i)
        hdiag' hlower' hvalid'
    apply hperturb i deltaL
    · intro k j
      simpa [fp', p26AsFPModel, p26Gamma, NumStability.gamma,
        p26Transpose] using hdeltaL k j
    · intro k
      change ∑ j, (p26Transpose R k j + deltaL k j) *
        p26ForwardSub fp n (p26Transpose R) (X i) j = X i k
      rw [p26ForwardSub_eq_library fp n (p26Transpose R) (X i)]
      exact heq k
  let c : ℝ :=
    (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hc : 0 ≤ c := by
    dsimp [c]
    have hhead : 0 ≤ (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n := by
      positivity
    exact mul_nonneg (mul_nonneg hhead fp.u_nonneg) hxNorm
  have hres :
      p26FrobNorm (p26Residual (p26RoundedQ fp X R) R X) ≤
        c * p26FrobNorm (p26RoundedQ fp X R) := by
    apply p26FrobNorm_le_mul_of_rows _ _ c hc
    simpa [c] using hrow
  calc
    p26FrobNorm (p26Residual (p26RoundedQ fp X R) R X)
        ≤ c * p26FrobNorm (p26RoundedQ fp X R) := hres
    _ ≤ c * Real.sqrt (3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hQFrob hc
    _ ≤ 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hsqrt3 : (11 : ℝ) / 10 * Real.sqrt 3 ≤ 2 := by
        have hs3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
        have hs30 := Real.sqrt_nonneg (3 : ℝ)
        nlinarith
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      have hrest : 0 ≤ (n : ℝ) ^ 2 * fp.u * xNorm :=
        mul_nonneg (mul_nonneg (sq_nonneg _) fp.u_nonneg) hxNorm
      have hsqrtn := Real.sq_sqrt hn0
      dsimp [c]
      calc
        (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm *
              (Real.sqrt 3 * Real.sqrt n) =
            ((11 : ℝ) / 10 * Real.sqrt 3) *
              ((n : ℝ) * Real.sqrt n ^ 2 * fp.u * xNorm) := by ring
        _ = ((11 : ℝ) / 10 * Real.sqrt 3) *
              ((n : ℝ) ^ 2 * fp.u * xNorm) := by rw [hsqrtn]; ring
        _ ≤ 2 * ((n : ℝ) ^ 2 * fp.u * xNorm) :=
          mul_le_mul_of_nonneg_right hsqrt3 hrest
        _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by ring

end HighamBench
