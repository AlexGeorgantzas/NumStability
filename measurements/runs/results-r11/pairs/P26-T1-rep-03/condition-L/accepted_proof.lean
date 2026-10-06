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
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

private lemma p26ForwardSubSteps_eq (fp : P26FPModel) (n : ℕ)
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
      simp only [p26ForwardSubSteps, NumStability.fl_forwardSub_steps]
      apply ih

private lemma p26ForwardSub_eq (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ) :
    p26ForwardSub fp n L b =
      NumStability.fl_forwardSub (p26AsFPModel fp) n L b := by
  unfold p26ForwardSub NumStability.fl_forwardSub
  exact p26ForwardSubSteps_eq fp n L b n (le_refl n) (fun _ => 0)

private lemma p26VecNormSq_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ p26VecNormSq x := by
  unfold p26VecNormSq
  positivity

private lemma p26VecNorm_sq {n : ℕ} (x : Fin n → ℝ) :
    p26VecNorm x ^ 2 = p26VecNormSq x := by
  exact Real.sq_sqrt (p26VecNormSq_nonneg x)

private lemma p26FrobNormSq_nonneg {m n : ℕ} (A : P26Matrix m n) :
    0 ≤ p26FrobNormSq A := by
  unfold p26FrobNormSq
  exact Finset.sum_nonneg (fun i _ => p26VecNormSq_nonneg (A i))

private lemma p26FrobNorm_sq {m n : ℕ} (A : P26Matrix m n) :
    p26FrobNorm A ^ 2 = p26FrobNormSq A := by
  exact Real.sq_sqrt (p26FrobNormSq_nonneg A)

private lemma p26FrobNorm_le_mul_of_row_le {m n : ℕ}
    (A B : P26Matrix m n) (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ i, p26VecNorm (A i) ≤ c * p26VecNorm (B i)) :
    p26FrobNorm A ≤ c * p26FrobNorm B := by
  have hrow_sq : ∀ i, p26VecNormSq (A i) ≤ c ^ 2 * p26VecNormSq (B i) := by
    intro i
    rw [← p26VecNorm_sq, ← p26VecNorm_sq]
    have hA : 0 ≤ p26VecNorm (A i) := Real.sqrt_nonneg _
    have hB : 0 ≤ p26VecNorm (B i) := Real.sqrt_nonneg _
    calc
      p26VecNorm (A i) ^ 2 ≤ (c * p26VecNorm (B i)) ^ 2 :=
        (sq_le_sq₀ hA (mul_nonneg hc hB)).mpr (hrow i)
      _ = c ^ 2 * p26VecNorm (B i) ^ 2 := by ring
  have hsquares : p26FrobNormSq A ≤ c ^ 2 * p26FrobNormSq B := by
    unfold p26FrobNormSq
    calc
      ∑ i, p26VecNormSq (A i) ≤
          ∑ i, c ^ 2 * p26VecNormSq (B i) :=
        Finset.sum_le_sum (fun i _ => hrow_sq i)
      _ = c ^ 2 * ∑ i, p26VecNormSq (B i) := by
        exact (Finset.mul_sum _ _ _).symm
  have hsq : p26FrobNorm A ^ 2 ≤ (c * p26FrobNorm B) ^ 2 := by
    rw [p26FrobNorm_sq, mul_pow, p26FrobNorm_sq]
    exact hsquares
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))).mp hsq

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
  let Q : P26Matrix m n := p26RoundedQ fp X R
  let c : ℝ :=
    (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hrow : ∀ i, p26VecNorm (p26Residual Q R X i) ≤
      c * p26VecNorm (Q i) := by
    intro i
    obtain ⟨deltaL, hdeltaL, hsolve⟩ :=
      NumStability.forwardSub_backward_error
        (p26AsFPModel fp) n (p26Transpose R) (X i)
        (by
          intro k
          simpa [p26Transpose] using hdiag k)
        (by
          intro k j hkj
          simpa [p26Transpose] using hupper j k hkj)
        (by
          simpa [NumStability.gammaValid, P26GammaValid, p26AsFPModel]
            using hvalid)
    have hdeltaL' : ∀ k j,
        |deltaL k j| ≤ p26Gamma fp.u n * |R j k| := by
      intro k j
      simpa [NumStability.gamma, p26Gamma, p26AsFPModel, p26Transpose]
        using hdeltaL k j
    have hsolve' : ∀ k, ∑ j : Fin n,
        (p26Transpose R k j + deltaL k j) * Q i j = X i k := by
      intro k
      rw [show Q i = p26ForwardSub fp n (p26Transpose R) (X i) by
        rfl, p26ForwardSub_eq]
      exact hsolve k
    have hi := hperturb i deltaL hdeltaL' hsolve'
    simpa [Q, c] using hi
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (by positivity)) (Real.sqrt_nonneg _))
        fp.u_nonneg)
      hxNorm
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hsqrt_three : Real.sqrt (3 : ℝ) ≤ (20 : ℝ) / 11 := by
    have hs3 : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
    have h20 : 0 ≤ (20 : ℝ) / 11 := by norm_num
    rw [← (sq_le_sq₀ hs3 h20)]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hsqrt_product :
      Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ)) =
        Real.sqrt 3 * (n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      Real.sqrt (n : ℝ) * (Real.sqrt 3 * Real.sqrt (n : ℝ)) =
          Real.sqrt 3 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
      _ = Real.sqrt 3 * (n : ℝ) := by
        rw [Real.mul_self_sqrt hn0]
  have hcoefficient :
      c * Real.sqrt (3 * (n : ℝ)) ≤
        2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
    have hscalar : (11 : ℝ) / 10 * Real.sqrt 3 ≤ 2 := by
      nlinarith
    have hbase : 0 ≤ (n : ℝ) ^ 2 * fp.u * xNorm :=
      mul_nonneg (mul_nonneg (sq_nonneg _) fp.u_nonneg) hxNorm
    dsimp [c]
    calc
      ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt (n : ℝ) * fp.u * xNorm) *
          Real.sqrt (3 * (n : ℝ)) =
          ((11 : ℝ) / 10 * Real.sqrt 3) *
            ((n : ℝ) ^ 2 * fp.u * xNorm) := by
              calc
                _ = (11 : ℝ) / 10 * (n : ℝ) *
                    (Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ))) *
                    fp.u * xNorm := by ring
                _ = (11 : ℝ) / 10 * (n : ℝ) *
                    (Real.sqrt 3 * (n : ℝ)) * fp.u * xNorm := by
                      rw [hsqrt_product]
                _ = _ := by ring
      _ ≤ 2 * ((n : ℝ) ^ 2 * fp.u * xNorm) :=
        mul_le_mul_of_nonneg_right hscalar hbase
      _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by ring
  change p26FrobNorm (p26Residual Q R X) ≤
    2 * (n : ℝ) ^ 2 * fp.u * xNorm
  calc
    p26FrobNorm (p26Residual Q R X) ≤ c * p26FrobNorm Q :=
      p26FrobNorm_le_mul_of_row_le _ _ c hc hrow
    _ ≤ c * Real.sqrt (3 * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (by simpa [Q] using hQFrob) hc
    _ ≤ 2 * (n : ℝ) ^ 2 * fp.u * xNorm := hcoefficient

end HighamBench
