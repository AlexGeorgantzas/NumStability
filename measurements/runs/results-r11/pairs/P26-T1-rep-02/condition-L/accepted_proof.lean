import HighamBench.P26Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace HighamBench

private noncomputable def p26AsFPModel (fp : P26FPModel) :
    NumStability.FPModel where
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
    (L : P26Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) :
    p26ForwardSubSteps fp n L b k hk x =
      NumStability.fl_forwardSub_steps (p26AsFPModel fp) n L b k hk x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      simp only [p26ForwardSubSteps, NumStability.fl_forwardSub_steps]
      simp only [p26AsFPModel]
      rw [ih]
      rfl

private lemma p26ForwardSub_eq (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ) :
    p26ForwardSub fp n L b =
      NumStability.fl_forwardSub (p26AsFPModel fp) n L b := by
  exact p26ForwardSubSteps_eq fp n L b n (le_refl n) (fun _ => 0)

private lemma p26VecNormSq_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ p26VecNormSq x := by
  unfold p26VecNormSq
  positivity

private lemma p26FrobNormSq_nonneg {m n : ℕ} (A : P26Matrix m n) :
    0 ≤ p26FrobNormSq A := by
  unfold p26FrobNormSq
  exact Finset.sum_nonneg fun i _ => p26VecNormSq_nonneg (A i)

private lemma p26VecNorm_sq {n : ℕ} (x : Fin n → ℝ) :
    p26VecNorm x ^ 2 = p26VecNormSq x := by
  exact Real.sq_sqrt (p26VecNormSq_nonneg x)

private lemma p26FrobNorm_sq {m n : ℕ} (A : P26Matrix m n) :
    p26FrobNorm A ^ 2 = p26FrobNormSq A := by
  exact Real.sq_sqrt (p26FrobNormSq_nonneg A)

private lemma p26FrobNorm_le_mul {m n : ℕ}
    (A B : P26Matrix m n) (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ i, p26VecNorm (A i) ≤ c * p26VecNorm (B i)) :
    p26FrobNorm A ≤ c * p26FrobNorm B := by
  have hrowSq : ∀ i, p26VecNormSq (A i) ≤ c ^ 2 * p26VecNormSq (B i) := by
    intro i
    rw [← p26VecNorm_sq, ← p26VecNorm_sq]
    have hA : 0 ≤ p26VecNorm (A i) := Real.sqrt_nonneg _
    have hB : 0 ≤ p26VecNorm (B i) := Real.sqrt_nonneg _
    nlinarith [hrow i]
  have hsq : p26FrobNorm A ^ 2 ≤ (c * p26FrobNorm B) ^ 2 := by
    rw [p26FrobNorm_sq, p26FrobNormSq, mul_pow, p26FrobNorm_sq,
      p26FrobNormSq, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hrowSq i
  have hA : 0 ≤ p26FrobNorm A := Real.sqrt_nonneg _
  have hB : 0 ≤ p26FrobNorm B := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hc hB]

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
  let nfp := p26AsFPModel fp
  have hnvalid : NumStability.gammaValid nfp n := by
    simpa [nfp, p26AsFPModel, NumStability.gammaValid, P26GammaValid] using hvalid
  have hLdiag : ∀ i, p26Transpose R i i ≠ 0 := by
    intro i
    simpa [p26Transpose] using hdiag i
  have hLlower : ∀ i j : Fin n, i.val < j.val → p26Transpose R i j = 0 := by
    intro i j hij
    simpa [p26Transpose] using hupper j i hij
  have hrows : ∀ i : Fin m,
      p26VecNorm (p26Residual (p26RoundedQ fp X R) R X i) ≤
        ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm) *
          p26VecNorm (p26RoundedQ fp X R i) := by
    intro i
    obtain ⟨deltaL, hdeltaL, heq⟩ :=
      NumStability.forwardSub_backward_error nfp n (p26Transpose R) (X i)
        hLdiag hLlower hnvalid
    apply hperturb i deltaL
    · intro k j
      simpa [nfp, p26AsFPModel, NumStability.gamma, p26Gamma] using hdeltaL k j
    · intro k
      simpa [p26RoundedQ, p26ForwardSub_eq, nfp] using heq k
  let c : ℝ := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hn0)
          (Real.sqrt_nonneg _))
        fp.u_nonneg)
      hxNorm
  have hresQ :
      p26FrobNorm (p26Residual (p26RoundedQ fp X R) R X) ≤
        c * p26FrobNorm (p26RoundedQ fp X R) := by
    apply p26FrobNorm_le_mul _ _ c hc
    intro i
    simpa [c] using hrows i
  have hresSqrt :
      p26FrobNorm (p26Residual (p26RoundedQ fp X R) R X) ≤
        c * Real.sqrt (3 * (n : ℝ)) :=
    le_trans hresQ (mul_le_mul_of_nonneg_left hQFrob hc)
  have hsqrt3 : Real.sqrt (3 : ℝ) ≤ (20 : ℝ) / 11 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hsqrtprod :
      Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ)) ≤
        (20 : ℝ) / 11 * (n : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      Real.sqrt (n : ℝ) * (Real.sqrt 3 * Real.sqrt (n : ℝ)) =
          Real.sqrt 3 * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
      _ = Real.sqrt 3 * (n : ℝ) := by rw [Real.mul_self_sqrt hn0]
      _ ≤ ((20 : ℝ) / 11) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrt3 hn0
  have hconstant :
      c * Real.sqrt (3 * (n : ℝ)) ≤
        2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
    calc
      c * Real.sqrt (3 * (n : ℝ)) =
          ((11 : ℝ) / 10 * (n : ℝ) * fp.u * xNorm) *
            (Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ))) := by
              dsimp [c]
              ring
      _ ≤ ((11 : ℝ) / 10 * (n : ℝ) * fp.u * xNorm) *
            ((20 : ℝ) / 11 * (n : ℝ)) := by
              apply mul_le_mul_of_nonneg_left hsqrtprod
              exact mul_nonneg
                (mul_nonneg (mul_nonneg (by norm_num) hn0) fp.u_nonneg)
                hxNorm
      _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by ring
  exact le_trans hresSqrt hconstant

end HighamBench
