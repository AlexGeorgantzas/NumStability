import HighamBench.P28Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

private noncomputable def p28AsFPModel (fp : P28FPModel) :
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
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring
  model_sqrt := by
    intro x _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

private lemma p28_rounded_dot_product_error
    (fp : P28FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hvalid : P28GammaValid fp.u n) :
    |p28RoundedDotProduct fp n x y - ∑ k : Fin n, x k * y k| ≤
      p28Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  simpa [p28RoundedDotProduct, p28Gamma, p28AsFPModel,
    NumStability.fl_dotProduct, NumStability.gamma,
    NumStability.gammaValid] using
    (NumStability.dotProduct_error_bound (p28AsFPModel fp) n x y hvalid)

private lemma p28_rounded_mat_mul_error
    (fp : P28FPModel) (n : ℕ) (A B : P28RealMatrix n)
    (hvalid : P28GammaValid fp.u n) (i j : Fin n) :
    |p28RoundedMatMul fp A B i j - p28MatMul A B i j| ≤
      p28Gamma fp.u n * ∑ k : Fin n, |A i k| * |B k j| := by
  simpa [p28RoundedMatMul, p28MatMul] using
    p28_rounded_dot_product_error fp n (A i) (fun k ↦ B k j) hvalid

/-- P28-T1: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p28_t1_newton_schulz_triple_product_error
    (fp : P28FPModel) (n : ℕ) (X : P28RealMatrix n)
    (hvalid : P28GammaValid fp.u n) :
    ∀ i j,
      |p28RoundedGramTriple fp X i j - p28ExactGramTriple X i j| ≤
        p28GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P28-T1-H001
  intro i j
  let R : P28RealMatrix n := p28RoundedMatMul fp X (p28Transpose X)
  let E : P28RealMatrix n := p28MatMul X (p28Transpose X)
  have houter :
      |p28RoundedMatMul fp R X i j - p28MatMul R X i j| ≤
        p28Gamma fp.u n * ∑ k : Fin n, |R i k| * |X k j| :=
    p28_rounded_mat_mul_error fp n R X hvalid i j
  have hfirst : ∀ k : Fin n,
      |R i k - E i k| ≤
        p28Gamma fp.u n * ∑ l : Fin n, |X i l| * |X k l| := by
    intro k
    simpa [R, E, p28Transpose] using
      p28_rounded_mat_mul_error fp n X (p28Transpose X) hvalid i k
  have htransport :
      |p28MatMul R X i j - p28MatMul E X i j| ≤
        p28Gamma fp.u n *
          ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
    rw [p28MatMul, p28MatMul, ← Finset.sum_sub_distrib]
    calc
      |∑ k : Fin n, (R i k * X k j - E i k * X k j)| ≤
          ∑ k : Fin n, |R i k * X k j - E i k * X k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |R i k - E i k| * |X k j| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← sub_mul, abs_mul]
      _ ≤ ∑ k : Fin n,
          (p28Gamma fp.u n * ∑ l : Fin n, |X i l| * |X k l|) *
            |X k j| := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hfirst k) (abs_nonneg _)
      _ = p28Gamma fp.u n *
          ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  calc
    |p28RoundedGramTriple fp X i j - p28ExactGramTriple X i j| =
        |(p28RoundedMatMul fp R X i j - p28MatMul R X i j) +
          (p28MatMul R X i j - p28MatMul E X i j)| := by
      simp only [p28RoundedGramTriple, p28ExactGramTriple, R, E]
      congr 1
      ring
    _ ≤ |p28RoundedMatMul fp R X i j - p28MatMul R X i j| +
          |p28MatMul R X i j - p28MatMul E X i j| := abs_add_le _ _
    _ ≤ p28Gamma fp.u n * (∑ k : Fin n, |R i k| * |X k j|) +
          p28Gamma fp.u n *
            ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| :=
      add_le_add houter htransport
    _ = p28GramTripleErrorMajorant fp X i j := by
      simp only [p28GramTripleErrorMajorant, R]

end HighamBench
