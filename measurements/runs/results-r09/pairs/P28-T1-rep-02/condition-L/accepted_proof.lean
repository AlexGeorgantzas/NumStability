import HighamBench.P28Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

noncomputable def p28FPModelToNumStability (fp : P28FPModel) :
    NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y ↦ x - y
  fl_mul := fp.fl_mul
  fl_div := fun x y ↦ x / y
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

lemma p28RoundedDotProduct_error_bound
    (fp : P28FPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hvalid : P28GammaValid fp.u n) :
    |p28RoundedDotProduct fp n x y - ∑ k : Fin n, x k * y k| ≤
      p28Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  simpa [p28RoundedDotProduct, p28Gamma, p28FPModelToNumStability,
    NumStability.fl_dotProduct, NumStability.gamma,
    NumStability.gammaValid, P28GammaValid] using
    (NumStability.dotProduct_error_bound
      (p28FPModelToNumStability fp) n x y hvalid)

/-- P28-T1: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p28_t1_newton_schulz_triple_product_error
    (fp : P28FPModel) (n : ℕ) (X : P28RealMatrix n)
    (hvalid : P28GammaValid fp.u n) :
    ∀ i j,
      |p28RoundedGramTriple fp X i j - p28ExactGramTriple X i j| ≤
        p28GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P28-T1-H001
  intro i j
  let Ahat : P28RealMatrix n := p28RoundedMatMul fp X (p28Transpose X)
  let A : P28RealMatrix n := p28MatMul X (p28Transpose X)
  have houter := p28RoundedDotProduct_error_bound fp n
    (Ahat i) (fun k ↦ X k j) hvalid
  have hinner : ∀ k : Fin n,
      |Ahat i k - A i k| ≤
        p28Gamma fp.u n * ∑ l : Fin n, |X i l| * |X k l| := by
    intro k
    simpa [Ahat, A, p28RoundedMatMul, p28MatMul, p28Transpose] using
      (p28RoundedDotProduct_error_bound fp n
        (X i) (fun l ↦ X k l) hvalid)
  have htransport :
      |∑ k : Fin n, Ahat i k * X k j - ∑ k : Fin n, A i k * X k j| ≤
        p28Gamma fp.u n *
          ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k : Fin n, (Ahat i k * X k j - A i k * X k j)| ≤
          ∑ k : Fin n, |Ahat i k * X k j - A i k * X k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |Ahat i k - A i k| * |X k j| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← sub_mul, abs_mul]
      _ ≤ ∑ k : Fin n,
          (p28Gamma fp.u n * ∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hinner k) (abs_nonneg _)
      _ = p28Gamma fp.u n *
          ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hsplit :
      |p28RoundedDotProduct fp n (Ahat i) (fun k ↦ X k j) -
          ∑ k : Fin n, A i k * X k j| ≤
        |p28RoundedDotProduct fp n (Ahat i) (fun k ↦ X k j) -
          ∑ k : Fin n, Ahat i k * X k j| +
        |∑ k : Fin n, Ahat i k * X k j - ∑ k : Fin n, A i k * X k j| := by
    calc
      |p28RoundedDotProduct fp n (Ahat i) (fun k ↦ X k j) -
          ∑ k : Fin n, A i k * X k j| =
        |(p28RoundedDotProduct fp n (Ahat i) (fun k ↦ X k j) -
            ∑ k : Fin n, Ahat i k * X k j) +
          (∑ k : Fin n, Ahat i k * X k j - ∑ k : Fin n, A i k * X k j)| := by
            congr 1
            ring
      _ ≤ _ := abs_add_le _ _
  have hcombined := le_trans hsplit (add_le_add houter htransport)
  simpa [p28RoundedGramTriple, p28ExactGramTriple,
    p28GramTripleErrorMajorant, p28RoundedMatMul, p28MatMul, Ahat, A] using
    hcombined

end HighamBench
