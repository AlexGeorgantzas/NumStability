import HighamBench.P28Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

open scoped BigOperators

/-- Embed the two-operation model used by P28 into the library's full
floating-point model.  The operations not used by the dot product are taken to
be exact. -/
noncomputable def p28ToFPModel (fp : P28FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fp.fl_mul
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fun x y => ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := fp.model_mul
  model_div := fun x y _ => ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := fun x _ => ⟨0, by simpa using fp.u_nonneg, by ring⟩

lemma p28RoundedDotProduct_eq_fl_dotProduct
    (fp : P28FPModel) (n : ℕ) (x y : Fin n → ℝ) :
    p28RoundedDotProduct fp n x y =
      NumStability.fl_dotProduct (p28ToFPModel fp) n x y := by
  cases n <;> rfl

/-- P28-T1: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p28_t1_newton_schulz_triple_product_error
    (fp : P28FPModel) (n : ℕ) (X : P28RealMatrix n)
    (hvalid : P28GammaValid fp.u n) :
    ∀ i j,
      |p28RoundedGramTriple fp X i j - p28ExactGramTriple X i j| ≤
        p28GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P28-T1-H001
  intro i j
  let fp' : NumStability.FPModel := p28ToFPModel fp
  have hvalid' : NumStability.gammaValid fp' n := by
    simpa [fp', p28ToFPModel, NumStability.gammaValid, P28GammaValid] using hvalid
  have houter :=
    NumStability.dotProduct_error_bound fp' n
      (fun k => p28RoundedMatMul fp X (p28Transpose X) i k)
      (fun k => X k j) hvalid'
  have houter' :
      |p28RoundedGramTriple fp X i j -
          ∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j| ≤
        p28Gamma fp.u n *
          ∑ k : Fin n, |p28RoundedMatMul fp X (p28Transpose X) i k| * |X k j| := by
    simpa [p28RoundedGramTriple, p28RoundedMatMul,
      p28RoundedDotProduct_eq_fl_dotProduct, fp', p28ToFPModel,
      p28Gamma, NumStability.gamma] using houter
  have hinner : ∀ k : Fin n,
      |p28RoundedMatMul fp X (p28Transpose X) i k -
          ∑ l : Fin n, X i l * X k l| ≤
        p28Gamma fp.u n * ∑ l : Fin n, |X i l| * |X k l| := by
    intro k
    have h :=
      NumStability.dotProduct_error_bound fp' n
        (fun l => X i l) (fun l => p28Transpose X l k) hvalid'
    simpa [p28RoundedMatMul, p28RoundedDotProduct_eq_fl_dotProduct,
      p28Transpose, fp', p28ToFPModel, p28Gamma,
      NumStability.gamma] using h
  have htransport :
      |∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j -
          ∑ k : Fin n, (∑ l : Fin n, X i l * X k l) * X k j| ≤
        p28Gamma fp.u n *
          ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k : Fin n,
          (p28RoundedMatMul fp X (p28Transpose X) i k * X k j -
            (∑ l : Fin n, X i l * X k l) * X k j)| ≤
          ∑ k : Fin n,
            |p28RoundedMatMul fp X (p28Transpose X) i k * X k j -
              (∑ l : Fin n, X i l * X k l) * X k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n,
            |p28RoundedMatMul fp X (p28Transpose X) i k -
              ∑ l : Fin n, X i l * X k l| * |X k j| := by
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
  calc
    |p28RoundedGramTriple fp X i j - p28ExactGramTriple X i j| =
        |(p28RoundedGramTriple fp X i j -
            ∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j) +
          ((∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j) -
            ∑ k : Fin n, (∑ l : Fin n, X i l * X k l) * X k j)| := by
      simp only [p28ExactGramTriple, p28MatMul, p28Transpose]
      congr 1
      ring
    _ ≤
        |p28RoundedGramTriple fp X i j -
            ∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j| +
          |(∑ k : Fin n, p28RoundedMatMul fp X (p28Transpose X) i k * X k j) -
            ∑ k : Fin n, (∑ l : Fin n, X i l * X k l) * X k j| :=
      abs_add_le _ _
    _ ≤ p28Gamma fp.u n *
          (∑ k : Fin n,
            |p28RoundedMatMul fp X (p28Transpose X) i k| * |X k j|) +
        p28Gamma fp.u n *
          (∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j|) :=
      add_le_add houter' htransport
    _ = p28GramTripleErrorMajorant fp X i j := by
      rfl

end HighamBench
