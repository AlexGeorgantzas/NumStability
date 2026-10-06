import HighamBench.P23Definitions
import NumStability.Analysis.Error.MatrixProducts.EvaluationTrees.ProductErrorNotation

namespace HighamBench

noncomputable def p23ToFPModel (fp : P23FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

open NumStability

noncomputable def p23PowerTree {n : ℕ} (X : P23Matrix n) :
    ℕ → Ch14RectProductTree n n
  | 0 => .leaf X
  | k + 1 => .node (p23PowerTree X k) (.leaf X)

@[simp] theorem p23PowerTree_operationBudget {n : ℕ} (X : P23Matrix n) :
    ∀ k, Ch14RectProductTree.operationBudget (p23PowerTree X k) = k * n
  | 0 => by simp [p23PowerTree]
  | k + 1 => by
      simp [p23PowerTree, p23PowerTree_operationBudget X k, Nat.succ_mul]

@[simp] theorem p23PowerTree_exactEval {n : ℕ} (X : P23Matrix n) :
    ∀ k, Ch14RectProductTree.exactEval (p23PowerTree X k) = p23PowerSteps X k
  | 0 => rfl
  | k + 1 => by
      simp only [p23PowerTree, Ch14RectProductTree.exactEval_node,
        Ch14RectProductTree.exactEval_leaf, p23PowerSteps]
      rw [p23PowerTree_exactEval X k]
      rfl

@[simp] theorem p23PowerTree_roundedEval (fp : P23FPModel) {n : ℕ}
    (X : P23Matrix n) :
    ∀ k, Ch14RectProductTree.roundedEval (p23ToFPModel fp) (p23PowerTree X k) =
      p23RoundedPowerSteps fp X k
  | 0 => rfl
  | k + 1 => by
      simp only [p23PowerTree, Ch14RectProductTree.roundedEval_node,
        Ch14RectProductTree.roundedEval_leaf, p23RoundedPowerSteps]
      rw [p23PowerTree_roundedEval fp X k]
      rfl

@[simp] theorem p23PowerTree_exactAbsProduct {n : ℕ} (X : P23Matrix n) :
    ∀ k, Ch14RectProductTree.exactAbsProduct (p23PowerTree X k) =
      p23PowerSteps (p23AbsMatrix X) k
  | 0 => rfl
  | k + 1 => by
      simp only [p23PowerTree, Ch14RectProductTree.exactAbsProduct_node,
        Ch14RectProductTree.exactAbsProduct_leaf, p23PowerSteps]
      rw [p23PowerTree_exactAbsProduct X k]
      rfl

/-- P23-T1: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p23_t1_lemma_2_2
    (fp : P23FPModel) (n k : ℕ) (X : P23Matrix n)
    (hvalid : P23GammaValid fp.u (k * n)) :
    ∀ i j,
      |p23RoundedPowerSteps fp X k i j - p23PowerSteps X k i j| ≤
        p23Gamma fp.u (k * n) * p23PowerSteps (p23AbsMatrix X) k i j := by
  -- PROOF_START P23-T1-H001
  intro i j
  let fp' := p23ToFPModel fp
  let tree := p23PowerTree X k
  have hvalid' : gammaValid fp' (Ch14RectProductTree.operationBudget tree) := by
    simpa [fp', tree, gammaValid, P23GammaValid] using hvalid
  have herr :=
    Ch14RectProductTree.productDelta_abs_le_orderCoefficient fp' tree hvalid' i j
  have hcoef :=
    Ch14RectProductTree.orderCoefficient_le_gamma_operationBudget fp' tree hvalid'
  have habs := Ch14RectProductTree.exactAbsProduct_nonneg tree i j
  have h := herr.trans (mul_le_mul_of_nonneg_right hcoef habs)
  simpa [Ch14RectProductTree.productDelta, fp', tree, gamma, p23Gamma] using h

end HighamBench
