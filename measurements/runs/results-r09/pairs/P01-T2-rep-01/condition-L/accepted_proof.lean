import HighamBench.P01Definitions
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Pairwise.Core

namespace HighamBench

open scoped BigOperators

private noncomputable def StandardAddModel.toFPModel
    (fp : StandardAddModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg
  model_mul := by
    intro x y
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg
  model_div := by
    intro x y _hy
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg
  model_sqrt := by
    intro x _hx
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg

private theorem recursiveSum_eq_library (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      recursiveSum fp.fl_add n v =
        NumStability.fl_recursiveSum fp.toFPModel n v
  | 0, v => by
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | n + 1, v => by
      unfold NumStability.fl_recursiveSum
      rw [Fin.foldl_succ_last]
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, NumStability.fl_recursiveSum,
          StandardAddModel.toFPModel, fp.fl_add_zero]
      · rw [recursiveSum, dif_neg hn]
        congr 1
        exact recursiveSum_eq_library fp n (fun i => v i.castSucc)

private theorem recursivePreRound_eq_library (fp : StandardAddModel)
    {n : ℕ} (v : Fin n → ℝ) :
    recursivePreRound fp.fl_add v =
      NumStability.fl_partialSums fp.toFPModel v := by
  funext i
  unfold recursivePreRound NumStability.fl_partialSums
  rw [recursiveSum_eq_library]

private theorem pairwiseSum_eq_library (fp : StandardAddModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ),
      pairwiseSum fp.fl_add r v =
        NumStability.fl_pairwiseSum fp.toFPModel r v
  | 0, v => by
      simp [pairwiseSum, NumStability.fl_pairwiseSum]
  | r + 1, v => by
      simp only [pairwiseSum, NumStability.fl_pairwiseSum]
      congr 1
      · apply pairwiseSum_eq_library fp r
      · apply pairwiseSum_eq_library fp r

theorem p01_t2_recursive_running_and_pairwise_bounds
    (fp : StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u (2 ^ r - 1)) :
    |recursiveSum fp.fl_add (2 ^ r) v - ∑ i : Fin (2 ^ r), v i| ≤
        fp.u * ∑ i : Fin (2 ^ r), |recursivePreRound fp.fl_add v i| ∧
    |recursiveSum fp.fl_add (2 ^ r) v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u (2 ^ r - 1) * ∑ i : Fin (2 ^ r), |v i| ∧
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u r * ∑ i : Fin (2 ^ r), |v i| := by
  -- PROOF_START P01-T2-H001
  let model := fp.toFPModel
  have hvalid' : NumStability.gammaValid model (2 ^ r - 1) := by
    simpa [model, StandardAddModel.toFPModel, GammaValid,
      NumStability.gammaValid] using hvalid
  have pow_bound : ∀ k : ℕ, k ≤ 2 ^ k - 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        simp only [pow_succ]
        have hp : 0 < 2 ^ k := pow_pos (by omega) k
        have hsub : 2 ^ k - 1 + 1 = 2 ^ k := Nat.sub_add_cancel (by omega)
        have hstep : k + 1 ≤ 2 ^ k := by
          calc
            k + 1 ≤ (2 ^ k - 1) + 1 := Nat.add_le_add_right ih 1
            _ = 2 ^ k := hsub
        omega
  have hr_le : r ≤ 2 ^ r - 1 := pow_bound r
  have hrvalid : NumStability.gammaValid model r :=
    NumStability.gammaValid_mono model hr_le hvalid'
  constructor
  · simpa [model, StandardAddModel.toFPModel, recursiveSum_eq_library,
      recursivePreRound_eq_library] using
      (NumStability.recursiveSum_running_error_bound model (2 ^ r) v)
  constructor
  · simpa [model, StandardAddModel.toFPModel, gamma,
      NumStability.gamma, recursiveSum_eq_library] using
      (NumStability.recursiveSum_forward_error_bound model (2 ^ r) v hvalid')
  · simpa [model, StandardAddModel.toFPModel, gamma,
      NumStability.gamma, pairwiseSum_eq_library] using
      (NumStability.pairwiseSum_forward_error_bound model r v hrvalid)

end HighamBench
