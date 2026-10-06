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
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := by
    intro x y
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

private lemma recursiveSum_eq_library (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      recursiveSum fp.fl_add n v =
        NumStability.fl_recursiveSum fp.toFPModel n v := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | succ n ih =>
      intro v
      by_cases hn : n = 0
      · subst n
        rw [recursiveSum]
        unfold NumStability.fl_recursiveSum
        rw [Fin.foldl_succ_last]
        simp [StandardAddModel.toFPModel, fp.fl_add_zero]
      · rw [recursiveSum, dif_neg hn]
        unfold NumStability.fl_recursiveSum
        rw [Fin.foldl_succ_last]
        change fp.fl_add _ _ = fp.fl_add _ _
        congr 1
        exact ih _

private lemma recursivePreRound_eq_library (fp : StandardAddModel)
    {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    recursivePreRound fp.fl_add v i =
      NumStability.fl_partialSums fp.toFPModel v i := by
  unfold recursivePreRound NumStability.fl_partialSums
  rw [recursiveSum_eq_library]

private lemma pairwiseSum_eq_library (fp : StandardAddModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ),
      pairwiseSum fp.fl_add r v =
        NumStability.fl_pairwiseSum fp.toFPModel r v := by
  intro r
  induction r with
  | zero =>
      intro v
      rfl
  | succ r ih =>
      intro v
      simp only [pairwiseSum, NumStability.fl_pairwiseSum,
        StandardAddModel.toFPModel]
      congr 1
      · exact ih _
      · exact ih _

private lemma depth_le_rounds (r : ℕ) : r ≤ 2 ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ r := by positivity
      omega

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
  let fp' : NumStability.FPModel := fp.toFPModel
  have hvalid' : NumStability.gammaValid fp' (2 ^ r - 1) := by
    simpa [fp', StandardAddModel.toFPModel, NumStability.gammaValid,
      GammaValid] using hvalid
  have hdepth : NumStability.gammaValid fp' r :=
    NumStability.gammaValid_mono fp' (depth_le_rounds r) hvalid'
  have hrun :=
    NumStability.recursiveSum_running_error_bound fp' (2 ^ r) v
  have hrec :=
    NumStability.recursiveSum_forward_error_bound fp' (2 ^ r) v hvalid'
  have hpair :=
    NumStability.pairwiseSum_forward_error_bound fp' r v hdepth
  constructor
  · simpa [fp', StandardAddModel.toFPModel, recursiveSum_eq_library,
      recursivePreRound_eq_library] using hrun
  constructor
  · simpa [fp', StandardAddModel.toFPModel, recursiveSum_eq_library,
      HighamBench.gamma, NumStability.gamma] using hrec
  · simpa [fp', StandardAddModel.toFPModel, pairwiseSum_eq_library,
      HighamBench.gamma, NumStability.gamma] using hpair

end HighamBench
