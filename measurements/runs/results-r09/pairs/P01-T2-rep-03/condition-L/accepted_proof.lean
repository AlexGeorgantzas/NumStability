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
    intro x y _
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg
  model_sqrt := by
    intro x _
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg

private theorem recursiveSum_eq_library (fp : StandardAddModel) :
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
      rw [NumStability.fl_recursiveSum, Fin.foldl_succ_last]
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, NumStability.fl_recursiveSum,
          StandardAddModel.toFPModel, fp.fl_add_zero]
      · rw [recursiveSum, dif_neg hn, ih]
        rfl

private theorem recursivePreRound_eq_library (fp : StandardAddModel)
    {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    recursivePreRound fp.fl_add v i =
      NumStability.fl_partialSums fp.toFPModel v i := by
  unfold recursivePreRound NumStability.fl_partialSums
  rw [recursiveSum_eq_library]

private theorem pairwiseSum_eq_library (fp : StandardAddModel) :
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
      · apply ih
      · apply ih

private theorem depth_le_rounding_count (r : ℕ) : r ≤ 2 ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ r := Nat.pow_pos (by omega)
      have hstep : r + 1 ≤ 2 ^ r := by omega
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
  let fp' := fp.toFPModel
  have hvalid' : NumStability.gammaValid fp' (2 ^ r - 1) := by
    exact hvalid
  have hr_le : r ≤ 2 ^ r - 1 := depth_le_rounding_count r
  have hvalid_r : NumStability.gammaValid fp' r :=
    NumStability.gammaValid_mono fp' hr_le hvalid'
  constructor
  · simpa [fp', recursiveSum_eq_library, recursivePreRound_eq_library] using
      (NumStability.recursiveSum_running_error_bound fp' (2 ^ r) v)
  constructor
  · simpa [fp', gamma, NumStability.gamma, recursiveSum_eq_library] using
      (NumStability.recursiveSum_forward_error_bound fp' (2 ^ r) v hvalid')
  · simpa [fp', gamma, NumStability.gamma, pairwiseSum_eq_library] using
      (NumStability.pairwiseSum_forward_error_bound fp' r v hvalid_r)

end HighamBench
