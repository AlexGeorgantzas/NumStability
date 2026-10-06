import HighamBench.P01Definitions
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Pairwise.Core

namespace HighamBench

open scoped BigOperators

private noncomputable def standardAddModelToFPModel
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
        NumStability.fl_recursiveSum (standardAddModelToFPModel fp) n v := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | succ n ih =>
      intro v
      have hfold :
          NumStability.fl_recursiveSum (standardAddModelToFPModel fp) (n + 1) v =
            fp.fl_add
              (NumStability.fl_recursiveSum (standardAddModelToFPModel fp) n
                (fun i : Fin n => v i.castSucc))
              (v (Fin.last n)) :=
        Fin.foldl_succ_last _ _
      rw [recursiveSum.eq_2, hfold]
      by_cases hn : n = 0
      · subst n
        simpa [NumStability.fl_recursiveSum] using
          (fp.fl_add_zero (v (Fin.last 0))).symm
      · rw [ih]
        simp [hn]

private theorem recursivePreRound_eq_library
    (fp : StandardAddModel) {n : ℕ} (v : Fin n → ℝ) :
    recursivePreRound fp.fl_add v =
      NumStability.fl_partialSums (standardAddModelToFPModel fp) v := by
  funext i
  simp only [recursivePreRound, NumStability.fl_partialSums]
  rw [recursiveSum_eq_library]

private theorem pairwiseSum_eq_library (fp : StandardAddModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ),
      pairwiseSum fp.fl_add r v =
        NumStability.fl_pairwiseSum (standardAddModelToFPModel fp) r v := by
  intro r
  induction r with
  | zero =>
      intro v
      rfl
  | succ r ih =>
      intro v
      simp only [pairwiseSum, NumStability.fl_pairwiseSum]
      change fp.fl_add _ _ = fp.fl_add _ _
      congr 1
      · rw [ih]
        congr 1
      · rw [ih]
        congr 1

private theorem rank_le_pow_two_sub_one (r : ℕ) : r ≤ 2 ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ r := one_le_pow₀ (by omega)
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
  let fp' := standardAddModelToFPModel fp
  have hvalid' : NumStability.gammaValid fp' (2 ^ r - 1) := by
    simpa [fp', standardAddModelToFPModel, GammaValid,
      NumStability.gammaValid] using hvalid
  have hvalid_r : NumStability.gammaValid fp' r :=
    NumStability.gammaValid_mono fp' (rank_le_pow_two_sub_one r) hvalid'
  have hrun := NumStability.recursiveSum_running_error_bound fp' (2 ^ r) v
  have hrec := NumStability.recursiveSum_forward_error_bound fp' (2 ^ r) v hvalid'
  have hpair := NumStability.pairwiseSum_forward_error_bound fp' r v hvalid_r
  constructor
  · simpa [fp', recursiveSum_eq_library, recursivePreRound_eq_library,
      standardAddModelToFPModel] using hrun
  constructor
  · simpa [fp', recursiveSum_eq_library, standardAddModelToFPModel,
      gamma, NumStability.gamma] using hrec
  · simpa [fp', pairwiseSum_eq_library, standardAddModelToFPModel,
      gamma, NumStability.gamma] using hpair

end HighamBench
