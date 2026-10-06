import HighamBench.P01Definitions
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Pairwise.Core

namespace HighamBench

open scoped BigOperators

noncomputable def StandardAddModel.toFPModel (fp : StandardAddModel) :
    NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
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

lemma recursiveSum_eq_numStability (fp : StandardAddModel) :
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
      unfold NumStability.fl_recursiveSum
      rw [Fin.foldl_succ_last]
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, NumStability.fl_recursiveSum,
          StandardAddModel.toFPModel, fp.fl_add_zero]
      · simp only [recursiveSum, dif_neg hn]
        change fp.fl_add
            (recursiveSum fp.fl_add n (fun i => v i.castSucc))
            (v (Fin.last n)) = _
        rw [ih]
        rfl

lemma recursivePreRound_eq_numStability (fp : StandardAddModel)
    {n : ℕ} (v : Fin n → ℝ) :
    recursivePreRound fp.fl_add v =
      NumStability.fl_partialSums fp.toFPModel v := by
  funext i
  simp only [recursivePreRound, NumStability.fl_partialSums]
  rw [recursiveSum_eq_numStability]

lemma pairwiseSum_eq_numStability (fp : StandardAddModel) :
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
      simp only [pairwiseSum, NumStability.fl_pairwiseSum]
      change fp.fl_add _ _ = fp.fl_add _ _
      congr 1
      · rw [ih]
        congr 1
      · rw [ih]
        congr 1

lemma gamma_eq_numStability (fp : StandardAddModel) (n : ℕ) :
    gamma fp.u n = NumStability.gamma fp.toFPModel n := by
  rfl

lemma gammaValid_iff_numStability (fp : StandardAddModel) (n : ℕ) :
    GammaValid fp.u n ↔ NumStability.gammaValid fp.toFPModel n := by
  rfl

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
  let n := 2 ^ r
  have hnvalid : NumStability.gammaValid fp.toFPModel (n - 1) := by
    exact (gammaValid_iff_numStability fp (n - 1)).mp hvalid
  have hr_le : r ≤ n - 1 := by
    dsimp [n]
    exact Nat.le_sub_one_of_lt (Nat.lt_two_pow_self)
  have hrvalid : NumStability.gammaValid fp.toFPModel r :=
    NumStability.gammaValid_mono fp.toFPModel hr_le hnvalid
  constructor
  · simpa [n, recursiveSum_eq_numStability,
        recursivePreRound_eq_numStability,
        StandardAddModel.toFPModel] using
      (NumStability.recursiveSum_running_error_bound fp.toFPModel n v)
  constructor
  · simpa [n, recursiveSum_eq_numStability, gamma_eq_numStability,
        StandardAddModel.toFPModel] using
      (NumStability.recursiveSum_forward_error_bound fp.toFPModel n v hnvalid)
  · simpa [n, pairwiseSum_eq_numStability, gamma_eq_numStability,
        StandardAddModel.toFPModel] using
      (NumStability.pairwiseSum_forward_error_bound fp.toFPModel r v hrvalid)

end HighamBench
