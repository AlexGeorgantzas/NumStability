import HighamBench.P01Definitions
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Pairwise.Core

namespace HighamBench

open scoped BigOperators

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
  let fp' : NumStability.FPModel :=
    { u := fp.u
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
        simpa using fp.u_nonneg }
  have hrec : ∀ (n : ℕ) (w : Fin n → ℝ),
      recursiveSum fp.fl_add n w = NumStability.fl_recursiveSum fp' n w := by
    intro n
    induction n with
    | zero =>
        intro w
        simp [recursiveSum, NumStability.fl_recursiveSum]
    | succ n ih =>
        intro w
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [recursiveSum, NumStability.fl_recursiveSum,
            Fin.foldl_succ_last, fp', fp.fl_add_zero]
        · rw [recursiveSum, dif_neg (Nat.ne_of_gt hn)]
          rw [show NumStability.fl_recursiveSum fp' (n + 1) w =
              fp'.fl_add
                (NumStability.fl_recursiveSum fp' n (fun i => w i.castSucc))
                (w (Fin.last n)) from Fin.foldl_succ_last _ _]
          rw [ih]
  have hpartial : ∀ {n : ℕ} (w : Fin n → ℝ) (i : Fin n),
      recursivePreRound fp.fl_add w i =
        NumStability.fl_partialSums fp' w i := by
    intro n w i
    simp only [recursivePreRound, NumStability.fl_partialSums]
    rw [hrec]
  have hpair : ∀ (k : ℕ) (w : Fin (2 ^ k) → ℝ),
      pairwiseSum fp.fl_add k w = NumStability.fl_pairwiseSum fp' k w := by
    intro k
    induction k with
    | zero =>
        intro w
        rfl
    | succ k ih =>
        intro w
        simp only [pairwiseSum, NumStability.fl_pairwiseSum]
        rw [ih, ih]
        congr 2 <;> funext i <;> apply congrArg w <;> apply Fin.ext <;> rfl
  have hvalid' : NumStability.gammaValid fp' (2 ^ r - 1) := by
    exact hvalid
  have hrle : r ≤ 2 ^ r - 1 := by
    have hrlt : r < 2 ^ r := Nat.lt_two_pow_self
    omega
  have hvalid_r : NumStability.gammaValid fp' r :=
    NumStability.gammaValid_mono fp' hrle hvalid'
  constructor
  · simpa only [hrec, hpartial] using
      (NumStability.recursiveSum_running_error_bound fp' (2 ^ r) v)
  constructor
  · simpa only [hrec, NumStability.gamma, gamma, fp'] using
      (NumStability.recursiveSum_forward_error_bound fp' (2 ^ r) v hvalid')
  · simpa only [hpair, NumStability.gamma, gamma, fp'] using
      (NumStability.pairwiseSum_forward_error_bound fp' r v hvalid_r)

end HighamBench
