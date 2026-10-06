import HighamBench.P01Definitions
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

private lemma pairwiseSum_eq_library (fp : StandardAddModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) :
    pairwiseSum fp.fl_add r v =
      NumStability.fl_pairwiseSum fp.toFPModel r v := by
  induction r with
  | zero =>
      simp [pairwiseSum, NumStability.fl_pairwiseSum]
  | succ r ih =>
      simp only [pairwiseSum, NumStability.fl_pairwiseSum,
        StandardAddModel.toFPModel]
      congr 1
      · simpa [leftIndex] using
          ih (v := fun i => v (leftIndex r i))
      · simpa [rightIndex, Nat.add_comm] using
          ih (v := fun i => v (rightIndex r i))

theorem p01_t1_pairwise_nonnegative
    (fp : StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u r)
    (hv : ∀ i, 0 ≤ v i) :
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp.u r * ∑ i : Fin (2 ^ r), v i := by
  -- PROOF_START P01-T1-H001
  let nfp := fp.toFPModel
  have hvalid' : NumStability.gammaValid nfp r := by
    simpa [nfp, StandardAddModel.toFPModel, GammaValid,
      NumStability.gammaValid] using hvalid
  have h := NumStability.pairwiseSum_forward_error_bound nfp r v hvalid'
  rw [← pairwiseSum_eq_library fp r v] at h
  simpa [nfp, StandardAddModel.toFPModel, gamma, NumStability.gamma,
    abs_of_nonneg (hv _)] using h

end HighamBench
