import HighamBench.P01Definitions
import NumStability.Algorithms.Summation.Pairwise.Core

namespace HighamBench

open scoped BigOperators

theorem p01_t1_pairwise_nonnegative
    (fp : StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u r)
    (hv : ∀ i, 0 ≤ v i) :
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp.u r * ∑ i : Fin (2 ^ r), v i := by
  -- PROOF_START P01-T1-H001
  let nfp : NumStability.FPModel :=
    { NumStability.FPModel.exactWithUnitRoundoff fp.u fp.u_nonneg with
      fl_add := fp.fl_add
      fl_add_zero := fp.fl_add_zero
      model_add := fp.model_add }
  have hvalid' : NumStability.gammaValid nfp r := by
    simpa [nfp, NumStability.gammaValid, GammaValid] using hvalid
  have hpairwise_all : ∀ (k : ℕ) (w : Fin (2 ^ k) → ℝ),
      NumStability.fl_pairwiseSum nfp k w = pairwiseSum fp.fl_add k w := by
    intro k
    induction k with
    | zero => intro w; rfl
    | succ k ih =>
        intro w
        simp only [NumStability.fl_pairwiseSum, pairwiseSum]
        change fp.fl_add _ _ = fp.fl_add _ _
        congr 1 <;> simpa [leftIndex, rightIndex] using ih _
  have hpairwise := hpairwise_all r v
  have hbound :=
    NumStability.pairwiseSum_forward_error_bound nfp r v hvalid'
  rw [hpairwise] at hbound
  simpa [nfp, NumStability.gamma, gamma, abs_of_nonneg (hv _)] using hbound

end HighamBench
