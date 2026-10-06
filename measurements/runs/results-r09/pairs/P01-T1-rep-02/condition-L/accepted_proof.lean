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
  let fp' : NumStability.FPModel := {
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
      intro x y hy
      refine ⟨0, ?_, by ring⟩
      simpa using fp.u_nonneg
    model_sqrt := by
      intro x hx
      refine ⟨0, ?_, by ring⟩
      simpa using fp.u_nonneg
  }
  have hvalid' : NumStability.gammaValid fp' r := by
    simpa [NumStability.gammaValid, fp'] using hvalid
  have hp : ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ),
      pairwiseSum fp.fl_add r v = NumStability.fl_pairwiseSum fp' r v := by
    intro n
    induction n with
    | zero =>
      intro w
      rfl
    | succ n ih =>
      intro w
      simp only [pairwiseSum, NumStability.fl_pairwiseSum]
      change fp.fl_add _ _ = fp.fl_add _ _
      congr 1
      · apply ih
      · apply ih
  have hb := NumStability.pairwiseSum_forward_error_bound fp' r v hvalid'
  rw [hp] at *
  simpa [NumStability.gamma, gamma, fp', abs_of_nonneg (hv _)] using hb

end HighamBench
