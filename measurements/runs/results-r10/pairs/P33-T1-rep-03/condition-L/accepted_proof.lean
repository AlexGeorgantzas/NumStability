import HighamBench.P33Definitions
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core

namespace HighamBench

open scoped BigOperators

private noncomputable def p33ToFPModel (fp : P33FPModel) :
    NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := by
    intro y _hy
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  let fp' := p33ToFPModel fp
  cases s with
  | zero =>
      obtain ⟨δ, hδ, hfl⟩ := fp.model_sub b 0
      have hvalid' : NumStability.gammaValid fp' 1 := by
        simpa [fp', p33ToFPModel, NumStability.gammaValid,
          P33GammaValid] using hvalid
      have huγ : fp.u ≤ NumStability.gamma fp' 1 := by
        simpa [fp', p33ToFPModel] using
          (NumStability.u_le_gamma fp' (by omega : 0 < 1) hvalid')
      simp [p33RoundedResidual, p33RoundedSparseRowProduct,
        p33ExactResidual, p33ResidualErrorMajorant]
      rw [hfl]
      simp only [sub_zero]
      rw [show b * (1 + δ) - b = b * δ by ring, abs_mul]
      calc
        |b| * |δ| ≤ |b| * fp.u :=
          mul_le_mul_of_nonneg_left hδ (abs_nonneg b)
        _ = fp.u * |b| := by ring
        _ ≤ NumStability.gamma fp' 1 * |b| :=
          mul_le_mul_of_nonneg_right huγ (abs_nonneg b)
        _ = p33Gamma fp.u 1 * |b| := by
          rfl
  | succ n =>
      have hs : NumStability.gammaValid fp' (n + 1) := by
        apply NumStability.gammaValid_mono fp' (by omega : n + 1 ≤ n + 1 + 1)
        simpa [fp', p33ToFPModel, NumStability.gammaValid,
          P33GammaValid] using hvalid
      have hs1 : NumStability.gammaValid fp' (n + 1 + 1) := by
        simpa [fp', p33ToFPModel, NumStability.gammaValid,
          P33GammaValid] using hvalid
      have h := NumStability.conventional_residual_error fp' (n + 1)
        (fun _ => a) x (fun _ => b) hs hs1 (0 : Fin (n + 1))
      simpa [fp', p33ToFPModel, NumStability.fl_residual,
        NumStability.fl_matVec, NumStability.fl_dotProduct,
        p33RoundedResidual, p33RoundedSparseRowProduct,
        p33ExactResidual, p33ResidualErrorMajorant,
        NumStability.gamma, p33Gamma] using h

end HighamBench
