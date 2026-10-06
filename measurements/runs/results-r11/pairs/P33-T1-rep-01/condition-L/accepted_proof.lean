import HighamBench.P33Definitions
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core

namespace HighamBench

noncomputable def p33ToFPModel (fp : P33FPModel) : NumStability.FPModel where
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
  let nfp : NumStability.FPModel := p33ToFPModel fp
  have hn1 : NumStability.gammaValid nfp (s + 1) := by
    simpa [NumStability.gammaValid, nfp, p33ToFPModel, P33GammaValid] using hvalid
  have hn : NumStability.gammaValid nfp s :=
    NumStability.gammaValid_mono nfp (Nat.le_succ s) hn1
  cases s with
  | zero =>
      obtain ⟨δ, hδ, hfl⟩ := fp.model_sub b 0
      have hu_gamma : fp.u ≤ p33Gamma fp.u 1 := by
        simpa [p33Gamma, NumStability.gamma, nfp, p33ToFPModel] using
          (NumStability.u_le_gamma nfp (by omega : 0 < 1) hn1)
      have herr : fp.fl_sub b 0 - b = b * δ := by
        rw [hfl]
        ring
      simp only [p33RoundedResidual, p33RoundedSparseRowProduct,
        p33ExactResidual, p33ResidualErrorMajorant, Finset.univ_eq_empty,
        Finset.sum_empty, sub_zero, add_zero]
      rw [herr, abs_mul]
      calc
        |b| * |δ| ≤ |b| * fp.u :=
          mul_le_mul_of_nonneg_left hδ (abs_nonneg b)
        _ ≤ |b| * p33Gamma fp.u 1 :=
          mul_le_mul_of_nonneg_left hu_gamma (abs_nonneg b)
        _ = p33Gamma fp.u 1 * |b| := mul_comm _ _
  | succ k =>
      let A : Fin (k + 1) → Fin (k + 1) → ℝ := fun _ j ↦ a j
      let bv : Fin (k + 1) → ℝ := fun _ ↦ b
      have hres := NumStability.conventional_residual_error
        nfp (k + 1) A x bv hn hn1 (0 : Fin (k + 1))
      simpa [p33RoundedResidual, p33RoundedSparseRowProduct,
        p33ExactResidual, p33ResidualErrorMajorant, p33Gamma,
        NumStability.fl_residual, NumStability.fl_matVec,
        NumStability.fl_dotProduct, NumStability.gamma,
        nfp, p33ToFPModel, A, bv] using hres

end HighamBench
