import HighamBench.P33Definitions
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core

namespace HighamBench

/-- The paper-local arithmetic model, viewed as the library's standard model. -/
noncomputable def p33StandardModel (fp : P33FPModel) : NumStability.FPModel where
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
    intro y hy
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
  let nfp := p33StandardModel fp
  have hvalid' : NumStability.gammaValid nfp (s + 1) := by
    simpa [nfp, p33StandardModel, NumStability.gammaValid, P33GammaValid] using hvalid
  cases s with
  | zero =>
      obtain ⟨delta, hdelta, hround⟩ := fp.model_sub b 0
      have hgamma : fp.u ≤ NumStability.gamma nfp 1 := by
        exact NumStability.u_le_gamma nfp (by omega)
          (NumStability.gammaValid_mono nfp (by omega) hvalid')
      have hmul : |b * delta| ≤ NumStability.gamma nfp 1 * |b| := by
        calc
          |b * delta| = |b| * |delta| := abs_mul _ _
          _ ≤ |b| * fp.u := mul_le_mul_of_nonneg_left hdelta (abs_nonneg b)
          _ ≤ |b| * NumStability.gamma nfp 1 :=
            mul_le_mul_of_nonneg_left hgamma (abs_nonneg b)
          _ = NumStability.gamma nfp 1 * |b| := by ring
      simp only [p33RoundedResidual, p33RoundedSparseRowProduct,
        p33ExactResidual, p33ResidualErrorMajorant]
      simp
      rw [hround]
      have heq : (b - 0) * (1 + delta) - b = b * delta := by ring
      rw [heq]
      simpa [p33Gamma, NumStability.gamma, nfp, p33StandardModel] using hmul
  | succ k =>
      have hkvalid : NumStability.gammaValid nfp (k + 1) :=
        NumStability.gammaValid_mono nfp (by omega) hvalid'
      let A : Fin (k + 1) → Fin (k + 1) → ℝ := fun _ j ↦ a j
      let bv : Fin (k + 1) → ℝ := fun _ ↦ b
      have h := NumStability.conventional_residual_error nfp (k + 1) A x bv
        hkvalid hvalid' (0 : Fin (k + 1))
      simpa [NumStability.fl_residual, NumStability.fl_matVec,
        NumStability.fl_dotProduct, p33RoundedResidual,
        p33RoundedSparseRowProduct, p33ExactResidual,
        p33ResidualErrorMajorant, p33Gamma, NumStability.gamma,
        nfp, p33StandardModel, A, bv] using h

end HighamBench
