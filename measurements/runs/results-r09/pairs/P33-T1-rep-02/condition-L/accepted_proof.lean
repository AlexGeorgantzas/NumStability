import HighamBench.P33Definitions
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core

namespace HighamBench

open scoped BigOperators

/-- View the paper-local arithmetic model as the library's standard model. -/
noncomputable def p33FPModel (fp : P33FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  cases s with
  | zero =>
      obtain ⟨delta, hdelta, hfl⟩ := fp.model_sub b 0
      rw [p33RoundedResidual, p33RoundedSparseRowProduct, hfl]
      simp only [p33ExactResidual, Finset.univ_eq_empty, Finset.sum_empty,
        sub_zero, p33ResidualErrorMajorant]
      have hu_gamma : fp.u ≤ p33Gamma fp.u (0 + 1) := by
        have h := NumStability.u_le_gamma (p33FPModel fp) (k := 1)
          Nat.one_pos hvalid
        simpa [p33FPModel, p33Gamma, NumStability.gamma] using h
      calc
        |b * (1 + delta) - b| = |b| * |delta| := by rw [show b * (1 + delta) - b = b * delta by ring, abs_mul]
        _ ≤ |b| * fp.u := mul_le_mul_of_nonneg_left hdelta (abs_nonneg b)
        _ ≤ |b| * p33Gamma fp.u (0 + 1) :=
          mul_le_mul_of_nonneg_left hu_gamma (abs_nonneg b)
        _ = p33Gamma fp.u (0 + 1) * (|b| + 0) := by ring
  | succ n =>
      let A : Fin (n + 1) → Fin (n + 1) → ℝ := fun _ j ↦ a j
      let bv : Fin (n + 1) → ℝ := fun _ ↦ b
      have hn : NumStability.gammaValid (p33FPModel fp) (n + 1) :=
        NumStability.gammaValid_mono (p33FPModel fp) (Nat.le_succ (n + 1)) hvalid
      have h := NumStability.conventional_residual_error
        (p33FPModel fp) (n + 1) A x bv hn hvalid (0 : Fin (n + 1))
      simpa [A, bv, p33FPModel, NumStability.fl_residual,
        NumStability.fl_matVec, NumStability.fl_dotProduct,
        p33RoundedResidual, p33RoundedSparseRowProduct,
        p33ExactResidual, p33ResidualErrorMajorant,
        p33Gamma, NumStability.gamma] using h

end HighamBench
