import HighamBench.P29Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

noncomputable def p29ToFPModel (fp : P29FPModel) : NumStability.FPModel where
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
    intro x hx
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

/-- P29-T1: the first-step Schur-complement error calculation in Appendix B. -/
theorem p29_t1_first_schur_error
    (fp : P29FPModel) (m r : ℕ)
    (A22 : P29Matrix m m) (L11 : P29Matrix m r)
    (A12 : P29Matrix r m)
    (hvalid : P29GammaValid fp.u r) :
    ∀ i j,
      |p29RoundedSchur fp A22 L11 A12 i j -
          p29ExactSchur A22 L11 A12 i j| ≤
        p29SchurErrorMajorant fp A22 L11 A12 i j := by
  -- PROOF_START P29-T1-H001
  intro i j
  have hgamma : NumStability.gammaValid (p29ToFPModel fp) r := by
    simpa [NumStability.gammaValid, P29GammaValid, p29ToFPModel] using hvalid
  have hdot := NumStability.dotProduct_error_bound
    (p29ToFPModel fp) r (L11 i) (fun k => A12 k j) hgamma
  have hdot' :
      |p29RoundedMatMul fp L11 A12 i j - p29MatMul L11 A12 i j| ≤
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    simpa [p29RoundedMatMul, p29RoundedDotProduct, p29MatMul,
      p29Gamma, NumStability.fl_dotProduct, NumStability.gamma,
      p29ToFPModel] using hdot
  obtain ⟨δ, hδ, hsub⟩ :=
    fp.model_sub (A22 i j) (p29RoundedMatMul fp L11 A12 i j)
  unfold p29RoundedSchur p29ExactSchur p29SchurErrorMajorant
  calc
    |fp.fl_sub (A22 i j) (p29RoundedMatMul fp L11 A12 i j) -
          (A22 i j - p29MatMul L11 A12 i j)| =
        |δ * (A22 i j - p29RoundedMatMul fp L11 A12 i j) +
          (p29MatMul L11 A12 i j - p29RoundedMatMul fp L11 A12 i j)| := by
            rw [hsub]
            congr 1
            ring
    _ ≤ |δ * (A22 i j - p29RoundedMatMul fp L11 A12 i j)| +
          |p29MatMul L11 A12 i j - p29RoundedMatMul fp L11 A12 i j| :=
        abs_add_le _ _
    _ = |δ| * |A22 i j - p29RoundedMatMul fp L11 A12 i j| +
          |p29RoundedMatMul fp L11 A12 i j - p29MatMul L11 A12 i j| := by
        rw [abs_mul, abs_sub_comm (p29MatMul L11 A12 i j)]
    _ ≤ fp.u * |A22 i j - p29RoundedMatMul fp L11 A12 i j| +
          p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hδ (abs_nonneg _)) hdot'

end HighamBench
