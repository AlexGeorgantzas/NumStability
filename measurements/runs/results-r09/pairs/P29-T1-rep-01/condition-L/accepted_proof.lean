import HighamBench.P29Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

noncomputable def p29FPModelToNumStability
    (fp : P29FPModel) : NumStability.FPModel where
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
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

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
  let nfp := p29FPModelToNumStability fp
  have hnvalid : NumStability.gammaValid nfp r := by
    simpa [NumStability.gammaValid, nfp, p29FPModelToNumStability,
      P29GammaValid] using hvalid
  have hdot :=
    NumStability.dotProduct_error_bound nfp r (L11 i) (fun k => A12 k j) hnvalid
  have hdot' :
      |p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j) -
          ∑ k : Fin r, L11 i k * A12 k j| ≤
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    simpa [nfp, p29FPModelToNumStability, p29RoundedDotProduct,
      NumStability.fl_dotProduct, p29Gamma, NumStability.gamma] using hdot
  obtain ⟨δ, hδ, hsub⟩ :=
    fp.model_sub (A22 i j)
      (p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j))
  unfold p29RoundedSchur p29ExactSchur p29RoundedMatMul p29MatMul
  rw [hsub]
  unfold p29SchurErrorMajorant
  let d := p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j)
  let e := ∑ k : Fin r, L11 i k * A12 k j
  have hlocal : |(A22 i j - d) * δ| ≤ fp.u * |A22 i j - d| := by
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_left hδ (abs_nonneg (A22 i j - d))
    nlinarith
  have hdot'' : |e - d| ≤
      p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    simpa [d, e, abs_sub_comm] using hdot'
  calc
    |(A22 i j - d) * (1 + δ) - (A22 i j - e)| =
        |(A22 i j - d) * δ + (e - d)| := by
      congr 1
      ring
    _ ≤ |(A22 i j - d) * δ| + |e - d| := abs_add_le _ _
    _ ≤ fp.u * |A22 i j - d| +
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| :=
      add_le_add hlocal hdot''

end HighamBench
