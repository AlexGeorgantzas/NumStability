import HighamBench.P29Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

noncomputable def p29AsFPModel (fp : P29FPModel) : NumStability.FPModel where
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
    refine ⟨0, ?_, by ring⟩
    simpa using fp.u_nonneg

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
  let fp' : NumStability.FPModel := p29AsFPModel fp
  let rounded : ℝ := p29RoundedMatMul fp L11 A12 i j
  let exact : ℝ := p29MatMul L11 A12 i j
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub (A22 i j) rounded
  have hvalid' : NumStability.gammaValid fp' r := by
    simpa [fp', p29AsFPModel, NumStability.gammaValid, P29GammaValid] using hvalid
  have hdot :
      |rounded - exact| ≤
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    simpa [rounded, exact, p29RoundedMatMul, p29MatMul,
      p29RoundedDotProduct, fp', p29AsFPModel, p29Gamma,
      NumStability.fl_dotProduct, NumStability.gamma] using
      (NumStability.dotProduct_error_bound fp' r (L11 i)
        (fun k => A12 k j) hvalid')
  have hid :
      p29RoundedSchur fp A22 L11 A12 i j -
          p29ExactSchur A22 L11 A12 i j =
        (A22 i j - rounded) * δ + (exact - rounded) := by
    simp only [p29RoundedSchur, p29ExactSchur]
    rw [hsub]
    ring
  rw [hid]
  calc
    |(A22 i j - rounded) * δ + (exact - rounded)| ≤
        |(A22 i j - rounded) * δ| + |exact - rounded| := abs_add_le _ _
    _ = |A22 i j - rounded| * |δ| + |rounded - exact| := by
      rw [abs_mul, abs_sub_comm exact rounded]
    _ ≤ |A22 i j - rounded| * fp.u +
          p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
      gcongr
    _ = p29SchurErrorMajorant fp A22 L11 A12 i j := by
      simp [p29SchurErrorMajorant, rounded]
      ring

end HighamBench
