import HighamBench.P29Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

noncomputable def P29FPModel.toNumStability (fp : P29FPModel) :
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
    intro x hx
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

lemma p29RoundedDotProduct_eq_library (fp : P29FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p29RoundedDotProduct fp n x y =
      NumStability.fl_dotProduct fp.toNumStability n x y := by
  rfl

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
  let qhat := p29RoundedMatMul fp L11 A12 i j
  let q := p29MatMul L11 A12 i j
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub (A22 i j) qhat
  have hdot :
      |qhat - q| ≤
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    have hlib := NumStability.dotProduct_error_bound fp.toNumStability r
      (L11 i) (fun k => A12 k j) (by simpa [NumStability.gammaValid] using hvalid)
    simpa [qhat, q, p29RoundedMatMul, p29MatMul,
      p29RoundedDotProduct_eq_library, p29Gamma, NumStability.gamma] using hlib
  have hdecomp :
      fp.fl_sub (A22 i j) qhat - (A22 i j - q) =
        (A22 i j - qhat) * δ + (q - qhat) := by
    rw [hsub]
    ring
  change |fp.fl_sub (A22 i j) qhat - (A22 i j - q)| ≤
    fp.u * |A22 i j - qhat| +
      p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j|
  rw [hdecomp]
  calc
    |(A22 i j - qhat) * δ + (q - qhat)| ≤
        |(A22 i j - qhat) * δ| + |q - qhat| := abs_add_le _ _
    _ = |A22 i j - qhat| * |δ| + |q - qhat| := by rw [abs_mul]
    _ ≤ fp.u * |A22 i j - qhat| +
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
      have hfirst : |A22 i j - qhat| * |δ| ≤
          fp.u * |A22 i j - qhat| := by
        nlinarith [abs_nonneg (A22 i j - qhat)]
      have hsecond : |q - qhat| ≤
          p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
        simpa [abs_sub_comm] using hdot
      exact add_le_add hfirst hsecond
    _ = p29SchurErrorMajorant fp A22 L11 A12 i j := by
      simp only [p29SchurErrorMajorant, qhat]

end HighamBench
