import HighamBench.P29Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

/-- View the paper-local arithmetic model as the library model.  Square root
is irrelevant here, so it is interpreted exactly. -/
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
  let q := p29RoundedMatMul fp L11 A12 i j
  let s := p29MatMul L11 A12 i j
  have hgamma : NumStability.gammaValid (p29AsFPModel fp) r := by
    simpa [NumStability.gammaValid, p29AsFPModel] using hvalid
  have hdot0 :=
    NumStability.dotProduct_error_bound (p29AsFPModel fp) r
      (L11 i) (fun k => A12 k j) hgamma
  have hdot :
      |q - s| ≤
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    simpa [q, s, p29RoundedMatMul, p29RoundedDotProduct, p29MatMul,
      p29Gamma, p29AsFPModel, NumStability.fl_dotProduct,
      NumStability.gamma] using hdot0
  obtain ⟨δ, hδ, hround⟩ := fp.model_sub (A22 i j) q
  change
    |fp.fl_sub (A22 i j) q - (A22 i j - s)| ≤
      fp.u * |A22 i j - q| +
        p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j|
  rw [hround]
  have hrearrange :
      (A22 i j - q) * (1 + δ) - (A22 i j - s) =
        (A22 i j - q) * δ + (s - q) := by
    ring
  rw [hrearrange]
  calc
    |(A22 i j - q) * δ + (s - q)| ≤
        |(A22 i j - q) * δ| + |s - q| := by
      rw [abs_le]
      constructor <;>
        linarith [le_abs_self ((A22 i j - q) * δ), le_abs_self (s - q),
          neg_abs_le ((A22 i j - q) * δ), neg_abs_le (s - q)]
    _ = |A22 i j - q| * |δ| + |s - q| := by rw [abs_mul]
    _ ≤ |A22 i j - q| * fp.u +
          p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hδ (abs_nonneg _))
        (by simpa [abs_sub_comm] using hdot)
    _ = fp.u * |A22 i j - q| +
          p29Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
      ring

end HighamBench
