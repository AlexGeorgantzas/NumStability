import HighamBench.P29Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

/- `P29FPModel` is the fragment of NumStability's general floating-point
model needed here.  Supply exact square root for the one extra operation in
the general model. -/
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
  let d := p29RoundedDotProduct fp r (L11 i) (fun k => A12 k j)
  let e := ∑ k : Fin r, L11 i k * A12 k j
  let b := ∑ k : Fin r, |L11 i k| * |A12 k j|
  have hv : NumStability.gammaValid (p29ToFPModel fp) r := by
    simpa [NumStability.gammaValid, P29GammaValid, p29ToFPModel] using hvalid
  have hd : |d - e| ≤ p29Gamma fp.u r * b := by
    simpa [d, e, b, p29RoundedDotProduct, p29Gamma, p29ToFPModel,
      NumStability.fl_dotProduct, NumStability.gamma] using
      (NumStability.dotProduct_error_bound (p29ToFPModel fp) r
        (L11 i) (fun k => A12 k j) hv)
  obtain ⟨δ, hδ, hs⟩ := fp.model_sub (A22 i j) d
  have hre :
      p29RoundedSchur fp A22 L11 A12 i j -
          p29ExactSchur A22 L11 A12 i j =
        (A22 i j - d) * δ + (e - d) := by
    simp only [p29RoundedSchur, p29RoundedMatMul, p29ExactSchur, p29MatMul]
    change fp.fl_sub (A22 i j) d - (A22 i j - e) = _
    rw [hs]
    ring
  rw [hre]
  unfold p29SchurErrorMajorant
  change |(A22 i j - d) * δ + (e - d)| ≤ fp.u * |A22 i j - d| + p29Gamma fp.u r * b
  calc
    |(A22 i j - d) * δ + (e - d)| ≤
        |(A22 i j - d) * δ| + |e - d| := abs_add_le _ _
    _ = |A22 i j - d| * |δ| + |d - e| := by
      rw [abs_mul, abs_sub_comm e d]
    _ ≤ |A22 i j - d| * fp.u + p29Gamma fp.u r * b := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hδ (abs_nonneg _)) hd
    _ = fp.u * |A22 i j - d| + p29Gamma fp.u r * b := by ring

end HighamBench
