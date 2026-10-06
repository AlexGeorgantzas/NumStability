import HighamBench.P33Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

open scoped BigOperators

/-- View the paper-local arithmetic model as the library's standard model. -/
noncomputable def p33AsFPModel (fp : P33FPModel) : NumStability.FPModel where
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
  let f : NumStability.FPModel := p33AsFPModel fp
  let d : ℝ := p33RoundedSparseRowProduct fp s a x
  let q : ℝ := ∑ j : Fin s, a j * x j
  let S : ℝ := ∑ j : Fin s, |a j| * |x j|

  have hs1 : NumStability.gammaValid f (s + 1) := by
    simpa [f, p33AsFPModel, NumStability.gammaValid, P33GammaValid] using hvalid
  have hs : NumStability.gammaValid f s :=
    NumStability.gammaValid_mono f (Nat.le_succ s) hs1
  have hdot :
      |d - q| ≤ NumStability.gamma f s * S := by
    simpa [d, q, S, f, p33AsFPModel, p33RoundedSparseRowProduct,
      NumStability.fl_dotProduct] using
      (NumStability.dotProduct_error_bound f s a x hs)
  have hS : 0 ≤ S := by
    exact Finset.sum_nonneg (fun j _ ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hq : |q| ≤ S := by
    calc
      |q| ≤ ∑ j : Fin s, |a j * x j| := by
        simpa [q] using
          (Finset.abs_sum_le_sum_abs (f := fun j : Fin s ↦ a j * x j) Finset.univ)
      _ = S := by simp [S, abs_mul]
  have hd : |d| ≤ (1 + NumStability.gamma f s) * S := by
    calc
      |d| = |q + (d - q)| := by congr 1 <;> ring
      _ ≤ |q| + |d - q| := abs_add_le _ _
      _ ≤ S + NumStability.gamma f s * S := add_le_add hq hdot
      _ = (1 + NumStability.gamma f s) * S := by ring
  have hbd :
      |b - d| ≤ |b| + (1 + NumStability.gamma f s) * S := by
    calc
      |b - d| = |b + -d| := by congr 1 <;> ring
      _ ≤ |b| + |-d| := abs_add_le _ _
      _ = |b| + |d| := by rw [abs_neg]
      _ ≤ |b| + (1 + NumStability.gamma f s) * S := add_le_add le_rfl hd

  obtain ⟨δ, hδ, hfl⟩ := fp.model_sub b d
  have hlocal :
      |(b - d) * (1 + δ) - (b - q)| ≤
        fp.u * (|b| + (1 + NumStability.gamma f s) * S) +
          NumStability.gamma f s * S := by
    have hround :
        |(b - d) * δ| ≤
          fp.u * (|b| + (1 + NumStability.gamma f s) * S) := by
      calc
        |(b - d) * δ| = |δ| * |b - d| := by rw [abs_mul, mul_comm]
        _ ≤ fp.u * |b - d| :=
          mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
        _ ≤ fp.u * (|b| + (1 + NumStability.gamma f s) * S) :=
          mul_le_mul_of_nonneg_left hbd fp.u_nonneg
    calc
      |(b - d) * (1 + δ) - (b - q)| =
          |(q - d) + (b - d) * δ| := by congr 1 <;> ring
      _ ≤ |q - d| + |(b - d) * δ| := abs_add_le _ _
      _ = |d - q| + |(b - d) * δ| := by rw [abs_sub_comm]
      _ ≤ NumStability.gamma f s * S +
          fp.u * (|b| + (1 + NumStability.gamma f s) * S) :=
        add_le_add hdot hround
      _ = fp.u * (|b| + (1 + NumStability.gamma f s) * S) +
          NumStability.gamma f s * S := by ring

  have hgammaS : 0 ≤ NumStability.gamma f s :=
    NumStability.gamma_nonneg f hs
  have hvalid1 : NumStability.gammaValid f 1 :=
    NumStability.gammaValid_mono f (by omega : 1 ≤ s + 1) hs1
  have hu_le_gamma1 : fp.u ≤ NumStability.gamma f 1 := by
    simpa [f, p33AsFPModel] using
      (NumStability.u_le_gamma f (by omega : 0 < 1) hvalid1)
  have hgamma_sum :
      NumStability.gamma f 1 + NumStability.gamma f s +
          NumStability.gamma f 1 * NumStability.gamma f s ≤
        NumStability.gamma f (s + 1) := by
    have h := NumStability.gamma_sum_le f 1 s (by
      simpa [Nat.add_comm] using hs1)
    simpa [Nat.add_comm] using h
  have hcoeff :
      fp.u + NumStability.gamma f s + fp.u * NumStability.gamma f s ≤
        NumStability.gamma f (s + 1) := by
    have hprod : fp.u * NumStability.gamma f s ≤
        NumStability.gamma f 1 * NumStability.gamma f s :=
      mul_le_mul_of_nonneg_right hu_le_gamma1 hgammaS
    linarith
  have hu_le_final : fp.u ≤ NumStability.gamma f (s + 1) := by
    simpa [f, p33AsFPModel] using
      (NumStability.u_le_gamma f (Nat.succ_pos s) hs1)
  have hfinal :
      |(b - d) * (1 + δ) - (b - q)| ≤
        NumStability.gamma f (s + 1) * (|b| + S) := by
    calc
      |(b - d) * (1 + δ) - (b - q)| ≤
          fp.u * (|b| + (1 + NumStability.gamma f s) * S) +
            NumStability.gamma f s * S := hlocal
      _ = fp.u * |b| +
          (fp.u + NumStability.gamma f s +
            fp.u * NumStability.gamma f s) * S := by ring
      _ ≤ NumStability.gamma f (s + 1) * |b| +
          NumStability.gamma f (s + 1) * S := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hu_le_final (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hcoeff hS)
      _ = NumStability.gamma f (s + 1) * (|b| + S) := by ring

  change |fp.fl_sub b d - (b - q)| ≤
    p33Gamma fp.u (s + 1) * (|b| + S)
  rw [hfl]
  simpa [p33Gamma, f, p33AsFPModel, NumStability.gamma] using hfinal

end HighamBench
