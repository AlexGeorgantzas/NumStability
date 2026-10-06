import HighamBench.P33Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

open scoped BigOperators

/-- View the paper-local arithmetic model as the reusable library model. -/
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

lemma p33RoundedSparseRowProduct_eq_fl_dotProduct
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) :
    p33RoundedSparseRowProduct fp s a x =
      NumStability.fl_dotProduct (p33ToFPModel fp) s a x := by
  rfl

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  let nfp : NumStability.FPModel := p33ToFPModel fp
  have hvalidN : NumStability.gammaValid nfp (s + 1) := by
    simpa [NumStability.gammaValid, P33GammaValid, nfp, p33ToFPModel] using hvalid
  have hvalidS : NumStability.gammaValid nfp s :=
    NumStability.gammaValid_mono nfp (Nat.le_succ s) hvalidN
  have hvalid1 : NumStability.gammaValid nfp 1 :=
    NumStability.gammaValid_mono nfp (by omega) hvalidN
  obtain ⟨eta, heta, hdot⟩ :=
    NumStability.dotProduct_backward_error nfp s a x hvalidS
  have hrow :
      p33RoundedSparseRowProduct fp s a x =
        ∑ i : Fin s, a i * x i * (1 + eta i) := by
    rw [p33RoundedSparseRowProduct_eq_fl_dotProduct]
    exact hdot
  obtain ⟨delta, hdelta, hsub⟩ :=
    fp.model_sub b (p33RoundedSparseRowProduct fp s a x)
  have hdelta1 : |delta| ≤ NumStability.gamma nfp 1 := by
    exact le_trans hdelta
      (NumStability.u_le_gamma nfp Nat.one_pos hvalid1)
  have hcombine (i : Fin s) :
      ∃ theta : ℝ,
        |theta| ≤ NumStability.gamma nfp (s + 1) ∧
          (1 + eta i) * (1 + delta) = 1 + theta := by
    exact NumStability.gamma_mul nfp s 1 (eta i) delta
      (heta i) hdelta1 hvalidN
  let theta : Fin s → ℝ := fun i ↦ Classical.choose (hcombine i)
  have htheta (i : Fin s) :
      |theta i| ≤ NumStability.gamma nfp (s + 1) :=
    (Classical.choose_spec (hcombine i)).1
  have htheta_eq (i : Fin s) :
      (1 + eta i) * (1 + delta) = 1 + theta i :=
    (Classical.choose_spec (hcombine i)).2
  have hsums :
      (∑ i : Fin s, a i * x i * (1 + eta i)) * (1 + delta) =
        ∑ i : Fin s, a i * x i * (1 + theta i) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [mul_assoc, htheta_eq i]
  have hsumdiff :
      (∑ i : Fin s, a i * x i * (1 + theta i)) -
          ∑ i : Fin s, a i * x i =
        ∑ i : Fin s, a i * x i * theta i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have herr :
      p33RoundedResidual fp s a x b - p33ExactResidual s a x b =
        b * delta - ∑ i : Fin s, a i * x i * theta i := by
    calc
      p33RoundedResidual fp s a x b - p33ExactResidual s a x b =
          (b - ∑ i : Fin s, a i * x i * (1 + eta i)) * (1 + delta) -
            (b - ∑ i : Fin s, a i * x i) := by
              rw [p33RoundedResidual, p33ExactResidual, hsub, hrow]
      _ = b * delta -
          ((∑ i : Fin s, a i * x i * (1 + eta i)) * (1 + delta) -
            ∑ i : Fin s, a i * x i) := by ring
      _ = b * delta -
          ((∑ i : Fin s, a i * x i * (1 + theta i)) -
            ∑ i : Fin s, a i * x i) := by rw [hsums]
      _ = b * delta - ∑ i : Fin s, a i * x i * theta i := by rw [hsumdiff]
  have hdeltaN : |delta| ≤ NumStability.gamma nfp (s + 1) :=
    le_trans hdelta1
      (NumStability.gamma_mono nfp (by omega) hvalidN)
  have hgamma_nonneg : 0 ≤ NumStability.gamma nfp (s + 1) :=
    NumStability.gamma_nonneg nfp hvalidN
  rw [herr]
  calc
    |b * delta - ∑ i : Fin s, a i * x i * theta i| ≤
        |b * delta| + |∑ i : Fin s, a i * x i * theta i| := abs_sub _ _
    _ ≤ |b * delta| + ∑ i : Fin s, |a i * x i * theta i| :=
      add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
    _ = |b| * |delta| + ∑ i : Fin s, |a i| * |x i| * |theta i| := by
      simp only [abs_mul]
    _ ≤ |b| * NumStability.gamma nfp (s + 1) +
        ∑ i : Fin s, |a i| * |x i| * NumStability.gamma nfp (s + 1) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hdeltaN (abs_nonneg b)
      · apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_left (htheta i)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = NumStability.gamma nfp (s + 1) *
        (|b| + ∑ i : Fin s, |a i| * |x i|) := by
      rw [← Finset.sum_mul]
      ring
    _ = p33ResidualErrorMajorant fp s a x b := by
      simp [p33ResidualErrorMajorant, p33Gamma, NumStability.gamma,
        nfp, p33ToFPModel]

end HighamBench
