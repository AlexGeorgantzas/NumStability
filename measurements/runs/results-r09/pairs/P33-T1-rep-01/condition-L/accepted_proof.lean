import HighamBench.P33Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

open scoped BigOperators

/-- Regard the paper-local arithmetic model as a `NumStability` model. -/
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
    intro y hy
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

lemma p33RoundedSparseRowProduct_eq_fl_dotProduct
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) :
    p33RoundedSparseRowProduct fp s a x =
      NumStability.fl_dotProduct (p33AsFPModel fp) s a x := by
  rfl

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  let F : NumStability.FPModel := p33AsFPModel fp
  have hvalidF : NumStability.gammaValid F (s + 1) := by
    simpa [F, p33AsFPModel, NumStability.gammaValid, P33GammaValid] using hvalid
  have hvalidS : NumStability.gammaValid F s :=
    NumStability.gammaValid_mono F (Nat.le_succ s) hvalidF
  have hvalidOne : NumStability.gammaValid F 1 :=
    NumStability.gammaValid_mono F (Nat.succ_le_succ (Nat.zero_le s)) hvalidF
  obtain ⟨eta, heta, hdot⟩ :=
    NumStability.dotProduct_backward_error F s a x hvalidS
  obtain ⟨delta, hdelta, hsub⟩ :=
    fp.model_sub b (p33RoundedSparseRowProduct fp s a x)
  have hdeltaOne : |delta| ≤ NumStability.gamma F 1 := by
    exact le_trans hdelta
      (NumStability.u_le_gamma F Nat.one_pos hvalidOne)
  have hvalidAdd : NumStability.gammaValid F (s + 1) := by
    simpa only [Nat.add_comm] using hvalidF
  let theta : Fin s → ℝ := fun i ↦
    Classical.choose
      (NumStability.gamma_mul F s 1 (eta i) delta
        (heta i) hdeltaOne hvalidAdd)
  have htheta : ∀ i, |theta i| ≤ NumStability.gamma F (s + 1) := by
    intro i
    exact (Classical.choose_spec
      (NumStability.gamma_mul F s 1 (eta i) delta
        (heta i) hdeltaOne hvalidAdd)).1
  have hthetaEq : ∀ i, (1 + eta i) * (1 + delta) = 1 + theta i := by
    intro i
    exact (Classical.choose_spec
        (NumStability.gamma_mul F s 1 (eta i) delta
          (heta i) hdeltaOne hvalidAdd)).2
  have hdeltaFinal : |delta| ≤ NumStability.gamma F (s + 1) :=
    le_trans hdeltaOne
      (NumStability.gamma_mono F
        (Nat.succ_le_succ (Nat.zero_le s)) hvalidF)
  have hrounded : p33RoundedSparseRowProduct fp s a x =
      ∑ i : Fin s, a i * x i * (1 + eta i) := by
    rw [p33RoundedSparseRowProduct_eq_fl_dotProduct]
    exact hdot
  have herr :
      p33RoundedResidual fp s a x b - p33ExactResidual s a x b =
        b * delta - ∑ i : Fin s, a i * x i * theta i := by
    unfold p33RoundedResidual p33ExactResidual
    rw [hsub, hrounded]
    rw [sub_mul, Finset.sum_mul]
    have hsum :
        ∑ i : Fin s, a i * x i * (1 + eta i) * (1 + delta) =
          ∑ i : Fin s, a i * x i * (1 + theta i) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        a i * x i * (1 + eta i) * (1 + delta) =
            a i * x i * ((1 + eta i) * (1 + delta)) := by ring
        _ = a i * x i * (1 + theta i) := by rw [hthetaEq i]
    have hsumExpand :
        ∑ i : Fin s, a i * x i * (1 + theta i) =
          (∑ i : Fin s, a i * x i) +
            ∑ i : Fin s, a i * x i * theta i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum]
    rw [hsumExpand]
    ring
  rw [herr]
  calc
    |b * delta - ∑ i : Fin s, a i * x i * theta i|
        ≤ |b * delta| + |∑ i : Fin s, a i * x i * theta i| := abs_sub _ _
    _ ≤ |b * delta| + ∑ i : Fin s, |a i * x i * theta i| :=
      add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
    _ = |b| * |delta| + ∑ i : Fin s, |a i| * |x i| * |theta i| := by
      simp only [abs_mul]
    _ ≤ |b| * NumStability.gamma F (s + 1) +
          ∑ i : Fin s, |a i| * |x i| * NumStability.gamma F (s + 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          hdeltaFinal
          (abs_nonneg b))
        (Finset.sum_le_sum fun i hi ↦
          mul_le_mul_of_nonneg_left (htheta i)
            (mul_nonneg (abs_nonneg (a i)) (abs_nonneg (x i))))
    _ = NumStability.gamma F (s + 1) *
          (|b| + ∑ i : Fin s, |a i| * |x i|) := by
      rw [← Finset.sum_mul]
      ring
    _ = p33ResidualErrorMajorant fp s a x b := by
      rfl

end HighamBench
