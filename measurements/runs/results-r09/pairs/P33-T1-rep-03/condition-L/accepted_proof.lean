import HighamBench.P33Definitions
import NumStability.Algorithms.DotProduct

namespace HighamBench

open scoped BigOperators

noncomputable def p33FPModelToNumStability (fp : P33FPModel) :
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
    intro y _hy
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

lemma p33RoundedSparseRowProduct_eq_fl_dotProduct
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) :
    p33RoundedSparseRowProduct fp s a x =
      NumStability.fl_dotProduct (p33FPModelToNumStability fp) s a x := by
  cases s <;> rfl

/-- P33-T1: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p33_t1_sparse_residual_error
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P33GammaValid fp.u (s + 1)) :
    |p33RoundedResidual fp s a x b - p33ExactResidual s a x b| ≤
      p33ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P33-T1-H001
  let nfp := p33FPModelToNumStability fp
  have hvalid' : NumStability.gammaValid nfp (s + 1) := by
    exact hvalid
  have hvalid_s : NumStability.gammaValid nfp s :=
    NumStability.gammaValid_mono nfp (Nat.le_succ s) hvalid'
  have hvalid_one : NumStability.gammaValid nfp 1 :=
    NumStability.gammaValid_mono nfp (by omega) hvalid'
  have hdot := NumStability.dotProduct_error_bound nfp s a x hvalid_s
  have hu_gamma_one : nfp.u ≤ NumStability.gamma nfp 1 :=
    NumStability.u_le_gamma nfp Nat.one_pos hvalid_one
  have hgamma_s_nonneg : 0 ≤ NumStability.gamma nfp s :=
    NumStability.gamma_nonneg nfp hvalid_s
  have hcoeff :
      nfp.u + NumStability.gamma nfp s +
          nfp.u * NumStability.gamma nfp s ≤
        NumStability.gamma nfp (s + 1) := by
    obtain ⟨theta, htheta, htheta_eq⟩ :=
      NumStability.gamma_mul nfp s 1 (NumStability.gamma nfp s) nfp.u
        (abs_of_nonneg hgamma_s_nonneg).le
        (by simpa [abs_of_nonneg nfp.u_nonneg] using hu_gamma_one) hvalid'
    have htheta_val :
        theta = NumStability.gamma nfp s + nfp.u +
          NumStability.gamma nfp s * nfp.u := by
      nlinarith [htheta_eq]
    rw [htheta_val] at htheta
    rw [abs_of_nonneg] at htheta
    · nlinarith
    · exact add_nonneg (add_nonneg hgamma_s_nonneg nfp.u_nonneg)
        (mul_nonneg hgamma_s_nonneg nfp.u_nonneg)
  obtain ⟨delta, hdelta, hsub⟩ :=
    fp.model_sub b (p33RoundedSparseRowProduct fp s a x)
  rw [p33RoundedSparseRowProduct_eq_fl_dotProduct] at hsub
  rw [p33RoundedResidual, p33ExactResidual, p33ResidualErrorMajorant,
    p33RoundedSparseRowProduct_eq_fl_dotProduct]
  change
    |fp.fl_sub b (NumStability.fl_dotProduct nfp s a x) -
        (b - ∑ j : Fin s, a j * x j)| ≤
      NumStability.gamma nfp (s + 1) *
        (|b| + ∑ j : Fin s, |a j| * |x j|)
  rw [hsub]
  let exactDot := ∑ j : Fin s, a j * x j
  let dotError := NumStability.fl_dotProduct nfp s a x - exactDot
  let absSum := ∑ j : Fin s, |a j| * |x j|
  have hdot' : |dotError| ≤ NumStability.gamma nfp s * absSum := by
    simpa [dotError, exactDot, absSum] using hdot
  have hexactDot : |exactDot| ≤ absSum := by
    calc
      |exactDot| ≤ ∑ j : Fin s, |a j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = absSum := by simp [absSum, abs_mul]
  have hgamma_big_nonneg : 0 ≤ NumStability.gamma nfp (s + 1) :=
    NumStability.gamma_nonneg nfp hvalid'
  have habsSum_nonneg : 0 ≤ absSum := by positivity
  have hb_nonneg : 0 ≤ |b| := abs_nonneg b
  have hdelta_nonneg : 0 ≤ 1 + |delta| := by positivity
  have hmain :
      |(b - NumStability.fl_dotProduct nfp s a x) * (1 + delta) -
          (b - exactDot)| ≤
        nfp.u * |b| +
          (nfp.u + NumStability.gamma nfp s +
            nfp.u * NumStability.gamma nfp s) * absSum := by
    have hrewrite :
        (b - NumStability.fl_dotProduct nfp s a x) * (1 + delta) -
            (b - exactDot) =
          delta * (b - exactDot) - (1 + delta) * dotError := by
      dsimp [dotError, exactDot]
      ring
    rw [hrewrite]
    calc
      |delta * (b - exactDot) - (1 + delta) * dotError|
          ≤ |delta * (b - exactDot)| + |(1 + delta) * dotError| :=
            abs_sub _ _
      _ = |delta| * |b - exactDot| + |1 + delta| * |dotError| := by
            rw [abs_mul, abs_mul]
      _ ≤ |delta| * (|b| + |exactDot|) +
            (1 + |delta|) * |dotError| := by
          gcongr
          · exact abs_sub b exactDot
          · exact (abs_add_le 1 delta).trans_eq (by simp)
      _ ≤ nfp.u * (|b| + absSum) +
            (1 + nfp.u) * (NumStability.gamma nfp s * absSum) := by
          apply add_le_add
          · exact mul_le_mul hdelta (add_le_add le_rfl hexactDot)
              (by positivity) nfp.u_nonneg
          · exact mul_le_mul (add_le_add le_rfl hdelta) hdot'
              (abs_nonneg dotError) (add_nonneg zero_le_one nfp.u_nonneg)
      _ = nfp.u * |b| +
            (nfp.u + NumStability.gamma nfp s +
              nfp.u * NumStability.gamma nfp s) * absSum := by ring
  calc
    |(b - NumStability.fl_dotProduct nfp s a x) * (1 + delta) -
        (b - ∑ j : Fin s, a j * x j)|
        ≤ nfp.u * |b| +
          (nfp.u + NumStability.gamma nfp s +
            nfp.u * NumStability.gamma nfp s) * absSum := by
          simpa [exactDot] using hmain
    _ ≤ NumStability.gamma nfp (s + 1) * |b| +
          NumStability.gamma nfp (s + 1) * absSum := by
        gcongr
        · exact le_trans hu_gamma_one
            (NumStability.gamma_mono nfp (by omega) hvalid')
    _ = NumStability.gamma nfp (s + 1) *
          (|b| + ∑ j : Fin s, |a j| * |x j|) := by
        simp [absSum, mul_add]

end HighamBench
