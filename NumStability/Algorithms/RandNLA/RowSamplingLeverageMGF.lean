-- Algorithms/RandNLA/RowSamplingLeverageMGF.lean
--
-- One-step matrix-CGF prerequisites for Algorithm 2 leverage-score sampling.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import NumStability.Algorithms.RandNLA.RowSamplingLeverage
import NumStability.Algorithms.RandNLA.RowSamplingTraceMGF
import NumStability.Analysis.MatrixConcentration

namespace NumStability

open scoped BigOperators ComplexOrder

/-!
## Centered leverage covariance log-CGF

This file instantiates the repository's generic centered C-star Bernstein
log-CGF theorem with Algorithm 2's one-step leverage covariance observable

`X_i = rowOuterGramSample U i - I`.

It is a source-sharp concentration prerequisite: it proves the one-step
matrix-CGF bound needed before applying the row-trace product-law MGF adapter
and the final rank-one tail conversion.
-/

/-- Row outer-product estimators are symmetric finite real matrices. -/
theorem rowOuterGramSample_symmetric {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) :
    IsSymmetricFiniteMatrix (fun j k : Fin n => rowOuterGramSample U i j k) := by
  intro j k
  unfold rowOuterGramSample
  ring

/-- The centered one-step row outer-product estimator `X_i - I` is symmetric. -/
theorem rowOuterGramSample_centered_symmetric {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) :
    IsSymmetricFiniteMatrix
      (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k) := by
  intro j k
  have hrow := rowOuterGramSample_symmetric U i j k
  change rowOuterGramSample U i j k = rowOuterGramSample U i k j at hrow
  change
    rowOuterGramSample U i j k - finiteIdMatrix j k =
      rowOuterGramSample U i k j - finiteIdMatrix k j
  rw [hrow]
  by_cases h : j = k
  · subst h
    simp [finiteIdMatrix]
  · have hk : k ≠ j := Ne.symm h
    simp [finiteIdMatrix, h, hk]

/-- C-star self-adjointness of the centered one-step leverage covariance
observable. -/
theorem leverage_rowOuterGramSample_centered_cstar_selfAdjoint {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) :
    IsSelfAdjoint
      (finiteComplexCStarMatrix
        (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k)) := by
  exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
    (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k)
    (rowOuterGramSample_centered_symmetric U i)

/-- Under the leverage-score one-sample law, the centered covariance
observable has mean zero. -/
theorem leverage_rowOuterGramSample_centered_expectationCStarMatrix_eq_zero
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) :
    (rowSqNormSampleProbability U
        (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)).expectationCStarMatrix
      (fun i : RowSample m =>
        finiteComplexCStarMatrix
          (fun j k : Fin n =>
            rowOuterGramSample U i j k - finiteIdMatrix j k)) = 0 := by
  classical
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  rw [FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix]
  ext j k
  change
    ((rowSqNormSampleProbability U hden).expectationReal
        (fun i : RowSample m =>
          rowOuterGramSample U i j k - finiteIdMatrix j k) : ℂ) = 0
  have hmean :
      ∑ i : Fin m, rowSqNormProb U i * rowOuterGramSample U i j k =
        finiteIdMatrix j k := by
    simpa [leverageScoreProb] using
      leverage_rowOuterGramSample_mean_eq_id U hU hn j k
  have hprob :
      ∑ i : Fin m, rowSqNormProb U i = 1 := by
    simpa [leverageScoreProb] using
      leverageScoreProb_sum_eq_one U hU hn
  have hreal :
      (rowSqNormSampleProbability U hden).expectationReal
        (fun i : RowSample m =>
          rowOuterGramSample U i j k - finiteIdMatrix j k) = 0 := by
    unfold FiniteProbability.expectationReal rowSqNormSampleProbability
    calc
      ∑ i : Fin m,
          rowSqNormProb U i *
            (rowOuterGramSample U i j k - finiteIdMatrix j k)
          =
        ∑ i : Fin m,
          (rowSqNormProb U i * rowOuterGramSample U i j k -
            rowSqNormProb U i * finiteIdMatrix j k) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ =
        ∑ i : Fin m, rowSqNormProb U i * rowOuterGramSample U i j k -
          ∑ i : Fin m, rowSqNormProb U i * finiteIdMatrix j k := by
            rw [Finset.sum_sub_distrib]
      _ =
        finiteIdMatrix j k - finiteIdMatrix j k := by
            rw [hmean]
            have hconst :
                (∑ i : Fin m, rowSqNormProb U i * finiteIdMatrix j k) =
                  finiteIdMatrix j k * ∑ i : Fin m, rowSqNormProb U i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
            rw [hconst, hprob]
            ring
      _ = 0 := by ring
  simp [hreal]

/-- The centered one-step leverage covariance observable is bounded above by
`n I` in finite Loewner order.  This conservative upper bound is enough to
instantiate the generic one-step Bernstein log-CGF theorem. -/
theorem leverage_rowOuterGramSample_centered_finiteLoewnerLe_nat
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (i : Fin m) :
    finiteLoewnerLe
      (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k)
      (fun j k : Fin n => (n : ℝ) * finiteIdMatrix j k) := by
  intro x
  have hY :=
    leverage_rowOuterGramSample_finiteLoewnerLe_nat U hU hn i x
  rw [finiteQuadraticForm_smul_finiteIdMatrix] at hY
  rw [finiteQuadraticForm_sub, finiteQuadraticForm_finiteIdMatrix,
    finiteQuadraticForm_smul_finiteIdMatrix]
  exact (sub_le_self _ (finiteVecNorm2Sq_nonneg x)).trans hY

/-- Real spectrum upper bound for the centered leverage covariance observable,
obtained from the finite Loewner bound after embedding in complex C-star
matrices. -/
theorem leverage_rowOuterGramSample_centered_spectrum_le_nat {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) (i : Fin m) {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (fun j k : Fin n =>
            rowOuterGramSample U i j k - finiteIdMatrix j k))) :
    x ≤ (n : ℝ) := by
  classical
  let M : Fin n → Fin n → ℝ :=
    fun j k => rowOuterGramSample U i j k - finiteIdMatrix j k
  let N : Fin n → Fin n → ℝ :=
    fun j k => (n : ℝ) * finiteIdMatrix j k
  have hMsym : IsSymmetricFiniteMatrix M := by
    simpa [M] using rowOuterGramSample_centered_symmetric U i
  have hNsym : IsSymmetricFiniteMatrix N := by
    simpa [N] using smulFiniteIdMatrix_symmetric (n : ℝ)
  have hLe : finiteLoewnerLe M N := by
    simpa [M, N] using
      leverage_rowOuterGramSample_centered_finiteLoewnerLe_nat U hU hn i
  have hCLe :
      finiteComplexCStarMatrix M ≤
        ((n : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
    have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M N hMsym hNsym hLe
    simpa [N, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hxM :
      x ∈ spectrum ℝ (finiteComplexCStarMatrix M) := by
    simpa [M] using hx
  exact cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxM

/-- For leverage-score probabilities, the one-step rank-one estimator squares
to `n` times itself. -/
theorem leverage_finiteMatMul_rowOuterGramSample_self_eq_nat_smul
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (i : Fin m) :
    finiteMatMul
        (fun j k : Fin n => rowOuterGramSample U i j k)
        (fun j k : Fin n => rowOuterGramSample U i j k) =
      fun j k : Fin n => (n : ℝ) * rowOuterGramSample U i j k := by
  classical
  ext j k
  let p : ℝ := rowSqNormProb U i
  have hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  by_cases hpzero : p = 0
  · have hzero := rowOuterGramSample_eq_zero_of_prob_zero U hden i hpzero
    simp [finiteMatMul, hzero]
  · have hp_nonneg : 0 ≤ p := rowSqNormProb_nonneg U hden i
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hrow_pos : 0 < rowNormSq U i := by
      unfold p rowSqNormProb at hp_pos
      exact (div_pos_iff_of_pos_right hden).mp hp_pos
    have hprob_eq : p = rowNormSq U i / (n : ℝ) := by
      unfold p rowSqNormProb
      rw [rowSqNormProbDen_eq_nat_of_orthonormal_columns U hU]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    unfold finiteMatMul rowOuterGramSample
    calc
      ∑ l : Fin n,
          (U i j * U i l / rowSqNormProb U i) *
            (U i l * U i k / rowSqNormProb U i)
          =
        (U i j * U i k / p ^ 2) *
          ∑ l : Fin n, U i l ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            unfold p
            field_simp [hpzero]
      _ =
        (U i j * U i k / p ^ 2) * rowNormSq U i := by
            simp [rowNormSq]
      _ =
        (n : ℝ) * (U i j * U i k / p) := by
            rw [hprob_eq]
            field_simp [hrow_pos.ne', hnR]
      _ =
        (n : ℝ) * (U i j * U i k / rowSqNormProb U i) := by
            rfl

/-- Entrywise square identity for the centered leverage covariance observable. -/
theorem leverage_finiteMatMul_centered_rowOuterGramSample_self_eq
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (i : Fin m) :
    finiteMatMul
        (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k)
        (fun j k : Fin n => rowOuterGramSample U i j k - finiteIdMatrix j k) =
      fun j k : Fin n =>
        ((n : ℝ) - 2) * rowOuterGramSample U i j k + finiteIdMatrix j k := by
  classical
  ext j k
  have hsq :=
    congrFun (congrFun
      (leverage_finiteMatMul_rowOuterGramSample_self_eq_nat_smul U hU hn i)
      j) k
  unfold finiteMatMul
  change
    (∑ l : Fin n,
      rowOuterGramSample U i j l * rowOuterGramSample U i l k) =
      (n : ℝ) * rowOuterGramSample U i j k at hsq
  calc
    ∑ l : Fin n,
        (rowOuterGramSample U i j l - finiteIdMatrix j l) *
          (rowOuterGramSample U i l k - finiteIdMatrix l k)
        =
      (∑ l : Fin n,
        rowOuterGramSample U i j l * rowOuterGramSample U i l k) -
        rowOuterGramSample U i j k -
        rowOuterGramSample U i j k +
        finiteIdMatrix j k := by
          calc
            ∑ l : Fin n,
                (rowOuterGramSample U i j l - finiteIdMatrix j l) *
                  (rowOuterGramSample U i l k - finiteIdMatrix l k)
                =
              ∑ l : Fin n,
                (rowOuterGramSample U i j l *
                    rowOuterGramSample U i l k -
                  rowOuterGramSample U i j l * finiteIdMatrix l k -
                  finiteIdMatrix j l * rowOuterGramSample U i l k +
                  finiteIdMatrix j l * finiteIdMatrix l k) := by
                  apply Finset.sum_congr rfl
                  intro l _
                  ring
            _ =
              (∑ l : Fin n,
                  rowOuterGramSample U i j l *
                    rowOuterGramSample U i l k) -
                (∑ l : Fin n,
                  rowOuterGramSample U i j l * finiteIdMatrix l k) -
                (∑ l : Fin n,
                  finiteIdMatrix j l * rowOuterGramSample U i l k) +
                (∑ l : Fin n,
                  finiteIdMatrix j l * finiteIdMatrix l k) := by
                  rw [Finset.sum_add_distrib]
                  rw [Finset.sum_sub_distrib]
                  rw [Finset.sum_sub_distrib]
            _ =
              (∑ l : Fin n,
                rowOuterGramSample U i j l * rowOuterGramSample U i l k) -
                rowOuterGramSample U i j k -
                rowOuterGramSample U i j k +
                finiteIdMatrix j k := by
                  simp [finiteIdMatrix]
    _ =
      ((n : ℝ) - 2) * rowOuterGramSample U i j k + finiteIdMatrix j k := by
        rw [hsq]
        ring

/-- The centered one-step leverage covariance observable has exact variance
proxy `(n-1)I` under the leverage one-sample law. -/
theorem leverage_rowOuterGramSample_centered_square_expectationCStarMatrix_eq
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) :
    (rowSqNormSampleProbability U
        (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)).expectationCStarMatrix
      (fun i : RowSample m =>
        (finiteComplexCStarMatrix
            (fun j k : Fin n =>
              rowOuterGramSample U i j k - finiteIdMatrix j k) *
          finiteComplexCStarMatrix
            (fun j k : Fin n =>
              rowOuterGramSample U i j k - finiteIdMatrix j k) :
          CStarMatrix (Fin n) (Fin n) ℂ)) =
      (((n : ℝ) - 1 : ℝ) : ℂ) •
        (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
  classical
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let C : RowSample m → Fin n → Fin n → ℝ :=
    fun i j k => rowOuterGramSample U i j k - finiteIdMatrix j k
  have hprod :
      (fun i : RowSample m =>
        (finiteComplexCStarMatrix (C i) *
          finiteComplexCStarMatrix (C i) :
          CStarMatrix (Fin n) (Fin n) ℂ)) =
      fun i : RowSample m =>
        finiteComplexCStarMatrix (finiteMatMul (C i) (C i)) := by
    funext i
    rw [finiteComplexCStarMatrix_mul]
  rw [hprod]
  rw [FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix]
  ext j k
  change
    ((rowSqNormSampleProbability U hden).expectationReal
        (fun i : RowSample m => finiteMatMul (C i) (C i) j k) : ℂ) =
      ((((n : ℝ) - 1 : ℝ) : ℂ) •
        (1 : CStarMatrix (Fin n) (Fin n) ℂ)) j k
  have hmean :
      ∑ i : Fin m, rowSqNormProb U i * rowOuterGramSample U i j k =
        finiteIdMatrix j k := by
    simpa [leverageScoreProb] using
      leverage_rowOuterGramSample_mean_eq_id U hU hn j k
  have hprob :
      ∑ i : Fin m, rowSqNormProb U i = 1 := by
    simpa [leverageScoreProb] using
      leverageScoreProb_sum_eq_one U hU hn
  have hreal :
      (rowSqNormSampleProbability U hden).expectationReal
        (fun i : RowSample m => finiteMatMul (C i) (C i) j k) =
        ((n : ℝ) - 1) * finiteIdMatrix j k := by
    unfold FiniteProbability.expectationReal rowSqNormSampleProbability
    calc
      ∑ i : Fin m, rowSqNormProb U i * finiteMatMul (C i) (C i) j k
          =
        ∑ i : Fin m,
          rowSqNormProb U i *
            (((n : ℝ) - 2) * rowOuterGramSample U i j k +
              finiteIdMatrix j k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [leverage_finiteMatMul_centered_rowOuterGramSample_self_eq
              U hU hn i]
      _ =
        ∑ i : Fin m,
          (((n : ℝ) - 2) *
            (rowSqNormProb U i * rowOuterGramSample U i j k) +
            finiteIdMatrix j k * rowSqNormProb U i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ =
        ((n : ℝ) - 2) *
            (∑ i : Fin m,
              rowSqNormProb U i * rowOuterGramSample U i j k) +
          finiteIdMatrix j k * ∑ i : Fin m, rowSqNormProb U i := by
            rw [Finset.sum_add_distrib]
            rw [Finset.mul_sum]
            rw [Finset.mul_sum]
      _ = ((n : ℝ) - 1) * finiteIdMatrix j k := by
            rw [hmean, hprob]
            ring
  rw [hreal]
  by_cases hjk : j = k
  · subst hjk
    simp [finiteIdMatrix]
  · simp [finiteIdMatrix, hjk]

/-- One-step centered leverage covariance Bernstein log-CGF bound.

This theorem is the Algorithm 2 analogue of the one-sample matrix-CGF
instantiations used in the Algorithm 1 spectral route.  It does not assume any
concentration event: the proof applies the local generic C-star Bernstein
log-CGF theorem to the centered row outer-product observable. -/
theorem leverage_rowOuterGramSample_centered_log_cgf_le
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    {theta : ℝ} (htheta : 0 ≤ theta) :
    CFC.log
        ((rowSqNormSampleProbability U
          (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)).expectationCStarMatrix
          (fun i : RowSample m =>
            NormedSpace.exp
              (theta •
                finiteComplexCStarMatrix
                  (fun j k : Fin n =>
                    rowOuterGramSample U i j k - finiteIdMatrix j k) :
                CStarMatrix (Fin n) (Fin n) ℂ))) ≤
      ((Real.exp (theta * (n : ℝ)) - theta * (n : ℝ) - 1) /
          (n : ℝ) ^ 2) •
        (rowSqNormSampleProbability U
          (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)).expectationCStarMatrix
          (fun i : RowSample m =>
            (finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  rowOuterGramSample U i j k - finiteIdMatrix j k) *
              finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  rowOuterGramSample U i j k - finiteIdMatrix j k) :
              CStarMatrix (Fin n) (Fin n) ℂ)) := by
  classical
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let P := rowSqNormSampleProbability U hden
  let X : RowSample m → CStarMatrix (Fin n) (Fin n) ℂ :=
    fun i =>
      finiteComplexCStarMatrix
        (fun j k : Fin n =>
          rowOuterGramSample U i j k - finiteIdMatrix j k)
  have hX : ∀ i, IsSelfAdjoint (X i) := by
    intro i
    simpa [X] using
      leverage_rowOuterGramSample_centered_cstar_selfAdjoint U i
  have hmean : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, hden] using
      leverage_rowOuterGramSample_centered_expectationCStarMatrix_eq_zero
        U hU hn
  have hR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hspec :
      ∀ i : RowSample m, 0 < P.prob i →
        ∀ x : ℝ, x ∈ spectrum ℝ (X i) → x ≤ (n : ℝ) := by
    intro i _ x hx
    simpa [X] using
      leverage_rowOuterGramSample_centered_spectrum_le_nat
        U hU hn i hx
  have h :=
    P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
      hX hmean htheta hR hspec
  simpa [P, X, hden] using h

/-- Scalarized one-step centered leverage covariance Bernstein log-CGF bound.

This composes the log-CGF theorem with the exact variance identity
`E[(Y_i-I)^2]=(n-1)I`. -/
theorem leverage_rowOuterGramSample_centered_log_cgf_le_scalar
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    {theta : ℝ} (htheta : 0 ≤ theta) :
    CFC.log
        ((rowSqNormSampleProbability U
          (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)).expectationCStarMatrix
          (fun i : RowSample m =>
            NormedSpace.exp
              (theta •
                finiteComplexCStarMatrix
                  (fun j k : Fin n =>
                    rowOuterGramSample U i j k - finiteIdMatrix j k) :
                CStarMatrix (Fin n) (Fin n) ℂ))) ≤
      (((Real.exp (theta * (n : ℝ)) - theta * (n : ℝ) - 1) /
          (n : ℝ) ^ 2 : ℝ) •
        (((n : ℝ) - 1 : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
  classical
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let beta : ℝ :=
    (Real.exp (theta * (n : ℝ)) - theta * (n : ℝ) - 1) / (n : ℝ) ^ 2
  have h :=
    leverage_rowOuterGramSample_centered_log_cgf_le U hU hn htheta
  have hvar :=
    leverage_rowOuterGramSample_centered_square_expectationCStarMatrix_eq U hU hn
  simpa [beta, hden, hvar] using h

/-- The negative centered leverage covariance observable `I - Y_i` is bounded
above by `I` in finite Loewner order. -/
theorem leverage_rowOuterGramSample_neg_centered_finiteLoewnerLe_one
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (i : Fin m) :
    finiteLoewnerLe
      (fun j k : Fin n => -(rowOuterGramSample U i j k - finiteIdMatrix j k))
      (fun j k : Fin n => finiteIdMatrix j k) := by
  intro x
  have hpsd := leverage_rowOuterGramSample_finitePSD U hU hn i x
  rw [show
      (fun j k : Fin n =>
        -(rowOuterGramSample U i j k - finiteIdMatrix j k)) =
        fun j k : Fin n => finiteIdMatrix j k - rowOuterGramSample U i j k by
        ext j k
        ring]
  rw [finiteQuadraticForm_sub, finiteQuadraticForm_finiteIdMatrix]
  linarith

/-- Real spectrum upper bound for `-(Y_i-I)`, using PSD of the row
outer-product estimator. -/
theorem leverage_rowOuterGramSample_neg_centered_spectrum_le_one {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) (i : Fin m) {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (fun j k : Fin n =>
            rowOuterGramSample U i j k - finiteIdMatrix j k) :
          CStarMatrix (Fin n) (Fin n) ℂ)) :
    x ≤ 1 := by
  classical
  let M : Fin n → Fin n → ℝ :=
    fun j k => -(rowOuterGramSample U i j k - finiteIdMatrix j k)
  let N : Fin n → Fin n → ℝ := fun j k => finiteIdMatrix j k
  have hMsym : IsSymmetricFiniteMatrix M := by
    intro j k
    dsimp [M]
    have hsym := rowOuterGramSample_centered_symmetric U i j k
    simpa using congrArg Neg.neg hsym
  have hNsym : IsSymmetricFiniteMatrix N := by
    intro j k
    by_cases h : j = k
    · subst h
      simp [N, finiteIdMatrix]
    · have hk : k ≠ j := Ne.symm h
      simp [N, finiteIdMatrix, h, hk]
  have hLe : finiteLoewnerLe M N := by
    simpa [M, N] using
      leverage_rowOuterGramSample_neg_centered_finiteLoewnerLe_one U hU hn i
  have hCLe :
      finiteComplexCStarMatrix M ≤
        (1 : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
    have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M N hMsym hNsym hLe
    simpa [N, finiteComplexCStarMatrix_finiteIdMatrix] using hC
  have hMembed :
      finiteComplexCStarMatrix M =
        -finiteComplexCStarMatrix
          (fun j k : Fin n =>
            rowOuterGramSample U i j k - finiteIdMatrix j k) := by
    ext j k
    simp [M]
  have hxM :
      x ∈ spectrum ℝ (finiteComplexCStarMatrix M) := by
    simpa [hMembed] using hx
  exact cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxM

/-- One-step Bernstein log-CGF bound for the negative centered leverage
covariance observable. -/
theorem leverage_rowOuterGramSample_neg_centered_log_cgf_le
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    {theta : ℝ} (htheta : 0 ≤ theta) :
    let beta : ℝ := Real.exp theta - theta - 1
    CFC.log
        ((rowSqNormSampleProbability U
          (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)).expectationCStarMatrix
          (fun i : RowSample m =>
            NormedSpace.exp
              (theta •
                (-finiteComplexCStarMatrix
                  (fun j k : Fin n =>
                    rowOuterGramSample U i j k - finiteIdMatrix j k)) :
                CStarMatrix (Fin n) (Fin n) ℂ))) ≤
      beta •
        (rowSqNormSampleProbability U
          (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)).expectationCStarMatrix
          (fun i : RowSample m =>
            (finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  rowOuterGramSample U i j k - finiteIdMatrix j k) *
              finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  rowOuterGramSample U i j k - finiteIdMatrix j k) :
              CStarMatrix (Fin n) (Fin n) ℂ)) := by
  classical
  intro beta
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let P := rowSqNormSampleProbability U hden
  let X : RowSample m → CStarMatrix (Fin n) (Fin n) ℂ :=
    fun i =>
      finiteComplexCStarMatrix
        (fun j k : Fin n =>
          rowOuterGramSample U i j k - finiteIdMatrix j k)
  let Xneg : RowSample m → CStarMatrix (Fin n) (Fin n) ℂ :=
    fun i => -X i
  have hX : ∀ i, IsSelfAdjoint (Xneg i) := by
    intro i
    have hXi : IsSelfAdjoint (X i) := by
      simpa [X] using
        leverage_rowOuterGramSample_centered_cstar_selfAdjoint U i
    simpa [Xneg] using hXi.neg
  have hmeanX : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, hden] using
      leverage_rowOuterGramSample_centered_expectationCStarMatrix_eq_zero
        U hU hn
  have hmean : P.expectationCStarMatrix Xneg = 0 := by
    calc
      P.expectationCStarMatrix Xneg = -P.expectationCStarMatrix X := by
        simpa [Xneg] using
          (FiniteProbability.expectationCStarMatrix_neg P X)
      _ = 0 := by simp [hmeanX]
  have hR : 0 < (1 : ℝ) := by norm_num
  have hspec :
      ∀ i : RowSample m, 0 < P.prob i →
        ∀ x : ℝ, x ∈ spectrum ℝ (Xneg i) → x ≤ (1 : ℝ) := by
    intro i _ x hx
    simpa [X, Xneg] using
      leverage_rowOuterGramSample_neg_centered_spectrum_le_one
        U hU hn i hx
  have hlog :=
    P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
      hX hmean htheta hR hspec
  have hsq :
      (fun i : RowSample m => Xneg i * Xneg i) =
        (fun i : RowSample m => X i * X i) := by
    funext i
    ext j k
    simp [Xneg, X, CStarMatrix.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    ring
  simpa [P, X, Xneg, hden, beta, hsq] using hlog

/-- Scalarized negative-centered one-step leverage covariance log-CGF bound. -/
theorem leverage_rowOuterGramSample_neg_centered_log_cgf_le_scalar
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    {theta : ℝ} (htheta : 0 ≤ theta) :
    let beta : ℝ := Real.exp theta - theta - 1
    CFC.log
        ((rowSqNormSampleProbability U
          (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)).expectationCStarMatrix
          (fun i : RowSample m =>
            NormedSpace.exp
              (theta •
                (-finiteComplexCStarMatrix
                  (fun j k : Fin n =>
                    rowOuterGramSample U i j k - finiteIdMatrix j k)) :
                CStarMatrix (Fin n) (Fin n) ℂ))) ≤
      beta •
        (((n : ℝ) - 1 : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
  classical
  intro beta
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  have h :=
    leverage_rowOuterGramSample_neg_centered_log_cgf_le U hU hn htheta
  have hvar :=
    leverage_rowOuterGramSample_centered_square_expectationCStarMatrix_eq U hU hn
  simpa [beta, hden, hvar] using h

/-- Product-law scalar trace-MGF bound for the centered leverage covariance
increments.

This theorem composes the one-step centered leverage log-CGF estimate with the
row-trace MGF adapter.  It is the Algorithm 2 equation (7) source-sharp MGF
frontier before converting the trace bound into a largest-eigenvalue tail and
then simplifying the sample-size constants. -/
theorem leverage_rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_centered_le
    {m n s : ℕ} {theta : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (htheta : 0 ≤ theta) :
    let beta : ℝ :=
      (Real.exp (theta * (n : ℝ)) - theta * (n : ℝ) - 1) / (n : ℝ) ^ 2
    rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) U
      (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)
      (fun _a _b : Fin n => 0)
      (fun i j k =>
        theta * (rowOuterGramSample U i j k - finiteIdMatrix j k)) ≤
      (n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1))) := by
  classical
  intro beta
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let X : RowSample m → Fin n → Fin n → ℝ :=
    fun i j k => rowOuterGramSample U i j k - finiteIdMatrix j k
  have hlog :
      CFC.log
          ((rowSqNormSampleProbability U hden).expectationCStarMatrix
            (fun i : RowSample m =>
              NormedSpace.exp
                (theta • finiteComplexCStarMatrix (X i) :
                  CStarMatrix (Fin n) (Fin n) ℂ))) ≤
        beta •
          (((n : ℝ) - 1 : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
    simpa [beta, X, hden] using
      leverage_rowOuterGramSample_centered_log_cgf_le_scalar
        U hU hn htheta
  have hK :
      CFC.log
          ((rowSqNormSampleProbability U hden).expectationCStarMatrix
            (fun i : RowSample m =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun j k : Fin n => theta * X i j k)))) ≤
        (((beta * ((n : ℝ) - 1) : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
    have hEq :
        ((beta • ((((n : ℝ) - 1 : ℝ) : ℂ) : ℂ)) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) =
          (((beta * ((n : ℝ) - 1) : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    have hAssoc :
        beta • ((((n : ℝ) - 1 : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) =
          ((beta • ((((n : ℝ) - 1 : ℝ) : ℂ) : ℂ)) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    have hexp :
        (fun i : RowSample m =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun j k : Fin n => theta * X i j k))) =
        (fun i : RowSample m =>
          NormedSpace.exp
            (theta • finiteComplexCStarMatrix (X i) :
              CStarMatrix (Fin n) (Fin n) ℂ)) := by
      funext i
      rw [finiteComplexCStarMatrix_smul]
      rfl
    rw [hexp]
    rw [← hEq]
    exact hlog.trans (le_of_eq hAssoc)
  have hbound :=
    rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) U hden
      (fun (i : RowSample m) (j k : Fin n) => theta * X i j k)
      hK
  simpa [X, hden, beta, Fintype.card_fin] using hbound

/-- Product-law scalar trace-MGF bound for the negative centered leverage
covariance increments. -/
theorem leverage_rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_neg_centered_le
    {m n s : ℕ} {theta : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (htheta : 0 ≤ theta) :
    let beta : ℝ := Real.exp theta - theta - 1
    rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) U
      (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)
      (fun _a _b : Fin n => 0)
      (fun i j k =>
        (-theta) * (rowOuterGramSample U i j k - finiteIdMatrix j k)) ≤
      (n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1))) := by
  classical
  intro beta
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let X : RowSample m → Fin n → Fin n → ℝ :=
    fun i j k => rowOuterGramSample U i j k - finiteIdMatrix j k
  have hlog :
      CFC.log
          ((rowSqNormSampleProbability U hden).expectationCStarMatrix
            (fun i : RowSample m =>
              NormedSpace.exp
                (theta •
                  (-finiteComplexCStarMatrix (X i)) :
                  CStarMatrix (Fin n) (Fin n) ℂ))) ≤
        beta •
          (((n : ℝ) - 1 : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
    simpa [beta, X, hden] using
      leverage_rowOuterGramSample_neg_centered_log_cgf_le_scalar
        U hU hn htheta
  have hK :
      CFC.log
          ((rowSqNormSampleProbability U hden).expectationCStarMatrix
            (fun i : RowSample m =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun j k : Fin n => (-theta) * X i j k)))) ≤
        (((beta * ((n : ℝ) - 1) : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
    have hEq :
        ((beta • ((((n : ℝ) - 1 : ℝ) : ℂ) : ℂ)) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) =
          (((beta * ((n : ℝ) - 1) : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    have hAssoc :
        beta • ((((n : ℝ) - 1 : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) =
          ((beta • ((((n : ℝ) - 1 : ℝ) : ℂ) : ℂ)) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    have hexp :
        (fun i : RowSample m =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun j k : Fin n => (-theta) * X i j k))) =
        (fun i : RowSample m =>
          NormedSpace.exp
            (theta •
              (-finiteComplexCStarMatrix (X i)) :
              CStarMatrix (Fin n) (Fin n) ℂ)) := by
      funext i
      congr 1
      ext j k
      simp [X]
      ring
    rw [hexp]
    rw [← hEq]
    exact hlog.trans (le_of_eq hAssoc)
  have hbound :=
    rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) U hden
      (fun (i : RowSample m) (j k : Fin n) => (-theta) * X i j k)
      hK
  simpa [X, hden, beta, Fintype.card_fin] using hbound

/-- Upper-tail trace-MGF-to-eigenvalue bound for the centered leverage
covariance sum.

This is the first high-probability step in the source-sharp Algorithm 2
equation (7) route.  It proves the largest-eigenvalue Markov conversion from
the locally proved trace-MGF bound; it still leaves the scalar optimization and
sample-size simplification as the next theorem. -/
theorem leverage_rowSqNormTraceProbability_eventProb_exists_finiteHermitianEigenvalue_centered_sum_ge_le_exp
    {m n s : ℕ} {theta : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (htheta : 0 ≤ theta)
    (T : ℝ) :
    let beta : ℝ :=
      (Real.exp (theta * (n : ℝ)) - theta * (n : ℝ) - 1) / (n : ℝ) ^ 2
    (rowSqNormTraceProbability (steps := s) U
        (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)).eventProb
      {samples |
        ∃ a : Fin n,
          T ≤ finiteHermitianEigenvalues
            (fun j k : Fin n =>
              ∑ t : Fin s,
                theta *
                  (rowOuterGramSample U (samples t) j k -
                    finiteIdMatrix j k))
            (by
              intro j k
              apply Finset.sum_congr rfl
              intro t _
              have hsym :=
                rowOuterGramSample_centered_symmetric U (samples t) j k
              change
                theta *
                    (rowOuterGramSample U (samples t) j k -
                      finiteIdMatrix j k) =
                  theta *
                    (rowOuterGramSample U (samples t) k j -
                      finiteIdMatrix k j)
              simpa using congrArg (fun x => theta * x) hsym)
            a} ≤
      Real.exp (-T) *
        ((n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1)))) := by
  classical
  intro beta
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let P := rowSqNormTraceProbability (steps := s) U hden
  let X : RowSample m → Fin n → Fin n → ℝ :=
    fun i j k => theta * (rowOuterGramSample U i j k - finiteIdMatrix j k)
  let M : RowTrace m s → Fin n → Fin n → ℝ :=
    fun samples j k => ∑ t : Fin s, X (samples t) j k
  have hM : ∀ samples, IsSymmetricFiniteMatrix (M samples) := by
    intro samples j k
    dsimp [M, X]
    apply Finset.sum_congr rfl
    intro t _
    have hsym := rowOuterGramSample_centered_symmetric U (samples t) j k
    change
      theta *
          (rowOuterGramSample U (samples t) j k - finiteIdMatrix j k) =
        theta *
          (rowOuterGramSample U (samples t) k j - finiteIdMatrix k j)
    simpa using congrArg (fun x => theta * x) hsym
  have hzeroSym :
      IsSymmetricFiniteMatrix (fun _a _b : Fin n => 0) := by
    intro j k
    rfl
  have hXsym : ∀ i : RowSample m, IsSymmetricFiniteMatrix (X i) := by
    intro i j k
    dsimp [X]
    have hsym := rowOuterGramSample_centered_symmetric U i j k
    change
      theta * (rowOuterGramSample U i j k - finiteIdMatrix j k) =
        theta * (rowOuterGramSample U i k j - finiteIdMatrix k j)
    simpa using congrArg (fun x => theta * x) hsym
  have hTraceLog :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (M samples))) ≤
        rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) U hden
          (fun _a _b : Fin n => 0)
          X := by
    have h :=
      rowSqNormTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
        (steps := s) U hden hzeroSym hXsym
    simpa [P, M, X, rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound]
      using h
  have hTraceScalar :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (M samples))) ≤
        (n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1))) := by
    exact hTraceLog.trans
      (by
        simpa [hden, X, beta] using
          leverage_rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_centered_le
            (s := s) U hU hn htheta)
  simpa [P, M, X, hden, beta] using
    FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_trace_bound
      (P := P) (M := M) hM T
      ((n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1))))
      hTraceScalar

/-- High-probability upper-tail form for all eigenvalues of the centered
leverage covariance sum. -/
theorem leverage_rowSqNormTraceProbability_eventProb_forall_finiteHermitianEigenvalue_centered_sum_lt_ge_one_sub_exp
    {m n s : ℕ} {theta : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n) (htheta : 0 ≤ theta)
    (T : ℝ) :
    let beta : ℝ :=
      (Real.exp (theta * (n : ℝ)) - theta * (n : ℝ) - 1) / (n : ℝ) ^ 2
    1 -
      Real.exp (-T) *
        ((n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1)))) ≤
      (rowSqNormTraceProbability (steps := s) U
          (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)).eventProb
        {samples |
          ∀ a : Fin n,
            finiteHermitianEigenvalues
              (fun j k : Fin n =>
                ∑ t : Fin s,
                  theta *
                    (rowOuterGramSample U (samples t) j k -
                      finiteIdMatrix j k))
              (by
                intro j k
                apply Finset.sum_congr rfl
                intro t _
                have hsym :=
                  rowOuterGramSample_centered_symmetric U (samples t) j k
                change
                  theta *
                      (rowOuterGramSample U (samples t) j k -
                        finiteIdMatrix j k) =
                    theta *
                      (rowOuterGramSample U (samples t) k j -
                        finiteIdMatrix k j)
                simpa using congrArg (fun x => theta * x) hsym)
              a < T} := by
  classical
  intro beta
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let P := rowSqNormTraceProbability (steps := s) U hden
  let X : RowSample m → Fin n → Fin n → ℝ :=
    fun i j k => theta * (rowOuterGramSample U i j k - finiteIdMatrix j k)
  let M : RowTrace m s → Fin n → Fin n → ℝ :=
    fun samples j k => ∑ t : Fin s, X (samples t) j k
  have hM : ∀ samples, IsSymmetricFiniteMatrix (M samples) := by
    intro samples j k
    dsimp [M, X]
    apply Finset.sum_congr rfl
    intro t _
    have hsym := rowOuterGramSample_centered_symmetric U (samples t) j k
    change
      theta *
          (rowOuterGramSample U (samples t) j k - finiteIdMatrix j k) =
        theta *
          (rowOuterGramSample U (samples t) k j - finiteIdMatrix k j)
    simpa using congrArg (fun x => theta * x) hsym
  have hzeroSym :
      IsSymmetricFiniteMatrix (fun _a _b : Fin n => 0) := by
    intro j k
    rfl
  have hXsym : ∀ i : RowSample m, IsSymmetricFiniteMatrix (X i) := by
    intro i j k
    dsimp [X]
    have hsym := rowOuterGramSample_centered_symmetric U i j k
    change
      theta * (rowOuterGramSample U i j k - finiteIdMatrix j k) =
        theta * (rowOuterGramSample U i k j - finiteIdMatrix k j)
    simpa using congrArg (fun x => theta * x) hsym
  have hTraceLog :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (M samples))) ≤
        rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) U hden
          (fun _a _b : Fin n => 0)
          X := by
    have h :=
      rowSqNormTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
        (steps := s) U hden hzeroSym hXsym
    simpa [P, M, X, rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound]
      using h
  have hTraceScalar :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (M samples))) ≤
        (n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1))) := by
    exact hTraceLog.trans
      (by
        simpa [hden, X, beta] using
          leverage_rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_centered_le
            (s := s) U hU hn htheta)
  simpa [P, M, X, hden, beta] using
    FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound
      (P := P) (M := M) hM T
      ((n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1))))
      hTraceScalar

/-- One-sided source-sharp high-probability Loewner upper bound for
`rowSampleGram - I`.

This converts the centered-sum eigenvalue event into the sampled Gram matrix
event using the exact average identity and scalar cancellation in finite
Loewner order.  It is the upper-tail half of Algorithm 2 equation (7); the
lower-tail half uses the separate negative-centered log-CGF route. -/
theorem leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_upper_lt_ge_one_sub_exp
    {m n s : ℕ} {theta ε : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta) :
    let beta : ℝ :=
      (Real.exp (theta * (n : ℝ)) - theta * (n : ℝ) - 1) / (n : ℝ) ^ 2
    1 -
      Real.exp (-(theta * (s : ℝ) * ε)) *
        ((n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1)))) ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
            (fun j k : Fin n => ε * finiteIdMatrix j k)} := by
  classical
  intro beta
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let P := rowSqNormTraceProbability (steps := s) U hden
  let T : ℝ := theta * (s : ℝ) * ε
  let GoodEig : Set (RowTrace m s) :=
    {samples |
      ∀ a : Fin n,
        finiteHermitianEigenvalues
          (fun j k : Fin n =>
            ∑ t : Fin s,
              theta *
                (rowOuterGramSample U (samples t) j k -
                  finiteIdMatrix j k))
          (by
            intro j k
            apply Finset.sum_congr rfl
            intro t _
            have hsym :=
              rowOuterGramSample_centered_symmetric U (samples t) j k
            change
              theta *
                  (rowOuterGramSample U (samples t) j k -
                    finiteIdMatrix j k) =
                theta *
                  (rowOuterGramSample U (samples t) k j -
                    finiteIdMatrix k j)
            simpa using congrArg (fun x => theta * x) hsym)
          a < T}
  let GoodLoewner : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  have hEigProb :
      1 -
        Real.exp (-T) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1)))) ≤
        P.eventProb GoodEig := by
    simpa [P, GoodEig, T, beta, hden, leverageTraceProbability] using
      leverage_rowSqNormTraceProbability_eventProb_forall_finiteHermitianEigenvalue_centered_sum_lt_ge_one_sub_exp
        (s := s) (theta := theta) U hU hn (le_of_lt htheta) T
  have hsubset : GoodEig ⊆ GoodLoewner := by
    intro samples hsamples
    let M : Fin n → Fin n → ℝ :=
      fun j k =>
        ∑ t : Fin s,
          theta *
            (rowOuterGramSample U (samples t) j k - finiteIdMatrix j k)
    have hM : IsSymmetricFiniteMatrix M := by
      intro j k
      dsimp [M]
      apply Finset.sum_congr rfl
      intro t _
      have hsym := rowOuterGramSample_centered_symmetric U (samples t) j k
      change
        theta *
            (rowOuterGramSample U (samples t) j k - finiteIdMatrix j k) =
          theta *
            (rowOuterGramSample U (samples t) k j - finiteIdMatrix k j)
      simpa using congrArg (fun x => theta * x) hsym
    have hEig : ∀ a : Fin n, finiteHermitianEigenvalues M hM a ≤ T := by
      intro a
      exact le_of_lt (by simpa [GoodEig, M, T] using hsamples a)
    have hLoM :
        finiteLoewnerLe M (fun j k : Fin n => T * finiteIdMatrix j k) :=
      finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le M hM hEig
    let E : Fin n → Fin n → ℝ :=
      fun j k => rowSampleGram s U samples j k - finiteIdMatrix j k
    have hM_eq :
        M = fun j k : Fin n => (theta * (s : ℝ)) * E j k := by
      ext j k
      have hcenter :=
        rowSampleGram_sub_finiteIdMatrix_eq_centered_rowOuterGramSample_average
          U hden hs samples j k
      have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
      dsimp [M, E]
      calc
        ∑ t : Fin s,
            theta *
              (rowOuterGramSample U (samples t) j k - finiteIdMatrix j k)
            =
          theta * ∑ t : Fin s,
            (rowOuterGramSample U (samples t) j k - finiteIdMatrix j k) := by
            rw [Finset.mul_sum]
        _ =
          theta * (s : ℝ) *
            ((∑ t : Fin s,
              (rowOuterGramSample U (samples t) j k - finiteIdMatrix j k)) /
                (s : ℝ)) := by
            field_simp [hs_ne]
        _ = theta * (s : ℝ) *
            (rowSampleGram s U samples j k - finiteIdMatrix j k) := by
            rw [← hcenter]
    have hscaled :
        finiteLoewnerLe
          (fun j k : Fin n => (theta * (s : ℝ)) * E j k)
          (fun j k : Fin n => T * finiteIdMatrix j k) := by
      simpa [hM_eq] using hLoM
    have htheta_s : 0 < theta * (s : ℝ) := mul_pos htheta hs
    have hunscaled :=
      finiteLoewnerLe_of_smul_left_le_smul_id E htheta_s hscaled
    have hTdiv : T / (theta * (s : ℝ)) = ε := by
      dsimp [T]
      field_simp [(ne_of_gt htheta_s)]
    have hGood : GoodLoewner samples := by
      simpa [GoodLoewner, E, hTdiv] using hunscaled
    exact hGood
  exact hEigProb.trans (FiniteProbability.eventProb_mono P hsubset)

/-- One-sided lower-tail high-probability Loewner bound for
`rowSampleGram - I`, written as `-(rowSampleGram-I) <= ε I`. -/
theorem leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_lower_lt_ge_one_sub_exp
    {m n s : ℕ} {theta ε : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta) :
    let beta : ℝ := Real.exp theta - theta - 1
    1 -
      Real.exp (-(theta * (s : ℝ) * ε)) *
        ((n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1)))) ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
            (fun j k : Fin n => ε * finiteIdMatrix j k)} := by
  classical
  intro beta
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let P := rowSqNormTraceProbability (steps := s) U hden
  let T : ℝ := theta * (s : ℝ) * ε
  let Xneg : RowSample m → Fin n → Fin n → ℝ :=
    fun i j k => (-theta) * (rowOuterGramSample U i j k - finiteIdMatrix j k)
  let Mneg : RowTrace m s → Fin n → Fin n → ℝ :=
    fun samples j k => ∑ t : Fin s, Xneg (samples t) j k
  let GoodEig : Set (RowTrace m s) :=
    {samples |
      ∀ a : Fin n,
        finiteHermitianEigenvalues (Mneg samples)
          (by
            intro j k
            dsimp [Mneg, Xneg]
            apply Finset.sum_congr rfl
            intro t _
            have hsym :=
              rowOuterGramSample_centered_symmetric U (samples t) j k
            change
              (-theta) *
                  (rowOuterGramSample U (samples t) j k -
                    finiteIdMatrix j k) =
                (-theta) *
                  (rowOuterGramSample U (samples t) k j -
                    finiteIdMatrix k j)
            simpa using congrArg (fun x => (-theta) * x) hsym)
          a < T}
  let GoodLoewner : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  have hMneg : ∀ samples, IsSymmetricFiniteMatrix (Mneg samples) := by
    intro samples j k
    dsimp [Mneg, Xneg]
    apply Finset.sum_congr rfl
    intro t _
    have hsym := rowOuterGramSample_centered_symmetric U (samples t) j k
    change
      (-theta) *
          (rowOuterGramSample U (samples t) j k - finiteIdMatrix j k) =
        (-theta) *
          (rowOuterGramSample U (samples t) k j - finiteIdMatrix k j)
    simpa using congrArg (fun x => (-theta) * x) hsym
  have hzeroSym :
      IsSymmetricFiniteMatrix (fun _a _b : Fin n => 0) := by
    intro j k
    rfl
  have hXnegSym : ∀ i : RowSample m, IsSymmetricFiniteMatrix (Xneg i) := by
    intro i j k
    dsimp [Xneg]
    have hsym := rowOuterGramSample_centered_symmetric U i j k
    change
      (-theta) * (rowOuterGramSample U i j k - finiteIdMatrix j k) =
        (-theta) * (rowOuterGramSample U i k j - finiteIdMatrix k j)
    simpa using congrArg (fun x => (-theta) * x) hsym
  have hTraceLog :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (Mneg samples))) ≤
        rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) U hden
          (fun _a _b : Fin n => 0)
          Xneg := by
    have h :=
      rowSqNormTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
        (steps := s) U hden hzeroSym hXnegSym
    simpa [P, Mneg, Xneg, rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound]
      using h
  have hTraceScalar :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (Mneg samples))) ≤
        (n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1))) := by
    exact hTraceLog.trans
      (by
        simpa [hden, Xneg, beta] using
          leverage_rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_neg_centered_le
            (s := s) U hU hn (le_of_lt htheta))
  have hEigProb :
      1 -
        Real.exp (-T) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1)))) ≤
        P.eventProb GoodEig := by
    simpa [P, GoodEig, Mneg, T, beta, hden, leverageTraceProbability] using
      FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound
        (P := P) (M := Mneg) hMneg T
        ((n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1))))
        hTraceScalar
  have hsubset : GoodEig ⊆ GoodLoewner := by
    intro samples hsamples
    have hEig : ∀ a : Fin n, finiteHermitianEigenvalues (Mneg samples) (hMneg samples) a ≤ T := by
      intro a
      exact le_of_lt (by simpa [GoodEig, Mneg, T] using hsamples a)
    have hLoM :
        finiteLoewnerLe (Mneg samples)
          (fun j k : Fin n => T * finiteIdMatrix j k) :=
      finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le
        (Mneg samples) (hMneg samples) hEig
    let Eneg : Fin n → Fin n → ℝ :=
      fun j k => -(rowSampleGram s U samples j k - finiteIdMatrix j k)
    have hM_eq :
        Mneg samples = fun j k : Fin n => (theta * (s : ℝ)) * Eneg j k := by
      ext j k
      have hcenter :=
        rowSampleGram_sub_finiteIdMatrix_eq_centered_rowOuterGramSample_average
          U hden hs samples j k
      have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
      dsimp [Mneg, Xneg, Eneg]
      calc
        ∑ t : Fin s,
            (-theta) *
              (rowOuterGramSample U (samples t) j k - finiteIdMatrix j k)
            =
          (-theta) * ∑ t : Fin s,
            (rowOuterGramSample U (samples t) j k - finiteIdMatrix j k) := by
            rw [Finset.mul_sum]
        _ =
          theta * (s : ℝ) *
            (-((∑ t : Fin s,
              (rowOuterGramSample U (samples t) j k - finiteIdMatrix j k)) /
                (s : ℝ))) := by
            field_simp [hs_ne]
        _ = theta * (s : ℝ) *
            (-(rowSampleGram s U samples j k - finiteIdMatrix j k)) := by
            rw [← hcenter]
    have hscaled :
        finiteLoewnerLe
          (fun j k : Fin n => (theta * (s : ℝ)) * Eneg j k)
          (fun j k : Fin n => T * finiteIdMatrix j k) := by
      simpa [hM_eq] using hLoM
    have htheta_s : 0 < theta * (s : ℝ) := mul_pos htheta hs
    have hunscaled :=
      finiteLoewnerLe_of_smul_left_le_smul_id Eneg htheta_s hscaled
    have hTdiv : T / (theta * (s : ℝ)) = ε := by
      dsimp [T]
      field_simp [(ne_of_gt htheta_s)]
    have hGood : GoodLoewner samples := by
      simpa [GoodLoewner, Eneg, hTdiv] using hunscaled
    exact hGood
  exact hEigProb.trans (FiniteProbability.eventProb_mono P hsubset)

/-- One-sided upper-tail sample-budget form for Algorithm 2 leverage
row-sampling.

This removes the raw exponential-tail hypothesis by choosing the Bennett
optimizer for the upper-tail radius `L = n`, variance proxy `W = n-1`, and
target radius `ε`. -/
theorem leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_upper_ge_one_sub_delta_half_of_sample_budget
    {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hε : 0 < ε) (hδ : 0 < δ)
    (hbudget :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε))) :
    1 - δ / 2 ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
            (fun j k : Fin n => ε * finiteIdMatrix j k)} := by
  classical
  let theta : ℝ := Real.log (1 + (n : ℝ) * ε / ((n : ℝ) - 1)) / (n : ℝ)
  let beta : ℝ :=
    (Real.exp (theta * (n : ℝ)) - theta * (n : ℝ) - 1) / (n : ℝ) ^ 2
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have htheta : 0 < theta := by
    have hquot : 0 < (n : ℝ) * ε / ((n : ℝ) - 1) := by positivity
    have harg : 1 < 1 + (n : ℝ) * ε / ((n : ℝ) - 1) := by linarith
    dsimp [theta]
    exact div_pos (Real.log_pos harg) hnReal
  have htail :
      Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1)))) ≤
        δ / 2 := by
    simpa [theta, beta, mul_assoc, mul_left_comm, mul_comm] using
      real_bernstein_tail_le_half_delta_of_quadratic_budget
        (B := (n : ℝ)) (W := (n : ℝ) - 1) (L := (n : ℝ))
        (r := ε) (s := (s : ℝ)) (δ := δ)
        hnReal hnVar hnReal hε hs hδ hbudget
  have hbase :=
    leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_upper_lt_ge_one_sub_exp
      (s := s) (theta := theta) (ε := ε) U hU hn hs htheta
  exact (sub_le_sub_left htail 1).trans
    (by simpa [theta, beta] using hbase)

/-- One-sided lower-tail sample-budget form for Algorithm 2 leverage
row-sampling.

This chooses the Bennett optimizer for the lower-tail radius `L = 1`, the same
variance proxy `W = n-1`, and target radius `ε`. -/
theorem leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_lower_ge_one_sub_delta_half_of_sample_budget
    {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hε : 0 < ε) (hδ : 0 < δ)
    (hbudget :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ / 2 ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
            (fun j k : Fin n => ε * finiteIdMatrix j k)} := by
  classical
  let theta : ℝ := Real.log (1 + (1 : ℝ) * ε / ((n : ℝ) - 1)) / (1 : ℝ)
  let beta : ℝ := Real.exp theta - theta - 1
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have htheta : 0 < theta := by
    have hquot : 0 < (1 : ℝ) * ε / ((n : ℝ) - 1) := by positivity
    have harg : 1 < 1 + (1 : ℝ) * ε / ((n : ℝ) - 1) := by linarith
    dsimp [theta]
    simpa using Real.log_pos harg
  have htail :
      Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (beta * ((n : ℝ) - 1)))) ≤
        δ / 2 := by
    simpa [theta, beta, mul_assoc, mul_left_comm, mul_comm] using
      real_bernstein_tail_le_half_delta_of_quadratic_budget
        (B := (n : ℝ)) (W := (n : ℝ) - 1) (L := (1 : ℝ))
        (r := ε) (s := (s : ℝ)) (δ := δ)
        hnReal hnVar (by norm_num) hε hs hδ
        (by simpa [mul_assoc, mul_left_comm, mul_comm] using hbudget)
  have hbase :=
    leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_lower_lt_ge_one_sub_exp
      (s := s) (theta := theta) (ε := ε) U hU hn hs htheta
  exact (sub_le_sub_left htail 1).trans
    (by simpa [theta, beta] using hbase)

/-- Two-sided high-probability finite-Loewner form of the Algorithm 2
leverage-score covariance concentration route.

The theorem keeps the positive and negative one-step CGF constants separate:
the upper side uses radius `n`, while the lower side uses radius `1`.  This is
the source-sharp high-probability event before optional scalar optimization of
`theta` and simplification to the paper's displayed sample-size condition. -/
theorem leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_exp
    {m n s : ℕ} {theta ε : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta) :
    let betaUpper : ℝ :=
      (Real.exp (theta * (n : ℝ)) - theta * (n : ℝ) - 1) / (n : ℝ) ^ 2
    let betaLower : ℝ := Real.exp theta - theta - 1
    let tailUpper : ℝ :=
      Real.exp (-(theta * (s : ℝ) * ε)) *
        ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * ((n : ℝ) - 1))))
    let tailLower : ℝ :=
      Real.exp (-(theta * (s : ℝ) * ε)) *
        ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * ((n : ℝ) - 1))))
    1 - (tailUpper + tailLower) ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
            (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
            (fun j k : Fin n => ε * finiteIdMatrix j k)} := by
  classical
  intro betaUpper betaLower tailUpper tailLower
  let P := leverageTraceProbability (steps := s) U hU hn
  let EU : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  let EL : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  have hEU : 1 - tailUpper ≤ P.eventProb EU := by
    simpa [P, EU, betaUpper, tailUpper] using
      leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_upper_lt_ge_one_sub_exp
        (s := s) (theta := theta) (ε := ε) U hU hn hs htheta
  have hEL : 1 - tailLower ≤ P.eventProb EL := by
    simpa [P, EL, betaLower, tailLower] using
      leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_lower_lt_ge_one_sub_exp
        (s := s) (theta := theta) (ε := ε) U hU hn hs htheta
  have hinter :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P EU EL
      tailUpper tailLower hEU hEL
  exact le_trans (by rfl) (by
    simpa [P, EU, EL, tailUpper, tailLower] using hinter)

/-- Delta-budget corollary of the two-sided leverage-score covariance
concentration theorem.

The scalar premise is a deterministic tail-budget inequality.  It is not a
probabilistic hidden hypothesis; the remaining paper-level simplification is to
prove convenient sample-size conditions that imply this budget. -/
theorem leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget
    {m n s : ℕ} {theta ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta)
    (hbudget :
      let betaUpper : ℝ :=
        (Real.exp (theta * (n : ℝ)) - theta * (n : ℝ) - 1) / (n : ℝ) ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * ((n : ℝ) - 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * ((n : ℝ) - 1))))
      tailUpper + tailLower ≤ δ) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
            (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
            (fun j k : Fin n => ε * finiteIdMatrix j k)} := by
  classical
  let betaUpper : ℝ :=
    (Real.exp (theta * (n : ℝ)) - theta * (n : ℝ) - 1) / (n : ℝ) ^ 2
  let betaLower : ℝ := Real.exp theta - theta - 1
  let tailUpper : ℝ :=
    Real.exp (-(theta * (s : ℝ) * ε)) *
      ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * ((n : ℝ) - 1))))
  let tailLower : ℝ :=
    Real.exp (-(theta * (s : ℝ) * ε)) *
      ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * ((n : ℝ) - 1))))
  have hhp :=
    leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_exp
      (s := s) (theta := theta) (ε := ε) U hU hn hs htheta
  have hbudget' : tailUpper + tailLower ≤ δ := by
    simpa [betaUpper, betaLower, tailUpper, tailLower] using hbudget
  exact (sub_le_sub_left hbudget' 1).trans
    (by simpa [betaUpper, betaLower, tailUpper, tailLower] using hhp)

/-- Two-sided sample-budget corollary for Algorithm 2 leverage row-sampling.

This is the source-aligned scalar-budget replacement for the explicit
exponential tails: the upper and lower Bennett optimizers are allowed to differ,
so the result combines the two one-sided events by a union bound. -/
theorem leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
            (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
            (fun j k : Fin n => ε * finiteIdMatrix j k)} := by
  classical
  let P := leverageTraceProbability (steps := s) U hU hn
  let EU : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  let EL : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  have hEU : 1 - δ / 2 ≤ P.eventProb EU := by
    simpa [P, EU] using
      leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_upper_ge_one_sub_delta_half_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U hU hn hnVar hs hε hδ
        hbudgetUpper
  have hEL : 1 - δ / 2 ≤ P.eventProb EL := by
    simpa [P, EL] using
      leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_lower_ge_one_sub_delta_half_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U hU hn hnVar hs hε hδ
        hbudgetLower
  have hinter :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P EU EL
      (δ / 2) (δ / 2) hEU hEL
  have hδsum : δ / 2 + δ / 2 = δ := by ring
  simpa [P, EU, EL, hδsum] using hinter

/-- Floating-point transfer for the source-aligned Algorithm 2 leverage
row-sampling sample-budget theorem.

The exact event is the two-sided finite-Loewner event from the Bennett
sample-budget corollary.  The floating-point part is deterministic on the
probability-one positive-support event and adds
`rowSampleGramFullFpPerturbBudget fp s U` to both Loewner sides. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDot fp s U samples j k - finiteIdMatrix j k)
            (fun j k : Fin n =>
              (ε + rowSampleGramFullFpPerturbBudget fp s U) *
                finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDot fp s U samples j k - finiteIdMatrix j k))
            (fun j k : Fin n =>
              (ε + rowSampleGramFullFpPerturbBudget fp s U) *
                finiteIdMatrix j k)} := by
  classical
  let P := leverageTraceProbability (steps := s) U hU hn
  let τ : ℝ := rowSampleGramFullFpPerturbBudget fp s U
  let E : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
        (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb U samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k : Fin n =>
          fl_rowSampleGramDot fp s U samples j k -
            rowSampleGram s U samples j k) ≤ τ}
  let G : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          fl_rowSampleGramDot fp s U samples j k - finiteIdMatrix j k)
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(fl_rowSampleGramDot fp s U samples j k - finiteIdMatrix j k))
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k)}
  have hE :
      1 - δ ≤ P.eventProb E := by
    simpa [P, E] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U hU hn hnVar hs hε hδ
        hbudgetUpper hbudgetLower
  have hGoodProb : P.eventProb Good = 1 := by
    let hden : 0 < rowSqNormProbDen U :=
      rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
    simpa [P, Good, leverageTraceProbability] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) U hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb U samples := by
      simpa [Good] using hgood
    simpa [F, τ] using
      leverage_fl_rowSampleGramDot_perturb_bound
        fp U hU hn hs hγ samples hgood_pos
  have hF : 1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have hEF :
      1 - (δ + 0) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P E F δ 0 hE hF
  have hsubset : E ∩ F ⊆ G := by
    intro samples hsamples
    rcases hsamples with ⟨hexact, hpert⟩
    rcases hexact with ⟨hExactUpper, hExactLower⟩
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => rowSampleGram s U samples j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_rowSampleGramDot fp s U samples j k -
          rowSampleGram s U samples j k
    have hDeltaOp : opNorm2Le Delta τ :=
      opNorm2Le_of_frobNorm_le Delta (by simpa [F, Delta, τ] using hpert)
    have hDeltaUpper :
        finiteLoewnerLe Delta
          (fun j k : Fin n => τ * finiteIdMatrix j k) := by
      intro x
      rw [finiteQuadraticForm_smul_finiteIdMatrix]
      have habs :=
        abs_vecInnerProduct_matMulVec_le_of_opNorm2Le Delta hDeltaOp x
      have hquad :
          |finiteQuadraticForm Delta x| ≤ τ * finiteVecNorm2Sq x := by
        simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
          finiteVecNorm2Sq, vecNorm2Sq] using habs
      exact (le_abs_self (finiteQuadraticForm Delta x)).trans hquad
    have hDeltaLower :
        finiteLoewnerLe (fun j k : Fin n => -Delta j k)
          (fun j k : Fin n => τ * finiteIdMatrix j k) := by
      intro x
      rw [finiteQuadraticForm_smul_finiteIdMatrix]
      have hDeltaNegOp :
          opNorm2Le (fun j k : Fin n => -Delta j k) τ := by
        have hneg :
            frobNorm (fun j k : Fin n => -Delta j k) ≤ τ := by
          have hpertDelta : frobNorm Delta ≤ τ := by
            simpa [F, Delta, τ] using hpert
          simpa [frobNorm_neg] using hpertDelta
        exact opNorm2Le_of_frobNorm_le (fun j k : Fin n => -Delta j k) hneg
      have habs :=
        abs_vecInnerProduct_matMulVec_le_of_opNorm2Le
          (fun j k : Fin n => -Delta j k) hDeltaNegOp x
      have hquad :
          |finiteQuadraticForm (fun j k : Fin n => -Delta j k) x| ≤
            τ * finiteVecNorm2Sq x := by
        simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
          finiteVecNorm2Sq, vecNorm2Sq] using habs
      exact (le_abs_self
        (finiteQuadraticForm (fun j k : Fin n => -Delta j k) x)).trans hquad
    have hExactUpper' :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [Exact] using hExactUpper
    have hExactLower' :
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [Exact] using hExactLower
    have hUpperAdd := finiteLoewnerLe_add hExactUpper' hDeltaUpper
    have hLowerAdd := finiteLoewnerLe_add hExactLower' hDeltaLower
    have hUpperRhs :
        finiteLoewnerLe
          (fun j k : Fin n =>
            ε * finiteIdMatrix j k + τ * finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      intro x
      rw [finiteQuadraticForm_add, finiteQuadraticForm_smul_finiteIdMatrix,
        finiteQuadraticForm_smul_finiteIdMatrix,
        finiteQuadraticForm_smul_finiteIdMatrix]
      have hcombine :
          ε * finiteVecNorm2Sq x + τ * finiteVecNorm2Sq x =
            (ε + τ) * finiteVecNorm2Sq x := by
        ring
      rw [hcombine]
    have hLowerRhs :
        finiteLoewnerLe
          (fun j k : Fin n =>
            ε * finiteIdMatrix j k + τ * finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := hUpperRhs
    have hCompEq :
        (fun j k : Fin n =>
          fl_rowSampleGramDot fp s U samples j k - finiteIdMatrix j k) =
        fun j k : Fin n => Exact j k + Delta j k := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hNegCompEq :
        (fun j k : Fin n =>
          -(fl_rowSampleGramDot fp s U samples j k - finiteIdMatrix j k)) =
        fun j k : Fin n => -Exact j k + -Delta j k := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_rowSampleGramDot fp s U samples j k - finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hCompEq]
      exact finiteLoewnerLe_trans hUpperAdd hUpperRhs
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_rowSampleGramDot fp s U samples j k - finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hNegCompEq]
      exact finiteLoewnerLe_trans hLowerAdd hLowerRhs
    exact ⟨hUpper, hLower⟩
  have hG := hEF.trans (FiniteProbability.eventProb_mono P hsubset)
  simpa [P, E, F, G, τ] using hG

/-- Fully floating-point equation (7) for the computed-denominator Algorithm 2
    path.

The exact event is the same two-sided Bennett finite-Loewner event.  The
floating-point radius now charges the computed row-scale denominator, rounded
row scaling, and floating-point dot products for the Gram entries. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U))
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp U dhat.den samples j k -
                finiteIdMatrix j k)
            (fun j k : Fin n =>
              (ε + rowSampleGramComputedDenFullFpPerturbBudget fp s U dhat) *
                finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp U dhat.den samples j k -
                finiteIdMatrix j k))
            (fun j k : Fin n =>
              (ε + rowSampleGramComputedDenFullFpPerturbBudget fp s U dhat) *
                finiteIdMatrix j k)} := by
  classical
  let P := leverageTraceProbability (steps := s) U hU hn
  let τ : ℝ := rowSampleGramComputedDenFullFpPerturbBudget fp s U dhat
  let E : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n => rowSampleGram s U samples j k - finiteIdMatrix j k)
        (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n => -(rowSampleGram s U samples j k - finiteIdMatrix j k))
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb U samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp U dhat.den samples j k -
            rowSampleGram s U samples j k) ≤ τ}
  let G : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp U dhat.den samples j k -
            finiteIdMatrix j k)
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(fl_rowSampleGramDotWithComputedDen fp U dhat.den samples j k -
            finiteIdMatrix j k))
        (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k)}
  have hE :
      1 - δ ≤ P.eventProb E := by
    simpa [P, E] using
      leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
        (s := s) (ε := ε) (δ := δ) U hU hn hnVar hs hε hδ
        hbudgetUpper hbudgetLower
  have hGoodProb : P.eventProb Good = 1 := by
    let hden : 0 < rowSqNormProbDen U :=
      rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
    simpa [P, Good, leverageTraceProbability] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) U hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb U samples := by
      simpa [Good] using hgood
    simpa [F, τ] using
      leverage_fl_rowSampleGramDotWithComputedDen_perturb_bound
        fp U hU hn hs hγ dhat samples hgood_pos
  have hF : 1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have hEF :
      1 - (δ + 0) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P E F δ 0 hE hF
  have hsubset : E ∩ F ⊆ G := by
    intro samples hsamples
    rcases hsamples with ⟨hexact, hpert⟩
    rcases hexact with ⟨hExactUpper, hExactLower⟩
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => rowSampleGram s U samples j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_rowSampleGramDotWithComputedDen fp U dhat.den samples j k -
          rowSampleGram s U samples j k
    have hDeltaOp : opNorm2Le Delta τ :=
      opNorm2Le_of_frobNorm_le Delta (by simpa [F, Delta, τ] using hpert)
    have hDeltaUpper :
        finiteLoewnerLe Delta
          (fun j k : Fin n => τ * finiteIdMatrix j k) := by
      intro x
      rw [finiteQuadraticForm_smul_finiteIdMatrix]
      have habs :=
        abs_vecInnerProduct_matMulVec_le_of_opNorm2Le Delta hDeltaOp x
      have hquad :
          |finiteQuadraticForm Delta x| ≤ τ * finiteVecNorm2Sq x := by
        simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
          finiteVecNorm2Sq, vecNorm2Sq] using habs
      exact (le_abs_self (finiteQuadraticForm Delta x)).trans hquad
    have hDeltaLower :
        finiteLoewnerLe (fun j k : Fin n => -Delta j k)
          (fun j k : Fin n => τ * finiteIdMatrix j k) := by
      intro x
      rw [finiteQuadraticForm_smul_finiteIdMatrix]
      have hDeltaNegOp :
          opNorm2Le (fun j k : Fin n => -Delta j k) τ := by
        have hneg :
            frobNorm (fun j k : Fin n => -Delta j k) ≤ τ := by
          have hpertDelta : frobNorm Delta ≤ τ := by
            simpa [F, Delta, τ] using hpert
          simpa [frobNorm_neg] using hpertDelta
        exact opNorm2Le_of_frobNorm_le (fun j k : Fin n => -Delta j k) hneg
      have habs :=
        abs_vecInnerProduct_matMulVec_le_of_opNorm2Le
          (fun j k : Fin n => -Delta j k) hDeltaNegOp x
      have hquad :
          |finiteQuadraticForm (fun j k : Fin n => -Delta j k) x| ≤
            τ * finiteVecNorm2Sq x := by
        simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
          finiteVecNorm2Sq, vecNorm2Sq] using habs
      exact (le_abs_self
        (finiteQuadraticForm (fun j k : Fin n => -Delta j k) x)).trans hquad
    have hExactUpper' :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [Exact] using hExactUpper
    have hExactLower' :
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [Exact] using hExactLower
    have hUpperAdd := finiteLoewnerLe_add hExactUpper' hDeltaUpper
    have hLowerAdd := finiteLoewnerLe_add hExactLower' hDeltaLower
    have hUpperRhs :
        finiteLoewnerLe
          (fun j k : Fin n =>
            ε * finiteIdMatrix j k + τ * finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      intro x
      rw [finiteQuadraticForm_add, finiteQuadraticForm_smul_finiteIdMatrix,
        finiteQuadraticForm_smul_finiteIdMatrix,
        finiteQuadraticForm_smul_finiteIdMatrix]
      have hcombine :
          ε * finiteVecNorm2Sq x + τ * finiteVecNorm2Sq x =
            (ε + τ) * finiteVecNorm2Sq x := by
        ring
      rw [hcombine]
    have hLowerRhs :
        finiteLoewnerLe
          (fun j k : Fin n =>
            ε * finiteIdMatrix j k + τ * finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := hUpperRhs
    have hCompEq :
        (fun j k : Fin n =>
          fl_rowSampleGramDotWithComputedDen fp U dhat.den samples j k -
            finiteIdMatrix j k) =
        fun j k : Fin n => Exact j k + Delta j k := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hNegCompEq :
        (fun j k : Fin n =>
          -(fl_rowSampleGramDotWithComputedDen fp U dhat.den samples j k -
            finiteIdMatrix j k)) =
        fun j k : Fin n => -Exact j k + -Delta j k := by
      ext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_rowSampleGramDotWithComputedDen fp U dhat.den samples j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hCompEq]
      exact finiteLoewnerLe_trans hUpperAdd hUpperRhs
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_rowSampleGramDotWithComputedDen fp U dhat.den samples j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hNegCompEq]
      exact finiteLoewnerLe_trans hLowerAdd hLowerRhs
    exact ⟨hUpper, hLower⟩
  have hG := hEF.trans (FiniteProbability.eventProb_mono P hsubset)
  simpa [P, E, F, G, τ] using hG

/-- Positive `gammaValid` horizons imply the unit roundoff is below one.

This small adapter lets concrete square-root denominator certificates use the
same sample-count roundoff guard as the downstream dot-product analysis. -/
theorem unitRoundoff_lt_one_of_pos_gammaValid
    (fp : FPModel) {s : ℕ} (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) :
    fp.u < 1 := by
  have hsNat : 0 < s := by exact_mod_cast hs
  have hone_le_s_nat : 1 ≤ s := Nat.succ_le_iff.mpr hsNat
  have hone_le_s : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hone_le_s_nat
  have hu_le_su : fp.u ≤ (s : ℝ) * fp.u := by
    simpa using mul_le_mul_of_nonneg_right hone_le_s fp.u_nonneg
  have hsu_lt_one : (s : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hγ
  exact lt_of_le_of_lt hu_le_su hsu_lt_one

/-- Concrete leverage-score denominator routine for Algorithm 2 equation (7).

The probability table remains the exact leverage-score law by project
convention.  The non-probability denominator used by the implementation is the
rounded routine `fl_sqrt (fl_mul s p_i)`, and the constructor below carries the
proved absolute denominator-error bound for that routine. -/
noncomputable def leverageFlMulThenSqrtRowScaleDen
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s) :
    ComputedRowScaleDen fp s (rowSqNormProb U) :=
  ComputedRowScaleDen.flMulThenSqrt fp s (rowSqNormProb U)
    (rowSqNormProb_nonneg U
      (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn))
    hs (unitRoundoff_lt_one_of_pos_gammaValid fp hs hγ)

@[simp] theorem leverageFlMulThenSqrtRowScaleDen_den
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s) :
    (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den =
      fun i => fp.fl_sqrt (fp.fl_mul (s : ℝ) (rowSqNormProb U i)) := rfl

/-- Fully concrete floating-point equation (7) for Algorithm 2.

This is the implementation-facing specialization of the computed-denominator
theorem above to the actual denominator routine
`dhat_i = fl_sqrt (fl_mul s p_i)`, where `p_i` is the exact leverage-score
sampling probability.  Thus the final radius charges the rounded denominator
formation, rounded row scaling, and floating-point Gram dot products, without
leaving an arbitrary denominator certificate in the theorem statement. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDotWithFlMulThenSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
    (fp : FPModel) {m n s : ℕ} {ε δ : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hnVar : 0 < (n : ℝ) - 1)
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hbudgetUpper :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * (n : ℝ) * ε)))
    (hbudgetLower :
      Real.log ((2 * (n : ℝ)) / δ) ≤
        (s : ℝ) *
          (ε ^ 2 /
            (2 * ((n : ℝ) - 1) + (2 / 3 : ℝ) * ε))) :
    1 - δ ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              fl_rowSampleGramDotWithComputedDen fp U
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k)
            (fun j k : Fin n =>
              (ε +
                  rowSampleGramComputedDenFullFpPerturbBudget fp s U
                    (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(fl_rowSampleGramDotWithComputedDen fp U
                  (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ).den
                  samples j k -
                finiteIdMatrix j k))
            (fun j k : Fin n =>
              (ε +
                  rowSampleGramComputedDenFullFpPerturbBudget fp s U
                    (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)) *
                finiteIdMatrix j k)} := by
  exact
    leverageTraceProbability_eventProb_fl_rowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget
      fp U hU hn hnVar hs hγ
      (leverageFlMulThenSqrtRowScaleDen fp U hU hn hs hγ)
      hε hδ hbudgetUpper hbudgetLower

end NumStability
