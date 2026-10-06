-- Algorithms/RandNLA/UniformRowSamplingMGF.lean
--
-- One-step matrix-CGF prerequisites for uniform row sampling after
-- randomized preconditioning.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import NumStability.Algorithms.RandNLA.UniformRowSampling
import NumStability.Analysis.LiebTrace
import NumStability.Analysis.MatrixConcentration

namespace NumStability

open scoped BigOperators ComplexOrder

/-!
## Centered uniform row covariance log-CGF

This file starts the concentration route for Algorithm 3 after the
coordinate-Hoeffding leverage-uniformization event.  The one-step observable is

`X_i = m u_i u_i^T - I`.

The file proves mean-zero, self-adjointness, and bounded-spectrum prerequisites
for applying the repository's generic matrix Bernstein/Lieb trace-CGF theorem.
It does not assume concentration; concentration for iid averages is built on
these one-step facts.
-/

/-- The centered uniform one-step estimator is symmetric. -/
theorem uniformRowOuterGramSample_centered_symmetric {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) :
    IsSymmetricFiniteMatrix
      (fun j k : Fin n =>
        uniformRowOuterGramSample U i j k - finiteIdMatrix j k) := by
  intro j k
  have hrow := uniformRowOuterGramSample_symmetric U i j k
  change uniformRowOuterGramSample U i j k =
    uniformRowOuterGramSample U i k j at hrow
  change
    uniformRowOuterGramSample U i j k - finiteIdMatrix j k =
      uniformRowOuterGramSample U i k j - finiteIdMatrix k j
  rw [hrow]
  by_cases h : j = k
  · subst h
    simp [finiteIdMatrix]
  · have hk : k ≠ j := Ne.symm h
    simp [finiteIdMatrix, h, hk]

/-- C-star self-adjointness of the centered uniform one-step estimator. -/
theorem uniformRowOuterGramSample_centered_cstar_selfAdjoint {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) :
    IsSelfAdjoint
      (finiteComplexCStarMatrix
        (fun j k : Fin n =>
          uniformRowOuterGramSample U i j k - finiteIdMatrix j k)) := by
  exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
    (fun j k : Fin n =>
      uniformRowOuterGramSample U i j k - finiteIdMatrix j k)
    (uniformRowOuterGramSample_centered_symmetric U i)

/-- Under the one-sample uniform row law, the centered uniform estimator has
mean zero for an orthonormal-column matrix. -/
theorem uniformRowOuterGramSample_centered_expectationCStarMatrix_eq_zero
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) :
    (uniformRowSampleProbability hm).expectationCStarMatrix
      (fun i : RowSample m =>
        finiteComplexCStarMatrix
          (fun j k : Fin n =>
            uniformRowOuterGramSample U i j k - finiteIdMatrix j k)) = 0 := by
  classical
  rw [FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix]
  ext j k
  change
    ((uniformRowSampleProbability hm).expectationReal
        (fun i : RowSample m =>
          uniformRowOuterGramSample U i j k - finiteIdMatrix j k) : ℂ) = 0
  have hmean :
      ∑ i : Fin m, uniformRowProb i * uniformRowOuterGramSample U i j k =
        finiteIdMatrix j k := by
    simpa [uniformRowProb] using
      uniform_rowOuterGramSample_mean_eq_id U hU hm j k
  have hprob :
      ∑ i : Fin m, uniformRowProb i = 1 :=
    uniformRowProb_sum_eq_one hm
  have hreal :
      (uniformRowSampleProbability hm).expectationReal
        (fun i : RowSample m =>
          uniformRowOuterGramSample U i j k - finiteIdMatrix j k) = 0 := by
    unfold FiniteProbability.expectationReal uniformRowSampleProbability
    calc
      ∑ i : Fin m,
          uniformRowProb i *
            (uniformRowOuterGramSample U i j k - finiteIdMatrix j k)
          =
        ∑ i : Fin m,
          (uniformRowProb i * uniformRowOuterGramSample U i j k -
            uniformRowProb i * finiteIdMatrix j k) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ =
        ∑ i : Fin m, uniformRowProb i * uniformRowOuterGramSample U i j k -
          ∑ i : Fin m, uniformRowProb i * finiteIdMatrix j k := by
            rw [Finset.sum_sub_distrib]
      _ =
        finiteIdMatrix j k - finiteIdMatrix j k := by
            rw [hmean]
            have hconst :
                (∑ i : Fin m, uniformRowProb i * finiteIdMatrix j k) =
                  finiteIdMatrix j k * ∑ i : Fin m, uniformRowProb i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
            rw [hconst, hprob]
            ring
      _ = 0 := by ring
  simp [hreal]

/-- If a uniform one-step estimator is bounded above by `L I`, then the
centered estimator is also bounded above by `L I`. -/
theorem uniformRowOuterGramSample_centered_finiteLoewnerLe_of_sample_le
    {m n : ℕ} (U : Fin m → Fin n → ℝ) (i : Fin m) {L : ℝ}
    (hL :
      finiteLoewnerLe
        (fun j k : Fin n => uniformRowOuterGramSample U i j k)
        (fun j k : Fin n => L * finiteIdMatrix j k)) :
    finiteLoewnerLe
      (fun j k : Fin n => uniformRowOuterGramSample U i j k - finiteIdMatrix j k)
      (fun j k : Fin n => L * finiteIdMatrix j k) := by
  intro x
  have hY := hL x
  rw [finiteQuadraticForm_smul_finiteIdMatrix] at hY
  rw [finiteQuadraticForm_sub, finiteQuadraticForm_finiteIdMatrix,
    finiteQuadraticForm_smul_finiteIdMatrix]
  exact (sub_le_self _ (finiteVecNorm2Sq_nonneg x)).trans hY

/-- Real spectrum upper bound for a centered uniform one-step estimator. -/
theorem uniformRowOuterGramSample_centered_spectrum_le_of_sample_le {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) {L x : ℝ}
    (hL :
      finiteLoewnerLe
        (fun j k : Fin n => uniformRowOuterGramSample U i j k)
        (fun j k : Fin n => L * finiteIdMatrix j k))
    (hx :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (fun j k : Fin n =>
            uniformRowOuterGramSample U i j k - finiteIdMatrix j k))) :
    x ≤ L := by
  classical
  let M : Fin n → Fin n → ℝ :=
    fun j k => uniformRowOuterGramSample U i j k - finiteIdMatrix j k
  let N : Fin n → Fin n → ℝ :=
    fun j k => L * finiteIdMatrix j k
  have hMsym : IsSymmetricFiniteMatrix M := by
    simpa [M] using uniformRowOuterGramSample_centered_symmetric U i
  have hNsym : IsSymmetricFiniteMatrix N := by
    simpa [N] using smulFiniteIdMatrix_symmetric L
  have hLe : finiteLoewnerLe M N := by
    simpa [M, N] using
      uniformRowOuterGramSample_centered_finiteLoewnerLe_of_sample_le U i hL
  have hCLe :
      finiteComplexCStarMatrix M ≤
        (L : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
    have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M N hMsym hNsym hLe
    simpa [N, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hxM : x ∈ spectrum ℝ (finiteComplexCStarMatrix M) := by
    simpa [M] using hx
  exact cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxM

/-- The negative centered uniform estimator `I - X_i` is bounded above by
`I`, using only positive semidefiniteness of the one-step estimator. -/
theorem uniformRowOuterGramSample_neg_centered_finiteLoewnerLe_one
    {m n : ℕ} (U : Fin m → Fin n → ℝ) (i : Fin m) :
    finiteLoewnerLe
      (fun j k : Fin n => -(uniformRowOuterGramSample U i j k - finiteIdMatrix j k))
      (fun j k : Fin n => finiteIdMatrix j k) := by
  intro x
  have hpsd := finitePSD_uniformRowOuterGramSample U i x
  rw [show
      (fun j k : Fin n =>
        -(uniformRowOuterGramSample U i j k - finiteIdMatrix j k)) =
        fun j k : Fin n => finiteIdMatrix j k - uniformRowOuterGramSample U i j k by
        ext j k
        ring]
  rw [finiteQuadraticForm_sub, finiteQuadraticForm_finiteIdMatrix]
  linarith

/-- Real spectrum upper bound for the negative centered uniform estimator. -/
theorem uniformRowOuterGramSample_neg_centered_spectrum_le_one {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (fun j k : Fin n =>
            uniformRowOuterGramSample U i j k - finiteIdMatrix j k) :
          CStarMatrix (Fin n) (Fin n) ℂ)) :
    x ≤ 1 := by
  classical
  let M : Fin n → Fin n → ℝ :=
    fun j k => -(uniformRowOuterGramSample U i j k - finiteIdMatrix j k)
  let N : Fin n → Fin n → ℝ := fun j k => finiteIdMatrix j k
  have hMsym : IsSymmetricFiniteMatrix M := by
    intro j k
    dsimp [M]
    have hsym := uniformRowOuterGramSample_centered_symmetric U i j k
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
      uniformRowOuterGramSample_neg_centered_finiteLoewnerLe_one U i
  have hCLe :
      finiteComplexCStarMatrix M ≤
        (1 : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
    have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M N hMsym hNsym hLe
    simpa [N, finiteComplexCStarMatrix_finiteIdMatrix] using hC
  have hMembed :
      finiteComplexCStarMatrix M =
        -finiteComplexCStarMatrix
          (fun j k : Fin n =>
            uniformRowOuterGramSample U i j k - finiteIdMatrix j k) := by
    ext j k
    simp [M]
  have hxM :
      x ∈ spectrum ℝ (finiteComplexCStarMatrix M) := by
    simpa [hMembed] using hx
  exact cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxM

/-- The square of a uniform one-step row outer-product estimator is a scalar
multiple of itself. -/
theorem uniform_finiteMatMul_rowOuterGramSample_self_eq
    {m n : ℕ} (U : Fin m → Fin n → ℝ) (i : Fin m) :
    finiteMatMul
        (fun j k : Fin n => uniformRowOuterGramSample U i j k)
        (fun j k : Fin n => uniformRowOuterGramSample U i j k) =
      fun j k : Fin n =>
        ((m : ℝ) * rowNormSq U i) *
          uniformRowOuterGramSample U i j k := by
  classical
  ext j k
  unfold finiteMatMul uniformRowOuterGramSample rowNormSq
  calc
    ∑ l : Fin n,
        ((m : ℝ) * U i j * U i l) * ((m : ℝ) * U i l * U i k)
        =
      ((m : ℝ) * (m : ℝ) * U i j * U i k) *
        ∑ l : Fin n, U i l ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
    _ =
      ((m : ℝ) * ∑ l : Fin n, U i l ^ 2) *
        ((m : ℝ) * U i j * U i k) := by
          ring

/-- Entrywise square identity for the centered uniform one-step estimator. -/
theorem uniform_finiteMatMul_centered_rowOuterGramSample_self_eq
    {m n : ℕ} (U : Fin m → Fin n → ℝ) (i : Fin m) :
    finiteMatMul
        (fun j k : Fin n =>
          uniformRowOuterGramSample U i j k - finiteIdMatrix j k)
        (fun j k : Fin n =>
          uniformRowOuterGramSample U i j k - finiteIdMatrix j k) =
      fun j k : Fin n =>
        finiteMatMul
            (fun a b : Fin n => uniformRowOuterGramSample U i a b)
            (fun a b : Fin n => uniformRowOuterGramSample U i a b) j k -
          uniformRowOuterGramSample U i j k -
          uniformRowOuterGramSample U i j k +
          finiteIdMatrix j k := by
  classical
  ext j k
  unfold finiteMatMul
  calc
    ∑ l : Fin n,
        (uniformRowOuterGramSample U i j l - finiteIdMatrix j l) *
          (uniformRowOuterGramSample U i l k - finiteIdMatrix l k)
        =
      (∑ l : Fin n,
        uniformRowOuterGramSample U i j l *
          uniformRowOuterGramSample U i l k) -
        uniformRowOuterGramSample U i j k -
        uniformRowOuterGramSample U i j k +
        finiteIdMatrix j k := by
          calc
            ∑ l : Fin n,
                (uniformRowOuterGramSample U i j l - finiteIdMatrix j l) *
                  (uniformRowOuterGramSample U i l k - finiteIdMatrix l k)
                =
              ∑ l : Fin n,
                (uniformRowOuterGramSample U i j l *
                    uniformRowOuterGramSample U i l k -
                  uniformRowOuterGramSample U i j l * finiteIdMatrix l k -
                  finiteIdMatrix j l * uniformRowOuterGramSample U i l k +
                  finiteIdMatrix j l * finiteIdMatrix l k) := by
                  apply Finset.sum_congr rfl
                  intro l _
                  ring
            _ =
              (∑ l : Fin n,
                  uniformRowOuterGramSample U i j l *
                    uniformRowOuterGramSample U i l k) -
                (∑ l : Fin n,
                  uniformRowOuterGramSample U i j l * finiteIdMatrix l k) -
                (∑ l : Fin n,
                  finiteIdMatrix j l * uniformRowOuterGramSample U i l k) +
                (∑ l : Fin n,
                  finiteIdMatrix j l * finiteIdMatrix l k) := by
                  rw [Finset.sum_add_distrib]
                  rw [Finset.sum_sub_distrib]
                  rw [Finset.sum_sub_distrib]
            _ =
              (∑ l : Fin n,
                uniformRowOuterGramSample U i j l *
                  uniformRowOuterGramSample U i l k) -
                uniformRowOuterGramSample U i j k -
                uniformRowOuterGramSample U i j k +
                finiteIdMatrix j k := by
                  simp [finiteIdMatrix]

/-- A deterministic row-norm/Loewner bound gives a pointwise variance proxy
for the centered uniform one-step estimator. -/
theorem uniform_finiteMatMul_centered_rowOuterGramSample_self_finiteLoewnerLe
    {m n : ℕ} (U : Fin m → Fin n → ℝ) (i : Fin m) {L : ℝ}
    (hrow : (m : ℝ) * rowNormSq U i ≤ L)
    (hY :
      finiteLoewnerLe
        (fun j k : Fin n => uniformRowOuterGramSample U i j k)
        (fun j k : Fin n => L * finiteIdMatrix j k)) :
    finiteLoewnerLe
      (finiteMatMul
        (fun j k : Fin n =>
          uniformRowOuterGramSample U i j k - finiteIdMatrix j k)
        (fun j k : Fin n =>
          uniformRowOuterGramSample U i j k - finiteIdMatrix j k))
      (fun j k : Fin n => (L ^ 2 + 1) * finiteIdMatrix j k) := by
  intro x
  let Y : Fin n → Fin n → ℝ :=
    fun j k => uniformRowOuterGramSample U i j k
  let C : Fin n → Fin n → ℝ :=
    fun j k => uniformRowOuterGramSample U i j k - finiteIdMatrix j k
  have hc_nonneg : 0 ≤ (m : ℝ) * rowNormSq U i :=
    mul_nonneg (Nat.cast_nonneg m) (rowNormSq_nonneg U i)
  have hL_nonneg : 0 ≤ L := hc_nonneg.trans hrow
  have hYsq_eq :
      finiteMatMul Y Y =
        fun j k : Fin n => ((m : ℝ) * rowNormSq U i) * Y j k := by
    simpa [Y] using uniform_finiteMatMul_rowOuterGramSample_self_eq U i
  have hCeq :
      finiteMatMul C C =
        fun j k : Fin n =>
          finiteMatMul Y Y j k - Y j k - Y j k + finiteIdMatrix j k := by
    simpa [Y, C] using
      uniform_finiteMatMul_centered_rowOuterGramSample_self_eq U i
  have hYpsd : finitePSD Y := by
    simpa [Y] using finitePSD_uniformRowOuterGramSample U i
  have hY_le : finiteLoewnerLe Y (fun j k : Fin n => L * finiteIdMatrix j k) := by
    simpa [Y] using hY
  have hYsq_le_Lsq :
      finiteQuadraticForm (finiteMatMul Y Y) x ≤
        L ^ 2 * finiteVecNorm2Sq x := by
    rw [hYsq_eq, finiteQuadraticForm_smul]
    have hcoef :
        ((m : ℝ) * rowNormSq U i) * finiteQuadraticForm Y x ≤
          L * finiteQuadraticForm Y x :=
      mul_le_mul_of_nonneg_right hrow (hYpsd x)
    have hLq :
        L * finiteQuadraticForm Y x ≤ L * (L * finiteVecNorm2Sq x) :=
      mul_le_mul_of_nonneg_left
        (by
          have hy := hY_le x
          simpa [finiteQuadraticForm_smul_finiteIdMatrix] using hy)
        hL_nonneg
    calc
      ((m : ℝ) * rowNormSq U i) * finiteQuadraticForm Y x
          ≤ L * finiteQuadraticForm Y x := hcoef
      _ ≤ L * (L * finiteVecNorm2Sq x) := hLq
      _ = L ^ 2 * finiteVecNorm2Sq x := by ring
  have hC_le :
      finiteQuadraticForm (finiteMatMul C C) x ≤
        finiteQuadraticForm (finiteMatMul Y Y) x +
          finiteVecNorm2Sq x := by
    rw [hCeq, finiteQuadraticForm_add, finiteQuadraticForm_sub,
      finiteQuadraticForm_sub, finiteQuadraticForm_finiteIdMatrix]
    have hnonneg : 0 ≤ 2 * finiteQuadraticForm Y x := by
      nlinarith [hYpsd x]
    linarith
  rw [finiteQuadraticForm_smul_finiteIdMatrix]
  calc
    finiteQuadraticForm (finiteMatMul C C) x
        ≤ finiteQuadraticForm (finiteMatMul Y Y) x +
          finiteVecNorm2Sq x := hC_le
    _ ≤ L ^ 2 * finiteVecNorm2Sq x + finiteVecNorm2Sq x :=
          add_le_add hYsq_le_Lsq (le_refl _)
    _ = (L ^ 2 + 1) * finiteVecNorm2Sq x := by ring

/-- C⋆-matrix variance proxy for the centered uniform one-step estimator. -/
theorem uniformRowOuterGramSample_centered_square_expectationCStarMatrix_le
    {m n : ℕ} (U : Fin m → Fin n → ℝ) (hm : 0 < m) {L : ℝ}
    (hrow : ∀ i : RowSample m, (m : ℝ) * rowNormSq U i ≤ L)
    (hY :
      ∀ i : RowSample m,
        finiteLoewnerLe
          (fun j k : Fin n => uniformRowOuterGramSample U i j k)
          (fun j k : Fin n => L * finiteIdMatrix j k)) :
    (uniformRowSampleProbability hm).expectationCStarMatrix
      (fun i : RowSample m =>
        (finiteComplexCStarMatrix
            (fun j k : Fin n =>
              uniformRowOuterGramSample U i j k - finiteIdMatrix j k) *
          finiteComplexCStarMatrix
            (fun j k : Fin n =>
              uniformRowOuterGramSample U i j k - finiteIdMatrix j k) :
          CStarMatrix (Fin n) (Fin n) ℂ)) ≤
      ((L ^ 2 + 1 : ℝ) : ℂ) •
        (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
  classical
  let P := uniformRowSampleProbability hm
  let C : RowSample m → Fin n → Fin n → ℝ :=
    fun i j k => uniformRowOuterGramSample U i j k - finiteIdMatrix j k
  let W : ℝ := L ^ 2 + 1
  have hpoint :
      ∀ i : RowSample m,
        (finiteComplexCStarMatrix (C i) * finiteComplexCStarMatrix (C i) :
          CStarMatrix (Fin n) (Fin n) ℂ) ≤
          (W : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
    intro i
    have hprod :
        (finiteComplexCStarMatrix (C i) * finiteComplexCStarMatrix (C i) :
          CStarMatrix (Fin n) (Fin n) ℂ) =
          finiteComplexCStarMatrix (finiteMatMul (C i) (C i)) := by
      rw [finiteComplexCStarMatrix_mul]
    rw [hprod]
    have hMsym :
        IsSymmetricFiniteMatrix (finiteMatMul (C i) (C i)) :=
      finiteMatMul_self_symmetric_of_symmetric (C i)
        (by simpa [C] using uniformRowOuterGramSample_centered_symmetric U i)
    have hNsym :
        IsSymmetricFiniteMatrix
          (fun j k : Fin n => W * finiteIdMatrix j k) :=
      smulFiniteIdMatrix_symmetric W
    have hLe :
        finiteLoewnerLe (finiteMatMul (C i) (C i))
          (fun j k : Fin n => W * finiteIdMatrix j k) := by
      simpa [C, W] using
        uniform_finiteMatMul_centered_rowOuterGramSample_self_finiteLoewnerLe
          U i (hrow i) (hY i)
    have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe
      (finiteMatMul (C i) (C i))
      (fun j k : Fin n => W * finiteIdMatrix j k) hMsym hNsym hLe
    simpa [W, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hmono :=
    FiniteProbability.expectationCStarMatrix_mono P
      (fun i : RowSample m =>
        (finiteComplexCStarMatrix (C i) * finiteComplexCStarMatrix (C i) :
          CStarMatrix (Fin n) (Fin n) ℂ))
      (fun _i : RowSample m =>
        (W : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) ℂ))
      hpoint
  have hconst :
      P.expectationCStarMatrix
        (fun _i : RowSample m =>
          (W : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) ℂ)) =
        (W : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) ℂ) :=
    FiniteProbability.expectationCStarMatrix_const P
      ((W : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) ℂ))
  simpa [P, C, W] using hmono.trans (le_of_eq hconst)

/-- One-step Bernstein log-CGF bound for centered uniform row covariance
increments under a deterministic one-step Loewner bound. -/
theorem uniformRowOuterGramSample_centered_log_cgf_le_of_forall_sample_le
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {L theta : ℝ} (hLpos : 0 < L) (htheta : 0 ≤ theta)
    (hL :
      ∀ i : RowSample m,
        finiteLoewnerLe
          (fun j k : Fin n => uniformRowOuterGramSample U i j k)
          (fun j k : Fin n => L * finiteIdMatrix j k)) :
    CFC.log
        ((uniformRowSampleProbability hm).expectationCStarMatrix
          (fun i : RowSample m =>
            NormedSpace.exp
              (theta •
                finiteComplexCStarMatrix
                  (fun j k : Fin n =>
                    uniformRowOuterGramSample U i j k - finiteIdMatrix j k) :
                CStarMatrix (Fin n) (Fin n) ℂ))) ≤
      ((Real.exp (theta * L) - theta * L - 1) / L ^ 2) •
        (uniformRowSampleProbability hm).expectationCStarMatrix
          (fun i : RowSample m =>
            (finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  uniformRowOuterGramSample U i j k - finiteIdMatrix j k) *
              finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  uniformRowOuterGramSample U i j k - finiteIdMatrix j k) :
              CStarMatrix (Fin n) (Fin n) ℂ)) := by
  classical
  let P := uniformRowSampleProbability hm
  let X : RowSample m → CStarMatrix (Fin n) (Fin n) ℂ :=
    fun i =>
      finiteComplexCStarMatrix
        (fun j k : Fin n =>
          uniformRowOuterGramSample U i j k - finiteIdMatrix j k)
  have hX : ∀ i, IsSelfAdjoint (X i) := by
    intro i
    simpa [X] using
      uniformRowOuterGramSample_centered_cstar_selfAdjoint U i
  have hmean : P.expectationCStarMatrix X = 0 := by
    simpa [P, X] using
      uniformRowOuterGramSample_centered_expectationCStarMatrix_eq_zero
        U hU hm
  have hspec :
      ∀ i : RowSample m, 0 < P.prob i →
        ∀ x : ℝ, x ∈ spectrum ℝ (X i) → x ≤ L := by
    intro i _ x hx
    simpa [X] using
      uniformRowOuterGramSample_centered_spectrum_le_of_sample_le
        U i (hL i) hx
  have h :=
    P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
      hX hmean htheta hLpos hspec
  simpa [P, X] using h

/-- Scalarized one-step Bernstein log-CGF bound for centered uniform row
covariance increments, from a supplied variance proxy.

The variance proxy is explicit here; downstream paper-level theorems must prove
it from row-norm/leverage hypotheses before using this wrapper. -/
theorem uniformRowOuterGramSample_centered_log_cgf_le_scalar_of_variance_proxy
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {L W theta : ℝ} (hLpos : 0 < L) (htheta : 0 ≤ theta)
    (hL :
      ∀ i : RowSample m,
        finiteLoewnerLe
          (fun j k : Fin n => uniformRowOuterGramSample U i j k)
          (fun j k : Fin n => L * finiteIdMatrix j k))
    (hvar :
      (uniformRowSampleProbability hm).expectationCStarMatrix
          (fun i : RowSample m =>
            (finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  uniformRowOuterGramSample U i j k - finiteIdMatrix j k) *
              finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  uniformRowOuterGramSample U i j k - finiteIdMatrix j k) :
              CStarMatrix (Fin n) (Fin n) ℂ)) ≤
        (W : ℂ) • (1 : CStarMatrix (Fin n) (Fin n) ℂ)) :
    CFC.log
        ((uniformRowSampleProbability hm).expectationCStarMatrix
          (fun i : RowSample m =>
            NormedSpace.exp
              (theta •
                finiteComplexCStarMatrix
                  (fun j k : Fin n =>
                    uniformRowOuterGramSample U i j k - finiteIdMatrix j k) :
                CStarMatrix (Fin n) (Fin n) ℂ))) ≤
      (((((Real.exp (theta * L) - theta * L - 1) / L ^ 2) * W : ℝ) : ℂ) •
        (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
  classical
  let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
  have hbase :=
    uniformRowOuterGramSample_centered_log_cgf_le_of_forall_sample_le
      U hU hm hLpos htheta hL
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
        (uniformRowSampleProbability hm).expectationCStarMatrix
          (fun i : RowSample m =>
            (finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  uniformRowOuterGramSample U i j k - finiteIdMatrix j k) *
              finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  uniformRowOuterGramSample U i j k - finiteIdMatrix j k) :
              CStarMatrix (Fin n) (Fin n) ℂ)) ≤
        (((beta * W : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((W : ℂ) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) =
          (((beta * W : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    exact h1.trans (le_of_eq hEq)
  exact hbase.trans (by simpa [beta] using hscaled)

/-- Scalarized one-step Bernstein log-CGF bound for centered uniform row
covariance increments, with the variance proxy proved from row-norm and
one-step Loewner bounds. -/
theorem uniformRowOuterGramSample_centered_log_cgf_le_scalar_of_forall_rowNorm_bound
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {L theta : ℝ} (hLpos : 0 < L) (htheta : 0 ≤ theta)
    (hrow : ∀ i : RowSample m, (m : ℝ) * rowNormSq U i ≤ L)
    (hY :
      ∀ i : RowSample m,
        finiteLoewnerLe
          (fun j k : Fin n => uniformRowOuterGramSample U i j k)
          (fun j k : Fin n => L * finiteIdMatrix j k)) :
    CFC.log
        ((uniformRowSampleProbability hm).expectationCStarMatrix
          (fun i : RowSample m =>
            NormedSpace.exp
              (theta •
                finiteComplexCStarMatrix
                  (fun j k : Fin n =>
                    uniformRowOuterGramSample U i j k - finiteIdMatrix j k) :
                CStarMatrix (Fin n) (Fin n) ℂ))) ≤
      (((((Real.exp (theta * L) - theta * L - 1) / L ^ 2) *
          (L ^ 2 + 1) : ℝ) : ℂ) •
        (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
  classical
  have hvar :=
    uniformRowOuterGramSample_centered_square_expectationCStarMatrix_le
      U hm hrow hY
  simpa using
    uniformRowOuterGramSample_centered_log_cgf_le_scalar_of_variance_proxy
      U hU hm hLpos htheta hY hvar

/-- One-step Bernstein log-CGF bound for the negative centered uniform row
covariance observable. -/
theorem uniformRowOuterGramSample_neg_centered_log_cgf_le_of_forall_sample_le
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta : ℝ} (htheta : 0 ≤ theta) :
    let beta : ℝ := Real.exp theta - theta - 1
    CFC.log
        ((uniformRowSampleProbability hm).expectationCStarMatrix
          (fun i : RowSample m =>
            NormedSpace.exp
              (theta •
                (-finiteComplexCStarMatrix
                  (fun j k : Fin n =>
                    uniformRowOuterGramSample U i j k - finiteIdMatrix j k)) :
                CStarMatrix (Fin n) (Fin n) ℂ))) ≤
      beta •
        (uniformRowSampleProbability hm).expectationCStarMatrix
          (fun i : RowSample m =>
            (finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  uniformRowOuterGramSample U i j k - finiteIdMatrix j k) *
              finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  uniformRowOuterGramSample U i j k - finiteIdMatrix j k) :
              CStarMatrix (Fin n) (Fin n) ℂ)) := by
  classical
  intro beta
  let P := uniformRowSampleProbability hm
  let X : RowSample m → CStarMatrix (Fin n) (Fin n) ℂ :=
    fun i =>
      finiteComplexCStarMatrix
        (fun j k : Fin n =>
          uniformRowOuterGramSample U i j k - finiteIdMatrix j k)
  let Xneg : RowSample m → CStarMatrix (Fin n) (Fin n) ℂ :=
    fun i => -X i
  have hX : ∀ i, IsSelfAdjoint (Xneg i) := by
    intro i
    have hXi : IsSelfAdjoint (X i) := by
      simpa [X] using
        uniformRowOuterGramSample_centered_cstar_selfAdjoint U i
    simpa [Xneg] using hXi.neg
  have hmeanX : P.expectationCStarMatrix X = 0 := by
    simpa [P, X] using
      uniformRowOuterGramSample_centered_expectationCStarMatrix_eq_zero
        U hU hm
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
      uniformRowOuterGramSample_neg_centered_spectrum_le_one U i hx
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
  simpa [P, X, Xneg, beta, hsq] using hlog

/-- Scalarized negative-centered one-step CGF bound for uniform row sampling,
with the variance proxy proved from row-norm and one-step Loewner bounds. -/
theorem uniformRowOuterGramSample_neg_centered_log_cgf_le_scalar_of_forall_rowNorm_bound
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {L theta : ℝ} (htheta : 0 ≤ theta)
    (hrow : ∀ i : RowSample m, (m : ℝ) * rowNormSq U i ≤ L)
    (hY :
      ∀ i : RowSample m,
        finiteLoewnerLe
          (fun j k : Fin n => uniformRowOuterGramSample U i j k)
          (fun j k : Fin n => L * finiteIdMatrix j k)) :
    let beta : ℝ := Real.exp theta - theta - 1
    CFC.log
        ((uniformRowSampleProbability hm).expectationCStarMatrix
          (fun i : RowSample m =>
            NormedSpace.exp
              (theta •
                (-finiteComplexCStarMatrix
                  (fun j k : Fin n =>
                    uniformRowOuterGramSample U i j k - finiteIdMatrix j k)) :
                CStarMatrix (Fin n) (Fin n) ℂ))) ≤
      ((beta * (L ^ 2 + 1) : ℝ) : ℂ) •
        (1 : CStarMatrix (Fin n) (Fin n) ℂ) := by
  classical
  intro beta
  have hbase :=
    uniformRowOuterGramSample_neg_centered_log_cgf_le_of_forall_sample_le
      U hU hm htheta
  have hvar :=
    uniformRowOuterGramSample_centered_square_expectationCStarMatrix_le
      U hm hrow hY
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    exact real_exp_sub_self_sub_one_nonneg theta
  have hscaled :
      beta •
        (uniformRowSampleProbability hm).expectationCStarMatrix
          (fun i : RowSample m =>
            (finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  uniformRowOuterGramSample U i j k - finiteIdMatrix j k) *
              finiteComplexCStarMatrix
                (fun j k : Fin n =>
                  uniformRowOuterGramSample U i j k - finiteIdMatrix j k) :
              CStarMatrix (Fin n) (Fin n) ℂ)) ≤
        (((beta * (L ^ 2 + 1) : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((((L ^ 2 + 1 : ℝ) : ℂ)) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) =
          (((beta * (L ^ 2 + 1) : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    exact h1.trans (le_of_eq hEq)
  exact hbase.trans (by simpa [beta] using hscaled)

-- ============================================================
-- Uniform product trace-MGF adapters
-- ============================================================

/-- Complex-valued marginal expectation for one coordinate of the iid uniform
row product trace law. -/
theorem uniformRowTraceProbability_expectationComplex_step_eq
    {m steps : ℕ} (hm : 0 < m) (t0 : Fin steps)
    (f : RowSample m → ℂ) :
    (uniformRowTraceProbability (steps := steps) hm).expectationComplex
      (fun samples => f (samples t0)) =
      ∑ i : RowSample m, (uniformRowProb i : ℂ) * f i := by
  classical
  apply Complex.ext
  · have hre :=
      uniformRowTraceProbMass_marginal_one hm t0
        (fun i : RowSample m => (f i).re)
    simpa [FiniteProbability.expectationComplex, uniformRowTraceProbability]
      using hre
  · have him :=
      uniformRowTraceProbMass_marginal_one hm t0
        (fun i : RowSample m => (f i).im)
    simpa [FiniteProbability.expectationComplex, uniformRowTraceProbability]
      using him

/-- C⋆-matrix-valued marginal expectation for one coordinate of the iid uniform
row product trace law. -/
theorem uniformRowTraceProbability_expectationCStarMatrix_step_eq
    {m steps : ℕ} (hm : 0 < m) (t0 : Fin steps)
    {ι : Type*} [Fintype ι]
    (F : RowSample m → CStarMatrix ι ι ℂ) :
    (uniformRowTraceProbability (steps := steps) hm).expectationCStarMatrix
      (fun samples => F (samples t0)) =
      ∑ i : RowSample m, (uniformRowProb i : ℂ) • F i := by
  classical
  ext a b
  have h :=
    uniformRowTraceProbability_expectationComplex_step_eq hm t0
      (fun i : RowSample m => F i a b)
  change
    (uniformRowTraceProbability (steps := steps) hm).expectationComplex
        (fun samples => F (samples t0) a b) =
      (∑ i : RowSample m, (uniformRowProb i : ℂ) • F i) a b
  rw [show
      (∑ i : RowSample m, (uniformRowProb i : ℂ) • F i) a b =
        ∑ i : RowSample m,
          ((uniformRowProb i : ℂ) • F i) a b by
    exact Matrix.sum_apply a b Finset.univ
      (fun i => ((uniformRowProb i : ℂ) • F i :
        CStarMatrix ι ι ℂ))]
  simpa [smul_eq_mul] using h

/-- The product-law C⋆ marginal expectation agrees with the one-sample uniform
probability space. -/
theorem uniformRowTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation
    {m steps : ℕ} (hm : 0 < m) (t0 : Fin steps)
    {ι : Type*} [Fintype ι]
    (F : RowSample m → CStarMatrix ι ι ℂ) :
    (uniformRowTraceProbability (steps := steps) hm).expectationCStarMatrix
      (fun samples => F (samples t0)) =
      (uniformRowSampleProbability hm).expectationCStarMatrix F := by
  classical
  rw [uniformRowTraceProbability_expectationCStarMatrix_step_eq hm t0 F]
  rw [FiniteProbability.expectationCStarMatrix_eq_sum_smul]
  simp [uniformRowSampleProbability]

/-- The uniform row product trace mass of a trace obtained by appending one
last sample factors into prefix mass times one-sample mass. -/
theorem uniformRowTraceProbMass_snoc {m steps : ℕ}
    (pref : RowTrace m steps) (lastSample : RowSample m) :
    uniformRowTraceProbMass (Fin.snoc pref lastSample) =
      uniformRowTraceProbMass pref * uniformRowProb lastSample := by
  classical
  unfold uniformRowTraceProbMass
  rw [Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Conditioning on the last row sample for real-valued statistics under the
iid uniform product trace law. -/
theorem uniformRowTraceProbability_expectationReal_succ_last_eq
    {m steps : ℕ} (hm : 0 < m)
    (F : RowTrace m steps → RowSample m → ℝ) :
    (uniformRowTraceProbability (steps := steps + 1) hm).expectationReal
      (fun samples =>
        F (Fin.init samples) (samples (Fin.last steps))) =
    (uniformRowTraceProbability (steps := steps) hm).expectationReal
      (fun pref =>
        (uniformRowSampleProbability hm).expectationReal
          (fun lastSample => F pref lastSample)) := by
  classical
  let e :
      RowSample m × RowTrace m steps ≃
        RowTrace m (steps + 1) :=
    Fin.snocEquiv (fun _ : Fin (steps + 1) => RowSample m)
  unfold FiniteProbability.expectationReal uniformRowTraceProbability
    uniformRowSampleProbability
  calc
    ∑ samples : RowTrace m (steps + 1),
        uniformRowTraceProbMass samples *
          F (Fin.init samples) (samples (Fin.last steps))
        = ∑ p : RowSample m × RowTrace m steps,
            uniformRowTraceProbMass (Fin.snoc p.2 p.1) *
              F p.2 p.1 := by
            symm
            refine Fintype.sum_equiv e
              (fun p : RowSample m × RowTrace m steps =>
                uniformRowTraceProbMass (Fin.snoc p.2 p.1) * F p.2 p.1)
              (fun samples : RowTrace m (steps + 1) =>
                uniformRowTraceProbMass samples *
                  F (Fin.init samples) (samples (Fin.last steps))) ?_
            intro p
            have hp :
                ((Fin.snocEquiv
                    (fun _ : Fin (steps + 1) => RowSample m)) p) =
                  Fin.snoc p.2 p.1 := by
              rfl
            rw [hp]
            simp [Fin.init_snoc, Fin.snoc_last]
    _ = ∑ p : RowSample m × RowTrace m steps,
          (uniformRowTraceProbMass p.2 * uniformRowProb p.1) *
            F p.2 p.1 := by
            apply Finset.sum_congr rfl
            intro p _
            rw [uniformRowTraceProbMass_snoc]
    _ = ∑ pref : RowTrace m steps,
          uniformRowTraceProbMass pref *
            (∑ lastSample : RowSample m,
              uniformRowProb lastSample * F pref lastSample) := by
            rw [Fintype.sum_prod_type_right]
            apply Finset.sum_congr rfl
            intro pref _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro lastSample _
            ring

/-- One-step Tropp trace-MGF domination specialized to one coordinate of the
iid uniform row trace law. -/
theorem uniformRowTraceProbability_expectationReal_trace_normed_exp_add_step_le
    {m steps : ℕ} (hm : 0 < m) (t0 : Fin steps)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H)
    {X : RowSample m → CStarMatrix ι ι ℂ}
    (hX : ∀ i, IsSelfAdjoint (X i)) :
    (uniformRowTraceProbability (steps := steps) hm).expectationReal
      (fun samples =>
        (cstarMatrixTrace
          (NormedSpace.exp (H + X (samples t0)))).re) ≤
    (cstarMatrixTrace
      (NormedSpace.exp
        (H + CFC.log
          ((uniformRowSampleProbability hm).expectationCStarMatrix
            (fun i => NormedSpace.exp (X i)))))).re := by
  let P := uniformRowTraceProbability (steps := steps) hm
  have hbase :=
    FiniteProbability.expectationReal_trace_normed_exp_add_le
      P hH (X := fun samples => X (samples t0))
      (fun samples => hX (samples t0))
  have hmean :
      P.expectationCStarMatrix
        (fun samples => NormedSpace.exp (X (samples t0))) =
      (uniformRowSampleProbability hm).expectationCStarMatrix
        (fun i => NormedSpace.exp (X i)) :=
    uniformRowTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation
      hm t0 (fun i => NormedSpace.exp (X i))
  simpa [P, hmean] using hbase

/-- Iterated iid trace-MGF domination for the uniform row product trace law. -/
theorem uniformRowTraceProbability_expectationReal_trace_normed_exp_add_sum_le
    {m steps : ℕ} (hm : 0 < m)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H)
    {X : RowSample m → CStarMatrix ι ι ℂ}
    (hX : ∀ i, IsSelfAdjoint (X i)) :
    (uniformRowTraceProbability (steps := steps) hm).expectationReal
      (fun samples =>
        (cstarMatrixTrace
          (NormedSpace.exp
            (H + ∑ t : Fin steps, X (samples t)))).re) ≤
    (cstarMatrixTrace
      (NormedSpace.exp
        (H + ∑ _t : Fin steps,
          CFC.log
            ((uniformRowSampleProbability hm).expectationCStarMatrix
              (fun i => NormedSpace.exp (X i)))))).re := by
  classical
  induction steps generalizing H with
  | zero =>
      exact le_of_eq (by
        simpa using
          (FiniteProbability.expectationReal_const
            (uniformRowTraceProbability (steps := 0) hm)
            ((cstarMatrixTrace (NormedSpace.exp H)).re)))
  | succ steps ih =>
      let K : CStarMatrix ι ι ℂ :=
        CFC.log
          ((uniformRowSampleProbability hm).expectationCStarMatrix
            (fun i => NormedSpace.exp (X i)))
      have hsplit :
          (uniformRowTraceProbability (steps := steps + 1) hm).expectationReal
            (fun samples =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  (H + ∑ t : Fin (steps + 1), X (samples t)))).re) =
          (uniformRowTraceProbability (steps := steps) hm).expectationReal
            (fun pref =>
              (uniformRowSampleProbability hm).expectationReal
                (fun lastSample =>
                  (cstarMatrixTrace
                    (NormedSpace.exp
                      (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re)) := by
        calc
          (uniformRowTraceProbability (steps := steps + 1) hm).expectationReal
              (fun samples =>
                (cstarMatrixTrace
                  (NormedSpace.exp
                    (H + ∑ t : Fin (steps + 1), X (samples t)))).re)
              =
            (uniformRowTraceProbability (steps := steps + 1) hm).expectationReal
              (fun samples =>
                (cstarMatrixTrace
                  (NormedSpace.exp
                    (H + (∑ t : Fin steps, X (Fin.init samples t) +
                      X (samples (Fin.last steps)))))).re) := by
                apply congrArg
                funext samples
                congr 3
                rw [Fin.sum_univ_castSucc]
                simp [Fin.init]
          _ =
            (uniformRowTraceProbability (steps := steps) hm).expectationReal
              (fun pref =>
                (uniformRowSampleProbability hm).expectationReal
                  (fun lastSample =>
                    (cstarMatrixTrace
                      (NormedSpace.exp
                        (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re)) := by
              simpa using
                uniformRowTraceProbability_expectationReal_succ_last_eq
                  hm
                  (fun pref lastSample =>
                    (cstarMatrixTrace
                      (NormedSpace.exp
                        (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re)
      have hstep :
          ∀ pref : RowTrace m steps,
            (uniformRowSampleProbability hm).expectationReal
              (fun lastSample =>
                (cstarMatrixTrace
                  (NormedSpace.exp
                    (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re) ≤
            (cstarMatrixTrace
              (NormedSpace.exp
                (H + ∑ t : Fin steps, X (pref t) + K))).re := by
        intro pref
        let Hpref : CStarMatrix ι ι ℂ :=
          H + ∑ t : Fin steps, X (pref t)
        have hHpref : IsSelfAdjoint Hpref := by
          exact hH.add
            (cstarMatrix_finset_sum_isSelfAdjoint
              (s := (Finset.univ : Finset (Fin steps)))
              (F := fun t : Fin steps => X (pref t))
              (fun t _ => hX (pref t)))
        have hbase :=
          FiniteProbability.expectationReal_trace_normed_exp_add_le
            (uniformRowSampleProbability hm) hHpref hX
        simpa [Hpref, K, add_assoc] using hbase
      have hmono :
          (uniformRowTraceProbability (steps := steps) hm).expectationReal
            (fun pref =>
              (uniformRowSampleProbability hm).expectationReal
                (fun lastSample =>
                  (cstarMatrixTrace
                    (NormedSpace.exp
                      (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re)) ≤
          (uniformRowTraceProbability (steps := steps) hm).expectationReal
            (fun pref =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  (H + ∑ t : Fin steps, X (pref t) + K))).re) := by
        apply FiniteProbability.expectationReal_mono
        intro pref
        exact hstep pref
      have hih :
          (uniformRowTraceProbability (steps := steps) hm).expectationReal
            (fun pref =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  ((H + K) + ∑ t : Fin steps, X (pref t)))).re) ≤
          (cstarMatrixTrace
            (NormedSpace.exp
              ((H + K) + ∑ _t : Fin steps, K))).re := by
        have hHK : IsSelfAdjoint (H + K) :=
          hH.add (cstarMatrix_log_isSelfAdjoint _)
        exact ih hHK
      have hrewrite_left :
          (uniformRowTraceProbability (steps := steps) hm).expectationReal
            (fun pref =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  (H + ∑ t : Fin steps, X (pref t) + K))).re) =
          (uniformRowTraceProbability (steps := steps) hm).expectationReal
            (fun pref =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  ((H + K) + ∑ t : Fin steps, X (pref t)))).re) := by
        apply congrArg
        funext pref
        congr 3
        ac_rfl
      have hrewrite_right :
          (cstarMatrixTrace
            (NormedSpace.exp
              ((H + K) + ∑ _t : Fin steps, K))).re =
          (cstarMatrixTrace
            (NormedSpace.exp
              (H + ∑ _t : Fin (steps + 1), K))).re := by
        dsimp [K]
        congr 3
        rw [Fin.sum_univ_castSucc]
        ac_rfl
      calc
        (uniformRowTraceProbability (steps := steps + 1) hm).expectationReal
          (fun samples =>
            (cstarMatrixTrace
              (NormedSpace.exp
                (H + ∑ t : Fin (steps + 1), X (samples t)))).re)
            =
          (uniformRowTraceProbability (steps := steps) hm).expectationReal
            (fun pref =>
              (uniformRowSampleProbability hm).expectationReal
                (fun lastSample =>
                  (cstarMatrixTrace
                    (NormedSpace.exp
                      (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re)) := hsplit
        _ ≤
          (uniformRowTraceProbability (steps := steps) hm).expectationReal
            (fun pref =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  (H + ∑ t : Fin steps, X (pref t) + K))).re) := hmono
        _ =
          (uniformRowTraceProbability (steps := steps) hm).expectationReal
            (fun pref =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  ((H + K) + ∑ t : Fin steps, X (pref t)))).re) := hrewrite_left
        _ ≤
          (cstarMatrixTrace
            (NormedSpace.exp
              ((H + K) + ∑ _t : Fin steps, K))).re := hih
        _ =
          (cstarMatrixTrace
            (NormedSpace.exp
              (H + ∑ _t : Fin (steps + 1), K))).re := hrewrite_right

/-- Real finite-trace version of the iid uniform trace-MGF adapter. -/
theorem uniformRowTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
    {m steps : ℕ} (hm : 0 < m)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : ι → ι → ℝ} (hH : IsSymmetricFiniteMatrix H)
    {X : RowSample m → ι → ι → ℝ}
    (hX : ∀ i, IsSymmetricFiniteMatrix (X i)) :
    (uniformRowTraceProbability (steps := steps) hm).expectationReal
      (fun samples =>
        finiteTrace
          (finiteMatrixExp
            (fun a b : ι => H a b + ∑ t : Fin steps, X (samples t) a b))) ≤
    (cstarMatrixTrace
      (NormedSpace.exp
        (finiteComplexCStarMatrix H + ∑ _t : Fin steps,
          CFC.log
            ((uniformRowSampleProbability hm).expectationCStarMatrix
              (fun i =>
                NormedSpace.exp (finiteComplexCStarMatrix (X i))))))).re := by
  classical
  let P := uniformRowTraceProbability (steps := steps) hm
  let Hc : CStarMatrix ι ι ℂ := finiteComplexCStarMatrix H
  let Xc : RowSample m → CStarMatrix ι ι ℂ :=
    fun i => finiteComplexCStarMatrix (X i)
  have hembed :
      ∀ samples : RowTrace m steps,
        finiteComplexCStarMatrix
          (fun a b : ι => H a b + ∑ t : Fin steps, X (samples t) a b) =
        Hc + ∑ t : Fin steps, Xc (samples t) := by
    intro samples
    calc
      finiteComplexCStarMatrix
          (fun a b : ι => H a b + ∑ t : Fin steps, X (samples t) a b)
          =
        finiteComplexCStarMatrix H +
          finiteComplexCStarMatrix
            (fun a b : ι => ∑ t : Fin steps, X (samples t) a b) := by
            rw [finiteComplexCStarMatrix_add]
      _ = Hc + ∑ t : Fin steps, Xc (samples t) := by
            dsimp [Hc, Xc]
            rw [show
                finiteComplexCStarMatrix
                    (fun a b : ι => ∑ t : Fin steps, X (samples t) a b) =
                  ∑ t : Fin steps,
                    finiteComplexCStarMatrix (X (samples t)) by
              simpa using
                (finiteComplexCStarMatrix_finset_sum
                  (s := (Finset.univ : Finset (Fin steps)))
                  (F := fun t : Fin steps => X (samples t)))]
  have htrace_eq :
      P.expectationReal
        (fun samples =>
          finiteTrace
            (finiteMatrixExp
              (fun a b : ι => H a b + ∑ t : Fin steps, X (samples t) a b))) =
      P.expectationReal
        (fun samples =>
          (cstarMatrixTrace
            (NormedSpace.exp
              (Hc + ∑ t : Fin steps, Xc (samples t)))).re) := by
    unfold P FiniteProbability.expectationReal
    apply Finset.sum_congr rfl
    intro samples _
    have hsample :
        finiteTrace
            (finiteMatrixExp
              (fun a b : ι => H a b + ∑ t : Fin steps, X (samples t) a b)) =
          (cstarMatrixTrace
            (NormedSpace.exp
              (Hc + ∑ t : Fin steps, Xc (samples t)))).re := by
      rw [← cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix_re
        (fun a b : ι => H a b + ∑ t : Fin steps, X (samples t) a b)]
      rw [hembed samples]
    simpa using
      congrArg (fun z => (uniformRowTraceProbability hm).prob samples * z) hsample
  rw [htrace_eq]
  have hHc : IsSelfAdjoint Hc := by
    dsimp [Hc]
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric H hH
  have hXc : ∀ i, IsSelfAdjoint (Xc i) := by
    intro i
    dsimp [Xc]
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric (X i) (hX i)
  simpa [Hc, Xc, P] using
    (uniformRowTraceProbability_expectationReal_trace_normed_exp_add_sum_le
      (steps := steps) hm (H := Hc) hHc (X := Xc) hXc)

/-- Scalar trace-MGF log-bound functional for iid uniform row sampling. -/
noncomputable def uniformRowTraceProbabilityFiniteRealTraceMGFLogBound
    {m steps : ℕ} (hm : 0 < m)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → ι → ℝ)
    (X : RowSample m → ι → ι → ℝ) : ℝ :=
  (cstarMatrixTrace
    (NormedSpace.exp
      (finiteComplexCStarMatrix H + ∑ _t : Fin steps,
          CFC.log
            ((uniformRowSampleProbability hm).expectationCStarMatrix
              (fun i =>
                NormedSpace.exp (finiteComplexCStarMatrix (X i))))))).re

/-- Scalar trace-MGF bound from a one-step logarithmic-CGF Loewner bound for
iid uniform row sampling. -/
theorem uniformRowTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
    {m steps : ℕ} (hm : 0 < m)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : RowSample m → ι → ι → ℝ) {c : ℝ}
    (hK :
      CFC.log
          ((uniformRowSampleProbability hm).expectationCStarMatrix
            (fun i =>
              NormedSpace.exp (finiteComplexCStarMatrix (X i)))) ≤
        (c : ℂ) • (1 : CStarMatrix ι ι ℂ)) :
    uniformRowTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := steps) hm
      (fun _a _b : ι => 0) X ≤
      (Fintype.card ι : ℝ) * Real.exp ((steps : ℝ) * c) := by
  classical
  let K : CStarMatrix ι ι ℂ :=
    CFC.log
      ((uniformRowSampleProbability hm).expectationCStarMatrix
        (fun i =>
          NormedSpace.exp (finiteComplexCStarMatrix (X i))))
  have hKsa : IsSelfAdjoint K := by
    dsimp [K]
    exact cstarMatrix_log_isSelfAdjoint _
  have hsumsa :
      IsSelfAdjoint
        (finiteComplexCStarMatrix (fun _a _b : ι => 0) +
          ∑ _t : Fin steps, K) := by
    have hzero : IsSelfAdjoint (finiteComplexCStarMatrix (fun _a _b : ι => 0)) := by
      rw [finiteComplexCStarMatrix_zero]
      simp
    exact hzero.add
      (cstarMatrix_finset_sum_isSelfAdjoint
        (s := (Finset.univ : Finset (Fin steps)))
        (F := fun _t : Fin steps => K)
        (fun _t _ht => hKsa))
  have hsumLe :
      finiteComplexCStarMatrix (fun _a _b : ι => 0) + ∑ _t : Fin steps, K ≤
        (((steps : ℝ) * c : ℝ) : ℂ) • (1 : CStarMatrix ι ι ℂ) := by
    rw [finiteComplexCStarMatrix_zero, zero_add]
    have hsum :
        (∑ _t : Fin steps, K) ≤
          ∑ _t : Fin steps, ((c : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
      exact Finset.sum_le_sum (fun _t _ht => by simpa [K] using hK)
    refine hsum.trans ?_
    rw [cstarMatrix_fin_sum_const_complex_smul_one]
    simp [mul_comm]
  simpa [uniformRowTraceProbabilityFiniteRealTraceMGFLogBound, K] using
    cstarMatrixTrace_normedSpace_exp_re_le_card_mul_exp_of_le_real_smul_one
      hsumsa hsumLe

/-- Product-law scalar trace-MGF bound for centered uniform row covariance
increments under a deterministic row-norm/Loewner bound. -/
theorem uniformRowTraceProbabilityFiniteRealTraceMGFLogBound_centered_le
    {m n s : ℕ} {theta L : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    (hLpos : 0 < L) (htheta : 0 ≤ theta)
    (hrow : ∀ i : RowSample m, (m : ℝ) * rowNormSq U i ≤ L)
    (hY :
      ∀ i : RowSample m,
        finiteLoewnerLe
          (fun j k : Fin n => uniformRowOuterGramSample U i j k)
          (fun j k : Fin n => L * finiteIdMatrix j k)) :
    let beta : ℝ :=
      (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    uniformRowTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) hm
      (fun _a _b : Fin n => 0)
      (fun i j k =>
        theta * (uniformRowOuterGramSample U i j k - finiteIdMatrix j k)) ≤
      (n : ℝ) * Real.exp ((s : ℝ) * (beta * (L ^ 2 + 1))) := by
  classical
  intro beta
  let X : RowSample m → Fin n → Fin n → ℝ :=
    fun i j k => uniformRowOuterGramSample U i j k - finiteIdMatrix j k
  have hlog :
      CFC.log
          ((uniformRowSampleProbability hm).expectationCStarMatrix
            (fun i : RowSample m =>
              NormedSpace.exp
                (theta • finiteComplexCStarMatrix (X i) :
                  CStarMatrix (Fin n) (Fin n) ℂ))) ≤
        (((beta * (L ^ 2 + 1) : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
    simpa [beta, X] using
      uniformRowOuterGramSample_centered_log_cgf_le_scalar_of_forall_rowNorm_bound
        U hU hm hLpos htheta hrow hY
  have hK :
      CFC.log
          ((uniformRowSampleProbability hm).expectationCStarMatrix
            (fun i : RowSample m =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun j k : Fin n => theta * X i j k)))) ≤
        (((beta * (L ^ 2 + 1) : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
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
    exact hlog
  have hbound :=
    uniformRowTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) hm
      (fun (i : RowSample m) (j k : Fin n) => theta * X i j k)
      hK
  simpa [X, beta, Fintype.card_fin] using hbound

/-- Product-law scalar trace-MGF bound for negative centered uniform row
covariance increments under a deterministic row-norm/Loewner bound. -/
theorem uniformRowTraceProbabilityFiniteRealTraceMGFLogBound_neg_centered_le
    {m n s : ℕ} {theta L : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    (htheta : 0 ≤ theta)
    (hrow : ∀ i : RowSample m, (m : ℝ) * rowNormSq U i ≤ L)
    (hY :
      ∀ i : RowSample m,
        finiteLoewnerLe
          (fun j k : Fin n => uniformRowOuterGramSample U i j k)
          (fun j k : Fin n => L * finiteIdMatrix j k)) :
    let beta : ℝ := Real.exp theta - theta - 1
    uniformRowTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) hm
      (fun _a _b : Fin n => 0)
      (fun i j k =>
        (-theta) * (uniformRowOuterGramSample U i j k - finiteIdMatrix j k)) ≤
      (n : ℝ) * Real.exp ((s : ℝ) * (beta * (L ^ 2 + 1))) := by
  classical
  intro beta
  let X : RowSample m → Fin n → Fin n → ℝ :=
    fun i j k => uniformRowOuterGramSample U i j k - finiteIdMatrix j k
  have hlog :
      CFC.log
          ((uniformRowSampleProbability hm).expectationCStarMatrix
            (fun i : RowSample m =>
              NormedSpace.exp
                (theta •
                  (-finiteComplexCStarMatrix (X i)) :
                  CStarMatrix (Fin n) (Fin n) ℂ))) ≤
        (((beta * (L ^ 2 + 1) : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
    simpa [beta, X] using
      uniformRowOuterGramSample_neg_centered_log_cgf_le_scalar_of_forall_rowNorm_bound
        U hU hm htheta hrow hY
  have hK :
      CFC.log
          ((uniformRowSampleProbability hm).expectationCStarMatrix
            (fun i : RowSample m =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun j k : Fin n => (-theta) * X i j k)))) ≤
        (((beta * (L ^ 2 + 1) : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n) (Fin n) ℂ)) := by
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
    exact hlog
  have hbound :=
    uniformRowTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) hm
      (fun (i : RowSample m) (j k : Fin n) => (-theta) * X i j k)
      hK
  simpa [X, beta, Fintype.card_fin] using hbound

/-- One-sided upper-tail high-probability Loewner bound for the uniform
sample-average Gram error. -/
theorem uniformRowTraceProbability_eventProb_uniformRowSampleGram_finiteLoewnerLe_upper_lt_ge_one_sub_exp
    {m n s : ℕ} {theta ε L : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta) (hLpos : 0 < L)
    (hrow : ∀ i : RowSample m, (m : ℝ) * rowNormSq U i ≤ L)
    (hY :
      ∀ i : RowSample m,
        finiteLoewnerLe
          (fun j k : Fin n => uniformRowOuterGramSample U i j k)
          (fun j k : Fin n => L * finiteIdMatrix j k)) :
    let beta : ℝ :=
      (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    1 -
      Real.exp (-(theta * (s : ℝ) * ε)) *
        ((n : ℝ) * Real.exp ((s : ℝ) * (beta * (L ^ 2 + 1)))) ≤
      (uniformRowTraceProbability (steps := s) hm).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              uniformRowSampleGram U samples j k - finiteIdMatrix j k)
            (fun j k : Fin n => ε * finiteIdMatrix j k)} := by
  classical
  intro beta
  let P := uniformRowTraceProbability (steps := s) hm
  let T : ℝ := theta * (s : ℝ) * ε
  let X : RowSample m → Fin n → Fin n → ℝ :=
    fun i j k => theta * (uniformRowOuterGramSample U i j k - finiteIdMatrix j k)
  let M : RowTrace m s → Fin n → Fin n → ℝ :=
    fun samples j k => ∑ t : Fin s, X (samples t) j k
  let GoodEig : Set (RowTrace m s) :=
    {samples |
      ∀ a : Fin n,
        finiteHermitianEigenvalues (M samples)
          (by
            intro j k
            dsimp [M, X]
            apply Finset.sum_congr rfl
            intro t _
            have hsym :=
              uniformRowOuterGramSample_centered_symmetric U (samples t) j k
            change
              theta *
                  (uniformRowOuterGramSample U (samples t) j k -
                    finiteIdMatrix j k) =
                theta *
                  (uniformRowOuterGramSample U (samples t) k j -
                    finiteIdMatrix k j)
            simpa using congrArg (fun x => theta * x) hsym)
          a < T}
  let GoodLoewner : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          uniformRowSampleGram U samples j k - finiteIdMatrix j k)
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  have hM : ∀ samples, IsSymmetricFiniteMatrix (M samples) := by
    intro samples j k
    dsimp [M, X]
    apply Finset.sum_congr rfl
    intro t _
    have hsym := uniformRowOuterGramSample_centered_symmetric U (samples t) j k
    change
      theta *
          (uniformRowOuterGramSample U (samples t) j k -
            finiteIdMatrix j k) =
        theta *
          (uniformRowOuterGramSample U (samples t) k j -
            finiteIdMatrix k j)
    simpa using congrArg (fun x => theta * x) hsym
  have hzeroSym :
      IsSymmetricFiniteMatrix (fun _a _b : Fin n => 0) := by
    intro j k
    rfl
  have hXsym : ∀ i : RowSample m, IsSymmetricFiniteMatrix (X i) := by
    intro i j k
    dsimp [X]
    have hsym := uniformRowOuterGramSample_centered_symmetric U i j k
    change
      theta * (uniformRowOuterGramSample U i j k - finiteIdMatrix j k) =
        theta * (uniformRowOuterGramSample U i k j - finiteIdMatrix k j)
    simpa using congrArg (fun x => theta * x) hsym
  have hTraceLog :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (M samples))) ≤
        uniformRowTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) hm
          (fun _a _b : Fin n => 0)
          X := by
    have h :=
      uniformRowTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
        (steps := s) hm hzeroSym hXsym
    simpa [P, M, X, uniformRowTraceProbabilityFiniteRealTraceMGFLogBound]
      using h
  have hTraceScalar :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (M samples))) ≤
        (n : ℝ) * Real.exp ((s : ℝ) * (beta * (L ^ 2 + 1))) := by
    exact hTraceLog.trans
      (by
        simpa [X, beta] using
          uniformRowTraceProbabilityFiniteRealTraceMGFLogBound_centered_le
            (s := s) U hU hm hLpos (le_of_lt htheta) hrow hY)
  have hEigProb :
      1 -
        Real.exp (-T) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (beta * (L ^ 2 + 1)))) ≤
        P.eventProb GoodEig := by
    simpa [P, GoodEig, M, T, beta] using
      FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound
        (P := P) (M := M) hM T
        ((n : ℝ) * Real.exp ((s : ℝ) * (beta * (L ^ 2 + 1))))
        hTraceScalar
  have hsubset : GoodEig ⊆ GoodLoewner := by
    intro samples hsamples
    have hEig : ∀ a : Fin n, finiteHermitianEigenvalues (M samples) (hM samples) a ≤ T := by
      intro a
      exact le_of_lt (by simpa [GoodEig, M, T] using hsamples a)
    have hLoM :
        finiteLoewnerLe (M samples)
          (fun j k : Fin n => T * finiteIdMatrix j k) :=
      finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le
        (M samples) (hM samples) hEig
    let E : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram U samples j k - finiteIdMatrix j k
    have hM_eq :
        M samples = fun j k : Fin n => (theta * (s : ℝ)) * E j k := by
      ext j k
      have hcenter :=
        uniformRowSampleGram_sub_finiteIdMatrix_eq_centered_average
          U hs samples j k
      have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
      dsimp [M, X, E]
      calc
        ∑ t : Fin s,
            theta *
              (uniformRowOuterGramSample U (samples t) j k - finiteIdMatrix j k)
            =
          theta * ∑ t : Fin s,
            (uniformRowOuterGramSample U (samples t) j k - finiteIdMatrix j k) := by
            rw [Finset.mul_sum]
        _ =
          theta * (s : ℝ) *
            ((∑ t : Fin s,
              (uniformRowOuterGramSample U (samples t) j k - finiteIdMatrix j k)) /
                (s : ℝ)) := by
            field_simp [hs_ne]
        _ = theta * (s : ℝ) *
            (uniformRowSampleGram U samples j k - finiteIdMatrix j k) := by
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

/-- One-sided lower-tail high-probability Loewner bound for the uniform
sample-average Gram error, written as `-(G-I) <= ε I`. -/
theorem uniformRowTraceProbability_eventProb_uniformRowSampleGram_finiteLoewnerLe_lower_lt_ge_one_sub_exp
    {m n s : ℕ} {theta ε L : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta)
    (hrow : ∀ i : RowSample m, (m : ℝ) * rowNormSq U i ≤ L)
    (hY :
      ∀ i : RowSample m,
        finiteLoewnerLe
          (fun j k : Fin n => uniformRowOuterGramSample U i j k)
          (fun j k : Fin n => L * finiteIdMatrix j k)) :
    let beta : ℝ := Real.exp theta - theta - 1
    1 -
      Real.exp (-(theta * (s : ℝ) * ε)) *
        ((n : ℝ) * Real.exp ((s : ℝ) * (beta * (L ^ 2 + 1)))) ≤
      (uniformRowTraceProbability (steps := s) hm).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(uniformRowSampleGram U samples j k - finiteIdMatrix j k))
            (fun j k : Fin n => ε * finiteIdMatrix j k)} := by
  classical
  intro beta
  let P := uniformRowTraceProbability (steps := s) hm
  let T : ℝ := theta * (s : ℝ) * ε
  let Xneg : RowSample m → Fin n → Fin n → ℝ :=
    fun i j k => (-theta) * (uniformRowOuterGramSample U i j k - finiteIdMatrix j k)
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
              uniformRowOuterGramSample_centered_symmetric U (samples t) j k
            change
              (-theta) *
                  (uniformRowOuterGramSample U (samples t) j k -
                    finiteIdMatrix j k) =
                (-theta) *
                  (uniformRowOuterGramSample U (samples t) k j -
                    finiteIdMatrix k j)
            simpa using congrArg (fun x => (-theta) * x) hsym)
          a < T}
  let GoodLoewner : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(uniformRowSampleGram U samples j k - finiteIdMatrix j k))
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  have hMneg : ∀ samples, IsSymmetricFiniteMatrix (Mneg samples) := by
    intro samples j k
    dsimp [Mneg, Xneg]
    apply Finset.sum_congr rfl
    intro t _
    have hsym := uniformRowOuterGramSample_centered_symmetric U (samples t) j k
    change
      (-theta) *
          (uniformRowOuterGramSample U (samples t) j k -
            finiteIdMatrix j k) =
        (-theta) *
          (uniformRowOuterGramSample U (samples t) k j -
            finiteIdMatrix k j)
    simpa using congrArg (fun x => (-theta) * x) hsym
  have hzeroSym :
      IsSymmetricFiniteMatrix (fun _a _b : Fin n => 0) := by
    intro j k
    rfl
  have hXnegSym : ∀ i : RowSample m, IsSymmetricFiniteMatrix (Xneg i) := by
    intro i j k
    dsimp [Xneg]
    have hsym := uniformRowOuterGramSample_centered_symmetric U i j k
    change
      (-theta) * (uniformRowOuterGramSample U i j k - finiteIdMatrix j k) =
        (-theta) * (uniformRowOuterGramSample U i k j - finiteIdMatrix k j)
    simpa using congrArg (fun x => (-theta) * x) hsym
  have hTraceLog :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (Mneg samples))) ≤
        uniformRowTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) hm
          (fun _a _b : Fin n => 0)
          Xneg := by
    have h :=
      uniformRowTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
        (steps := s) hm hzeroSym hXnegSym
    simpa [P, Mneg, Xneg, uniformRowTraceProbabilityFiniteRealTraceMGFLogBound]
      using h
  have hTraceScalar :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (Mneg samples))) ≤
        (n : ℝ) * Real.exp ((s : ℝ) * (beta * (L ^ 2 + 1))) := by
    exact hTraceLog.trans
      (by
        simpa [Xneg, beta] using
          uniformRowTraceProbabilityFiniteRealTraceMGFLogBound_neg_centered_le
            (s := s) U hU hm (le_of_lt htheta) hrow hY)
  have hEigProb :
      1 -
        Real.exp (-T) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (beta * (L ^ 2 + 1)))) ≤
        P.eventProb GoodEig := by
    simpa [P, GoodEig, Mneg, T, beta] using
      FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound
        (P := P) (M := Mneg) hMneg T
        ((n : ℝ) * Real.exp ((s : ℝ) * (beta * (L ^ 2 + 1))))
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
      fun j k => -(uniformRowSampleGram U samples j k - finiteIdMatrix j k)
    have hM_eq :
        Mneg samples = fun j k : Fin n => (theta * (s : ℝ)) * Eneg j k := by
      ext j k
      have hcenter :=
        uniformRowSampleGram_sub_finiteIdMatrix_eq_centered_average
          U hs samples j k
      have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
      dsimp [Mneg, Xneg, Eneg]
      calc
        ∑ t : Fin s,
            (-theta) *
              (uniformRowOuterGramSample U (samples t) j k - finiteIdMatrix j k)
            =
          (-theta) * ∑ t : Fin s,
            (uniformRowOuterGramSample U (samples t) j k - finiteIdMatrix j k) := by
            rw [Finset.mul_sum]
        _ =
          theta * (s : ℝ) *
            (-((∑ t : Fin s,
              (uniformRowOuterGramSample U (samples t) j k - finiteIdMatrix j k)) /
                (s : ℝ))) := by
            field_simp [hs_ne]
        _ = theta * (s : ℝ) *
            (-(uniformRowSampleGram U samples j k - finiteIdMatrix j k)) := by
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

/-- Two-sided high-probability finite-Loewner form for iid uniform row
sampling under a deterministic row-norm/Loewner bound. -/
theorem uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_exp
    {m n s : ℕ} {theta ε L : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta) (hLpos : 0 < L)
    (hrow : ∀ i : RowSample m, (m : ℝ) * rowNormSq U i ≤ L)
    (hY :
      ∀ i : RowSample m,
        finiteLoewnerLe
          (fun j k : Fin n => uniformRowOuterGramSample U i j k)
          (fun j k : Fin n => L * finiteIdMatrix j k)) :
    let betaUpper : ℝ :=
      (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let betaLower : ℝ := Real.exp theta - theta - 1
    let tailUpper : ℝ :=
      Real.exp (-(theta * (s : ℝ) * ε)) *
        ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
    let tailLower : ℝ :=
      Real.exp (-(theta * (s : ℝ) * ε)) *
        ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
    1 - (tailUpper + tailLower) ≤
      (uniformRowTraceProbability (steps := s) hm).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              uniformRowSampleGram U samples j k - finiteIdMatrix j k)
            (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(uniformRowSampleGram U samples j k - finiteIdMatrix j k))
            (fun j k : Fin n => ε * finiteIdMatrix j k)} := by
  classical
  intro betaUpper betaLower tailUpper tailLower
  let P := uniformRowTraceProbability (steps := s) hm
  let EU : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          uniformRowSampleGram U samples j k - finiteIdMatrix j k)
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  let EL : Set (RowTrace m s) :=
    {samples |
      finiteLoewnerLe
        (fun j k : Fin n =>
          -(uniformRowSampleGram U samples j k - finiteIdMatrix j k))
        (fun j k : Fin n => ε * finiteIdMatrix j k)}
  have hEU : 1 - tailUpper ≤ P.eventProb EU := by
    simpa [P, EU, betaUpper, tailUpper] using
      uniformRowTraceProbability_eventProb_uniformRowSampleGram_finiteLoewnerLe_upper_lt_ge_one_sub_exp
        (s := s) (theta := theta) (ε := ε) (L := L)
        U hU hm hs htheta hLpos hrow hY
  have hEL : 1 - tailLower ≤ P.eventProb EL := by
    simpa [P, EL, betaLower, tailLower] using
      uniformRowTraceProbability_eventProb_uniformRowSampleGram_finiteLoewnerLe_lower_lt_ge_one_sub_exp
        (s := s) (theta := theta) (ε := ε) (L := L)
        U hU hm hs htheta hrow hY
  have hinter :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P EU EL
      tailUpper tailLower hEU hEL
  exact le_trans (by rfl) (by
    simpa [P, EU, EL, tailUpper, tailLower] using hinter)

/-- Delta-budget corollary for the two-sided uniform row sample-average Gram
concentration theorem. -/
theorem uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget
    {m n s : ℕ} {theta ε δ L : ℝ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta) (hLpos : 0 < L)
    (hrow : ∀ i : RowSample m, (m : ℝ) * rowNormSq U i ≤ L)
    (hY :
      ∀ i : RowSample m,
        finiteLoewnerLe
          (fun j k : Fin n => uniformRowOuterGramSample U i j k)
          (fun j k : Fin n => L * finiteIdMatrix j k))
    (hbudget :
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δ) :
    1 - δ ≤
      (uniformRowTraceProbability (steps := s) hm).eventProb
        {samples |
          finiteLoewnerLe
            (fun j k : Fin n =>
              uniformRowSampleGram U samples j k - finiteIdMatrix j k)
            (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
          finiteLoewnerLe
            (fun j k : Fin n =>
              -(uniformRowSampleGram U samples j k - finiteIdMatrix j k))
            (fun j k : Fin n => ε * finiteIdMatrix j k)} := by
  classical
  let betaUpper : ℝ :=
    (Real.exp (theta * L) - theta * L - 1) / L ^ 2
  let betaLower : ℝ := Real.exp theta - theta - 1
  let tailUpper : ℝ :=
    Real.exp (-(theta * (s : ℝ) * ε)) *
      ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
  let tailLower : ℝ :=
    Real.exp (-(theta * (s : ℝ) * ε)) *
      ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
  have hhp :=
    uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_exp
      (s := s) (theta := theta) (ε := ε) (L := L)
      U hU hm hs htheta hLpos hrow hY
  have hbudget' : tailUpper + tailLower ≤ δ := by
    simpa [betaUpper, betaLower, tailUpper, tailLower] using hbudget
  exact (sub_le_sub_left hbudget' 1).trans
    (by simpa [betaUpper, betaLower, tailUpper, tailLower] using hhp)

end NumStability
