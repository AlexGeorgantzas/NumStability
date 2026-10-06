-- Algorithms/RandNLA/RowSamplingLeverage.lean
--
-- Leverage-score row-sampling consequences for Algorithm 2 of
-- Drineas--Mahoney's CACM RandNLA survey.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.RandNLA.RowSamplingGram

namespace NumStability

open scoped BigOperators

/-!
## Algorithm 2 with leverage-score probabilities

Equation (6) in Drineas--Mahoney defines the row-sampling probabilities by
applying the norm-squared row distribution to an orthonormal-column matrix
`U` spanning the column space of `A`:

`p_i = ||U_i*||_2^2 / ∑_r ||U_r*||_2^2 = ||U_i*||_2^2 / n`.

This file keeps Algorithm 2's sampled sketch and Gram-matrix machinery from
`RowSampling.lean` and `RowSamplingGram.lean`, specializing it to such `U`.
The equation (7) result is stated in vector-action form,
`||Mx||₂ ≤ c ||x||₂` for all `x`, which is the operator-2-norm inequality
without introducing a separate supremum-valued spectral norm.
-/

-- ============================================================
-- Leverage-score probabilities: equation (6)
-- ============================================================

/-- Rectangular orthonormal-column condition: `UᵀU = I`. -/
def HasOrthonormalColumns {m n : ℕ} (U : Fin m → Fin n → ℝ) : Prop :=
  ∀ j k : Fin n, ∑ i : Fin m, U i j * U i k = if j = k then 1 else 0

/-- The leverage score of row `i`, `||U_i*||₂²`. -/
noncomputable def leverageScore {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (i : Fin m) : ℝ :=
  rowNormSq U i

/-- Equation (6) leverage-score row probability.

This is definitionally the existing norm-squared row probability applied to
the orthonormal-column basis `U`; the orthonormality theorem below rewrites
the denominator as `n`. -/
noncomputable def leverageScoreProb {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (i : Fin m) : ℝ :=
  rowSqNormProb U i

/-- The Gram matrix of an orthonormal-column matrix is the identity. -/
theorem rowGram_eq_id_of_orthonormal_columns {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U) :
    rowGram U = idMatrix n := by
  ext j k
  exact hU j k

/-- Multiplying an arbitrary coefficient vector by a matrix with orthonormal
    columns preserves the Euclidean squared norm. -/
theorem hasOrthonormalColumns_vecNorm2Sq_mul_vec_eq
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (q : Fin n → ℝ) :
    vecNorm2Sq (fun k : Fin m => ∑ j : Fin n, U k j * q j) =
      vecNorm2Sq q := by
  classical
  unfold vecNorm2Sq
  calc
    (∑ k : Fin m, (∑ j : Fin n, U k j * q j) ^ 2)
        = ∑ k : Fin m, ∑ j : Fin n, ∑ l : Fin n,
            (U k j * U k l) * (q j * q l) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [pow_two]
          have h := Finset.sum_mul_sum
            (s := (Finset.univ : Finset (Fin n)))
            (t := (Finset.univ : Finset (Fin n)))
            (f := fun j => U k j * q j)
            (g := fun l => U k l * q l)
          simpa [mul_assoc, mul_left_comm, mul_comm] using h
    _ = ∑ j : Fin n, ∑ l : Fin n,
          (∑ k : Fin m, U k j * U k l) * (q j * q l) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _
          rw [← Finset.sum_mul]
    _ = ∑ j : Fin n, ∑ l : Fin n,
          (if j = l then 1 else 0) * (q j * q l) := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro l _
          rw [hU j l]
    _ = ∑ j : Fin n, q j ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          simp [pow_two]

/-- The same orthonormal-column isometry written with the repository's
`rectMatMulVec` notation. -/
theorem hasOrthonormalColumns_vecNorm2Sq_rectMatMulVec_eq
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (q : Fin n → ℝ) :
    vecNorm2Sq (rectMatMulVec U q) = vecNorm2Sq q := by
  simpa [rectMatMulVec] using
    hasOrthonormalColumns_vecNorm2Sq_mul_vec_eq U hU q

/-- The transpose action of a matrix with orthonormal columns is a contraction
    in Euclidean squared norm.

This is the deterministic linear-algebra dependency needed to package the
signed-Hadamard row-norm Lipschitz constant used in Tropp's SRHT proof route. -/
theorem hasOrthonormalColumns_transpose_mul_vecNorm2Sq_le
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (z : Fin m → ℝ) :
    vecNorm2Sq (fun j : Fin n => ∑ k : Fin m, z k * U k j) ≤
      vecNorm2Sq z := by
  classical
  let q : Fin n → ℝ := fun j => ∑ k : Fin m, z k * U k j
  let u : Fin m → ℝ := fun k => ∑ j : Fin n, U k j * q j
  have hu_norm : vecNorm2Sq u = vecNorm2Sq q := by
    simpa [u] using hasOrthonormalColumns_vecNorm2Sq_mul_vec_eq U hU q
  have hinner : (∑ k : Fin m, z k * u k) = vecNorm2Sq q := by
    calc
      (∑ k : Fin m, z k * u k)
          = ∑ k : Fin m, ∑ j : Fin n, z k * (U k j * q j) := by
              apply Finset.sum_congr rfl
              intro k _
              simp [u, Finset.mul_sum]
      _ = ∑ j : Fin n, ∑ k : Fin m, z k * (U k j * q j) := by
              rw [Finset.sum_comm]
      _ = ∑ j : Fin n, (∑ k : Fin m, z k * U k j) * q j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = ∑ j : Fin n, q j * q j := by
              apply Finset.sum_congr rfl
              intro j _
              simp [q]
      _ = vecNorm2Sq q := by
              unfold vecNorm2Sq
              apply Finset.sum_congr rfl
              intro j _
              ring
  have hcs := vecInnerProduct_sq_le z u
  have hsq : vecNorm2Sq q ^ 2 ≤ vecNorm2Sq z * vecNorm2Sq q := by
    simpa [hinner, hu_norm] using hcs
  have hq_nonneg : 0 ≤ vecNorm2Sq q := vecNorm2Sq_nonneg q
  by_cases hq_zero : vecNorm2Sq q = 0
  · simpa [q, hq_zero] using vecNorm2Sq_nonneg z
  · have hq_pos : 0 < vecNorm2Sq q := lt_of_le_of_ne hq_nonneg (Ne.symm hq_zero)
    have hdiv := div_le_div_of_nonneg_right hsq (le_of_lt hq_pos)
    have hcancel_left : vecNorm2Sq q ^ 2 / vecNorm2Sq q = vecNorm2Sq q := by
      field_simp [hq_zero]
    have hcancel_right :
        (vecNorm2Sq z * vecNorm2Sq q) / vecNorm2Sq q = vecNorm2Sq z := by
      field_simp [hq_zero]
    simpa [q, hcancel_left, hcancel_right] using hdiv

/-- Every row of an orthonormal-column matrix has squared norm at most one. -/
theorem rowNormSq_le_one_of_hasOrthonormalColumns
    {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (i : Fin m) :
    rowNormSq U i ≤ 1 := by
  classical
  let z : Fin m → ℝ := fun k => if k = i then 1 else 0
  have hcontract :=
    hasOrthonormalColumns_transpose_mul_vecNorm2Sq_le U hU z
  have hleft :
      vecNorm2Sq (fun j : Fin n => ∑ k : Fin m, z k * U k j) =
        rowNormSq U i := by
    unfold vecNorm2Sq rowNormSq
    apply Finset.sum_congr rfl
    intro j _
    have hsum : (∑ k : Fin m, z k * U k j) = U i j := by
      simp [z]
    change (∑ k : Fin m, z k * U k j) ^ 2 = U i j ^ 2
    rw [hsum]
  have hright : vecNorm2Sq z = 1 := by
    unfold vecNorm2Sq
    simp [z]
  simpa [hleft, hright] using hcontract

/-- For an orthonormal-column `m × n` matrix, the squared Frobenius norm is
    `n`, the number of columns. -/
theorem rowSqNormProbDen_eq_nat_of_orthonormal_columns {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U) :
    rowSqNormProbDen U = (n : ℝ) := by
  unfold rowSqNormProbDen frobNormSqRect
  calc
    ∑ i : Fin m, ∑ j : Fin n, U i j ^ 2
        = ∑ j : Fin n, ∑ i : Fin m, U i j ^ 2 := by
            rw [Finset.sum_comm]
    _ = ∑ j : Fin n, ∑ i : Fin m, U i j * U i j := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ∑ j : Fin n, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro j _
            simpa using hU j j
    _ = (n : ℝ) := by
            simp

/-- The leverage-score denominator is positive when `n > 0`. -/
theorem rowSqNormProbDen_pos_of_orthonormal_columns {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) :
    0 < rowSqNormProbDen U := by
  rw [rowSqNormProbDen_eq_nat_of_orthonormal_columns U hU]
  exact_mod_cast hn

/-- Equation (6) in denominator-`n` form:
    `p_i = ||U_i*||₂² / n`. -/
theorem leverageScoreProb_eq_rowNormSq_div_nat {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (i : Fin m) :
    leverageScoreProb U i = leverageScore U i / (n : ℝ) := by
  unfold leverageScoreProb leverageScore rowSqNormProb
  rw [rowSqNormProbDen_eq_nat_of_orthonormal_columns U hU]

/-- Leverage-score probabilities sum to one. -/
theorem leverageScoreProb_sum_eq_one {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) :
    ∑ i : Fin m, leverageScoreProb U i = 1 := by
  unfold leverageScoreProb
  exact rowSqNormProb_sum_eq_one U
    (ne_of_gt (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn))

/-- Canonical independent Algorithm 2 trace law for equation (6). -/
noncomputable def leverageTraceProbability {m n steps : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) : FiniteProbability (RowTrace m steps) :=
  rowSqNormTraceProbability U
    (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn)

-- ============================================================
-- One-step rank-one facts for source-sharp equation (7) concentration
-- ============================================================

/-- One-step leverage outer-product estimators are positive semidefinite.

This is one of the local side conditions needed to instantiate a
rank-one matrix Chernoff/Bernstein theorem such as Oliveira's Lemma 1 in the
proof of the sharper sampled-Gram bound behind CACM equation (7). -/
theorem leverage_rowOuterGramSample_finitePSD {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) (i : Fin m) :
    finitePSD (fun j k : Fin n => rowOuterGramSample U i j k) := by
  exact finitePSD_rowOuterGramSample U
    (rowSqNormProbDen_pos_of_orthonormal_columns U hU hn) i

/-- Under leverage probabilities, the one-step row outer-product estimator has
    expectation `I`.

This is the exact `E[YYᵀ] = I` hypothesis in Oliveira's bounded rank-one
concentration lemma, specialized to an orthonormal-column basis `U`. -/
theorem leverage_rowOuterGramSample_mean_eq_id {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) (j k : Fin n) :
    ∑ i : Fin m, leverageScoreProb U i * rowOuterGramSample U i j k =
      idMatrix n j k := by
  have hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  have hmean := rowOuterGramSample_mean_eq_rowGram U hden j k
  simpa [leverageScoreProb, rowGram_eq_id_of_orthonormal_columns U hU] using hmean

/-- Under leverage probabilities, each one-step row outer-product estimator is
    bounded above by `n I` in Loewner order.

Equivalently, for every test vector `x`,
`xᵀ (u_i u_iᵀ / p_i) x ≤ n ||x||₂²`.  This is the local `|Y|² ≤ n`
boundedness condition for the source-sharp rank-one concentration route behind
CACM equation (7). -/
theorem leverage_rowOuterGramSample_finiteLoewnerLe_nat {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) (i : Fin m) :
    finiteLoewnerLe
      (fun j k : Fin n => rowOuterGramSample U i j k)
      (fun j k : Fin n => (n : ℝ) * finiteIdMatrix j k) := by
  classical
  intro x
  have hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  by_cases hpzero : rowSqNormProb U i = 0
  · have hzero := rowOuterGramSample_eq_zero_of_prob_zero U hden i hpzero
    have hleft :
        finiteQuadraticForm
            (fun j k : Fin n => rowOuterGramSample U i j k) x = 0 := by
      simp [hzero, finiteQuadraticForm, finiteMatVec]
    rw [hleft, finiteQuadraticForm_smul_finiteIdMatrix]
    exact mul_nonneg (Nat.cast_nonneg n) (finiteVecNorm2Sq_nonneg x)
  · have hp_nonneg : 0 ≤ rowSqNormProb U i := rowSqNormProb_nonneg U hden i
    have hprob : 0 < rowSqNormProb U i :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hrow_pos : 0 < rowNormSq U i := by
      unfold rowSqNormProb at hprob
      exact (div_pos_iff_of_pos_right hden).mp hprob
    have hprob_eq : rowSqNormProb U i = rowNormSq U i / (n : ℝ) := by
      unfold rowSqNormProb
      rw [rowSqNormProbDen_eq_nat_of_orthonormal_columns U hU]
    have hinner :
        (∑ j : Fin n, U i j * x j) ^ 2 ≤
          rowNormSq U i * finiteVecNorm2Sq x := by
      simpa [rowNormSq, finiteVecNorm2Sq, vecNorm2Sq] using
        vecInnerProduct_sq_le (fun j : Fin n => U i j) x
    rw [finiteQuadraticForm_rowOuterGramSample_eq_sq_div U i hprob x]
    rw [finiteQuadraticForm_smul_finiteIdMatrix]
    calc
      (∑ j : Fin n, U i j * x j) ^ 2 / rowSqNormProb U i
          ≤ (rowNormSq U i * finiteVecNorm2Sq x) /
              rowSqNormProb U i := by
            exact div_le_div_of_nonneg_right hinner hp_nonneg
      _ = (n : ℝ) * finiteVecNorm2Sq x := by
            rw [hprob_eq]
            field_simp [hrow_pos.ne', hnR]

-- ============================================================
-- Equation (7): exact arithmetic
-- ============================================================

/-- Exact equation (7), stated as an operator-2-norm bound in vector-action
    form. The proof reuses the equation (5) Frobenius high-probability theorem
    for norm-squared row sampling, applied to the orthonormal-column matrix
    `U`, and then uses `||M||₂ ≤ ||M||_F`.

The event says that the exact sampled sketch satisfies
`||(ŨᵀŨ - I)x||₂ ≤ ε ||x||₂` for every vector `x`. -/
theorem leverageTraceProbability_eventProb_rowSampleGram_opNorm2_error_le_epsilon
    {m n : ℕ} {s : ℕ} (U : Fin m → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (hn : 0 < n)
    (hs : 0 < (s : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * (ε / (n : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          opNorm2Le
            (fun j k => rowSampleGram s U samples j k - idMatrix n j k)
            ε} := by
  classical
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let η : ℝ := ε / (n : ℝ)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hη : 0 < η := div_pos hε (by exact_mod_cast hn)
  have hden_eq : rowSqNormProbDen U = (n : ℝ) :=
    rowSqNormProbDen_eq_nat_of_orthonormal_columns U hU
  have hgram : rowGram U = idMatrix n :=
    rowGram_eq_id_of_orthonormal_columns U hU
  have hscale : η * rowSqNormProbDen U = ε := by
    simp [η, hden_eq, hnR]
  let P := leverageTraceProbability (steps := s) U hU hn
  let E : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => rowSampleGram s U samples j k - rowGram U j k) ≤
          η * rowSqNormProbDen U}
  let F : Set (RowTrace m s) :=
    {samples |
      opNorm2Le
        (fun j k => rowSampleGram s U samples j k - idMatrix n j k) ε}
  have hbase :
      1 - 1 / ((s : ℝ) * η ^ 2) ≤
        P.eventProb E := by
    simpa [P, E, leverageTraceProbability] using
      rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon
        (A := U) hden hs η hη
  have hsubset : E ⊆ F := by
    intro samples hsamples
    have hsamples' :
        frobNorm
          (fun j k => rowSampleGram s U samples j k - rowGram U j k) ≤
            η * rowSqNormProbDen U := by
      simpa [E] using hsamples
    have hFrob :
        frobNorm
          (fun j k => rowSampleGram s U samples j k - idMatrix n j k) ≤
            ε := by
      simpa [hgram, hscale] using hsamples'
    exact opNorm2Le_of_frobNorm_le
      (fun j k => rowSampleGram s U samples j k - idMatrix n j k) hFrob
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

-- ============================================================
-- Floating-point leverage-score stability and equation (7)
-- ============================================================

/-- Deterministic fully floating-point Gram perturbation bound for Algorithm 2
    under the leverage-score distribution. This is the stability component used
    in the floating-point equation (7) corollary. -/
theorem leverage_fl_rowSampleGramDot_perturb_bound
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (samples : RowTrace m s) (hgood : rowTracePositiveProb U samples) :
    frobNorm
      (fun j k =>
        fl_rowSampleGramDot fp s U samples j k -
          rowSampleGram s U samples j k) ≤
      rowSampleGramFullFpPerturbBudget fp s U := by
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  have hentry :
      ∀ t j,
        |fl_rowSampleSketch fp s U samples t j -
          rowSampleSketch s U samples t j| ≤
          |rowSampleSketch s U samples t j| * fp.u := by
    intro t j
    have hprob : 0 < rowSqNormProb U (samples t) := hgood t
    exact fl_rowSampleSketch_error_bound fp s U samples t j
      (rowSampleScaleDen_ne_zero s U (samples t) hs hprob)
  exact fl_rowSampleGramDot_perturb_bound_of_entrywise
    fp U hden hs hγ samples hentry

/-- Deterministic fully floating-point Gram perturbation bound for Algorithm 2
    under the leverage-score distribution, including computed row-scale
    denominators. -/
theorem leverage_fl_rowSampleGramDotWithComputedDen_perturb_bound
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb U))
    (samples : RowTrace m s) (hgood : rowTracePositiveProb U samples) :
    frobNorm
      (fun j k =>
        fl_rowSampleGramDotWithComputedDen fp U dhat.den samples j k -
          rowSampleGram s U samples j k) ≤
      rowSampleGramComputedDenFullFpPerturbBudget fp s U dhat := by
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  exact fl_rowSampleGramDotWithComputedDen_perturb_bound
    fp U hden hs hγ dhat samples hgood

/-- Fully floating-point equation (7), in vector-action operator-2 form.

With the same probability as the exact equation (7) Frobenius argument, the
computed Gram matrix formed by rounded row scaling and the library's
floating-point dot product satisfies

`||(fl(ŨᵀŨ) - I)x||₂ ≤ (ε + τ_full) ||x||₂`

for every vector `x`, where
`τ_full = rowSampleGramFullFpPerturbBudget fp s U`. -/
theorem leverageTraceProbability_eventProb_fl_rowSampleGramDot_opNorm2_error_le_epsilon_add_budget
    (fp : FPModel) {m n : ℕ} {s : ℕ}
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (hn : 0 < n) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    {ε : ℝ} (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * (ε / (n : ℝ)) ^ 2) ≤
      (leverageTraceProbability (steps := s) U hU hn).eventProb
        {samples |
          opNorm2Le
            (fun j k => fl_rowSampleGramDot fp s U samples j k -
              idMatrix n j k)
            (ε + rowSampleGramFullFpPerturbBudget fp s U)} := by
  classical
  let hden : 0 < rowSqNormProbDen U :=
    rowSqNormProbDen_pos_of_orthonormal_columns U hU hn
  let η : ℝ := ε / (n : ℝ)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hη : 0 < η := div_pos hε (by exact_mod_cast hn)
  have hden_eq : rowSqNormProbDen U = (n : ℝ) :=
    rowSqNormProbDen_eq_nat_of_orthonormal_columns U hU
  have hgram : rowGram U = idMatrix n :=
    rowGram_eq_id_of_orthonormal_columns U hU
  have hscale :
      η * rowSqNormProbDen U +
          rowSampleGramFullFpPerturbBudget fp s U =
        ε + rowSampleGramFullFpPerturbBudget fp s U := by
    simp [η, hden_eq, hnR]
  let P := leverageTraceProbability (steps := s) U hU hn
  let E : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => fl_rowSampleGramDot fp s U samples j k -
          rowGram U j k) ≤
        η * rowSqNormProbDen U +
          rowSampleGramFullFpPerturbBudget fp s U}
  let F : Set (RowTrace m s) :=
    {samples |
      opNorm2Le
        (fun j k => fl_rowSampleGramDot fp s U samples j k -
          idMatrix n j k)
        (ε + rowSampleGramFullFpPerturbBudget fp s U)}
  have hbase :
      1 - 1 / ((s : ℝ) * η ^ 2) ≤
        P.eventProb E := by
    simpa [P, E, leverageTraceProbability] using
      rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget
        fp (A := U) hden hs hγ η hη
  have hsubset : E ⊆ F := by
    intro samples hsamples
    have hsamples' :
        frobNorm
          (fun j k => fl_rowSampleGramDot fp s U samples j k -
            rowGram U j k) ≤
          η * rowSqNormProbDen U +
            rowSampleGramFullFpPerturbBudget fp s U := by
      simpa [E] using hsamples
    have hFrob :
        frobNorm
          (fun j k => fl_rowSampleGramDot fp s U samples j k -
            idMatrix n j k) ≤
          ε + rowSampleGramFullFpPerturbBudget fp s U := by
      simpa [hgram, hscale] using hsamples'
    exact opNorm2Le_of_frobNorm_le
      (fun j k => fl_rowSampleGramDot fp s U samples j k - idMatrix n j k)
      hFrob
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

end NumStability
