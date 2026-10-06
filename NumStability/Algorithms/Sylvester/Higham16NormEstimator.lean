-- Algorithms/Sylvester/Higham16NormEstimator.lean
--
-- Higham, 2nd ed., Chapter 16.4, equation (16.29): the LAPACK-style condition
-- estimator path for the Sylvester practical error bound.
--
-- Higham (16.29), p.315, replaces the exact componentwise inverse budget
-- `‖ |P^{-1}| (|Rhat| + Ru) ‖` (the max-entry norm of the (16.29) practical
-- budget vector) by a *condition estimator*: the norm-1 estimator of
-- Hager/Higham (LAPACK's xLACON kernel, Algorithm 14.4), which produces a
-- COMPUTABLE quantity `gamma`.  The honest content is that xLACON returns a
-- guaranteed LOWER bound `gamma <= (true norm)`; the algorithm can
-- underestimate, so `gamma` is NOT a guaranteed upper bound on the condition
-- term.  This file proves exactly that:
--
--   * the single-column probe never exceeds the true one-norm
--     (`oneNormGColumn_le_oneNormG`), the elementary "estimator <= true norm"
--     fact underlying every one-norm estimator;
--   * the LAPACK estimator value transported onto the vectorized Sylvester
--     inverse is a proven lower bound on the true (16.29) practical budget
--     (`sylvesterVecCoeff_lapack_condEstimate_le_practicalBudget`), via the
--     eq (14.1) identity `‖ |A^{-1}| d ‖ = ‖ A^{-1} D ‖`;
--   * the (16.29) practical relative error bound stated together with the
--     estimator, honestly labeled as using a computable lower bound on the
--     condition term (`sylvester_practical_error_bound_with_norm1_estimator`).
--
-- Import-only: builds on the closed Chapter 16 (16.29) infrastructure in
-- `Higham16.lean` and the proved one-norm estimator in `CondEstimation.lean`.

import NumStability.Algorithms.Sylvester.Higham16
import NumStability.Algorithms.CondEstimation

namespace NumStability

open scoped BigOperators

namespace NormEstimator

-- ============================================================
-- Part A.  Generic one-norm / inf-norm over an arbitrary Fintype index
-- ============================================================

/-- The one-norm (maximum absolute column sum) of a square matrix indexed by an
    arbitrary finite type.  This is the general-index analogue of the repository
    `oneNorm` (Higham §6.3), needed because the vectorized Sylvester coefficient
    is indexed by the product type `Fin n × Fin m` rather than `Fin N`. -/
noncomputable def oneNormG {ι : Type*} [Fintype ι] (M : ι → ι → Real) : Real :=
  norm (fun j => ∑ i : ι, |M i j|)

/-- The inf-norm (maximum absolute row sum) of a square matrix indexed by an
    arbitrary finite type; the general-index analogue of the repository
    `infNorm` (Higham §6.3). -/
noncomputable def infNormG {ι : Type*} [Fintype ι] (M : ι → ι → Real) : Real :=
  norm (fun i => ∑ j : ι, |M i j|)

/-- Higham §6.3: the one-norm is nonnegative. -/
lemma oneNormG_nonneg {ι : Type*} [Fintype ι] (M : ι → ι → Real) :
    0 <= oneNormG M := by
  unfold oneNormG; exact norm_nonneg _

/-- Higham §6.3: the inf-norm is nonnegative. -/
lemma infNormG_nonneg {ι : Type*} [Fintype ι] (M : ι → ι → Real) :
    0 <= infNormG M := by
  unfold infNormG; exact norm_nonneg _

/-- Higham §6.3 / Algorithm 14.3: a single-column probe of the one-norm never
    exceeds the true one-norm.  The `j`-th column sum `∑_i |M_ij|` is exactly
    `‖M e_j‖₁`; taking the max over columns can only increase it.  This is the
    elementary lower-bound property behind *every* one-norm estimator: probing a
    subset of columns can never overshoot the maximum. -/
lemma oneNormGColumn_le_oneNormG {ι : Type*} [Fintype ι]
    (M : ι → ι → Real) (j : ι) :
    (∑ i : ι, |M i j|) <= oneNormG M := by
  unfold oneNormG
  have hnn : 0 <= ∑ i : ι, |M i j| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h := norm_le_pi_norm (fun j => ∑ i : ι, |M i j|) j
  rw [Real.norm_eq_abs, abs_of_nonneg hnn] at h
  exact h

/-- Higham §6.3: the inf-norm is bounded above by any uniform row-sum bound. -/
lemma infNormG_le_of_row_sum_le {ι : Type*} [Fintype ι]
    (M : ι → ι → Real) {c : Real}
    (hrows : forall i : ι, (∑ j : ι, |M i j|) <= c) (hc : 0 <= c) :
    infNormG M <= c := by
  unfold infNormG
  rw [pi_norm_le_iff_of_nonneg hc]
  intro i
  have hnn : 0 <= ∑ j : ι, |M i j| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hrows i

/-- Higham §6.3: every row sum is bounded by the inf-norm. -/
lemma row_sum_le_infNormG {ι : Type*} [Fintype ι]
    (M : ι → ι → Real) (i : ι) :
    (∑ j : ι, |M i j|) <= infNormG M := by
  unfold infNormG
  have hnn : 0 <= ∑ j : ι, |M i j| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h := norm_le_pi_norm (fun i => ∑ j : ι, |M i j|) i
  rw [Real.norm_eq_abs, abs_of_nonneg hnn] at h
  exact h

-- ============================================================
-- Part A.2  Bridges: generic norms vs. the repository `Fin n` norms
-- ============================================================

/-- On `Fin n` the general-index inf-norm coincides with the repository
    `infNorm` (Mathlib's `linfty_opNorm`).  Both are the maximum absolute row
    sum. -/
lemma infNormG_eq_infNorm {n : Nat} (M : Fin n → Fin n → Real) :
    infNormG M = infNorm M := by
  apply le_antisymm
  · apply infNormG_le_of_row_sum_le
    · intro i; exact row_sum_le_infNorm M i
    · exact infNorm_nonneg M
  · apply infNorm_le_of_row_sum_le
    · intro i; exact row_sum_le_infNormG M i
    · exact infNormG_nonneg M

/-- On `Fin n` the general-index one-norm coincides with the repository
    `oneNorm`.  Both are the maximum absolute column sum, expressed through the
    inf-norm of the transpose (`oneNorm A = infNorm Aᵀ`, Higham §6.3). -/
lemma oneNormG_eq_oneNorm {n : Nat} (M : Fin n → Fin n → Real) :
    oneNormG M = oneNorm M := by
  have h : oneNormG M = infNormG (fun i j => M j i) := by
    unfold oneNormG infNormG; rfl
  rw [h, infNormG_eq_infNorm, oneNorm_eq_infNorm_transpose]

/-- The general-index one-norm as an inf-norm of the transpose (matching the
    repository `oneNorm A = infNorm Aᵀ`). -/
lemma oneNormG_eq_infNormG_transpose {ι : Type*} [Fintype ι]
    (M : ι → ι → Real) :
    oneNormG M = infNormG (fun i j => M j i) := by
  unfold oneNormG infNormG; rfl

-- ============================================================
-- Part A.3  Reindexing invariance under a Fintype equivalence
-- ============================================================

/-- The finite sup-norm of a vector is invariant under reindexing its domain by
    an equivalence.  Used to transport product-indexed data to `Fin N`. -/
lemma pi_norm_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : ι → Real) :
    norm f = norm (fun k => f (e.symm k)) := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    have h := norm_le_pi_norm (fun k => f (e.symm k)) (e i)
    simpa using h
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro k
    have h := norm_le_pi_norm f (e.symm k)
    simpa using h

/-- The general-index inf-norm is invariant under reindexing the matrix by an
    equivalence.  Reindexing permutes the row sums (via `Equiv.sum_comp`) and
    permutes which row attains the maximum (via `pi_norm_comp_equiv`). -/
lemma infNormG_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : ι → ι → Real) :
    infNormG M = infNormG (fun a b : κ => M (e.symm a) (e.symm b)) := by
  unfold infNormG
  rw [pi_norm_comp_equiv e (fun i => ∑ j : ι, |M i j|)]
  congr 1
  ext a
  exact (Equiv.sum_comp e.symm (fun j => |M (e.symm a) j|)).symm

/-- The general-index one-norm is invariant under reindexing by an
    equivalence. -/
lemma oneNormG_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : ι → ι → Real) :
    oneNormG M = oneNormG (fun a b : κ => M (e.symm a) (e.symm b)) := by
  rw [oneNormG_eq_infNormG_transpose, oneNormG_eq_infNormG_transpose]
  exact infNormG_reindex e (fun i j => M j i)

-- ============================================================
-- Part B.  The one-norm condition estimator on a general-index matrix
-- ============================================================

/-- Higham, 2nd ed., Algorithm 14.4 (LAPACK's `xLACON` kernel), applied to a
    square matrix indexed by an arbitrary nonempty finite type.  The matrix is
    reindexed onto `Fin (card ι)` by the canonical `Fintype.equivFin`, and the
    proved `Fin n` LAPACK estimator `lapackNormEstimator` is run there.  This is
    the computable norm-1 condition estimator used by the practical error
    bound. -/
noncomputable def lapackNormEstimatorG {ι : Type*} [Fintype ι]
    (hι : 0 < Fintype.card ι) (M : ι → ι → Real) : Real :=
  let e := Fintype.equivFin ι
  lapackNormEstimator hι (fun a b : Fin (Fintype.card ι) => M (e.symm a) (e.symm b))

/-- **Estimator lower-bound guarantee** (Higham, Algorithm 14.4).

    The general-index LAPACK norm-1 estimator returns a computable quantity that
    never exceeds the true one-norm: `lapackNormEstimatorG M <= ‖M‖₁`.  This is
    the HONEST content — the estimator gives a guaranteed *lower* bound and may
    underestimate; it is not a guaranteed upper bound. -/
theorem lapackNormEstimatorG_le_oneNormG {ι : Type*} [Fintype ι]
    (hι : 0 < Fintype.card ι) (M : ι → ι → Real) :
    lapackNormEstimatorG hι M <= oneNormG M := by
  unfold lapackNormEstimatorG
  set e := Fintype.equivFin ι with he
  have hbound :=
    lapackNormEstimator_lower_bound hι
      (fun a b : Fin (Fintype.card ι) => M (e.symm a) (e.symm b))
  rw [oneNormG_reindex e M]
  rw [oneNormG_eq_oneNorm
      (fun a b : Fin (Fintype.card ι) => M (e.symm a) (e.symm b))]
  exact hbound

/-- Predicate: `gamma` is a computable *lower* bound on the true one-norm of
    `M`.  This is precisely what a norm-1 condition estimator (Hager/Higham
    LACON, Algorithm 14.4) certifies; it captures the honest guarantee and,
    crucially, does NOT assert any upper bound.  Higham (16.29) uses such an
    estimator in place of the exact condition term. -/
def IsOneNormLowerEstimate {ι : Type*} [Fintype ι]
    (M : ι → ι → Real) (gamma : Real) : Prop :=
  gamma <= oneNormG M

/-- The LAPACK estimator supplies a one-norm lower estimate. -/
theorem lapackNormEstimatorG_isOneNormLowerEstimate {ι : Type*} [Fintype ι]
    (hι : 0 < Fintype.card ι) (M : ι → ι → Real) :
    IsOneNormLowerEstimate M (lapackNormEstimatorG hι M) :=
  lapackNormEstimatorG_le_oneNormG hι M

/-- A single-column probe supplies a one-norm lower estimate (Higham §6.3 /
    Algorithm 14.3): `‖M e_j‖₁ = ∑_i |M_ij| <= ‖M‖₁`. -/
theorem columnProbe_isOneNormLowerEstimate {ι : Type*} [Fintype ι]
    (M : ι → ι → Real) (j : ι) :
    IsOneNormLowerEstimate M (∑ i : ι, |M i j|) :=
  oneNormGColumn_le_oneNormG M j

-- ============================================================
-- Part C.1  The equation (14.1) norm identity for a general index
-- ============================================================

/-- **Norm identity** (Higham, 2nd ed., §14.1, equation (14.1)), general index.

    For a nonnegative weight vector `d`, the max-entry norm of the componentwise
    product `|M| d` equals the inf-norm of the scaled matrix `M · diag(d)`:
      `‖ |M| d ‖_∞ = ‖ M D ‖_∞`.
    This reduces the componentwise inverse budget (which needs `|M|`) to a
    matrix-norm estimation problem (which needs only `M D`), the step that lets
    the one-norm estimator drive the (16.29) budget. -/
theorem condNormIdentityG {ι : Type*} [Fintype ι]
    (M : ι → ι → Real) (d : ι → Real) (hd : forall i, 0 <= d i) :
    norm (fun i => ∑ j : ι, |M i j| * d j) =
      infNormG (fun i j => M i j * d j) := by
  unfold infNormG
  congr 1
  ext i
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_mul, abs_of_nonneg (hd j)]

/-- The one-norm of `(M · diag(d))ᵀ` equals the max-entry norm of `|M| d` for
    nonnegative `d`.  This is the estimator-facing form of equation (14.1): the
    one-norm estimator applied to `(M D)ᵀ` targets exactly the componentwise
    inverse-budget norm `‖ |M| d ‖_∞`. -/
theorem oneNormG_transpose_scaled_eq_absBudget {ι : Type*} [Fintype ι]
    (M : ι → ι → Real) (d : ι → Real) (hd : forall i, 0 <= d i) :
    oneNormG (fun a b => (fun i j => M i j * d j) b a) =
      norm (fun i => ∑ j : ι, |M i j| * d j) := by
  rw [oneNormG_eq_infNormG_transpose]
  rw [condNormIdentityG M d hd]

-- ============================================================
-- Part C.2  Sylvester (16.29): the estimator lower-bounds the practical budget
-- ============================================================

/-- Positive cardinality of the vectorized Sylvester product index. -/
lemma card_prod_fin_pos {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    0 < Fintype.card (Prod (Fin n) (Fin m)) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  exact Nat.mul_pos hn hm

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    the componentwise residual weight `d_q = |vec(Rhat)_q| + vec(Ru)_q` that the
    (16.29) practical budget multiplies against `|P^{-1}|`.  It is nonnegative
    whenever the residual-rounding budget `Ru` is. -/
noncomputable def sylvesterResidualWeight (m n : Nat)
    (Rhat Ru : RMatFn m n) : Prod (Fin n) (Fin m) → Real :=
  fun q => |Matrix.vec Rhat q| + Matrix.vec Ru q

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): the residual weight
    `|vec(Rhat)| + vec(Ru)` is nonnegative whenever `Ru` is. -/
lemma sylvesterResidualWeight_nonneg (m n : Nat)
    (Rhat Ru : RMatFn m n) (hRu : forall i j, 0 <= Ru i j) :
    forall q, 0 <= sylvesterResidualWeight m n Rhat Ru q := by
  intro q
  unfold sylvesterResidualWeight
  exact add_nonneg (abs_nonneg _) (by simpa [Matrix.vec] using hRu q.2 q.1)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    the *estimand matrix* for the condition estimator, `(P^{-1} D)ᵀ`, where
    `P = I_n ⊗ A - Bᵀ ⊗ I_m` is the vectorized Sylvester coefficient and
    `D = diag(d)` scales columns by the residual weight `d`.  Running the
    one-norm estimator on this matrix targets exactly the (16.29) budget
    `‖ |P^{-1}| d ‖_∞` via equation (14.1). -/
noncomputable def sylvesterCondEstimatorMatrix (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (Rhat Ru : RMatFn m n) :
    Prod (Fin n) (Fin m) → Prod (Fin n) (Fin m) → Real :=
  fun a b =>
    ((sylvesterVecCoeff m n A B)⁻¹) b a * sylvesterResidualWeight m n Rhat Ru a

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29) + equation (14.1):
    the max-entry norm of the (16.29) practical budget with the exact inverse
    `|P^{-1}|` equals the one-norm of the estimand matrix `(P^{-1} D)ᵀ`. -/
theorem sylvesterPracticalBudget_maxNorm_eq_oneNormG (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (Rhat Ru : RMatFn m n)
    (hRu : forall i j, 0 <= Ru i j) :
    sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) =
      oneNormG (sylvesterCondEstimatorMatrix m n A B Rhat Ru) := by
  -- LHS: the budget vector is `p ↦ ∑_q |P⁻¹_pq| d_q`; equation (14.1) rewrites
  -- its max-entry norm as `infNormG (P⁻¹ D)`.
  have hLHS :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n
            (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) =
        infNormG (fun i j =>
          ((sylvesterVecCoeff m n A B)⁻¹) i j *
            sylvesterResidualWeight m n Rhat Ru j) := by
    unfold sylvesterVecMaxNorm
    have hbudget :
        sylvesterPracticalBudgetVec m n
            (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru =
          fun p => ∑ q : Prod (Fin n) (Fin m),
            |((sylvesterVecCoeff m n A B)⁻¹) p q| *
              sylvesterResidualWeight m n Rhat Ru q := by
      rfl
    rw [hbudget]
    exact condNormIdentityG
      (fun p q => ((sylvesterVecCoeff m n A B)⁻¹) p q)
      (sylvesterResidualWeight m n Rhat Ru)
      (sylvesterResidualWeight_nonneg m n Rhat Ru hRu)
  rw [hLHS, oneNormG_eq_infNormG_transpose]
  unfold sylvesterCondEstimatorMatrix
  rfl

/-- **The condition estimator on the vectorized Sylvester operator**
    (Higham, 2nd ed., Chapter 16.4, equation (16.29); LAPACK `xLACON`).

    The LAPACK norm-1 estimator applied to the estimand matrix `(P^{-1} D)ᵀ`.
    This is the computable quantity that Higham (16.29) uses in place of the
    exact condition term. -/
noncomputable def sylvesterLapackCondEstimate (m n : Nat)
    (hm : 0 < m) (hn : 0 < n)
    (A : RMatFn m m) (B : RMatFn n n) (Rhat Ru : RMatFn m n) : Real :=
  lapackNormEstimatorG (card_prod_fin_pos hm hn)
    (sylvesterCondEstimatorMatrix m n A B Rhat Ru)

/-- **Estimator lower-bound on the (16.29) practical budget**
    (Higham, 2nd ed., Chapter 16.4, equation (16.29); Algorithm 14.4).

    The computable LAPACK norm-1 condition estimate is a guaranteed LOWER bound
    on the exact (16.29) practical budget `‖ |P^{-1}| (|vec(Rhat)| + vec(Ru)) ‖`.
    This is the honest guarantee of the estimator path: `xLACON` returns a
    computable quantity that never *exceeds* the true budget, so it may
    underestimate the condition term and is NOT a guaranteed upper bound.  This
    is exactly Higham's "using a condition estimator" caveat, made precise. -/
theorem sylvesterLapackCondEstimate_le_practicalBudget (m n : Nat)
    (hm : 0 < m) (hn : 0 < n)
    (A : RMatFn m m) (B : RMatFn n n) (Rhat Ru : RMatFn m n)
    (hRu : forall i j, 0 <= Ru i j) :
    sylvesterLapackCondEstimate m n hm hn A B Rhat Ru <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) := by
  unfold sylvesterLapackCondEstimate
  rw [sylvesterPracticalBudget_maxNorm_eq_oneNormG m n A B Rhat Ru hRu]
  exact lapackNormEstimatorG_le_oneNormG (card_prod_fin_pos hm hn)
    (sylvesterCondEstimatorMatrix m n A B Rhat Ru)

/-- The (16.29) practical *relative* budget term
    `‖ |P^{-1}| (|vec(Rhat)| + vec(Ru)) ‖ / ‖Xhat‖` appearing on the right of the
    practical error bound. -/
noncomputable def sylvesterPracticalRelativeBudget (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (Xhat Rhat Ru : RMatFn m n) : Real :=
  sylvesterVecMaxNorm m n
      (sylvesterPracticalBudgetVec m n
        (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
    sylvesterMaxEntryNormRect m n Xhat

/-- The LAPACK condition estimate divided by `‖Xhat‖`, the computable estimator
    proxy for the (16.29) relative practical budget. -/
noncomputable def sylvesterLapackRelativeCondEstimate (n : Nat)
    (hn : 0 < n) (A B Xhat Rhat Ru : RMatFn n n) : Real :=
  sylvesterLapackCondEstimate n n hn hn A B Rhat Ru /
    sylvesterMaxEntryNormRect n n Xhat

-- ============================================================
-- Part C.3  The (16.29) practical error bound WITH the condition estimator
-- ============================================================

/-- **Higham, 2nd ed., Chapter 16.4, equation (16.29): the LAPACK-style
    condition-estimator path for the Sylvester practical error bound.**

    For a square Sylvester system with nonsingular vectorized coefficient
    `P = I_n ⊗ A - Bᵀ ⊗ I_m`, an exact solution `X`, a computed solution `Xhat`,
    and a computed-residual budget certificate `(Rhat, Ru)`, this bundles the two
    halves of Higham's estimator path (16.29), p.315:

    1.  **Guaranteed upper bound** (the practical bound itself):
        the relative max-entry forward error is bounded by the practical budget
        term
          `‖X - Xhat‖ / ‖Xhat‖ <= ‖ |P^{-1}| (|vec(Rhat)| + vec(Ru)) ‖ / ‖Xhat‖`.

    2.  **Estimator = computable LOWER bound on that term** (the caveat):
        the computable LAPACK norm-1 condition estimate never exceeds the exact
        budget term,
          `sylvesterLapackRelativeCondEstimate <= (practical budget term)`.

    Honesty: the estimator supplies a *lower* bound on the condition term, so
    substituting it into the bound can *underestimate* the error — it does NOT
    give a guaranteed upper bound.  This is exactly Higham's warning that a
    condition estimator "can underestimate", stated precisely: the practical
    upper bound (1) is separate from, and always at least as large as, the
    computable estimate (2). -/
theorem sylvester_practical_error_bound_with_norm1_estimator (n : Nat)
    (hn : 0 < n)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    (sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterPracticalRelativeBudget n n A B Xhat Rhat Ru) ∧
    (sylvesterLapackRelativeCondEstimate n hn A B Xhat Rhat Ru <=
      sylvesterPracticalRelativeBudget n n A B Xhat Rhat Ru) := by
  refine ⟨?_, ?_⟩
  · -- (1) The guaranteed practical upper bound (det-nonsingular certificate).
    unfold sylvesterPracticalRelativeBudget
    exact
      sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
        n A B C X Xhat Rhat Ru hdet hX hBudget hXhat
  · -- (2) The estimator is a computable lower bound on the same budget term.
    unfold sylvesterLapackRelativeCondEstimate sylvesterPracticalRelativeBudget
    exact div_le_div_of_nonneg_right
      (sylvesterLapackCondEstimate_le_practicalBudget n n hn hn A B Rhat Ru
        hBudget.1)
      (le_of_lt hXhat)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias for
    the LAPACK-style condition-estimator practical error bound. -/
alias H16_eq16_29_sylvester_practical_error_bound_with_norm1_estimator :=
  sylvester_practical_error_bound_with_norm1_estimator

end NormEstimator

end NumStability
