import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalErrorBounds
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Algorithms.NormEstimation.OneNorm.GeneralIndex
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalEstimator.OneNorm

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

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




namespace NumStability

open scoped BigOperators

namespace NormEstimator

-- ============================================================
-- Part A.  Generic one-norm / inf-norm over an arbitrary Fintype index
-- ============================================================































































-- ============================================================
-- Part A.2  Bridges: generic norms vs. the repository `Fin n` norms
-- ============================================================






























-- ============================================================
-- Part A.3  Reindexing invariance under a Fintype equivalence
-- ============================================================




































-- ============================================================
-- Part B.  The one-norm condition estimator on a general-index matrix
-- ============================================================





















































-- ============================================================
-- Part C.1  The equation (14.1) norm identity for a general index
-- ============================================================































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























































end NormEstimator

end NumStability
