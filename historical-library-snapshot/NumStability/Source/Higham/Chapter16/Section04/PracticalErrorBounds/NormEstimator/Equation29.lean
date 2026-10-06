import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalErrorBounds
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalEstimator.OneNorm
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Analysis.MatrixAlgebra

/-!
# Source.Higham.Chapter16.Section04.PracticalErrorBounds.NormEstimator.Equation29

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
