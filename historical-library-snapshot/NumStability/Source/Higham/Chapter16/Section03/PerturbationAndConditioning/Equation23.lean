import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.FirstOrder
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.Separation
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.StructuredSylvester
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Analysis.MatrixAlgebra

/-!
# Source.Higham.Chapter16.Section03.PerturbationAndConditioning.Equation23

W05 semantic leaf. Declaration commands are copied byte-identically from the frozen C0004 owners.
-/

-- Algorithms/Sylvester/Higham16Psi.lean
--
-- Concrete realizations of the structured Sylvester condition number Psi for
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 16.3, equations (16.23)-(16.24).
--
-- The certificate predicate `SylvesterPsiFirstOrderBound` (in
-- `SylvesterPerturbation.lean`) is the theorem-facing form of the (16.24)
-- structured first-order bound: a real `Psi` that dominates the structured
-- inverse first-order Sylvester perturbation map, so that the printed relative
-- bound (16.23) `||dX||_F / ||X||_F <= sqrt 3 * Psi * eps` follows through
-- `sylvester_relative_first_order_bound_of_psi`.
--
-- This file constructs concrete `Psi` witnesses that INSTANTIATE that
-- predicate:
--
--   * `sylvesterPsi_of_inverseOpBound` / `_isPsiFirstOrderBound` -- the honest
--     GENERAL certificate instantiation.  Higham writes
--     `Psi = ||P^{-1}[ alpha (X^T kron I) - beta (I kron X) - gamma I ]||_2 / ||vec X||_2`
--     where `P = I kron A - B^T kron I`.  The exact operator-norm construction
--     of `||P^{-1}||` from `A, B` needs an SVD / operator-norm API that is not
--     present here, so we take the inverse-operator Frobenius bound `M`
--     (an upper bound on `||P^{-1}||_2`, i.e. `1 / sep(A,B)`) as SUPPLIED data,
--     exactly as the book writes `Psi` in terms of `||P^{-1}||`.  From `M` we
--     build the closed-form `Psi = M * ((alpha + beta) * ||X||_F + gamma) / ||X||_F`
--     and prove it satisfies the certificate.
--
--   * `sylvesterPsiDiagonal` / `_isPsiFirstOrderBound` -- the concrete DIAGONAL
--     case.  With `A = diag a`, `B = diag b` and an entrywise separation lower
--     bound `s <= |a_i - b_j|` (so `s > 0` is a lower bound on `sep` and
--     `1/s` bounds every entry of the explicit inverse
--     `sylvesterDiagonalVecCoeffInv`, whose entries are `(a_i - b_j)^{-1}`),
--     the inverse-operator bound `M = 1/s` is explicit, and
--     `sylvesterPsiDiagonal = (1/s) * ((alpha + beta) * ||X||_F + gamma) / ||X||_F`.
--     This closes (16.24) for the diagonalizable / distinct-eigenvalue case
--     that the diagonal foundation of `Higham16.lean` already covers.
--
--   * `H16_eq16_24_structured_condition_diagonal` -- the labeled (16.24)/(16.23)
--     wrapper tying the diagonal `Psi` to the printed relative first-order
--     perturbation bound via `sylvester_relative_first_order_bound_of_psi`.
--
-- Honest scope.  The DIAGONAL witness is fully self-contained (no supplied
-- operator-norm data beyond the entrywise separation `s`, which is elementary
-- for diagonal matrices).  It therefore covers exactly the case where `A` and
-- `B` are diagonal with separated diagonal entries -- i.e. the diagonalizable
-- Sylvester operator with distinct eigenvalues expressed in eigencoordinates.
-- The GENERAL witness takes the `||P^{-1}||`-type bound `M` as data, matching
-- how Higham states `Psi`; instantiating `M` for a nondiagonal `A, B` from the
-- entries of `A, B` alone is precisely the missing SVD/operator-norm step.




namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- Triple-norm single-block bounds (from eq (16.23))
-- ============================================================




























































































-- ============================================================
-- Linearized right-hand side bound (from eq (16.22))
-- ============================================================



















































/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the `dA / alpha` block bound. -/
alias H16_eq16_23_frobNorm_le_alpha_mul_tripleNorm :=
  frobNorm_le_alpha_mul_tripleNorm

/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the `dB / beta` block bound. -/
alias H16_eq16_23_frobNorm_le_beta_mul_tripleNorm :=
  frobNorm_le_beta_mul_tripleNorm

/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the `dC / gamma` block bound. -/
alias H16_eq16_23_frobNorm_le_gamma_mul_tripleNorm :=
  frobNorm_le_gamma_mul_tripleNorm

/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the first-order Sylvester right-hand-side
    Frobenius bound. -/
alias H16_eq16_23_sylvester_first_order_rhs_frobNorm_le :=
  sylvester_first_order_rhs_frobNorm_le

-- ============================================================
-- General certificate instantiation from a supplied inverse-operator bound
-- (eq (16.24), the `||P^{-1}||`-structured Psi taken as data)
-- ============================================================


















































































































































































































/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the sep-lower-bound first-order Sylvester endpoint. -/
theorem H16_eq16_23_sylvester_first_order_bound_of_sepLowerBound (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A B sigma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX <=
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvester_first_order_bound_of_sepLowerBound n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma
      halpha hbeta hgamma hsigma hX hSep hLin

/-- Higham, 2nd ed., Section 16.3, equation (16.23):
    source-numbered alias for the exact-infimum first-order Sylvester endpoint. -/
theorem H16_eq16_23_sylvester_first_order_bound_of_pos_le_sylvesterSepInf (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A B)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX <=
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvester_first_order_bound_of_pos_le_sylvesterSepInf n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma
      halpha hbeta hgamma hsigma hX hle hLin











































































































































































-- ============================================================
-- Diagonal-case Psi realization (eq (16.24), diagonal / distinct-eigenvalue)
-- ============================================================























































































-- ============================================================
-- Labeled (16.24)/(16.23) wrapper for the diagonal case
-- ============================================================
























































































end NumStability
-- Algorithms/Sylvester/SylvesterPerturbation.lean
--
-- Perturbation theory for the Sylvester equation (Higham §15.3).
-- Eqs 15.22-15.28: linearized perturbation equation, first-order
-- perturbation bound, a posteriori error bound, and Lyapunov specialization.












namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- Linearized perturbation equation (§15.3, eq 15.22)
-- ============================================================














































-- ============================================================
-- Structured first-order condition-number surface (§16.3, eqs 16.23-16.24)
-- ============================================================







































































































/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-numbered aliases for the primitive structured Sylvester first-order
    condition-number surface. -/
noncomputable abbrev H16_eq16_23_sylvesterScaledPerturbationTripleNorm :=
  sylvesterScaledPerturbationTripleNorm

alias H16_eq16_23_sylvesterScaledPerturbationTripleNorm_le_sqrt_three_mul :=
  sylvesterScaledPerturbationTripleNorm_le_sqrt_three_mul




alias H16_eq16_23_sylvester_relative_first_order_bound_of_psi :=
  sylvester_relative_first_order_bound_of_psi

-- ============================================================
-- Lyapunov first-order condition-number surface (§16.3, eq 16.27)
-- ============================================================








































































































-- ============================================================
-- First-order perturbation bound (§15.3, eq 15.25)
-- ============================================================











































































-- ============================================================
-- A posteriori error bound (§15.3, eq 15.28)
-- ============================================================











































-- ============================================================
-- Lyapunov perturbation (§15.3, eq 15.27)
-- ============================================================

































-- ============================================================
-- Relative perturbation bound (§15.3, eq 15.25 relative form)
-- ============================================================




















































end NumStability
