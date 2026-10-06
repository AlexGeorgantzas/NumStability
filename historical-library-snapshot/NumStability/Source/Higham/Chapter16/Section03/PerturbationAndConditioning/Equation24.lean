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
# Source.Higham.Chapter16.Section03.PerturbationAndConditioning.Equation24

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








































































-- ============================================================
-- General certificate instantiation from a supplied inverse-operator bound
-- (eq (16.24), the `||P^{-1}||`-structured Psi taken as data)
-- ============================================================












/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered abbreviation for the supplied inverse-operator bound
    underlying the structured condition number `Psi`. -/
abbrev H16_eq16_24_SylvesterInverseOpBound :=
  SylvesterInverseOpBound







































/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered abbreviation for the supplied-inverse-bound structured
    condition number value. -/
noncomputable abbrev H16_eq16_24_sylvesterPsi_of_inverseOpBound :=
  sylvesterPsi_of_inverseOpBound





























































































































/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for turning a positive separation lower bound into
    supplied inverse-operator data. -/
alias H16_eq16_24_sylvesterInverseOpBound_of_sepLowerBound :=
  sylvesterInverseOpBound_of_sepLowerBound

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for the supplied-inverse-bound structured
    condition-certificate constructor. -/
alias H16_eq16_24_sylvesterPsi_of_inverseOpBound_isPsiFirstOrderBound :=
  sylvesterPsi_of_inverseOpBound_isPsiFirstOrderBound

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for the sep-lower-bound structured
    condition-certificate constructor. -/
alias H16_eq16_24_sylvesterPsi_of_sepLowerBound_isPsiFirstOrderBound :=
  sylvesterPsi_of_sepLowerBound_isPsiFirstOrderBound

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for the exact-infimum structured
    condition-certificate constructor. -/
alias H16_eq16_24_sylvesterPsi_of_pos_le_sylvesterSepInf_isPsiFirstOrderBound :=
  sylvesterPsi_of_pos_le_sylvesterSepInf_isPsiFirstOrderBound











































/-- Higham, 2nd ed., §16.3, eqs. (16.23)-(16.24) (p. 313):
    sep-based structured first-order perturbation bound. If
    `SepLowerBound A B sigma` holds, then the printed relative bound follows
    with the safe condition-number value
    `sylvesterPsi_of_inverseOpBound ... (1 / sigma)`.

    Scope: this is an exact-arithmetic theorem from a supplied sep lower-bound
    certificate. It does not compute the sharper nondiagonal operator norm
    `||P^{-1}[...]||`. -/
theorem H16_eq16_24_structured_condition_of_sepLowerBound (n : ℕ)
    (A B X ΔA ΔB ΔC ΔX : Fin n → Fin n → ℝ)
    (α β γ sigma ε : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hsigma : 0 < sigma) (hε : 0 ≤ ε)
    (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A B sigma)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔB : frobNorm ΔB ≤ ε * β)
    (hΔC : frobNorm ΔC ≤ ε * γ)
    (hLin : ∀ i j,
      sylvesterOp n A B ΔX i j =
        ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) :
    frobNorm ΔX / frobNorm X ≤
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X α β γ (1 / sigma) * ε := by
  have hPsi :=
    sylvesterPsi_of_sepLowerBound_isPsiFirstOrderBound n A B X α β γ sigma
      hα hβ hγ hsigma hX hSep
  have hΨnn : 0 ≤ sylvesterPsi_of_inverseOpBound n X α β γ (1 / sigma) := by
    unfold sylvesterPsi_of_inverseOpBound
    have hMnn : (0 : ℝ) ≤ 1 / sigma := by positivity
    have hnum : 0 ≤ (α + β) * frobNorm X + γ := by
      have hXnn : 0 ≤ frobNorm X := le_of_lt hX
      nlinarith [le_of_lt hα, le_of_lt hβ, le_of_lt hγ, hXnn]
    positivity
  exact sylvester_relative_first_order_bound_of_psi n
    A B X ΔA ΔB ΔC ΔX α β γ
    (sylvesterPsi_of_inverseOpBound n X α β γ (1 / sigma)) ε
    hPsi hX hΨnn hα hβ hγ hε hΔA hΔB hΔC hLin

/-- Higham, 2nd ed., Section 16.3-16.4, equations (16.23)-(16.24):
    structured first-order perturbation bound from a positive lower bound on
    the exact infimum model of `sep(A,B)`.  This is the same safe Psi value as
    the `SepLowerBound` route, exposed directly through `sylvesterSepInf`.

    Scope: this is an exact-arithmetic lower-bound certificate route. It does
    not assert the sharper displayed nondiagonal operator norm when that norm is
    smaller than the reciprocal sep bound. -/
theorem H16_eq16_24_structured_condition_of_pos_le_sylvesterSepInf (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A B)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_sepLowerBound n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3, equations (16.23)-(16.24):
    sep-based relative first-order Sylvester perturbation bound with the safe
    condition value `sylvesterPsi_of_inverseOpBound ... (1 / sigma)`. -/
theorem sylvester_relative_first_order_bound_of_sepLowerBound (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A B sigma)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_sepLowerBound n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hSep
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3-16.4, equations (16.23)-(16.24):
    relative first-order Sylvester perturbation bound from a positive lower
    bound on the exact infimum model of `sep(A,B)`. -/
theorem sylvester_relative_first_order_bound_of_pos_le_sylvesterSepInf (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A B)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_pos_le_sylvesterSepInf n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hle
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for the sep-lower-bound relative Sylvester endpoint. -/
theorem H16_eq16_24_sylvester_relative_first_order_bound_of_sepLowerBound (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hSep : SepLowerBound n A B sigma)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    sylvester_relative_first_order_bound_of_sepLowerBound n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hSep
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3, equation (16.24):
    source-numbered alias for the exact-infimum relative Sylvester endpoint. -/
theorem H16_eq16_24_sylvester_relative_first_order_bound_of_pos_le_sylvesterSepInf
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hle : sigma <= sylvesterSepInf n A B)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    sylvester_relative_first_order_bound_of_pos_le_sylvesterSepInf n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hle
      hDeltaA hDeltaB hDeltaC hLin

-- ============================================================
-- Diagonal-case Psi realization (eq (16.24), diagonal / distinct-eigenvalue)
-- ============================================================
























































/-- Higham, 2nd ed., Section 16.3, equation (16.24), diagonal case:
    source-numbered abbreviation for the explicit diagonal structured
    condition number value. -/
noncomputable abbrev H16_eq16_24_sylvesterPsiDiagonal :=
  sylvesterPsiDiagonal





















/-- Higham, 2nd ed., Section 16.3, equation (16.24), diagonal case:
    source-numbered alias for the diagonal structured-condition certificate. -/
alias H16_eq16_24_sylvesterPsiDiagonal_isPsiFirstOrderBound :=
  sylvesterPsiDiagonal_isPsiFirstOrderBound

-- ============================================================
-- Labeled (16.24)/(16.23) wrapper for the diagonal case
-- ============================================================

/-- Higham, 2nd ed., §16.3, eqs (16.23)-(16.24), diagonal case (p. 313):
    the printed structured relative first-order perturbation bound
      `||dX||_F / ||X||_F <= sqrt 3 * Psi * eps`
    with the CONCRETE diagonal condition number `Psi = sylvesterPsiDiagonal`.

    Hypotheses: `A = diag a`, `B = diag b` with entrywise separation `s`, data
    weights `alpha, beta, gamma`, normwise data budgets `||dA|| <= eps*alpha`,
    `||dB|| <= eps*beta`, `||dC|| <= eps*gamma`, and the linearized first-order
    equation `A dX - dX B = dC - dA X + X dB`.

    Honest scope: this is the (16.23)/(16.24) closure for the separated diagonal
    (equivalently: distinct-eigenvalue, diagonalized) Sylvester equation. -/
theorem H16_eq16_24_structured_condition_diagonal (n : ℕ)
    (a b : Fin n → ℝ) (X ΔA ΔB ΔC ΔX : Fin n → Fin n → ℝ)
    (α β γ s ε : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hs : 0 < s) (hε : 0 ≤ ε)
    (hX : 0 < frobNorm X)
    (hsep : ∀ i j, s ≤ |a i - b j|)
    (hΔA : frobNorm ΔA ≤ ε * α)
    (hΔB : frobNorm ΔB ≤ ε * β)
    (hΔC : frobNorm ΔC ≤ ε * γ)
    (hLin : ∀ i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) ΔX i j =
        ΔC i j - matMul n ΔA X i j + matMul n X ΔB i j) :
    frobNorm ΔX / frobNorm X ≤
      Real.sqrt 3 * sylvesterPsiDiagonal n X α β γ s * ε := by
  have hPsi :=
    sylvesterPsiDiagonal_isPsiFirstOrderBound n a b X α β γ s
      hα hβ hγ hs hX hsep
  have hΨnn : 0 ≤ sylvesterPsiDiagonal n X α β γ s := by
    unfold sylvesterPsiDiagonal sylvesterPsi_of_inverseOpBound
    have h1 : (0 : ℝ) ≤ 1 / s := by positivity
    have h2 : 0 ≤ (α + β) * frobNorm X + γ := by
      have := frobNorm_nonneg X; nlinarith
    positivity
  exact sylvester_relative_first_order_bound_of_psi n
    (Matrix.diagonal a) (Matrix.diagonal b) X ΔA ΔB ΔC ΔX
    α β γ (sylvesterPsiDiagonal n X α β γ s) ε
    hPsi hX hΨnn hα hβ hγ hε hΔA hΔB hΔC hLin

/-- Higham, 2nd ed., Section 16.3, equations (16.23)-(16.24), diagonal case:
    relative first-order Sylvester perturbation bound with the concrete
    diagonal condition number `sylvesterPsiDiagonal`. -/
theorem sylvester_relative_first_order_bound_diagonal (n : Nat)
    (a b : Fin n -> Real) (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma s eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hs : 0 < s) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hsep : forall i j, s <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 * sylvesterPsiDiagonal n X alpha beta gamma s * eps := by
  exact
    H16_eq16_24_structured_condition_diagonal n
      a b X DeltaA DeltaB DeltaC DeltaX alpha beta gamma s eps
      halpha hbeta hgamma hs heps hX hsep
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Section 16.3, equation (16.24), diagonal case:
    source-numbered alias for the diagonal relative Sylvester endpoint. -/
theorem H16_eq16_24_sylvester_relative_first_order_bound_diagonal (n : Nat)
    (a b : Fin n -> Real) (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma s eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hs : 0 < s) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hsep : forall i j, s <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 * sylvesterPsiDiagonal n X alpha beta gamma s * eps := by
  exact
    sylvester_relative_first_order_bound_diagonal n
      a b X DeltaA DeltaB DeltaC DeltaX alpha beta gamma s eps
      halpha hbeta hgamma hs heps hX hsep
      hDeltaA hDeltaB hDeltaC hLin

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
















































































































abbrev H16_eq16_24_SylvesterPsiFirstOrderBound :=
  SylvesterPsiFirstOrderBound




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
