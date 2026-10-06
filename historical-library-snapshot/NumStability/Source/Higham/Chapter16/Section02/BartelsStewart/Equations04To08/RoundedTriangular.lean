import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.RoundedSolve
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.RoundedTriangular

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16RoundedTriangular.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 16.2, pp. 307-308, equations (16.7)-(16.8): the rounded
-- triangular-solve backward-error model for the vectorized Schur-form
-- Sylvester system, and its componentwise residual consequence.
--
-- Setting.  After the real Schur reduction (16.4)-(16.5), the transformed
-- Sylvester equation `R Z - Z S = C~` with upper-triangular factors `R`
-- (m x m) and `S` (n x n) is solved column by column by substitution
-- ((16.6)).  Higham observes that this whole process is the substitution
-- solve of one large `nm x nm` triangular linear system whose coefficient is
-- the vec/Kronecker matrix `P = I_n kron R - S^T kron I_m` of (16.2), and
-- that the standard Chapter 8 backward-error analysis (Theorem 8.5) of
-- substitution therefore applies:
--
--   (16.7)  (P + DeltaP) vec(Z^) = vec(C~),  |DeltaP| <= c_{m,n} u |P|,
--   (16.8)  |vec(C~) - P vec(Z^)| <= c_{m,n} u |P| |vec(Z^)|
--           (equivalently  |C~ - R Z^ + Z^ S| <= c_{m,n} u (|R||Z^| + |Z^||S|)).
--
-- This file proves exactly that instantiation:
--
-- * `sylvesterBackSubIndexEquiv` ranks the product index `(k, i)` (column
--   `k` of the unknown, row `i` inside the column) in the Bartels-Stewart
--   elimination order; under this ranking the vec/Kronecker coefficient of
--   the supplied triangular Schur-coordinate pair is genuinely upper
--   triangular (`sylvesterSchurBackSubCoeff_eq_zero_of_val_lt`), and its
--   diagonal entries are the eigenvalue differences `R_ii - S_kk`.
-- * `flSylvesterSchurBackSubSolveVec` is the computed solution: Chapter 8
--   floating-point back substitution (Algorithm 8.1, `fl_backSub`) applied
--   to the reordered vectorized system.  Back substitution processes the
--   reordered rows exactly in the Bartels-Stewart order (columns of `Z`
--   left to right, rows within a column bottom up).
-- * (16.7) is `sylvesterVecCoeff_triangular_backSub_backward_error`, an
--   instantiation of the Chapter 8 Theorem 8.5 endpoint
--   `backSub_backward_error`, transported through the index equivalence.
-- * (16.8) is derived in vectorized componentwise form
--   (`sylvesterVecCoeff_triangular_backSub_componentwise_residual`) and in
--   the printed matrix shape with the `|R||Z^| + |Z^||S|` budget
--   (`sylvesterResidualRect_triangular_backSub_componentwise_le`).
--
-- Honest scope:
-- * Schur factors are SUPPLIED (orthogonal `U`, `V` with upper-triangular
--   `R`, `S`), matching the printed setting, which assumes the Schur
--   decomposition has already been computed; errors in computing the Schur
--   factors and in forming `C~ = fl(U^T C V)` belong to the (16.9) overall
--   bound and are NOT asserted here.  The right-hand side `C~` is an
--   arbitrary supplied matrix, so it covers whatever transformed right-hand
--   side was computed upstream.
-- * The printed unspecified constant `c_{m,n} u` is realized as the explicit
--   same-gamma-class envelope `gamma_{nm} = nm*u/(1 - nm*u)` coming from the
--   Chapter 8 theorem on the `nm x nm` system.  We do not claim the printed
--   letter constant.
-- * The computed-solution model is the Chapter 8 dense back-substitution
--   loop: every superdiagonal entry of the reordered system participates in
--   the row recurrence, including the structural zeros of the Kronecker
--   coefficient.  The componentwise bound `|DeltaP| <= gamma_{nm} |P|`
--   forces the perturbation to vanish on that zero pattern, so the
--   backward-error conclusion is exactly the printed componentwise model.
-- * Only the strictly triangular (all 1x1 diagonal blocks) Schur case is
--   treated; the quasi-triangular 2x2-block variant of (16.7) remains open.







namespace NumStability

namespace Wave14

open scoped BigOperators

-- ============================================================
-- The Bartels-Stewart elimination order on the product index
-- ============================================================










































































-- ============================================================
-- The reordered nm x nm triangular system of (16.7)
-- ============================================================
























































































-- ============================================================
-- The computed solution: Chapter 8 back substitution on the big system
-- ============================================================






























-- ============================================================
-- (16.7): rounded triangular-solve backward error
-- ============================================================






















































-- ============================================================
-- (16.8): componentwise residual consequence
-- ============================================================


























































































































































-- ============================================================
-- Bridges to the house shifted-determinant certificates
-- ============================================================




















































-- ============================================================
-- Supplied Schur-factor wrappers
-- ============================================================



























































































-- ============================================================
-- Source-numbered aliases
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7): source-numbered
    alias for the raw triangular-solve backward-error model of the vectorized
    Sylvester system. -/
alias H16_eq16_7_sylvesterVecCoeff_triangular_backSub_backward_error :=
  sylvesterVecCoeff_triangular_backSub_backward_error

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8):
    source-numbered alias for the raw vectorized componentwise residual
    consequence of the (16.7) backward-error model. -/
alias H16_eq16_8_sylvesterVecCoeff_triangular_backSub_componentwise_residual :=
  sylvesterVecCoeff_triangular_backSub_componentwise_residual

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8):
    source-numbered alias for the raw printed matrix form
    `|C~ - R Z^ + Z^ S| <= gamma_{nm} (|R||Z^| + |Z^||S|)` of the
    componentwise residual consequence. -/
alias H16_eq16_8_sylvesterResidualRect_triangular_backSub_componentwise_le :=
  sylvesterResidualRect_triangular_backSub_componentwise_le

/-- Higham, 2nd ed., Chapter 16.2, p. 307, equation (16.7): source-numbered
    alias for the supplied Schur-factor rounded triangular-solve
    backward-error model of the vectorized Sylvester system. -/
alias H16_eq16_7_sylvesterVecCoeff_schurTriangular_backSub_backward_error :=
  sylvesterVecCoeff_schurTriangular_backSub_backward_error

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8):
    source-numbered alias for the vectorized componentwise residual
    consequence of the (16.7) backward-error model. -/
alias H16_eq16_8_sylvesterVecCoeff_schurTriangular_backSub_componentwise_residual :=
  sylvesterVecCoeff_schurTriangular_backSub_componentwise_residual

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8):
    source-numbered alias for the printed matrix form
    `|C~ - R Z^ + Z^ S| <= gamma_{nm} (|R||Z^| + |Z^||S|)` of the
    componentwise residual consequence. -/
alias H16_eq16_8_sylvesterResidualRect_schurTriangular_backSub_componentwise_le :=
  sylvesterResidualRect_schurTriangular_backSub_componentwise_le

end Wave14

end NumStability
