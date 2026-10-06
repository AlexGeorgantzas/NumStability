import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiQuasiSolve
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiTriangularSolve
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.SmallSystemRounding
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.QuasiQuasiSylvester

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16QuasiQuasiSylvester.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 16.2, pp. 307-308, equations (16.6)-(16.8), fully quasi-triangular
-- (real Schur) variant, Sylvester level.  Companion endpoint file to
-- `Higham16QuasiQuasiRounded`: the engine file proved the parametric rounded
-- Gaussian-elimination kernel (`flGESolve` with its Theorems 9.3-9.4
-- backward error), the rounded block back substitution over an interval
-- block partition (`flPartitionBackSub` with its Theorem 8.5-style block
-- backward error), and the quasi-quasi structural layer: the interleaved
-- two-column Bartels-Stewart ranking `sylvesterQQIndexEquiv`, under which
-- the (16.2) coefficient `P = I_n kron R - S^T kron I_m` of a
-- quasi-triangular pair (`R` with 2 x 2 diagonal ROW blocks marked by
-- `dblR`, `S` with 2 x 2 diagonal COLUMN blocks marked by `dblS`) is block
-- upper triangular for the induced 1/2/4 interval partition
-- (`sylvesterQQBs`/`sylvesterQQBe`, `sylvesterQQPartition_valid`,
-- `sylvesterQQBackSubCoeff_zero`), with diagonal blocks identified in
-- factor entries by `sylvesterQQBlockCoeff_entry`.  This file instantiates
-- that engine on the Sylvester data and delivers the printed
-- (16.7)/(16.8)-shaped statements for the fully quasi-quasi
-- Bartels-Stewart solve:
--
--   (16.7)  (P + DeltaP) vec(Z^) = vec(C~), with
--           |DeltaP| <= (1+rho) gamma_{nm+20} |P| componentwise under the
--           per-block growth certificates, and unconditionally with the
--           explicit Theorem 9.3 |L^||U^|-shaped per-block elimination
--           budget (`sylvesterQQBudget`);
--   (16.8)  |vec(C~) - P vec(Z^)| <= (1+rho) gamma_{nm+20} (|P| |vec(Z^)|)
--           componentwise, and in the printed matrix shape
--           |C~ - R Z^ + Z^ S| <= (1+rho) gamma_{nm+20} (|R||Z^| + |Z^||S|)
--           entrywise,
--
-- for `Z^ = flSylvesterQQBlockBackSubSolve`, the computed quasi-quasi block
-- Bartels-Stewart solution of the substitution (16.6) (defined here from
-- the engine's `flPartitionBackSub` on the interleaved reordered system).
--
-- Honest scope (inherited from the engine file):
-- * Schur factors are SUPPLIED (quasi-upper-triangular `R` with adjacent
--   2 x 2 diagonal row blocks marked by `dblR`, quasi-upper-triangular `S`
--   with adjacent 2 x 2 diagonal column blocks marked by `dblS`), as in the
--   printed setting; errors in computing the real Schur decompositions or
--   the transformed right-hand side belong to (16.9) and are not modeled
--   here.  `C~` is an arbitrary supplied right-hand side.
-- * The diagonal blocks of order 1, 2, 4 are solved by GE WITHOUT pivoting
--   (`flGESolve`).  The hypotheses are the honest per-block completion
--   certificates the engine takes: every COMPUTED pivot of every diagonal
--   block elimination is nonzero (`flGEPivots` on the explicit factor-entry
--   blocks `sylvesterQQDiagBlock`, which are exactly the shifted systems of
--   order <= 4 the printed algorithm solves on p. 308).  Nothing is
--   smuggled.
-- * GE is not componentwise backward stable relative to `|P|` alone: the
--   unconditional (16.7) bound carries the explicit transported Theorem 9.3
--   `|L^||U^|`-shaped budget `sylvesterQQBudget` (the engine
--   `partitionBudget`: `flGEBudget` on the diagonal blocks, `|P|` off the
--   blocks; it dominates `|P|` entrywise).  The printed fully componentwise
--   shape takes the standard per-block budget-domination certificates
--   `flGEBudget <= (1 + rho) |block|` as an explicit hypothesis and carries
--   the explicit `(1+rho)` growth factor.
-- * The printed unspecified constant `c_{m,n} u` is realized as the honest
--   same-gamma-class envelope `gamma_{nm+20}`, the engine envelope
--   `gamma_{N + 5B}` at `N = nm`, `B = 4`: Chapter 8 fold accumulation on
--   at most `nm` terms composed with the size-<=-4 kernel envelope
--   `gamma_{5*4} = gamma_20`.  We do not claim the printed letter constant.



namespace NumStability

namespace Wave16

open scoped BigOperators
open Wave15

-- ============================================================
-- The explicit factor-entry diagonal blocks of the substitution
-- ============================================================

































































-- ============================================================
-- The computed quasi-quasi Bartels-Stewart solution
-- ============================================================











































-- ============================================================
-- The transported per-entry elimination budget
-- ============================================================






















































































-- ============================================================
-- Transport of the engine hypotheses to the factor-entry blocks
-- ============================================================








































































-- ============================================================
-- (16.7): rounded block-substitution backward error
-- ============================================================












































































































































-- ============================================================
-- (16.8): componentwise residual consequence
-- ============================================================





























































































































































































































































































































































































































-- ============================================================
-- Source-numbered aliases
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    explicit factor-entry diagonal-block identification of the interleaved
    reordered coefficient. -/
alias H16_eq16_6_quasiquasi_sylvesterQQBlockSubCoeff_eq_diagBlock :=
  sylvesterQQBlockSubCoeff_eq_diagBlock

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    vectorized/matrix bookkeeping of the computed rounded quasi-quasi
    Schur solve. -/
alias H16_eq16_6_quasiquasi_vec_flSylvesterQQBlockBackSubSolve :=
  vec_flSylvesterQQBlockBackSubSolve

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6), fully
    quasi-triangular (real Schur) variant: source-numbered alias for
    transport of the per-block computed-pivot completion certificates to
    the interleaved reordered system. -/
alias H16_eq16_6_quasiquasi_sylvesterQQBlockPivots_transport :=
  sylvesterQQBlockPivots_transport

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), with Chapter 9.3
    growth control, fully quasi-triangular (real Schur) variant:
    source-numbered alias for transport of the per-block budget-domination
    certificates that collapse the explicit GE fill-in into the
    componentwise `(1 + rho)` budget. -/
alias H16_eq16_6_quasiquasi_sylvesterQQPartitionBudget_le_of_growth :=
  sylvesterQQPartitionBudget_le_of_growth

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.7), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    unconditional backward-error model with the explicit transported
    Theorem 9.3 elimination budget. -/
alias H16_eq16_7_quasiquasi_sylvesterVecCoeff_blockBackSub_backward_error :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_backward_error

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.7), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    printed fully componentwise backward-error model
    `(P + DeltaP) x^ = vec(C~)`, `|DeltaP| <= (1+rho) gamma_{nm+20} |P|`
    under the per-block pivot/growth certificates. -/
alias H16_eq16_7_quasiquasi_sylvesterVecCoeff_blockBackSub_backward_error_componentwise :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_backward_error_componentwise

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    vectorized componentwise residual consequence with the explicit
    transported elimination budget from the unconditional (16.7) model. -/
alias H16_eq16_8_quasiquasi_sylvesterVecCoeff_blockBackSub_componentwise_residual_with_budget :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_residual_with_budget

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    printed matrix residual consequence with the explicit GE fill-in
    excess from the unconditional (16.7) model. -/
alias H16_eq16_8_quasiquasi_sylvesterResidualRect_blockBackSub_componentwise_le_with_budget :=
  sylvesterResidualRect_quasiQuasi_blockBackSub_componentwise_le_with_budget

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    vectorized componentwise residual consequence
    `|vec(C~) - P x^| <= (1+rho) gamma_{nm+20} (|P| |x^|)`. -/
alias H16_eq16_8_quasiquasi_sylvesterVecCoeff_blockBackSub_componentwise_residual :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_residual

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equation (16.8), fully
    quasi-triangular (real Schur) variant: source-numbered alias for the
    printed matrix form
    `|C~ - R Z^ + Z^ S| <= (1+rho) gamma_{nm+20} (|R||Z^| + |Z^||S|)`. -/
alias H16_eq16_8_quasiquasi_sylvesterResidualRect_blockBackSub_componentwise_le :=
  sylvesterResidualRect_quasiQuasi_blockBackSub_componentwise_le

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.7)-(16.8),
    fully quasi-triangular (real Schur) variant: source-numbered alias for
    the bundled componentwise backward-error and residual endpoint
    package. -/
alias H16_eq16_7_8_quasiquasi_sylvesterVecCoeff_blockBackSub_componentwise_error_and_residual :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_error_and_residual

/-- Higham, 2nd ed., Chapter 16.2, pp. 307-308, equations (16.7)-(16.8),
    fully quasi-triangular (real Schur) variant: source-numbered alias for
    the bundled unconditional elimination-budget backward-error and
    residual endpoint package. -/
alias H16_eq16_7_8_quasiquasi_sylvesterVecCoeff_blockBackSub_componentwise_error_and_residual_with_budget :=
  sylvesterVecCoeff_quasiQuasi_blockBackSub_componentwise_error_and_residual_with_budget

end Wave16

end NumStability
