import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiTriangularSolve
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiTriangularSylvester
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.RoundedSolve
import NumStability.Analysis.MatrixAlgebra
import NumStability.FloatingPoint.Model

/-!
# Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.QuasiRoundedSylvester

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16QuasiRoundedSylvester.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 16.2, pp. 307-308, equations (16.6)-(16.8), quasi-triangular
-- (real Schur) variant, Sylvester level.  Companion endpoint file to
-- `Higham16QuasiRoundedSolve`: the engine file proved the rounded
-- quasi-triangular block back-substitution model
-- (`flQuasiBlockBackSub_backward_error` and its fully componentwise and
-- residual forms) together with the structural layer identifying the
-- reordered vec/Kronecker coefficient `P = I_n kron R - S^T kron I_m` of
-- (16.2) as a block upper-triangular `nm x nm` system with the same
-- 1 x 1 / 2 x 2 diagonal-block structure as the quasi-triangular factor
-- `R`.  This file instantiates that engine on the Sylvester data and
-- delivers the printed (16.7)/(16.8)-shaped statements for the
-- quasi-triangular Bartels-Stewart solve:
--
--   (16.7)  (P + DeltaP) vec(Z^) = vec(C~), with
--           |DeltaP| <= (1+rho) gamma_{nm+9} |P| componentwise under the
--           per-block growth certificates, and unconditionally with the
--           explicit Theorem 9.3 |L||U|-shaped elimination fill-in budget
--           (`sylvesterQuasiGrowthTerm`);
--   (16.8)  |vec(C~) - P vec(Z^)| <= (1+rho) gamma_{nm+9} (|P| |vec(Z^)|)
--           componentwise, and in the printed matrix shape
--           |C~ - R Z^ + Z^ S| <= (1+rho) gamma_{nm+9} (|R||Z^| + |Z^||S|)
--           entrywise,
--
-- for `Z^ = flSylvesterQuasiSchurBlockBackSubSolve`, the computed
-- quasi-triangular block Bartels-Stewart solution of (16.6).
--
-- Honest scope (inherited from the engine file):
-- * Schur factors are SUPPLIED (quasi-upper-triangular `R` with adjacent
--   2 x 2 diagonal blocks marked by `dblR`, upper-triangular `S`), as in
--   the printed setting; errors in computing the real Schur decompositions
--   or the transformed right-hand side belong to (16.9) and are not
--   modeled here.  `C~` is an arbitrary supplied right-hand side.
-- * The 2 x 2 diagonal blocks are solved by GE WITHOUT pivoting.  The
--   hypotheses are the honest per-block completion certificates the engine
--   takes: diagonal separation `R_ii /= S_kk` on every row `i` that is not
--   the bottom row of a marked block (the scalar pivots and the block
--   first pivots), and a nonzero COMPUTED second pivot for every marked
--   shifted 2 x 2 block.  Nothing is smuggled.
-- * GE is not componentwise backward stable relative to `|P|` alone: the
--   unconditional (16.7) budget carries the explicit per-block elimination
--   fill-in (the `n = 2` instance of the printed `|L^||U^|` budget of
--   Theorem 9.3, transported to the product index as
--   `sylvesterQuasiGrowthTerm`).  The printed fully componentwise shape
--   takes the standard per-block growth certificates
--   `|R_{i,i+1}| |R_{i+1,i}| <= rho |R_ii - S_kk| |R_{i+1,i+1} - S_kk|`
--   as an explicit hypothesis and carries the explicit `(1+rho)` factor.
-- * The printed unspecified constant `c_{m,n} u` is realized as the
--   explicit same-gamma-class envelope `gamma_{nm+9}`, the engine envelope
--   `gamma_{N+9}` at `N = nm`: Chapter 8 fold accumulation on at most `nm`
--   terms composed with the 9-operation 2 x 2 kernel envelope `gamma_9`.
--   We do not claim the printed letter constant.
-- * Only the mixed case "R quasi-triangular, S strictly triangular" is
--   delivered; a 2 x 2 block of `S` couples unknown columns at rank
--   distance `m`, so the fully quasi-quasi case needs the interleaved
--   two-column ordering with diagonal blocks of size up to 4 and remains
--   open (see the engine file header).



namespace NumStability

namespace Wave15

open scoped BigOperators

-- ============================================================
-- The transported per-entry elimination fill-in budget
-- ============================================================


















-- ============================================================
-- Transport of the engine hypotheses through the index equivalence
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

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.7),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    induced product-index adjacent-pair marking used by the rounded
    quasi-triangular block substitution. -/
alias H16_eq16_6_quasi_sylvesterQuasiPairing_isQuasiBlockPairing :=
  sylvesterQuasiPairing_isQuasiBlockPairing

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.7),
    quasi-triangular (real Schur) variant: source-numbered alias for decoding
    a marked product-index block into the corresponding `2 x 2` diagonal block
    of the reordered vec/Kronecker coefficient. -/
alias H16_eq16_6_quasi_sylvesterQuasiPairing_block_decode :=
  sylvesterQuasiPairing_block_decode

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    same-column off-diagonal entries of the vec/Kronecker Sylvester
    coefficient used when decoding marked `2 x 2` product-index blocks. -/
alias H16_eq16_2_quasi_sylvesterVecCoeff_same_col_apply :=
  sylvesterVecCoeff_same_col_apply

/-- Higham, 2nd ed., Chapter 16.2, equations (16.6)-(16.7),
    quasi-triangular (real Schur) variant: source-numbered alias for
    transporting the non-bottom-row condition through the Bartels-Stewart
    product-index order. -/
alias H16_eq16_6_quasi_sylvesterQuasiPairing_notSecond_decode :=
  sylvesterQuasiPairing_notSecond_decode

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.7),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    generic zero theorem of the reordered vec/Kronecker coefficient below the
    marked block diagonal. -/
alias H16_eq16_6_quasi_sylvesterQuasiSchurBackSubCoeff_eq_zero :=
  sylvesterQuasiSchurBackSubCoeff_eq_zero

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.7),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    below-subdiagonal zero pattern of the reordered vec/Kronecker coefficient
    used by the rounded block substitution. -/
alias H16_eq16_6_quasi_sylvesterQuasiSchurBackSubCoeff_below_subdiag_zero :=
  sylvesterQuasiSchurBackSubCoeff_below_subdiag_zero

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.7),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    off-block first-subdiagonal zero pattern of the reordered vec/Kronecker
    coefficient used by the rounded block substitution. -/
alias H16_eq16_6_quasi_sylvesterQuasiSchurBackSubCoeff_subdiag_zero :=
  sylvesterQuasiSchurBackSubCoeff_subdiag_zero

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.7),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    combined zero pattern below the marked block diagonal of the reordered
    vec/Kronecker coefficient. -/
alias H16_eq16_6_quasi_sylvesterQuasiSchurBackSubCoeff_below_markedBlock_zero :=
  sylvesterQuasiSchurBackSubCoeff_below_markedBlock_zero

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6),
    quasi-triangular (real Schur) variant: source-numbered alias for transport
    of the scalar and first-block-pivot separation certificate to the reordered
    coefficient. -/
alias H16_eq16_6_quasi_sylvesterQuasiSchurBackSubCoeff_pivot_ne_zero :=
  sylvesterQuasiSchurBackSubCoeff_pivot_ne_zero

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6),
    quasi-triangular (real Schur) variant: source-numbered alias for transport
    of the computed second-pivot certificate for each marked shifted `2 x 2`
    block. -/
alias H16_eq16_6_quasi_sylvesterQuasiSchurBackSubCoeff_secondPivot_ne_zero :=
  sylvesterQuasiSchurBackSubCoeff_secondPivot_ne_zero

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), with Chapter 9.3 growth
    control: source-numbered alias for transport of the marked-block growth
    certificate that collapses the explicit GE fill-in into the componentwise
    `(1 + rho)` budget. -/
alias H16_eq16_6_quasi_sylvesterQuasiSchurBackSubCoeff_growth :=
  sylvesterQuasiSchurBackSubCoeff_growth

/-- Higham, 2nd ed., Chapter 16.2, p. 308, equation (16.6),
    quasi-triangular (real Schur) variant: source-numbered alias for the
    vectorized/matrix bookkeeping of the computed rounded quasi-triangular
    Schur solve. -/
alias H16_eq16_6_quasi_vec_flSylvesterQuasiSchurBlockBackSubSolve :=
  vec_flSylvesterQuasiSchurBlockBackSubSolve

























































end Wave15

end NumStability
