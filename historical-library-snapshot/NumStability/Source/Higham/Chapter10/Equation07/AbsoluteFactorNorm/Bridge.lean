import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter06.Lemma06.Core.Results
import NumStability.Source.Higham.Chapter06.Lemma06.OperatorTwoNormBound.Bridge
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11

/-!
# Chapter10 Equation07 AbsoluteFactorNorm Bridge

Canonical destination for material split out of
`NumStability.Algorithms.Ch10Ch14Lemma66Op2Bridge` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

namespace Lemma66Op2Bridge

/-- **Higham Ch.10, eq. (10.7) key inequality.**  ch10.txt: "The key inequality
is (using Lemma 6.6) `‖ |R| ‖₂² ≤ n‖R‖₂²`".  Squaring the bridge inequality for
the (square) computed Cholesky factor `R`. -/
theorem lemma66c_ch10_absFactor_op2Sq_le {n : ℕ} (hn : 0 < n) (R : CMatrix n n) :
    complexMatrixOp2 (complexAbsMatrix R) ^ 2 ≤ (n : ℝ) * complexMatrixOp2 R ^ 2 := by
  have hbase := lemma66c_absMatrix_op2_le_sqrt_card hn R
  have h0 : 0 ≤ complexMatrixOp2 (complexAbsMatrix R) := complexMatrixOp2_nonneg _
  calc complexMatrixOp2 (complexAbsMatrix R) ^ 2
      ≤ (Real.sqrt (n : ℝ) * complexMatrixOp2 R) ^ 2 := pow_le_pow_left₀ h0 hbase 2
    _ = Real.sqrt (n : ℝ) ^ 2 * complexMatrixOp2 R ^ 2 := by ring
    _ = (n : ℝ) * complexMatrixOp2 R ^ 2 := by
        rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ))]

end Lemma66Op2Bridge
end NumStability
