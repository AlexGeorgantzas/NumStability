-- Source/Higham/Chapter06/Problem09.lean
--
-- Higham Chapter 6, Problem 6.9 source-facing theorem package.

import NumStability.Analysis.SingularValues.Basic

/-!
# Higham Chapter 6, Problem 6.9

Packages Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Problem 6.9: the two-sided comparison between the operator two-norm and the
Frobenius norm, including its dimension factor.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Source-facing Problem 6.9 comparison package:
    `1 * ||A||₂ <= ||A||_F <= sqrt n * ||A||₂`. -/
theorem highamProblem69_frobenius_op2_bounds {m n : Nat} (hn : 0 < n)
    (A : CMatrix m n) :
    (1 : Real) * complexMatrixOp2 A ≤ complexMatrixFrobenius A ∧
      complexMatrixFrobenius A ≤ Real.sqrt (n : Real) * complexMatrixOp2 A := by
  refine ⟨?_, complexMatrixFrobenius_le_sqrt_card_mul_complexMatrixOp2 A⟩
  simpa using complexMatrixOp2_le_complexMatrixFrobenius hn A
end NumStability
