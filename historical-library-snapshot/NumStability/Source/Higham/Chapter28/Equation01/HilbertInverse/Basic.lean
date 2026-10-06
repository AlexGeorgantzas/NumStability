import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic

/-!
# Chapter28 Equation01 HilbertInverse Basic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- The explicit integer-valued expression printed in equation (28.1).  This
definition records the exact candidate entry; the generic inverse proof is a
separate selected obligation recorded in the Chapter 28 ledger. -/
noncomputable def hilbertInverseEntry (n : ℕ) (i j : Fin n) : ℝ :=
  (-1 : ℝ) ^ (i.val + j.val) * (i.val + j.val + 1) *
    Nat.choose (n + i.val) (n - (j.val + 1)) *
    Nat.choose (n + j.val) (n - (i.val + 1)) *
    (Nat.choose (i.val + j.val) i.val : ℝ) ^ 2

/-- Equation (28.1)'s candidate inverse matrix. -/
noncomputable def hilbertInverseFormula (n : ℕ) : RSqMat n :=
  fun i j => hilbertInverseEntry n i j

@[simp] theorem hilbertInverseFormula_apply {n : ℕ} (i j : Fin n) :
    hilbertInverseFormula n i j = hilbertInverseEntry n i j := rfl

/-- Base-order closure check for equation (28.1).  The generic binomial
convolution remains the selected open theorem, but the encoded formula is
proved to be the inverse at order one. -/
theorem hilbert_order_one_inverse_formula :
    hilbertMatrix 1 * hilbertInverseFormula 1 = (1 : RSqMat 1) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul_apply, hilbertMatrix, hilbertInverseFormula,
    hilbertInverseEntry]

end NumStability
