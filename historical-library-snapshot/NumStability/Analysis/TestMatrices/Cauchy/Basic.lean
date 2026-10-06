import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Analysis TestMatrices Cauchy Basic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Higham, 2nd ed., Section 28.1, pp. 514-515: a rectangular Cauchy matrix
`C_ij = 1/(x_i+y_j)`. -/
noncomputable def cauchyMatrix {m n : ℕ} (x : RVec m) (y : RVec n) : RMat m n :=
  fun i j => 1 / (x i + y j)

@[simp] theorem cauchyMatrix_apply {m n : ℕ} (x : RVec m) (y : RVec n)
    (i : Fin m) (j : Fin n) :
    cauchyMatrix x y i j = 1 / (x i + y j) := rfl

/-- Transposition swaps the two node families in a rectangular Cauchy matrix. -/
theorem cauchyMatrix_transpose {m n : ℕ} (x : RVec m) (y : RVec n) :
    (cauchyMatrix x y).transpose = cauchyMatrix y x := by
  ext i j
  simp [cauchyMatrix, add_comm]

/-- The exact determinant product printed in Section 28.1 for a square Cauchy
matrix.  The filtered products use the natural `Fin n` order. -/
noncomputable def cauchyDetFormula (n : ℕ) (x y : RVec n) : ℝ :=
  (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      (x j - x i) * (y j - y i)) /
    (∏ i : Fin n, ∏ j : Fin n, (x i + y j))

/-- The entrywise inverse formula printed for a nonsingular square Cauchy
matrix.  In an inverse entry `(i,j)`, `i` indexes the `y` nodes and `j` the
`x` nodes. -/
noncomputable def cauchyInverseEntry
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  (∏ k : Fin n, (x j + y k) * (x k + y i)) /
    ((x j + y i) *
      (∏ k ∈ Finset.univ.erase j, (x j - x k)) *
      (∏ k ∈ Finset.univ.erase i, (y i - y k)))

noncomputable def cauchyInverseFormula
    (n : ℕ) (x y : RVec n) : RSqMat n :=
  fun i j => cauchyInverseEntry n x y i j

/-- Base-order validation of the generic Cauchy inverse formula. -/
theorem cauchy_order_one_inverse_formula
    (x y : RVec 1) (hxy : x 0 + y 0 ≠ 0) :
    cauchyMatrix x y * cauchyInverseFormula 1 x y = (1 : RSqMat 1) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, cauchyMatrix, cauchyInverseFormula,
    cauchyInverseEntry, hxy]

/-- Base-order validation of the Cauchy determinant product. -/
theorem cauchy_order_one_det_formula (x y : RVec 1) :
    Matrix.det (cauchyMatrix x y) = cauchyDetFormula 1 x y := by
  simp [cauchyMatrix, cauchyDetFormula]

end NumStability
