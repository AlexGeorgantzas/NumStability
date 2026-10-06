import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic

/-!
# Chapter28 Equation02 ExactHilbertDeterminant Basic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Base-order closure check for the exact determinant part of (28.2). -/
theorem hilbert_order_one_det_formula :
    Matrix.det (hilbertMatrix 1) = hilbertDetFormula 1 := by
  norm_num [hilbertMatrix, hilbertDetFormula, factorialProduct, Matrix.det_fin_one,
    Finset.prod_range_succ]

end NumStability
