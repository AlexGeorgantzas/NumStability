import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic

/-!
# Chapter28 Equation03 HilbertCholeskyFactor Basic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Higham, 2nd ed., Section 28.1, p. 513, equation (28.3): the upper-
triangular Cholesky-factor entry formula, translated to zero-based indices. -/
noncomputable def hilbertInvCholeskyEntry (n : ℕ) (i j : Fin n) : ℝ :=
  hilbertRNat i.val j.val

/-- Matrix form of (28.3). -/
noncomputable def hilbertCholeskyFactor (n : ℕ) : RSqMat n :=
  fun i j => hilbertInvCholeskyEntry n i j

end NumStability
