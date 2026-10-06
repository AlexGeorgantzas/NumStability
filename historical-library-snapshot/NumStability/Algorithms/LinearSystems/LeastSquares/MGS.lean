import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# MGS

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- Source-facing exact factorization data for Higham, 2nd ed., Chapter 20,
    Section 20.3:
    `[A b] = [Q₁ q] [[R z], [0 ρ]]`, with `q` orthogonal to the columns of
    `Q₁` and with the displayed columns normalized as produced by exact MGS.

    This is an exact algebraic certificate, not a floating-point MGS
    implementation or stability theorem. -/
structure MGSAugmentedLSFactorization {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (Q1 : Fin m → Fin n → ℝ) (q : Fin m → ℝ)
    (R : Fin n → Fin n → ℝ) (z : Fin n → ℝ) (rho : ℝ) : Prop where
  /-- Matrix columns satisfy `A = Q₁R`. -/
  A_eq : ∀ i j, A i j = ∑ k : Fin n, Q1 i k * R k j
  /-- Right-hand side column satisfies `b = Q₁z + ρq`. -/
  b_eq : ∀ i, b i = ∑ k : Fin n, Q1 i k * z k + rho * q i
  /-- Columns of `Q₁` are orthonormal. -/
  Q1_col_orthonormal :
    ∀ j k : Fin n, ∑ i : Fin m, Q1 i j * Q1 i k =
      if j = k then 1 else 0
  /-- The final column `q` is orthogonal to every column of `Q₁`. -/
  q_orthogonal : ∀ j : Fin n, ∑ i : Fin m, Q1 i j * q i = 0
  /-- The final column `q` has Euclidean norm one. -/
  q_norm : vecNorm2Sq q = 1

end NumStability
