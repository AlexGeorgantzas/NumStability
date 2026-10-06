import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Source.Higham.Chapter13.Equation02

This module formalizes the source-facing Chapter 13 statements for
`Equation02`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- **Equation (13.2)**, one exact block LU step with Schur complement.
    For an invertible leading block `A₁₁`, the 2-by-2 block matrix factors as
    `[[I,0],[A₂₁ A₁₁^{-1},I]] * [[A₁₁,A₁₂],[0,S]]`, where
    `S = A₂₂ - A₂₁ A₁₁^{-1} A₁₂`. -/
theorem higham13_eq13_2_block_lu_step
    {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing α]
    (A11 : Matrix m m α) (A12 : Matrix m n α)
    (A21 : Matrix n m α) (A22 : Matrix n n α) [Invertible A11] :
    Matrix.fromBlocks A11 A12 A21 A22 =
      Matrix.fromBlocks 1 0 (A21 * ⅟A11) 1 *
        Matrix.fromBlocks A11 A12 0 (A22 - A21 * ⅟A11 * A12) := by
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc]

end NumStability
