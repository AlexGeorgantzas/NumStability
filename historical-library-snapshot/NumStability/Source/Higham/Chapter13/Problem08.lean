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
# Source.Higham.Chapter13.Problem08

This module formalizes the source-facing Chapter 13 statements for
`Problem08`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- **Problem 13.8**, block inverse formula around an invertible leading block.
    This is the standard inverse formula expressed in terms of the Schur
    complement `D - C A^{-1} B`. -/
theorem higham13_problem13_8_block_inverse
    {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing α]
    (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] [Invertible (D - C * ⅟A * B)]
    [Invertible (Matrix.fromBlocks A B C D)] :
    ⅟(Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks
        (⅟A + ⅟A * B * ⅟(D - C * ⅟A * B) * C * ⅟A)
        (-(⅟A * B * ⅟(D - C * ⅟A * B)))
        (-(⅟(D - C * ⅟A * B) * C * ⅟A))
        (⅟(D - C * ⅟A * B)) := by
  simpa using Matrix.invOf_fromBlocks₁₁_eq A B C D

end NumStability
