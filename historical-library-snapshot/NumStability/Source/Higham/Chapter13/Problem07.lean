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
# Source.Higham.Chapter13.Problem07

This module formalizes the source-facing Chapter 13 statements for
`Problem07`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- **Problem 13.7**, Schur determinant identity.  For a block matrix
    `X = [[A, B], [C, D]]` with invertible leading block `A`, Mathlib's Schur
    complement determinant theorem gives
    `det X = det A * det (D - C A^{-1} B)`. -/
theorem higham13_problem13_7_det_schur
    {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing α]
    (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] :
    (Matrix.fromBlocks A B C D).det = A.det * (D - C * ⅟A * B).det := by
  simpa using Matrix.det_fromBlocks₁₁ A B C D

/-- **Problem 13.7**, commuting-block corollary.  In the equal-block-size case,
    if `A` commutes with `C`, the Schur determinant identity reduces to
    `det [[A,B],[C,D]] = det (A D - C B)`. -/
theorem higham13_problem13_7_det_commuting_AC
    {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α]
    (A B C D : Matrix n n α) [Invertible A] (hAC : A * C = C * A) :
    (Matrix.fromBlocks A B C D).det = (A * D - C * B).det := by
  rw [Matrix.det_fromBlocks₁₁]
  rw [← Matrix.det_mul]
  congr 1
  calc
    A * (D - C * ⅟A * B) = A * D - A * (C * ⅟A * B) := by
      rw [Matrix.mul_sub]
    _ = A * D - C * B := by
      congr 1
      calc
        A * (C * ⅟A * B) = (A * C) * ⅟A * B := by
          simp [Matrix.mul_assoc]
        _ = (C * A) * ⅟A * B := by
          rw [hAC]
        _ = C * (A * ⅟A) * B := by
          simp [Matrix.mul_assoc]
        _ = C * B := by
          simp

end NumStability
