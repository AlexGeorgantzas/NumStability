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
# Source.Higham.Chapter13.Problem09

This module formalizes the source-facing Chapter 13 statements for
`Problem09`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics



/-- **Problem 13.9**, resolvent identity:
    `(I - A B)^{-1} = I + A (I - B A)^{-1} B`.
    The proof verifies that the displayed right-hand side is a right inverse of
    `I - A B`; the `Invertible` hypotheses record the nonsingularity conditions
    under which the inverses are interpreted. -/
theorem higham13_problem13_9_resolvent_identity
    {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing α]
    (A : Matrix m n α) (B : Matrix n m α)
    [Invertible (1 - A * B : Matrix m m α)]
    [Invertible (1 - B * A : Matrix n n α)] :
    ⅟(1 - A * B) = 1 + A * ⅟(1 - B * A) * B := by
  apply invOf_eq_right_inv
  let S : Matrix n n α := ⅟(1 - B * A)
  have hS : (1 - B * A) * S = (1 : Matrix n n α) := by
    dsimp [S]
    exact mul_invOf_self _
  have hSsub : S - B * A * S = (1 : Matrix n n α) := by
    calc
      S - B * A * S = (1 - B * A) * S := by
        rw [Matrix.sub_mul, Matrix.one_mul]
      _ = 1 := hS
  have hmid : A * S - (A * (B * A)) * S = A * (S - B * A * S) := by
    rw [Matrix.mul_sub]
    simp [Matrix.mul_assoc]
  calc
    (1 - A * B) * (1 + A * S * B)
        = (1 - A * B) * 1 + (1 - A * B) * (A * S * B) := by
          rw [Matrix.mul_add]
    _ = (1 - A * B) + ((1 - A * B) * A) * S * B := by
          rw [Matrix.mul_one]
          simp [Matrix.mul_assoc]
    _ = (1 - A * B) + (A - A * (B * A)) * S * B := by
          congr 1
          rw [Matrix.sub_mul, Matrix.one_mul]
          simp [Matrix.mul_assoc]
    _ = (1 - A * B) + A * (S - B * A * S) * B := by
          rw [Matrix.sub_mul, hmid]
    _ = (1 - A * B) + A * (1 : Matrix n n α) * B := by
          rw [hSsub]
    _ = 1 := by
          simp

/-- **Problem 13.9**, Sherman--Morrison--Woodbury identity.  This source-facing
    wrapper exposes Mathlib's Woodbury theorem with the notation used by the
    chapter exercise. -/
theorem higham13_problem13_9_sherman_morrison_woodbury
    {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing α]
    (A : Matrix n n α) (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α)
    (hA : IsUnit A) (hC : IsUnit C) (hAC : IsUnit (C⁻¹ + V * A⁻¹ * U)) :
    (A + U * C * V)⁻¹ =
      A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ :=
  Matrix.add_mul_mul_inv_eq_sub A U C V hA hC hAC

end NumStability
