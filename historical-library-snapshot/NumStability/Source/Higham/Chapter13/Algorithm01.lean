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
# Source.Higham.Chapter13.Algorithm01

This module formalizes the source-facing Chapter 13 statements for
`Algorithm01`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- **Algorithm 13.1**, exact output check for partitioned outer-product LU.
    If the algorithm's displayed steps hold -- `A₁₁ = L₁₁ U₁₁`,
    `L₁₁ U₁₂ = A₁₂`, `L₂₁ U₁₁ = A₂₁`, `S = A₂₂ - L₂₁ U₁₂`, and the recursive
    call returns `S = L₂₂ U₂₂` -- then the assembled block factors multiply to
    the original matrix. -/
theorem higham13_algorithm13_1_partitioned_lu_reconstructs
    {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing α]
    (L11 U11 A11 : Matrix m m α) (U12 A12 : Matrix m n α)
    (L21 A21 : Matrix n m α) (L22 U22 S A22 : Matrix n n α)
    (h11 : L11 * U11 = A11) (h12 : L11 * U12 = A12)
    (h21 : L21 * U11 = A21) (hSfact : L22 * U22 = S)
    (hSdef : S = A22 - L21 * U12) :
    Matrix.fromBlocks A11 A12 A21 A22 =
      Matrix.fromBlocks L11 0 L21 L22 * Matrix.fromBlocks U11 U12 0 U22 := by
  rw [Matrix.fromBlocks_multiply]
  simp [h11, h12, h21, hSfact, hSdef]

/-- **Algorithm 13.1 Schur complement form**.
    The partitioned solves `A₁₁ = L₁₁U₁₁`, `L₁₁U₁₂ = A₁₂`, and
    `L₂₁U₁₁ = A₂₁` imply `L₂₁U₁₂ = A₂₁ A₁₁^{-1} A₁₂`, so the step
    `S = A₂₂ - L₂₁U₁₂` is exactly the Schur complement
    `S = A₂₂ - A₂₁ A₁₁^{-1} A₁₂`. -/
theorem higham13_algorithm13_1_schur_complement_eq
    {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommRing α]
    (L11 U11 A11 : Matrix m m α) (U12 A12 : Matrix m n α)
    (L21 A21 : Matrix n m α) (S A22 : Matrix n n α)
    [Invertible L11] [Invertible U11] [Invertible A11]
    (h11 : L11 * U11 = A11) (h12 : L11 * U12 = A12)
    (h21 : L21 * U11 = A21) (hSdef : S = A22 - L21 * U12) :
    S = A22 - A21 * ⅟A11 * A12 := by
  have hAinv : ⅟A11 = ⅟U11 * ⅟L11 := by
    apply invOf_eq_right_inv
    calc
      A11 * (⅟U11 * ⅟L11) = (L11 * U11) * (⅟U11 * ⅟L11) := by
        rw [h11]
      _ = 1 := by
        simp [Matrix.mul_assoc]
  have hprod : L21 * U12 = A21 * ⅟A11 * A12 := by
    rw [hAinv, ← h12, ← h21]
    simp [Matrix.mul_assoc]
  rw [hSdef, hprod]

end NumStability
