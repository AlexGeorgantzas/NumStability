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
import NumStability.Source.Higham.Chapter13.Algorithm01

/-!
# Source.Higham.Chapter13.Algorithm04

This module formalizes the source-facing Chapter 13 statements for
`Algorithm04`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- **Algorithm 13.4**, exact output check for recursively partitioned LU.
    The first recursive call supplies `[A₁₁; A₂₁] = [L₁₁; L₂₁] U₁₁`,
    the triangular solve supplies `L₁₁ U₁₂ = A₁₂`, and the second recursive
    call supplies `S = L₂₂ U₂₂`; after forming `S = A₂₂ - L₂₁ U₁₂`, the
    assembled block factors multiply to the original matrix. -/
theorem higham13_algorithm13_4_recursive_partitioned_lu_reconstructs
    {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α]
    (L11 U11 A11 U12 A12 L21 A21 L22 U22 S A22 : Matrix n n α)
    (h11 : L11 * U11 = A11) (h21 : L21 * U11 = A21)
    (h12 : L11 * U12 = A12) (hSfact : L22 * U22 = S)
    (hSdef : S = A22 - L21 * U12) :
    Matrix.fromBlocks A11 A12 A21 A22 =
      Matrix.fromBlocks L11 0 L21 L22 * Matrix.fromBlocks U11 U12 0 U22 := by
  exact higham13_algorithm13_1_partitioned_lu_reconstructs
    L11 U11 A11 U12 A12 L21 A21 L22 U22 S A22 h11 h12 h21 hSfact hSdef

end NumStability
