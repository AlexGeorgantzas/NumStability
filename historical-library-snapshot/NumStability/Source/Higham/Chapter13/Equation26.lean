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
import NumStability.Source.Higham.Chapter13.Equation20

/-!
# Source.Higham.Chapter13.Equation26

This module formalizes the source-facing Chapter 13 statements for
`Equation26`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- **Equation (13.26)**, Problem 13.4 partition display.
    This is the same four-block partition as (13.20), with the additional
    source assumption that the leading block is nonsingular.  The nonsingularity
    is recorded as an `Invertible` hypothesis for downstream Schur-complement
    and condition-number work; the display itself is again `fromBlocks`. -/
theorem higham13_eq13_26_partition {r s α : Type*}
    [Fintype r] [DecidableEq r] [Semiring α]
    (A : Matrix (r ⊕ s) (r ⊕ s) α) [Invertible A.toBlocks₁₁] :
    A = Matrix.fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂ := by
  exact higham13_eq13_20_partition A

end NumStability
