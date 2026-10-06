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
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance

/-!
# Source.Higham.Chapter13.Problem03

This module formalizes the source-facing Chapter 13 statements for
`Problem03`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- The scalar-block witness for **Problem 13.3**:
    `[[1, -1], [-1, 1]]`.  It is symmetric with positive diagonal and is
    row block diagonally dominant for one-by-one scalar blocks, but is not SPD. -/
def higham13_problem13_3_counterexample_matrix : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 1 else -1

/-- **Problem 13.3**: the counterexample matrix is symmetric. -/
theorem higham13_problem13_3_counterexample_symmetric :
    ∀ i j : Fin 2,
      higham13_problem13_3_counterexample_matrix i j =
        higham13_problem13_3_counterexample_matrix j i := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [higham13_problem13_3_counterexample_matrix]

/-- **Problem 13.3**: the counterexample matrix has positive diagonal entries. -/
theorem higham13_problem13_3_counterexample_positive_diagonal :
    ∀ i : Fin 2, 0 < higham13_problem13_3_counterexample_matrix i i := by
  intro i
  fin_cases i <;> norm_num [higham13_problem13_3_counterexample_matrix]

/-- **Problem 13.3**: as one-by-one scalar blocks, the counterexample is row
    block diagonally dominant.  The block-norm table is `|Aᵢⱼ|`, and the diagonal
    inverse-norm reciprocal is `1` on each scalar diagonal block. -/
theorem higham13_problem13_3_counterexample_row_block_diag_dom :
    IsBlockDiagDomRow 2
      (fun i j : Fin 2 => |higham13_problem13_3_counterexample_matrix i j|)
      (fun _ : Fin 2 => 1) := by
  intro i
  fin_cases i <;>
    norm_num [higham13_problem13_3_counterexample_matrix]

/-- The same Problem 13.3 witness is singular.  This is a small source-audit
    check for Theorem 13.7: nonstrict block diagonal dominance with positive
    scalar diagonal blocks does not by itself supply the nonsingularity
    hypothesis used by the block-LU existence theorem. -/
theorem higham13_problem13_3_counterexample_singular :
    Matrix.det (higham13_problem13_3_counterexample_matrix :
      Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  rw [Matrix.det_fin_two]
  simp [higham13_problem13_3_counterexample_matrix]

/-- **Problem 13.3**: the counterexample is not positive definite.  The vector
    `(1,1)` is nonzero and has quadratic form zero. -/
theorem higham13_problem13_3_counterexample_not_spd :
    ¬ IsSymPosDef 2 higham13_problem13_3_counterexample_matrix := by
  intro hSPD
  let x : Fin 2 → ℝ := fun _ => 1
  have hx : ∃ i : Fin 2, x i ≠ 0 := by
    refine ⟨0, ?_⟩
    simp [x]
  have hpos := hSPD.2 x hx
  have hzero :
      (∑ i : Fin 2, ∑ j : Fin 2,
        x i * higham13_problem13_3_counterexample_matrix i j * x j) = 0 := by
    norm_num [x, higham13_problem13_3_counterexample_matrix]
  linarith

/-- **Problem 13.3** (Higham, 2nd ed., Chapter 13, p. 257): a symmetric matrix
    with positive diagonal entries and row block diagonal dominance need not be
    positive definite.  The witness is the scalar-block matrix
    `[[1, -1], [-1, 1]]`. -/
theorem higham13_problem13_3_counterexample :
    (∀ i j : Fin 2,
      higham13_problem13_3_counterexample_matrix i j =
        higham13_problem13_3_counterexample_matrix j i) ∧
    (∀ i : Fin 2, 0 < higham13_problem13_3_counterexample_matrix i i) ∧
    IsBlockDiagDomRow 2
      (fun i j : Fin 2 => |higham13_problem13_3_counterexample_matrix i j|)
      (fun _ : Fin 2 => 1) ∧
    ¬ IsSymPosDef 2 higham13_problem13_3_counterexample_matrix :=
  ⟨higham13_problem13_3_counterexample_symmetric,
    higham13_problem13_3_counterexample_positive_diagonal,
    higham13_problem13_3_counterexample_row_block_diag_dom,
    higham13_problem13_3_counterexample_not_spd⟩

end NumStability
