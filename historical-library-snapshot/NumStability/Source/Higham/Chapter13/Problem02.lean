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
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance

/-!
# Source.Higham.Chapter13.Problem02

This module formalizes the source-facing Chapter 13 statements for
`Problem02`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- **Problem 13.2** column/1-norm witness for the direction
    point diagonal dominance does not imply block diagonal dominance.

    With 2-by-2 scalar blocks, this is
    `[[C, 0], [E, I]]`, where `C = [[1,-1],[-1,2]]` and
    `E` has only its `(1,2)` source entry equal to `1/2`.  The full
    matrix is column diagonally dominant, while the first block column
    violates block diagonal dominance for the 1-norm because the off-block
    1-norm contribution is `1/2` and `‖C⁻¹‖₁⁻¹ = 1/3`. -/
noncomputable def higham13_problem13_2_point_col_not_block_col_matrix : Fin 4 → Fin 4 → ℝ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => -1
    | 1, 0 => -1
    | 1, 1 => 2
    | 2, 1 => 1 / 2
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0

/-- Problem 13.2 1-norm block table for
    `higham13_problem13_2_point_col_not_block_col_matrix`.
    The diagonal inverse-norm reciprocal for the first block is `1/3`, while
    the lower-left off-block has 1-norm `1/2`. -/
noncomputable def higham13_problem13_2_point_col_not_block_col_blockNormOne :
    Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 3
    | 1, 1 => 1
    | 1, 0 => 1 / 2
    | _, _ => 0

/-- Problem 13.2 1-norm diagonal inverse-norm reciprocal table for
    `higham13_problem13_2_point_col_not_block_col_matrix`. -/
noncomputable def higham13_problem13_2_point_col_not_block_col_invDiagOne :
    Fin 2 → ℝ :=
  fun j =>
    match j.val with
    | 0 => 1 / 3
    | _ => 1

/-- **Problem 13.2**, 1-norm direction: the column point-diagonal witness is
    point diagonally dominant. -/
theorem higham13_problem13_2_point_col_not_block_col_point :
    IsDiagDominant 4 higham13_problem13_2_point_col_not_block_col_matrix := by
  intro j
  fin_cases j <;>
    rw [Fin.sum_univ_four] <;>
    norm_num [Fin.ext_iff, higham13_problem13_2_point_col_not_block_col_matrix]

/-- **Problem 13.2**, 1-norm direction: the same witness is not block diagonally
    dominant by columns for the displayed 2-by-2 block 1-norm table. -/
theorem higham13_problem13_2_point_col_not_block_col_not_block :
    ¬ IsBlockDiagDomCol 2
      higham13_problem13_2_point_col_not_block_col_blockNormOne
      higham13_problem13_2_point_col_not_block_col_invDiagOne := by
  intro h
  have hbad : (1 / 2 : ℝ) ≤ 1 / 3 := by
    simpa [higham13_problem13_2_point_col_not_block_col_blockNormOne,
      higham13_problem13_2_point_col_not_block_col_invDiagOne] using h 0
  norm_num at hbad

/-- **Problem 13.2** block/1-norm witness for the reverse direction.

    The matrix is block diagonal with first block `[[1,2],[0,1]]` and second
    block `I`.  Since all off-diagonal blocks are zero it is block diagonally
    dominant in the 1-norm, but column point diagonal dominance fails in the
    second scalar column. -/
noncomputable def higham13_problem13_2_block_not_point_matrix : Fin 4 → Fin 4 → ℝ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => 2
    | 1, 1 => 1
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0

/-- Problem 13.2 1-norm block table for the block-diagonal reverse witness.
    The first diagonal inverse has 1-norm `3`, hence reciprocal `1/3`;
    all off-diagonal block norms are zero. -/
noncomputable def higham13_problem13_2_block_not_point_blockNormOne :
    Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 3
    | 1, 1 => 1
    | _, _ => 0

/-- Problem 13.2 1-norm diagonal inverse-norm reciprocal table for the
    block-diagonal reverse witness. -/
noncomputable def higham13_problem13_2_block_not_point_invDiagOne : Fin 2 → ℝ :=
  fun j =>
    match j.val with
    | 0 => 1 / 3
    | _ => 1

/-- **Problem 13.2**, reverse 1-norm direction: the block-diagonal witness is
    block diagonally dominant by columns. -/
theorem higham13_problem13_2_block_not_point_block_col :
    IsBlockDiagDomCol 2
      higham13_problem13_2_block_not_point_blockNormOne
      higham13_problem13_2_block_not_point_invDiagOne := by
  intro j
  fin_cases j <;>
    norm_num [higham13_problem13_2_block_not_point_blockNormOne,
      higham13_problem13_2_block_not_point_invDiagOne]

/-- **Problem 13.2**, reverse 1-norm direction: the block-diagonal witness is
    not column point diagonally dominant. -/
theorem higham13_problem13_2_block_not_point_not_point_col :
    ¬ IsDiagDominant 4 higham13_problem13_2_block_not_point_matrix := by
  intro h
  have hbad := h 1
  rw [Fin.sum_univ_four] at hbad
  norm_num [higham13_problem13_2_block_not_point_matrix] at hbad

/-- **Problem 13.2** row/∞-norm witness for the direction
    point diagonal dominance does not imply block diagonal dominance.

    It is the row analogue of the 1-norm witness: the full matrix is row
    diagonally dominant, but the first block row violates block diagonal
    dominance for the infinity norm because the off-block contribution is
    `1/2 > 1/3 = ‖C⁻¹‖∞⁻¹`. -/
noncomputable def higham13_problem13_2_point_row_not_block_row_matrix : Fin 4 → Fin 4 → ℝ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 1
    | 0, 1 => -1
    | 1, 0 => -1
    | 1, 1 => 2
    | 1, 2 => 1 / 2
    | 2, 2 => 1
    | 3, 3 => 1
    | _, _ => 0

/-- Problem 13.2 infinity-norm block table for
    `higham13_problem13_2_point_row_not_block_row_matrix`.
    The upper-right off-block has infinity norm `1/2`; the first diagonal
    inverse has infinity norm `3`, hence reciprocal `1/3`. -/
noncomputable def higham13_problem13_2_point_row_not_block_row_blockNormInf :
    Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 3
    | 1, 1 => 1
    | 0, 1 => 1 / 2
    | _, _ => 0

/-- Problem 13.2 infinity-norm diagonal inverse-norm reciprocal table for the
    row witness. -/
noncomputable def higham13_problem13_2_point_row_not_block_row_invDiagInf :
    Fin 2 → ℝ :=
  fun i =>
    match i.val with
    | 0 => 1 / 3
    | _ => 1

/-- **Problem 13.2**, infinity-norm direction: the row point-diagonal witness is
    row diagonally dominant. -/
theorem higham13_problem13_2_point_row_not_block_row_point :
    IsRowDiagDominant 4 higham13_problem13_2_point_row_not_block_row_matrix := by
  intro i
  fin_cases i <;>
    rw [Fin.sum_univ_four] <;>
    norm_num [Fin.ext_iff, higham13_problem13_2_point_row_not_block_row_matrix]

/-- **Problem 13.2**, infinity-norm direction: the same witness is not block
    diagonally dominant by rows for the displayed 2-by-2 block infinity-norm
    table. -/
theorem higham13_problem13_2_point_row_not_block_row_not_block :
    ¬ IsBlockDiagDomRow 2
      higham13_problem13_2_point_row_not_block_row_blockNormInf
      higham13_problem13_2_point_row_not_block_row_invDiagInf := by
  intro h
  have hbad : (1 / 2 : ℝ) ≤ 1 / 3 := by
    simpa [higham13_problem13_2_point_row_not_block_row_blockNormInf,
      higham13_problem13_2_point_row_not_block_row_invDiagInf] using h 0
  norm_num at hbad

/-- Problem 13.2 infinity-norm block table for the block-diagonal reverse
    witness.  All off-diagonal blocks are zero; the first diagonal inverse has
    infinity norm `3`, hence reciprocal `1/3`. -/
noncomputable def higham13_problem13_2_block_not_point_blockNormInf :
    Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 3
    | 1, 1 => 1
    | _, _ => 0

/-- Problem 13.2 infinity-norm diagonal inverse-norm reciprocal table for the
    block-diagonal reverse witness. -/
noncomputable def higham13_problem13_2_block_not_point_invDiagInf : Fin 2 → ℝ :=
  fun i =>
    match i.val with
    | 0 => 1 / 3
    | _ => 1

/-- **Problem 13.2**, reverse infinity-norm direction: the block-diagonal witness
    is block diagonally dominant by rows. -/
theorem higham13_problem13_2_block_not_point_block_row :
    IsBlockDiagDomRow 2
      higham13_problem13_2_block_not_point_blockNormInf
      higham13_problem13_2_block_not_point_invDiagInf := by
  intro i
  fin_cases i <;>
    norm_num [higham13_problem13_2_block_not_point_blockNormInf,
      higham13_problem13_2_block_not_point_invDiagInf]

/-- **Problem 13.2**, reverse infinity-norm direction: the block-diagonal witness
    is not row point diagonally dominant. -/
theorem higham13_problem13_2_block_not_point_not_point_row :
    ¬ IsRowDiagDominant 4 higham13_problem13_2_block_not_point_matrix := by
  intro h
  have hbad := h 0
  rw [Fin.sum_univ_four] at hbad
  norm_num [higham13_problem13_2_block_not_point_matrix] at hbad

/-- **Problem 13.2** (Higham, 2nd ed., Chapter 13, p. 257):
    for the 1-norm and infinity norm, point diagonal dominance and block
    diagonal dominance do not imply each other.  The 1-norm statements use
    column diagonal dominance and block-column dominance; the infinity-norm
    statements use row diagonal dominance and block-row dominance. -/
theorem higham13_problem13_2_incomparability :
    (IsDiagDominant 4 higham13_problem13_2_point_col_not_block_col_matrix ∧
      ¬ IsBlockDiagDomCol 2
        higham13_problem13_2_point_col_not_block_col_blockNormOne
        higham13_problem13_2_point_col_not_block_col_invDiagOne) ∧
    (IsBlockDiagDomCol 2
        higham13_problem13_2_block_not_point_blockNormOne
        higham13_problem13_2_block_not_point_invDiagOne ∧
      ¬ IsDiagDominant 4 higham13_problem13_2_block_not_point_matrix) ∧
    (IsRowDiagDominant 4 higham13_problem13_2_point_row_not_block_row_matrix ∧
      ¬ IsBlockDiagDomRow 2
        higham13_problem13_2_point_row_not_block_row_blockNormInf
        higham13_problem13_2_point_row_not_block_row_invDiagInf) ∧
    (IsBlockDiagDomRow 2
        higham13_problem13_2_block_not_point_blockNormInf
        higham13_problem13_2_block_not_point_invDiagInf ∧
      ¬ IsRowDiagDominant 4 higham13_problem13_2_block_not_point_matrix) :=
  ⟨⟨higham13_problem13_2_point_col_not_block_col_point,
      higham13_problem13_2_point_col_not_block_col_not_block⟩,
    ⟨higham13_problem13_2_block_not_point_block_col,
      higham13_problem13_2_block_not_point_not_point_col⟩,
    ⟨higham13_problem13_2_point_row_not_block_row_point,
      higham13_problem13_2_point_row_not_block_row_not_block⟩,
    ⟨higham13_problem13_2_block_not_point_block_row,
      higham13_problem13_2_block_not_point_not_point_row⟩⟩

end NumStability
