import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# Chapter08 Equation10 ColumnPivotedQR Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapters1To9SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators
open scoped Topology
open scoped Matrix.Norms.Operator

namespace NumStability

/-- At one executed column-pivoted Householder stage, the squared diagonal
pivot dominates the squared 2-norm of every later active column.  This is the
strong full-column form underlying Higham's (8.10).

The maximality premise is not assumed: `colPivotSwap` is the repository's
executed maximal-column selection.  The only structural premise says that the
exact Householder reflector has annihilated the tail of its pivot column. -/
theorem higham8_10_colPivot_stage_full_column_sq_le_pivot_sq
    {q : ℕ}
    (A : Fin (q + 1) → Fin (q + 1) → ℝ)
    (P : Fin (q + 1) → Fin (q + 1) → ℝ)
    (hP : IsOrthogonal (q + 1) P)
    (hpivotTail : ∀ i : Fin q,
      matMulRect (q + 1) (q + 1) (q + 1) P (Wave20.colPivotSwap A)
        i.succ 0 = 0)
    (j : Fin q) :
    ∑ i : Fin (q + 1),
        (matMulRect (q + 1) (q + 1) (q + 1) P
          (Wave20.colPivotSwap A) i j.succ) ^ 2 ≤
      (matMulRect (q + 1) (q + 1) (q + 1) P
        (Wave20.colPivotSwap A) 0 0) ^ 2 := by
  let R : Fin (q + 1) → Fin (q + 1) → ℝ :=
    matMulRect (q + 1) (q + 1) (q + 1) P (Wave20.colPivotSwap A)
  have hjmax : columnFrob R j.succ ≤ columnFrob R 0 := by
    calc
      columnFrob R j.succ = columnFrob (Wave20.colPivotSwap A) j.succ := by
        exact columnFrob_orthogonal_left P (Wave20.colPivotSwap A) hP j.succ
      _ ≤ columnFrob (Wave20.colPivotSwap A) 0 :=
        Wave20.columnFrob_colPivotSwap_zero_max A j.succ
      _ = columnFrob R 0 := by
        symm
        exact columnFrob_orthogonal_left P (Wave20.colPivotSwap A) hP 0
  have hsq : columnFrob R j.succ ^ 2 ≤ columnFrob R 0 ^ 2 := by
    nlinarith [columnFrob_nonneg R j.succ, columnFrob_nonneg R 0]
  have hpivotSq : columnFrob R 0 ^ 2 = R 0 0 ^ 2 := by
    have htail : ∀ i : Fin q, R i.succ 0 = 0 := by
      intro i
      exact hpivotTail i
    rw [columnFrob_eq_vecNorm2, vecNorm2_sq]
    unfold vecNorm2Sq
    rw [Fin.sum_univ_succ]
    simp [htail]
  have hjSq : columnFrob R j.succ ^ 2 = ∑ i : Fin (q + 1), (R i j.succ) ^ 2 := by
    rw [columnFrob_eq_vecNorm2, vecNorm2_sq]
    rfl
  rw [hjSq, hpivotSq] at hsq
  exact hsq

/-- Higham (8.10), in the coordinates of an arbitrary active pivot stage:
for later active column `j+1`, the pivot square dominates the partial column
sum through row `j+1`.  The preceding theorem proves the stronger bound with
the whole active column, so this is an immediate nonnegative sub-sum. -/
theorem higham8_10_colPivot_stage_partial_column_sq_le_pivot_sq
    {q : ℕ}
    (A : Fin (q + 1) → Fin (q + 1) → ℝ)
    (P : Fin (q + 1) → Fin (q + 1) → ℝ)
    (hP : IsOrthogonal (q + 1) P)
    (hpivotTail : ∀ i : Fin q,
      matMulRect (q + 1) (q + 1) (q + 1) P (Wave20.colPivotSwap A)
        i.succ 0 = 0)
    (j : Fin q) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (q + 1) => i.val ≤ j.val + 1),
        (matMulRect (q + 1) (q + 1) (q + 1) P
          (Wave20.colPivotSwap A) i j.succ) ^ 2 ≤
      (matMulRect (q + 1) (q + 1) (q + 1) P
        (Wave20.colPivotSwap A) 0 0) ^ 2 := by
  calc
    ∑ i ∈ Finset.univ.filter (fun i : Fin (q + 1) => i.val ≤ j.val + 1),
        (matMulRect (q + 1) (q + 1) (q + 1) P
          (Wave20.colPivotSwap A) i j.succ) ^ 2 ≤
      ∑ i : Fin (q + 1),
        (matMulRect (q + 1) (q + 1) (q + 1) P
          (Wave20.colPivotSwap A) i j.succ) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun _ _ _ => sq_nonneg _)
    _ ≤ (matMulRect (q + 1) (q + 1) (q + 1) P
          (Wave20.colPivotSwap A) 0 0) ^ 2 :=
      higham8_10_colPivot_stage_full_column_sq_le_pivot_sq
        A P hP hpivotTail j

end NumStability
