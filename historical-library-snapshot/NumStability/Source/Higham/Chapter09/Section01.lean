import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LU.SpecialMatrices
import NumStability.Algorithms.LU.Tridiagonal
import NumStability.Algorithms.LU.TridiagonalCond
import NumStability.Algorithms.LU.TridiagonalRecurrence
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Higham Chapter 9: Section01

Canonical source-correspondence owner from Chapter 9 destination-DAG layer 1.
-/

namespace NumStability

open scoped BigOperators
open ComplexConjugate
open Matrix

/-- **Section 9.1**, partial-pivoting first-stage choice: among the active
rows `i >= k`, row `r` has maximal absolute value in column `k`. -/
def higham9_1_partialPivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r : Fin n) : Prop :=
  k.val ≤ r.val ∧
    ∀ i : Fin n, k.val ≤ i.val → |Astage i k| ≤ |Astage r k|

/-- **Section 9.1**, complete-pivoting first-stage choice: among the active
submatrix `i,j >= k`, entry `(r,s)` has maximal absolute value. -/
def higham9_1_completePivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s : Fin n) : Prop :=
  k.val ≤ r.val ∧ k.val ≤ s.val ∧
    ∀ i j : Fin n, k.val ≤ i.val → k.val ≤ j.val →
      |Astage i j| ≤ |Astage r s|

/-- **Section 9.1**, rook-pivoting accepted pivot: the selected entry is
maximal in both its active column and its active row. -/
def higham9_1_rookPivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s : Fin n) : Prop :=
  k.val ≤ r.val ∧ k.val ≤ s.val ∧
    (∀ i : Fin n, k.val ≤ i.val → |Astage i s| ≤ |Astage r s|) ∧
    (∀ j : Fin n, k.val ≤ j.val → |Astage r j| ≤ |Astage r s|)

/-- **Section 9.1**, partial-pivoting row choice exists on the finite active
column. -/
theorem higham9_1_exists_partialPivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n) :
    ∃ r : Fin n, higham9_1_partialPivotChoice Astage k r := by
  classical
  let active : Finset (Fin n) := Finset.univ.filter fun i => k.val ≤ i.val
  have hactive : active.Nonempty := by
    refine ⟨k, ?_⟩
    simp [active]
  obtain ⟨r, hr_mem, hr_max⟩ :=
    Finset.exists_max_image active (fun i : Fin n => |Astage i k|) hactive
  refine ⟨r, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hr_mem).2
  · intro i hi
    exact hr_max i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

/-- **Section 9.1**, complete-pivoting entry choice exists on the finite
active submatrix. -/
theorem higham9_1_exists_completePivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n) :
    ∃ r s : Fin n, higham9_1_completePivotChoice Astage k r s := by
  classical
  let active : Finset (Fin n × Fin n) :=
    Finset.univ.filter fun p => k.val ≤ p.1.val ∧ k.val ≤ p.2.val
  have hactive : active.Nonempty := by
    refine ⟨(k, k), ?_⟩
    simp [active]
  obtain ⟨p, hp_mem, hp_max⟩ :=
    Finset.exists_max_image active
      (fun p : Fin n × Fin n => |Astage p.1 p.2|)
      hactive
  refine ⟨p.1, p.2, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hp_mem).2.1
  · exact (Finset.mem_filter.mp hp_mem).2.2
  · intro i j hi hj
    exact hp_max (i, j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), ⟨hi, hj⟩⟩)

/-- A complete-pivoting maximum is also an accepted rook-pivoting entry. -/
theorem higham9_1_rookPivotChoice_of_completePivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s : Fin n)
    (hchoice : higham9_1_completePivotChoice Astage k r s) :
    higham9_1_rookPivotChoice Astage k r s := by
  refine ⟨hchoice.1, hchoice.2.1, ?_, ?_⟩
  · intro i hi
    exact hchoice.2.2 i s hi hchoice.2.1
  · intro j hj
    exact hchoice.2.2 r j hchoice.1 hj

/-- **Section 9.1**, an accepted rook-pivoting entry exists by taking a
complete-pivoting maximum. -/
theorem higham9_1_exists_rookPivotChoice {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n) :
    ∃ r s : Fin n, higham9_1_rookPivotChoice Astage k r s := by
  obtain ⟨r, s, hchoice⟩ :=
    higham9_1_exists_completePivotChoice Astage k
  exact ⟨r, s, higham9_1_rookPivotChoice_of_completePivotChoice
    Astage k r s hchoice⟩

/-- A partial-pivoting maximum is nonzero if the active column contains a
nonzero entry. -/
theorem higham9_1_partialPivotChoice_pivot_ne_zero_of_exists {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r : Fin n)
    (hchoice : higham9_1_partialPivotChoice Astage k r)
    (hactive : ∃ i : Fin n, k.val ≤ i.val ∧ Astage i k ≠ 0) :
    Astage r k ≠ 0 := by
  rcases hactive with ⟨i, hi, hne⟩
  intro hr
  have hle : |Astage i k| ≤ 0 := by
    simpa [hr] using hchoice.2 i hi
  have hzero : |Astage i k| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact hne (abs_eq_zero.mp hzero)

/-- A complete-pivoting maximum is nonzero if the active submatrix contains a
nonzero entry. -/
theorem higham9_1_completePivotChoice_pivot_ne_zero_of_exists {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s : Fin n)
    (hchoice : higham9_1_completePivotChoice Astage k r s)
    (hactive : ∃ i j : Fin n, k.val ≤ i.val ∧ k.val ≤ j.val ∧
      Astage i j ≠ 0) :
    Astage r s ≠ 0 := by
  rcases hactive with ⟨i, j, hi, hj, hne⟩
  intro hrs
  have hle : |Astage i j| ≤ 0 := by
    simpa [hrs] using hchoice.2.2 i j hi hj
  have hzero : |Astage i j| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact hne (abs_eq_zero.mp hzero)

/-- A partial-pivoting row with a nonzero selected pivot exists whenever the
active column contains a nonzero entry. -/
theorem higham9_1_exists_partialPivotChoice_pivot_ne_zero {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive : ∃ i : Fin n, k.val ≤ i.val ∧ Astage i k ≠ 0) :
    ∃ r : Fin n,
      higham9_1_partialPivotChoice Astage k r ∧ Astage r k ≠ 0 := by
  obtain ⟨r, hchoice⟩ := higham9_1_exists_partialPivotChoice Astage k
  exact ⟨r, hchoice,
    higham9_1_partialPivotChoice_pivot_ne_zero_of_exists
      Astage k r hchoice hactive⟩

/-- A complete-pivoting entry with a nonzero selected pivot exists whenever the
active submatrix contains a nonzero entry. -/
theorem higham9_1_exists_completePivotChoice_pivot_ne_zero {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive : ∃ i j : Fin n, k.val ≤ i.val ∧ k.val ≤ j.val ∧
      Astage i j ≠ 0) :
    ∃ r s : Fin n,
      higham9_1_completePivotChoice Astage k r s ∧ Astage r s ≠ 0 := by
  obtain ⟨r, s, hchoice⟩ := higham9_1_exists_completePivotChoice Astage k
  exact ⟨r, s, hchoice,
    higham9_1_completePivotChoice_pivot_ne_zero_of_exists
      Astage k r s hchoice hactive⟩

/-- **Section 9.1**, a nonsingular active matrix has at least one nonzero
entry.  This is the determinant side condition needed to start a
complete-pivoting trace. -/
theorem higham9_1_exists_entry_ne_zero_of_det_ne_zero {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∃ i j : Fin (m + 1), A i j ≠ 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hzero :
      (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = 0 := by
    ext i j
    exact hnone i j
  rw [hzero] at hdet
  have hdet_zero :
      Matrix.det (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) = 0 := by
    rw [Matrix.det_zero]
    exact ⟨0⟩
  exact hdet hdet_zero

/-- **Section 9.1**, a nonsingular matrix admits a nonzero first complete
pivot.  The active submatrix is the full matrix at `k = 0`. -/
theorem higham9_1_exists_first_completePivotChoice_pivot_ne_zero_of_det_ne_zero
    {m : ℕ} (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hdet :
      Matrix.det (Matrix.of A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) ≠ 0) :
    ∃ r s : Fin (m + 1),
      higham9_1_completePivotChoice A 0 r s ∧ A r s ≠ 0 := by
  obtain ⟨i, j, hij⟩ :=
    higham9_1_exists_entry_ne_zero_of_det_ne_zero A hdet
  exact higham9_1_exists_completePivotChoice_pivot_ne_zero A 0
    ⟨i, j, Nat.zero_le i.val, Nat.zero_le j.val, hij⟩

/-- Partial pivoting gives multipliers bounded by one in absolute value. -/
theorem higham9_1_partialPivot_multiplier_abs_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r i : Fin n)
    (hchoice : higham9_1_partialPivotChoice Astage k r)
    (hpivot : Astage r k ≠ 0)
    (hi : k.val ≤ i.val) :
    |Astage i k / Astage r k| ≤ 1 := by
  have hcol : |Astage i k| ≤ |Astage r k| := hchoice.2 i hi
  have hden_pos : 0 < |Astage r k| := abs_pos.mpr hpivot
  rw [abs_div, div_le_iff₀ hden_pos]
  simpa using hcol

/-- Complete pivoting gives column multipliers bounded by one for the selected
pivot column. -/
theorem higham9_1_completePivot_column_multiplier_abs_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s i : Fin n)
    (hchoice : higham9_1_completePivotChoice Astage k r s)
    (hpivot : Astage r s ≠ 0)
    (hi : k.val ≤ i.val) :
    |Astage i s / Astage r s| ≤ 1 := by
  have hcol : |Astage i s| ≤ |Astage r s| :=
    hchoice.2.2 i s hi hchoice.2.1
  have hden_pos : 0 < |Astage r s| := abs_pos.mpr hpivot
  rw [abs_div, div_le_iff₀ hden_pos]
  simpa using hcol

/-- Complete pivoting bounds every active entry by the selected pivot, hence
any active entry divided by the pivot has absolute value at most one. -/
theorem higham9_1_completePivot_active_entry_ratio_abs_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s i j : Fin n)
    (hchoice : higham9_1_completePivotChoice Astage k r s)
    (hpivot : Astage r s ≠ 0)
    (hi : k.val ≤ i.val) (hj : k.val ≤ j.val) :
    |Astage i j / Astage r s| ≤ 1 := by
  have hentry : |Astage i j| ≤ |Astage r s| :=
    hchoice.2.2 i j hi hj
  have hden_pos : 0 < |Astage r s| := abs_pos.mpr hpivot
  rw [abs_div, div_le_iff₀ hden_pos]
  simpa using hentry

/-- Rook pivoting gives column multipliers bounded by one for the accepted
pivot column. -/
theorem higham9_1_rookPivot_column_multiplier_abs_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s i : Fin n)
    (hchoice : higham9_1_rookPivotChoice Astage k r s)
    (hpivot : Astage r s ≠ 0)
    (hi : k.val ≤ i.val) :
    |Astage i s / Astage r s| ≤ 1 := by
  have hcol : |Astage i s| ≤ |Astage r s| := hchoice.2.2.1 i hi
  have hden_pos : 0 < |Astage r s| := abs_pos.mpr hpivot
  rw [abs_div, div_le_iff₀ hden_pos]
  simpa using hcol

/-- Rook pivoting gives row-side entry ratios bounded by one for the accepted
pivot row. -/
theorem higham9_1_rookPivot_row_multiplier_abs_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r s j : Fin n)
    (hchoice : higham9_1_rookPivotChoice Astage k r s)
    (hpivot : Astage r s ≠ 0)
    (hj : k.val ≤ j.val) :
    |Astage r j / Astage r s| ≤ 1 := by
  have hrow : |Astage r j| ≤ |Astage r s| := hchoice.2.2.2 j hj
  have hden_pos : 0 < |Astage r s| := abs_pos.mpr hpivot
  rw [abs_div, div_le_iff₀ hden_pos]
  simpa using hrow

/-- First-stage partial pivoting can choose a nonzero pivot with all active
column multipliers bounded by one whenever the active column is nonzero. -/
theorem higham9_1_exists_partialPivot_nonzero_and_multiplier_bound {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive : ∃ i : Fin n, k.val ≤ i.val ∧ Astage i k ≠ 0) :
    ∃ r : Fin n,
      higham9_1_partialPivotChoice Astage k r ∧
      Astage r k ≠ 0 ∧
      ∀ i : Fin n, k.val ≤ i.val → |Astage i k / Astage r k| ≤ 1 := by
  obtain ⟨r, hchoice, hpivot⟩ :=
    higham9_1_exists_partialPivotChoice_pivot_ne_zero Astage k hactive
  exact ⟨r, hchoice, hpivot, fun i hi =>
    higham9_1_partialPivot_multiplier_abs_le_one Astage k r i
      hchoice hpivot hi⟩

/-- First-stage complete pivoting can choose a nonzero pivot with active
column and whole-active-submatrix ratios bounded by one whenever the active
submatrix is nonzero. -/
theorem higham9_1_exists_completePivot_nonzero_and_ratio_bounds {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive : ∃ i j : Fin n, k.val ≤ i.val ∧ k.val ≤ j.val ∧
      Astage i j ≠ 0) :
    ∃ r s : Fin n,
      higham9_1_completePivotChoice Astage k r s ∧
      Astage r s ≠ 0 ∧
      (∀ i : Fin n, k.val ≤ i.val → |Astage i s / Astage r s| ≤ 1) ∧
      (∀ i j : Fin n, k.val ≤ i.val → k.val ≤ j.val →
        |Astage i j / Astage r s| ≤ 1) := by
  obtain ⟨r, s, hchoice, hpivot⟩ :=
    higham9_1_exists_completePivotChoice_pivot_ne_zero Astage k hactive
  exact ⟨r, s, hchoice, hpivot,
    (fun i hi =>
      higham9_1_completePivot_column_multiplier_abs_le_one Astage k r s i
        hchoice hpivot hi),
    (fun i j hi hj =>
      higham9_1_completePivot_active_entry_ratio_abs_le_one Astage k r s i j
        hchoice hpivot hi hj)⟩

/-- A complete-pivoting maximum supplies an accepted rook pivot with nonzero
pivot and row/column active ratios bounded by one whenever the active
submatrix is nonzero. -/
theorem higham9_1_exists_rookPivot_nonzero_and_ratio_bounds {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive : ∃ i j : Fin n, k.val ≤ i.val ∧ k.val ≤ j.val ∧
      Astage i j ≠ 0) :
    ∃ r s : Fin n,
      higham9_1_rookPivotChoice Astage k r s ∧
      Astage r s ≠ 0 ∧
      (∀ i : Fin n, k.val ≤ i.val → |Astage i s / Astage r s| ≤ 1) ∧
      (∀ j : Fin n, k.val ≤ j.val → |Astage r j / Astage r s| ≤ 1) := by
  obtain ⟨r, s, hcomplete, hpivot⟩ :=
    higham9_1_exists_completePivotChoice_pivot_ne_zero Astage k hactive
  have hrook : higham9_1_rookPivotChoice Astage k r s :=
    higham9_1_rookPivotChoice_of_completePivotChoice Astage k r s hcomplete
  exact ⟨r, s, hrook, hpivot,
    (fun i hi =>
      higham9_1_rookPivot_column_multiplier_abs_le_one Astage k r s i
        hrook hpivot hi),
    (fun j hj =>
      higham9_1_rookPivot_row_multiplier_abs_le_one Astage k r s j
        hrook hpivot hj)⟩

/-- **Algorithm 9.2**: Doolittle's method certificate for the computed factors. -/
abbrev higham9_2_DoolittleLU (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (fp : FPModel) : Prop :=
  DoolittleLU n A L_hat U_hat fp

end NumStability
