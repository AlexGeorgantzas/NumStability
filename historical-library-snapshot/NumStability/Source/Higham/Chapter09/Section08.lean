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
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LU.SpecialMatrices
import NumStability.Algorithms.LU.Tridiagonal
import NumStability.Algorithms.LU.TridiagonalCond
import NumStability.Algorithms.LU.TridiagonalRecurrence
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter09.Section06

/-!
# Higham Chapter 9: Section08

Canonical source-correspondence owner from Chapter 9 destination-DAG layer 6.
-/

namespace NumStability

open scoped BigOperators
open ComplexConjugate
open Matrix

/-- **Equation (9.24)**: scaled right-hand side. -/
noncomputable def higham9_24_scaledRhs {n : ℕ}
    (D1 : Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => D1 i * b i

/-- **Equation (9.24)**: change of variables `y = D₂⁻¹ x`. -/
noncomputable def higham9_24_scaledUnknown {n : ℕ}
    (D2 : Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (D2 i)⁻¹ * x i

/-- **Equation (9.24)**: inverse change of variables `x = D₂ y`. -/
noncomputable def higham9_24_unscaledUnknown {n : ℕ}
    (D2 : Fin n → ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => D2 i * y i

/-- **Equation (9.24)**, `x = D₂(D₂⁻¹x)` for componentwise nonsingular
right scaling. -/
theorem higham9_24_unscaledUnknown_scaledUnknown {n : ℕ}
    (D2 x : Fin n → ℝ) (hD2 : ∀ j : Fin n, D2 j ≠ 0) :
    higham9_24_unscaledUnknown D2 (higham9_24_scaledUnknown D2 x) = x := by
  funext j
  unfold higham9_24_unscaledUnknown higham9_24_scaledUnknown
  field_simp [hD2 j]

/-- **Equation (9.24)**, `D₂⁻¹(D₂y) = y` for componentwise nonsingular
right scaling. -/
theorem higham9_24_scaledUnknown_unscaledUnknown {n : ℕ}
    (D2 y : Fin n → ℝ) (hD2 : ∀ j : Fin n, D2 j ≠ 0) :
    higham9_24_scaledUnknown D2 (higham9_24_unscaledUnknown D2 y) = y := by
  funext j
  unfold higham9_24_scaledUnknown higham9_24_unscaledUnknown
  field_simp [hD2 j]

/-- **Equation (9.24)**: scaling preserves exact solutions when `D₂` is
nonsingular componentwise. -/
theorem higham9_24_scaled_system_equiv {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b x D1 D2 : Fin n → ℝ)
    (hD2 : ∀ j : Fin n, D2 j ≠ 0)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i) :
    ∀ i, ∑ j : Fin n,
        higham9_24_scaledMatrix D1 D2 A i j *
          higham9_24_scaledUnknown D2 x j =
        higham9_24_scaledRhs D1 b i := by
  intro i
  unfold higham9_24_scaledMatrix higham9_24_scaledUnknown higham9_24_scaledRhs
  have hterm : ∀ j : Fin n,
      (D1 i * A i j * D2 j) * ((D2 j)⁻¹ * x j) =
        D1 i * (A i j * x j) := by
    intro j
    field_simp [hD2 j]
  calc
    ∑ j : Fin n, (D1 i * A i j * D2 j) * ((D2 j)⁻¹ * x j)
        = ∑ j : Fin n, D1 i * (A i j * x j) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hterm j
    _ = D1 i * ∑ j : Fin n, A i j * x j := by
          rw [Finset.mul_sum]
    _ = D1 i * b i := by
          rw [hAx i]

/-- **Equation (9.24)**: an exact solution of the scaled system gives an exact
solution of the original system after the inverse change of variables
`x = D₂ y`, when `D₁` is componentwise nonsingular. -/
theorem higham9_24_original_system_of_scaled_system {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b y D1 D2 : Fin n → ℝ)
    (hD1 : ∀ i : Fin n, D1 i ≠ 0)
    (hscaled : ∀ i, ∑ j : Fin n,
        higham9_24_scaledMatrix D1 D2 A i j * y j =
        higham9_24_scaledRhs D1 b i) :
    ∀ i, ∑ j : Fin n,
        A i j * higham9_24_unscaledUnknown D2 y j = b i := by
  intro i
  unfold higham9_24_unscaledUnknown
  have hscaled_i := hscaled i
  unfold higham9_24_scaledMatrix higham9_24_scaledRhs at hscaled_i
  have hsum :
      (∑ j : Fin n, (D1 i * A i j * D2 j) * y j) =
        D1 i * ∑ j : Fin n, A i j * (D2 j * y j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmul :
      D1 i * (∑ j : Fin n, A i j * (D2 j * y j)) = D1 i * b i := by
    simpa [hsum] using hscaled_i
  exact mul_left_cancel₀ (hD1 i) hmul

/-- **Equation (9.24)**: source-facing equivalence between the original system
`Ax = b` and the two-sided diagonally scaled system
`(D₁AD₂)(D₂⁻¹x) = D₁b`. -/
theorem higham9_24_scaled_system_iff_original_system {n : ℕ}
    (A : Fin n → Fin n → ℝ) (b x D1 D2 : Fin n → ℝ)
    (hD1 : ∀ i : Fin n, D1 i ≠ 0)
    (hD2 : ∀ j : Fin n, D2 j ≠ 0) :
    (∀ i, ∑ j : Fin n, A i j * x j = b i) ↔
      (∀ i, ∑ j : Fin n,
          higham9_24_scaledMatrix D1 D2 A i j *
            higham9_24_scaledUnknown D2 x j =
          higham9_24_scaledRhs D1 b i) := by
  constructor
  · exact higham9_24_scaled_system_equiv A b x D1 D2 hD2
  · intro hscaled
    have horiginal :=
      higham9_24_original_system_of_scaled_system
        A b (higham9_24_scaledUnknown D2 x) D1 D2 hD1 hscaled
    simpa [higham9_24_unscaledUnknown_scaledUnknown D2 x hD2] using horiginal

/-- **Equation (9.24)**, Matrix-notation forward direction for two-sided
diagonal scaling. -/
theorem higham9_24_matrix_scaled_system_equiv {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b x D1 D2 : Fin n → ℝ)
    (hD2 : ∀ j : Fin n, D2 j ≠ 0)
    (hAx : Matrix.mulVec A x = b) :
    Matrix.mulVec (higham9_24_scaledMatrix D1 D2 A)
        (higham9_24_scaledUnknown D2 x) =
      higham9_24_scaledRhs D1 b := by
  funext i
  have hAx_entries : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i := by
    intro i
    simpa [Matrix.mulVec, dotProduct] using congrFun hAx i
  simpa [Matrix.mulVec, dotProduct] using
    higham9_24_scaled_system_equiv
      (A := A) (b := b) (x := x) (D1 := D1) (D2 := D2) hD2 hAx_entries i

/-- **Equation (9.24)**, Matrix-notation reverse direction for two-sided
diagonal scaling. -/
theorem higham9_24_matrix_original_system_of_scaled_system {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b y D1 D2 : Fin n → ℝ)
    (hD1 : ∀ i : Fin n, D1 i ≠ 0)
    (hscaled :
      Matrix.mulVec (higham9_24_scaledMatrix D1 D2 A) y =
        higham9_24_scaledRhs D1 b) :
    Matrix.mulVec A (higham9_24_unscaledUnknown D2 y) = b := by
  funext i
  have hscaled_entries : ∀ i : Fin n,
      ∑ j : Fin n, higham9_24_scaledMatrix D1 D2 A i j * y j =
        higham9_24_scaledRhs D1 b i := by
    intro i
    simpa [Matrix.mulVec, dotProduct] using congrFun hscaled i
  simpa [Matrix.mulVec, dotProduct] using
    higham9_24_original_system_of_scaled_system
      (A := A) (b := b) (y := y) (D1 := D1) (D2 := D2) hD1 hscaled_entries i

/-- **Equation (9.24)**, Matrix-notation source-facing equivalence between
`A *ᵥ x = b` and the two-sided diagonally scaled system. -/
theorem higham9_24_matrix_scaled_system_iff_original_system {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b x D1 D2 : Fin n → ℝ)
    (hD1 : ∀ i : Fin n, D1 i ≠ 0)
    (hD2 : ∀ j : Fin n, D2 j ≠ 0) :
    Matrix.mulVec A x = b ↔
      Matrix.mulVec (higham9_24_scaledMatrix D1 D2 A)
          (higham9_24_scaledUnknown D2 x) =
        higham9_24_scaledRhs D1 b := by
  constructor
  · exact higham9_24_matrix_scaled_system_equiv A b x D1 D2 hD2
  · intro hscaled
    have horiginal :=
      higham9_24_matrix_original_system_of_scaled_system
        A b (higham9_24_scaledUnknown D2 x) D1 D2 hD1 hscaled
    simpa [higham9_24_unscaledUnknown_scaledUnknown D2 x hD2] using horiginal

/-- **Equation (9.25)**: trailing row `∞`-norm used by implicit row scaling. -/
noncomputable def higham9_25_trailingRowInf {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k i : Fin n) : ℝ :=
  Finset.sup' (Finset.univ.filter (fun j : Fin n => k.val ≤ j.val))
    ⟨k, by simp⟩ (fun j => |Astage i j|)

/-- **Equation (9.25)**, the trailing row norm dominates the active pivot-column
entry because column `k` belongs to the trailing index set. -/
theorem higham9_25_abs_stage_entry_le_trailingRowInf {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k i : Fin n) :
    |Astage i k| ≤ higham9_25_trailingRowInf Astage k i := by
  unfold higham9_25_trailingRowInf
  exact Finset.le_sup' (fun j : Fin n => |Astage i j|) (by simp)

/-- **Equation (9.25)**, nonnegativity of the trailing row norm. -/
theorem higham9_25_trailingRowInf_nonneg {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k i : Fin n) :
    0 ≤ higham9_25_trailingRowInf Astage k i :=
  le_trans (abs_nonneg (Astage i k))
    (higham9_25_abs_stage_entry_le_trailingRowInf Astage k i)

/-- **Equation (9.25)**, nonnegativity of the implicit row-scaling pivot ratio. -/
theorem higham9_25_scaled_pivot_ratio_nonneg {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k i : Fin n) :
    0 ≤ |Astage i k| / higham9_25_trailingRowInf Astage k i :=
  div_nonneg (abs_nonneg (Astage i k))
    (higham9_25_trailingRowInf_nonneg Astage k i)

/-- **Equation (9.25)**, the implicit row-scaling pivot ratio is at most one
whenever the trailing row norm is nonzero. -/
theorem higham9_25_scaled_pivot_ratio_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k i : Fin n)
    (hrow : higham9_25_trailingRowInf Astage k i ≠ 0) :
    |Astage i k| / higham9_25_trailingRowInf Astage k i ≤ 1 := by
  have hden_pos : 0 < higham9_25_trailingRowInf Astage k i :=
    lt_of_le_of_ne
      (higham9_25_trailingRowInf_nonneg Astage k i) (Ne.symm hrow)
  rw [div_le_iff₀ hden_pos]
  simpa using higham9_25_abs_stage_entry_le_trailingRowInf Astage k i

/-- **Equation (9.25)**: implicit row-scaling pivot rule. -/
def higham9_25_implicitRowScalingPivotRule {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r : Fin n) : Prop :=
  k.val ≤ r.val ∧
  higham9_25_trailingRowInf Astage k r ≠ 0 ∧
  ∀ i : Fin n, k.val ≤ i.val →
    higham9_25_trailingRowInf Astage k i ≠ 0 →
      |Astage i k| / higham9_25_trailingRowInf Astage k i ≤
        |Astage r k| / higham9_25_trailingRowInf Astage k r

/-- **Equation (9.25)**, the selected implicit row-scaling pivot ratio is
nonnegative. -/
theorem higham9_25_implicitRowScalingPivotRule_ratio_nonneg {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r : Fin n)
    (_hrule : higham9_25_implicitRowScalingPivotRule Astage k r) :
    0 ≤ |Astage r k| / higham9_25_trailingRowInf Astage k r :=
  higham9_25_scaled_pivot_ratio_nonneg Astage k r

/-- **Equation (9.25)**, the selected implicit row-scaling pivot ratio is at
most one. -/
theorem higham9_25_implicitRowScalingPivotRule_ratio_le_one {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k r : Fin n)
    (hrule : higham9_25_implicitRowScalingPivotRule Astage k r) :
    |Astage r k| / higham9_25_trailingRowInf Astage k r ≤ 1 :=
  higham9_25_scaled_pivot_ratio_le_one Astage k r hrule.2.1

/-- **Equation (9.25)**, finite active-set existence for implicit row scaling.

If some active row has nonzero trailing row norm, then a row maximizing the
scaled pivot ratio in Higham's implicit row-scaling rule exists.  This is only
the finite pivot-choice layer; it does not construct a rounded elimination
trace from the rule. -/
theorem higham9_25_exists_implicitRowScalingPivotRule {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive :
      ∃ i : Fin n,
        k.val ≤ i.val ∧ higham9_25_trailingRowInf Astage k i ≠ 0) :
    ∃ r : Fin n, higham9_25_implicitRowScalingPivotRule Astage k r := by
  classical
  let activeRows : Finset (Fin n) :=
    Finset.univ.filter
      (fun i : Fin n =>
        k.val ≤ i.val ∧ higham9_25_trailingRowInf Astage k i ≠ 0)
  have hactiveRows : activeRows.Nonempty := by
    rcases hactive with ⟨i, hik, hiNorm⟩
    have hikFin : k ≤ i := hik
    refine ⟨i, ?_⟩
    simp [activeRows, hikFin, hiNorm]
  obtain ⟨r, hr, hmax⟩ :=
    Finset.exists_max_image activeRows
      (fun i : Fin n =>
        |Astage i k| / higham9_25_trailingRowInf Astage k i)
      hactiveRows
  have hr_active :
      k.val ≤ r.val ∧ higham9_25_trailingRowInf Astage k r ≠ 0 := by
    simpa [activeRows] using hr
  refine ⟨r, hr_active.1, hr_active.2, ?_⟩
  intro i hik hiNorm
  have hikFin : k ≤ i := hik
  have hi_mem : i ∈ activeRows := by
    simp [activeRows, hikFin, hiNorm]
  exact hmax i hi_mem

/-- **Equation (9.25)**, a nonzero active pivot-column entry makes the
corresponding trailing row norm nonzero. -/
theorem higham9_25_trailingRowInf_ne_zero_of_stage_entry_ne_zero {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k i : Fin n)
    (hentry : Astage i k ≠ 0) :
    higham9_25_trailingRowInf Astage k i ≠ 0 := by
  have hentry_pos : 0 < |Astage i k| := abs_pos.mpr hentry
  have hrow_pos : 0 < higham9_25_trailingRowInf Astage k i :=
    lt_of_lt_of_le hentry_pos
      (higham9_25_abs_stage_entry_le_trailingRowInf Astage k i)
  exact ne_of_gt hrow_pos

/-- **Equation (9.25)**, source-facing finite pivot-choice existence from a
nonzero active pivot-column entry. -/
theorem higham9_25_exists_implicitRowScalingPivotRule_of_active_column_nonzero
    {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : Fin n)
    (hactive :
      ∃ i : Fin n,
        k.val ≤ i.val ∧ Astage i k ≠ 0) :
    ∃ r : Fin n, higham9_25_implicitRowScalingPivotRule Astage k r := by
  rcases hactive with ⟨i, hik, hentry⟩
  exact higham9_25_exists_implicitRowScalingPivotRule Astage k
    ⟨i, hik,
      higham9_25_trailingRowInf_ne_zero_of_stage_entry_ne_zero
        Astage k i hentry⟩

/-- **Equation (9.26)**, finite real prefix `p`-norm, implemented through the
shared complex `L^p` API. -/
noncomputable def higham9_26_prefixLpNorm {k : ℕ} (p : ℝ)
    (x : Fin k → ℝ) : ℝ :=
  complexVecLpNorm (ENNReal.ofReal p) (fun r : Fin k => (x r : ℂ))

end NumStability
