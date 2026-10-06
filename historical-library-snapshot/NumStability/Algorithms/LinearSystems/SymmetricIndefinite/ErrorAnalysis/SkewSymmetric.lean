import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms LinearSystems SymmetricIndefinite ErrorAnalysis SkewSymmetric

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyIndefinite` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Algorithm 11.9 source decision predicate for Bunch's skew-symmetric pivoting
strategy at the first stage. -/
def SkewBunchPivotChoice (firstColumnTailZero : Prop)
    (pivotMagnitude : ℝ) (s : PivotSize) : Prop :=
  (firstColumnTailZero ∧ s = PivotSize.one) ∨
  (¬ firstColumnTailZero ∧ 0 < pivotMagnitude ∧ s = PivotSize.two)

/-- **Skew 2×2 multiplier bound** (Higham §11.3).  For Bunch's skew-symmetric
    pivoting, the row of `CE⁻¹` has entries `−a_{i2}/a₂₁, a_{i1}/a₂₁`; since the
    pivot `a₂₁` is the largest-magnitude entry (`|c| ≤ |a₂₁|`), each multiplier —
    and hence every entry of `L` — is bounded by 1.  Derived, not assumed. -/
theorem skew_twoByTwo_multiplier_bound (c a : ℝ) (ha : a ≠ 0) (hc : |c| ≤ |a|) :
    |c / a| ≤ 1 := by
  rw [abs_div, div_le_one (abs_pos.mpr ha)]
  exact hc

/-- **Skew 2×2 Schur-complement entry bound** (Higham §11.3).  The Schur entry
    `s = a_ij − (a_{i2}/a₂₁)·a_{j1} + (a_{i1}/a₂₁)·a_{j2}` for a 2×2 skew pivot,
    with every active entry bounded by `M` and multipliers bounded by 1
    (`|a_{i1}|, |a_{i2}| ≤ |a₂₁|`), satisfies the printed bound `|s| ≤ 3·M`. -/
theorem skew_twoByTwo_schur_entry_bound
    (aij ai1 ai2 aj1 aj2 a21 M : ℝ)
    (ha : a21 ≠ 0)
    (hij : |aij| ≤ M) (hj1 : |aj1| ≤ M) (hj2 : |aj2| ≤ M)
    (hi1 : |ai1| ≤ |a21|) (hi2 : |ai2| ≤ |a21|) :
    |aij - (ai2 / a21) * aj1 + (ai1 / a21) * aj2| ≤ 3 * M := by
  have hm1 : |ai2 / a21| ≤ 1 := skew_twoByTwo_multiplier_bound ai2 a21 ha hi2
  have hm2 : |ai1 / a21| ≤ 1 := skew_twoByTwo_multiplier_bound ai1 a21 ha hi1
  have t1 : |ai2 / a21 * aj1| ≤ M := by
    rw [abs_mul]
    calc |ai2 / a21| * |aj1| ≤ 1 * M := mul_le_mul hm1 hj1 (abs_nonneg _) (by norm_num)
      _ = M := by ring
  have t2 : |ai1 / a21 * aj2| ≤ M := by
    rw [abs_mul]
    calc |ai1 / a21| * |aj2| ≤ 1 * M := mul_le_mul hm2 hj2 (abs_nonneg _) (by norm_num)
      _ = M := by ring
  have htriA : |aij - ai2 / a21 * aj1| ≤ |aij| + |ai2 / a21 * aj1| := by
    have h := abs_add_le aij (-(ai2 / a21 * aj1))
    rwa [← sub_eq_add_neg, abs_neg] at h
  calc |aij - ai2 / a21 * aj1 + ai1 / a21 * aj2|
      ≤ |aij - ai2 / a21 * aj1| + |ai1 / a21 * aj2| := abs_add_le _ _
    _ ≤ (|aij| + |ai2 / a21 * aj1|) + |ai1 / a21 * aj2| := add_le_add htriA (le_refl _)
    _ ≤ (M + M) + M := add_le_add (add_le_add hij t1) t2
    _ = 3 * M := by ring

end NumStability
