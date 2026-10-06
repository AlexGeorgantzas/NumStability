/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Algorithm 11.9: printed two-column pivot discrepancy

Higham, 2nd ed., Chapter 11, pp. 225--226, claims that Algorithm 11.9's
search of the first two active columns makes both entries of every row of
`C E^{-1}` at most one in modulus.  The finite example below shows that this
does not follow: after the selected row/column is moved into position two,
that new column was not searched and can contain an arbitrarily larger
entry.

The final theorem records a source-honest correction: a global maximum
skew pivot (complete pivoting) does give both multiplier bounds.
-/

import NumStability.Algorithms.Cholesky.Higham11SkewActualSelector

namespace NumStability

/-- A nonsingular skew-symmetric matrix whose first two columns have maximum
modulus `2`, while the column moved into the second pivot position contains
an entry of modulus `100`. -/
def higham11_9_twoColumnCounterexample : Fin 4 → Fin 4 → ℝ :=
  !![(0 : ℝ), 0, -2, 0;
     0, 0, 0, -1;
     2, 0, 0, 100;
     0, 1, -100, 0]

/-- An explicit inverse, used only to certify that the discrepancy is not a
singular-input artefact. -/
noncomputable def higham11_9_twoColumnCounterexampleInv : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 50, 1 / 2, 0;
     -50, 0, 0, 1;
     -1 / 2, 0, 0, 0;
     0, -1, 0, 0]

theorem higham11_9_twoColumnCounterexample_skew :
    higham11_16_IsSkewSymmetric 4 higham11_9_twoColumnCounterexample := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [higham11_9_twoColumnCounterexample]

theorem higham11_9_twoColumnCounterexample_mul_inv :
    (Matrix.of higham11_9_twoColumnCounterexample) *
        higham11_9_twoColumnCounterexampleInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, higham11_9_twoColumnCounterexample,
      higham11_9_twoColumnCounterexampleInv, Fin.sum_univ_four] <;>
    norm_num

theorem higham11_9_twoColumnCounterexample_nonsingular :
    IsUnit (Matrix.of higham11_9_twoColumnCounterexample) := by
  exact isUnit_iff_exists_inv.mpr
    ⟨higham11_9_twoColumnCounterexampleInv,
      higham11_9_twoColumnCounterexample_mul_inv⟩

private theorem higham11_9_twoColumnCounterexample_score_le_two
    (q p : Fin 4) :
    higham11_9_skewPairScore higham11_9_twoColumnCounterexample (q, p) ≤ 2 := by
  fin_cases q <;> fin_cases p <;>
    norm_num [higham11_9_skewPairScore,
      higham11_9_twoColumnCounterexample]

private theorem higham11_9_twoColumnCounterexample_score_eq_two
    (q p : Fin 4)
    (h : higham11_9_skewPairScore higham11_9_twoColumnCounterexample
      (q, p) = 2) :
    q = (0 : Fin 4) ∧ p = (2 : Fin 4) := by
  revert h
  fin_cases q <;> fin_cases p <;>
    simp [higham11_9_skewPairScore,
      higham11_9_twoColumnCounterexample]

theorem higham11_9_twoColumnCounterexample_pivotMagnitude :
    higham11_9_skewPivotMagnitude (by omega : 2 ≤ 4)
      higham11_9_twoColumnCounterexample = 2 := by
  have hlower := higham11_9_skewPairArgmax_spec (by omega : 2 ≤ 4)
    higham11_9_twoColumnCounterexample (0 : Fin 4) (2 : Fin 4)
  have hupper := higham11_9_twoColumnCounterexample_score_le_two
    (higham11_9_skewPivotQ (by omega : 2 ≤ 4)
      higham11_9_twoColumnCounterexample)
    (higham11_9_skewPivotP (by omega : 2 ≤ 4)
      higham11_9_twoColumnCounterexample)
  have hcandidate :
      higham11_9_skewPairScore higham11_9_twoColumnCounterexample
        ((0 : Fin 4), (2 : Fin 4)) = 2 := by
    simp [higham11_9_skewPairScore,
      higham11_9_twoColumnCounterexample]
  rw [hcandidate] at hlower
  exact le_antisymm hupper hlower

theorem higham11_9_twoColumnCounterexample_argmax :
    higham11_9_skewPairArgmax (by omega : 2 ≤ 4)
      higham11_9_twoColumnCounterexample = ((0 : Fin 4), (2 : Fin 4)) := by
  let qp := higham11_9_skewPairArgmax (by omega : 2 ≤ 4)
    higham11_9_twoColumnCounterexample
  have hscore :
      higham11_9_skewPairScore higham11_9_twoColumnCounterexample qp = 2 := by
    simpa [qp, higham11_9_skewPivotMagnitude] using
      higham11_9_twoColumnCounterexample_pivotMagnitude
  have hpair := higham11_9_twoColumnCounterexample_score_eq_two
    qp.1 qp.2 hscore
  exact Prod.ext hpair.1 hpair.2

/-- **Source discrepancy, Algorithm 11.9.**  The actual finite implementation
of the printed two-column argmax selects the unique entry of modulus `2`.
After the printed symmetric interchanges, a row of `C E^{-1}` nevertheless
contains a multiplier of modulus `50`, contradicting the next page's claimed
unit bound. -/
theorem higham11_9_printed_twoColumn_search_does_not_bound_multipliers :
    higham11_16_IsSkewSymmetric 4 higham11_9_twoColumnCounterexample ∧
      IsUnit (Matrix.of higham11_9_twoColumnCounterexample) ∧
      1 <
        |higham11_9_skewActualPermutedMatrix (by omega : 2 ≤ 4)
              higham11_9_twoColumnCounterexample (3 : Fin 4) (1 : Fin 4) /
          higham11_9_skewActualPermutedMatrix (by omega : 2 ≤ 4)
              higham11_9_twoColumnCounterexample (1 : Fin 4) (0 : Fin 4)| := by
  refine ⟨higham11_9_twoColumnCounterexample_skew,
    higham11_9_twoColumnCounterexample_nonsingular, ?_⟩
  have hq : higham11_9_skewPivotQ (by omega : 2 ≤ 4)
      higham11_9_twoColumnCounterexample = (0 : Fin 4) := by
    simpa [higham11_9_skewPivotQ] using congrArg Prod.fst
      higham11_9_twoColumnCounterexample_argmax
  have hp : higham11_9_skewPivotP (by omega : 2 ≤ 4)
      higham11_9_twoColumnCounterexample = (2 : Fin 4) := by
    simpa [higham11_9_skewPivotP] using congrArg Prod.snd
      higham11_9_twoColumnCounterexample_argmax
  have hperm : higham11_9_skewActualPerm (by omega : 2 ≤ 4)
      higham11_9_twoColumnCounterexample =
        Equiv.swap (1 : Fin 4) (2 : Fin 4) := by
    ext i
    simp [higham11_9_skewActualPerm, hq, hp]
  have hperm0 : higham11_9_skewActualPerm (by omega : 2 ≤ 4)
      higham11_9_twoColumnCounterexample (0 : Fin 4) = 0 := by
    rw [hperm]
    simp [Equiv.swap_apply_def]
  have hperm1 : higham11_9_skewActualPerm (by omega : 2 ≤ 4)
      higham11_9_twoColumnCounterexample (1 : Fin 4) = 2 := by
    rw [hperm]
    simp
  have hperm3 : higham11_9_skewActualPerm (by omega : 2 ≤ 4)
      higham11_9_twoColumnCounterexample (3 : Fin 4) = 3 := by
    rw [hperm]
    simp [Equiv.swap_apply_def]
  have hnum :
      higham11_9_skewActualPermutedMatrix (by omega : 2 ≤ 4)
        higham11_9_twoColumnCounterexample (3 : Fin 4) (1 : Fin 4) = -100 := by
    simp only [higham11_9_skewActualPermutedMatrix, hperm3, hperm1]
    rfl
  have hden :
      higham11_9_skewActualPermutedMatrix (by omega : 2 ≤ 4)
        higham11_9_twoColumnCounterexample (1 : Fin 4) (0 : Fin 4) = 2 := by
    simp only [higham11_9_skewActualPermutedMatrix, hperm1, hperm0]
    rfl
  rw [hnum, hden]
  norm_num

/-- Corrected local statement: selecting a nonzero *global* maximum entry of
the active skew matrix bounds both entries of every exact multiplier row.
This is the complete-pivoting repair of the false inference following
Algorithm 11.9. -/
theorem higham11_9_globalMaxPivot_bounds_both_multipliers {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p q : Fin n)
    (hpivot : A p q ≠ 0)
    (hmax : ∀ i j, |A i j| ≤ |A p q|) :
    ∀ i,
      |A i p / A p q| ≤ 1 ∧ |A i q / A p q| ≤ 1 := by
  intro i
  exact ⟨
    skew_twoByTwo_multiplier_bound (A i p) (A p q) hpivot (hmax i p),
    skew_twoByTwo_multiplier_bound (A i q) (A p q) hpivot (hmax i q)⟩

/-- A sharper repair that preserves the printed local `3 M` Schur-growth
bound without the false assertion that both multipliers are bounded.  It is
enough that the two entries from the searched pivot column are bounded by
the pivot; the possibly large entries from the newly moved column remain
paired with those small entries. -/
theorem higham11_9_coupled_skew_schur_entry_bound
    (aij ai1 ai2 aj1 aj2 a21 M : ℝ)
    (ha : a21 ≠ 0)
    (hij : |aij| ≤ M)
    (hi1 : |ai1| ≤ |a21|) (hj1 : |aj1| ≤ |a21|)
    (hi2 : |ai2| ≤ M) (hj2 : |aj2| ≤ M) :
    |aij - (ai2 / a21) * aj1 + (ai1 / a21) * aj2| ≤ 3 * M := by
  have hratioJ : |aj1 / a21| ≤ 1 :=
    skew_twoByTwo_multiplier_bound aj1 a21 ha hj1
  have hratioI : |ai1 / a21| ≤ 1 :=
    skew_twoByTwo_multiplier_bound ai1 a21 ha hi1
  have hM : 0 ≤ M := (abs_nonneg ai2).trans hi2
  have hterm1 : |(ai2 / a21) * aj1| ≤ M := by
    have hrearrange : (ai2 / a21) * aj1 = ai2 * (aj1 / a21) := by
      field_simp
    rw [hrearrange, abs_mul]
    calc
      |ai2| * |aj1 / a21| ≤ M * 1 :=
        mul_le_mul hi2 hratioJ (abs_nonneg _) hM
      _ = M := mul_one _
  have hterm2 : |(ai1 / a21) * aj2| ≤ M := by
    rw [abs_mul]
    calc
      |ai1 / a21| * |aj2| ≤ 1 * M :=
        mul_le_mul hratioI hj2 (abs_nonneg _) (by positivity)
      _ = M := one_mul _
  calc
    |aij - (ai2 / a21) * aj1 + (ai1 / a21) * aj2|
        ≤ |aij| + |(ai2 / a21) * aj1| + |(ai1 / a21) * aj2| := by
          calc
            |aij - (ai2 / a21) * aj1 + (ai1 / a21) * aj2|
                ≤ |aij - (ai2 / a21) * aj1| +
                    |(ai1 / a21) * aj2| := abs_add_le _ _
            _ ≤ (|aij| + |(ai2 / a21) * aj1|) +
                    |(ai1 / a21) * aj2| :=
              add_le_add (by simpa [sub_eq_add_neg] using
                (abs_add_le aij (-((ai2 / a21) * aj1)))) (le_refl _)
    _ ≤ M + M + M := add_le_add (add_le_add hij hterm1) hterm2
    _ = 3 * M := by ring

end NumStability
