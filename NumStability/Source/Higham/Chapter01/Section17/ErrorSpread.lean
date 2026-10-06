import NumStability.Source.Higham.Chapter01.Section17.StoredGrid

namespace NumStability

/-!
# Nonrandom rounding error-spread conclusions

Final Figure 1.6 consequences for Kahan's Higham Section 1.17 example. These
results turn the stored-grid certificates into an unconditional selected-pair
error-spread bound and show that the IEEE-double error is not constant across
the source grid.
-/

/-- Selected-pair Figure 1.6 diagnostic bridge specialized to the modeled
IEEE-double Horner path with the source-grid input first stored in IEEE double. -/
theorem ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_of_output_spread
    (η : ℝ)
    (hspread :
      (1 : ℝ) / 10 ^ 15 + η <
        |ieeeDoubleKahanStoredGridRationalFunction 289 -
          ieeeDoubleKahanStoredGridRationalFunction 175|) :
    η <
      |(ieeeDoubleKahanStoredGridRationalFunction 289 -
          kahanRationalFunction (kahanHornerGridPoint 289)) -
        (ieeeDoubleKahanStoredGridRationalFunction 175 -
          kahanRationalFunction (kahanHornerGridPoint 175))| := by
  exact
    kahanRoundedGrid_175_289_error_spread_gt_of_output_spread
      ieeeDoubleKahanStoredGridRationalFunction η hspread

/-- Reusable bridge from two selected stored-grid IEEE-double rounded Horner
values to the Figure 1.6 error spread lower bound.  The unconditional theorem
below supplies the two exact stored input/output certificates. -/
theorem ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13_of_output_values
    (h175 :
      ieeeDoubleKahanStoredGridRationalFunction 175 =
        (4927149988474991 : ℝ) / 562949953421312)
    (h289 :
      ieeeDoubleKahanStoredGridRationalFunction 289 =
        (2463574994237539 : ℝ) / 281474976710656) :
    (1 : ℝ) / 10 ^ 13 <
      |(ieeeDoubleKahanStoredGridRationalFunction 289 -
          kahanRationalFunction (kahanHornerGridPoint 289)) -
        (ieeeDoubleKahanStoredGridRationalFunction 175 -
          kahanRationalFunction (kahanHornerGridPoint 175))| := by
  apply ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_of_output_spread
    (η := (1 : ℝ) / 10 ^ 13)
  rw [h289, h175]
  norm_num

/-- Fully certified selected-pair Figure 1.6 diagnostic for the stored-input
IEEE-double Horner trace.  The two concrete rounded outputs are proved by the
preceding primitive-operation certificates. -/
theorem ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13 :
    (1 : ℝ) / 10 ^ 13 <
      |(ieeeDoubleKahanStoredGridRationalFunction 289 -
          kahanRationalFunction (kahanHornerGridPoint 289)) -
        (ieeeDoubleKahanStoredGridRationalFunction 175 -
          kahanRationalFunction (kahanHornerGridPoint 175))| := by
  exact
    ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13_of_output_values
      ieeeDoubleKahanStoredGridRationalFunction_175_eq
      ieeeDoubleKahanStoredGridRationalFunction_289_eq

/-- Stored-input IEEE-double rounded error at a source-grid point, measured
against the exact rational-function reference at the original source grid
point. -/
noncomputable def ieeeDoubleKahanStoredGridError (k : ℕ) : ℝ :=
  ieeeDoubleKahanStoredGridRationalFunction k -
    kahanRationalFunction (kahanHornerGridPoint k)

/-- Source-grid existential form of the selected-pair Figure 1.6 diagnostic:
two valid grid indices have stored-input IEEE-double rounded errors differing
by more than `10^-13`. -/
theorem exists_ieeeDoubleKahanStoredGridRationalFunction_grid_error_spread_gt_one_e13 :
    ∃ k l : ℕ,
      1 ≤ k ∧ k ≤ 361 ∧ 1 ≤ l ∧ l ≤ 361 ∧
        (1 : ℝ) / 10 ^ 13 <
          |(ieeeDoubleKahanStoredGridRationalFunction l -
              kahanRationalFunction (kahanHornerGridPoint l)) -
            (ieeeDoubleKahanStoredGridRationalFunction k -
              kahanRationalFunction (kahanHornerGridPoint k))| := by
  refine ⟨175, 289, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact ieeeDoubleKahanStoredGridRationalFunction_175_289_error_spread_gt_one_e13

/-- The selected-pair diagnostic in terms of the named stored-grid error
sequence. -/
theorem exists_ieeeDoubleKahanStoredGridError_pair_spread_gt_one_e13 :
    ∃ k l : ℕ,
      1 ≤ k ∧ k ≤ 361 ∧ 1 ≤ l ∧ l ≤ 361 ∧
        (1 : ℝ) / 10 ^ 13 <
          |ieeeDoubleKahanStoredGridError l -
            ieeeDoubleKahanStoredGridError k| := by
  simpa [ieeeDoubleKahanStoredGridError] using
    exists_ieeeDoubleKahanStoredGridRationalFunction_grid_error_spread_gt_one_e13

/-- Nonconstancy corollary for Figure 1.6: the modeled stored-input
IEEE-double rounded-error sequence on the source grid is not constant.  This
uses the certified selected pair, not an enumeration of all 361 points. -/
theorem not_forall_ieeeDoubleKahanStoredGridError_eq_on_source_grid :
    ¬ ∀ k l : ℕ, 1 ≤ k → k ≤ 361 → 1 ≤ l → l ≤ 361 →
      ieeeDoubleKahanStoredGridError k = ieeeDoubleKahanStoredGridError l := by
  intro hconst
  rcases exists_ieeeDoubleKahanStoredGridError_pair_spread_gt_one_e13 with
    ⟨k, l, hk1, hk361, hl1, hl361, hspread⟩
  have heq : ieeeDoubleKahanStoredGridError l =
      ieeeDoubleKahanStoredGridError k := by
    simpa [eq_comm] using hconst k l hk1 hk361 hl1 hl361
  have hzero :
      |ieeeDoubleKahanStoredGridError l -
        ieeeDoubleKahanStoredGridError k| = 0 := by
    rw [heq, sub_self, abs_zero]
  have hpos : (0 : ℝ) < (1 : ℝ) / 10 ^ 13 := by norm_num
  nlinarith

end NumStability
