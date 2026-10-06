import NumStability.Algorithms.Cholesky.Higham11SkewSourceCorrection

/-!
# Higham Algorithm 11.9: exact recursive skew-Schur trace

This file follows the execution printed on pp. 225--226.  A zero first-column
tail produces a `1 x 1` zero pivot and no arithmetic; otherwise the concrete
two-column selector from `Higham11SkewActualSelector` supplies `(q,p)`, the
associated symmetric permutation moves those indices to zero and one, and the
trace recurses on the exact skew Schur complement.

The sentence after Algorithm 11.9 claiming that both entries of every
multiplier row have modulus at most one is false for the printed two-column
search.  The recursive growth proof below therefore never uses
`higham11_9_skew_L_entry_bound_interface` or the two-multiplier hypothesis of
`higham11_9_skew_schur_entry_bound`.  It uses only the valid coupled local
theorem `higham11_9_coupled_skew_schur_entry_bound`.
-/

namespace NumStability

abbrev Higham11SkewMatrix (n : ℕ) := Fin n → Fin n → ℝ

/-- The unchanged trailing principal block at a printed one-column no-action
stage. -/
def higham11_9_skewNoActionTail {n : ℕ}
    (A : Higham11SkewMatrix (n + 1)) : Higham11SkewMatrix n :=
  fun i j => A i.succ j.succ

theorem higham11_9_skewNoActionTail_isSkew {n : ℕ}
    (A : Higham11SkewMatrix (n + 1))
    (hA : higham11_16_IsSkewSymmetric (n + 1) A) :
    higham11_16_IsSkewSymmetric n (higham11_9_skewNoActionTail A) := by
  intro i j
  exact hA i.succ j.succ

/-- The exact trailing Schur complement after the actual selected pair has
been moved to leading indices zero and one.  This is the scalar form printed
on p. 226:
`aij - (ai2/a21) * aj1 + (ai1/a21) * aj2`. -/
noncomputable def higham11_9_skewActualSchurTwo {n : ℕ}
    (A : Higham11SkewMatrix (n + 2)) : Higham11SkewMatrix n :=
  let B := higham11_9_skewActualPermutedMatrix (by omega : 2 ≤ n + 2) A
  fun i j =>
    B i.succ.succ j.succ.succ -
        (B i.succ.succ (Fin.succ 0) / B (Fin.succ 0) 0) * B j.succ.succ 0 +
      (B i.succ.succ 0 / B (Fin.succ 0) 0) * B j.succ.succ (Fin.succ 0)

/-- A positive selector value makes the actual permutation send new index
zero to `q`. -/
theorem higham11_9_skewActualPerm_zero_of_pos {n : ℕ} (hn2 : 2 ≤ n)
    (A : Higham11SkewMatrix n)
    (hpos : 0 < higham11_9_skewPivotMagnitude hn2 A) :
    higham11_9_skewActualPerm hn2 A
        (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) =
      higham11_9_skewPivotQ hn2 A := by
  have hidx := higham11_9_skewPairArgmax_indices_of_pos hn2 A hpos
  have hq : higham11_9_skewPivotQ hn2 A =
      (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) ∨
      higham11_9_skewPivotQ hn2 A =
        (⟨1, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) := by
    have hv : (higham11_9_skewPivotQ hn2 A).val = 0 ∨
        (higham11_9_skewPivotQ hn2 A).val = 1 := by omega
    rcases hv with hv | hv
    · exact Or.inl (Fin.ext hv)
    · exact Or.inr (Fin.ext hv)
  rcases hq with hq | hq
  · have hp0 : higham11_9_skewPivotP hn2 A ≠
        (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) := by
      intro hp
      have := hidx.2
      rw [hq, hp] at this
      simp at this
    simp only [higham11_9_skewActualPerm, hq, Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hp0)]
    simp
  · have hp0 : higham11_9_skewPivotP hn2 A ≠
        (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) := by
      intro hp
      have := hidx.2
      rw [hq, hp] at this
      simp at this
    have hp1 : higham11_9_skewPivotP hn2 A ≠
        (⟨1, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) := by
      intro hp
      have := hidx.2
      rw [hq, hp] at this
      simp at this
    simp only [higham11_9_skewActualPerm, hq, Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) (Ne.symm hp0)]
    simp

/-- A positive selector value makes the actual permutation send new index one
to `p`. -/
theorem higham11_9_skewActualPerm_one_of_pos {n : ℕ} (hn2 : 2 ≤ n)
    (A : Higham11SkewMatrix n)
    (hpos : 0 < higham11_9_skewPivotMagnitude hn2 A) :
    higham11_9_skewActualPerm hn2 A
        (⟨1, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) =
      higham11_9_skewPivotP hn2 A := by
  have hidx := higham11_9_skewPairArgmax_indices_of_pos hn2 A hpos
  have hq : higham11_9_skewPivotQ hn2 A =
      (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) ∨
      higham11_9_skewPivotQ hn2 A =
        (⟨1, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) := by
    have hv : (higham11_9_skewPivotQ hn2 A).val = 0 ∨
        (higham11_9_skewPivotQ hn2 A).val = 1 := by omega
    rcases hv with hv | hv
    · exact Or.inl (Fin.ext hv)
    · exact Or.inr (Fin.ext hv)
  rcases hq with hq | hq
  · simp [higham11_9_skewActualPerm, hq]
  · have hp0 : higham11_9_skewPivotP hn2 A ≠
        (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) := by
      intro hp
      have := hidx.2
      rw [hq, hp] at this
      simp at this
    have hp1 : higham11_9_skewPivotP hn2 A ≠
        (⟨1, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) := by
      intro hp
      have := hidx.2
      rw [hq, hp] at this
      simp at this
    simp only [higham11_9_skewActualPerm, hq, Equiv.trans_apply]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hp0 hp1]

/-- The leading entry of the permuted block is literally the selected pivot. -/
theorem higham11_9_skewActualPermuted_pivot_eq_selected {n : ℕ}
    (hn2 : 2 ≤ n) (A : Higham11SkewMatrix n)
    (hpos : 0 < higham11_9_skewPivotMagnitude hn2 A) :
    higham11_9_skewActualPermutedMatrix hn2 A
        (⟨1, lt_of_lt_of_le (by omega) hn2⟩ : Fin n)
        (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) =
      A (higham11_9_skewPivotP hn2 A) (higham11_9_skewPivotQ hn2 A) := by
  simp only [higham11_9_skewActualPermutedMatrix]
  rw [higham11_9_skewActualPerm_one_of_pos hn2 A hpos,
    higham11_9_skewActualPerm_zero_of_pos hn2 A hpos]

/-- The actual two-by-two branch has a nonzero leading skew pivot. -/
theorem higham11_9_skewActualPermuted_pivot_ne_zero {n : ℕ}
    (hn2 : 2 ≤ n) (A : Higham11SkewMatrix n)
    (hzero : ¬ higham11_9_firstColumnTailZero hn2 A) :
    higham11_9_skewActualPermutedMatrix hn2 A
        (⟨1, lt_of_lt_of_le (by omega) hn2⟩ : Fin n)
        (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) ≠ 0 := by
  have hpos :=
    higham11_9_skewPivotMagnitude_pos_of_firstColumnTail_ne_zero hn2 A hzero
  rw [higham11_9_skewActualPermuted_pivot_eq_selected hn2 A hpos]
  have habs := higham11_9_skewPivotMagnitude_eq_abs_entry_of_pos hn2 A hpos
  intro hz
  rw [hz, abs_zero] at habs
  linarith

/-- Although the printed search does not bound both multiplier entries, it
does bound every entry in the *selected* pivot column.  The `q = 1`, row-zero
case follows from skew-symmetry and the searched first column. -/
theorem higham11_9_skewPivot_dominates_selected_column {n : ℕ}
    (hn2 : 2 ≤ n) (A : Higham11SkewMatrix n)
    (hA : higham11_16_IsSkewSymmetric n A)
    (hpos : 0 < higham11_9_skewPivotMagnitude hn2 A)
    (r : Fin n) (hr : r ≠ higham11_9_skewPivotQ hn2 A) :
    |A r (higham11_9_skewPivotQ hn2 A)| ≤
      higham11_9_skewPivotMagnitude hn2 A := by
  have hidx := higham11_9_skewPairArgmax_indices_of_pos hn2 A hpos
  have hq : higham11_9_skewPivotQ hn2 A =
      (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) ∨
      higham11_9_skewPivotQ hn2 A =
        (⟨1, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) := by
    have hv : (higham11_9_skewPivotQ hn2 A).val = 0 ∨
        (higham11_9_skewPivotQ hn2 A).val = 1 := by omega
    rcases hv with hv | hv
    · exact Or.inl (Fin.ext hv)
    · exact Or.inr (Fin.ext hv)
  rcases hq with hq | hq
  · have hrpos : 0 < r.val := by
      have hrne : r.val ≠ 0 := by
        intro hv
        apply hr
        rw [hq]
        exact Fin.ext hv
      omega
    simpa [hq] using higham11_9_skewPivot_dominates_column_zero hn2 A r hrpos
  · by_cases hr0 : r.val = 0
    · have hre : r = (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) := Fin.ext hr0
      rw [hre]
      calc
        |A (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n)
            (higham11_9_skewPivotQ hn2 A)| =
            |A (higham11_9_skewPivotQ hn2 A)
              (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n)| := by
                rw [hA]
                simp
        _ ≤ higham11_9_skewPivotMagnitude hn2 A := by
          apply higham11_9_skewPivot_dominates_column_zero hn2 A
          rw [hq]
          simp
    · have hr1 : r.val ≠ 1 := by
        intro hv
        apply hr
        rw [hq]
        exact Fin.ext hv
      have hrgt : 1 < r.val := by omega
      simpa [hq] using higham11_9_skewPivot_dominates_column_one hn2 A r hrgt

/-- Every trailing entry in the first pivot column of the actual permuted
matrix is bounded by the nonzero leading pivot.  This is the searched-column
half of the corrected coupled invariant. -/
theorem higham11_9_skewActualPermuted_trailing_column_zero_le_pivot {n : ℕ}
    (A : Higham11SkewMatrix (n + 2))
    (hA : higham11_16_IsSkewSymmetric (n + 2) A)
    (hzero : ¬ higham11_9_firstColumnTailZero (by omega : 2 ≤ n + 2) A)
    (i : Fin n) :
    |higham11_9_skewActualPermutedMatrix (by omega : 2 ≤ n + 2) A
        i.succ.succ 0| ≤
      |higham11_9_skewActualPermutedMatrix (by omega : 2 ≤ n + 2) A
        (Fin.succ 0) 0| := by
  let hn2 : 2 ≤ n + 2 := by omega
  let σ := higham11_9_skewActualPerm hn2 A
  have hpos :=
    higham11_9_skewPivotMagnitude_pos_of_firstColumnTail_ne_zero hn2 A hzero
  have hσ0 : σ (0 : Fin (n + 2)) = higham11_9_skewPivotQ hn2 A :=
    higham11_9_skewActualPerm_zero_of_pos hn2 A hpos
  have hσ1 : σ (Fin.succ 0) = higham11_9_skewPivotP hn2 A :=
    higham11_9_skewActualPerm_one_of_pos hn2 A hpos
  have hne : σ i.succ.succ ≠ higham11_9_skewPivotQ hn2 A := by
    rw [← hσ0]
    intro heq
    have hi0 := σ.injective heq
    have hval := congrArg Fin.val hi0
    simp at hval
  have hselected :=
    higham11_9_skewPivot_dominates_selected_column hn2 A hA hpos
      (σ i.succ.succ) hne
  have hpivot := higham11_9_skewPivotMagnitude_eq_abs_entry_of_pos hn2 A hpos
  change |A (σ i.succ.succ) (σ 0)| ≤
    |A (σ (Fin.succ 0)) (σ 0)|
  rw [hσ0, hσ1, ← hpivot]
  exact hselected

/-- The literal selected Schur complement preserves skew-symmetry. -/
theorem higham11_9_skewActualSchurTwo_isSkew {n : ℕ}
    (A : Higham11SkewMatrix (n + 2))
    (hA : higham11_16_IsSkewSymmetric (n + 2) A) :
    higham11_16_IsSkewSymmetric n (higham11_9_skewActualSchurTwo A) := by
  let B := higham11_9_skewActualPermutedMatrix (by omega : 2 ≤ n + 2) A
  have hB : higham11_16_IsSkewSymmetric (n + 2) B :=
    higham11_9_skewActualPermutedMatrix_isSkew (by omega) A hA
  intro i j
  simp only [higham11_9_skewActualSchurTwo]
  change B i.succ.succ j.succ.succ -
        (B i.succ.succ (Fin.succ 0) / B (Fin.succ 0) 0) * B j.succ.succ 0 +
      (B i.succ.succ 0 / B (Fin.succ 0) 0) * B j.succ.succ (Fin.succ 0) =
    -(B j.succ.succ i.succ.succ -
        (B j.succ.succ (Fin.succ 0) / B (Fin.succ 0) 0) * B i.succ.succ 0 +
      (B j.succ.succ 0 / B (Fin.succ 0) 0) * B i.succ.succ (Fin.succ 0))
  rw [hB i.succ.succ j.succ.succ,
    hB i.succ.succ 0, hB i.succ.succ (Fin.succ 0),
    hB j.succ.succ 0, hB j.succ.succ (Fin.succ 0)]
  ring

/-- Correct local `3 M` bound for the literal selected Schur update.  The
proof uses the coupled invariant from `Higham11SkewSourceCorrection`; it does
not assert that the newly moved second pivot column is pivot-bounded. -/
theorem higham11_9_skewActualSchurTwo_entry_bound {n : ℕ}
    (A : Higham11SkewMatrix (n + 2))
    (hA : higham11_16_IsSkewSymmetric (n + 2) A)
    (hzero : ¬ higham11_9_firstColumnTailZero (by omega : 2 ≤ n + 2) A)
    (i j : Fin n) :
    |higham11_9_skewActualSchurTwo A i j| ≤
      3 * maxEntryNorm (by omega : 0 < n + 2) A := by
  let hn2 : 2 ≤ n + 2 := by omega
  let B := higham11_9_skewActualPermutedMatrix hn2 A
  have hpivot : B (Fin.succ 0) 0 ≠ 0 :=
    higham11_9_skewActualPermuted_pivot_ne_zero hn2 A hzero
  have hentry : ∀ r c : Fin (n + 2),
      |B r c| ≤ maxEntryNorm (by omega : 0 < n + 2) A := by
    intro r c
    exact entry_le_maxEntryNorm (by omega) A _ _
  have hi1 : |B i.succ.succ 0| ≤ |B (Fin.succ 0) 0| :=
    higham11_9_skewActualPermuted_trailing_column_zero_le_pivot A hA hzero i
  have hj1 : |B j.succ.succ 0| ≤ |B (Fin.succ 0) 0| :=
    higham11_9_skewActualPermuted_trailing_column_zero_le_pivot A hA hzero j
  change
    |B i.succ.succ j.succ.succ -
        (B i.succ.succ (Fin.succ 0) / B (Fin.succ 0) 0) * B j.succ.succ 0 +
      (B i.succ.succ 0 / B (Fin.succ 0) 0) * B j.succ.succ (Fin.succ 0)| ≤
      3 * maxEntryNorm (by omega : 0 < n + 2) A
  exact higham11_9_coupled_skew_schur_entry_bound
    (B i.succ.succ j.succ.succ) (B i.succ.succ 0)
    (B i.succ.succ (Fin.succ 0)) (B j.succ.succ 0)
    (B j.succ.succ (Fin.succ 0)) (B (Fin.succ 0) 0)
    (maxEntryNorm (by omega : 0 < n + 2) A) hpivot
    (hentry _ _) hi1 hj1 (hentry _ _) (hentry _ _)

/-- Max-entry form of the valid local `3 M` recurrence. -/
theorem higham11_9_skewActualSchurTwo_maxEntryNorm_le {n : ℕ}
    (hn : 0 < n) (A : Higham11SkewMatrix (n + 2))
    (hA : higham11_16_IsSkewSymmetric (n + 2) A)
    (hzero : ¬ higham11_9_firstColumnTailZero (by omega : 2 ≤ n + 2) A) :
    maxEntryNorm hn (higham11_9_skewActualSchurTwo A) ≤
      3 * maxEntryNorm (by omega : 0 < n + 2) A :=
  maxEntryNorm_le_of_entry_le_bound hn (higham11_9_skewActualSchurTwo A)
    (3 * maxEntryNorm (by omega : 0 < n + 2) A)
    (higham11_9_skewActualSchurTwo_entry_bound A hA hzero)

/-- A one-column no-action stage cannot increase the max-entry norm. -/
theorem higham11_9_skewNoActionTail_maxEntryNorm_le {n : ℕ}
    (hn : 0 < n) (A : Higham11SkewMatrix (n + 1)) :
    maxEntryNorm hn (higham11_9_skewNoActionTail A) ≤
      maxEntryNorm (by omega : 0 < n + 1) A := by
  apply maxEntryNorm_le_of_entry_le_bound
  intro i j
  exact entry_le_maxEntryNorm (by omega) A i.succ j.succ

/-! ## Literal recursive execution -/

/-- A structurally terminating, exact execution of Algorithm 11.9.  Every
branch is determined by the current active matrix.  In the `two` constructor
the tail is the Schur complement formed with the actual selector and actual
symmetric permutation, not an externally supplied schedule. -/
inductive Higham11ExactSkewTrace :
    {n : ℕ} → (A : Higham11SkewMatrix n) → Type
  | nil (A : Higham11SkewMatrix 0) : Higham11ExactSkewTrace A
  | singleton (A : Higham11SkewMatrix 1)
      (hA : higham11_16_IsSkewSymmetric 1 A) :
      Higham11ExactSkewTrace A
  | noAction {n : ℕ} (A : Higham11SkewMatrix (n + 2))
      (hA : higham11_16_IsSkewSymmetric (n + 2) A)
      (hzero : higham11_9_firstColumnTailZero (by omega : 2 ≤ n + 2) A)
      (tail : Higham11ExactSkewTrace (higham11_9_skewNoActionTail A)) :
      Higham11ExactSkewTrace A
  | two {n : ℕ} (A : Higham11SkewMatrix (n + 2))
      (hA : higham11_16_IsSkewSymmetric (n + 2) A)
      (hzero : ¬ higham11_9_firstColumnTailZero (by omega : 2 ≤ n + 2) A)
      (tail : Higham11ExactSkewTrace (higham11_9_skewActualSchurTwo A)) :
      Higham11ExactSkewTrace A

namespace Higham11ExactSkewTrace

/-- Block widths in the exact elimination order. -/
noncomputable def widths : {n : ℕ} → {A : Higham11SkewMatrix n} →
    Higham11ExactSkewTrace A → List ℕ
  | _, _, .nil _ => []
  | _, _, .singleton _ _ => [1]
  | _, _, .noAction _ _ _ tail => 1 :: tail.widths
  | _, _, .two _ _ _ tail => 2 :: tail.widths

/-- Structural termination/accounting: the recursive block widths consume
exactly the original dimension. -/
@[simp] theorem widths_sum : {n : ℕ} → {A : Higham11SkewMatrix n} →
    (trace : Higham11ExactSkewTrace A) → trace.widths.sum = n
  | _, _, .nil _ => by simp [widths]
  | _, _, .singleton _ _ => by simp [widths]
  | _, _, .noAction _ _ _ tail => by
      simp [widths, widths_sum tail]
      omega
  | _, _, .two _ _ _ tail => by
      simp [widths, widths_sum tail]
      omega

/-- Number of all selected two-by-two pivots, including a final pivot that
has no nontrivial trailing Schur block. -/
noncomputable def twoPivots : {n : ℕ} → {A : Higham11SkewMatrix n} →
    Higham11ExactSkewTrace A → ℕ
  | _, _, .nil _ => 0
  | _, _, .singleton _ _ => 0
  | _, _, .noAction _ _ _ tail => tail.twoPivots
  | _, _, .two _ _ _ tail => tail.twoPivots + 1

/-- Every two-by-two pivot consumes two indices. -/
theorem two_mul_twoPivots_le_dimension : {n : ℕ} →
    {A : Higham11SkewMatrix n} → (trace : Higham11ExactSkewTrace A) →
    2 * trace.twoPivots ≤ n
  | _, _, .nil _ => by simp [twoPivots]
  | _, _, .singleton _ _ => by simp [twoPivots]
  | _, _, .noAction _ _ _ tail => by
      have ih := two_mul_twoPivots_le_dimension tail
      simp only [twoPivots]
      omega
  | _, _, .two _ _ _ tail => by
      have ih := two_mul_twoPivots_le_dimension tail
      simp only [twoPivots]
      omega

/-- Number of two-by-two stages capable of increasing a later nontrivial
skew block.  A two-by-two stage whose tail has dimension zero or one is not
counted: the zero-dimensional tail is empty and a skew `1 x 1` tail is zero. -/
noncomputable def growthUpdates : {n : ℕ} → {A : Higham11SkewMatrix n} →
    Higham11ExactSkewTrace A → ℕ
  | _, _, .nil _ => 0
  | _, _, .singleton _ _ => 0
  | _, _, .noAction _ _ _ tail => tail.growthUpdates
  | _, _, .two (n := n) _ _ _ tail =>
      if 2 ≤ n then tail.growthUpdates + 1 else tail.growthUpdates

/-- Max-entry magnitudes of every nonempty active matrix in execution order. -/
noncomputable def stageMaxes : {n : ℕ} → {A : Higham11SkewMatrix n} →
    Higham11ExactSkewTrace A → List ℝ
  | _, _, .nil _ => []
  | _, _, .singleton A _ => [maxEntryNorm (by omega) A]
  | _, _, .noAction A _ _ tail =>
      maxEntryNorm (by omega) A :: tail.stageMaxes
  | _, _, .two A _ _ tail =>
      maxEntryNorm (by omega) A :: tail.stageMaxes

/-- The source count, stated honestly for growth-producing updates:
`2 * q ≤ n - 2`. -/
theorem two_mul_growthUpdates_le_sub_two : {n : ℕ} →
    {A : Higham11SkewMatrix n} → (trace : Higham11ExactSkewTrace A) →
    2 * trace.growthUpdates ≤ n - 2
  | _, _, .nil _ => by simp [growthUpdates]
  | _, _, .singleton _ _ => by simp [growthUpdates]
  | _, _, .noAction _ _ _ tail => by
      have ih := two_mul_growthUpdates_le_sub_two tail
      simp only [growthUpdates]
      omega
  | _, _, .two (n := n) _ _ _ tail => by
      have ih := two_mul_growthUpdates_le_sub_two tail
      by_cases hn : 2 ≤ n
      · simp [growthUpdates, hn]
        omega
      · simp [growthUpdates, hn]
        omega

/-- Every active matrix carried by a trace is skew-symmetric. -/
theorem isSkew : {n : ℕ} → {A : Higham11SkewMatrix n} →
    Higham11ExactSkewTrace A → higham11_16_IsSkewSymmetric n A
  | _, _, .nil A => by intro i; exact Fin.elim0 i
  | _, _, .singleton _ hA => hA
  | _, _, .noAction _ hA _ _ => hA
  | _, _, .two _ hA _ _ => hA

/-- A skew one-by-one matrix has max-entry norm zero. -/
theorem singleton_maxEntryNorm_eq_zero (A : Higham11SkewMatrix 1)
    (hA : higham11_16_IsSkewSymmetric 1 A) :
    maxEntryNorm (by omega : 0 < 1) A = 0 := by
  apply le_antisymm
  · apply maxEntryNorm_le_of_entry_le_bound (by omega) A 0
    intro i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0,
      higham11_16_skew_diag_zero 1 A hA 0]
    simp
  · exact maxEntryNorm_nonneg (by omega) A

/-- Traces of dimension at most one contain only zero stage maxima. -/
theorem stageMaxes_eq_zero_of_dimension_le_one {n : ℕ}
    {A : Higham11SkewMatrix n} (trace : Higham11ExactSkewTrace A)
    (hn : n ≤ 1) : ∀ μ ∈ trace.stageMaxes, μ = 0 := by
  cases trace with
  | nil => simp [stageMaxes]
  | singleton A hA =>
      simp [stageMaxes, singleton_maxEntryNorm_eq_zero A hA]
  | noAction A hA hzero tail => omega
  | two A hA hzero tail => omega

/-- Exact trace recurrence: every active maximum is bounded by one factor
`3` for each growth-producing two-by-two update. -/
theorem stageMax_le_growth_pow : {n : ℕ} →
    {A : Higham11SkewMatrix n} → (trace : Higham11ExactSkewTrace A) →
    (hn : 0 < n) → ∀ μ ∈ trace.stageMaxes,
      μ ≤ (3 : ℝ) ^ trace.growthUpdates * maxEntryNorm hn A := by
  intro n A trace
  induction trace with
  | nil A =>
      intro hn
      omega
  | singleton A hA =>
      intro hn μ hμ
      simp only [stageMaxes, List.mem_singleton] at hμ
      subst μ
      simp [growthUpdates]
  | @noAction n A hA hzero tail ih =>
      intro hn μ hμ
      simp only [stageMaxes, List.mem_cons] at hμ
      rcases hμ with hμ | hμ
      · subst μ
        have hM : 0 ≤ maxEntryNorm (by omega : 0 < n + 2) A :=
          maxEntryNorm_nonneg (by omega) A
        have hp : (1 : ℝ) ≤ (3 : ℝ) ^ tail.growthUpdates :=
          one_le_pow₀ (by norm_num)
        simpa [growthUpdates] using le_mul_of_one_le_left hM hp
      · have htail := ih (by omega : 0 < n + 1) μ hμ
        have hnorm :=
          higham11_9_skewNoActionTail_maxEntryNorm_le
            (by omega : 0 < n + 1) A
        calc
          μ ≤ (3 : ℝ) ^ tail.growthUpdates *
              maxEntryNorm (by omega : 0 < n + 1)
                (higham11_9_skewNoActionTail A) := htail
          _ ≤ (3 : ℝ) ^ tail.growthUpdates *
              maxEntryNorm (by omega : 0 < n + 2) A :=
            mul_le_mul_of_nonneg_left hnorm (by positivity)
          _ = (3 : ℝ) ^
                (Higham11ExactSkewTrace.noAction A hA hzero tail).growthUpdates *
              maxEntryNorm hn A := by rfl
  | @two n A hA hzero tail ih =>
      intro hn μ hμ
      simp only [stageMaxes, List.mem_cons] at hμ
      rcases hμ with hμ | hμ
      · subst μ
        have hM : 0 ≤ maxEntryNorm (by omega : 0 < n + 2) A :=
          maxEntryNorm_nonneg (by omega) A
        have hp : (1 : ℝ) ≤
            (3 : ℝ) ^
              (Higham11ExactSkewTrace.two A hA hzero tail).growthUpdates :=
          one_le_pow₀ (by norm_num)
        exact le_mul_of_one_le_left hM hp
      · by_cases hdim : 2 ≤ n
        · have htail := ih (by omega : 0 < n) μ hμ
          have hnorm := higham11_9_skewActualSchurTwo_maxEntryNorm_le
            (by omega : 0 < n) A hA hzero
          calc
            μ ≤ (3 : ℝ) ^ tail.growthUpdates *
                maxEntryNorm (by omega : 0 < n)
                  (higham11_9_skewActualSchurTwo A) := htail
            _ ≤ (3 : ℝ) ^ tail.growthUpdates *
                (3 * maxEntryNorm (by omega : 0 < n + 2) A) :=
              mul_le_mul_of_nonneg_left hnorm (by positivity)
            _ = (3 : ℝ) ^ (tail.growthUpdates + 1) *
                maxEntryNorm (by omega : 0 < n + 2) A := by
              rw [pow_succ]
              ring
            _ = (3 : ℝ) ^
                  (Higham11ExactSkewTrace.two A hA hzero tail).growthUpdates *
                maxEntryNorm hn A := by
              simp [growthUpdates, hdim]
        · have hz := stageMaxes_eq_zero_of_dimension_le_one tail (by omega) μ hμ
          rw [hz]
          exact mul_nonneg (pow_nonneg (by norm_num) _)
            (maxEntryNorm_nonneg hn A)

/-- Every active max-entry magnitude satisfies the printed global envelope
`(sqrt 3)^(n-2)`; this is derived from the corrected local coupled recurrence
and the trace's structural update count. -/
theorem stageMax_le_printed_sqrt_growth {n : ℕ}
    {A : Higham11SkewMatrix n} (trace : Higham11ExactSkewTrace A)
    (hn : 0 < n) (μ : ℝ) (hμ : μ ∈ trace.stageMaxes) :
    μ ≤ (Real.sqrt 3) ^ (n - 2) * maxEntryNorm hn A := by
  have hlocal := trace.stageMax_le_growth_pow hn μ hμ
  have hcount := trace.two_mul_growthUpdates_le_sub_two
  have hsqrtSq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hthreePow : (3 : ℝ) ^ trace.growthUpdates =
      (Real.sqrt 3) ^ (2 * trace.growthUpdates) := by
    calc
      (3 : ℝ) ^ trace.growthUpdates =
          ((Real.sqrt 3) ^ 2) ^ trace.growthUpdates := by rw [hsqrtSq]
      _ = (Real.sqrt 3) ^ (2 * trace.growthUpdates) :=
        (pow_mul (Real.sqrt 3) 2 trace.growthUpdates).symm
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [Real.one_le_sqrt]
    norm_num
  have hpow : (Real.sqrt 3) ^ (2 * trace.growthUpdates) ≤
      (Real.sqrt 3) ^ (n - 2) :=
    pow_le_pow_right₀ hsqrtOne hcount
  calc
    μ ≤ (3 : ℝ) ^ trace.growthUpdates * maxEntryNorm hn A := hlocal
    _ = (Real.sqrt 3) ^ (2 * trace.growthUpdates) *
        maxEntryNorm hn A := by rw [hthreePow]
    _ ≤ (Real.sqrt 3) ^ (n - 2) * maxEntryNorm hn A :=
      mul_le_mul_of_nonneg_right hpow (maxEntryNorm_nonneg hn A)

/-- Ratio form of the source growth-factor statement for every matrix in the
actual recursive trace. -/
theorem stageGrowthFactor_printed_bound {n : ℕ}
    {A : Higham11SkewMatrix n} (trace : Higham11ExactSkewTrace A)
    (hn : 0 < n) (hAmax : 0 < maxEntryNorm hn A)
    (μ : ℝ) (hμ : μ ∈ trace.stageMaxes) :
    higham11_9_skewGrowthBound n (μ / maxEntryNorm hn A) := by
  unfold higham11_9_skewGrowthBound
  rw [div_le_iff₀ hAmax]
  exact trace.stageMax_le_printed_sqrt_growth hn μ hμ

/-- The stage permutation is identity at a no-action stage and is exactly the
actual selector permutation at a two-by-two stage. -/
noncomputable def firstPerm : {n : ℕ} → {A : Higham11SkewMatrix n} →
    Higham11ExactSkewTrace A → Equiv.Perm (Fin n)
  | _, _, .nil _ => Equiv.refl _
  | _, _, .singleton _ _ => Equiv.refl _
  | _, _, .noAction _ _ _ _ => Equiv.refl _
  | _, _, .two A _ _ _ => higham11_9_skewActualPerm (by omega) A

theorem firstPerm_injective {n : ℕ} {A : Higham11SkewMatrix n}
    (trace : Higham11ExactSkewTrace A) : Function.Injective trace.firstPerm :=
  trace.firstPerm.injective

/-- The selected first-stage symmetric permutation preserves skew-symmetry. -/
theorem firstPermuted_isSkew {n : ℕ} {A : Higham11SkewMatrix n}
    (trace : Higham11ExactSkewTrace A) :
    higham11_16_IsSkewSymmetric n
      (fun i j => A (trace.firstPerm i) (trace.firstPerm j)) := by
  intro i j
  exact trace.isSkew _ _

end Higham11ExactSkewTrace

/-- The no-action branch has a zero leading off-diagonal column and, by
skew-symmetry, a zero leading off-diagonal row. -/
theorem higham11_9_noAction_offDiagonal_zero {n : ℕ}
    (A : Higham11SkewMatrix (n + 2))
    (hA : higham11_16_IsSkewSymmetric (n + 2) A)
    (hzero : higham11_9_firstColumnTailZero (by omega : 2 ≤ n + 2) A) :
    ∀ j : Fin (n + 2), j ≠ 0 → A j 0 = 0 ∧ A 0 j = 0 := by
  intro j hj
  have hcol := hzero j hj
  have hcol' : A j 0 = 0 := by simpa using hcol
  refine ⟨hcol', ?_⟩
  calc
    A 0 j = -A j 0 := hA 0 j
    _ = 0 := by rw [hcol', neg_zero]

/-- Every finite skew-symmetric matrix has the literal, structurally
terminating Algorithm 11.9 trace. -/
theorem higham11_9_nonempty_exactSkewTrace :
    ∀ {n : ℕ} (A : Higham11SkewMatrix n),
      higham11_16_IsSkewSymmetric n A → Nonempty (Higham11ExactSkewTrace A) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro A hA
      cases n with
      | zero => exact ⟨.nil A⟩
      | succ m =>
          cases m with
          | zero => exact ⟨.singleton A hA⟩
          | succ k =>
              by_cases hzero :
                  higham11_9_firstColumnTailZero (by omega : 2 ≤ k + 2) A
              · let S := higham11_9_skewNoActionTail A
                have hS : higham11_16_IsSkewSymmetric (k + 1) S :=
                  higham11_9_skewNoActionTail_isSkew A hA
                let tail : Higham11ExactSkewTrace S :=
                  Classical.choice (ih (k + 1) (by omega) S hS)
                exact ⟨.noAction A hA hzero tail⟩
              · let S := higham11_9_skewActualSchurTwo A
                have hS : higham11_16_IsSkewSymmetric k S :=
                  higham11_9_skewActualSchurTwo_isSkew A hA
                let tail : Higham11ExactSkewTrace S :=
                  Classical.choice (ih k (by omega) S hS)
                exact ⟨.two A hA hzero tail⟩

/-- Choice-fixed exact recursive execution of Algorithm 11.9. -/
noncomputable def higham11_9_exactSkewTrace {n : ℕ}
    (A : Higham11SkewMatrix n) (hA : higham11_16_IsSkewSymmetric n A) :
    Higham11ExactSkewTrace A :=
  Classical.choice (higham11_9_nonempty_exactSkewTrace A hA)

/-- Public discrepancy witness retained next to the corrected recursive trace:
the actual printed selector can produce a multiplier of modulus `50 > 1`. -/
theorem higham11_9_exactSkewTrace_printed_unit_multiplier_claim_is_false :
    higham11_16_IsSkewSymmetric 4 higham11_9_twoColumnCounterexample ∧
      IsUnit (Matrix.of higham11_9_twoColumnCounterexample) ∧
      1 <
        |higham11_9_skewActualPermutedMatrix (by omega : 2 ≤ 4)
              higham11_9_twoColumnCounterexample (3 : Fin 4) (1 : Fin 4) /
          higham11_9_skewActualPermutedMatrix (by omega : 2 ≤ 4)
              higham11_9_twoColumnCounterexample (1 : Fin 4) (0 : Fin 4)| :=
  higham11_9_printed_twoColumn_search_does_not_bound_multipliers

end NumStability
