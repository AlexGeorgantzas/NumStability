import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.QRSolve
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.QR.GramSchmidtPolar
import NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR
import NumStability.Algorithms.LinearSystems.QR.HouseholderSpec
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Source.Higham.Chapter19.Theorem06.CoxHighamAssembly
import NumStability.Source.Higham.Chapter19.Theorem06.Pivoted
import NumStability.Analysis.SingularValues.RectangularRankFactorization
import NumStability.Source.Higham.Chapter21.Equation04.Pseudoinverse
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot
import NumStability.Source.Higham.Chapter19.Theorem06.ElementwisePackaged

namespace NumStability

open scoped BigOperators

/-!
# Basic

Canonical reusable module extracted without change from LSE.
-/

private theorem theorem20_7_finUniv_nonempty_of_pos {n : ℕ} (hn : 0 < n) :
    (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0, hn⟩, by simp⟩
private theorem theorem20_7_finProdUniv_nonempty_of_pos {n : ℕ} (hn : 0 < n) :
    (Finset.univ : Finset (Fin n × Fin n)).Nonempty :=
  ⟨(⟨0, hn⟩, ⟨0, hn⟩), by simp⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    source row scale `max_j |a_ij|` for a nonempty row. -/
noncomputable def theorem20_7_initialRowMax {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin n))
    (theorem20_7_finUniv_nonempty_of_pos hn) (fun j => |A i j|)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    finite source maximum `max_{j,k} |a_ij^(k)|` over the modeled QR stages. -/
noncomputable def theorem20_7_stageRowMax {m n : ℕ} (hn : 0 < n)
    (Astage : ℕ → Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin n × Fin n))
    (theorem20_7_finProdUniv_nonempty_of_pos hn)
    (fun p => |Astage p.1.val i p.2|)
/-- Each initial row entry is bounded by the source row maximum used in
    Theorem 20.7. -/
theorem theorem20_7_initialRowMax_entry_le {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    |A i j| ≤ theorem20_7_initialRowMax hn A i := by
  unfold theorem20_7_initialRowMax
  exact
    Finset.le_sup' (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => |A i j|) (Finset.mem_univ j)
/-- The initial row maximum in Theorem 20.7 is nonnegative. -/
theorem theorem20_7_initialRowMax_nonneg {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    0 ≤ theorem20_7_initialRowMax hn A i := by
  let j : Fin n := ⟨0, hn⟩
  exact
    (abs_nonneg (A i j)).trans
      (theorem20_7_initialRowMax_entry_le hn A i j)
/-- A nonzero source row has a positive row maximum in the Theorem 20.7
    normalizer. -/
theorem theorem20_7_initialRowMax_pos_of_exists_entry_ne_zero {m n : ℕ}
    (hn : 0 < n) (A : Fin m → Fin n → ℝ) (i : Fin m)
    (hrow : ∃ j : Fin n, A i j ≠ 0) :
    0 < theorem20_7_initialRowMax hn A i := by
  rcases hrow with ⟨j, hj⟩
  exact
    (abs_pos.mpr hj).trans_le
      (theorem20_7_initialRowMax_entry_le hn A i j)
/-- Each staged row entry is bounded by the staged row maximum used in
    Theorem 20.7. -/
theorem theorem20_7_stageRowMax_entry_le {m n : ℕ} (hn : 0 < n)
    (Astage : ℕ → Fin m → Fin n → ℝ) (i : Fin m)
    (k j : Fin n) :
    |Astage k.val i j| ≤ theorem20_7_stageRowMax hn Astage i := by
  unfold theorem20_7_stageRowMax
  exact
    Finset.le_sup' (s := (Finset.univ : Finset (Fin n × Fin n)))
      (f := fun p => |Astage p.1.val i p.2|)
      (Finset.mem_univ (k, j))
/-- The staged row maximum in Theorem 20.7 is nonnegative. -/
theorem theorem20_7_stageRowMax_nonneg {m n : ℕ} (hn : 0 < n)
    (Astage : ℕ → Fin m → Fin n → ℝ) (i : Fin m) :
    0 ≤ theorem20_7_stageRowMax hn Astage i := by
  let k : Fin n := ⟨0, hn⟩
  let j : Fin n := ⟨0, hn⟩
  exact
    (abs_nonneg (Astage k.val i j)).trans
      (theorem20_7_stageRowMax_entry_le hn Astage i k j)
/-- Pointwise staged entry bounds imply the finite staged-row maximum bound
    needed for the `α_i` ratio in Theorem 20.7. -/
theorem theorem20_7_stageRowMax_le_of_entry_le {m n : ℕ} (hn : 0 < n)
    (Astage : ℕ → Fin m → Fin n → ℝ) (i : Fin m) {C : ℝ}
    (hbound : ∀ k j : Fin n, |Astage k.val i j| ≤ C) :
    theorem20_7_stageRowMax hn Astage i ≤ C := by
  unfold theorem20_7_stageRowMax
  apply Finset.sup'_le
  intro p _hp
  exact hbound p.1 p.2
/-- Nat-indexed variant of `theorem20_7_stageRowMax_le_of_entry_le`.
    This is the form produced by the Chapter 19 row-wise QR stage recurrences. -/
theorem theorem20_7_stageRowMax_le_of_entry_le_nat {m n : ℕ} (hn : 0 < n)
    (Astage : ℕ → Fin m → Fin n → ℝ) (i : Fin m) {C : ℝ}
    (hbound : ∀ k : ℕ, k < n → ∀ j : Fin n, |Astage k i j| ≤ C) :
    theorem20_7_stageRowMax hn Astage i ≤ C := by
  exact theorem20_7_stageRowMax_le_of_entry_le hn Astage i
    (fun k j => hbound k.val k.isLt j)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    the source ratio `α_i = max_{j,k}|a_ij^(k)| / max_j |a_ij|`. -/
noncomputable def theorem20_7_alpha {m n : ℕ} (hn : 0 < n)
    (Astage : ℕ → Fin m → Fin n → ℝ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  theorem20_7_stageRowMax hn Astage i / theorem20_7_initialRowMax hn A i
/-- If the staged row maximum is at most `C` times the initial row maximum,
    then the Theorem 20.7 source ratio `α_i` is at most `C`. -/
theorem theorem20_7_alpha_le_of_stageRowMax_le_mul_initial {m n : ℕ}
    (hn : 0 < n) (Astage : ℕ → Fin m → Fin n → ℝ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) {C : ℝ}
    (hden : 0 < theorem20_7_initialRowMax hn A i)
    (hstage :
      theorem20_7_stageRowMax hn Astage i ≤
        C * theorem20_7_initialRowMax hn A i) :
    theorem20_7_alpha hn Astage A i ≤ C := by
  dsimp [theorem20_7_alpha]
  exact (div_le_iff₀ hden).mpr hstage
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    every finite row key admits a row permutation that is descending on each
    displayed active suffix.

This is the generic `Tuple.sort` bridge used to instantiate source row sorting
without importing heavier chapter-specific enumeration lemmas. -/
theorem theorem20_7_exists_descending_key_permutation_nat {m n : ℕ}
    (hnm : n ≤ m) (key : Fin m → ℝ) :
    ∃ σ : Fin m ≃ Fin m,
      ∀ k : ℕ, ∀ hk : k < n, ∀ s : Fin m, k ≤ s.val →
        key (σ s) ≤ key (σ ⟨k, lt_of_lt_of_le hk hnm⟩) := by
  let σ : Fin m ≃ Fin m := Tuple.sort (fun i : Fin m => - key i)
  refine ⟨σ, ?_⟩
  intro k hk s hks
  have hle : (⟨k, lt_of_lt_of_le hk hnm⟩ : Fin m) ≤ s := by
    exact hks
  have hmono := (Tuple.monotone_sort (fun i : Fin m => - key i)) hle
  exact neg_le_neg_iff.mp hmono
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    row sorting relabels the source row maximum by the sorting permutation. -/
theorem theorem20_7_initialRowMax_permuteRows {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (σ : Fin m ≃ Fin m) (i : Fin m) :
    theorem20_7_initialRowMax hn (fun r j => A (σ r) j) i =
      theorem20_7_initialRowMax hn A (σ i) := by
  simp [theorem20_7_initialRowMax]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    row sorting relabels the staged row maximum by the same permutation. -/
theorem theorem20_7_stageRowMax_permuteRows {m n : ℕ} (hn : 0 < n)
    (Astage : ℕ → Fin m → Fin n → ℝ) (σ : Fin m ≃ Fin m) (i : Fin m) :
    theorem20_7_stageRowMax hn (fun k r j => Astage k (σ r) j) i =
      theorem20_7_stageRowMax hn Astage (σ i) := by
  simp [theorem20_7_stageRowMax]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    common row sorting relabels the source ratio `α_i`. -/
theorem theorem20_7_alpha_permuteRows {m n : ℕ} (hn : 0 < n)
    (Astage : ℕ → Fin m → Fin n → ℝ) (A : Fin m → Fin n → ℝ)
    (σ : Fin m ≃ Fin m) (i : Fin m) :
    theorem20_7_alpha hn
        (fun k r j => Astage k (σ r) j) (fun r j => A (σ r) j) i =
      theorem20_7_alpha hn Astage A (σ i) := by
  simp [theorem20_7_alpha, theorem20_7_stageRowMax_permuteRows,
    theorem20_7_initialRowMax_permuteRows]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 row-sorting bridge:
    a permutation whose displayed active suffix is sorted by the original row
    maxima supplies the sorted-source hypothesis for the permuted matrix. -/
theorem theorem20_7_initialRowMax_sorted_of_permuteRows_sorted_nat
    {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (A : Fin m → Fin n → ℝ) (σ : Fin m ≃ Fin m)
    (hσA :
      ∀ k : ℕ, ∀ hk : k < n, ∀ s : Fin m, k ≤ s.val →
        theorem20_7_initialRowMax hn A (σ s) ≤
          theorem20_7_initialRowMax hn A
            (σ ⟨k, lt_of_lt_of_le hk hnm⟩)) :
    ∀ k : ℕ, ∀ hk : k < n, ∀ s : Fin m, k ≤ s.val →
      theorem20_7_initialRowMax hn (fun r j => A (σ r) j) s ≤
        theorem20_7_initialRowMax hn (fun r j => A (σ r) j)
          ⟨k, lt_of_lt_of_le hk hnm⟩ := by
  intro k hk s hks
  simpa [theorem20_7_initialRowMax_permuteRows] using hσA k hk s hks
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 row-sorting bridge:
    a permutation whose displayed active suffix is sorted by the original
    right-hand-side magnitudes supplies the `|b|` sorted-source hypothesis for
    the permuted vector. -/
theorem theorem20_7_abs_b_sorted_of_permuteRows_sorted_nat
    {m n : ℕ} (hnm : n ≤ m) (b : Fin m → ℝ) (σ : Fin m ≃ Fin m)
    (hσb :
      ∀ k : ℕ, ∀ hk : k < n, ∀ s : Fin m, k ≤ s.val →
        |b (σ s)| ≤ |b (σ ⟨k, lt_of_lt_of_le hk hnm⟩)|) :
    ∀ k : ℕ, ∀ hk : k < n, ∀ s : Fin m, k ≤ s.val →
      |(fun r => b (σ r)) s| ≤
        |(fun r => b (σ r)) ⟨k, lt_of_lt_of_le hk hnm⟩| := by
  intro k hk s hks
  simpa using hσb k hk s hks
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 row-scale bridge:
    an explicit row permutation transports the unweighted source ratio
    hypothesis to the permuted matrix. -/
theorem theorem20_7_initialRowMax_ratio_of_permuteRows_ratio_nat
    {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (A : Fin m → Fin n → ℝ) (σ : Fin m ≃ Fin m) {rho : ℝ}
    (hσratio :
      ∀ k : ℕ, ∀ hk : k < n, ∀ r : Fin m, k ≤ r.val →
        theorem20_7_initialRowMax hn A
            (σ ⟨k, lt_of_lt_of_le hk hnm⟩) /
          theorem20_7_initialRowMax hn A (σ r) ≤ rho) :
    ∀ k : ℕ, ∀ hk : k < n, ∀ r : Fin m, k ≤ r.val →
      theorem20_7_initialRowMax hn (fun s j => A (σ s) j)
          ⟨k, lt_of_lt_of_le hk hnm⟩ /
        theorem20_7_initialRowMax hn (fun s j => A (σ s) j) r ≤ rho := by
  intro k hk r hkr
  simpa [theorem20_7_initialRowMax_permuteRows] using hσratio k hk r hkr
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 row-sorting bridge:
    the source matrix row scale admits a concrete row permutation whose
    displayed active suffixes are sorted for the permuted matrix. -/
theorem theorem20_7_exists_initialRowMax_sorted_permuteRows_nat
    {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (A : Fin m → Fin n → ℝ) :
    ∃ σ : Fin m ≃ Fin m,
      ∀ k : ℕ, ∀ hk : k < n, ∀ s : Fin m, k ≤ s.val →
        theorem20_7_initialRowMax hn (fun r j => A (σ r) j) s ≤
          theorem20_7_initialRowMax hn (fun r j => A (σ r) j)
            ⟨k, lt_of_lt_of_le hk hnm⟩ := by
  rcases theorem20_7_exists_descending_key_permutation_nat hnm
      (fun i : Fin m => theorem20_7_initialRowMax hn A i) with
    ⟨σ, hσ⟩
  exact
    ⟨σ, theorem20_7_initialRowMax_sorted_of_permuteRows_sorted_nat
      hn hnm A σ hσ⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 row-sorting bridge:
    the source right-hand-side magnitudes have a concrete row permutation
    whose displayed active suffixes are sorted for the permuted vector. -/
theorem theorem20_7_exists_abs_b_sorted_permuteRows_nat
    {m n : ℕ} (hnm : n ≤ m) (b : Fin m → ℝ) :
    ∃ σ : Fin m ≃ Fin m,
      ∀ k : ℕ, ∀ hk : k < n, ∀ s : Fin m, k ≤ s.val →
        |(fun r => b (σ r)) s| ≤
          |(fun r => b (σ r)) ⟨k, lt_of_lt_of_le hk hnm⟩| := by
  rcases theorem20_7_exists_descending_key_permutation_nat hnm
      (fun i : Fin m => |b i|) with
    ⟨σ, hσ⟩
  refine ⟨σ, ?_⟩
  intro k hk s hks
  simpa using hσ k hk s hks
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 row-sorting policy:
    if source right-hand-side magnitudes are monotone with the source row
    maxima, a source row-max sorting hypothesis also sorts the source `|b|`
    key. -/
theorem theorem20_7_abs_b_sorted_of_initialRowMax_sorted_compat_nat
    {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hcompat :
      ∀ i j : Fin m,
        theorem20_7_initialRowMax hn A i ≤
          theorem20_7_initialRowMax hn A j →
        |b i| ≤ |b j|)
    (hAsorted :
      ∀ k : ℕ, ∀ hk : k < n, ∀ s : Fin m, k ≤ s.val →
        theorem20_7_initialRowMax hn A s ≤
          theorem20_7_initialRowMax hn A ⟨k, lt_of_lt_of_le hk hnm⟩) :
    ∀ k : ℕ, ∀ hk : k < n, ∀ s : Fin m, k ≤ s.val →
      |b s| ≤ |b ⟨k, lt_of_lt_of_le hk hnm⟩| := by
  intro k hk s hks
  exact hcompat s ⟨k, lt_of_lt_of_le hk hnm⟩ (hAsorted k hk s hks)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 row-sorting policy:
    if the source right-hand-side magnitudes are monotone with the source row
    maxima, any row-max sorting permutation also sorts the `|b|` key. -/
theorem theorem20_7_abs_b_sorted_of_permuteRows_initialRowMax_sorted_compat_nat
    {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (σ : Fin m ≃ Fin m)
    (hcompat :
      ∀ i j : Fin m,
        theorem20_7_initialRowMax hn A i ≤
          theorem20_7_initialRowMax hn A j →
        |b i| ≤ |b j|)
    (hσA :
      ∀ k : ℕ, ∀ hk : k < n, ∀ s : Fin m, k ≤ s.val →
        theorem20_7_initialRowMax hn A (σ s) ≤
          theorem20_7_initialRowMax hn A
            (σ ⟨k, lt_of_lt_of_le hk hnm⟩)) :
    ∀ k : ℕ, ∀ hk : k < n, ∀ s : Fin m, k ≤ s.val →
      |b (σ s)| ≤ |b (σ ⟨k, lt_of_lt_of_le hk hnm⟩)| := by
  intro k hk s hks
  exact
    hcompat (σ s) (σ ⟨k, lt_of_lt_of_le hk hnm⟩)
      (hσA k hk s hks)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 QR dependency:
    the raw pivot-maximality field follows from choosing the current active
    column with the finite active-max pivot selector. -/
theorem theorem20_7_pivotMax_of_activeMaxPivotColumn_nat
    {m n : ℕ} (hnm : n ≤ m)
    (Astage : ℕ → Fin m → Fin n → ℝ)
    (hpivotChoice : ∀ t (ht : t < n),
      Fin.mk t ht =
        householderActiveMaxPivotColumn
          (Fin.mk t (lt_of_lt_of_le ht hnm)) (Fin.mk t ht) (Astage t)) :
    ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
      householderTrailingColumnNorm2Sq
          (m := m) (n := n)
          (Fin.mk t (lt_of_lt_of_le ht hnm)) (Astage t) l ≤
        householderTrailingColumnNorm2Sq
          (m := m) (n := n)
          (Fin.mk t (lt_of_lt_of_le ht hnm)) (Astage t) (Fin.mk t ht) := by
  intro t ht l hl
  have hmax :=
    householderActiveMaxPivotColumn_pivot_max
      (Fin.mk t (lt_of_lt_of_le ht hnm)) (Fin.mk t ht) (Astage t) l hl
  simpa [← hpivotChoice t ht] using hmax
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 QR dependency:
    after swapping the active-max column into the current displayed pivot
    column, the displayed stage satisfies the raw pivot-maximality field used
    by the signed stored-QR completion wrappers. -/
theorem theorem20_7_pivotMax_of_activeMaxPivotColumn_stage_swaps_nat
    {m n : ℕ} (hnm : n ≤ m)
    (Araw Astage : ℕ → Fin m → Fin n → ℝ)
    (hstageSorted : ∀ t (ht : t < n),
      Astage t =
        householderSwapColumns (Araw t) (Fin.mk t ht)
          (householderActiveMaxPivotColumn
            (Fin.mk t (lt_of_lt_of_le ht hnm)) (Fin.mk t ht) (Araw t))) :
    ∀ t (ht : t < n), ∀ l : Fin n, t ≤ l.val →
      householderTrailingColumnNorm2Sq
          (m := m) (n := n)
          (Fin.mk t (lt_of_lt_of_le ht hnm)) (Astage t) l ≤
        householderTrailingColumnNorm2Sq
          (m := m) (n := n)
          (Fin.mk t (lt_of_lt_of_le ht hnm)) (Astage t) (Fin.mk t ht) := by
  intro t ht l hl
  rw [hstageSorted t ht]
  exact
    householderSwapColumns_activeMaxPivotColumn_pivot_max
      (Fin.mk t (lt_of_lt_of_le ht hnm)) (Fin.mk t ht) (Araw t) l hl
/-- Theorem 20.7 route audit: source row sorting alone does not imply the
    stronger `sqrt(m)` row-scale domination hypothesis used by the Chapter 19
    accumulated-error transfer.

For two rows and one column, row sorting can hold with row scales `2, 1`, but
the pivot row scale `2` is not bounded by `sqrt(2) * 1`. -/
theorem theorem20_7_initialRowMax_sorted_not_imp_sqrt_row_domination_two_by_one :
    ∃ A : Fin 2 → Fin 1 → ℝ,
      (∀ k : ℕ, ∀ hk : k < 1, ∀ s : Fin 2, k ≤ s.val →
        theorem20_7_initialRowMax (by norm_num : 0 < 1) A s ≤
          theorem20_7_initialRowMax (by norm_num : 0 < 1) A
            ⟨k, lt_of_lt_of_le hk (by norm_num : 1 ≤ 2)⟩) ∧
      ¬ (∀ k : ℕ, ∀ hk : k < 1, ∀ r : Fin 2, k ≤ r.val →
        theorem20_7_initialRowMax (by norm_num : 0 < 1) A
            ⟨k, lt_of_lt_of_le hk (by norm_num : 1 ≤ 2)⟩ ≤
          Real.sqrt (2 : ℝ) *
            theorem20_7_initialRowMax (by norm_num : 0 < 1) A r) := by
  let A : Fin 2 → Fin 1 → ℝ := fun i _ =>
    if i.val = 0 then 2 else 1
  refine ⟨A, ?_, ?_⟩
  · intro k hk s _hks
    have hk0 : k = 0 := Nat.lt_one_iff.mp hk
    subst k
    fin_cases s <;> simp [theorem20_7_initialRowMax, A]
  · intro hdom
    have h :=
      hdom 0 (by norm_num) ⟨1, by norm_num⟩ (by norm_num)
    simp [theorem20_7_initialRowMax, A] at h
    have hsqrt2_lt_two : Real.sqrt (2 : ℝ) < 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
        Real.sqrt_nonneg (2 : ℝ)]
    linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 QR dependency:
    Chapter 19's packaged original-space pivoted Householder QR backward-error
    result, exposed at the Chapter 20 row-wise least-squares boundary.

    This is the fully proved `sqrt(m)` column-norm package for the concrete
    computed pivoted QR.  It is weaker than the printed row-specific
    Powell--Reid envelope, but it gives a reusable original-space perturbation
    witness for later Theorem 20.7 handoffs. -/
theorem theorem20_7_pivoted_householder_qr_packaged_original_space_column_norm
    (fp : FPModel) (m n : ℕ) (A : Fin m → Fin n → ℝ)
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex m)) :
    ∃ (π : Equiv.Perm (Fin n)) (Q : Fin m → Fin m → ℝ)
      (Rhat : Fin m → Fin n → ℝ) (DeltaA : Fin m → Fin n → ℝ),
      IsUpperTrapezoidal m n Rhat ∧
      IsOrthogonal m Q ∧
      (∀ i j, Wave13.columnPermuteMatrix A π i j + DeltaA i j =
        matMulRect m m n Q Rhat i j) ∧
      (∀ i j, |DeltaA i j| ≤
        Real.sqrt (m : ℝ) *
          (H19.Theorem19_4.gamma_tilde fp m n *
            columnFrob (Wave13.columnPermuteMatrix A π) j)) :=
  Wave18C.theorem19_6_packaged_original_space_column_norm
    fp m n A hn hnm hvalid
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 QR dependency:
    per-stage column-pivoting discharge of the Cox--Higham recursive
    `hratio` obligation.

The newly merged Chapter 19 per-stage column-pivoting API proves the executed
sigma-ordering for the pivoted stage.  This wrapper feeds that sigma-ratio
directly into `Wave19.entrywise_recursive_cons`, replacing the abstract
`∀ j, ||Eta_j|| / ||v|| <= gammaTilde` premise by the concrete pivot-scale
conditions supplied by `Wave20.colPivot_ratio_le_of_sigma`. -/
theorem theorem20_7_colPivot_entrywise_recursive_cons_of_sigma
    {m p : ℕ}
    (A : Fin (m + 1) → Fin (p + 1) → ℝ)
    (Eta : Fin (m + 1) → Fin p → ℝ)
    (v : Fin (m + 1) → ℝ)
    (alpha : Fin (m + 1) → ℝ)
    (u gamma gammaTilde : ℝ)
    (hσpos :
      0 < |vecNorm2
        (panelFirstColumn (Nat.succ_pos p) (Wave20.colPivotSwap A))|)
    (huγ : 0 ≤ u + 2 * gamma)
    (hf : ∀ j : Fin p,
      vecNorm2 (fun s : Fin (m + 1) => Eta s j) ≤
        (u + 2 * gamma) *
          |vecNorm2
            (panelFirstColumn (Nat.succ_pos p) (Wave20.colPivotSwap A))|)
    (hvscale :
      Real.sqrt 2 *
          |vecNorm2
            (panelFirstColumn (Nat.succ_pos p) (Wave20.colPivotSwap A))| ≤
        vecNorm2 v)
    (hfold : (u + 2 * gamma) / Real.sqrt 2 ≤ gammaTilde)
    (hvpos : 0 < vecNorm2 v)
    (hvnorm : (∑ s : Fin (m + 1), v s * v s) = 2)
    (halpha : ∀ i, 0 ≤ alpha i)
    (hv2alpha : ∀ i, |v i| ≤ 2 * alpha i)
    (hgamma : 0 ≤ gammaTilde)
    (i : Fin (m + 1)) (j : Fin p) :
    |matMulRect (m + 1) (m + 1) p (householder (m + 1) v 1) Eta i j| ≤
      |Eta i j| + 4 * gammaTilde * alpha i := by
  have hratio :
      ∀ j : Fin p,
        vecNorm2 (fun s : Fin (m + 1) => Eta s j) / vecNorm2 v ≤
          gammaTilde := by
    intro j
    exact
      Wave20.colPivot_ratio_le_of_sigma A
        (fun s : Fin (m + 1) => Eta s j) v u gamma gammaTilde hσpos huγ
        (hf j) hvscale hfold
  exact
    Wave19.entrywise_recursive_cons v Eta alpha gammaTilde hvpos hvnorm halpha
      hv2alpha hratio hgamma i j
/-- Theorem 20.7 row-scale bridge: an explicit source-row ratio bound
    discharges the `sqrt(m)` domination hypothesis used by the Chapter 19
    accumulated-error transfer for the unweighted row normalizer. -/
theorem theorem20_7_initialRowMax_sqrt_domination_of_ratio_le_nat
    {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hrows : ∀ i : Fin m, ∃ j : Fin n, A i j ≠ 0)
    (hratio :
      ∀ k : ℕ, ∀ hk : k < n, ∀ r : Fin m, k ≤ r.val →
        theorem20_7_initialRowMax hn A
            ⟨k, lt_of_lt_of_le hk hnm⟩ /
          theorem20_7_initialRowMax hn A r ≤ Real.sqrt (m : ℝ)) :
    ∀ k : ℕ, ∀ hk : k < n, ∀ r : Fin m, k ≤ r.val →
      theorem20_7_initialRowMax hn A
          ⟨k, lt_of_lt_of_le hk hnm⟩ ≤
        Real.sqrt (m : ℝ) * theorem20_7_initialRowMax hn A r := by
  intro k hk r hkr
  have hden : 0 < theorem20_7_initialRowMax hn A r :=
    theorem20_7_initialRowMax_pos_of_exists_entry_ne_zero hn A r (hrows r)
  exact (div_le_iff₀ hden).mp (hratio k hk r hkr)
/-- Theorem 20.7 row-scale bridge: the pointwise `sqrt(m)` domination
    hypothesis for source row maxima implies the corresponding active-suffix
    source-row ratio bound. -/
theorem theorem20_7_initialRowMax_ratio_le_of_sqrt_domination_nat
    {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hrows : ∀ i : Fin m, ∃ j : Fin n, A i j ≠ 0)
    (hdom :
      ∀ k : ℕ, ∀ hk : k < n, ∀ r : Fin m, k ≤ r.val →
        theorem20_7_initialRowMax hn A
            ⟨k, lt_of_lt_of_le hk hnm⟩ ≤
          Real.sqrt (m : ℝ) * theorem20_7_initialRowMax hn A r) :
    ∀ k : ℕ, ∀ hk : k < n, ∀ r : Fin m, k ≤ r.val →
      theorem20_7_initialRowMax hn A
          ⟨k, lt_of_lt_of_le hk hnm⟩ /
        theorem20_7_initialRowMax hn A r ≤ Real.sqrt (m : ℝ) := by
  intro k hk r hkr
  have hden : 0 < theorem20_7_initialRowMax hn A r :=
    theorem20_7_initialRowMax_pos_of_exists_entry_ne_zero hn A r (hrows r)
  exact (div_le_iff₀ hden).mpr (hdom k hk r hkr)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    finite maximum over staged right-hand-side entries. -/
noncomputable def theorem20_7_stageBMax {m n : ℕ} (hn : 0 < n)
    (bstage : ℕ → Fin m → ℝ) (i : Fin m) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin n))
    (theorem20_7_finUniv_nonempty_of_pos hn) (fun k => |bstage k.val i|)
/-- Each staged right-hand-side entry is bounded by the finite staged `b`
    maximum used in the Theorem 20.7 `β_i` denominator bridge. -/
theorem theorem20_7_stageBMax_entry_le {m n : ℕ} (hn : 0 < n)
    (bstage : ℕ → Fin m → ℝ) (i : Fin m) (k : Fin n) :
    |bstage k.val i| ≤ theorem20_7_stageBMax hn bstage i := by
  unfold theorem20_7_stageBMax
  exact
    Finset.le_sup' (s := (Finset.univ : Finset (Fin n)))
      (f := fun k => |bstage k.val i|) (Finset.mem_univ k)
/-- Pointwise staged right-hand-side bounds imply the finite staged `b`
    maximum bound used in Theorem 20.7. -/
theorem theorem20_7_stageBMax_le_of_entry_le {m n : ℕ} (hn : 0 < n)
    (bstage : ℕ → Fin m → ℝ) (i : Fin m) {C : ℝ}
    (hbound : ∀ k : Fin n, |bstage k.val i| ≤ C) :
    theorem20_7_stageBMax hn bstage i ≤ C := by
  unfold theorem20_7_stageBMax
  apply Finset.sup'_le
  intro k _hk
  exact hbound k
/-- Nat-indexed variant of `theorem20_7_stageBMax_le_of_entry_le`.
    This matches the stage indexing of the Chapter 19 row-wise QR wrappers. -/
theorem theorem20_7_stageBMax_le_of_entry_le_nat {m n : ℕ} (hn : 0 < n)
    (bstage : ℕ → Fin m → ℝ) (i : Fin m) {C : ℝ}
    (hbound : ∀ k : ℕ, k < n → |bstage k i| ≤ C) :
    theorem20_7_stageBMax hn bstage i ≤ C := by
  exact theorem20_7_stageBMax_le_of_entry_le hn bstage i
    (fun k => hbound k.val k.isLt)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    row sorting relabels the staged right-hand-side maximum. -/
theorem theorem20_7_stageBMax_permuteRows {m n : ℕ} (hn : 0 < n)
    (bstage : ℕ → Fin m → ℝ) (σ : Fin m ≃ Fin m) (i : Fin m) :
    theorem20_7_stageBMax hn (fun k r => bstage k (σ r)) i =
      theorem20_7_stageBMax hn bstage (σ i) := by
  simp [theorem20_7_stageBMax]
/-- Finite row maximum for row-indexed Theorem 20.7 ratios. -/
noncomputable def theorem20_7_rowRatioMax {m : ℕ} (hm : 0 < m)
    (rho : Fin m → ℝ) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin m))
    (theorem20_7_finUniv_nonempty_of_pos hm) rho
/-- Each row ratio is bounded by the finite row maximum. -/
theorem theorem20_7_rowRatioMax_entry_le {m : ℕ} (hm : 0 < m)
    (rho : Fin m → ℝ) (i : Fin m) :
    rho i ≤ theorem20_7_rowRatioMax hm rho := by
  unfold theorem20_7_rowRatioMax
  exact
    Finset.le_sup' (s := (Finset.univ : Finset (Fin m)))
      (f := rho) (Finset.mem_univ i)
/-- Uniform row-ratio bounds imply the finite row maximum bound. -/
theorem theorem20_7_rowRatioMax_le_of_forall {m : ℕ} (hm : 0 < m)
    (rho : Fin m → ℝ) {C : ℝ} (h : ∀ i : Fin m, rho i ≤ C) :
    theorem20_7_rowRatioMax hm rho ≤ C := by
  unfold theorem20_7_rowRatioMax
  apply Finset.sup'_le
  intro i _hi
  exact h i
/-- Source nonzero-row witnesses are preserved by a common row permutation. -/
theorem theorem20_7_rows_nonzero_permuteRows
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (σ : Fin m ≃ Fin m)
    (hrows : ∀ i : Fin m, ∃ j : Fin n, A i j ≠ 0) :
    ∀ i : Fin m, ∃ j : Fin n, (fun r j => A (σ r) j) i j ≠ 0 := by
  intro i
  exact hrows (σ i)
/-- Source domination of `|b_i|` by `phi * rowMax_i` is preserved by a
    common row permutation. -/
theorem theorem20_7_abs_b_le_phi_initialRowMax_permuteRows
    {m n : ℕ} (hn : 0 < n) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (σ : Fin m ≃ Fin m) {phi : ℝ}
    (hdom : ∀ i : Fin m,
      |b i| ≤ phi * theorem20_7_initialRowMax hn A i) :
    ∀ i : Fin m,
      |(fun r => b (σ r)) i| ≤
        phi * theorem20_7_initialRowMax hn
          (fun r j => A (σ r) j) i := by
  intro i
  simpa [theorem20_7_initialRowMax_permuteRows] using hdom (σ i)
/-- If `α_i ≤ C`, the staged row maximum is bounded by `C` times the initial
    row maximum.  This is the reverse direction needed when a Theorem 20.7
    ratio bound has already been established. -/
theorem theorem20_7_stageRowMax_le_mul_initial_of_alpha_le {m n : ℕ}
    (hn : 0 < n) (Astage : ℕ → Fin m → Fin n → ℝ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) {C : ℝ}
    (hden : 0 < theorem20_7_initialRowMax hn A i)
    (halpha : theorem20_7_alpha hn Astage A i ≤ C) :
    theorem20_7_stageRowMax hn Astage i ≤
      C * theorem20_7_initialRowMax hn A i := by
  have hEq :
      theorem20_7_alpha hn Astage A i *
          theorem20_7_initialRowMax hn A i =
        theorem20_7_stageRowMax hn Astage i := by
    dsimp [theorem20_7_alpha]
    exact div_mul_cancel₀ _ (ne_of_gt hden)
  calc
    theorem20_7_stageRowMax hn Astage i
        = theorem20_7_alpha hn Astage A i *
            theorem20_7_initialRowMax hn A i := hEq.symm
    _ ≤ C * theorem20_7_initialRowMax hn A i :=
        mul_le_mul_of_nonneg_right halpha hden.le
/-- Theorem 20.7 support: signed stored-QR stages supply the completed-column
    preservation field needed by the one-step completion-time `A` adapter. -/
theorem theorem20_7_signed_stage_completed_column_preservation_nat
    {m n : ℕ} (hnm : n ≤ m)
    (fp : FPModel) (Astage : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hStep : ∀ k, k < n →
      Astage (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (storedQRSignedStageVector hnm Astage alpha k)
          (storedQRSignedStageBeta hnm Astage alpha k)
          (Astage k)) :
    ∀ i : Fin m, i.val + 1 < n → ∀ j : Fin n, j.val < i.val →
      ∀ a : Fin m,
        matMulVec m
          (householder m
            (storedQRSignedStageVector hnm Astage alpha i.val)
            (storedQRSignedStageBeta hnm Astage alpha i.val))
          (fun r => Astage i.val r j) a =
          Astage i.val a j := by
  intro i hi j hj a
  have hit : i.val < n := by omega
  have hStepConcrete : ∀ k (hk : k < n),
      Astage (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            (Fin.mk k (lt_of_lt_of_le hk hnm))
            (fun a => Astage k a (Fin.mk k hk)) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              (Fin.mk k (lt_of_lt_of_le hk hnm))
              (fun a => Astage k a (Fin.mk k hk)) (alpha k)))
          (Astage k) := by
    intro k hk
    simpa [storedQRSignedStageVector, storedQRSignedStageBeta, hk] using
      hStep k hk
  exact
    H19.Theorem19_6.stored_signed_stage_completed_column_preservation
      hnm fp Astage alpha hStepConcrete i.val hit j hj a
/-- Theorem 20.7 support: signed stored-QR stages supply the pivot-column
    zeroing field needed by the one-step completion-time `A` adapter. -/
theorem theorem20_7_signed_stage_pivot_column_zero_below_of_trailingNorm_pos_nat
    {m n : ℕ} (hnm : n ≤ m)
    (Astage : ℕ → Fin m → Fin n → ℝ) (alpha : ℕ → ℝ)
    (hAlphaDef : ∀ t (ht : t < n),
      alpha t =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              (Fin.mk t (lt_of_lt_of_le ht hnm))
              (fun a => Astage t a (Fin.mk t ht))))
          (Astage t (Fin.mk t (lt_of_lt_of_le ht hnm)) (Fin.mk t ht)))
    (htrailingPos : ∀ t (ht : t < n),
      0 < householderTrailingNorm2Sq m
          (Fin.mk t (lt_of_lt_of_le ht hnm))
          (fun a => Astage t a (Fin.mk t ht))) :
    ∀ i : Fin m, i.val + 1 < n → ∀ j : Fin n, j.val = i.val →
      ∀ a : Fin m, i.val < a.val →
        matMulVec m
          (householder m
            (storedQRSignedStageVector hnm Astage alpha i.val)
            (storedQRSignedStageBeta hnm Astage alpha i.val))
          (fun r => Astage i.val r j) a = 0 := by
  intro i hi j hj a ha
  have hit : i.val < n := by omega
  have hjext : j = Fin.mk i.val hit := Fin.ext hj
  subst j
  exact
    H19.Theorem19_6.stored_signed_stage_pivot_column_zero_below_of_trailingNorm_pos
      hnm Astage alpha i.val hit (hAlphaDef i.val hit)
      (htrailingPos i.val hit) a ha
/-- Theorem 20.7 support: a vector whose entries are bounded by a scalar
    multiple of a source row scale has the corresponding `sqrt(m)` norm bound.

This is the finite-dimensional norm bridge used to turn entrywise QR stage
bounds into the column/RHS norm estimates consumed by the compact-budget
coefficient adapters. -/
theorem theorem20_7_vecNorm2_le_sqrt_card_mul_scale_of_abs_le
    {m : ℕ} (x : Fin m → ℝ) {C S : ℝ}
    (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hentry : ∀ r : Fin m, |x r| ≤ C * S) :
    vecNorm2 x ≤ (Real.sqrt (m : ℝ) * C) * S := by
  have hB : 0 ≤ C * S := mul_nonneg hC hS
  calc
    vecNorm2 x ≤ Real.sqrt (m : ℝ) * (C * S) :=
      vecNorm2_le_sqrt_card_mul_of_abs_le x hB hentry
    _ = (Real.sqrt (m : ℝ) * C) * S := by ring
/-- Theorem 20.7 support: the concrete stored signed-stage Householder vector
    has the zero prefix expected of the active trailing reflector. -/
theorem theorem20_7_storedQRSignedStageVector_zero_prefix_nat
    {m n : ℕ} (hnm : n ≤ m)
    (Ahat : ℕ → Fin m → Fin n → ℝ) (alpha : ℕ → ℝ)
    {t : ℕ} (ht : t < n) :
    ∀ r : Fin m, r.val < t →
      storedQRSignedStageVector hnm Ahat alpha t r = 0 := by
  intro r hr
  simpa [storedQRSignedStageVector, ht] using
    householderTrailingActiveVector_zero_prefix m
      ⟨t, lt_of_lt_of_le ht hnm⟩
      (fun a => Ahat t a ⟨t, ht⟩) (alpha t) r hr
/-- Theorem 20.7 support: active-tail entry bounds control the norm of the
    trailing part of a vector.

This is the active-tail analogue of
`theorem20_7_vecNorm2_le_sqrt_card_mul_scale_of_abs_le`: entries above the
pivot are zeroed by `householderTrailingPart`, so callers only need bounds on
rows `p.val <= r.val`. -/
theorem theorem20_7_vecNorm2_trailingPart_le_sqrt_card_mul_scale_of_active_abs_le
    {m : ℕ} (p : Fin m) (x : Fin m → ℝ) {C S : ℝ}
    (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hentry : ∀ r : Fin m, p.val ≤ r.val → |x r| ≤ C * S) :
    vecNorm2 (householderTrailingPart m p x) ≤
      (Real.sqrt (m : ℝ) * C) * S := by
  refine
    theorem20_7_vecNorm2_le_sqrt_card_mul_scale_of_abs_le
      (householderTrailingPart m p x) hC hS ?_
  intro r
  by_cases hr : r.val < p.val
  · have hnonneg : 0 ≤ C * S := mul_nonneg hC hS
    simpa [householderTrailingPart, hr] using hnonneg
  · exact
      (by
        simpa [householderTrailingPart, hr] using
          hentry r (Nat.le_of_not_gt hr))
/-- Theorem 20.7 support: signed nonbreakdown stages discharge the scalar
    compact-coefficient slack premise for the active-tail completion adapters.

The previous active-tail adapters exposed a raw reflector-dependent
`householderCompactNormBudgetCoeff` comparison.  For the signed stored-QR
stage, the source alpha definition and positive trailing norm give a nonzero
Householder denominator, hence the Chapter 19 compact-coefficient estimate
`u + 2 * factor`.  This lemma turns that estimate into the exact scalar
slack premise used by the row-wise weighted-LS route. -/
theorem theorem20_7_signed_stage_norm_coeff_slack_of_trailingNorm_pos_nat
    {m n : ℕ} (hnm : n ≤ m)
    (fp : FPModel) (Ahat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ) (C slack : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hC : ∀ i : Fin m, i.val + 1 < n → 0 ≤ C i.val)
    (hAlphaDef : ∀ t (ht : t < n),
      alpha t =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              (Fin.mk t (lt_of_lt_of_le ht hnm))
              (fun a => Ahat t a (Fin.mk t ht))))
          (Ahat t (Fin.mk t (lt_of_lt_of_le ht hnm)) (Fin.mk t ht)))
    (htrailingPos : ∀ t (ht : t < n),
      0 < householderTrailingNorm2Sq m
          (Fin.mk t (lt_of_lt_of_le ht hnm))
          (fun a => Ahat t a (Fin.mk t ht)))
    (hcoeffSlack :
      ∀ i : Fin m, i.val + 1 < n →
        (fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m) *
            (Real.sqrt (m : ℝ) * C i.val) ≤
          slack i.val) :
    ∀ i : Fin m, i.val + 1 < n →
      householderCompactNormBudgetCoeff fp m
            (storedQRSignedStageVector hnm Ahat alpha i.val)
            (storedQRSignedStageBeta hnm Ahat alpha i.val) *
          (Real.sqrt (m : ℝ) * C i.val) ≤
        slack i.val := by
  intro i hi
  have hit : i.val < n := by omega
  let pivot : Fin m := Fin.mk i.val (lt_of_lt_of_le hit hnm)
  let pivotCol : Fin n := Fin.mk i.val hit
  have hAlphaSq :
      alpha i.val * alpha i.val =
        householderTrailingNorm2Sq m pivot
          (fun r => Ahat i.val r pivotCol) := by
    rw [hAlphaDef i.val hit]
    simpa [pivot, pivotCol] using
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
        m pivot (fun r => Ahat i.val r pivotCol)
  have hsign :
      alpha i.val * Ahat i.val pivot pivotCol ≤ 0 := by
    rw [hAlphaDef i.val hit]
    simpa [pivot, pivotCol] using
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
        m pivot (fun r => Ahat i.val r pivotCol)
  have hnorm :
      0 < householderTrailingNorm2Sq m pivot
          (fun r => Ahat i.val r pivotCol) := by
    simpa [pivot, pivotCol] using htrailingPos i.val hit
  have hden :
      (∑ r : Fin m,
        storedQRSignedStageVector hnm Ahat alpha i.val r *
          storedQRSignedStageVector hnm Ahat alpha i.val r) ≠ 0 := by
    have hden0 :
        (∑ r : Fin m,
          householderTrailingActiveVector m pivot
            (fun a => Ahat i.val a pivotCol) (alpha i.val) r *
            householderTrailingActiveVector m pivot
              (fun a => Ahat i.val a pivotCol) (alpha i.val) r) ≠ 0 :=
      householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
        m pivot (fun a => Ahat i.val a pivotCol) (alpha i.val)
        hAlphaSq hnorm hsign
    simpa [storedQRSignedStageVector, hit, pivot, pivotCol] using hden0
  have hcoeffStored :
      storedQRCompactStepNormBudgetCoeff hnm fp Ahat alpha ⟨i.val, hit⟩ ≤
        fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m :=
    storedQRCompactStepNormBudgetCoeff_le_of_den_ne_zero
      hnm fp Ahat alpha hm ⟨i.val, hit⟩ hden
  have hcoeff :
      householderCompactNormBudgetCoeff fp m
          (storedQRSignedStageVector hnm Ahat alpha i.val)
          (storedQRSignedStageBeta hnm Ahat alpha i.val) ≤
        fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m := by
    simpa [storedQRCompactStepNormBudgetCoeff] using hcoeffStored
  have hscale_nonneg : 0 ≤ Real.sqrt (m : ℝ) * C i.val :=
    mul_nonneg (Real.sqrt_nonneg _) (hC i hi)
  exact
    (mul_le_mul_of_nonneg_right hcoeff hscale_nonneg).trans
      (hcoeffSlack i hi)
/-- Theorem 20.7 support: stored RHS steps preserve completed rows.

Once row `i` has been processed, every later stored RHS step has active pivot
strictly below `i`; the definition of `fl_householderStoredRhsStep` copies such
prefix rows.  This is the exact preservation field needed by the weighted
least-squares completion-preservation route for `bhat`. -/
theorem theorem20_7_completedB_preservation_of_stored_rhs_steps_nat
    {m n : ℕ} (fp : FPModel) (v : ℕ → Fin m → ℝ) (beta : ℕ → ℝ)
    (bstage : ℕ → Fin m → ℝ)
    (hStep : ∀ k, k < n →
      bstage (k + 1) =
        fl_householderStoredRhsStep fp m k (v k) (beta k) (bstage k)) :
    ∀ i : Fin m, ∀ k : ℕ, k < n → i.val < k →
      bstage k i = bstage (i.val + 1) i := by
  have hprefix :
      ∀ k, k ≤ n → ∀ i : Fin m, i.val < k →
        bstage k i = bstage (i.val + 1) i := by
    intro k hk
    induction k with
    | zero =>
        intro i hi
        exact (Nat.not_lt_zero i.val hi).elim
    | succ k ih =>
        intro i hi
        have hk_lt : k < n := Nat.lt_of_succ_le hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | hi_eq
        · have hstepPoint :
            bstage (k + 1) i =
              fl_householderStoredRhsStep fp m k
                (v k) (beta k) (bstage k) i := by
              exact congrFun (hStep k hk_lt) i
          calc
            bstage (k + 1) i
                = fl_householderStoredRhsStep fp m k
                    (v k) (beta k) (bstage k) i := hstepPoint
            _ = bstage k i := by
                  simp [fl_householderStoredRhsStep, hi_lt]
            _ = bstage (i.val + 1) i := ih (Nat.le_of_lt hk_lt) i hi_lt
        · have hsucc : i.val + 1 = k + 1 := by omega
          simp [hsucc]
  intro i k hk hik
  exact hprefix k (Nat.le_of_lt hk) i hik
/-- Theorem 20.7 support: sequence-level completed-row preservation for `A`
    from a local stored-panel row-preservation field.

The concrete stored panel step does not, by definition alone, copy every row
above the active pivot on active/trailing columns.  This adapter therefore
exposes the honest local QR obligation: if each stored-panel step preserves all
rows above its pivot, then every completed row `i` remains equal to its
completion-time row `Astage (i+1) i` at all later stages. -/
theorem theorem20_7_completedA_preservation_of_stored_panel_step_row_preservation_nat
    {m n : ℕ} (fp : FPModel) (v : ℕ → Fin m → ℝ) (beta : ℕ → ℝ)
    (Astage : ℕ → Fin m → Fin n → ℝ)
    (hStep : ∀ k, k < n →
      Astage (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (beta k) (Astage k))
    (hrowStep :
      ∀ k, k < n → ∀ i : Fin m, i.val < k → ∀ j : Fin n,
        fl_householderStoredPanelStep fp m n k (v k) (beta k) (Astage k) i j =
          Astage k i j) :
    ∀ i : Fin m, ∀ k : ℕ, k < n → i.val < k → ∀ j : Fin n,
      Astage k i j = Astage (i.val + 1) i j := by
  have hprefix :
      ∀ k, k ≤ n → ∀ i : Fin m, i.val < k → ∀ j : Fin n,
        Astage k i j = Astage (i.val + 1) i j := by
    intro k hk
    induction k with
    | zero =>
        intro i hi j
        exact (Nat.not_lt_zero i.val hi).elim
    | succ k ih =>
        intro i hi j
        have hk_lt : k < n := Nat.lt_of_succ_le hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | hi_eq
        · have hstepPoint :
            Astage (k + 1) i j =
              fl_householderStoredPanelStep fp m n k
                (v k) (beta k) (Astage k) i j := by
              exact congrFun (congrFun (hStep k hk_lt) i) j
          calc
            Astage (k + 1) i j
                = fl_householderStoredPanelStep fp m n k
                    (v k) (beta k) (Astage k) i j := hstepPoint
            _ = Astage k i j := hrowStep k hk_lt i hi_lt j
            _ = Astage (i.val + 1) i j := ih (Nat.le_of_lt hk_lt) i hi_lt j
        · have hsucc : i.val + 1 = k + 1 := by omega
          simp [hsucc]
  intro i k hk hik j
  exact hprefix k (Nat.le_of_lt hk) i hik j
/-- Theorem 20.7 support: signed stored-QR stages preserve rows above the
    active pivot when subtracting zero is an exact copy operation.

The signed stage vector is zero above the pivot.  Therefore the compact
Householder update subtracts an exactly rounded zero from every entry in such a
row; completed columns are already copied by the stored-panel definition. -/
theorem theorem20_7_signed_stage_stored_panel_row_preservation_of_subtractZeroExact_nat
    {m n : ℕ} (hnm : n ≤ m) (fp : FPModel)
    (Ahat : ℕ → Fin m → Fin n → ℝ) (alpha : ℕ → ℝ)
    (hcopy : H19.Theorem19_13.subtractZeroExact fp) :
    ∀ k, k < n → ∀ i : Fin m, i.val < k → ∀ j : Fin n,
      fl_householderStoredPanelStep fp m n k
        (storedQRSignedStageVector hnm Ahat alpha k)
        (storedQRSignedStageBeta hnm Ahat alpha k)
        (Ahat k) i j =
        Ahat k i j := by
  intro k hk i hik j
  have hvzero : storedQRSignedStageVector hnm Ahat alpha k i = 0 := by
    unfold storedQRSignedStageVector
    simp only [dif_pos hk]
    exact
      householderTrailingActiveVector_zero_prefix m
        ⟨k, lt_of_lt_of_le hk hnm⟩
        (fun a => Ahat k a ⟨k, hk⟩) (alpha k) i hik
  by_cases hjlt : j.val < k
  · simp [fl_householderStoredPanelStep, hjlt]
  · have hraw :
        fl_householderApplyCompactPanel fp m n
            (storedQRSignedStageVector hnm Ahat alpha k)
            (storedQRSignedStageBeta hnm Ahat alpha k)
            (Ahat k) i j =
          Ahat k i j := by
      simpa [fl_householderApplyCompactPanel, fl_householderApplyCompact,
        hvzero, H19.Theorem19_13.fl_mul_zero_right] using hcopy (Ahat k i j)
    by_cases hjeq : j.val = k
    · have hnotBelow : ¬ k < i.val := Nat.not_lt.mpr (Nat.le_of_lt hik)
      simp [fl_householderStoredPanelStep, hjeq, hnotBelow, hraw]
    · simp [fl_householderStoredPanelStep, hjlt, hjeq, hraw]
/-- Theorem 20.7 support: sequence-level completed-row preservation for the
    signed stored-QR panel under exact subtract-by-zero copying. -/
theorem theorem20_7_completedA_preservation_of_signed_stage_subtractZeroExact_nat
    {m n : ℕ} (hnm : n ≤ m) (fp : FPModel)
    (Ahat : ℕ → Fin m → Fin n → ℝ) (alpha : ℕ → ℝ)
    (hcopy : H19.Theorem19_13.subtractZeroExact fp)
    (hStep : ∀ k, k < n →
      Ahat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (storedQRSignedStageVector hnm Ahat alpha k)
          (storedQRSignedStageBeta hnm Ahat alpha k)
          (Ahat k)) :
    ∀ i : Fin m, ∀ k : ℕ, k < n → i.val < k → ∀ j : Fin n,
      Ahat k i j = Ahat (i.val + 1) i j := by
  exact
    theorem20_7_completedA_preservation_of_stored_panel_step_row_preservation_nat
      fp (fun k => storedQRSignedStageVector hnm Ahat alpha k)
      (fun k => storedQRSignedStageBeta hnm Ahat alpha k)
      Ahat hStep
      (theorem20_7_signed_stage_stored_panel_row_preservation_of_subtractZeroExact_nat
        hnm fp Ahat alpha hcopy)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    one-based source column factor `j^2` in the perturbation bound for
    `Delta a_ij`.  Lean's `Fin` index `j` represents source column `j+1`. -/
noncomputable def theorem20_7_sourceColumnFactor {n : ℕ} (j : Fin n) : ℝ :=
  ((j.val + 1 : ℕ) : ℝ) ^ 2
/-- The Theorem 20.7 one-based source column factor is nonnegative. -/
theorem theorem20_7_sourceColumnFactor_nonneg {n : ℕ} (j : Fin n) :
    0 ≤ theorem20_7_sourceColumnFactor j := by
  dsimp [theorem20_7_sourceColumnFactor]
  exact sq_nonneg _
/-- The zero-based Cox--Higham column square is bounded by the one-based
    source column factor used in Higham Theorem 20.7. -/
theorem theorem20_7_zeroBasedColumnSq_le_sourceColumnFactor {n : ℕ}
    (j : Fin n) :
    (j.val : ℝ) ^ 2 ≤ theorem20_7_sourceColumnFactor j := by
  dsimp [theorem20_7_sourceColumnFactor]
  have hj0 : 0 ≤ (j.val : ℝ) := by
    exact_mod_cast Nat.zero_le j.val
  have hjle : (j.val : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ j.val
  exact pow_le_pow_left₀ hj0 hjle 2
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    source dimension factor `n^2` in the perturbation bound for `Delta b_i`. -/
noncomputable def theorem20_7_sourceDimensionFactor (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2
/-- The Theorem 20.7 source dimension factor is nonnegative. -/
theorem theorem20_7_sourceDimensionFactor_nonneg (n : ℕ) :
    0 ≤ theorem20_7_sourceDimensionFactor n := by
  dsimp [theorem20_7_sourceDimensionFactor]
  exact sq_nonneg _
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    concrete scalar compact slack used by the active-tail signed-stage route.

This is the per-stage scalar charged by the compact Householder coefficient
`fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m` against the natural
rowwise active-tail coefficient
`sqrt(m) * (sqrt(m) * rowwise_step_growth_factor^i + err)`. -/
noncomputable def theorem20_7_compactStepSlack
    (fp : FPModel) (m : ℕ) (err : ℝ) (i : ℕ) : ℝ :=
  (fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m) *
    (Real.sqrt (m : ℝ) *
      (Real.sqrt (m : ℝ) *
        H19.Theorem19_6.rowwise_step_growth_factor ^ i + err))
/-- The concrete compact slack is nonnegative under the usual roundoff guard
    and a nonnegative accumulated-error coefficient. -/
theorem theorem20_7_compactStepSlack_nonneg
    (fp : FPModel) (m : ℕ) (err : ℝ) (i : ℕ)
    (hmfp : gammaValid fp m) (herr : 0 ≤ err) :
    0 ≤ theorem20_7_compactStepSlack fp m err i := by
  have hcoeff : 0 ≤ fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m := by
    have hfac : 0 ≤ householderCompactNormBudgetCoeffFactor fp m :=
      householderCompactNormBudgetCoeffFactor_nonneg fp m hmfp
    have hu : 0 ≤ fp.u := fp.u_nonneg
    nlinarith
  have hinner :
      0 ≤ Real.sqrt (m : ℝ) *
            H19.Theorem19_6.rowwise_step_growth_factor ^ i + err := by
    exact
      add_nonneg
        (mul_nonneg (Real.sqrt_nonneg _)
          (pow_nonneg H19.Theorem19_6.rowwise_step_growth_factor_nonneg _))
        herr
  have hscale :
      0 ≤ Real.sqrt (m : ℝ) *
        (Real.sqrt (m : ℝ) *
          H19.Theorem19_6.rowwise_step_growth_factor ^ i + err) :=
    mul_nonneg (Real.sqrt_nonneg _) hinner
  simpa [theorem20_7_compactStepSlack] using mul_nonneg hcoeff hscale
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    combined exact-growth plus compact-update scalar factor for one active-tail
    signed stored-QR step. -/
noncomputable def theorem20_7_compactActiveStepFactor
    (fp : FPModel) (m : ℕ) : ℝ :=
  H19.Theorem19_6.active_row_growth_factor m +
    (fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m) *
      Real.sqrt (m : ℝ)
/-- The combined active-plus-compact step factor is nonnegative under the usual
    compact Householder roundoff guard. -/
theorem theorem20_7_compactActiveStepFactor_nonneg
    (fp : FPModel) (m : ℕ) (hmfp : gammaValid fp m) :
    0 ≤ theorem20_7_compactActiveStepFactor fp m := by
  have hactive : 0 ≤ H19.Theorem19_6.active_row_growth_factor m :=
    H19.Theorem19_6.active_row_growth_factor_nonneg m
  have hcoeff : 0 ≤ fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m := by
    have hfac : 0 ≤ householderCompactNormBudgetCoeffFactor fp m :=
      householderCompactNormBudgetCoeffFactor_nonneg fp m hmfp
    have hu : 0 ≤ fp.u := fp.u_nonneg
    nlinarith
  exact
    add_nonneg hactive (mul_nonneg hcoeff (Real.sqrt_nonneg _))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.7 support:
    honest larger active-tail scalar horizon after the printed rowwise horizon
    is not large enough for the current compact active-step factor.

The term `err` is grown with the same combined factor, avoiding the false
constant-error recurrence for the printed rowwise factor. -/
noncomputable def theorem20_7_compactActiveHorizon
    (fp : FPModel) (m : ℕ) (err : ℝ) (i : ℕ) : ℝ :=
  (Real.sqrt (m : ℝ) + err) *
    theorem20_7_compactActiveStepFactor fp m ^ i
/-- Compact-step slack associated with the larger compact-active horizon. -/
noncomputable def theorem20_7_compactActiveHorizonStepSlack
    (fp : FPModel) (m : ℕ) (err : ℝ) (i : ℕ) : ℝ :=
  (fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m) *
    Real.sqrt (m : ℝ) *
      theorem20_7_compactActiveHorizon fp m err i
/-- The compact-active horizon is nonnegative under the standard roundoff guard
    and nonnegative accumulated-error coefficient. -/
theorem theorem20_7_compactActiveHorizon_nonneg
    (fp : FPModel) (m : ℕ) (err : ℝ) (i : ℕ)
    (hmfp : gammaValid fp m) (herr : 0 ≤ err) :
    0 ≤ theorem20_7_compactActiveHorizon fp m err i := by
  have hbase :
      0 ≤ Real.sqrt (m : ℝ) + err :=
    add_nonneg (Real.sqrt_nonneg _) herr
  have hfactor :
      0 ≤ theorem20_7_compactActiveStepFactor fp m :=
    theorem20_7_compactActiveStepFactor_nonneg fp m hmfp
  exact
    mul_nonneg hbase (pow_nonneg hfactor _)
/-- The larger compact-active horizon has the exact one-step recurrence needed
    by the active-tail compact-budget route. -/
theorem theorem20_7_compactActiveHorizonStepSlack_recurrence_nat
    {m n : ℕ} (fp : FPModel) (err : ℝ) :
    ∀ i : Fin m, i.val + 1 < n →
      H19.Theorem19_6.active_row_growth_factor m *
            theorem20_7_compactActiveHorizon fp m err i.val +
          theorem20_7_compactActiveHorizonStepSlack fp m err i.val ≤
        theorem20_7_compactActiveHorizon fp m err (i.val + 1) := by
  intro i _hi
  have hleft :
      H19.Theorem19_6.active_row_growth_factor m *
            theorem20_7_compactActiveHorizon fp m err i.val +
          theorem20_7_compactActiveHorizonStepSlack fp m err i.val =
        theorem20_7_compactActiveStepFactor fp m *
          theorem20_7_compactActiveHorizon fp m err i.val := by
    simp [theorem20_7_compactActiveHorizonStepSlack,
      theorem20_7_compactActiveStepFactor]
    ring
  rw [hleft]
  dsimp [theorem20_7_compactActiveHorizon]
  rw [pow_succ]
  ring_nf
  exact le_rfl
/-- Theorem 20.7 support: the concrete stored-Householder QR matrix sequence
    has exact prefix lower zeros at every stage. -/
theorem theorem20_7_storedHouseholderQRMatrixSeq_prefix_lower_zero_nat
    {m n : ℕ} (fp : FPModel) (hnm : n ≤ m)
    (A : Fin m → Fin n → ℝ) :
    ∀ t, t ≤ n → ∀ (i : Fin m) (j : Fin n),
      j.val < t → j.val < i.val →
        storedHouseholderQRMatrixSeq fp hnm A t i j = 0 := by
  let Ahat : ℕ → Fin m → Fin n → ℝ := storedHouseholderQRMatrixSeq fp hnm A
  let alpha : ℕ → ℝ := storedHouseholderQRAlphaSeq fp hnm A
  have hStep : ∀ k, k < n →
      Ahat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (storedQRSignedStageVector hnm Ahat alpha k)
          (storedQRSignedStageBeta hnm Ahat alpha k)
          (Ahat k) := by
    intro k hk
    simpa [Ahat, alpha, storedQRSignedStageVector,
        storedQRSignedStageBeta, hk] using
      storedHouseholderQRMatrixSeq_succ_of_lt fp hnm A k hk
  have hprefix :=
    fl_householderStoredPanel_sequence_prefix_lower_zero
      fp
      (fun k => storedQRSignedStageVector hnm Ahat alpha k)
      (fun k => storedQRSignedStageBeta hnm Ahat alpha k)
      Ahat hStep
  simpa [Ahat] using hprefix
/-- Theorem 20.7 support: local previous-prefix diagonal nonzero follows from
    the corresponding leading-block diagonal nonzero hypothesis. -/
theorem theorem20_7_storedHouseholderQRMatrixSeq_diagPrev_of_diagLead_nat
    {m n : ℕ} (fp : FPModel) (hnm : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hdiagLead : ∀ t (ht : t < n) (r : Fin (t + 1)),
      storedHouseholderQRMatrixSeq fp hnm A t
        (qrLeadingRow m t
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le ht hnm)) r)
        (qrLeadingColumn n t ht r) ≠ 0) :
    ∀ t (ht : t < n) (r : Fin t),
      storedHouseholderQRMatrixSeq fp hnm A t
        (qrPrefixRow m t (le_of_lt (lt_of_lt_of_le ht hnm)) r)
        (qrPreviousColumn n t ht r) ≠ 0 := by
  intro t ht r
  simpa [qrPrefixRow, qrPreviousColumn, qrLeadingRow, qrLeadingColumn] using
    hdiagLead t ht (Fin.castSucc r)
/-- Theorem 20.7 support: leading-block diagonal nonzero follows from
    completed-step diagonal nonzero plus the current pivot diagonal facts. -/
theorem theorem20_7_storedHouseholderQRMatrixSeq_diagLead_of_step_diag_and_current_diag_nat
    {m n : ℕ} (fp : FPModel) (hnm : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hstepDiag : ∀ k (hk : k < n),
      storedHouseholderQRMatrixSeq fp hnm A (k + 1)
        ⟨k, lt_of_lt_of_le hk hnm⟩ ⟨k, hk⟩ ≠ 0)
    (hcurrentDiag : ∀ k (hk : k < n),
      storedHouseholderQRMatrixSeq fp hnm A k
        ⟨k, lt_of_lt_of_le hk hnm⟩ ⟨k, hk⟩ ≠ 0) :
    ∀ t (ht : t < n) (r : Fin (t + 1)),
      storedHouseholderQRMatrixSeq fp hnm A t
        (qrLeadingRow m t
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le ht hnm)) r)
        (qrLeadingColumn n t ht r) ≠ 0 := by
  let Ahat : ℕ → Fin m → Fin n → ℝ := storedHouseholderQRMatrixSeq fp hnm A
  let alpha : ℕ → ℝ := storedHouseholderQRAlphaSeq fp hnm A
  have hStep : ∀ k, k < n →
      Ahat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (storedQRSignedStageVector hnm Ahat alpha k)
          (storedQRSignedStageBeta hnm Ahat alpha k)
          (Ahat k) := by
    intro k hk
    simpa [Ahat, alpha, storedQRSignedStageVector,
        storedQRSignedStageBeta, hk] using
      storedHouseholderQRMatrixSeq_succ_of_lt fp hnm A k hk
  have hstepPanel : ∀ k (hk : k < n),
      fl_householderStoredPanelStep fp m n k
          (storedQRSignedStageVector hnm Ahat alpha k)
          (storedQRSignedStageBeta hnm Ahat alpha k)
          (Ahat k)
          ⟨k, lt_of_lt_of_le hk hnm⟩ ⟨k, hk⟩ ≠ 0 := by
    intro k hk
    have hpoint := congrFun
      (congrFun (hStep k hk) ⟨k, lt_of_lt_of_le hk hnm⟩) ⟨k, hk⟩
    rw [← hpoint]
    exact hstepDiag k hk
  have hprefixDiag :=
    fl_householderStoredPanel_sequence_prefix_diag_nonzero_of_step_diag_nonzero
      fp hnm
      (fun k => storedQRSignedStageVector hnm Ahat alpha k)
      (fun k => storedQRSignedStageBeta hnm Ahat alpha k)
      Ahat hStep hstepPanel
  intro t ht r
  by_cases hrt : r.val < t
  · have hprev :=
      hprefixDiag t (Nat.le_of_lt ht) ⟨r.val, hrt⟩
    simpa [Ahat, qrLeadingRow, qrLeadingColumn] using hprev
  · have hr_eq : r.val = t := by omega
    have hr_last : r = ⟨t, Nat.lt_succ_self t⟩ := Fin.ext hr_eq
    subst r
    simpa [Ahat, qrLeadingRow, qrLeadingColumn] using hcurrentDiag t ht
/-- Theorem 20.7 support: the stored QR prefix lower-zero invariant plus a
    nonsingular current leading block supplies the current pivot diagonal. -/
theorem theorem20_7_storedHouseholderQRMatrixSeq_current_diag_nonzero_of_leadingBlock_det_ne_zero_nat
    {m n : ℕ} (fp : FPModel) (hnm : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (storedHouseholderQRMatrixSeq fp hnm A k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hnm)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0) :
    ∀ k (hk : k < n),
      storedHouseholderQRMatrixSeq fp hnm A k
        ⟨k, lt_of_lt_of_le hk hnm⟩ ⟨k, hk⟩ ≠ 0 := by
  let Ahat : ℕ → Fin m → Fin n → ℝ := storedHouseholderQRMatrixSeq fp hnm A
  let alpha : ℕ → ℝ := storedHouseholderQRAlphaSeq fp hnm A
  have hStep : ∀ k (hk : k < n),
      Ahat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hnm⟩
            (fun a => Ahat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hnm⟩
              (fun a => Ahat k a ⟨k, hk⟩) (alpha k)))
          (Ahat k) := by
    intro k hk
    simpa [Ahat, alpha, storedQRSignedStageVector,
        storedQRSignedStageBeta, hk] using
      storedHouseholderQRMatrixSeq_succ_of_lt fp hnm A k hk
  have hdetLead' : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (Ahat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hnm)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
    intro k hk
    simpa [Ahat] using hdetLead k hk
  simpa [Ahat] using
    fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero
      fp hnm Ahat alpha hStep hdetLead'
/-- Higham, 2nd ed., Chapter 20, equation (20.23), feasibility part:
    `B x = d` for the equality-constrained least-squares problem. -/
def LSEFeasible {p n : ℕ} (B : Fin p → Fin n → ℝ)
    (d : Fin p → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i : Fin p, rectMatMulVec B x i = d i
/-- Higham, 2nd ed., Chapter 20, equation (20.23):
    `x` solves `min ||b - A x||_2` subject to `B x = d`.

    The shared objective uses the squared norm and residual sign `A x - b`;
    both are equivalent to the displayed source objective for minimizers. -/
def IsLSEMinimizer {m n p : ℕ} (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (B : Fin p → Fin n → ℝ)
    (d : Fin p → ℝ) (x : Fin n → ℝ) : Prop :=
  LSEFeasible B d x ∧
  ∀ y : Fin n → ℝ, LSEFeasible B d y → lsObjective A b x ≤ lsObjective A b y
/-- With no constraint rows, equality-constrained least squares is ordinary
    least squares.  This bridge is useful for the `p = 0` boundary of the
    Chapter 20 LSE results. -/
theorem isLSEMinimizer_empty_constraints_iff {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin 0 → Fin n → ℝ) (d : Fin 0 → ℝ) (x : Fin n → ℝ) :
    IsLSEMinimizer A b B d x ↔ IsLeastSquaresMinimizer A b x := by
  constructor
  · intro hx y
    exact hx.2 y (fun i => Fin.elim0 i)
  · intro hx
    refine ⟨(fun i => Fin.elim0 i), ?_⟩
    intro y _hy
    exact hx y
/-- Feasibility `Bx=d` gives the elementary Frobenius bound
    `||d||₂ <= ||B||_F ||x||₂`. -/
theorem LSEFeasible.vecNorm2_rhs_le_frobNormRect_mul {p n : ℕ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ} {x : Fin n → ℝ}
    (hx : LSEFeasible B d x) :
    vecNorm2 d ≤ frobNormRect B * vecNorm2 x := by
  have hd_eq : d = rectMatMulVec B x := by
    ext i
    exact (hx i).symm
  rw [hd_eq]
  exact vecNorm2_rectMatMulVec_le_frobNormRect_mul B x
/-- An exact LSE minimizer's constraint right-hand side is bounded by the
    source constraint matrix acting on the minimizer. -/
theorem IsLSEMinimizer.vecNorm2_constraint_rhs_le_frobNormRect_mul {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ} {x : Fin n → ℝ}
    (hx : IsLSEMinimizer A b B d x) :
    vecNorm2 d ≤ frobNormRect B * vecNorm2 x :=
  hx.1.vecNorm2_rhs_le_frobNormRect_mul

-- ------------------------------------------------------------
-- §20.9.1  Perturbation-theory scalar budget support
-- ------------------------------------------------------------
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    source projector `P = I - B^+ B` used in the LSE perturbation bound.

    The matrix `Bplus` is an explicit supplied table for the source
    pseudo-inverse `B^+`; this definition does not assert the Moore--Penrose
    equations. -/
noncomputable def theorem20_8Projection {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => idMatrix n i j - rectMatMul Bplus B i j
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    if the supplied `Bplus` is a right inverse of `B`, then the source
    projector `P = I - B^+ B` maps every vector into the constraint nullspace. -/
theorem theorem20_8Projection_constraint_zero {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p) :
    rectMatMul B (theorem20_8Projection B Bplus) =
      (fun _i _j => 0) := by
  calc
    rectMatMul B (theorem20_8Projection B Bplus)
        = fun i j =>
            rectMatMul B (idMatrix n) i j -
              rectMatMul B (rectMatMul Bplus B) i j := by
            ext i j
            unfold theorem20_8Projection rectMatMul
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = fun i j =>
          B i j - rectMatMul (rectMatMul B Bplus) B i j := by
            ext i j
            rw [rectMatMul_id_right]
            rw [rectMatMul_assoc]
    _ = fun i j => B i j - rectMatMul (idMatrix p) B i j := by
            rw [hright]
    _ = fun i j => B i j - B i j := by
            rw [rectMatMul_id_left]
    _ = fun _i _j => 0 := by
            ext i j
            ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    vector form of `B(I - B^+B) = 0`. -/
theorem theorem20_8Projection_constraint_vec_zero {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (x : Fin n → ℝ) :
    rectMatMulVec B (rectMatMulVec (theorem20_8Projection B Bplus) x) =
      (fun _i => 0) := by
  rw [← rectMatMulVec_rectMatMul B (theorem20_8Projection B Bplus) x]
  rw [theorem20_8Projection_constraint_zero B Bplus hright]
  ext i
  simp [rectMatMulVec]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the projector `P = I - B^+B` fixes every vector in the nullspace of `B`. -/
theorem theorem20_8Projection_apply_nullspace {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (x : Fin n → ℝ)
    (hBx : rectMatMulVec B x = (fun _i => 0)) :
    rectMatMulVec (theorem20_8Projection B Bplus) x = x := by
  ext i
  calc
    rectMatMulVec (theorem20_8Projection B Bplus) x i
        = rectMatMulVec (idMatrix n) x i -
            rectMatMulVec (rectMatMul Bplus B) x i := by
            unfold theorem20_8Projection rectMatMulVec
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = x i - rectMatMulVec Bplus (rectMatMulVec B x) i := by
            rw [rectMatMulVec_idMatrix]
            rw [rectMatMulVec_rectMatMul]
    _ = x i := by
            rw [hBx]
            simp [rectMatMulVec]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    vector idempotence of the nullspace projector `P = I - B^+B`. -/
theorem theorem20_8Projection_vec_idempotent {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (x : Fin n → ℝ) :
    rectMatMulVec (theorem20_8Projection B Bplus)
        (rectMatMulVec (theorem20_8Projection B Bplus) x) =
      rectMatMulVec (theorem20_8Projection B Bplus) x := by
  exact
    theorem20_8Projection_apply_nullspace B Bplus
      (rectMatMulVec (theorem20_8Projection B Bplus) x)
      (theorem20_8Projection_constraint_vec_zero B Bplus hright x)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    the source product `A P`, where `P = I - B^+ B`. -/
noncomputable def theorem20_8AP {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) : Fin m → Fin n → ℝ :=
  rectMatMul A (theorem20_8Projection B Bplus)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    on vectors satisfying the equality constraint's homogeneous equation
    `B x = 0`, the source product `A P` acts as `A`. -/
theorem theorem20_8AP_apply_nullspace {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (x : Fin n → ℝ)
    (hBx : rectMatMulVec B x = (fun _i => 0)) :
    rectMatMulVec (theorem20_8AP A B Bplus) x =
      rectMatMulVec A x := by
  rw [theorem20_8AP, rectMatMulVec_rectMatMul]
  rw [theorem20_8Projection_apply_nullspace B Bplus x hBx]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the difference of two feasible LSE points lies in the nullspace of `B`. -/
theorem theorem20_8_feasible_difference_constraint_zero {n p : ℕ}
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x) (hy : LSEFeasible B d y) :
    rectMatMulVec B (fun j => x j - y j) = (fun _i => 0) := by
  rw [rectMatMulVec_sub]
  ext i
  rw [hx i, hy i]
  simp
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    `P = I - B^+B` fixes feasible differences. -/
theorem theorem20_8Projection_apply_feasible_difference {n p : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x) (hy : LSEFeasible B d y) :
    rectMatMulVec (theorem20_8Projection B Bplus) (fun j => x j - y j) =
      (fun j => x j - y j) :=
  theorem20_8Projection_apply_nullspace B Bplus (fun j => x j - y j)
    (theorem20_8_feasible_difference_constraint_zero B d x y hx hy)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    on feasible differences, `A P` acts exactly as `A`. -/
theorem theorem20_8AP_apply_feasible_difference {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ)
    (d : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x) (hy : LSEFeasible B d y) :
    rectMatMulVec (theorem20_8AP A B Bplus) (fun j => x j - y j) =
      rectMatMulVec A (fun j => x j - y j) :=
  theorem20_8AP_apply_nullspace A B Bplus (fun j => x j - y j)
    (theorem20_8_feasible_difference_constraint_zero B d x y hx hy)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    adding a projected direction `P z` to a feasible point preserves the
    equality constraint. -/
theorem theorem20_8Projection_feasible_step {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d : Fin p → ℝ) (x0 z : Fin n → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hx0 : LSEFeasible B d x0) :
    LSEFeasible B d
      (fun j => x0 j + rectMatMulVec (theorem20_8Projection B Bplus) z j) := by
  intro i
  have hstep :=
    theorem20_8Projection_constraint_vec_zero B Bplus hright z
  rw [rectMatMulVec_add]
  change
    rectMatMulVec B x0 i +
        rectMatMulVec B (rectMatMulVec (theorem20_8Projection B Bplus) z) i =
      d i
  have hstep_i := congrFun hstep i
  rw [hx0 i, hstep_i]
  simp
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    exact action of `A` on a feasible nullspace step `x0 + P z`. -/
theorem theorem20_8AP_feasible_step_action {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ)
    (x0 z : Fin n → ℝ) :
    rectMatMulVec A
        (fun j => x0 j + rectMatMulVec (theorem20_8Projection B Bplus) z j) =
      fun i =>
        rectMatMulVec A x0 i +
          rectMatMulVec (theorem20_8AP A B Bplus) z i := by
  rw [rectMatMulVec_add]
  rw [theorem20_8AP, rectMatMulVec_rectMatMul]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    residual identity for the nullspace parametrization `x = x0 + P z`.

    The reduced unconstrained least-squares right-hand side is `b - A x0`,
    matching the source transformation of the feasible LSE problem (20.23). -/
theorem theorem20_8AP_feasible_step_residual {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (x0 z : Fin n → ℝ) :
    lsResidual A b
        (fun j => x0 j + rectMatMulVec (theorem20_8Projection B Bplus) z j) =
      lsResidual (theorem20_8AP A B Bplus)
        (fun i => b i - rectMatMulVec A x0 i) z := by
  ext i
  unfold lsResidual
  have hact := congrFun (theorem20_8AP_feasible_step_action A B Bplus x0 z) i
  rw [hact]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    objective identity for the nullspace parametrization of the LSE problem.

    This is the exact algebraic reduction of feasible steps in (20.23) to the
    unconstrained least-squares objective with matrix `AP`. -/
theorem theorem20_8AP_feasible_step_objective {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (x0 z : Fin n → ℝ) :
    lsObjective A b
        (fun j => x0 j + rectMatMulVec (theorem20_8Projection B Bplus) z j) =
      lsObjective (theorem20_8AP A B Bplus)
        (fun i => b i - rectMatMulVec A x0 i) z := by
  unfold lsObjective
  rw [theorem20_8AP_feasible_step_residual A b B Bplus x0 z]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    if `x0` and `y` are feasible for the same equality constraint, then the
    nullspace projector reconstructs `y` from the feasible base point `x0`. -/
theorem theorem20_8Projection_feasible_difference_decomp {n p : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d : Fin p → ℝ) (x0 y : Fin n → ℝ)
    (hx0 : LSEFeasible B d x0) (hy : LSEFeasible B d y) :
    (fun j => x0 j +
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k => y k - x0 k) j) =
      y := by
  have hproj :=
    theorem20_8Projection_apply_feasible_difference B Bplus d y x0 hy hx0
  ext j
  have hj := congrFun hproj j
  rw [hj]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    an exact minimizer of the reduced unconstrained problem in the nullspace
    variable lifts to an exact LSE minimizer. -/
theorem theorem20_8AP_unconstrained_minimizer_lifts {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d : Fin p → ℝ) (x0 z : Fin n → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hx0 : LSEFeasible B d x0)
    (hmin : IsLeastSquaresMinimizer (theorem20_8AP A B Bplus)
      (fun i => b i - rectMatMulVec A x0 i) z) :
    IsLSEMinimizer A b B d
      (fun j => x0 j + rectMatMulVec (theorem20_8Projection B Bplus) z j) := by
  constructor
  · exact theorem20_8Projection_feasible_step B Bplus d x0 z hright hx0
  · intro y hy
    calc
      lsObjective A b
          (fun j => x0 j + rectMatMulVec (theorem20_8Projection B Bplus) z j)
          =
        lsObjective (theorem20_8AP A B Bplus)
          (fun i => b i - rectMatMulVec A x0 i) z := by
          exact theorem20_8AP_feasible_step_objective A b B Bplus x0 z
      _ ≤ lsObjective (theorem20_8AP A B Bplus)
            (fun i => b i - rectMatMulVec A x0 i)
            (fun j => y j - x0 j) :=
          hmin (fun j => y j - x0 j)
      _ = lsObjective A b
            (fun j => x0 j +
              rectMatMulVec (theorem20_8Projection B Bplus)
                (fun k => y k - x0 k) j) := by
          exact (theorem20_8AP_feasible_step_objective A b B Bplus
            x0 (fun j => y j - x0 j)).symm
      _ = lsObjective A b y := by
          rw [theorem20_8Projection_feasible_difference_decomp
            B Bplus d x0 y hx0 hy]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    every exact LSE minimizer gives an exact minimizer of the reduced
    unconstrained problem when written relative to a feasible base point. -/
theorem theorem20_8AP_unconstrained_minimizer_of_lse_minimizer {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d : Fin p → ℝ) (x0 x : Fin n → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hx0 : LSEFeasible B d x0)
    (hx : IsLSEMinimizer A b B d x) :
    IsLeastSquaresMinimizer (theorem20_8AP A B Bplus)
      (fun i => b i - rectMatMulVec A x0 i)
      (fun j => x j - x0 j) := by
  intro z
  have hstep :
      LSEFeasible B d
        (fun j => x0 j + rectMatMulVec (theorem20_8Projection B Bplus) z j) :=
    theorem20_8Projection_feasible_step B Bplus d x0 z hright hx0
  have hx_feas : LSEFeasible B d x := hx.1
  have hle := hx.2
    (fun j => x0 j + rectMatMulVec (theorem20_8Projection B Bplus) z j) hstep
  calc
    lsObjective (theorem20_8AP A B Bplus)
        (fun i => b i - rectMatMulVec A x0 i)
        (fun j => x j - x0 j)
        =
      lsObjective A b
        (fun j => x0 j +
          rectMatMulVec (theorem20_8Projection B Bplus)
            (fun k => x k - x0 k) j) := by
        exact (theorem20_8AP_feasible_step_objective A b B Bplus
          x0 (fun j => x j - x0 j)).symm
    _ = lsObjective A b x := by
        rw [theorem20_8Projection_feasible_difference_decomp
          B Bplus d x0 x hx0 hx_feas]
    _ ≤ lsObjective A b
          (fun j => x0 j + rectMatMulVec (theorem20_8Projection B Bplus) z j) :=
        hle
    _ = lsObjective (theorem20_8AP A B Bplus)
          (fun i => b i - rectMatMulVec A x0 i) z := by
        exact theorem20_8AP_feasible_step_objective A b B Bplus x0 z
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    a minimizer of the perturbed equality-constrained problem gives an exact
    minimizer of the perturbed reduced `AP` least-squares problem, relative to
    a perturbed feasible base point. -/
theorem theorem20_8AP_perturbed_unconstrained_minimizer_of_lse_minimizer
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bpertplus : Fin n → Fin p → ℝ)
    (d Deltad : Fin p → ℝ) (x0 y : Fin n → ℝ)
    (hright :
      rectMatMul (fun i j => B i j + DeltaB i j) Bpertplus =
        idMatrix p)
    (hx0 : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) x0)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    IsLeastSquaresMinimizer
      (theorem20_8AP (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j) Bpertplus)
      (fun i =>
        b i + Deltab i -
          rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
      (fun j => y j - x0 j) :=
  _root_.NumStability.theorem20_8AP_unconstrained_minimizer_of_lse_minimizer
    (fun i j => A i j + DeltaA i j) (fun i => b i + Deltab i)
    (fun i j => B i j + DeltaB i j) Bpertplus
    (fun i => d i + Deltad i) x0 y hright hx0 hy
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    an exact LSE minimizer induces an exact unconstrained least-squares
    minimizer in any supplied coordinate basis for homogeneous feasible
    directions. -/
theorem IsLSEMinimizer.reduced_nullspace_minimizer {m n p q : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (N : Fin n → Fin q → ℝ)
    (hmin : IsLSEMinimizer A b B d x)
    (hN : rectMatMul B N = (fun _i : Fin p => fun _j : Fin q => 0)) :
    IsLeastSquaresMinimizer (rectMatMul A N) (lsResidualHigham A b x)
      (0 : Fin q → ℝ) := by
  intro z
  let candidate : Fin n → ℝ := fun j => x j + rectMatMulVec N z j
  have hNz : rectMatMulVec B (rectMatMulVec N z) =
      (fun _i : Fin p => 0) := by
    rw [← rectMatMulVec_rectMatMul B N z, hN]
    ext i
    simp [rectMatMulVec]
  have hfeas : LSEFeasible B d candidate := by
    intro i
    have hzi := congrFun hNz i
    change rectMatMulVec B (fun j => x j + rectMatMulVec N z j) i = d i
    rw [rectMatMulVec_add]
    change rectMatMulVec B x i +
        rectMatMulVec B (rectMatMulVec N z) i = d i
    rw [hmin.1 i, hzi]
    simp
  have hle : lsObjective A b x ≤ lsObjective A b candidate :=
    hmin.2 candidate hfeas
  have hobj0 :
      lsObjective (rectMatMul A N) (lsResidualHigham A b x)
          (0 : Fin q → ℝ) =
        lsObjective A b x := by
    unfold lsObjective lsResidual lsResidualHigham
    apply congrArg vecNorm2Sq
    ext i
    simp [rectMatMulVec]
  have hobjz :
      lsObjective A b candidate =
        lsObjective (rectMatMul A N) (lsResidualHigham A b x) z := by
    unfold lsObjective lsResidual lsResidualHigham
    apply congrArg vecNorm2Sq
    ext i
    rw [rectMatMulVec_add, rectMatMulVec_rectMatMul]
    ring
  calc
    lsObjective (rectMatMul A N) (lsResidualHigham A b x)
        (0 : Fin q → ℝ) = lsObjective A b x := hobj0
    _ ≤ lsObjective A b candidate := hle
    _ = lsObjective (rectMatMul A N) (lsResidualHigham A b x) z := hobjz
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    applying `P = I - B^+B` to a vector with a known constraint residual
    subtracts the supplied `B^+` correction. -/
theorem theorem20_8Projection_apply_of_constraint {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (v : Fin n → ℝ) (e : Fin p → ℝ)
    (hBv : rectMatMulVec B v = e) :
    rectMatMulVec (theorem20_8Projection B Bplus) v =
      fun j => v j - rectMatMulVec Bplus e j := by
  ext j
  calc
    rectMatMulVec (theorem20_8Projection B Bplus) v j
        = rectMatMulVec (idMatrix n) v j -
            rectMatMulVec (rectMatMul Bplus B) v j := by
            unfold theorem20_8Projection rectMatMulVec
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = v j - rectMatMulVec Bplus (rectMatMulVec B v) j := by
            rw [rectMatMulVec_idMatrix]
            rw [rectMatMulVec_rectMatMul]
    _ = v j - rectMatMulVec Bplus e j := by
            rw [hBv]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    if `x` is feasible for `(B,d)` and `y` is feasible for the perturbed
    constraint `(B + DeltaB)y = d + Deltad`, then the solution difference has
    constraint defect `Deltad - DeltaB*y` for the original constraint matrix. -/
theorem theorem20_8_perturbed_feasible_difference_constraint {n p : ℕ}
    (B DeltaB : Fin p → Fin n → ℝ) (d Deltad : Fin p → ℝ)
    (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    rectMatMulVec B (fun j => y j - x j) =
      fun i => Deltad i - rectMatMulVec DeltaB y i := by
  ext i
  have hdiff := congrFun (rectMatMulVec_sub B y x) i
  have hy_add :
      rectMatMulVec B y i + rectMatMulVec DeltaB y i = d i + Deltad i := by
    have hmat := congrFun (rectMatMulVec_mat_add B DeltaB y) i
    have hyi := hy i
    rw [hmat] at hyi
    exact hyi
  rw [hdiff, hx i]
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    projection of a difference between an original feasible point and a
    perturbed feasible point. -/
theorem theorem20_8Projection_apply_perturbed_feasible_difference {n p : ℕ}
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    rectMatMulVec (theorem20_8Projection B Bplus) (fun j => y j - x j) =
      fun j =>
        (y j - x j) -
          rectMatMulVec Bplus (fun i => Deltad i - rectMatMulVec DeltaB y i) j :=
  theorem20_8Projection_apply_of_constraint B Bplus (fun j => y j - x j)
    (fun i => Deltad i - rectMatMulVec DeltaB y i)
    (theorem20_8_perturbed_feasible_difference_constraint
      B DeltaB d Deltad x y hx hy)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the difference between an original feasible point and a perturbed feasible
    point splits into a nullspace-projected part plus the supplied `B^+`
    correction for the constraint defect. -/
theorem theorem20_8_perturbed_feasible_difference_decomp {n p : ℕ}
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    (fun j => y j - x j) =
      fun j =>
        rectMatMulVec (theorem20_8Projection B Bplus) (fun k => y k - x k) j +
          rectMatMulVec Bplus (fun i => Deltad i - rectMatMulVec DeltaB y i) j := by
  have hproj :=
    theorem20_8Projection_apply_perturbed_feasible_difference
      B DeltaB Bplus d Deltad x y hx hy
  ext j
  have hj := congrFun hproj j
  rw [hj]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    point form of the perturbed-feasible decomposition. -/
theorem theorem20_8_perturbed_feasible_point_decomp {n p : ℕ}
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    y =
      fun j =>
        x j +
          rectMatMulVec (theorem20_8Projection B Bplus) (fun k => y k - x k) j +
          rectMatMulVec Bplus (fun i => Deltad i - rectMatMulVec DeltaB y i) j := by
  have hdecomp :=
    theorem20_8_perturbed_feasible_difference_decomp
      B DeltaB Bplus d Deltad x y hx hy
  ext j
  have hj := congrFun hdecomp j
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    action of `A` on a perturbed feasible point after the source nullspace
    decomposition.  The last term is the explicit correction caused by the
    perturbed constraint defect `Deltad - DeltaB*y`. -/
theorem theorem20_8_perturbed_feasible_point_action_decomp {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    rectMatMulVec A y =
      fun i =>
        rectMatMulVec A x i +
          rectMatMulVec (theorem20_8AP A B Bplus) (fun k => y k - x k) i +
          rectMatMulVec A
            (rectMatMulVec Bplus
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i := by
  have hpoint :=
    theorem20_8_perturbed_feasible_point_decomp
      B DeltaB Bplus d Deltad x y hx hy
  calc
    rectMatMulVec A y =
        rectMatMulVec A
          (fun j =>
            x j + rectMatMulVec (theorem20_8Projection B Bplus)
              (fun k => y k - x k) j +
              rectMatMulVec Bplus
                (fun l => Deltad l - rectMatMulVec DeltaB y l) j) := by
          conv_lhs => rw [hpoint]
    _ = fun i =>
          rectMatMulVec A
              (fun j =>
                x j + rectMatMulVec (theorem20_8Projection B Bplus)
                  (fun k => y k - x k) j) i +
            rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l => Deltad l - rectMatMulVec DeltaB y l)) i := by
          rw [rectMatMulVec_add]
    _ = fun i =>
          (rectMatMulVec A x i +
            rectMatMulVec (theorem20_8AP A B Bplus) (fun k => y k - x k) i) +
            rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l => Deltad l - rectMatMulVec DeltaB y l)) i := by
          rw [theorem20_8AP_feasible_step_action A B Bplus x
            (fun k => y k - x k)]
    _ = fun i =>
          rectMatMulVec A x i +
            rectMatMulVec (theorem20_8AP A B Bplus) (fun k => y k - x k) i +
            rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l => Deltad l - rectMatMulVec DeltaB y l)) i := by
          ext i
          ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    projected `AP` step recovered from the action of `A` on a perturbed
    feasible point and the explicit right-inverse constraint correction. -/
theorem theorem20_8_AP_difference_eq_action_minus_constraint_correction {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    rectMatMulVec (theorem20_8AP A B Bplus) (fun k => y k - x k) =
      fun i =>
        rectMatMulVec A y i - rectMatMulVec A x i -
          rectMatMulVec A
            (rectMatMulVec Bplus
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i := by
  have haction :=
    theorem20_8_perturbed_feasible_point_action_decomp
      A B DeltaB Bplus d Deltad x y hx hy
  ext i
  have hi := congrFun haction i
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    residual decomposition for a point feasible for the perturbed constraint.

    The reduced `AP` residual is separated from the three explicit perturbation
    terms that must be bounded in the first-order LSE perturbation proof:
    `A*Bplus*(Deltad-DeltaB*y)`, `DeltaA*y`, and `Deltab`. -/
theorem theorem20_8_perturbed_feasible_residual_decomp {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    lsResidual (fun i j => A i j + DeltaA i j) (fun i => b i + Deltab i) y =
      fun i =>
        lsResidual (theorem20_8AP A B Bplus)
          (fun i => b i - rectMatMulVec A x i) (fun j => y j - x j) i +
          rectMatMulVec A
            (rectMatMulVec Bplus
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i +
          rectMatMulVec DeltaA y i -
          Deltab i := by
  ext i
  unfold lsResidual
  have hmat := congrFun (rectMatMulVec_mat_add A DeltaA y) i
  have hA :=
    congrFun
      (theorem20_8_perturbed_feasible_point_action_decomp
        A B DeltaB Bplus d Deltad x y hx hy) i
  rw [hmat, hA]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    solving the perturbed-residual decomposition for the reduced `AP`
    difference.  The perturbed residual is kept explicit, so this does not
    assume the reduced least-squares/Wedin forcing equation. -/
theorem theorem20_8_AP_difference_eq_of_perturbed_residual_eq {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ) (rpert : Fin m → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidual (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rpert) :
    rectMatMulVec (theorem20_8AP A B Bplus) (fun k => y k - x k) =
      fun i =>
        rpert i + (b i - rectMatMulVec A x i) -
          rectMatMulVec A
            (rectMatMulVec Bplus
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i -
          rectMatMulVec DeltaA y i + Deltab i := by
  have hdecomp :=
    theorem20_8_perturbed_feasible_residual_decomp
      A DeltaA b Deltab B DeltaB Bplus d Deltad x y hx hy
  ext i
  have hdecomp_i := congrFun hdecomp i
  have hres_i := congrFun hres i
  unfold lsResidual at hdecomp_i hres_i
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-sign version of `theorem20_8_AP_difference_eq_of_perturbed_residual_eq`,
    using Higham's residual convention `b - A*x`. -/
theorem theorem20_8_AP_difference_eq_of_perturbed_higham_residual_eq {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ) (rHigh : Fin m → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh) :
    rectMatMulVec (theorem20_8AP A B Bplus) (fun k => y k - x k) =
      fun i =>
        (b i - rectMatMulVec A x i) - rHigh i -
          rectMatMulVec A
            (rectMatMulVec Bplus
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i -
          rectMatMulVec DeltaA y i + Deltab i := by
  have hdecomp :=
    theorem20_8_perturbed_feasible_residual_decomp
      A DeltaA b Deltab B DeltaB Bplus d Deltad x y hx hy
  ext i
  have hdecomp_i := congrFun hdecomp i
  have hres_i := congrFun hres i
  unfold lsResidual at hdecomp_i
  unfold lsResidualHigham at hres_i
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    same-source-residual specialization of the Higham-sign reduced `AP`
    difference identity.  With perturbations written as `A + DeltaA` and
    `b + Deltab`, matching source and perturbed Higham residuals leave the
    reduced forcing `Deltab - DeltaA*y`, minus the constraint correction. -/
theorem theorem20_8_AP_difference_eq_of_same_higham_residual_eq {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hsame : r = rHigh) :
    rectMatMulVec (theorem20_8AP A B Bplus) (fun k => y k - x k) =
      fun i =>
        Deltab i - rectMatMulVec DeltaA y i -
          rectMatMulVec A
            (rectMatMulVec Bplus
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i := by
  have hbase :=
    theorem20_8_AP_difference_eq_of_perturbed_higham_residual_eq
      A DeltaA b Deltab B DeltaB Bplus d Deltad x y rHigh hx hy hres
  ext i
  have hbase_i := congrFun hbase i
  have hr_i := congrFun hr i
  have hsame_i := congrFun hsame i
  unfold lsResidualHigham at hr_i
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the constraint-defect vector `Deltad - DeltaB*y` is bounded by the
    supplied perturbation radii. -/
theorem theorem20_8_vecNorm2_constraint_defect_le {n p : ℕ}
    (DeltaB : Fin p → Fin n → ℝ) (Deltad : Fin p → ℝ)
    (y : Fin n → ℝ) {DeltaB_norm Deltad_norm : ℝ}
    (hDeltaB : rectOpNorm2Le DeltaB DeltaB_norm)
    (hDeltad : vecNorm2 Deltad ≤ Deltad_norm) :
    vecNorm2 (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) ≤
      Deltad_norm + DeltaB_norm * vecNorm2 y := by
  calc
    vecNorm2 (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i)
        ≤ vecNorm2 Deltad +
            vecNorm2 (fun i : Fin p => -rectMatMulVec DeltaB y i) := by
            simpa [sub_eq_add_neg] using
              vecNorm2_add_le Deltad
                (fun i : Fin p => -rectMatMulVec DeltaB y i)
    _ = vecNorm2 Deltad + vecNorm2 (rectMatMulVec DeltaB y) := by
            rw [vecNorm2_neg]
    _ ≤ Deltad_norm + DeltaB_norm * vecNorm2 y :=
            add_le_add hDeltad (hDeltaB y)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    applying `A*Bplus` to a constraint-defect vector is controlled by an
    operator-2 bound for the product. -/
theorem theorem20_8_vecNorm2_ABplus_apply_le {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (e : Fin p → ℝ) {ABplus_norm : ℝ}
    (hABplus : rectOpNorm2Le (rectMatMul A Bplus) ABplus_norm) :
    vecNorm2 (rectMatMulVec A (rectMatMulVec Bplus e)) ≤
      ABplus_norm * vecNorm2 e := by
  simpa [rectMatMulVec_rectMatMul] using hABplus e
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the explicit `A*Bplus*(Deltad-DeltaB*y)` correction term is bounded by
    perturbation radii and an operator-2 bound for `A*Bplus`. -/
theorem theorem20_8_vecNorm2_ABplus_constraint_defect_le {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (DeltaB : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (Deltad : Fin p → ℝ)
    (y : Fin n → ℝ) {ABplus_norm DeltaB_norm Deltad_norm : ℝ}
    (hABplus_nonneg : 0 ≤ ABplus_norm)
    (hABplus : rectOpNorm2Le (rectMatMul A Bplus) ABplus_norm)
    (hDeltaB : rectOpNorm2Le DeltaB DeltaB_norm)
    (hDeltad : vecNorm2 Deltad ≤ Deltad_norm) :
    vecNorm2
        (rectMatMulVec A
          (rectMatMulVec Bplus
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i))) ≤
      ABplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) := by
  let defect : Fin p → ℝ :=
    fun i => Deltad i - rectMatMulVec DeltaB y i
  have hdefect :
      vecNorm2 defect ≤ Deltad_norm + DeltaB_norm * vecNorm2 y := by
    exact theorem20_8_vecNorm2_constraint_defect_le DeltaB Deltad y
      hDeltaB hDeltad
  calc
    vecNorm2 (rectMatMulVec A (rectMatMulVec Bplus defect))
        ≤ ABplus_norm * vecNorm2 defect :=
            theorem20_8_vecNorm2_ABplus_apply_le A Bplus defect hABplus
    _ ≤ ABplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) :=
            mul_le_mul_of_nonneg_left hdefect hABplus_nonneg
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the three explicit correction terms in the perturbed residual decomposition
    are bounded by supplied operator and vector perturbation radii. -/
theorem theorem20_8_vecNorm2_perturbed_residual_correction_le {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (Deltad : Fin p → ℝ) (y : Fin n → ℝ)
    {ABplus_norm DeltaA_norm DeltaB_norm Deltad_norm Deltab_norm : ℝ}
    (hABplus_nonneg : 0 ≤ ABplus_norm)
    (hABplus : rectOpNorm2Le (rectMatMul A Bplus) ABplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltaB : rectOpNorm2Le DeltaB DeltaB_norm)
    (hDeltad : vecNorm2 Deltad ≤ Deltad_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm) :
    vecNorm2
        (fun i : Fin m =>
          rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p => Deltad l - rectMatMulVec DeltaB y l)) i +
            rectMatMulVec DeltaA y i - Deltab i) ≤
      ABplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) +
        DeltaA_norm * vecNorm2 y + Deltab_norm := by
  let defect : Fin p → ℝ :=
    fun l => Deltad l - rectMatMulVec DeltaB y l
  let correction : Fin m → ℝ :=
    rectMatMulVec A (rectMatMulVec Bplus defect)
  let deltaAction : Fin m → ℝ := rectMatMulVec DeltaA y
  have hcorrection :
      vecNorm2 correction ≤
        ABplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) := by
    exact theorem20_8_vecNorm2_ABplus_constraint_defect_le
      A DeltaB Bplus Deltad y hABplus_nonneg hABplus hDeltaB hDeltad
  have hdelta :
      vecNorm2 deltaAction ≤ DeltaA_norm * vecNorm2 y := hDeltaA y
  have htwo :
      vecNorm2 (fun i : Fin m => correction i + deltaAction i) ≤
        ABplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) +
          DeltaA_norm * vecNorm2 y := by
    exact (vecNorm2_add_le correction deltaAction).trans
      (add_le_add hcorrection hdelta)
  calc
    vecNorm2 (fun i : Fin m => correction i + deltaAction i - Deltab i)
        ≤ vecNorm2 (fun i : Fin m => correction i + deltaAction i) +
            vecNorm2 (fun i : Fin m => -Deltab i) := by
            simpa [sub_eq_add_neg] using
              vecNorm2_add_le
                (fun i : Fin m => correction i + deltaAction i)
                (fun i : Fin m => -Deltab i)
    _ = vecNorm2 (fun i : Fin m => correction i + deltaAction i) +
          vecNorm2 Deltab := by
            rw [vecNorm2_neg]
    _ ≤ (ABplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) +
          DeltaA_norm * vecNorm2 y) + Deltab_norm :=
            add_le_add htwo hDeltab
    _ = ABplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) +
          DeltaA_norm * vecNorm2 y + Deltab_norm := by
            ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    elementary Euclidean bound for Higham's signed residual `b - A*y`. -/
theorem theorem20_8_vecNorm2_higham_residual_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    vecNorm2 (lsResidualHigham A b y) ≤
      vecNorm2 b + frobNormRect A * vecNorm2 y := by
  calc
    vecNorm2 (lsResidualHigham A b y)
        = vecNorm2 (fun i : Fin m => b i - rectMatMulVec A y i) := by
            rfl
    _ ≤ vecNorm2 b +
          vecNorm2 (fun i : Fin m => -rectMatMulVec A y i) := by
            simpa [sub_eq_add_neg] using
              vecNorm2_add_le b
                (fun i : Fin m => -rectMatMulVec A y i)
    _ = vecNorm2 b + vecNorm2 (rectMatMulVec A y) := by
            rw [vecNorm2_neg]
    _ ≤ vecNorm2 b + frobNormRect A * vecNorm2 y :=
            add_le_add (le_refl (vecNorm2 b))
              (vecNorm2_rectMatMulVec_le_frobNormRect_mul A y)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source right-hand side bounded by the model action plus the source signed
    residual. -/
theorem theorem20_8_vecNorm2_b_le_frobNormRect_mul_x_add_sourceResidual
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    vecNorm2 b ≤
      frobNormRect A * vecNorm2 x + vecNorm2 (lsResidualHigham A b x) := by
  have hb_eq :
      b = fun i : Fin m => rectMatMulVec A x i + lsResidualHigham A b x i := by
    ext i
    simp [lsResidualHigham]
  calc
    vecNorm2 b =
        vecNorm2
          (fun i : Fin m => rectMatMulVec A x i + lsResidualHigham A b x i) :=
          congrArg vecNorm2 hb_eq
    _ ≤ vecNorm2 (rectMatMulVec A x) + vecNorm2 (lsResidualHigham A b x) :=
          vecNorm2_add_le (rectMatMulVec A x) (lsResidualHigham A b x)
    _ ≤ frobNormRect A * vecNorm2 x + vecNorm2 (lsResidualHigham A b x) :=
          add_le_add (vecNorm2_rectMatMulVec_le_frobNormRect_mul A x) le_rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source right-hand-side scale from a source residual scale. -/
theorem theorem20_8_vecNorm2_b_le_of_sourceResidualScale {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ)
    {residualScale : ℝ}
    (hresidual :
      vecNorm2 (lsResidualHigham A b x) ≤ residualScale * vecNorm2 x) :
    vecNorm2 b ≤ (frobNormRect A + residualScale) * vecNorm2 x := by
  have hbase :=
    theorem20_8_vecNorm2_b_le_frobNormRect_mul_x_add_sourceResidual A b x
  calc
    vecNorm2 b ≤
        frobNormRect A * vecNorm2 x +
          vecNorm2 (lsResidualHigham A b x) := hbase
    _ ≤ frobNormRect A * vecNorm2 x + residualScale * vecNorm2 x :=
        add_le_add le_rfl hresidual
    _ = (frobNormRect A + residualScale) * vecNorm2 x := by
        ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the stationarity-row right-hand side `DeltaB^T*mu - DeltaA^T*s` in the
    Cox--Higham KKT system is bounded by supplied operator-2 radii. -/
theorem theorem20_8_vecNorm2_stationarity_forcing_le {m n p : ℕ}
    (DeltaA : Fin m → Fin n → ℝ) (DeltaB : Fin p → Fin n → ℝ)
    (mu : Fin p → ℝ) (s : Fin m → ℝ)
    {DeltaB_norm DeltaA_norm : ℝ}
    (hDeltaB_norm_nonneg : 0 ≤ DeltaB_norm)
    (hDeltaA_norm_nonneg : 0 ≤ DeltaA_norm)
    (hDeltaB : rectOpNorm2Le DeltaB DeltaB_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm) :
    vecNorm2
        (fun j : Fin n =>
          (∑ r : Fin p, DeltaB r j * mu r) -
            (∑ i : Fin m, DeltaA i j * s i)) ≤
      DeltaB_norm * vecNorm2 mu + DeltaA_norm * vecNorm2 s := by
  have hDeltaBT :
      rectOpNorm2Le (finiteTranspose DeltaB) DeltaB_norm :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      DeltaB hDeltaB_norm_nonneg hDeltaB
  have hDeltaAT :
      rectOpNorm2Le (finiteTranspose DeltaA) DeltaA_norm :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      DeltaA hDeltaA_norm_nonneg hDeltaA
  have hB :
      vecNorm2 (rectMatMulVec (finiteTranspose DeltaB) mu) ≤
        DeltaB_norm * vecNorm2 mu := hDeltaBT mu
  have hA :
      vecNorm2 (rectMatMulVec (finiteTranspose DeltaA) s) ≤
        DeltaA_norm * vecNorm2 s := hDeltaAT s
  have hrepr :
      (fun j : Fin n =>
          (∑ r : Fin p, DeltaB r j * mu r) -
            (∑ i : Fin m, DeltaA i j * s i)) =
        fun j : Fin n =>
          rectMatMulVec (finiteTranspose DeltaB) mu j -
            rectMatMulVec (finiteTranspose DeltaA) s j := by
    ext j
    simp [rectMatMulVec, finiteTranspose]
  rw [hrepr]
  calc
    vecNorm2
        (fun j : Fin n =>
          rectMatMulVec (finiteTranspose DeltaB) mu j -
            rectMatMulVec (finiteTranspose DeltaA) s j)
        ≤ vecNorm2 (rectMatMulVec (finiteTranspose DeltaB) mu) +
            vecNorm2
              (fun j : Fin n =>
                -rectMatMulVec (finiteTranspose DeltaA) s j) := by
            simpa [sub_eq_add_neg] using
              vecNorm2_add_le (rectMatMulVec (finiteTranspose DeltaB) mu)
                (fun j : Fin n =>
                  -rectMatMulVec (finiteTranspose DeltaA) s j)
    _ = vecNorm2 (rectMatMulVec (finiteTranspose DeltaB) mu) +
          vecNorm2 (rectMatMulVec (finiteTranspose DeltaA) s) := by
            rw [vecNorm2_neg]
    _ ≤ DeltaB_norm * vecNorm2 mu + DeltaA_norm * vecNorm2 s :=
            add_le_add hB hA
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    source table `B_A^+ = (I - (AP)^+ A)B^+`.

    The arguments `Bplus` and `APplus` are supplied pseudo-inverse tables for
    `B^+` and `(AP)^+`, respectively.  The definition records the algebraic
    expression used in the printed condition quantities. -/
noncomputable def theorem20_8BAplus {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (_B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ) :
    Fin n → Fin p → ℝ :=
  rectMatMul (fun i j => idMatrix n i j - rectMatMul APplus A i j) Bplus
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    applying `B_A^+ = (I - (AP)^+ A)B^+` to a vector expands into the
    `B^+` term minus the reduced-problem pseudo-inverse correction. -/
theorem theorem20_8BAplus_apply {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (e : Fin p → ℝ) :
    rectMatMulVec (theorem20_8BAplus A B Bplus APplus) e =
      fun j : Fin n =>
        rectMatMulVec Bplus e j -
          rectMatMulVec APplus
            (rectMatMulVec A (rectMatMulVec Bplus e)) j := by
  ext j
  unfold theorem20_8BAplus
  rw [rectMatMulVec_rectMatMul]
  unfold rectMatMulVec
  have hsplit :
      (∑ k : Fin n,
          (idMatrix n j k - rectMatMul APplus A j k) *
            (∑ x : Fin p, Bplus k x * e x)) =
        (∑ k : Fin n,
          idMatrix n j k * (∑ x : Fin p, Bplus k x * e x)) -
        (∑ k : Fin n,
          rectMatMul APplus A j k *
            (∑ x : Fin p, Bplus k x * e x)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hid :=
    congrFun (rectMatMulVec_idMatrix (fun k : Fin n =>
      ∑ x : Fin p, Bplus k x * e x)) j
  have hcomp :=
    congrFun (rectMatMulVec_rectMatMul APplus A
      (rectMatMulVec Bplus e)) j
  have hid' :
      (∑ k : Fin n, idMatrix n j k *
          (∑ x : Fin p, Bplus k x * e x)) =
        ∑ x : Fin p, Bplus j x * e x := by
    simpa [rectMatMulVec] using hid
  have hcomp' :
      (∑ k : Fin n, rectMatMul APplus A j k *
          (∑ x : Fin p, Bplus k x * e x)) =
        ∑ x : Fin m,
          APplus j x *
            (∑ x_1 : Fin n,
              A x x_1 * (∑ x_2 : Fin p, Bplus x_1 x_2 * e x_2)) := by
    simpa [rectMatMulVec] using hcomp
  rw [hsplit, hid', hcomp']
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the source product `A B_A^+` splits into `A B^+` minus the
    `(AP)^+`-correction term. -/
theorem theorem20_8A_BAplus_apply {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (e : Fin p → ℝ) :
    rectMatMulVec A
        (rectMatMulVec (theorem20_8BAplus A B Bplus APplus) e) =
      fun i : Fin m =>
        rectMatMulVec A (rectMatMulVec Bplus e) i -
          rectMatMulVec A
            (rectMatMulVec APplus
              (rectMatMulVec A (rectMatMulVec Bplus e))) i := by
  rw [theorem20_8BAplus_apply, rectMatMulVec_sub]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the `A B^+` constraint-defect correction decomposes into the source
    `A B_A^+` term plus the reduced-problem pseudo-inverse correction. -/
theorem theorem20_8ABplus_eq_A_APplus_A_Bplus_add_A_BAplus {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (e : Fin p → ℝ) :
    rectMatMulVec A (rectMatMulVec Bplus e) =
      fun i : Fin m =>
        rectMatMulVec A
            (rectMatMulVec APplus
              (rectMatMulVec A (rectMatMulVec Bplus e))) i +
          rectMatMulVec A
            (rectMatMulVec (theorem20_8BAplus A B Bplus APplus) e) i := by
  ext i
  have h :=
    congrFun (theorem20_8A_BAplus_apply A B Bplus APplus e) i
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    applying the source product `A B_A^+` is controlled by an operator-2
    bound for that product. -/
theorem theorem20_8_vecNorm2_A_BAplus_apply_le {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (e : Fin p → ℝ) {ABAplus_norm : ℝ}
    (hABAplus :
      rectOpNorm2Le (rectMatMul A (theorem20_8BAplus A B Bplus APplus))
        ABAplus_norm) :
    vecNorm2
        (rectMatMulVec A
          (rectMatMulVec (theorem20_8BAplus A B Bplus APplus) e)) ≤
      ABAplus_norm * vecNorm2 e := by
  simpa [rectMatMulVec_rectMatMul] using hABAplus e
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the source `A B_A^+` constraint-defect correction is bounded by
    perturbation radii and an operator-2 bound for `A B_A^+`. -/
theorem theorem20_8_vecNorm2_A_BAplus_constraint_defect_le {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B DeltaB : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (Deltad : Fin p → ℝ) (y : Fin n → ℝ)
    {ABAplus_norm DeltaB_norm Deltad_norm : ℝ}
    (hABAplus_nonneg : 0 ≤ ABAplus_norm)
    (hABAplus :
      rectOpNorm2Le (rectMatMul A (theorem20_8BAplus A B Bplus APplus))
        ABAplus_norm)
    (hDeltaB : rectOpNorm2Le DeltaB DeltaB_norm)
    (hDeltad : vecNorm2 Deltad ≤ Deltad_norm) :
    vecNorm2
        (rectMatMulVec A
          (rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i))) ≤
      ABAplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) := by
  let defect : Fin p → ℝ :=
    fun i => Deltad i - rectMatMulVec DeltaB y i
  have hdefect :
      vecNorm2 defect ≤ Deltad_norm + DeltaB_norm * vecNorm2 y := by
    exact theorem20_8_vecNorm2_constraint_defect_le DeltaB Deltad y
      hDeltaB hDeltad
  calc
    vecNorm2
        (rectMatMulVec A
          (rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i)))
        = vecNorm2
            (rectMatMulVec A
              (rectMatMulVec (theorem20_8BAplus A B Bplus APplus) defect)) := by
            rfl
    _ ≤ ABAplus_norm * vecNorm2 defect :=
            theorem20_8_vecNorm2_A_BAplus_apply_le A B Bplus APplus
              defect hABAplus
    _ ≤ ABAplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) :=
            mul_le_mul_of_nonneg_left hdefect hABAplus_nonneg
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    residual decomposition with the constraint-defect correction split through
    the printed source quantity `B_A^+`. -/
theorem theorem20_8_perturbed_feasible_residual_decomp_BAplus {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    lsResidual (fun i j => A i j + DeltaA i j) (fun i => b i + Deltab i) y =
      fun i =>
        lsResidual (theorem20_8AP A B Bplus)
            (fun i => b i - rectMatMulVec A x i) (fun j => y j - x j) i +
          (rectMatMulVec A
              (rectMatMulVec APplus
                (rectMatMulVec A
                  (rectMatMulVec Bplus
                    (fun l => Deltad l - rectMatMulVec DeltaB y l)))) i +
            rectMatMulVec A
              (rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
                (fun l => Deltad l - rectMatMulVec DeltaB y l)) i) +
          rectMatMulVec DeltaA y i -
          Deltab i := by
  ext i
  let defect : Fin p → ℝ :=
    fun l => Deltad l - rectMatMulVec DeltaB y l
  have hres :=
    congrFun
      (theorem20_8_perturbed_feasible_residual_decomp
        A DeltaA b Deltab B DeltaB Bplus d Deltad x y hx hy) i
  have hsplit :=
    congrFun
      (theorem20_8ABplus_eq_A_APplus_A_Bplus_add_A_BAplus
        A B Bplus APplus defect) i
  change
    lsResidual (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y i =
      lsResidual (theorem20_8AP A B Bplus)
          (fun i => b i - rectMatMulVec A x i) (fun j => y j - x j) i +
        (rectMatMulVec A
            (rectMatMulVec APplus
              (rectMatMulVec A (rectMatMulVec Bplus defect))) i +
          rectMatMulVec A
            (rectMatMulVec (theorem20_8BAplus A B Bplus APplus) defect) i) +
        rectMatMulVec DeltaA y i -
        Deltab i
  rw [hres, hsplit]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    condition quantity `kappa_B(A) = ||A||_F ||(AP)^+||_2`. -/
noncomputable def theorem20_8KappaB {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ) : ℝ :=
  frobNormRect A * complexMatrixOp2 (realRectToCMatrix APplus)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    condition quantity `kappa_A(B) = ||B||_F ||B_A^+||_2`. -/
noncomputable def theorem20_8KappaA {n p : ℕ}
    (B : Fin p → Fin n → ℝ) (BAplus : Fin n → Fin p → ℝ) : ℝ :=
  frobNormRect B * complexMatrixOp2 (realRectToCMatrix BAplus)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8:
    residual multiplier in the first-order coefficient of (20.25),
    `kappa_B(A)^2 * ((||B||_F / ||A||_F) ||A B_A^+||_2 + 1)`. -/
noncomputable def theorem20_8ResidualAmplifier {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ) : ℝ :=
  theorem20_8KappaB A APplus ^ 2 *
    ((frobNormRect B / frobNormRect A) *
      complexMatrixOp2 (realRectToCMatrix (rectMatMul A BAplus)) + 1)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8, equation (20.25):
    the first-order scalar coefficient multiplying `eps`, excluding the
    source's `O(eps^2)` remainder. -/
noncomputable def theorem20_8FirstOrderRHS {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ) : ℝ :=
  theorem20_8KappaA B BAplus *
      (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) +
    theorem20_8KappaB A APplus *
      (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) +
    theorem20_8ResidualAmplifier A B APplus BAplus *
      (vecNorm2 r / (frobNormRect A * vecNorm2 x))
/-- The source quantity `kappa_B(A)` in Theorem 20.8 is nonnegative. -/
theorem theorem20_8KappaB_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ) :
    0 ≤ theorem20_8KappaB A APplus := by
  unfold theorem20_8KappaB
  exact mul_nonneg (frobNormRect_nonneg A)
    (complexMatrixOp2_nonneg (realRectToCMatrix APplus))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-shaped smallness `eps < 1 / kappa_B(A)` implies the multiplied
    Wedin smallness guard used by the reduced wrapper. -/
theorem theorem20_8KappaB_mul_eps_lt_one_of_eps_lt_inv {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    {eps : ℝ}
    (hkappa_pos : 0 < theorem20_8KappaB A APplus)
    (heps : eps < 1 / theorem20_8KappaB A APplus) :
    theorem20_8KappaB A APplus * eps < 1 := by
  have hmul := mul_lt_mul_of_pos_left heps hkappa_pos
  rwa [one_div, mul_inv_cancel₀ (ne_of_gt hkappa_pos)] at hmul
/-- Elementary small-gain algebra used by the residual-gap route: from
    `x <= a*x + b` and `a < 1`, absorb the self term. -/
theorem real_le_div_one_sub_of_le_mul_add {x a b : ℝ}
    (ha : a < 1) (h : x ≤ a * x + b) :
  x ≤ b / (1 - a) := by
  have hden : 0 < 1 - a := by linarith
  have hmul : (1 - a) * x ≤ b := by nlinarith
  exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hmul)
/-- Elementary norm-growth bound used in coupled Theorem 20.8 small-gain
    estimates: the perturbed solution norm is bounded by the source norm times
    one plus the relative solution difference. -/
theorem vecNorm2_le_one_add_relative_difference_mul {n : ℕ}
    (x y : Fin n → ℝ) (hxnorm : 0 < vecNorm2 x) :
    vecNorm2 y ≤
      (1 + vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x) *
        vecNorm2 x := by
  have hxne : vecNorm2 x ≠ 0 := ne_of_gt hxnorm
  have hy_eq : y = fun j : Fin n => x j + (y j - x j) := by
    ext j
    ring
  calc
    vecNorm2 y = vecNorm2 (fun j : Fin n => x j + (y j - x j)) :=
        congrArg vecNorm2 hy_eq
    _ ≤ vecNorm2 x + vecNorm2 (fun j : Fin n => y j - x j) :=
        vecNorm2_add_le x (fun j : Fin n => y j - x j)
    _ =
        vecNorm2 x +
          (vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x) *
            vecNorm2 x := by
        field_simp [hxne]
    _ =
        (1 + vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x) *
          vecNorm2 x := by
        ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the explicit non-residual part of the `B_A^+` split residual-gap estimate.

    The missing residual-gap estimate contains a self term
    `||(AP)||₂ * ||y-x||₂`; this definition names the remaining data and
    constraint-defect correction terms so the small-gain wrapper below can
    absorb the self term without re-exposing the long scalar expression. -/
noncomputable def theorem20_8BAplusResidualGapCorrection {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d : Fin p → ℝ)
    (y : Fin n → ℝ) (eps : ℝ) : ℝ :=
  (theorem20_8KappaB A APplus *
      (complexMatrixOp2 (realRectToCMatrix (rectMatMul A Bplus)) *
        (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul A (theorem20_8BAplus A B Bplus APplus))) *
      (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y)) +
    (eps * frobNormRect A) * vecNorm2 y +
    eps * vecNorm2 b
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the right-hand side obtained after substituting the `B_A^+` residual-gap
    split into the residual-explicit solution-difference inequality, before the
    small-gain self term is absorbed. -/
noncomputable def theorem20_8BAplusSmallGainSolutionRHS {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d : Fin p → ℝ)
    (y : Fin n → ℝ) (eps : ℝ) : ℝ :=
  complexMatrixOp2
      (realRectToCMatrix (theorem20_8BAplus A B Bplus APplus)) *
    (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y) +
  complexMatrixOp2 (realRectToCMatrix APplus) *
    (theorem20_8BAplusResidualGapCorrection A b B Bplus APplus d y eps +
      ((eps * frobNormRect A) * vecNorm2 y + eps * vecNorm2 b))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the residual-gap radius obtained after small-gain absorption of the
    `||(AP)^+||₂ ||AP||₂ ||y-x||₂` self term. -/
noncomputable def theorem20_8BAplusSmallGainResidualRadius {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d : Fin p → ℝ)
    (y : Fin n → ℝ) (eps : ℝ) : ℝ :=
  complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B Bplus)) *
      (theorem20_8BAplusSmallGainSolutionRHS A b B Bplus APplus d y eps /
        (1 -
          complexMatrixOp2 (realRectToCMatrix APplus) *
            complexMatrixOp2
              (realRectToCMatrix (theorem20_8AP A B Bplus)))) +
    theorem20_8BAplusResidualGapCorrection A b B Bplus APplus d y eps
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    coefficient of the source-solution residual-gap radius after small-gain
    absorption.  The radius is exactly `eps` times this coefficient. -/
noncomputable def theorem20_8BAplusSmallGainResidualRadiusCoeff {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  theorem20_8BAplusSmallGainResidualRadius A b B Bplus APplus d x 1
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the source-solution small-gain residual radius is linear in the perturbation
    parameter. -/
theorem theorem20_8BAplusSmallGainResidualRadius_eq_eps_mul_coeff
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (eps : ℝ) :
    theorem20_8BAplusSmallGainResidualRadius A b B Bplus APplus d x eps =
      eps * theorem20_8BAplusSmallGainResidualRadiusCoeff
        A b B Bplus APplus d x := by
  dsimp [theorem20_8BAplusSmallGainResidualRadiusCoeff,
    theorem20_8BAplusSmallGainResidualRadius,
    theorem20_8BAplusSmallGainSolutionRHS,
    theorem20_8BAplusResidualGapCorrection]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    a coefficient bound discharges the source residual-radius premise for
    nonnegative perturbation radii. -/
theorem theorem20_8BAplusSmallGainResidualRadius_le_eps_residual_of_coeff_le
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps)
    (hcoeff :
      theorem20_8BAplusSmallGainResidualRadiusCoeff A b B Bplus APplus d x ≤
        vecNorm2 (lsResidualHigham A b x)) :
    theorem20_8BAplusSmallGainResidualRadius A b B Bplus APplus d x eps ≤
      eps * vecNorm2 (lsResidualHigham A b x) := by
  rw [theorem20_8BAplusSmallGainResidualRadius_eq_eps_mul_coeff]
  exact mul_le_mul_of_nonneg_left hcoeff heps
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the non-residual `B_A^+` residual-gap correction is monotone in the
    perturbed-solution norm when the perturbation radius is nonnegative. -/
theorem theorem20_8BAplusResidualGapCorrection_mono_of_vecNorm2_le
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d : Fin p → ℝ)
    (x y : Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hyx : vecNorm2 y ≤ vecNorm2 x) :
    theorem20_8BAplusResidualGapCorrection A b B Bplus APplus d y eps ≤
      theorem20_8BAplusResidualGapCorrection A b B Bplus APplus d x eps := by
  let innerY : ℝ :=
    eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y
  let innerX : ℝ :=
    eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 x
  let kB : ℝ := theorem20_8KappaB A APplus
  let C1 : ℝ := complexMatrixOp2 (realRectToCMatrix (rectMatMul A Bplus))
  let C2 : ℝ :=
    complexMatrixOp2
      (realRectToCMatrix
        (rectMatMul A (theorem20_8BAplus A B Bplus APplus)))
  have hinner : innerY ≤ innerX := by
    dsimp [innerY, innerX]
    exact add_le_add (le_refl _) <|
      mul_le_mul_of_nonneg_left hyx
        (mul_nonneg heps (frobNormRect_nonneg B))
  have hkB : 0 ≤ kB := by
    dsimp [kB]
    exact theorem20_8KappaB_nonneg A APplus
  have hC1 : 0 ≤ C1 := by
    dsimp [C1]
    exact complexMatrixOp2_nonneg _
  have hC2 : 0 ≤ C2 := by
    dsimp [C2]
    exact complexMatrixOp2_nonneg _
  have hAcoeff : 0 ≤ eps * frobNormRect A :=
    mul_nonneg heps (frobNormRect_nonneg A)
  have hterm1 : kB * (C1 * innerY) ≤ kB * (C1 * innerX) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hinner hC1) hkB
  have hterm2 : C2 * innerY ≤ C2 * innerX :=
    mul_le_mul_of_nonneg_left hinner hC2
  have hterm3 :
      (eps * frobNormRect A) * vecNorm2 y ≤
        (eps * frobNormRect A) * vecNorm2 x :=
    mul_le_mul_of_nonneg_left hyx hAcoeff
  dsimp [theorem20_8BAplusResidualGapCorrection, innerY, innerX, kB, C1, C2]
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the `B_A^+` small-gain solution RHS is monotone in the
    perturbed-solution norm when the perturbation radius is nonnegative. -/
theorem theorem20_8BAplusSmallGainSolutionRHS_mono_of_vecNorm2_le
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d : Fin p → ℝ)
    (x y : Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hyx : vecNorm2 y ≤ vecNorm2 x) :
    theorem20_8BAplusSmallGainSolutionRHS A b B Bplus APplus d y eps ≤
      theorem20_8BAplusSmallGainSolutionRHS A b B Bplus APplus d x eps := by
  let innerY : ℝ :=
    eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 y
  let innerX : ℝ :=
    eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 x
  let CBA : ℝ :=
    complexMatrixOp2
      (realRectToCMatrix (theorem20_8BAplus A B Bplus APplus))
  let CAP : ℝ := complexMatrixOp2 (realRectToCMatrix APplus)
  let dataY : ℝ := (eps * frobNormRect A) * vecNorm2 y + eps * vecNorm2 b
  let dataX : ℝ := (eps * frobNormRect A) * vecNorm2 x + eps * vecNorm2 b
  let corrY : ℝ :=
    theorem20_8BAplusResidualGapCorrection A b B Bplus APplus d y eps
  let corrX : ℝ :=
    theorem20_8BAplusResidualGapCorrection A b B Bplus APplus d x eps
  have hinner : innerY ≤ innerX := by
    dsimp [innerY, innerX]
    exact add_le_add (le_refl _) <|
      mul_le_mul_of_nonneg_left hyx
        (mul_nonneg heps (frobNormRect_nonneg B))
  have hdata : dataY ≤ dataX := by
    dsimp [dataY, dataX]
    have hAcoeff : 0 ≤ eps * frobNormRect A :=
      mul_nonneg heps (frobNormRect_nonneg A)
    exact add_le_add
      (mul_le_mul_of_nonneg_left hyx hAcoeff) (le_refl _)
  have hcorr : corrY ≤ corrX := by
    dsimp [corrY, corrX]
    exact
      theorem20_8BAplusResidualGapCorrection_mono_of_vecNorm2_le
        A b B Bplus APplus d x y heps hyx
  have hCBA : 0 ≤ CBA := by
    dsimp [CBA]
    exact complexMatrixOp2_nonneg _
  have hCAP : 0 ≤ CAP := by
    dsimp [CAP]
    exact complexMatrixOp2_nonneg _
  have hterm1 : CBA * innerY ≤ CBA * innerX :=
    mul_le_mul_of_nonneg_left hinner hCBA
  have hterm2 : CAP * (corrY + dataY) ≤ CAP * (corrX + dataX) :=
    mul_le_mul_of_nonneg_left (add_le_add hcorr hdata) hCAP
  dsimp [theorem20_8BAplusSmallGainSolutionRHS, innerY, innerX, CBA, CAP,
    dataY, dataX, corrY, corrX]
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the absorbed `B_A^+` small-gain residual radius is monotone in the
    perturbed-solution norm under the small-gain denominator condition. -/
theorem theorem20_8BAplusSmallGainResidualRadius_mono_of_vecNorm2_le
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d : Fin p → ℝ)
    (x y : Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hyx : vecNorm2 y ≤ vecNorm2 x)
    (hgain :
      complexMatrixOp2 (realRectToCMatrix APplus) *
          complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B Bplus)) < 1) :
    theorem20_8BAplusSmallGainResidualRadius A b B Bplus APplus d y eps ≤
      theorem20_8BAplusSmallGainResidualRadius A b B Bplus APplus d x eps := by
  let APop : ℝ :=
    complexMatrixOp2 (realRectToCMatrix (theorem20_8AP A B Bplus))
  let APnorm : ℝ := complexMatrixOp2 (realRectToCMatrix APplus)
  let denom : ℝ := 1 - APnorm * APop
  let solY : ℝ :=
    theorem20_8BAplusSmallGainSolutionRHS A b B Bplus APplus d y eps
  let solX : ℝ :=
    theorem20_8BAplusSmallGainSolutionRHS A b B Bplus APplus d x eps
  let corrY : ℝ :=
    theorem20_8BAplusResidualGapCorrection A b B Bplus APplus d y eps
  let corrX : ℝ :=
    theorem20_8BAplusResidualGapCorrection A b B Bplus APplus d x eps
  have hden : 0 < denom := by
    dsimp [denom, APnorm, APop]
    linarith
  have hsol : solY ≤ solX := by
    dsimp [solY, solX]
    exact
      theorem20_8BAplusSmallGainSolutionRHS_mono_of_vecNorm2_le
        A b B Bplus APplus d x y heps hyx
  have hcorr : corrY ≤ corrX := by
    dsimp [corrY, corrX]
    exact
      theorem20_8BAplusResidualGapCorrection_mono_of_vecNorm2_le
        A b B Bplus APplus d x y heps hyx
  have hAPop : 0 ≤ APop := by
    dsimp [APop]
    exact complexMatrixOp2_nonneg _
  have hdiv : solY / denom ≤ solX / denom :=
    div_le_div_of_nonneg_right hsol (le_of_lt hden)
  have hscaled : APop * (solY / denom) ≤ APop * (solX / denom) :=
    mul_le_mul_of_nonneg_left hdiv hAPop
  dsimp [theorem20_8BAplusSmallGainResidualRadius, APop, APnorm, denom, solY,
    solX, corrY, corrX]
  linarith
/-- The source quantity `kappa_A(B)` in Theorem 20.8 is nonnegative. -/
theorem theorem20_8KappaA_nonneg {n p : ℕ}
    (B : Fin p → Fin n → ℝ) (BAplus : Fin n → Fin p → ℝ) :
    0 ≤ theorem20_8KappaA B BAplus := by
  unfold theorem20_8KappaA
  exact mul_nonneg (frobNormRect_nonneg B)
    (complexMatrixOp2_nonneg (realRectToCMatrix BAplus))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    applying the source correction matrix `B_A^+` is bounded by its operator
    2-norm. -/
theorem theorem20_8_vecNorm2_BAplus_apply_le {n p : ℕ}
    (BAplus : Fin n → Fin p → ℝ) (z : Fin p → ℝ) :
    vecNorm2 (rectMatMulVec BAplus z) ≤
      complexMatrixOp2 (realRectToCMatrix BAplus) * vecNorm2 z := by
  exact
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le BAplus le_rfl z
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the direct `B_A^+` constraint-defect correction is bounded by supplied
    operator and perturbation radii. -/
theorem theorem20_8_vecNorm2_BAplus_constraint_defect_le {n p : ℕ}
    (DeltaB : Fin p → Fin n → ℝ) (BAplus : Fin n → Fin p → ℝ)
    (Deltad : Fin p → ℝ) (y : Fin n → ℝ)
    {BAplus_norm DeltaB_norm Deltad_norm : ℝ}
    (hBAplus_nonneg : 0 ≤ BAplus_norm)
    (hBAplus : rectOpNorm2Le BAplus BAplus_norm)
    (hDeltaB : rectOpNorm2Le DeltaB DeltaB_norm)
    (hDeltad : vecNorm2 Deltad ≤ Deltad_norm) :
    vecNorm2
        (rectMatMulVec BAplus
          (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i)) ≤
      BAplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) := by
  let defect : Fin p → ℝ :=
    fun i => Deltad i - rectMatMulVec DeltaB y i
  have hdefect :
      vecNorm2 defect ≤ Deltad_norm + DeltaB_norm * vecNorm2 y := by
    exact theorem20_8_vecNorm2_constraint_defect_le DeltaB Deltad y
      hDeltaB hDeltad
  calc
    vecNorm2
        (rectMatMulVec BAplus
          (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i))
        = vecNorm2 (rectMatMulVec BAplus defect) := by
            rfl
    _ ≤ BAplus_norm * vecNorm2 defect := hBAplus defect
    _ ≤ BAplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) :=
      mul_le_mul_of_nonneg_left hdefect hBAplus_nonneg
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the direct `B_A^+` correction radius has the source-normalized
    `kappa_A(B) * (||d||/(||B||_F ||x||) + 1)` form when the first-order
    constraint defect uses `x`. -/
theorem theorem20_8KappaA_directCorrection_sourceTerm_eq {n p : ℕ}
    (B : Fin p → Fin n → ℝ) (BAplus : Fin n → Fin p → ℝ)
    (d : Fin p → ℝ) (x : Fin n → ℝ) {eps : ℝ}
    (hBpos : 0 < frobNormRect B) (hxpos : 0 < vecNorm2 x) :
    complexMatrixOp2 (realRectToCMatrix BAplus) *
        (eps * vecNorm2 d + (eps * frobNormRect B) * vecNorm2 x) =
      eps * theorem20_8KappaA B BAplus *
        (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) * vecNorm2 x := by
  unfold theorem20_8KappaA
  field_simp [ne_of_gt hBpos, ne_of_gt hxpos,
    mul_ne_zero (ne_of_gt hBpos) (ne_of_gt hxpos)]
/-- Under the natural nonzero-`A` denominator side condition, the residual
    amplifier in Theorem 20.8's first-order coefficient is nonnegative. -/
theorem theorem20_8ResidualAmplifier_nonneg {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    (hApos : 0 < frobNormRect A) :
    0 ≤ theorem20_8ResidualAmplifier A B APplus BAplus := by
  unfold theorem20_8ResidualAmplifier
  have hratio : 0 ≤ frobNormRect B / frobNormRect A :=
    div_nonneg (frobNormRect_nonneg B) (le_of_lt hApos)
  have hop :
      0 ≤ complexMatrixOp2
        (realRectToCMatrix (rectMatMul A BAplus)) :=
    complexMatrixOp2_nonneg (realRectToCMatrix (rectMatMul A BAplus))
  have hinside :
      0 ≤ (frobNormRect B / frobNormRect A) *
          complexMatrixOp2 (realRectToCMatrix (rectMatMul A BAplus)) + 1 := by
    nlinarith [mul_nonneg hratio hop]
  exact mul_nonneg (sq_nonneg _) hinside
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the source-normalized direct `kappa_A(B)` term is one summand of the
    first-order coefficient in (20.25). -/
theorem theorem20_8KappaA_sourceTerm_le_firstOrderRHS {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    (hApos : 0 < frobNormRect A) (hxpos : 0 < vecNorm2 x) :
    theorem20_8KappaA B BAplus *
        (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) ≤
      theorem20_8FirstOrderRHS A b B d x r APplus BAplus := by
  let termA : ℝ := theorem20_8KappaA B BAplus *
    (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1)
  let termB : ℝ := theorem20_8KappaB A APplus *
    (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1)
  let termR : ℝ := theorem20_8ResidualAmplifier A B APplus BAplus *
    (vecNorm2 r / (frobNormRect A * vecNorm2 x))
  have htermB_nonneg : 0 ≤ termB := by
    dsimp [termB]
    apply mul_nonneg
    · linarith [theorem20_8KappaB_nonneg A APplus]
    · have hratio : 0 ≤ vecNorm2 b / (frobNormRect A * vecNorm2 x) := by
        exact div_nonneg (vecNorm2_nonneg b)
          (le_of_lt (mul_pos hApos hxpos))
      linarith
  have htermR_nonneg : 0 ≤ termR := by
    dsimp [termR]
    exact mul_nonneg
      (theorem20_8ResidualAmplifier_nonneg A B APplus BAplus hApos)
      (div_nonneg (vecNorm2_nonneg r)
        (le_of_lt (mul_pos hApos hxpos)))
  change termA ≤ theorem20_8FirstOrderRHS A b B d x r APplus BAplus
  unfold theorem20_8FirstOrderRHS
  change termA ≤ termA + termB + termR
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the data-forcing radius through `(AP)^+` has the source-normalized
    `kappa_B(A) * (||b||/(||A||_F ||x||) + 1)` form. -/
theorem theorem20_8KappaB_dataForcing_sourceTerm_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (APplus : Fin n → Fin m → ℝ) {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hxpos : 0 < vecNorm2 x) :
    complexMatrixOp2 (realRectToCMatrix APplus) *
        ((eps * frobNormRect A) * vecNorm2 x + eps * vecNorm2 b) =
      eps * theorem20_8KappaB A APplus *
        (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) * vecNorm2 x := by
  unfold theorem20_8KappaB
  field_simp [ne_of_gt hApos, ne_of_gt hxpos,
    mul_ne_zero (ne_of_gt hApos) (ne_of_gt hxpos)]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the source-normalized `kappa_B(A)` data term is bounded by the full
    first-order coefficient in (20.25). -/
theorem theorem20_8KappaB_dataSourceTerm_le_firstOrderRHS {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    (hApos : 0 < frobNormRect A) (hxpos : 0 < vecNorm2 x) :
    theorem20_8KappaB A APplus *
        (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) ≤
      theorem20_8FirstOrderRHS A b B d x r APplus BAplus := by
  let termA : ℝ := theorem20_8KappaA B BAplus *
    (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1)
  let baseB : ℝ := vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1
  let termB : ℝ := theorem20_8KappaB A APplus * baseB
  let termR : ℝ := theorem20_8ResidualAmplifier A B APplus BAplus *
    (vecNorm2 r / (frobNormRect A * vecNorm2 x))
  have hbaseB_nonneg : 0 ≤ baseB := by
    dsimp [baseB]
    have hratio : 0 ≤ vecNorm2 b / (frobNormRect A * vecNorm2 x) := by
      exact div_nonneg (vecNorm2_nonneg b)
        (le_of_lt (mul_pos hApos hxpos))
    linarith
  have htermA_nonneg : 0 ≤ termA := by
    dsimp [termA]
    apply mul_nonneg
    · exact theorem20_8KappaA_nonneg B BAplus
    · have hratio : 0 ≤ vecNorm2 d / (frobNormRect B * vecNorm2 x) := by
        exact div_nonneg (vecNorm2_nonneg d)
          (mul_nonneg (frobNormRect_nonneg B) (le_of_lt hxpos))
      linarith
  have htermR_nonneg : 0 ≤ termR := by
    dsimp [termR]
    exact mul_nonneg
      (theorem20_8ResidualAmplifier_nonneg A B APplus BAplus hApos)
      (div_nonneg (vecNorm2_nonneg r)
        (le_of_lt (mul_pos hApos hxpos)))
  have hsecond :
      theorem20_8KappaB A APplus * baseB ≤ termB := by
    rfl
  change theorem20_8KappaB A APplus * baseB ≤
    theorem20_8FirstOrderRHS A b B d x r APplus BAplus
  unfold theorem20_8FirstOrderRHS
  change theorem20_8KappaB A APplus * baseB ≤ termA + termB + termR
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8, equation (20.25):
    the source-normalized residual-amplification term is one summand of the
    first-order coefficient. -/
theorem theorem20_8Residual_sourceTerm_le_firstOrderRHS {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    (hApos : 0 < frobNormRect A) (hBpos : 0 < frobNormRect B)
    (hxpos : 0 < vecNorm2 x) :
    theorem20_8ResidualAmplifier A B APplus BAplus *
        (vecNorm2 r / (frobNormRect A * vecNorm2 x)) ≤
      theorem20_8FirstOrderRHS A b B d x r APplus BAplus := by
  let termA : ℝ := theorem20_8KappaA B BAplus *
    (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1)
  let termB : ℝ := theorem20_8KappaB A APplus *
    (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1)
  let termR : ℝ := theorem20_8ResidualAmplifier A B APplus BAplus *
    (vecNorm2 r / (frobNormRect A * vecNorm2 x))
  have htermA_nonneg : 0 ≤ termA := by
    dsimp [termA]
    apply mul_nonneg
    · exact theorem20_8KappaA_nonneg B BAplus
    · have hratio : 0 ≤ vecNorm2 d / (frobNormRect B * vecNorm2 x) := by
        exact div_nonneg (vecNorm2_nonneg d)
          (le_of_lt (mul_pos hBpos hxpos))
      linarith
  have htermB_nonneg : 0 ≤ termB := by
    dsimp [termB]
    apply mul_nonneg
    · linarith [theorem20_8KappaB_nonneg A APplus]
    · have hratio : 0 ≤ vecNorm2 b / (frobNormRect A * vecNorm2 x) := by
        exact div_nonneg (vecNorm2_nonneg b)
          (le_of_lt (mul_pos hApos hxpos))
      linarith
  change termR ≤ theorem20_8FirstOrderRHS A b B d x r APplus BAplus
  unfold theorem20_8FirstOrderRHS
  change termR ≤ termA + termB + termR
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8, equation (20.25):
    multiplying the residual-amplification summand by `eps * ||x||_2`
    is bounded by the full first-order coefficient with the same scaling. -/
theorem theorem20_8Residual_sourceTerm_scaled_le_firstOrderRHS {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    {eps : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hBpos : 0 < frobNormRect B)
    (hxpos : 0 < vecNorm2 x) :
    eps * theorem20_8ResidualAmplifier A B APplus BAplus *
        (vecNorm2 r / (frobNormRect A * vecNorm2 x)) * vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x r APplus BAplus *
        vecNorm2 x := by
  have hfirst :
      theorem20_8ResidualAmplifier A B APplus BAplus *
          (vecNorm2 r / (frobNormRect A * vecNorm2 x)) ≤
        theorem20_8FirstOrderRHS A b B d x r APplus BAplus :=
    theorem20_8Residual_sourceTerm_le_firstOrderRHS A b B d x r APplus
      BAplus hApos hBpos hxpos
  have hmul := mul_le_mul_of_nonneg_left hfirst heps_nonneg
  have hmulx := mul_le_mul_of_nonneg_right hmul (le_of_lt hxpos)
  simpa [mul_assoc] using hmulx
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8, equation (20.25):
    the scaled residual summand is the same as the source residual radius
    `eps * residualAmplifier * ||r||_2 / ||A||_F`. -/
theorem theorem20_8Residual_sourceTerm_scaled_eq {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hxpos : 0 < vecNorm2 x) :
    eps * theorem20_8ResidualAmplifier A B APplus BAplus *
        (vecNorm2 r / (frobNormRect A * vecNorm2 x)) * vecNorm2 x =
      eps * theorem20_8ResidualAmplifier A B APplus BAplus *
        (vecNorm2 r / frobNormRect A) := by
  field_simp [ne_of_gt hApos, ne_of_gt hxpos,
    mul_ne_zero (ne_of_gt hApos) (ne_of_gt hxpos)]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8, equation (20.25):
    direct comparison between the source residual radius
    `eps * residualAmplifier * ||r||_2 / ||A||_F` and the full first-order
    coefficient multiplied by `eps * ||x||_2`. -/
theorem theorem20_8Residual_sourceRadius_le_firstOrderRHS_scaled {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    {eps : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hBpos : 0 < frobNormRect B)
    (hxpos : 0 < vecNorm2 x) :
    eps * theorem20_8ResidualAmplifier A B APplus BAplus *
        (vecNorm2 r / frobNormRect A) ≤
      eps * theorem20_8FirstOrderRHS A b B d x r APplus BAplus *
        vecNorm2 x := by
  have hscaled :
      eps * theorem20_8ResidualAmplifier A B APplus BAplus *
          (vecNorm2 r / (frobNormRect A * vecNorm2 x)) * vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x r APplus BAplus *
          vecNorm2 x :=
    theorem20_8Residual_sourceTerm_scaled_le_firstOrderRHS A b B d x r
      APplus BAplus heps_nonneg hApos hBpos hxpos
  simpa [theorem20_8Residual_sourceTerm_scaled_eq A B x r APplus BAplus
    hApos hxpos] using hscaled
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8, equation (20.25):
    the sum of the three printed first-order source coefficients is exactly
    the first-order coefficient `theorem20_8FirstOrderRHS`. -/
theorem theorem20_8SourceCoefficientSum_eq_firstOrderRHS {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ) :
    theorem20_8KappaA B BAplus *
          (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) +
        theorem20_8KappaB A APplus *
          (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) +
        theorem20_8ResidualAmplifier A B APplus BAplus *
          (vecNorm2 r / (frobNormRect A * vecNorm2 x)) =
      theorem20_8FirstOrderRHS A b B d x r APplus BAplus := by
  rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8, equation (20.25):
    after multiplication by `eps * ||x||_2`, the integrated source coefficient
    sum is still exactly the full first-order coefficient with the same
    scaling. -/
theorem theorem20_8SourceCoefficientSum_scaled_eq_firstOrderRHS {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    {eps : ℝ} :
    eps *
        (theorem20_8KappaA B BAplus *
            (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) +
          theorem20_8KappaB A APplus *
            (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) +
          theorem20_8ResidualAmplifier A B APplus BAplus *
            (vecNorm2 r / (frobNormRect A * vecNorm2 x))) *
        vecNorm2 x =
      eps * theorem20_8FirstOrderRHS A b B d x r APplus BAplus *
        vecNorm2 x := by
  rw [theorem20_8SourceCoefficientSum_eq_firstOrderRHS]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8, equation (20.25):
    the sum of the three printed first-order source coefficients is bounded
    by the single first-order coefficient `theorem20_8FirstOrderRHS`. -/
theorem theorem20_8SourceCoefficientSum_le_firstOrderRHS {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    (hApos : 0 < frobNormRect A) (hxpos : 0 < vecNorm2 x) :
    theorem20_8KappaA B BAplus *
          (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) +
        theorem20_8KappaB A APplus *
          (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) +
        theorem20_8ResidualAmplifier A B APplus BAplus *
          (vecNorm2 r / (frobNormRect A * vecNorm2 x)) ≤
      theorem20_8FirstOrderRHS A b B d x r APplus BAplus := by
  let termA : ℝ := theorem20_8KappaA B BAplus *
    (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1)
  let baseB : ℝ := vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1
  let termBsource : ℝ := theorem20_8KappaB A APplus * baseB
  let termBfull : ℝ := theorem20_8KappaB A APplus * baseB
  let termR : ℝ := theorem20_8ResidualAmplifier A B APplus BAplus *
    (vecNorm2 r / (frobNormRect A * vecNorm2 x))
  have hbaseB_nonneg : 0 ≤ baseB := by
    dsimp [baseB]
    have hratio : 0 ≤ vecNorm2 b / (frobNormRect A * vecNorm2 x) := by
      exact div_nonneg (vecNorm2_nonneg b)
        (le_of_lt (mul_pos hApos hxpos))
    linarith
  have hBsource_le_full : termBsource ≤ termBfull := by
    rfl
  change termA + termBsource + termR ≤
    theorem20_8FirstOrderRHS A b B d x r APplus BAplus
  unfold theorem20_8FirstOrderRHS
  change termA + termBsource + termR ≤ termA + termBfull + termR
  linarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8, equation (20.25):
    after multiplication by `eps * ||x||_2`, the integrated source coefficient
    sum is bounded by the full first-order coefficient with the same scaling. -/
theorem theorem20_8SourceCoefficientSum_scaled_le_firstOrderRHS {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    {eps : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hxpos : 0 < vecNorm2 x) :
    eps *
        (theorem20_8KappaA B BAplus *
            (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) +
          theorem20_8KappaB A APplus *
            (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) +
          theorem20_8ResidualAmplifier A B APplus BAplus *
            (vecNorm2 r / (frobNormRect A * vecNorm2 x))) *
        vecNorm2 x ≤
      eps * theorem20_8FirstOrderRHS A b B d x r APplus BAplus *
        vecNorm2 x := by
  have hcoeff :
      theorem20_8KappaA B BAplus *
            (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) +
          theorem20_8KappaB A APplus *
            (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) +
          theorem20_8ResidualAmplifier A B APplus BAplus *
            (vecNorm2 r / (frobNormRect A * vecNorm2 x)) ≤
        theorem20_8FirstOrderRHS A b B d x r APplus BAplus :=
    theorem20_8SourceCoefficientSum_le_firstOrderRHS A b B d x r APplus
      BAplus hApos hxpos
  have hmul := mul_le_mul_of_nonneg_left hcoeff heps_nonneg
  have hmulx := mul_le_mul_of_nonneg_right hmul (le_of_lt hxpos)
  simpa [mul_assoc] using hmulx
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8, equation (20.25):
    source-radius form of the integrated direct, data-forcing, and residual
    first-order components, bounded by the full first-order RHS scaling. -/
theorem theorem20_8SourceRadiiSum_le_firstOrderRHS_scaled {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    {eps : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hxpos : 0 < vecNorm2 x) :
    eps * theorem20_8KappaA B BAplus *
          (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) * vecNorm2 x +
        eps * theorem20_8KappaB A APplus *
          (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) * vecNorm2 x +
        eps * theorem20_8ResidualAmplifier A B APplus BAplus *
          (vecNorm2 r / frobNormRect A) ≤
      eps * theorem20_8FirstOrderRHS A b B d x r APplus BAplus *
        vecNorm2 x := by
  let termA : ℝ := theorem20_8KappaA B BAplus *
    (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1)
  let termB : ℝ := theorem20_8KappaB A APplus *
    (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1)
  let termR : ℝ := theorem20_8ResidualAmplifier A B APplus BAplus *
    (vecNorm2 r / (frobNormRect A * vecNorm2 x))
  have hscaled :
      eps * (termA + termB + termR) * vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x r APplus BAplus *
          vecNorm2 x := by
    exact theorem20_8SourceCoefficientSum_scaled_le_firstOrderRHS
      A b B d x r APplus BAplus heps_nonneg hApos hxpos
  have hres :
      eps * termR * vecNorm2 x =
        eps * theorem20_8ResidualAmplifier A B APplus BAplus *
          (vecNorm2 r / frobNormRect A) := by
    simpa [termR, mul_assoc] using
      theorem20_8Residual_sourceTerm_scaled_eq A B x r APplus BAplus
        hApos hxpos
  have hsum :
      eps * termA * vecNorm2 x + eps * termB * vecNorm2 x +
          eps * theorem20_8ResidualAmplifier A B APplus BAplus *
            (vecNorm2 r / frobNormRect A) =
        eps * (termA + termB + termR) * vecNorm2 x := by
    rw [← hres]
    ring
  calc
    eps * theorem20_8KappaA B BAplus *
          (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) * vecNorm2 x +
        eps * theorem20_8KappaB A APplus *
          (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) * vecNorm2 x +
        eps * theorem20_8ResidualAmplifier A B APplus BAplus *
          (vecNorm2 r / frobNormRect A) =
        eps * termA * vecNorm2 x + eps * termB * vecNorm2 x +
          eps * theorem20_8ResidualAmplifier A B APplus BAplus *
            (vecNorm2 r / frobNormRect A) := by
      dsimp [termA, termB]
      ring
    _ = eps * (termA + termB + termR) * vecNorm2 x := hsum
    _ ≤ eps * theorem20_8FirstOrderRHS A b B d x r APplus BAplus *
        vecNorm2 x := hscaled
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the Higham-sign data forcing `Deltab - DeltaA*y` has the same reduced
    correction norm as the opposite-sign vector used by the older conditional
    handoff. -/
theorem theorem20_8_vecNorm2_APplus_higham_data_forcing_eq {m n : ℕ}
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (y : Fin n → ℝ) :
    vecNorm2
        (rectMatMulVec APplus
          (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i)) =
      vecNorm2
        (rectMatMulVec APplus
          (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i)) := by
  let forcing : Fin m → ℝ :=
    fun i => rectMatMulVec DeltaA y i - Deltab i
  have hforcing :
      (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i) =
        fun i => (-1 : ℝ) * forcing i := by
    funext i
    dsimp [forcing]
    ring
  calc
    vecNorm2
        (rectMatMulVec APplus
          (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i))
        = vecNorm2
            (rectMatMulVec APplus (fun i : Fin m => (-1 : ℝ) * forcing i)) := by
            rw [hforcing]
    _ = vecNorm2 (fun j : Fin n => (-1 : ℝ) * rectMatMulVec APplus forcing j) := by
            rw [rectMatMulVec_smul]
    _ = vecNorm2 (rectMatMulVec APplus forcing) := by
            simpa using vecNorm2_neg (rectMatMulVec APplus forcing)
    _ = vecNorm2
          (rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i)) := by
            rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the packaged direct/data remainder has the explicit `eps^2` coefficient
    expected from the source `O(eps^2)` term, once the separate
    solution-difference radius has been supplied. -/
theorem theorem20_8_quadratic_remainder_relative_eq_eps_sq_coefficient
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (x : Fin n → ℝ)
    {eps solutionRadius : ℝ}
    (hxpos : 0 < vecNorm2 x) :
    (complexMatrixOp2
          (realRectToCMatrix (theorem20_8BAplus A B Bplus APplus)) *
        ((eps * frobNormRect B) *
          (eps * solutionRadius * vecNorm2 x)) +
      complexMatrixOp2 (realRectToCMatrix APplus) *
        ((eps * frobNormRect A) *
          (eps * solutionRadius * vecNorm2 x))) /
      vecNorm2 x =
    eps ^ 2 * solutionRadius *
      (complexMatrixOp2
          (realRectToCMatrix (theorem20_8BAplus A B Bplus APplus)) *
          frobNormRect B +
        complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  field_simp [ne_of_gt hxpos]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the relative-radius direct/data remainder has an explicit
    `eps * relativeRadius` coefficient.  This is the algebraic shape needed by
    KKT routes that first bound `||y - x||₂ / ||x||₂`. -/
theorem theorem20_8_relative_remainder_eq_eps_radius_coefficient
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (x : Fin n → ℝ)
    {eps relativeRadius : ℝ}
    (hxpos : 0 < vecNorm2 x) :
    (complexMatrixOp2
          (realRectToCMatrix (theorem20_8BAplus A B Bplus APplus)) *
        ((eps * frobNormRect B) *
          (relativeRadius * vecNorm2 x)) +
      complexMatrixOp2 (realRectToCMatrix APplus) *
        ((eps * frobNormRect A) *
          (relativeRadius * vecNorm2 x))) /
      vecNorm2 x =
    eps * relativeRadius *
      (complexMatrixOp2
          (realRectToCMatrix (theorem20_8BAplus A B Bplus APplus)) *
          frobNormRect B +
        complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A) := by
  field_simp [ne_of_gt hxpos]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    if the reduced-problem pseudoinverse equation has supplied the projected
    feasible-difference component, then the full feasible difference is exactly
    the printed `B_A^+` direct correction plus the `(AP)^+` data correction. -/
theorem theorem20_8_solution_difference_eq_BAplus_add_APplus_of_projected_difference
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (_b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hproj :
      rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k) =
        fun j : Fin n =>
          rectMatMulVec APplus
              (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
            rectMatMulVec APplus
              (rectMatMulVec A
                (rectMatMulVec Bplus
                  (fun l : Fin p =>
                    Deltad l - rectMatMulVec DeltaB y l))) j) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j := by
  let defect : Fin p → ℝ :=
    fun i => Deltad i - rectMatMulVec DeltaB y i
  have hdecomp :=
    theorem20_8_perturbed_feasible_difference_decomp
      B DeltaB Bplus d Deltad x y hx hy
  have hBA :=
    theorem20_8BAplus_apply A B Bplus APplus defect
  ext j
  have hdecomp_j := congrFun hdecomp j
  have hproj_j := congrFun hproj j
  have hBA_j := congrFun hBA j
  change
    y j - x j =
      rectMatMulVec (theorem20_8BAplus A B Bplus APplus) defect j +
        rectMatMulVec APplus
          (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j
  rw [hdecomp_j, hproj_j, hBA_j]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    residual-explicit exact solution-difference identity.  This is the exact
    algebraic counterpart of the printed correction-vector identity before the
    reduced-LS/Wedin forcing equation removes the visible residual terms. -/
theorem theorem20_8_solution_difference_eq_BAplus_add_APplus_of_perturbed_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (x y : Fin n → ℝ) (rHigh : Fin m → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B Bplus) =
        theorem20_8Projection B Bplus)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m =>
              (b i - rectMatMulVec A x i) - rHigh i -
                rectMatMulVec DeltaA y i + Deltab i) j := by
  let defect : Fin p → ℝ :=
    fun i => Deltad i - rectMatMulVec DeltaB y i
  let forcing : Fin m → ℝ :=
    fun i => (b i - rectMatMulVec A x i) - rHigh i -
      rectMatMulVec DeltaA y i + Deltab i
  let correction : Fin m → ℝ :=
    rectMatMulVec A (rectMatMulVec Bplus defect)
  have hdecomp :=
    theorem20_8_perturbed_feasible_difference_decomp
      B DeltaB Bplus d Deltad x y hx hy
  have hAPdiff :=
    theorem20_8_AP_difference_eq_of_perturbed_higham_residual_eq
      A DeltaA b Deltab B DeltaB Bplus d Deltad x y rHigh hx hy hres
  have hAPdiff_split :
      rectMatMulVec (theorem20_8AP A B Bplus) (fun k => y k - x k) =
        fun i : Fin m => forcing i - correction i := by
    ext i
    have hi := congrFun hAPdiff i
    dsimp [forcing, correction, defect] at hi ⊢
    linarith
  have hproj :
      rectMatMulVec (theorem20_8Projection B Bplus) (fun k => y k - x k) =
        fun j : Fin n =>
          rectMatMulVec APplus forcing j -
            rectMatMulVec APplus correction j := by
    calc
      rectMatMulVec (theorem20_8Projection B Bplus) (fun k => y k - x k) =
          rectMatMulVec (rectMatMul APplus (theorem20_8AP A B Bplus))
            (fun k => y k - x k) := by
            rw [hAPleft]
      _ = rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B Bplus)
              (fun k => y k - x k)) := by
            rw [rectMatMulVec_rectMatMul]
      _ = rectMatMulVec APplus (fun i : Fin m => forcing i - correction i) := by
            rw [hAPdiff_split]
      _ = fun j : Fin n =>
            rectMatMulVec APplus forcing j -
              rectMatMulVec APplus correction j := by
            rw [rectMatMulVec_sub]
  have hBA :=
    theorem20_8BAplus_apply A B Bplus APplus defect
  ext j
  have hdecomp_j := congrFun hdecomp j
  have hproj_j := congrFun hproj j
  have hBA_j := congrFun hBA j
  change
    y j - x j =
      rectMatMulVec (theorem20_8BAplus A B Bplus APplus) defect j +
        rectMatMulVec APplus forcing j
  rw [hdecomp_j, hproj_j, hBA_j]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    residual-explicit norm bound for the exact solution-difference identity.
    The bound keeps the visible Higham-sign residual forcing as a separate
    supplied radius. -/
theorem theorem20_8_vecNorm2_solution_difference_residual_forcing_le
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (x y : Fin n → ℝ) (rHigh : Fin m → ℝ)
    {BAplus_norm DeltaB_norm Deltad_norm forcing_norm : ℝ}
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B Bplus) =
        theorem20_8Projection B Bplus)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hBAplus_nonneg : 0 ≤ BAplus_norm)
    (hBAplus :
      rectOpNorm2Le (theorem20_8BAplus A B Bplus APplus) BAplus_norm)
    (hDeltaB : rectOpNorm2Le DeltaB DeltaB_norm)
    (hDeltad : vecNorm2 Deltad ≤ Deltad_norm)
    (hforcing :
      vecNorm2
          (fun i : Fin m =>
            (b i - rectMatMulVec A x i) - rHigh i -
              rectMatMulVec DeltaA y i + Deltab i) ≤ forcing_norm) :
    vecNorm2 (fun j : Fin n => y j - x j) ≤
      BAplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) +
        complexMatrixOp2 (realRectToCMatrix APplus) * forcing_norm := by
  let defect : Fin p → ℝ :=
    fun i => Deltad i - rectMatMulVec DeltaB y i
  let forcing : Fin m → ℝ :=
    fun i => (b i - rectMatMulVec A x i) - rHigh i -
      rectMatMulVec DeltaA y i + Deltab i
  let BAplus := theorem20_8BAplus A B Bplus APplus
  have hsol :=
    theorem20_8_solution_difference_eq_BAplus_add_APplus_of_perturbed_higham_residual_eq
      A DeltaA b Deltab B DeltaB Bplus APplus d Deltad x y rHigh
      hAPleft hx hy hres
  have hdirect :
      vecNorm2 (rectMatMulVec BAplus defect) ≤
        BAplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) := by
    exact theorem20_8_vecNorm2_BAplus_constraint_defect_le
      DeltaB BAplus Deltad y hBAplus_nonneg hBAplus hDeltaB hDeltad
  have hop_nonneg : 0 ≤ complexMatrixOp2 (realRectToCMatrix APplus) :=
    complexMatrixOp2_nonneg (realRectToCMatrix APplus)
  have hforcing_bound :
      vecNorm2 (rectMatMulVec APplus forcing) ≤
        complexMatrixOp2 (realRectToCMatrix APplus) * forcing_norm := by
    calc
      vecNorm2 (rectMatMulVec APplus forcing)
          ≤ complexMatrixOp2 (realRectToCMatrix APplus) * vecNorm2 forcing :=
              rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
                APplus le_rfl forcing
      _ ≤ complexMatrixOp2 (realRectToCMatrix APplus) * forcing_norm :=
              mul_le_mul_of_nonneg_left hforcing hop_nonneg
  calc
    vecNorm2 (fun j : Fin n => y j - x j) =
        vecNorm2 (fun j : Fin n =>
          rectMatMulVec BAplus defect j + rectMatMulVec APplus forcing j) := by
          rw [hsol]
    _ ≤ vecNorm2 (rectMatMulVec BAplus defect) +
          vecNorm2 (rectMatMulVec APplus forcing) :=
          vecNorm2_add_le (rectMatMulVec BAplus defect)
            (rectMatMulVec APplus forcing)
    _ ≤ BAplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) +
          complexMatrixOp2 (realRectToCMatrix APplus) * forcing_norm :=
          add_le_add hdirect hforcing_bound
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the projected-difference equation follows from the reduced `AP` equation
    once `(AP)^+ AP` is identified with the source nullspace projector `P`. -/
theorem theorem20_8_projected_difference_eq_APplus_of_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B Bplus) =
        theorem20_8Projection B Bplus)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B Bplus)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B Bplus)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  let diff : Fin n → ℝ := fun k => y k - x k
  let defect : Fin p → ℝ :=
    fun l => Deltad l - rectMatMulVec DeltaB y l
  let forcing : Fin m → ℝ := fun i => rectMatMulVec DeltaA y i - Deltab i
  let correction : Fin m → ℝ :=
    rectMatMulVec A (rectMatMulVec Bplus defect)
  calc
    rectMatMulVec (theorem20_8Projection B Bplus) diff =
        rectMatMulVec (rectMatMul APplus (theorem20_8AP A B Bplus)) diff := by
          rw [hAPleft]
    _ = rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus) diff) := by
          rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec APplus (fun i : Fin m => forcing i - correction i) := by
          rw [hAPdiff]
    _ = fun j : Fin n =>
          rectMatMulVec APplus forcing j -
            rectMatMulVec APplus correction j := by
          rw [rectMatMulVec_sub]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    residual-explicit projected-difference bridge in Higham's residual sign
    convention.  This is the exact version before the reduced-LS/Wedin route
    supplies the stronger source forcing equation. -/
theorem theorem20_8_projected_difference_eq_APplus_of_perturbed_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ) (rHigh : Fin m → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B Bplus) =
        theorem20_8Projection B Bplus)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh) :
    rectMatMulVec (theorem20_8Projection B Bplus)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m =>
              (b i - rectMatMulVec A x i) - rHigh i -
                rectMatMulVec DeltaA y i + Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  let diff : Fin n → ℝ := fun k => y k - x k
  let defect : Fin p → ℝ :=
    fun l => Deltad l - rectMatMulVec DeltaB y l
  let forcing : Fin m → ℝ :=
    fun i => (b i - rectMatMulVec A x i) - rHigh i -
      rectMatMulVec DeltaA y i + Deltab i
  let correction : Fin m → ℝ :=
    rectMatMulVec A (rectMatMulVec Bplus defect)
  have hAPdiff :=
    theorem20_8_AP_difference_eq_of_perturbed_higham_residual_eq
      A DeltaA b Deltab B DeltaB Bplus d Deltad x y rHigh hx hy hres
  have hAPdiff_split :
      rectMatMulVec (theorem20_8AP A B Bplus) diff =
        fun i : Fin m => forcing i - correction i := by
    ext i
    have hi := congrFun hAPdiff i
    dsimp [diff, forcing, correction, defect] at hi ⊢
    linarith
  calc
    rectMatMulVec (theorem20_8Projection B Bplus) diff =
        rectMatMulVec (rectMatMul APplus (theorem20_8AP A B Bplus)) diff := by
          rw [hAPleft]
    _ = rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus) diff) := by
          rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec APplus (fun i : Fin m => forcing i - correction i) := by
          rw [hAPdiff_split]
    _ = fun j : Fin n =>
          rectMatMulVec APplus forcing j -
            rectMatMulVec APplus correction j := by
          rw [rectMatMulVec_sub]
    _ = fun j : Fin n =>
          rectMatMulVec APplus
              (fun i : Fin m =>
                (b i - rectMatMulVec A x i) - rHigh i -
                  rectMatMulVec DeltaA y i + Deltab i) j -
            rectMatMulVec APplus
              (rectMatMulVec A
                (rectMatMulVec Bplus
                  (fun l : Fin p =>
                    Deltad l - rectMatMulVec DeltaB y l))) j := by
          rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    projected same-residual bridge in Higham's residual sign convention.
    This is the source-residual specialization of the residual-explicit bridge,
    with forcing `Deltab - DeltaA*y`. -/
theorem theorem20_8_projected_difference_eq_APplus_of_same_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B Bplus) =
        theorem20_8Projection B Bplus)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hsame : r = rHigh) :
    rectMatMulVec (theorem20_8Projection B Bplus)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  let diff : Fin n → ℝ := fun k => y k - x k
  let defect : Fin p → ℝ :=
    fun l => Deltad l - rectMatMulVec DeltaB y l
  let forcing : Fin m → ℝ := fun i => Deltab i - rectMatMulVec DeltaA y i
  let correction : Fin m → ℝ :=
    rectMatMulVec A (rectMatMulVec Bplus defect)
  have hAPdiff :=
    theorem20_8_AP_difference_eq_of_same_higham_residual_eq
      A DeltaA b Deltab B DeltaB Bplus d Deltad x y r rHigh
      hx hy hr hres hsame
  have hAPdiff_split :
      rectMatMulVec (theorem20_8AP A B Bplus) diff =
        fun i : Fin m => forcing i - correction i := by
    ext i
    have hi := congrFun hAPdiff i
    dsimp [diff, forcing, correction, defect] at hi ⊢
    linarith
  calc
    rectMatMulVec (theorem20_8Projection B Bplus) diff =
        rectMatMulVec (rectMatMul APplus (theorem20_8AP A B Bplus)) diff := by
          rw [hAPleft]
    _ = rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus) diff) := by
          rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec APplus (fun i : Fin m => forcing i - correction i) := by
          rw [hAPdiff_split]
    _ = fun j : Fin n =>
          rectMatMulVec APplus forcing j -
            rectMatMulVec APplus correction j := by
          rw [rectMatMulVec_sub]
    _ = fun j : Fin n =>
          rectMatMulVec APplus
              (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i) j -
            rectMatMulVec APplus
              (rectMatMulVec A
                (rectMatMulVec Bplus
                  (fun l : Fin p =>
                    Deltad l - rectMatMulVec DeltaB y l))) j := by
          rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    projected same-residual bridge using only the projected action of
    `(AP)^+ AP` on the actual feasible difference.  This is the vector-action
    counterpart of `theorem20_8_projected_difference_eq_APplus_of_same_higham_residual_eq`. -/
theorem theorem20_8_projected_difference_eq_APplus_of_same_higham_residual_projected_action
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    (hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k))
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hsame : r = rHigh) :
    rectMatMulVec (theorem20_8Projection B Bplus)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  let diff : Fin n → ℝ := fun k => y k - x k
  let defect : Fin p → ℝ :=
    fun l => Deltad l - rectMatMulVec DeltaB y l
  let forcing : Fin m → ℝ := fun i => Deltab i - rectMatMulVec DeltaA y i
  let correction : Fin m → ℝ :=
    rectMatMulVec A (rectMatMulVec Bplus defect)
  have hAPdiff :=
    theorem20_8_AP_difference_eq_of_same_higham_residual_eq
      A DeltaA b Deltab B DeltaB Bplus d Deltad x y r rHigh
      hx hy hr hres hsame
  have hAPdiff_split :
      rectMatMulVec (theorem20_8AP A B Bplus) diff =
        fun i : Fin m => forcing i - correction i := by
    ext i
    have hi := congrFun hAPdiff i
    dsimp [diff, forcing, correction, defect] at hi ⊢
    linarith
  calc
    rectMatMulVec (theorem20_8Projection B Bplus) diff =
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus) diff) := by
          exact hAPaction.symm
    _ = rectMatMulVec APplus (fun i : Fin m => forcing i - correction i) := by
          rw [hAPdiff_split]
    _ = fun j : Fin n =>
          rectMatMulVec APplus forcing j -
            rectMatMulVec APplus correction j := by
          rw [rectMatMulVec_sub]
    _ = fun j : Fin n =>
          rectMatMulVec APplus
              (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i) j -
            rectMatMulVec APplus
              (rectMatMulVec A
                (rectMatMulVec Bplus
                  (fun l : Fin p =>
                    Deltad l - rectMatMulVec DeltaB y l))) j := by
          rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    exact same-residual solution-difference identity in Higham's residual sign
    convention.  It specializes the residual-explicit identity to equal source
    and perturbed residuals, giving the correction vector with forcing
    `Deltab - DeltaA*y`. -/
theorem theorem20_8_solution_difference_eq_BAplus_add_APplus_of_same_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B Bplus) =
        theorem20_8Projection B Bplus)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hsame : r = rHigh) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i) j := by
  let defect : Fin p → ℝ :=
    fun i => Deltad i - rectMatMulVec DeltaB y i
  let forcing : Fin m → ℝ := fun i => Deltab i - rectMatMulVec DeltaA y i
  have hdecomp :=
    theorem20_8_perturbed_feasible_difference_decomp
      B DeltaB Bplus d Deltad x y hx hy
  have hproj :=
    theorem20_8_projected_difference_eq_APplus_of_same_higham_residual_eq
      A DeltaA b Deltab B DeltaB Bplus APplus d Deltad x y r rHigh
      hAPleft hx hy hr hres hsame
  have hBA :=
    theorem20_8BAplus_apply A B Bplus APplus defect
  ext j
  have hdecomp_j := congrFun hdecomp j
  have hproj_j := congrFun hproj j
  have hBA_j := congrFun hBA j
  change
    y j - x j =
      rectMatMulVec (theorem20_8BAplus A B Bplus APplus) defect j +
        rectMatMulVec APplus forcing j
  rw [hdecomp_j, hproj_j, hBA_j]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    exact same-residual solution-difference identity using only the projected
    action of `(AP)^+ AP` on the actual feasible difference. -/
theorem theorem20_8_solution_difference_eq_BAplus_add_APplus_of_same_higham_residual_projected_action
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    (hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k))
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hsame : r = rHigh) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i) j := by
  let defect : Fin p → ℝ :=
    fun i => Deltad i - rectMatMulVec DeltaB y i
  let forcing : Fin m → ℝ := fun i => Deltab i - rectMatMulVec DeltaA y i
  have hdecomp :=
    theorem20_8_perturbed_feasible_difference_decomp
      B DeltaB Bplus d Deltad x y hx hy
  have hproj :=
    theorem20_8_projected_difference_eq_APplus_of_same_higham_residual_projected_action
      A DeltaA b Deltab B DeltaB Bplus APplus d Deltad x y r rHigh
      hAPaction hx hy hr hres hsame
  have hBA :=
    theorem20_8BAplus_apply A B Bplus APplus defect
  ext j
  have hdecomp_j := congrFun hdecomp j
  have hproj_j := congrFun hproj j
  have hBA_j := congrFun hBA j
  change
    y j - x j =
      rectMatMulVec (theorem20_8BAplus A B Bplus APplus) defect j +
        rectMatMulVec APplus forcing j
  rw [hdecomp_j, hproj_j, hBA_j]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    a source-shaped sufficient condition for the projected action
    `(AP)^+ AP v = P v`.  It is enough for `(AP)^+` to be a left inverse of
    `A` on the homogeneous constraint nullspace, since `P v` lies there. -/
theorem theorem20_8_projected_action_of_nullspace_left_inverse
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus (rectMatMulVec A z) = z)
    (v : Fin n → ℝ) :
    rectMatMulVec APplus
        (rectMatMulVec (theorem20_8AP A B Bplus) v) =
      rectMatMulVec (theorem20_8Projection B Bplus) v := by
  let z : Fin n → ℝ :=
    rectMatMulVec (theorem20_8Projection B Bplus) v
  have hz : rectMatMulVec B z = (fun _i : Fin p => 0) :=
    theorem20_8Projection_constraint_vec_zero B Bplus hright v
  have hAP :
      rectMatMulVec (theorem20_8AP A B Bplus) v =
        rectMatMulVec A z := by
    rw [theorem20_8AP, rectMatMulVec_rectMatMul]
  rw [hAP]
  exact hleft_null z hz
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-facing projected action from the reduced operator.  It is enough for
    `(AP)^+` to left-invert `AP` on the homogeneous constraint nullspace,
    since the projector `P` maps every vector into that nullspace. -/
theorem theorem20_8_projected_action_of_AP_left_inverse_on_nullspace
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B Bplus) z) = z)
    (v : Fin n → ℝ) :
    rectMatMulVec APplus
        (rectMatMulVec (theorem20_8AP A B Bplus) v) =
      rectMatMulVec (theorem20_8Projection B Bplus) v := by
  let z : Fin n → ℝ :=
    rectMatMulVec (theorem20_8Projection B Bplus) v
  have hz : rectMatMulVec B z = (fun _i : Fin p => 0) :=
    theorem20_8Projection_constraint_vec_zero B Bplus hright v
  have hAPv :
      rectMatMulVec (theorem20_8AP A B Bplus) v =
        rectMatMulVec (theorem20_8AP A B Bplus) z := by
    rw [theorem20_8AP, rectMatMulVec_rectMatMul]
    exact (theorem20_8AP_apply_nullspace A B Bplus z hz).symm
  rw [hAPv]
  exact hAPleft_null z hz
/-- Matrix extensionality through the finite vector action used by the local
    rectangular-matrix API. -/
theorem rectMatMul_eq_of_forall_rectMatMulVec_eq {m n : ℕ}
    (M N : Fin m → Fin n → ℝ)
    (h : ∀ v : Fin n → ℝ, rectMatMulVec M v = rectMatMulVec N v) :
    M = N := by
  ext i j
  have hv := congrFun (h (finiteBasisVec j)) i
  have hMcol := congrFun (rectMatMulVec_finiteBasisVec_gsColumn M j) i
  have hNcol := congrFun (rectMatMulVec_finiteBasisVec_gsColumn N j) i
  simpa [gsColumn] using hMcol.symm.trans (hv.trans hNcol)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the reduced source product `AP = A(I - B^+B)` is fixed on the right by
    the source projector `P = I - B^+B` whenever `B^+` is a right inverse. -/
theorem theorem20_8AP_mul_projection_eq_self {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p) :
    rectMatMul (theorem20_8AP A B Bplus)
        (theorem20_8Projection B Bplus) =
      theorem20_8AP A B Bplus := by
  apply rectMatMul_eq_of_forall_rectMatMulVec_eq
  intro x
  calc
    rectMatMulVec
        (rectMatMul (theorem20_8AP A B Bplus)
          (theorem20_8Projection B Bplus)) x =
        rectMatMulVec (theorem20_8AP A B Bplus)
          (rectMatMulVec (theorem20_8Projection B Bplus) x) := by
          exact rectMatMulVec_rectMatMul
            (theorem20_8AP A B Bplus) (theorem20_8Projection B Bplus) x
    _ = rectMatMulVec A
          (rectMatMulVec (theorem20_8Projection B Bplus)
            (rectMatMulVec (theorem20_8Projection B Bplus) x)) := by
          rw [theorem20_8AP, rectMatMulVec_rectMatMul]
    _ = rectMatMulVec A
          (rectMatMulVec (theorem20_8Projection B Bplus) x) := by
          rw [theorem20_8Projection_vec_idempotent B Bplus hright x]
    _ = rectMatMulVec (theorem20_8AP A B Bplus) x := by
          rw [theorem20_8AP, rectMatMulVec_rectMatMul]
/-- Higham, 2nd ed., Chapter 20, equation (20.24):
    matrix form of the projected action `(AP)^+ AP = P` from the reduced
    operator left-inverse condition on the homogeneous constraint nullspace. -/
theorem theorem20_8_APplus_AP_eq_projection_of_AP_left_inverse_on_nullspace
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B Bplus) z) = z) :
    rectMatMul APplus (theorem20_8AP A B Bplus) =
      theorem20_8Projection B Bplus := by
  apply rectMatMul_eq_of_forall_rectMatMulVec_eq
  intro v
  simpa [rectMatMulVec_rectMatMul] using
    theorem20_8_projected_action_of_AP_left_inverse_on_nullspace
      A B Bplus APplus hright hAPleft_null v
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    a Penrose-style route to the reduced-operator left-inverse condition on
    the homogeneous constraint nullspace.  If `AP * (AP)^+ * AP = AP`,
    `(AP)^+` maps into `null(B)`, and `AP` is injective on `null(B)`, then
    `(AP)^+` left-inverts `AP` on that nullspace.

    This is still conditional infrastructure: the source Moore--Penrose
    pseudoinverse and projector assumptions have to supply these hypotheses. -/
theorem theorem20_8_AP_left_inverse_on_nullspace_of_penrose1_range_null_injective
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hPenrose1 :
      rectMatMul (rectMatMul (theorem20_8AP A B Bplus) APplus)
          (theorem20_8AP A B Bplus) =
        theorem20_8AP A B Bplus)
    (hAPplus_range_null :
      ∀ w : Fin m → ℝ,
        rectMatMulVec B (rectMatMulVec APplus w) =
          (fun _i : Fin p => 0))
    (hAP_inj_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec (theorem20_8AP A B Bplus) z =
              (fun _i : Fin m => 0) →
            z = (fun _j : Fin n => 0)) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus) z) = z := by
  intro z hz
  let AP := theorem20_8AP A B Bplus
  let w : Fin m → ℝ := rectMatMulVec AP z
  let u : Fin n → ℝ := fun j => rectMatMulVec APplus w j - z j
  have hAP_penrose_vec :
      rectMatMulVec AP (rectMatMulVec APplus w) = w := by
    calc
      rectMatMulVec AP (rectMatMulVec APplus w) =
          rectMatMulVec (rectMatMul AP APplus) w := by
            exact (rectMatMulVec_rectMatMul AP APplus w).symm
      _ = rectMatMulVec (rectMatMul (rectMatMul AP APplus) AP) z := by
            dsimp [w]
            exact (rectMatMulVec_rectMatMul (rectMatMul AP APplus) AP z).symm
      _ = rectMatMulVec AP z := by
            rw [hPenrose1]
      _ = w := rfl
  have hB_u : rectMatMulVec B u = (fun _i : Fin p => 0) := by
    calc
      rectMatMulVec B u =
          (fun i : Fin p =>
            rectMatMulVec B (rectMatMulVec APplus w) i -
              rectMatMulVec B z i) := by
            rw [rectMatMulVec_sub]
      _ = (fun _i : Fin p => 0) := by
            funext i
            have hrange_i := congrFun (hAPplus_range_null w) i
            have hz_i := congrFun hz i
            rw [hrange_i, hz_i]
            ring
  have hAP_u : rectMatMulVec AP u = (fun _i : Fin m => 0) := by
    calc
      rectMatMulVec AP u =
          (fun i : Fin m =>
            rectMatMulVec AP (rectMatMulVec APplus w) i -
              rectMatMulVec AP z i) := by
            rw [rectMatMulVec_sub]
      _ = (fun _i : Fin m => 0) := by
            funext i
            have hpen_i := congrFun hAP_penrose_vec i
            rw [hpen_i]
            ring
  have hu : u = (fun _j : Fin n => 0) :=
    hAP_inj_null u hB_u hAP_u
  ext j
  have huj : rectMatMulVec APplus w j - z j = 0 := by
    simpa [u] using congrFun hu j
  exact sub_eq_zero.mp huj
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    projected action `(AP)^+ AP v = Pv` from Penrose-style reduced-operator
    hypotheses plus source right-invertibility of `B`. -/
theorem theorem20_8_projected_action_of_AP_penrose1_range_null_injective
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hPenrose1 :
      rectMatMul (rectMatMul (theorem20_8AP A B Bplus) APplus)
          (theorem20_8AP A B Bplus) =
        theorem20_8AP A B Bplus)
    (hAPplus_range_null :
      ∀ w : Fin m → ℝ,
        rectMatMulVec B (rectMatMulVec APplus w) =
          (fun _i : Fin p => 0))
    (hAP_inj_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec (theorem20_8AP A B Bplus) z =
              (fun _i : Fin m => 0) →
            z = (fun _j : Fin n => 0))
    (v : Fin n → ℝ) :
    rectMatMulVec APplus
        (rectMatMulVec (theorem20_8AP A B Bplus) v) =
      rectMatMulVec (theorem20_8Projection B Bplus) v := by
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B Bplus) z) = z :=
    theorem20_8_AP_left_inverse_on_nullspace_of_penrose1_range_null_injective
      A B Bplus APplus hPenrose1 hAPplus_range_null hAP_inj_null
  exact
    theorem20_8_projected_action_of_AP_left_inverse_on_nullspace
      A B Bplus APplus hright hAPleft_null v
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the projected-difference equation follows from the reduced `AP` equation
    when the reduced pseudoinverse acts as the source projector on the actual
    feasible difference `y - x`. -/
theorem theorem20_8_projected_difference_eq_APplus_of_projected_action_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k))
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B Bplus)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B Bplus)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  let diff : Fin n → ℝ := fun k => y k - x k
  let defect : Fin p → ℝ :=
    fun l => Deltad l - rectMatMulVec DeltaB y l
  let forcing : Fin m → ℝ := fun i => rectMatMulVec DeltaA y i - Deltab i
  let correction : Fin m → ℝ :=
    rectMatMulVec A (rectMatMulVec Bplus defect)
  calc
    rectMatMulVec (theorem20_8Projection B Bplus) diff =
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus) diff) := by
          rw [← hAPaction]
    _ = rectMatMulVec APplus (fun i : Fin m => forcing i - correction i) := by
          rw [hAPdiff]
    _ = fun j : Fin n =>
          rectMatMulVec APplus forcing j -
            rectMatMulVec APplus correction j := by
          rw [rectMatMulVec_sub]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the reduced `AP` equation gives the projected-difference equation when
    `(AP)^+` is a left inverse of `A` on the homogeneous constraint nullspace. -/
theorem theorem20_8_projected_difference_eq_APplus_of_nullspace_left_inverse_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus (rectMatMulVec A z) = z)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B Bplus)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B Bplus)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  have hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k) :=
    theorem20_8_projected_action_of_nullspace_left_inverse
      A B Bplus APplus hright hleft_null (fun k => y k - x k)
  exact
    theorem20_8_projected_difference_eq_APplus_of_projected_action_reduced_difference_eq
      A DeltaA Deltab B DeltaB Bplus APplus Deltad y x hAPaction hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the reduced `AP` equation gives the projected-difference equation when
    `(AP)^+` left-inverts `AP` on the homogeneous constraint nullspace. -/
theorem theorem20_8_projected_difference_eq_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B Bplus) z) = z)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B Bplus)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B Bplus)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  have hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k) :=
    theorem20_8_projected_action_of_AP_left_inverse_on_nullspace
      A B Bplus APplus hright hAPleft_null (fun k => y k - x k)
  exact
    theorem20_8_projected_difference_eq_APplus_of_projected_action_reduced_difference_eq
      A DeltaA Deltab B DeltaB Bplus APplus Deltad y x hAPaction hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the reduced `AP` equation gives the projected-difference equation when
    the projected action is derived from Penrose-style reduced-operator
    hypotheses. -/
theorem theorem20_8_projected_difference_eq_APplus_of_AP_penrose1_range_null_injective_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hPenrose1 :
      rectMatMul (rectMatMul (theorem20_8AP A B Bplus) APplus)
          (theorem20_8AP A B Bplus) =
        theorem20_8AP A B Bplus)
    (hAPplus_range_null :
      ∀ w : Fin m → ℝ,
        rectMatMulVec B (rectMatMulVec APplus w) =
          (fun _i : Fin p => 0))
    (hAP_inj_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec (theorem20_8AP A B Bplus) z =
              (fun _i : Fin m => 0) →
            z = (fun _j : Fin n => 0))
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B Bplus)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B Bplus)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  have hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k) :=
    theorem20_8_projected_action_of_AP_penrose1_range_null_injective
      A B Bplus APplus hright hPenrose1 hAPplus_range_null hAP_inj_null
      (fun k => y k - x k)
  exact
    theorem20_8_projected_difference_eq_APplus_of_projected_action_reduced_difference_eq
      A DeltaA Deltab B DeltaB Bplus APplus Deltad y x hAPaction hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    exact printed correction-vector identity from the reduced `AP` equation
    and the projected action needed only on the actual feasible difference. -/
theorem theorem20_8_solution_difference_eq_BAplus_add_APplus_of_projected_action_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k))
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B Bplus)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j := by
  have hproj :
      rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k) =
        fun j : Fin n =>
          rectMatMulVec APplus
              (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
            rectMatMulVec APplus
              (rectMatMulVec A
                (rectMatMulVec Bplus
                  (fun l : Fin p =>
                    Deltad l - rectMatMulVec DeltaB y l))) j :=
    theorem20_8_projected_difference_eq_APplus_of_projected_action_reduced_difference_eq
      A DeltaA Deltab B DeltaB Bplus APplus Deltad y x hAPaction hAPdiff
  exact
    theorem20_8_solution_difference_eq_BAplus_add_APplus_of_projected_difference
      A DeltaA b Deltab B DeltaB Bplus APplus d Deltad x y hx hy hproj
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    exact printed correction-vector identity from the reduced `AP` equation
    and a left inverse for `AP` on the homogeneous constraint nullspace. -/
theorem theorem20_8_solution_difference_eq_BAplus_add_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B Bplus) z) = z)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B Bplus)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j := by
  have hproj :
      rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k) =
        fun j : Fin n =>
          rectMatMulVec APplus
              (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
            rectMatMulVec APplus
              (rectMatMulVec A
                (rectMatMulVec Bplus
                  (fun l : Fin p =>
                    Deltad l - rectMatMulVec DeltaB y l))) j :=
    theorem20_8_projected_difference_eq_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
      A DeltaA Deltab B DeltaB Bplus APplus Deltad y x hright
      hAPleft_null hAPdiff
  exact
    theorem20_8_solution_difference_eq_BAplus_add_APplus_of_projected_difference
      A DeltaA b Deltab B DeltaB Bplus APplus d Deltad x y hx hy hproj
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    exact printed correction-vector identity from the reduced `AP` equation
    and Penrose-style reduced-operator hypotheses. -/
theorem theorem20_8_solution_difference_eq_BAplus_add_APplus_of_AP_penrose1_range_null_injective_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hPenrose1 :
      rectMatMul (rectMatMul (theorem20_8AP A B Bplus) APplus)
          (theorem20_8AP A B Bplus) =
        theorem20_8AP A B Bplus)
    (hAPplus_range_null :
      ∀ w : Fin m → ℝ,
        rectMatMulVec B (rectMatMulVec APplus w) =
          (fun _i : Fin p => 0))
    (hAP_inj_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec (theorem20_8AP A B Bplus) z =
              (fun _i : Fin m => 0) →
            z = (fun _j : Fin n => 0))
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B Bplus)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec Bplus
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j := by
  have hproj :
      rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k) =
        fun j : Fin n =>
          rectMatMulVec APplus
              (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
            rectMatMulVec APplus
              (rectMatMulVec A
                (rectMatMulVec Bplus
                  (fun l : Fin p =>
                    Deltad l - rectMatMulVec DeltaB y l))) j :=
    theorem20_8_projected_difference_eq_APplus_of_AP_penrose1_range_null_injective_reduced_difference_eq
      A DeltaA Deltab B DeltaB Bplus APplus Deltad y x hright
      hPenrose1 hAPplus_range_null hAP_inj_null hAPdiff
  exact
    theorem20_8_solution_difference_eq_BAplus_add_APplus_of_projected_difference
      A DeltaA b Deltab B DeltaB Bplus APplus d Deltad x y hx hy hproj
/-- Under the natural positive denominator assumptions, the first-order
    coefficient in Theorem 20.8's perturbation bound is nonnegative. -/
theorem theorem20_8FirstOrderRHS_nonneg {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    (hApos : 0 < frobNormRect A) (hBpos : 0 < frobNormRect B)
    (hxpos : 0 < vecNorm2 x) :
    0 ≤ theorem20_8FirstOrderRHS A b B d x r APplus BAplus := by
  unfold theorem20_8FirstOrderRHS
  have hkA : 0 ≤ theorem20_8KappaA B BAplus :=
    theorem20_8KappaA_nonneg B BAplus
  have hkB : 0 ≤ theorem20_8KappaB A APplus :=
    theorem20_8KappaB_nonneg A APplus
  have hBx_pos : 0 < frobNormRect B * vecNorm2 x := mul_pos hBpos hxpos
  have hAx_pos : 0 < frobNormRect A * vecNorm2 x := mul_pos hApos hxpos
  have hd_term : 0 ≤ vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1 := by
    have hdiv : 0 ≤ vecNorm2 d / (frobNormRect B * vecNorm2 x) :=
      div_nonneg (vecNorm2_nonneg d) (le_of_lt hBx_pos)
    linarith
  have hb_term : 0 ≤ vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1 := by
    have hdiv : 0 ≤ vecNorm2 b / (frobNormRect A * vecNorm2 x) :=
      div_nonneg (vecNorm2_nonneg b) (le_of_lt hAx_pos)
    linarith
  have hres_ratio : 0 ≤ vecNorm2 r / (frobNormRect A * vecNorm2 x) :=
    div_nonneg (vecNorm2_nonneg r) (le_of_lt hAx_pos)
  have hres_amp : 0 ≤ theorem20_8ResidualAmplifier A B APplus BAplus :=
    theorem20_8ResidualAmplifier_nonneg A B APplus BAplus hApos
  have hfirst :
      0 ≤ theorem20_8KappaA B BAplus *
          (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) :=
    mul_nonneg hkA hd_term
  have hsecond :
      0 ≤ theorem20_8KappaB A APplus *
          (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) := by
    exact mul_nonneg hkB hb_term
  have hthird :
      0 ≤ theorem20_8ResidualAmplifier A B APplus BAplus *
          (vecNorm2 r / (frobNormRect A * vecNorm2 x)) :=
    mul_nonneg hres_amp hres_ratio
  exact add_nonneg (add_nonneg hfirst hsecond) hthird
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    residual-explicit solution-difference identity using only the projected
    action of `(AP)^+ AP` on the actual feasible difference.  This is the
    vector-action counterpart of
    `theorem20_8_solution_difference_eq_BAplus_add_APplus_of_perturbed_higham_residual_eq`. -/
theorem theorem20_8_solution_difference_eq_BAplus_add_APplus_of_perturbed_higham_residual_projected_action
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (x y : Fin n → ℝ) (rHigh : Fin m → ℝ)
    (hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k))
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m =>
              (b i - rectMatMulVec A x i) - rHigh i -
                rectMatMulVec DeltaA y i + Deltab i) j := by
  let diff : Fin n → ℝ := fun k => y k - x k
  let defect : Fin p → ℝ :=
    fun i => Deltad i - rectMatMulVec DeltaB y i
  let forcing : Fin m → ℝ :=
    fun i => (b i - rectMatMulVec A x i) - rHigh i -
      rectMatMulVec DeltaA y i + Deltab i
  let correction : Fin m → ℝ :=
    rectMatMulVec A (rectMatMulVec Bplus defect)
  have hdecomp :=
    theorem20_8_perturbed_feasible_difference_decomp
      B DeltaB Bplus d Deltad x y hx hy
  have hAPdiff :=
    theorem20_8_AP_difference_eq_of_perturbed_higham_residual_eq
      A DeltaA b Deltab B DeltaB Bplus d Deltad x y rHigh hx hy hres
  have hAPdiff_split :
      rectMatMulVec (theorem20_8AP A B Bplus) diff =
        fun i : Fin m => forcing i - correction i := by
    ext i
    have hi := congrFun hAPdiff i
    dsimp [diff, forcing, correction, defect] at hi ⊢
    linarith
  have hproj :
      rectMatMulVec (theorem20_8Projection B Bplus) diff =
        fun j : Fin n =>
          rectMatMulVec APplus forcing j -
            rectMatMulVec APplus correction j := by
    calc
      rectMatMulVec (theorem20_8Projection B Bplus) diff =
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B Bplus) diff) := by
            exact hAPaction.symm
      _ = rectMatMulVec APplus (fun i : Fin m => forcing i - correction i) := by
            rw [hAPdiff_split]
      _ = fun j : Fin n =>
            rectMatMulVec APplus forcing j -
              rectMatMulVec APplus correction j := by
            rw [rectMatMulVec_sub]
  have hBA :=
    theorem20_8BAplus_apply A B Bplus APplus defect
  ext j
  have hdecomp_j := congrFun hdecomp j
  have hproj_j := congrFun hproj j
  have hBA_j := congrFun hBA j
  change
    y j - x j =
      rectMatMulVec (theorem20_8BAplus A B Bplus APplus) defect j +
        rectMatMulVec APplus forcing j
  rw [hdecomp_j, hproj_j, hBA_j]
  ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    residual-explicit norm bound using only the projected action of
    `(AP)^+ AP` on `y - x`.  The reduced residual forcing remains a supplied
    radius. -/
theorem theorem20_8_vecNorm2_solution_difference_residual_forcing_le_projected_action
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Deltad : Fin p → ℝ)
    (x y : Fin n → ℝ) (rHigh : Fin m → ℝ)
    {BAplus_norm DeltaB_norm Deltad_norm forcing_norm : ℝ}
    (hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (fun k : Fin n => y k - x k))
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hBAplus_nonneg : 0 ≤ BAplus_norm)
    (hBAplus :
      rectOpNorm2Le (theorem20_8BAplus A B Bplus APplus) BAplus_norm)
    (hDeltaB : rectOpNorm2Le DeltaB DeltaB_norm)
    (hDeltad : vecNorm2 Deltad ≤ Deltad_norm)
    (hforcing :
      vecNorm2
          (fun i : Fin m =>
            (b i - rectMatMulVec A x i) - rHigh i -
              rectMatMulVec DeltaA y i + Deltab i) ≤ forcing_norm) :
    vecNorm2 (fun j : Fin n => y j - x j) ≤
      BAplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) +
        complexMatrixOp2 (realRectToCMatrix APplus) * forcing_norm := by
  let defect : Fin p → ℝ :=
    fun i => Deltad i - rectMatMulVec DeltaB y i
  let forcing : Fin m → ℝ :=
    fun i => (b i - rectMatMulVec A x i) - rHigh i -
      rectMatMulVec DeltaA y i + Deltab i
  let BAplus := theorem20_8BAplus A B Bplus APplus
  have hsol :=
    theorem20_8_solution_difference_eq_BAplus_add_APplus_of_perturbed_higham_residual_projected_action
      A DeltaA b Deltab B DeltaB Bplus APplus d Deltad x y rHigh
      hAPaction hx hy hres
  have hdirect :
      vecNorm2 (rectMatMulVec BAplus defect) ≤
        BAplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) := by
    exact theorem20_8_vecNorm2_BAplus_constraint_defect_le
      DeltaB BAplus Deltad y hBAplus_nonneg hBAplus hDeltaB hDeltad
  have hop_nonneg : 0 ≤ complexMatrixOp2 (realRectToCMatrix APplus) :=
    complexMatrixOp2_nonneg (realRectToCMatrix APplus)
  have hforcing_bound :
      vecNorm2 (rectMatMulVec APplus forcing) ≤
        complexMatrixOp2 (realRectToCMatrix APplus) * forcing_norm := by
    calc
      vecNorm2 (rectMatMulVec APplus forcing)
          ≤ complexMatrixOp2 (realRectToCMatrix APplus) * vecNorm2 forcing :=
              rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
                APplus le_rfl forcing
      _ ≤ complexMatrixOp2 (realRectToCMatrix APplus) * forcing_norm :=
              mul_le_mul_of_nonneg_left hforcing hop_nonneg
  calc
    vecNorm2 (fun j : Fin n => y j - x j) =
        vecNorm2 (fun j : Fin n =>
          rectMatMulVec BAplus defect j + rectMatMulVec APplus forcing j) := by
          rw [hsol]
    _ ≤ vecNorm2 (rectMatMulVec BAplus defect) +
          vecNorm2 (rectMatMulVec APplus forcing) :=
          vecNorm2_add_le (rectMatMulVec BAplus defect)
            (rectMatMulVec APplus forcing)
    _ ≤ BAplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) +
          complexMatrixOp2 (realRectToCMatrix APplus) * forcing_norm :=
          add_le_add hdirect hforcing_bound
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    obstruction to discharging the residual-amplifier factor automatically.

    If the source product `A B_A^+` has zero operator norm while
    `kappa_B(A)` is positive, the source-facing residual-amplifier lower-bound
    side condition `1 + 1/kappa_B(A) <= (||B||_F/||A||_F)||A B_A^+||_2` is
    impossible. -/
theorem theorem20_8_not_residual_amplifier_factor_ge_one_add_inv_of_ABAplus_op2_eq_zero
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    (hkappa_pos : 0 < theorem20_8KappaB A APplus)
    (hABAplus_zero :
      complexMatrixOp2 (realRectToCMatrix (rectMatMul A BAplus)) = 0) :
    ¬
      1 + (theorem20_8KappaB A APplus)⁻¹ ≤
        (frobNormRect B / frobNormRect A) *
          complexMatrixOp2 (realRectToCMatrix (rectMatMul A BAplus)) := by
  intro hfactor
  have hleft_pos :
      0 < 1 + (theorem20_8KappaB A APplus)⁻¹ := by
    have hinv_pos : 0 < (theorem20_8KappaB A APplus)⁻¹ :=
      inv_pos.mpr hkappa_pos
    linarith
  have hfactor_nonpos :
      1 + (theorem20_8KappaB A APplus)⁻¹ ≤ 0 := by
    simpa [hABAplus_zero] using hfactor
  exact (not_le_of_gt hleft_pos) hfactor_nonpos
/-- In the zero-residual case, Theorem 20.8's first-order coefficient drops
    its residual-amplification term. -/
theorem theorem20_8FirstOrderRHS_of_zero_residual {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ) :
    theorem20_8FirstOrderRHS A b B d x (fun _i : Fin m => 0) APplus BAplus =
      theorem20_8KappaA B BAplus *
          (vecNorm2 d / (frobNormRect B * vecNorm2 x) + 1) +
        theorem20_8KappaB A APplus *
          (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) := by
  simp [theorem20_8FirstOrderRHS, vecNorm2_zero]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8, equation (20.25):
    the first-order coefficient is the zero-residual coefficient plus the
    displayed residual-amplification term. -/
theorem theorem20_8FirstOrderRHS_eq_zero_residual_add_residual_term
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ) :
    theorem20_8FirstOrderRHS A b B d x r APplus BAplus =
      theorem20_8FirstOrderRHS A b B d x (fun _i : Fin m => 0) APplus BAplus +
        theorem20_8ResidualAmplifier A B APplus BAplus *
          (vecNorm2 r / (frobNormRect A * vecNorm2 x)) := by
  simp [theorem20_8FirstOrderRHS, vecNorm2_zero]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the first-order coefficient in (20.25) is monotone in the residual norm,
    under the natural positive denominator conditions. -/
theorem theorem20_8FirstOrderRHS_le_of_residual_norm_le {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r₁ r₂ : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    (hApos : 0 < frobNormRect A) (hxpos : 0 < vecNorm2 x)
    (hr : vecNorm2 r₁ ≤ vecNorm2 r₂) :
    theorem20_8FirstOrderRHS A b B d x r₁ APplus BAplus ≤
      theorem20_8FirstOrderRHS A b B d x r₂ APplus BAplus := by
  calc
    theorem20_8FirstOrderRHS A b B d x r₁ APplus BAplus
        = theorem20_8FirstOrderRHS A b B d x (fun _i : Fin m => 0)
            APplus BAplus +
          theorem20_8ResidualAmplifier A B APplus BAplus *
            (vecNorm2 r₁ / (frobNormRect A * vecNorm2 x)) :=
      theorem20_8FirstOrderRHS_eq_zero_residual_add_residual_term
        A b B d x r₁ APplus BAplus
    _ ≤ theorem20_8FirstOrderRHS A b B d x (fun _i : Fin m => 0)
            APplus BAplus +
          theorem20_8ResidualAmplifier A B APplus BAplus *
            (vecNorm2 r₂ / (frobNormRect A * vecNorm2 x)) := by
      have hterm :
          theorem20_8ResidualAmplifier A B APplus BAplus *
              (vecNorm2 r₁ / (frobNormRect A * vecNorm2 x)) ≤
            theorem20_8ResidualAmplifier A B APplus BAplus *
              (vecNorm2 r₂ / (frobNormRect A * vecNorm2 x)) := by
        apply mul_le_mul_of_nonneg_left
        · exact div_le_div_of_nonneg_right hr (le_of_lt (mul_pos hApos hxpos))
        · exact theorem20_8ResidualAmplifier_nonneg A B APplus BAplus hApos
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hterm
          (theorem20_8FirstOrderRHS A b B d x (fun _i : Fin m => 0)
            APplus BAplus)
    _ = theorem20_8FirstOrderRHS A b B d x r₂ APplus BAplus :=
      (theorem20_8FirstOrderRHS_eq_zero_residual_add_residual_term
        A b B d x r₂ APplus BAplus).symm
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the zero-residual first-order coefficient is the lower endpoint of the
    residual-dependent coefficient family. -/
theorem theorem20_8FirstOrderRHS_zero_residual_le {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (APplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin p → ℝ)
    (hApos : 0 < frobNormRect A) (hxpos : 0 < vecNorm2 x) :
    theorem20_8FirstOrderRHS A b B d x (fun _i : Fin m => 0) APplus BAplus ≤
      theorem20_8FirstOrderRHS A b B d x r APplus BAplus := by
  apply theorem20_8FirstOrderRHS_le_of_residual_norm_le
      A b B d x (fun _i : Fin m => 0) r APplus BAplus hApos hxpos
  simpa [vecNorm2_zero] using vecNorm2_nonneg r
/-- Higham, 2nd ed., Chapter 20, Problem 20.11 support:
    with no equality constraints, the first-order coefficient in (20.25)
    reduces to the unconstrained least-squares data and residual terms. -/
theorem problem20_11_unconstrained_firstOrderRHS_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin 0 → Fin n → ℝ) (d : Fin 0 → ℝ)
    (x : Fin n → ℝ) (r : Fin m → ℝ)
    (Aplus : Fin n → Fin m → ℝ) (BAplus : Fin n → Fin 0 → ℝ) :
    theorem20_8FirstOrderRHS A b B d x r Aplus BAplus =
      theorem20_8KappaB A Aplus *
          (vecNorm2 b / (frobNormRect A * vecNorm2 x) + 1) +
        theorem20_8KappaB A Aplus ^ 2 *
          (vecNorm2 r / (frobNormRect A * vecNorm2 x)) := by
  have hkA0 : theorem20_8KappaA B BAplus = 0 := by
    simp [theorem20_8KappaA, frobNormRect, frobNormSqRect]
  have hresamp :
      theorem20_8ResidualAmplifier A B Aplus BAplus =
        theorem20_8KappaB A Aplus ^ 2 := by
    simp [theorem20_8ResidualAmplifier, frobNormRect, frobNormSqRect]
  unfold theorem20_8FirstOrderRHS
  rw [hkA0, hresamp]
  ring
/-- The linear constraint map `x ↦ B x` used in the equality-constrained
    least-squares problem (20.23). -/
noncomputable def lseConstraintLinearMap {p n : ℕ}
    (B : Fin p → Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin p → ℝ) where
  toFun := rectMatMulVec B
  map_add' := by
    intro x y
    exact rectMatMulVec_add B x y
  map_smul' := by
    intro a x
    exact rectMatMulVec_smul B a x
/-- Higham, 2nd ed., Chapter 20, equation (20.24), first condition:
    local finite-dimensional formulation of the full-row-rank assumption
    `rank(B)=p` as surjectivity of the constraint map `x ↦ B x`. -/
def LSEFullRowRank {p n : ℕ} (B : Fin p → Fin n → ℝ) : Prop :=
  Function.Surjective (lseConstraintLinearMap B)
/-- Higham, 2nd ed., Chapter 20, equation (20.24), consistency consequence:
    the local full-row-rank condition makes the equality constraint `B x = d`
    feasible for every right-hand side `d`. -/
theorem LSEFullRowRank.exists_feasible {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (d : Fin p → ℝ) :
    ∃ x : Fin n → ℝ, LSEFeasible B d x := by
  rcases hB d with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro i
  simpa [lseConstraintLinearMap] using congrFun hx i
/-- Higham, 2nd ed., Chapter 20, equation (20.24) support:
    a source full-row-rank constraint matrix admits a noncomputable rectangular
    right inverse.  The `i`th column is any solution of `B x = e_i`. -/
noncomputable def LSEFullRowRank.rightInverse {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B) :
    Fin n → Fin p → ℝ :=
  fun j i =>
    Classical.choose
      (hB (fun k : Fin p => idMatrix p k i)) j
/-- Higham, 2nd ed., Chapter 20, equation (20.24) support:
    the noncomputable right inverse supplied by full row rank satisfies
    `B * Bplus = I`. -/
theorem LSEFullRowRank.rightInverse_spec {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B) :
    rectMatMul B hB.rightInverse = idMatrix p := by
  ext i k
  have hcol :=
    congrFun
      (Classical.choose_spec
        (hB (fun r : Fin p => idMatrix p r k))) i
  simpa [LSEFullRowRank.rightInverse, lseConstraintLinearMap, rectMatMul]
    using hcol
/-- Higham, 2nd ed., Chapter 20, equation (20.24) support:
    existential form of the rectangular right inverse obtained from source
    full row rank. -/
theorem LSEFullRowRank.exists_rightInverse {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B) :
    ∃ Bplus : Fin n → Fin p → ℝ, rectMatMul B Bplus = idMatrix p :=
  ⟨hB.rightInverse, hB.rightInverse_spec⟩
/-- Higham, 2nd ed., Chapter 20, equations (20.24)-(20.25) support:
    source full row rank instantiates the right-inverse projector
    `P = I - Bplus*B`, so the projected directions lie in `null(B)`.

    This uses the noncomputable right inverse supplied by full row rank; it is
    not a Moore--Penrose pseudoinverse characterization. -/
theorem LSEFullRowRank.theorem20_8Projection_constraint_zero {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B) :
    rectMatMul B (theorem20_8Projection B hB.rightInverse) =
      (fun _i _j => 0) :=
  _root_.NumStability.theorem20_8Projection_constraint_zero
    B hB.rightInverse hB.rightInverse_spec
/-- Higham, 2nd ed., Chapter 20, equations (20.24)-(20.25) support:
    vector form of the full-row-rank-instantiated identity
    `B(I - Bplus*B) = 0`. -/
theorem LSEFullRowRank.theorem20_8Projection_constraint_vec_zero {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (x : Fin n → ℝ) :
    rectMatMulVec B
        (rectMatMulVec (theorem20_8Projection B hB.rightInverse) x) =
      (fun _i => 0) :=
  _root_.NumStability.theorem20_8Projection_constraint_vec_zero B hB.rightInverse
    hB.rightInverse_spec x
/-- Higham, 2nd ed., Chapter 20, equations (20.24)-(20.25) support:
    vector idempotence of the nullspace projector instantiated from source
    full row rank. -/
theorem LSEFullRowRank.theorem20_8Projection_vec_idempotent {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (x : Fin n → ℝ) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (rectMatMulVec (theorem20_8Projection B hB.rightInverse) x) =
      rectMatMulVec (theorem20_8Projection B hB.rightInverse) x :=
  _root_.NumStability.theorem20_8Projection_vec_idempotent B hB.rightInverse
    hB.rightInverse_spec x
/-- Higham, 2nd ed., Chapter 20, equations (20.23)-(20.25) support:
    under source full row rank, adding a projected direction to a feasible
    point preserves the equality constraint. -/
theorem LSEFullRowRank.theorem20_8Projection_feasible_step {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (d : Fin p → ℝ) (x0 z : Fin n → ℝ)
    (hx0 : LSEFeasible B d x0) :
    LSEFeasible B d
      (fun j =>
        x0 j + rectMatMulVec (theorem20_8Projection B hB.rightInverse) z j) :=
  _root_.NumStability.theorem20_8Projection_feasible_step B hB.rightInverse d x0 z
    hB.rightInverse_spec hx0
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the reduced unconstrained minimizer lifts to an equality-constrained
    minimizer using the right inverse supplied by source full row rank. -/
theorem LSEFullRowRank.theorem20_8AP_unconstrained_minimizer_lifts
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (d : Fin p → ℝ) (x0 z : Fin n → ℝ)
    (hx0 : LSEFeasible B d x0)
    (hmin : IsLeastSquaresMinimizer
      (theorem20_8AP A B hB.rightInverse)
      (fun i => b i - rectMatMulVec A x0 i) z) :
    IsLSEMinimizer A b B d
      (fun j =>
        x0 j + rectMatMulVec (theorem20_8Projection B hB.rightInverse) z j) :=
  _root_.NumStability.theorem20_8AP_unconstrained_minimizer_lifts A b B hB.rightInverse
    d x0 z hB.rightInverse_spec hx0 hmin
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    every exact LSE minimizer gives a minimizer of the full-row-rank-instantiated
    reduced unconstrained problem. -/
theorem LSEFullRowRank.theorem20_8AP_unconstrained_minimizer_of_lse_minimizer
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (d : Fin p → ℝ) (x0 x : Fin n → ℝ)
    (hx0 : LSEFeasible B d x0)
    (hx : IsLSEMinimizer A b B d x) :
    IsLeastSquaresMinimizer (theorem20_8AP A B hB.rightInverse)
      (fun i => b i - rectMatMulVec A x0 i)
      (fun j => x j - x0 j) :=
  _root_.NumStability.theorem20_8AP_unconstrained_minimizer_of_lse_minimizer
    A b B hB.rightInverse d x0 x hB.rightInverse_spec hx0 hx
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    perturbed-data reduced-`AP` minimizer handoff using the right inverse
    supplied by full row rank of the perturbed constraint matrix. -/
theorem
    LSEFullRowRank.theorem20_8AP_perturbed_unconstrained_minimizer_of_lse_minimizer
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ)
    (hBpert : LSEFullRowRank (fun i j => B i j + DeltaB i j))
    (d Deltad : Fin p → ℝ) (x0 y : Fin n → ℝ)
    (hx0 : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) x0)
    (hy : IsLSEMinimizer
      (fun i j => A i j + DeltaA i j)
      (fun i => b i + Deltab i)
      (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    IsLeastSquaresMinimizer
      (theorem20_8AP (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j) hBpert.rightInverse)
      (fun i =>
        b i + Deltab i -
          rectMatMulVec (fun i j => A i j + DeltaA i j) x0 i)
      (fun j => y j - x0 j) :=
  _root_.NumStability.theorem20_8AP_perturbed_unconstrained_minimizer_of_lse_minimizer
    A DeltaA b Deltab B DeltaB hBpert.rightInverse d Deltad x0 y
    hBpert.rightInverse_spec hx0 hy
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    full-row-rank-instantiated form of applying `P = I - Bplus*B` to a vector
    with a known original-constraint residual. -/
theorem LSEFullRowRank.theorem20_8Projection_apply_of_constraint {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (v : Fin n → ℝ) (e : Fin p → ℝ)
    (hBv : rectMatMulVec B v = e) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse) v =
      fun j => v j - rectMatMulVec hB.rightInverse e j :=
  _root_.NumStability.theorem20_8Projection_apply_of_constraint
    B hB.rightInverse v e hBv
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    projection of an original/perturbed feasible difference, instantiated by
    the right inverse obtained from source full row rank. -/
theorem
    LSEFullRowRank.theorem20_8Projection_apply_perturbed_feasible_difference
    {n p : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (fun j => y j - x j) =
      fun j =>
        (y j - x j) -
          rectMatMulVec hB.rightInverse
            (fun i => Deltad i - rectMatMulVec DeltaB y i) j :=
  _root_.NumStability.theorem20_8Projection_apply_perturbed_feasible_difference
    B DeltaB hB.rightInverse d Deltad x y hx hy
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank form of the perturbed-feasible difference
    decomposition. -/
theorem LSEFullRowRank.theorem20_8_perturbed_feasible_difference_decomp
    {n p : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    (fun j => y j - x j) =
      fun j =>
        rectMatMulVec (theorem20_8Projection B hB.rightInverse)
            (fun k => y k - x k) j +
          rectMatMulVec hB.rightInverse
            (fun i => Deltad i - rectMatMulVec DeltaB y i) j :=
  _root_.NumStability.theorem20_8_perturbed_feasible_difference_decomp
    B DeltaB hB.rightInverse d Deltad x y hx hy
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank form of the perturbed-feasible point decomposition. -/
theorem LSEFullRowRank.theorem20_8_perturbed_feasible_point_decomp
    {n p : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    y =
      fun j =>
        x j +
          rectMatMulVec (theorem20_8Projection B hB.rightInverse)
            (fun k => y k - x k) j +
          rectMatMulVec hB.rightInverse
            (fun i => Deltad i - rectMatMulVec DeltaB y i) j :=
  _root_.NumStability.theorem20_8_perturbed_feasible_point_decomp
    B DeltaB hB.rightInverse d Deltad x y hx hy
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    action of `A` on a perturbed feasible point after the full-row-rank
    right-inverse nullspace decomposition. -/
theorem LSEFullRowRank.theorem20_8_perturbed_feasible_point_action_decomp
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    rectMatMulVec A y =
      fun i =>
        rectMatMulVec A x i +
          rectMatMulVec (theorem20_8AP A B hB.rightInverse)
            (fun k => y k - x k) i +
          rectMatMulVec A
            (rectMatMulVec hB.rightInverse
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i :=
  _root_.NumStability.theorem20_8_perturbed_feasible_point_action_decomp
    A B DeltaB hB.rightInverse d Deltad x y hx hy
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank form of the projected `AP` step identity, with the
    constraint right inverse supplied by `rank(B)=p`. -/
theorem LSEFullRowRank.theorem20_8_AP_difference_eq_action_minus_constraint_correction
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    rectMatMulVec (theorem20_8AP A B hB.rightInverse) (fun k => y k - x k) =
      fun i =>
        rectMatMulVec A y i - rectMatMulVec A x i -
          rectMatMulVec A
            (rectMatMulVec hB.rightInverse
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i :=
  _root_.NumStability.theorem20_8_AP_difference_eq_action_minus_constraint_correction
    A B DeltaB hB.rightInverse d Deltad x y hx hy
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    residual decomposition for a point feasible for the perturbed constraint,
    with the constraint right inverse supplied by source full row rank. -/
theorem LSEFullRowRank.theorem20_8_perturbed_feasible_residual_decomp
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    lsResidual (fun i j => A i j + DeltaA i j) (fun i => b i + Deltab i) y =
      fun i =>
        lsResidual (theorem20_8AP A B hB.rightInverse)
          (fun i => b i - rectMatMulVec A x i) (fun j => y j - x j) i +
          rectMatMulVec A
            (rectMatMulVec hB.rightInverse
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i +
          rectMatMulVec DeltaA y i -
          Deltab i :=
  _root_.NumStability.theorem20_8_perturbed_feasible_residual_decomp
    A DeltaA b Deltab B DeltaB hB.rightInverse d Deltad x y hx hy
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank form of the reduced `AP` difference solved from an
    explicit perturbed residual vector. -/
theorem LSEFullRowRank.theorem20_8_AP_difference_eq_of_perturbed_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ) (rpert : Fin m → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidual (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rpert) :
    rectMatMulVec (theorem20_8AP A B hB.rightInverse) (fun k => y k - x k) =
      fun i =>
        rpert i + (b i - rectMatMulVec A x i) -
          rectMatMulVec A
            (rectMatMulVec hB.rightInverse
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i -
          rectMatMulVec DeltaA y i + Deltab i :=
  _root_.NumStability.theorem20_8_AP_difference_eq_of_perturbed_residual_eq
    A DeltaA b Deltab B DeltaB hB.rightInverse d Deltad x y rpert hx hy hres
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank form of the Higham-sign reduced `AP` difference
    identity with an explicit perturbed residual vector. -/
theorem
    LSEFullRowRank.theorem20_8_AP_difference_eq_of_perturbed_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ) (rHigh : Fin m → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh) :
    rectMatMulVec (theorem20_8AP A B hB.rightInverse) (fun k => y k - x k) =
      fun i =>
        (b i - rectMatMulVec A x i) - rHigh i -
          rectMatMulVec A
            (rectMatMulVec hB.rightInverse
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i -
          rectMatMulVec DeltaA y i + Deltab i :=
  _root_.NumStability.theorem20_8_AP_difference_eq_of_perturbed_higham_residual_eq
    A DeltaA b Deltab B DeltaB hB.rightInverse d Deltad x y rHigh hx hy hres
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank same-residual specialization of the Higham-sign
    reduced `AP` difference identity. -/
theorem LSEFullRowRank.theorem20_8_AP_difference_eq_of_same_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hsame : r = rHigh) :
    rectMatMulVec (theorem20_8AP A B hB.rightInverse) (fun k => y k - x k) =
      fun i =>
        Deltab i - rectMatMulVec DeltaA y i -
          rectMatMulVec A
            (rectMatMulVec hB.rightInverse
              (fun l => Deltad l - rectMatMulVec DeltaB y l)) i :=
  _root_.NumStability.theorem20_8_AP_difference_eq_of_same_higham_residual_eq
    A DeltaA b Deltab B DeltaB hB.rightInverse d Deltad x y r rHigh
    hx hy hr hres hsame
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    full-row-rank-instantiated residual decomposition with the constraint
    correction split through the printed source quantity `B_A^+`.

    The supplied `APplus` remains explicit because this wrapper only discharges
    the raw right inverse of `B` from the source condition `rank(B)=p`. -/
theorem LSEFullRowRank.theorem20_8_perturbed_feasible_residual_decomp_BAplus
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y) :
    lsResidual (fun i j => A i j + DeltaA i j) (fun i => b i + Deltab i) y =
      fun i =>
        lsResidual (theorem20_8AP A B hB.rightInverse)
            (fun i => b i - rectMatMulVec A x i) (fun j => y j - x j) i +
          (rectMatMulVec A
              (rectMatMulVec APplus
                (rectMatMulVec A
                  (rectMatMulVec hB.rightInverse
                    (fun l => Deltad l - rectMatMulVec DeltaB y l)))) i +
            rectMatMulVec A
              (rectMatMulVec
                (theorem20_8BAplus A B hB.rightInverse APplus)
                (fun l => Deltad l - rectMatMulVec DeltaB y l)) i) +
          rectMatMulVec DeltaA y i -
          Deltab i :=
  _root_.NumStability.theorem20_8_perturbed_feasible_residual_decomp_BAplus
    A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad x y hx hy
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    full-row-rank-instantiated expansion of
    `B_A^+ = (I - (AP)^+ A) B^+` applied to a constraint-defect vector.

    This uses the right inverse supplied by source full row rank; it does not
    assert Moore--Penrose optimality for that right inverse. -/
theorem LSEFullRowRank.theorem20_8BAplus_apply {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (APplus : Fin n → Fin m → ℝ)
    (e : Fin p → ℝ) :
    rectMatMulVec (theorem20_8BAplus A B hB.rightInverse APplus) e =
      fun j : Fin n =>
        rectMatMulVec hB.rightInverse e j -
          rectMatMulVec APplus
            (rectMatMulVec A (rectMatMulVec hB.rightInverse e)) j :=
  _root_.NumStability.theorem20_8BAplus_apply
    A B hB.rightInverse APplus e
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    full-row-rank-instantiated expansion of the source product `A B_A^+`. -/
theorem LSEFullRowRank.theorem20_8A_BAplus_apply {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (APplus : Fin n → Fin m → ℝ)
    (e : Fin p → ℝ) :
    rectMatMulVec A
        (rectMatMulVec (theorem20_8BAplus A B hB.rightInverse APplus) e) =
      fun i : Fin m =>
        rectMatMulVec A (rectMatMulVec hB.rightInverse e) i -
          rectMatMulVec A
            (rectMatMulVec APplus
              (rectMatMulVec A (rectMatMulVec hB.rightInverse e))) i :=
  _root_.NumStability.theorem20_8A_BAplus_apply
    A B hB.rightInverse APplus e
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    full-row-rank-instantiated split of the old `A B^+` correction into the
    reduced-problem correction plus the printed `A B_A^+` correction. -/
theorem LSEFullRowRank.theorem20_8ABplus_eq_A_APplus_A_Bplus_add_A_BAplus
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (APplus : Fin n → Fin m → ℝ)
    (e : Fin p → ℝ) :
    rectMatMulVec A (rectMatMulVec hB.rightInverse e) =
      fun i : Fin m =>
        rectMatMulVec A
            (rectMatMulVec APplus
              (rectMatMulVec A (rectMatMulVec hB.rightInverse e))) i +
          rectMatMulVec A
            (rectMatMulVec
              (theorem20_8BAplus A B hB.rightInverse APplus) e) i :=
  _root_.NumStability.theorem20_8ABplus_eq_A_APplus_A_Bplus_add_A_BAplus
    A B hB.rightInverse APplus e
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank form of the reduced-`AP` projected-difference bridge.

    Full row rank supplies `Bplus = hB.rightInverse`; the two remaining
    hypotheses are exactly the still-open reduced-problem obligations
    `(AP)^+ AP = P` and the reduced equation for `AP*(y-x)`. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
        theorem20_8Projection B hB.rightInverse)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j :=
  _root_.NumStability.theorem20_8_projected_difference_eq_APplus_of_reduced_difference_eq
      A DeltaA Deltab B DeltaB hB.rightInverse APplus Deltad y x
      hAPleft hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank residual-explicit projected-difference bridge in
    Higham's residual sign convention. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_perturbed_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (y x : Fin n → ℝ) (rHigh : Fin m → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
        theorem20_8Projection B hB.rightInverse)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m =>
              (b i - rectMatMulVec A x i) - rHigh i -
                rectMatMulVec DeltaA y i + Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j :=
  _root_.NumStability.theorem20_8_projected_difference_eq_APplus_of_perturbed_higham_residual_eq
    A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad y x rHigh
    hAPleft hx hy hres
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank projected same-residual bridge in Higham's residual
    sign convention. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_same_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
        theorem20_8Projection B hB.rightInverse)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hsame : r = rHigh) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j :=
  _root_.NumStability.theorem20_8_projected_difference_eq_APplus_of_same_higham_residual_eq
    A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad x y r rHigh
    hAPleft hx hy hr hres hsame
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank exact solution-difference identity from the reduced
    `AP` obligations.  The conclusion is the printed correction vector
    `B_A^+*(Deltad-DeltaB*y) + (AP)^+*(DeltaA*y-Deltab)`.

    This is exact algebraic infrastructure: the reduced equation and
    `(AP)^+ AP = P` are still explicit hypotheses. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
        theorem20_8Projection B hB.rightInverse)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B hB.rightInverse APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j := by
  have hproj :
      rectMatMulVec (theorem20_8Projection B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun j : Fin n =>
          rectMatMulVec APplus
              (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
            rectMatMulVec APplus
              (rectMatMulVec A
                (rectMatMulVec hB.rightInverse
                  (fun l : Fin p =>
                    Deltad l - rectMatMulVec DeltaB y l))) j :=
    LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_reduced_difference_eq
      A DeltaA Deltab hB DeltaB APplus Deltad y x hAPleft hAPdiff
  exact
    _root_.NumStability.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_projected_difference
      A DeltaA (fun _ : Fin m => 0) Deltab B DeltaB hB.rightInverse APplus
      d Deltad x y hx hy hproj
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank residual-explicit solution-difference identity in
    Higham's residual sign convention. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_perturbed_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ) (rHigh : Fin m → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
        theorem20_8Projection B hB.rightInverse)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec (theorem20_8BAplus A B hB.rightInverse APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m =>
              (b i - rectMatMulVec A x i) - rHigh i -
                rectMatMulVec DeltaA y i + Deltab i) j :=
  _root_.NumStability.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_perturbed_higham_residual_eq
    A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad x y rHigh
    hAPleft hx hy hres
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank exact same-residual solution-difference identity in
    Higham's residual sign convention. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_same_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ) (r rHigh : Fin m → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
        theorem20_8Projection B hB.rightInverse)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hsame : r = rHigh) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec (theorem20_8BAplus A B hB.rightInverse APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i) j :=
  _root_.NumStability.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_same_higham_residual_eq
    A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad x y r rHigh
    hAPleft hx hy hr hres hsame
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank residual-explicit solution-difference norm bound. -/
theorem
    LSEFullRowRank.theorem20_8_vecNorm2_solution_difference_residual_forcing_le
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ) (rHigh : Fin m → ℝ)
    {BAplus_norm DeltaB_norm Deltad_norm forcing_norm : ℝ}
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
        theorem20_8Projection B hB.rightInverse)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hBAplus_nonneg : 0 ≤ BAplus_norm)
    (hBAplus :
      rectOpNorm2Le
        (theorem20_8BAplus A B hB.rightInverse APplus) BAplus_norm)
    (hDeltaB : rectOpNorm2Le DeltaB DeltaB_norm)
    (hDeltad : vecNorm2 Deltad ≤ Deltad_norm)
    (hforcing :
      vecNorm2
          (fun i : Fin m =>
            (b i - rectMatMulVec A x i) - rHigh i -
              rectMatMulVec DeltaA y i + Deltab i) ≤ forcing_norm) :
    vecNorm2 (fun j : Fin n => y j - x j) ≤
      BAplus_norm * (Deltad_norm + DeltaB_norm * vecNorm2 y) +
        complexMatrixOp2 (realRectToCMatrix APplus) * forcing_norm :=
  _root_.NumStability.theorem20_8_vecNorm2_solution_difference_residual_forcing_le
    A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad x y rHigh
    hAPleft hx hy hres hBAplus_nonneg hBAplus hDeltaB hDeltad hforcing
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 rank bridge:
    full row rank of `B` makes the transpose map `Bᵀ` injective.  This is the
    finite-dimensional algebra used by the exact-MGS GQR route to connect the
    source rank assumption to MGS nonbreakdown hypotheses. -/
theorem LSEFullRowRank.transpose_rectMatMulVec_injective {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B) :
    Function.Injective
      (rectMatMulVec (fun j : Fin n => fun i : Fin p => B i j)) := by
  let Bt : Fin n → Fin p → ℝ := fun j => fun i => B i j
  have hker : ∀ w : Fin p → ℝ, rectMatMulVec Bt w = 0 → w = 0 := by
    intro w hw
    rcases hB w with ⟨x, hx⟩
    have hxB : rectMatMulVec B x = w := by
      simpa [lseConstraintLinearMap] using hx
    have hinner :
        (∑ i : Fin p, w i * rectMatMulVec B x i) = 0 := by
      calc
        (∑ i : Fin p, w i * rectMatMulVec B x i)
            = ∑ i : Fin p, ∑ j : Fin n, w i * (B i j * x j) := by
                unfold rectMatMulVec
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
        _ = ∑ j : Fin n, ∑ i : Fin p, w i * (B i j * x j) := by
                rw [Finset.sum_comm]
        _ = ∑ j : Fin n, (∑ i : Fin p, B i j * w i) * x j := by
                apply Finset.sum_congr rfl
                intro j _
                calc
                  (∑ i : Fin p, w i * (B i j * x j))
                      = ∑ i : Fin p, (B i j * w i) * x j := by
                          apply Finset.sum_congr rfl
                          intro i _
                          ring
                  _ = (∑ i : Fin p, B i j * w i) * x j := by
                          rw [Finset.sum_mul]
        _ = ∑ j : Fin n, rectMatMulVec Bt w j * x j := by
                unfold rectMatMulVec Bt
                rfl
        _ = 0 := by
                simp [hw]
    have hsq : vecNorm2Sq w = 0 := by
      calc
        vecNorm2Sq w
            = ∑ i : Fin p, w i * rectMatMulVec B x i := by
                rw [hxB]
                unfold vecNorm2Sq
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = 0 := hinner
    have hnorm : vecNorm2 w = 0 := by
      unfold vecNorm2
      rw [Real.sqrt_eq_zero (vecNorm2Sq_nonneg w)]
      exact hsq
    ext i
    exact (vecNorm2_eq_zero_iff w).mp hnorm i
  intro y z hyz
  have hdiff : rectMatMulVec Bt (fun i => y i - z i) = 0 := by
    ext j
    have hentry := congrFun hyz j
    change (∑ i : Fin p, B i j * y i) =
      (∑ i : Fin p, B i j * z i) at hentry
    unfold rectMatMulVec Bt
    change (∑ i : Fin p, B i j * (y i - z i)) = 0
    calc
      (∑ i : Fin p, B i j * (y i - z i))
          = ∑ i : Fin p, (B i j * y i - B i j * z i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : Fin p, B i j * y i) -
            (∑ i : Fin p, B i j * z i) := by
              rw [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hentry
  have hzero := hker (fun i => y i - z i) hdiff
  ext i
  have hi : y i - z i = 0 := by
    simpa using congrFun hzero i
  exact sub_eq_zero.mp hi
/-- Converse finite-dimensional rank bridge for the Chapter 20 full-row-rank
    condition: if the transpose action `Bᵀ` is injective, then the constraint
    map `x ↦ Bx` is surjective. -/
theorem LSEFullRowRank.of_transpose_rectMatMulVec_injective {p n : ℕ}
    {B : Fin p → Fin n → ℝ}
    (hBt :
      Function.Injective
        (rectMatMulVec (fun j : Fin n => fun i : Fin p => B i j))) :
    LSEFullRowRank B := by
  let Bt : Fin n → Fin p → ℝ := fun j => fun i => B i j
  let C : (Fin p → ℝ) →ₗ[ℝ] (Fin p → ℝ) :=
    (lseConstraintLinearMap B).comp (lseConstraintLinearMap Bt)
  have hker : ∀ y : Fin p → ℝ, C y = 0 → y = 0 := by
    intro y hy
    have hinner :
        (∑ i : Fin p, y i * rectMatMulVec B (rectMatMulVec Bt y) i) =
          vecNorm2Sq (rectMatMulVec Bt y) := by
      calc
        (∑ i : Fin p, y i * rectMatMulVec B (rectMatMulVec Bt y) i)
            = ∑ i : Fin p, ∑ j : Fin n,
                y i * (B i j * rectMatMulVec Bt y j) := by
                unfold rectMatMulVec
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
        _ = ∑ j : Fin n, ∑ i : Fin p,
                y i * (B i j * rectMatMulVec Bt y j) := by
                rw [Finset.sum_comm]
        _ = ∑ j : Fin n,
                (∑ i : Fin p, B i j * y i) * rectMatMulVec Bt y j := by
                apply Finset.sum_congr rfl
                intro j _
                calc
                  (∑ i : Fin p, y i * (B i j * rectMatMulVec Bt y j))
                      = ∑ i : Fin p, (B i j * y i) *
                          rectMatMulVec Bt y j := by
                          apply Finset.sum_congr rfl
                          intro i _
                          ring
                  _ = (∑ i : Fin p, B i j * y i) *
                          rectMatMulVec Bt y j := by
                          rw [Finset.sum_mul]
        _ = ∑ j : Fin n, rectMatMulVec Bt y j *
                rectMatMulVec Bt y j := by
                unfold rectMatMulVec Bt
                rfl
        _ = vecNorm2Sq (rectMatMulVec Bt y) := by
                unfold vecNorm2Sq
                apply Finset.sum_congr rfl
                intro j _
                ring
    have hinner_zero :
        (∑ i : Fin p, y i * rectMatMulVec B (rectMatMulVec Bt y) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : rectMatMulVec B (rectMatMulVec Bt y) i = 0 := by
        simpa [C, lseConstraintLinearMap] using congrFun hy i
      rw [hi]
      ring
    have hsq : vecNorm2Sq (rectMatMulVec Bt y) = 0 := by
      rw [← hinner]
      exact hinner_zero
    have hnorm : vecNorm2 (rectMatMulVec Bt y) = 0 := by
      unfold vecNorm2
      rw [Real.sqrt_eq_zero (vecNorm2Sq_nonneg (rectMatMulVec Bt y))]
      exact hsq
    have hBt_zero : rectMatMulVec Bt y = 0 := by
      ext j
      exact (vecNorm2_eq_zero_iff (rectMatMulVec Bt y)).mp hnorm j
    have hBt_eq :
        rectMatMulVec Bt y = rectMatMulVec Bt (0 : Fin p → ℝ) := by
      rw [hBt_zero]
      ext j
      simp [rectMatMulVec]
    exact hBt hBt_eq
  have hC_injective : Function.Injective C := by
    intro y z hyz
    have hdiff : C (fun i => y i - z i) = 0 := by
      change C (y - z) = 0
      rw [map_sub]
      ext i
      exact sub_eq_zero.mpr (congrFun hyz i)
    have hzero := hker (fun i => y i - z i) hdiff
    ext i
    have hi := congrFun hzero i
    dsimp at hi
    exact sub_eq_zero.mp hi
  have hC_surjective : Function.Surjective C :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℝ) (V := Fin p → ℝ) (V₂ := Fin p → ℝ) rfl).1 hC_injective
  intro d
  rcases hC_surjective d with ⟨y, hy⟩
  refine ⟨rectMatMulVec Bt y, ?_⟩
  simpa [C, lseConstraintLinearMap] using hy
/-- Rectangular Gram nonsingularity from injectivity of the transpose action.
    This is the algebraic bridge from a full-row-rank rectangular matrix to
    invertibility of `A Aᵀ`, used by the Chapter 20 Gram-pseudoinverse route. -/
theorem rectGram_det_ne_zero_of_transpose_rectMatMulVec_injective {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hAt :
      Function.Injective
        (rectMatMulVec (fun j : Fin n => fun i : Fin m => A i j))) :
    Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  let At : Fin n → Fin m → ℝ := fun j => fun i => A i j
  have hAt' : Function.Injective (rectMatMulVec At) := by
    simpa [At] using hAt
  have hGram_inj : Function.Injective (rectMatMulVec (rectGram A)) := by
    intro y z hyz
    let w : Fin m → ℝ := fun i => y i - z i
    have hGram_w_zero : rectMatMulVec (rectGram A) w = 0 := by
      ext i
      have hentry := congrFun hyz i
      change (∑ j : Fin m, rectGram A i j * y j) =
        (∑ j : Fin m, rectGram A i j * z j) at hentry
      unfold w
      change (∑ j : Fin m, rectGram A i j * (y j - z j)) = 0
      calc
        (∑ j : Fin m, rectGram A i j * (y j - z j))
            = ∑ j : Fin m,
                (rectGram A i j * y j - rectGram A i j * z j) := by
                apply Finset.sum_congr rfl
                intro j _
                ring
        _ = (∑ j : Fin m, rectGram A i j * y j) -
              (∑ j : Fin m, rectGram A i j * z j) := by
                rw [Finset.sum_sub_distrib]
        _ = 0 := sub_eq_zero.mpr hentry
    have hAt_eq_transpose :
        rectMatMulVec At w = rectTransposeMulVec A w := by
      ext j
      simp [At, rectMatMulVec, rectTransposeMulVec]
    have hAw_zero : rectMatMulVec A (rectMatMulVec At w) = 0 := by
      rw [hAt_eq_transpose, rectMatMulVec_rectTransposeMulVec]
      ext i
      have hi := congrFun hGram_w_zero i
      simpa [matMulVec, rectMatMulVec] using hi
    have hinner :
        (∑ i : Fin m, w i * rectMatMulVec A (rectMatMulVec At w) i) =
          vecNorm2Sq (rectMatMulVec At w) := by
      calc
        (∑ i : Fin m, w i * rectMatMulVec A (rectMatMulVec At w) i)
            = ∑ i : Fin m, ∑ j : Fin n,
                w i * (A i j * rectMatMulVec At w j) := by
                unfold rectMatMulVec
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
        _ = ∑ j : Fin n, ∑ i : Fin m,
                w i * (A i j * rectMatMulVec At w j) := by
                rw [Finset.sum_comm]
        _ = ∑ j : Fin n,
                (∑ i : Fin m, A i j * w i) * rectMatMulVec At w j := by
                apply Finset.sum_congr rfl
                intro j _
                calc
                  (∑ i : Fin m, w i * (A i j * rectMatMulVec At w j))
                      = ∑ i : Fin m, (A i j * w i) *
                          rectMatMulVec At w j := by
                          apply Finset.sum_congr rfl
                          intro i _
                          ring
                  _ = (∑ i : Fin m, A i j * w i) *
                          rectMatMulVec At w j := by
                          rw [Finset.sum_mul]
        _ = ∑ j : Fin n, rectMatMulVec At w j *
                rectMatMulVec At w j := by
                unfold rectMatMulVec At
                rfl
        _ = vecNorm2Sq (rectMatMulVec At w) := by
                unfold vecNorm2Sq
                apply Finset.sum_congr rfl
                intro j _
                ring
    have hinner_zero :
        (∑ i : Fin m, w i * rectMatMulVec A (rectMatMulVec At w) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : rectMatMulVec A (rectMatMulVec At w) i = 0 := by
        simpa using congrFun hAw_zero i
      rw [hi]
      ring
    have hsq : vecNorm2Sq (rectMatMulVec At w) = 0 := by
      rw [← hinner]
      exact hinner_zero
    have hnorm : vecNorm2 (rectMatMulVec At w) = 0 := by
      unfold vecNorm2
      rw [Real.sqrt_eq_zero (vecNorm2Sq_nonneg (rectMatMulVec At w))]
      exact hsq
    have hAt_w_zero : rectMatMulVec At w = 0 := by
      ext j
      exact (vecNorm2_eq_zero_iff (rectMatMulVec At w)).mp hnorm j
    have hAt_w_eq :
        rectMatMulVec At w = rectMatMulVec At (0 : Fin m → ℝ) := by
      rw [hAt_w_zero]
      ext j
      simp [rectMatMulVec]
    have hw_zero := hAt' hAt_w_eq
    ext i
    have hi := congrFun hw_zero i
    dsimp [w] at hi
    exact sub_eq_zero.mp hi
  let M : Matrix (Fin m) (Fin m) ℝ := rectGram A
  have hM_inj : Function.Injective M.mulVec := by
    intro x y hxy
    apply hGram_inj
    ext i
    have hi := congrFun hxy i
    simpa [M, rectMatMulVec, Matrix.mulVec] using hi
  have hunitM : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hM_inj
  have hdetUnit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunitM
  have hdetNe : M.det ≠ 0 := isUnit_iff_ne_zero.mp hdetUnit
  simpa [M] using hdetNe
/-- Higham, 2nd ed., Chapter 20, equation (20.24) support:
    source full row rank makes the Gram matrix `B Bᵀ` nonsingular. -/
theorem LSEFullRowRank.rectGram_det_ne_zero {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B) :
    Matrix.det (rectGram B : Matrix (Fin p) (Fin p) ℝ) ≠ 0 :=
  rectGram_det_ne_zero_of_transpose_rectMatMulVec_injective B
    hB.transpose_rectMatMulVec_injective
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 exact-MGS rank bridge:
    full row rank of `B` supplies the stage-0 nonbreakdown fact for MGS applied
    to `Bᵀ`.  This is the first pivot in the rank-to-all-MGS-stages route. -/
theorem LSEFullRowRank.transpose_mgs_stage0_norm_ne_zero {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B) (j : Fin p) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors
        (fun col : Fin n => fun row : Fin p => B row col) 0 j) ≠ 0 := by
  exact
    modifiedGramSchmidtVectors_zero_norm_ne_zero_of_rectMatMulVec_injective
      (fun col : Fin n => fun row : Fin p => B row col)
      hB.transpose_rectMatMulVec_injective j
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 exact-MGS rank bridge:
    full row rank of `B` supplies every nonzero-stage normalizer needed for
    exact MGS applied to `Bᵀ`. -/
theorem LSEFullRowRank.transpose_mgs_norm_ne_zero {p n : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B) (j : Fin p) :
    gsColumnNorm2
      (modifiedGramSchmidtVectors
        (fun col : Fin n => fun row : Fin p => B row col) j.val j) ≠ 0 := by
  exact
    modifiedGramSchmidtVectors_norm_ne_zero_of_rectMatMulVec_injective
      (fun col : Fin n => fun row : Fin p => B row col)
      hB.transpose_rectMatMulVec_injective j
/-- Column permutations preserve equality-constrained least-squares minimizers.

    This is the coordinate-change bridge used by Higham's Chapter 20
    elimination method in (20.29): after solving the permuted problem, pulling
    the coefficient vector back by `Πᵀ` gives a minimizer for the original
    variables. -/
theorem IsLSEMinimizer.of_permuteCols {m n p : ℕ} (π : Fin n ≃ Fin n)
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x : Fin n → ℝ}
    (h : IsLSEMinimizer (rectPermuteCols π A) b (rectPermuteCols π B) d x) :
    IsLSEMinimizer A b B d (vecPermute π.symm x) := by
  refine ⟨?feasible, ?minimal⟩
  · intro i
    have hmul := congrFun (rectMatMulVec_permuteCols π B x) i
    exact hmul.symm.trans (h.1 i)
  · intro y hy
    have hy_perm : LSEFeasible (rectPermuteCols π B) d (vecPermute π y) := by
      intro i
      have hmul := congrFun
        (rectMatMulVec_permuteCols π B (vecPermute π y)) i
      rw [hmul]
      rw [vecPermute_symm_vecPermute]
      exact hy i
    have hineq := h.2 (vecPermute π y) hy_perm
    rw [lsObjective_permuteCols π A b x] at hineq
    rw [lsObjective_permuteCols π A b (vecPermute π y)] at hineq
    rw [vecPermute_symm_vecPermute] at hineq
    exact hineq
/-- Higham, 2nd ed., Chapter 20, equation (20.24), second condition:
    `null(A) ∩ null(B) = {0}`.  The full-row-rank consistency side is
    represented separately by `LSEFullRowRank`. -/
def LSENullIntersectionTrivial {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) : Prop :=
  ∀ v : Fin n → ℝ,
    rectMatMulVec A v = 0 →
    rectMatMulVec B v = 0 →
    v = 0
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the source condition `null(A) ∩ null(B) = {0}` makes `AP` injective on
    the homogeneous constraint nullspace.  On that nullspace, `AP = A`. -/
theorem theorem20_8_AP_injective_on_nullspace_of_nullIntersectionTrivial
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ)
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec (theorem20_8AP A B Bplus) z =
            (fun _i : Fin m => 0) →
          z = (fun _j : Fin n => 0) := by
  intro z hz hAPz
  have hAz : rectMatMulVec A z = (fun _i : Fin m => 0) := by
    rw [← theorem20_8AP_apply_nullspace A B Bplus z hz]
    exact hAPz
  exact hnull z hAz hz
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    Penrose1 plus range-in-`null(B)` gives the reduced-operator left inverse
    once the source null-intersection hypothesis supplies injectivity of `AP`
    on the constraint nullspace. -/
theorem theorem20_8_AP_left_inverse_on_nullspace_of_penrose1_range_null_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hPenrose1 :
      rectMatMul (rectMatMul (theorem20_8AP A B Bplus) APplus)
          (theorem20_8AP A B Bplus) =
        theorem20_8AP A B Bplus)
    (hAPplus_range_null :
      ∀ w : Fin m → ℝ,
        rectMatMulVec B (rectMatMulVec APplus w) =
          (fun _i : Fin p => 0))
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus) z) = z :=
  theorem20_8_AP_left_inverse_on_nullspace_of_penrose1_range_null_injective
    A B Bplus APplus hPenrose1 hAPplus_range_null
      (theorem20_8_AP_injective_on_nullspace_of_nullIntersectionTrivial
        A B Bplus hnull)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    a matrix-level annihilation certificate `B * (AP)^+ = 0` gives the
    range-in-`null(B)` hypothesis needed by the Penrose-style bridge. -/
theorem theorem20_8_APplus_range_null_of_constraint_annihilates
    {m n p : ℕ}
    (B : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hBAPplus : rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0)) :
    ∀ w : Fin m → ℝ,
      rectMatMulVec B (rectMatMulVec APplus w) = (fun _i : Fin p => 0) := by
  intro w
  calc
    rectMatMulVec B (rectMatMulVec APplus w) =
        rectMatMulVec (rectMatMul B APplus) w := by
          exact (rectMatMulVec_rectMatMul B APplus w).symm
    _ = rectMatMulVec (fun _i : Fin p => fun _j : Fin m => 0) w := by
          rw [hBAPplus]
    _ = (fun _i : Fin p => 0) := by
          ext i
          unfold rectMatMulVec
          simp
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    Penrose1 plus the matrix-level annihilation `B * (AP)^+ = 0` gives the
    reduced-operator left inverse once (20.24)'s null-intersection condition is
    available. -/
theorem theorem20_8_AP_left_inverse_on_nullspace_of_penrose1_matrix_range_null_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hPenrose1 :
      rectMatMul (rectMatMul (theorem20_8AP A B Bplus) APplus)
          (theorem20_8AP A B Bplus) =
        theorem20_8AP A B Bplus)
    (hBAPplus : rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus) z) = z :=
  theorem20_8_AP_left_inverse_on_nullspace_of_penrose1_range_null_nullIntersection
    A B Bplus APplus hPenrose1
      (theorem20_8_APplus_range_null_of_constraint_annihilates B APplus hBAPplus)
      hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the first Penrose equation for the source reduced operator `AP` extracted
    from the repository Moore--Penrose certificate structure. -/
theorem theorem20_8_penrose1_of_rectMoorePenrosePseudoinverse
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B Bplus) APplus) :
    rectMatMul (rectMatMul (theorem20_8AP A B Bplus) APplus)
        (theorem20_8AP A B Bplus) =
      theorem20_8AP A B Bplus :=
  hMP.reproduces_matrix
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    if the columns of `APᵀ` lie in the constraint nullspace and `APplus` is a
    Moore--Penrose pseudoinverse of `AP`, then the columns of `APplus` also lie
    in the constraint nullspace.  This uses the Penrose domain-projection
    symmetry to express the range of `APplus` through the row space of `AP`. -/
theorem theorem20_8_APplus_constraint_annihilates_of_MP_transpose_constraint
    {m n p : ℕ}
    (AP : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ)
    (hMP : RectMoorePenrosePseudoinverse m n AP APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose AP) =
        (fun _i : Fin p => fun _j : Fin m => 0)) :
    rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0) := by
  have hBdomain :
      rectMatMul B (rectMatMul APplus AP) =
        (fun _i : Fin p => fun _j : Fin n => 0) := by
    ext i j
    calc
      rectMatMul B (rectMatMul APplus AP) i j =
          ∑ k : Fin n, B i k * rectMatMul APplus AP k j := rfl
      _ = ∑ k : Fin n, B i k * rectMatMul APplus AP j k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hMP.domain_projection_symmetric k j]
      _ = ∑ k : Fin n, B i k *
            (∑ l : Fin m, APplus j l * AP l k) := rfl
      _ = ∑ k : Fin n, ∑ l : Fin m,
            B i k * (APplus j l * AP l k) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
      _ = ∑ l : Fin m, ∑ k : Fin n,
            B i k * (APplus j l * AP l k) := by
          rw [Finset.sum_comm]
      _ = ∑ l : Fin m, APplus j l *
            (∑ k : Fin n, B i k * AP l k) := by
          apply Finset.sum_congr rfl
          intro l _
          calc
            (∑ k : Fin n, B i k * (APplus j l * AP l k)) =
                ∑ k : Fin n, APplus j l * (B i k * AP l k) := by
                apply Finset.sum_congr rfl
                intro k _
                ring
            _ = APplus j l * (∑ k : Fin n, B i k * AP l k) := by
                rw [Finset.mul_sum]
      _ = ∑ l : Fin m, APplus j l *
            rectMatMul B (finiteTranspose AP) i l := by
          rfl
      _ = ∑ l : Fin m, APplus j l * 0 := by
          apply Finset.sum_congr rfl
          intro l _
          have hl := congrFun (congrFun hBAPt i) l
          rw [hl]
      _ = 0 := by simp
  calc
    rectMatMul B APplus =
        rectMatMul B (rectMatMul (rectMatMul APplus AP) APplus) := by
        rw [hMP.reproduces_pseudoinverse]
    _ = rectMatMul (rectMatMul B (rectMatMul APplus AP)) APplus := by
        rw [← rectMatMul_assoc]
    _ = rectMatMul (fun _i : Fin p => fun _j : Fin n => 0) APplus := by
        rw [hBdomain]
    _ = (fun _i : Fin p => fun _j : Fin m => 0) := by
        ext i j
        unfold rectMatMul
        simp
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    a Moore--Penrose certificate for `(AP)^+`, the transpose-range certificate
    `B*(AP)^T = 0`, and (20.24)'s null-intersection condition together give the
    reduced-operator left inverse on `null(B)`. -/
theorem theorem20_8_AP_left_inverse_on_nullspace_of_MP_transpose_range_null_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B Bplus) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B Bplus)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus) z) = z :=
  theorem20_8_AP_left_inverse_on_nullspace_of_penrose1_matrix_range_null_nullIntersection
    A B Bplus APplus
      (theorem20_8_penrose1_of_rectMoorePenrosePseudoinverse
        A B Bplus APplus hMP)
      (theorem20_8_APplus_constraint_annihilates_of_MP_transpose_constraint
        (theorem20_8AP A B Bplus) B APplus hMP hBAPt)
      hnull
/-- Higham, 2nd ed., Chapter 20, equation (20.24):
    Moore--Penrose/transpose-range route to the matrix identity
    `(AP)^+ AP = P`.  The source rank conditions enter through the explicit
    right-inverse and null-intersection hypotheses. -/
theorem theorem20_8_APplus_AP_eq_projection_of_MP_transpose_range_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B Bplus) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B Bplus)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B) :
    rectMatMul APplus (theorem20_8AP A B Bplus) =
      theorem20_8Projection B Bplus :=
  theorem20_8_APplus_AP_eq_projection_of_AP_left_inverse_on_nullspace
    A B Bplus APplus hright
    (theorem20_8_AP_left_inverse_on_nullspace_of_MP_transpose_range_null_nullIntersection
      A B Bplus APplus hMP hBAPt hnull)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    a Moore--Penrose certificate for `(AP)^+`, matrix-level annihilation
    `B*(AP)^+ = 0`, and (20.24)'s null-intersection condition together give
    the reduced-operator left inverse on `null(B)`. -/
theorem theorem20_8_AP_left_inverse_on_nullspace_of_MP_matrix_range_null_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B Bplus) APplus)
    (hBAPplus : rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus) z) = z :=
  theorem20_8_AP_left_inverse_on_nullspace_of_penrose1_matrix_range_null_nullIntersection
    A B Bplus APplus
      (theorem20_8_penrose1_of_rectMoorePenrosePseudoinverse
        A B Bplus APplus hMP)
      hBAPplus hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    if the source projector `P = I - B^+B` fixes the columns of `(AP)^+`,
    then those columns satisfy the constraint nullspace equation. -/
theorem theorem20_8_APplus_constraint_annihilates_of_projection_range
    {m n p : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hProjAPplus :
      rectMatMul (theorem20_8Projection B Bplus) APplus = APplus) :
    rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0) := by
  calc
    rectMatMul B APplus =
        rectMatMul B (rectMatMul (theorem20_8Projection B Bplus) APplus) := by
          rw [hProjAPplus]
    _ = rectMatMul (rectMatMul B (theorem20_8Projection B Bplus)) APplus := by
          rw [rectMatMul_assoc]
    _ = rectMatMul (fun _i : Fin p => fun _j : Fin n => 0) APplus := by
          rw [theorem20_8Projection_constraint_zero B Bplus hright]
    _ = (fun _i : Fin p => fun _j : Fin m => 0) := by
          ext i j
          unfold rectMatMul
          simp
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    if the columns of `(AP)^+` satisfy the constraint nullspace equation, then
    the source projector `P = I - B^+B` fixes those columns. -/
theorem theorem20_8_APplus_projection_range_of_constraint_annihilates
    {m n p : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ)
    (hBAPplus :
      rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0)) :
    rectMatMul (theorem20_8Projection B Bplus) APplus = APplus := by
  apply rectMatMul_eq_of_forall_rectMatMulVec_eq
  intro w
  have hnull :
      rectMatMulVec B (rectMatMulVec APplus w) = (fun _i : Fin p => 0) := by
    calc
      rectMatMulVec B (rectMatMulVec APplus w) =
          rectMatMulVec (rectMatMul B APplus) w := by
            exact (rectMatMulVec_rectMatMul B APplus w).symm
      _ = rectMatMulVec (fun _i : Fin p => fun _j : Fin m => 0) w := by
            rw [hBAPplus]
      _ = (fun _i : Fin p => 0) := by
            ext i
            unfold rectMatMulVec
            simp
  calc
    rectMatMulVec (rectMatMul (theorem20_8Projection B Bplus) APplus) w =
        rectMatMulVec (theorem20_8Projection B Bplus)
          (rectMatMulVec APplus w) := by
          exact rectMatMulVec_rectMatMul (theorem20_8Projection B Bplus) APplus w
    _ = rectMatMulVec APplus w := by
          exact theorem20_8Projection_apply_nullspace B Bplus
            (rectMatMulVec APplus w) hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    a Moore--Penrose certificate for `AP` plus the transpose-range certificate
    `B*AP^T = 0` gives the projector-range identity
    `P*(AP)^+ = (AP)^+`. -/
theorem theorem20_8_APplus_projection_range_of_MP_transpose_constraint
    {m n p : ℕ}
    (AP : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hMP : RectMoorePenrosePseudoinverse m n AP APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose AP) =
        (fun _i : Fin p => fun _j : Fin m => 0)) :
    rectMatMul (theorem20_8Projection B Bplus) APplus = APplus :=
  theorem20_8_APplus_projection_range_of_constraint_annihilates B Bplus
    APplus
    (theorem20_8_APplus_constraint_annihilates_of_MP_transpose_constraint
      AP B APplus hMP hBAPt)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source reduced-operator specialization of the MP/transpose-range
    projector-range bridge for `AP = A(I-B^+B)`. -/
theorem theorem20_8_APplus_projection_range_of_MP_transpose_range
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B Bplus) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B Bplus)) =
        (fun _i : Fin p => fun _j : Fin m => 0)) :
    rectMatMul (theorem20_8Projection B Bplus) APplus = APplus :=
  theorem20_8_APplus_projection_range_of_MP_transpose_constraint
    (theorem20_8AP A B Bplus) B Bplus APplus hMP hBAPt
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the reduced-operator left inverse follows from a Moore--Penrose certificate
    for `(AP)^+`, a projector-range certificate `P*(AP)^+ = (AP)^+`, source
    right-invertibility of `B^+`, and (20.24)'s null-intersection condition. -/
theorem theorem20_8_AP_left_inverse_on_nullspace_of_MP_projection_range_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B Bplus) APplus)
    (hProjAPplus :
      rectMatMul (theorem20_8Projection B Bplus) APplus = APplus)
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B Bplus) z) = z :=
  theorem20_8_AP_left_inverse_on_nullspace_of_MP_matrix_range_null_nullIntersection
    A B Bplus APplus hMP
      (theorem20_8_APplus_constraint_annihilates_of_projection_range
        B Bplus APplus hright hProjAPplus)
      hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source full row rank instantiates the projector-range-to-annihilation bridge
    for the noncomputable right inverse obtained from `rank(B)=p`. -/
theorem LSEFullRowRank.theorem20_8_APplus_constraint_annihilates_of_projection_range
    {m n p : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hProjAPplus :
      rectMatMul (theorem20_8Projection B hB.rightInverse) APplus = APplus) :
    rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0) :=
  _root_.NumStability.theorem20_8_APplus_constraint_annihilates_of_projection_range
    B hB.rightInverse APplus hB.rightInverse_spec hProjAPplus
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source full row rank instantiates the annihilation-to-projector-range bridge
    for the noncomputable right inverse obtained from `rank(B)=p`. -/
theorem LSEFullRowRank.theorem20_8_APplus_projection_range_of_constraint_annihilates
    {m n p : ℕ}
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hBAPplus :
      rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0)) :
    rectMatMul (theorem20_8Projection B hB.rightInverse) APplus = APplus :=
  _root_.NumStability.theorem20_8_APplus_projection_range_of_constraint_annihilates
    B hB.rightInverse APplus hBAPplus
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank specialization of the MP/transpose-range
    projector-range bridge for `AP = A(I-B^+B)`. -/
theorem LSEFullRowRank.theorem20_8_APplus_projection_range_of_MP_transpose_range
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0)) :
    rectMatMul (theorem20_8Projection B hB.rightInverse) APplus = APplus :=
  _root_.NumStability.theorem20_8_APplus_projection_range_of_MP_transpose_range
    A B hB.rightInverse APplus hMP hBAPt
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank form of the current Moore--Penrose/projector-range
    reduced-left-inverse route.  The remaining supplied hypotheses are the
    source-specific Moore--Penrose certificate for `(AP)^+`, the projector-range
    certificate, and (20.24)'s null-intersection condition. -/
theorem
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_projection_range_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hProjAPplus :
      rectMatMul (theorem20_8Projection B hB.rightInverse) APplus = APplus)
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
  _root_.NumStability.theorem20_8_AP_left_inverse_on_nullspace_of_MP_projection_range_nullIntersection
    A B hB.rightInverse APplus hB.rightInverse_spec hMP hProjAPplus hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank form of the Moore--Penrose/matrix-annihilation
    reduced-left-inverse route.  This keeps the rank-tolerant Moore--Penrose
    certificate abstract and uses the direct source-shaped range certificate
    `B*(AP)^+ = 0`, rather than the stronger projector-range equality. -/
theorem
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_matrix_range_null_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPplus :
      rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
  _root_.NumStability.theorem20_8_AP_left_inverse_on_nullspace_of_MP_matrix_range_null_nullIntersection
    A B hB.rightInverse APplus hMP hBAPplus hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank projected-difference handoff from a Moore--Penrose
    certificate, the matrix-annihilation certificate `B*(AP)^+ = 0`,
    (20.24)'s null-intersection condition, and the remaining reduced
    `AP*(y-x)` equation. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_MP_matrix_range_null_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPplus :
      rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_matrix_range_null_nullIntersection
      A hB APplus hMP hBAPplus hnull
  exact
    _root_.NumStability.theorem20_8_projected_difference_eq_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
      A DeltaA Deltab B DeltaB hB.rightInverse APplus Deltad y x
      hB.rightInverse_spec hAPleft_null hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank exact correction-vector identity with the reduced
    projector action discharged by a Moore--Penrose certificate and
    `B*(AP)^+ = 0`. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_matrix_range_null_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPplus :
      rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B hB.rightInverse APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j := by
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_matrix_range_null_nullIntersection
      A hB APplus hMP hBAPplus hnull
  exact
    _root_.NumStability.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
      A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad y x hx hy
      hB.rightInverse_spec hAPleft_null hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank form of the Moore--Penrose/transpose-range
    reduced-left-inverse route.  This replaces the direct matrix-annihilation
    certificate `B*(AP)^+ = 0` by `B*(AP)^T = 0` plus the Penrose fields for
    the chosen rank-tolerant pseudoinverse. -/
theorem
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_transpose_range_null_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
  _root_.NumStability.theorem20_8_AP_left_inverse_on_nullspace_of_MP_transpose_range_null_nullIntersection
    A B hB.rightInverse APplus hMP hBAPt hnull
/-- Higham, 2nd ed., Chapter 20, equation (20.24):
    source-full-row-rank Moore--Penrose/transpose-range route to the matrix
    identity `(AP)^+ AP = P`. -/
theorem
    LSEFullRowRank.theorem20_8_APplus_AP_eq_projection_of_MP_transpose_range_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B) :
    rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
      theorem20_8Projection B hB.rightInverse :=
  _root_.NumStability.theorem20_8_APplus_AP_eq_projection_of_MP_transpose_range_nullIntersection
    A B hB.rightInverse APplus hB.rightInverse_spec hMP hBAPt hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank projected-difference handoff from a Moore--Penrose
    certificate, the transpose-range certificate `B*(AP)^T = 0`, (20.24)'s
    null-intersection condition, and the remaining reduced `AP*(y-x)`
    equation. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_MP_transpose_range_null_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_transpose_range_null_nullIntersection
      A hB APplus hMP hBAPt hnull
  exact
    _root_.NumStability.theorem20_8_projected_difference_eq_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
      A DeltaA Deltab B DeltaB hB.rightInverse APplus Deltad y x
      hB.rightInverse_spec hAPleft_null hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank exact correction-vector identity with the reduced
    projector action discharged by a Moore--Penrose certificate and
    transpose-range certificate `B*(AP)^T = 0`. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_transpose_range_null_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B hB.rightInverse APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j := by
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_transpose_range_null_nullIntersection
      A hB APplus hMP hBAPt hnull
  exact
    _root_.NumStability.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
      A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad y x hx hy
      hB.rightInverse_spec hAPleft_null hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank projected-difference handoff from a Moore--Penrose
    certificate, a projector-range certificate, (20.24)'s null-intersection
    condition, and the remaining reduced `AP*(y-x)` equation. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_MP_projection_range_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hProjAPplus :
      rectMatMul (theorem20_8Projection B hB.rightInverse) APplus = APplus)
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_projection_range_nullIntersection
      A hB APplus hMP hProjAPplus hnull
  exact
    _root_.NumStability.theorem20_8_projected_difference_eq_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
      A DeltaA Deltab B DeltaB hB.rightInverse APplus Deltad y x
      hB.rightInverse_spec hAPleft_null hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank exact correction-vector identity with the reduced
    projector action discharged by Moore--Penrose/projector-range certificates. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_projection_range_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hProjAPplus :
      rectMatMul (theorem20_8Projection B hB.rightInverse) APplus = APplus)
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B hB.rightInverse APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j := by
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_projection_range_nullIntersection
      A hB APplus hMP hProjAPplus hnull
  exact
    _root_.NumStability.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
      A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad y x hx hy
      hB.rightInverse_spec hAPleft_null hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    determinant-facing Moore--Penrose certificate for the concrete Gram table
    chosen for `(AP)^+` in the source-full-row-rank route.  This instantiates
    the shared Chapter 21 pseudoinverse construction at the reduced operator
    `AP = A(I - B^+B)`. -/
theorem
    LSEFullRowRank.theorem20_8_rectMoorePenrosePseudoinverse_AP_of_gram_det_ne_zero
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (hdet :
      Matrix.det
        (rectGram (theorem20_8AP A B hB.rightInverse) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    RectMoorePenrosePseudoinverse m n
      (theorem20_8AP A B hB.rightInverse)
      (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse)) :=
  higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero
    (theorem20_8AP A B hB.rightInverse) hdet
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    concrete Gram-table form of the projector-range-to-annihilation bridge.
    The remaining source-specific hypothesis is the projector-range certificate
    `P*(AP)^+ = (AP)^+` for the chosen Gram pseudoinverse. -/
theorem
    LSEFullRowRank.theorem20_8_gram_APplus_constraint_annihilates_of_projection_range
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (hProjAPplus :
      rectMatMul (theorem20_8Projection B hB.rightInverse)
          (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse)) =
        undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse)) :
    rectMatMul B
        (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse)) =
      (fun _i : Fin p => fun _j : Fin m => 0) :=
  LSEFullRowRank.theorem20_8_APplus_constraint_annihilates_of_projection_range
    hB (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
    hProjAPplus
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    for the concrete Gram pseudoinverse of `AP`, the matrix annihilation
    certificate `B*(AP)^+ = 0` follows from the simpler transpose-range
    certificate `B*(AP)^T = 0`. -/
theorem theorem20_8_gram_APplus_constraint_annihilates_of_AP_transpose_constraint
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B Bplus)) =
        (fun _i : Fin p => fun _j : Fin m => 0)) :
    rectMatMul B
        (undetAplusOfGramNonsingInv (theorem20_8AP A B Bplus)) =
      (fun _i : Fin p => fun _j : Fin m => 0) := by
  calc
    rectMatMul B
        (undetAplusOfGramNonsingInv (theorem20_8AP A B Bplus)) =
        rectMatMul B
          (rectMatMul (finiteTranspose (theorem20_8AP A B Bplus))
            (undetGramNonsingInv (theorem20_8AP A B Bplus))) := by
          rw [undetAplusOfGramNonsingInv]
          rw [undetAplusOfGramInv_eq_rectMatMul_finiteTranspose]
    _ =
        rectMatMul
          (rectMatMul B (finiteTranspose (theorem20_8AP A B Bplus)))
          (undetGramNonsingInv (theorem20_8AP A B Bplus)) := by
          rw [rectMatMul_assoc]
    _ =
        rectMatMul (fun _i : Fin p => fun _j : Fin m => 0)
          (undetGramNonsingInv (theorem20_8AP A B Bplus)) := by
          rw [hBAPt]
    _ = (fun _i : Fin p => fun _j : Fin m => 0) := by
          ext i j
          unfold rectMatMul
          simp
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    if `P = I - B^+B` is symmetric, then the reduced-operator transpose
    columns lie in the constraint nullspace: `B*(AP)^T = 0`. -/
theorem theorem20_8_AP_transpose_constraint_annihilates_of_projection_symmetric
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hPsym : IsSymmetricFiniteMatrix (theorem20_8Projection B Bplus)) :
    rectMatMul B (finiteTranspose (theorem20_8AP A B Bplus)) =
      (fun _i : Fin p => fun _j : Fin m => 0) := by
  let P : Fin n → Fin n → ℝ := theorem20_8Projection B Bplus
  have hBP : rectMatMul B P = (fun _i : Fin p => fun _j : Fin n => 0) :=
    theorem20_8Projection_constraint_zero B Bplus hright
  have hPsymP : IsSymmetricFiniteMatrix P := hPsym
  ext i l
  change (∑ j : Fin n, B i j * (∑ k : Fin n, A l k * P k j)) = 0
  calc
    (∑ j : Fin n, B i j * (∑ k : Fin n, A l k * P k j)) =
        ∑ j : Fin n, ∑ k : Fin n, B i j * (A l k * P k j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ j : Fin n, B i j * (A l k * P k j) := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n, A l k * (∑ j : Fin n, B i j * P j k) := by
          apply Finset.sum_congr rfl
          intro k _
          calc
            (∑ j : Fin n, B i j * (A l k * P k j)) =
                ∑ j : Fin n, A l k * (B i j * P j k) := by
                  apply Finset.sum_congr rfl
                  intro j _
                  rw [hPsymP k j]
                  ring
            _ = A l k * (∑ j : Fin n, B i j * P j k) := by
                  rw [Finset.mul_sum]
    _ = ∑ k : Fin n, A l k * 0 := by
          apply Finset.sum_congr rfl
          intro k _
          rw [show (∑ j : Fin n, B i j * P j k) = 0 by
            have hBPik := congrFun (congrFun hBP i) k
            simpa [rectMatMul] using hBPik]
    _ = 0 := by simp
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank specialization of the transpose-range-to-annihilation
    bridge for the concrete Gram table chosen for `(AP)^+`. -/
theorem
    LSEFullRowRank.theorem20_8_gram_APplus_constraint_annihilates_of_AP_transpose_constraint
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (hBAPt :
      rectMatMul B
          (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0)) :
    rectMatMul B
        (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse)) =
      (fun _i : Fin p => fun _j : Fin m => 0) :=
  _root_.NumStability.theorem20_8_gram_APplus_constraint_annihilates_of_AP_transpose_constraint
    A B hB.rightInverse hBAPt
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank specialization of the symmetric-projector proof of
    `B*(AP)^T = 0`. -/
theorem LSEFullRowRank.theorem20_8_AP_transpose_constraint_annihilates_of_projection_symmetric
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (hPsym : IsSymmetricFiniteMatrix (theorem20_8Projection B hB.rightInverse)) :
    rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
      (fun _i : Fin p => fun _j : Fin m => 0) :=
  _root_.NumStability.theorem20_8_AP_transpose_constraint_annihilates_of_projection_symmetric
    A B hB.rightInverse hB.rightInverse_spec hPsym
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    `P = I - B^+B` is symmetric whenever the domain projection `B^+B` is
    symmetric. -/
theorem theorem20_8Projection_symmetric_of_domain_projection_symmetric
    {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (hDom : IsSymmetricFiniteMatrix (rectMatMul Bplus B)) :
    IsSymmetricFiniteMatrix (theorem20_8Projection B Bplus) := by
  intro i j
  have hid : idMatrix n i j = idMatrix n j i := by
    unfold idMatrix
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Ne.symm hij]
  calc
    theorem20_8Projection B Bplus i j =
        idMatrix n i j - rectMatMul Bplus B i j := rfl
    _ = idMatrix n j i - rectMatMul Bplus B j i := by
          rw [hid, hDom i j]
    _ = theorem20_8Projection B Bplus j i := rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    the Gram pseudoinverse `B^T(BB^T)^{-1}` gives a symmetric source projector
    `P = I - B^+B`. -/
theorem theorem20_8Projection_symmetric_of_gram_pseudoinverse
    {p n : ℕ}
    (B : Fin p → Fin n → ℝ) :
    IsSymmetricFiniteMatrix
      (theorem20_8Projection B (undetAplusOfGramNonsingInv B)) :=
  theorem20_8Projection_symmetric_of_domain_projection_symmetric
    B (undetAplusOfGramNonsingInv B)
    (undetAplusOfGramNonsingInv_domain_projection_symmetric B)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    determinant-facing Gram-pseudoinverse version of the source-projector proof
    of `B*(AP)^T = 0`. -/
theorem theorem20_8_AP_transpose_constraint_annihilates_of_gram_projection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (hdetB : Matrix.det (rectGram B : Matrix (Fin p) (Fin p) ℝ) ≠ 0) :
    rectMatMul B
        (finiteTranspose
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B))) =
      (fun _i : Fin p => fun _j : Fin m => 0) :=
  theorem20_8_AP_transpose_constraint_annihilates_of_projection_symmetric
    A B (undetAplusOfGramNonsingInv B)
    (higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero B hdetB)
    (theorem20_8Projection_symmetric_of_gram_pseudoinverse B)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    determinant-facing Gram-pseudoinverse route to the matrix annihilation
    certificate `B*(AP)^+ = 0`, using the Gram pseudoinverse for `B`. -/
theorem theorem20_8_gram_APplus_constraint_annihilates_of_gram_projection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (hdetB : Matrix.det (rectGram B : Matrix (Fin p) (Fin p) ℝ) ≠ 0) :
    rectMatMul B
        (undetAplusOfGramNonsingInv
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B))) =
      (fun _i : Fin p => fun _j : Fin m => 0) :=
  theorem20_8_gram_APplus_constraint_annihilates_of_AP_transpose_constraint
    A B (undetAplusOfGramNonsingInv B)
    (theorem20_8_AP_transpose_constraint_annihilates_of_gram_projection A B hdetB)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    determinant-facing reduced left-inverse route using the Gram pseudoinverse
    for `B` and the concrete Gram pseudoinverse for `AP`. -/
theorem theorem20_8_AP_left_inverse_on_nullspace_of_gram_MP_gram_projection_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (hdetB : Matrix.det (rectGram B : Matrix (Fin p) (Fin p) ℝ) ≠ 0)
    (hdetAP :
      Matrix.det
        (rectGram (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec
            (undetAplusOfGramNonsingInv
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)))
            (rectMatMulVec
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) z) = z :=
  theorem20_8_AP_left_inverse_on_nullspace_of_MP_matrix_range_null_nullIntersection
    A B (undetAplusOfGramNonsingInv B)
    (undetAplusOfGramNonsingInv
      (theorem20_8AP A B (undetAplusOfGramNonsingInv B)))
    (higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero
      (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) hdetAP)
    (theorem20_8_gram_APplus_constraint_annihilates_of_gram_projection A B hdetB)
    hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    full-row-rank-facing version of the Gram-pseudoinverse reduced left-inverse
    route.  The source rank hypothesis discharges nonsingularity of `B Bᵀ`;
    nonsingularity of the reduced Gram matrix `(AP)(AP)ᵀ` remains explicit. -/
theorem
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_gram_MP_gram_projection_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (hdetAP :
      Matrix.det
        (rectGram (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec
            (undetAplusOfGramNonsingInv
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)))
            (rectMatMulVec
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) z) = z :=
  _root_.NumStability.theorem20_8_AP_left_inverse_on_nullspace_of_gram_MP_gram_projection_nullIntersection
    A B hB.rectGram_det_ne_zero hdetAP hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank reduced left-inverse route using the Gram
    pseudoinverse for `B` and an abstract rank-tolerant Moore--Penrose
    pseudoinverse for `AP`.  The transpose-range certificate is discharged
    from the symmetric Gram projector for `B`. -/
theorem
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_gram_projection_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus)
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec
            (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) z) = z :=
  _root_.NumStability.theorem20_8_AP_left_inverse_on_nullspace_of_MP_transpose_range_null_nullIntersection
    A B (undetAplusOfGramNonsingInv B) APplus hMP
    (theorem20_8_AP_transpose_constraint_annihilates_of_gram_projection
      A B hB.rectGram_det_ne_zero)
    hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank projected-difference handoff using the Gram
    pseudoinverse for `B` and an abstract rank-tolerant `(AP)^+`. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_MP_gram_projection_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus)
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec (undetAplusOfGramNonsingInv B)
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B (undetAplusOfGramNonsingInv B))
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec (undetAplusOfGramNonsingInv B)
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  have hright :
      rectMatMul B (undetAplusOfGramNonsingInv B) = idMatrix p :=
    higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
      B hB.rectGram_det_ne_zero
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_gram_projection_nullIntersection
      A hB APplus hMP hnull
  exact
    _root_.NumStability.theorem20_8_projected_difference_eq_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
      A DeltaA Deltab B DeltaB (undetAplusOfGramNonsingInv B) APplus
      Deltad y x hright hAPleft_null hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-full-row-rank exact correction-vector identity using the Gram
    pseudoinverse for `B` and an abstract rank-tolerant `(AP)^+`. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_gram_projection_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus)
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec (undetAplusOfGramNonsingInv B)
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j := by
  have hright :
      rectMatMul B (undetAplusOfGramNonsingInv B) = idMatrix p :=
    higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
      B hB.rectGram_det_ne_zero
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_gram_projection_nullIntersection
      A hB APplus hMP hnull
  exact
    _root_.NumStability.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
      A DeltaA b Deltab B DeltaB (undetAplusOfGramNonsingInv B) APplus
      d Deltad y x hx hy hright hAPleft_null hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    determinant-facing reduced left-inverse route for the concrete Gram
    pseudoinverse of `AP`, using the weaker matrix annihilation certificate
    `B*(AP)^+ = 0` directly. -/
theorem
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_gram_MP_matrix_range_null_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (hdet :
      Matrix.det
        (rectGram (theorem20_8AP A B hB.rightInverse) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hBAPplus :
      rectMatMul B
          (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec
            (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
            (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
  _root_.NumStability.theorem20_8_AP_left_inverse_on_nullspace_of_MP_matrix_range_null_nullIntersection
    A B hB.rightInverse
    (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
    (LSEFullRowRank.theorem20_8_rectMoorePenrosePseudoinverse_AP_of_gram_det_ne_zero
      A hB hdet)
    hBAPplus hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    determinant-facing reduced left-inverse route for the concrete Gram
    pseudoinverse of `AP`, reducing matrix annihilation to the transpose-range
    certificate `B*(AP)^T = 0`. -/
theorem
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_gram_MP_transpose_range_null_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (hdet :
      Matrix.det
        (rectGram (theorem20_8AP A B hB.rightInverse) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hBAPt :
      rectMatMul B
          (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec
            (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
            (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
  LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_gram_MP_matrix_range_null_nullIntersection
    A hB hdet
    (LSEFullRowRank.theorem20_8_gram_APplus_constraint_annihilates_of_AP_transpose_constraint
      A hB hBAPt)
    hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    determinant-facing reduced left-inverse route for the concrete Gram
    pseudoinverse of `AP`.  The Moore--Penrose certificate is now discharged
    by nonsingularity of `rectGram(AP)`; the projector-range certificate and
    (20.24)'s null-intersection condition remain visible. -/
theorem
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_gram_MP_projection_range_nullIntersection
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (hdet :
      Matrix.det
        (rectGram (theorem20_8AP A B hB.rightInverse) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hProjAPplus :
      rectMatMul (theorem20_8Projection B hB.rightInverse)
          (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse)) =
        undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
    (hnull : LSENullIntersectionTrivial A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec
            (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
            (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
  LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_projection_range_nullIntersection
    A hB (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
      (LSEFullRowRank.theorem20_8_rectMoorePenrosePseudoinverse_AP_of_gram_det_ne_zero
        A hB hdet)
      hProjAPplus hnull
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    concrete Gram-pseudoinverse form of the projected-difference handoff using
    the matrix annihilation certificate `B*(AP)^+ = 0` directly. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_gram_APplus_of_matrix_range_null_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hdet :
      Matrix.det
        (rectGram (theorem20_8AP A B hB.rightInverse) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hBAPplus :
      rectMatMul B
          (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec
            (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec
            (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
            (rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec
              (undetAplusOfGramNonsingInv
                (theorem20_8AP A B hB.rightInverse))
              (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_gram_MP_matrix_range_null_nullIntersection
      A hB hdet hBAPplus hnull
  exact
    _root_.NumStability.theorem20_8_projected_difference_eq_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
      A DeltaA Deltab B DeltaB hB.rightInverse
      (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
      Deltad y x hB.rightInverse_spec hAPleft_null hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    concrete Gram-pseudoinverse projected-difference handoff from the
    transpose-range certificate `B*(AP)^T = 0`. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_gram_APplus_of_transpose_range_null_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hdet :
      Matrix.det
        (rectGram (theorem20_8AP A B hB.rightInverse) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hBAPt :
      rectMatMul B
          (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec
            (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec
            (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
            (rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j :=
  LSEFullRowRank.theorem20_8_projected_difference_eq_gram_APplus_of_matrix_range_null_nullIntersection_reduced_difference_eq
    A DeltaA Deltab hB DeltaB Deltad y x hdet
    (LSEFullRowRank.theorem20_8_gram_APplus_constraint_annihilates_of_AP_transpose_constraint
      A hB hBAPt)
    hnull hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    concrete Gram-pseudoinverse form of the projected-difference handoff.
    This removes the abstract Moore--Penrose certificate from the final route
    under the determinant hypothesis, while keeping the projector-range and
    reduced-`AP` equations explicit. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_gram_APplus_of_projection_range_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hdet :
      Matrix.det
        (rectGram (theorem20_8AP A B hB.rightInverse) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hProjAPplus :
      rectMatMul (theorem20_8Projection B hB.rightInverse)
          (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse)) =
        undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec
            (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec
            (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
            (rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j := by
  exact
    LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_MP_projection_range_nullIntersection_reduced_difference_eq
      A DeltaA Deltab hB DeltaB
      (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
      Deltad y x
      (LSEFullRowRank.theorem20_8_rectMoorePenrosePseudoinverse_AP_of_gram_det_ne_zero
        A hB hdet)
      hProjAPplus hnull hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    concrete Gram-pseudoinverse exact correction-vector identity using the
    matrix annihilation certificate `B*(AP)^+ = 0` directly. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_gram_APplus_of_matrix_range_null_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (d Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hdet :
      Matrix.det
        (rectGram (theorem20_8AP A B hB.rightInverse) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hBAPplus :
      rectMatMul B
          (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B hB.rightInverse
              (undetAplusOfGramNonsingInv
                (theorem20_8AP A B hB.rightInverse)))
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec
            (undetAplusOfGramNonsingInv
              (theorem20_8AP A B hB.rightInverse))
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j := by
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec
              (undetAplusOfGramNonsingInv
                (theorem20_8AP A B hB.rightInverse))
              (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_gram_MP_matrix_range_null_nullIntersection
      A hB hdet hBAPplus hnull
  exact
    _root_.NumStability.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_AP_left_inverse_on_nullspace_reduced_difference_eq
      A DeltaA b Deltab B DeltaB hB.rightInverse
      (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
      d Deltad y x hx hy hB.rightInverse_spec hAPleft_null hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    concrete Gram-pseudoinverse exact correction-vector identity from the
    transpose-range certificate `B*(AP)^T = 0`. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_gram_APplus_of_transpose_range_null_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (d Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hdet :
      Matrix.det
        (rectGram (theorem20_8AP A B hB.rightInverse) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hBAPt :
      rectMatMul B
          (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B hB.rightInverse
              (undetAplusOfGramNonsingInv
                (theorem20_8AP A B hB.rightInverse)))
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec
            (undetAplusOfGramNonsingInv
              (theorem20_8AP A B hB.rightInverse))
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j :=
  LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_gram_APplus_of_matrix_range_null_nullIntersection_reduced_difference_eq
    A DeltaA b Deltab hB DeltaB d Deltad y x hx hy hdet
    (LSEFullRowRank.theorem20_8_gram_APplus_constraint_annihilates_of_AP_transpose_constraint
      A hB hBAPt)
    hnull hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    concrete Gram-pseudoinverse form of the exact printed correction-vector
    identity. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_gram_APplus_of_projection_range_nullIntersection_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (d Deltad : Fin p → ℝ)
    (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hdet :
      Matrix.det
        (rectGram (theorem20_8AP A B hB.rightInverse) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hProjAPplus :
      rectMatMul (theorem20_8Projection B hB.rightInverse)
          (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse)) =
        undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
    (hnull : LSENullIntersectionTrivial A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B hB.rightInverse
              (undetAplusOfGramNonsingInv
                (theorem20_8AP A B hB.rightInverse)))
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec
            (undetAplusOfGramNonsingInv
              (theorem20_8AP A B hB.rightInverse))
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j := by
  exact
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_projection_range_nullIntersection_reduced_difference_eq
      A DeltaA b Deltab hB DeltaB
      (undetAplusOfGramNonsingInv (theorem20_8AP A B hB.rightInverse))
      d Deltad y x hx hy
      (LSEFullRowRank.theorem20_8_rectMoorePenrosePseudoinverse_AP_of_gram_det_ne_zero
        A hB hdet)
      hProjAPplus hnull hAPdiff
/-- Higham, 2nd ed., Chapter 20, equation (20.24): vertical stack
    `[A; B]`, the local representation of `[A^T, B^T]^T`. -/
noncomputable def lseStackedMatrix {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) :
    Fin (m + p) → Fin n → ℝ :=
  Fin.append A B
/-- Multiplication by the vertical stack `[A; B]` splits into the two source
    actions `A x` and `B x`. -/
theorem lseStackedMatrix_mulVec {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (x : Fin n → ℝ) :
    rectMatMulVec (lseStackedMatrix A B) x =
      Fin.append (rectMatMulVec A x) (rectMatMulVec B x) := by
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (m + p) =>
      rectMatMulVec (lseStackedMatrix A B) x i =
        Fin.append (rectMatMulVec A x) (rectMatMulVec B x) i)
    ?left ?right i
  · intro i
    unfold rectMatMulVec lseStackedMatrix
    simp [Fin.append_left]
  · intro i
    unfold rectMatMulVec lseStackedMatrix
    simp [Fin.append_right]
/-- Kernel splitting for the stacked matrix `[A; B]` in (20.24). -/
theorem lseStackedMatrix_mulVec_eq_zero_iff {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (v : Fin n → ℝ) :
    rectMatMulVec (lseStackedMatrix A B) v = 0 ↔
      rectMatMulVec A v = 0 ∧ rectMatMulVec B v = 0 := by
  constructor
  · intro h
    constructor
    · ext i
      have hi := congrFun h (Fin.castAdd p i)
      rw [congrFun (lseStackedMatrix_mulVec A B v) (Fin.castAdd p i)] at hi
      simpa [Fin.append_left] using hi
    · ext i
      have hi := congrFun h (Fin.natAdd m i)
      rw [congrFun (lseStackedMatrix_mulVec A B v) (Fin.natAdd m i)] at hi
      simpa [Fin.append_right] using hi
  · rintro ⟨hA, hB⟩
    ext i
    rw [congrFun (lseStackedMatrix_mulVec A B v) i]
    refine Fin.addCases
      (motive := fun i : Fin (m + p) =>
        Fin.append (rectMatMulVec A v) (rectMatMulVec B v) i = 0)
      ?left ?right i
    · intro i
      simpa [Fin.append_left] using congrFun hA i
    · intro i
      simpa [Fin.append_right] using congrFun hB i
/-- Local finite-dimensional formulation of the source statement that
    `[A^T, B^T]^T` has full column rank. -/
def LSEStackedFullColumnRank {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) : Prop :=
  Function.Injective (rectMatMulVec (lseStackedMatrix A B))
/-- With no constraint rows, full column rank of the stacked LSE matrix
    `[A; B]` is exactly injectivity of the ordinary least-squares matrix
    action of `A`. -/
theorem lseStackedFullColumnRank_empty_constraints_iff {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin 0 → Fin n → ℝ) :
    LSEStackedFullColumnRank A B ↔
      Function.Injective (rectMatMulVec A) := by
  constructor
  · intro hStack x y hxy
    apply hStack
    ext i
    rw [congrFun (lseStackedMatrix_mulVec A B x) i,
      congrFun (lseStackedMatrix_mulVec A B y) i]
    refine Fin.addCases
      (motive := fun i : Fin (m + 0) =>
        Fin.append (rectMatMulVec A x) (rectMatMulVec B x) i =
          Fin.append (rectMatMulVec A y) (rectMatMulVec B y) i)
      ?_ ?_ i
    · intro j
      simpa only [Fin.append_left] using congrFun hxy j
    · intro j
      exact Fin.elim0 j
  · intro hA x y hxy
    apply hA
    ext i
    have hi := congrFun hxy (Fin.castAdd 0 i)
    rw [congrFun (lseStackedMatrix_mulVec A B x) (Fin.castAdd 0 i),
      congrFun (lseStackedMatrix_mulVec A B y) (Fin.castAdd 0 i)] at hi
    simpa only [Fin.append_left] using hi
/-- For a square constraint matrix, full row rank also makes the constraint
    action injective.  This is the finite square specialization used by the
    `q = 0` boundary of Theorem 20.10. -/
theorem LSEFullRowRank.square_rectMatMulVec_injective {p : ℕ}
    {B : Fin p → Fin p → ℝ} (hB : LSEFullRowRank B) :
    Function.Injective (rectMatMulVec B) := by
  let Binv : Fin p → Fin p → ℝ := hB.rightInverse
  have hright : IsRightInverse p B Binv := by
    intro i j
    have hij := congrFun (congrFun hB.rightInverse_spec i) j
    simpa [Binv, rectMatMul, matMul, idMatrix] using hij
  have hleft : IsLeftInverse p B Binv :=
    isLeftInverse_of_isRightInverse B Binv hright
  have hBinvB : rectMatMul Binv B = idMatrix p := by
    ext i j
    simpa [rectMatMul, matMul, idMatrix] using hleft i j
  intro x y hxy
  have hxy' := congrArg (rectMatMulVec Binv) hxy
  calc
    x = rectMatMulVec (idMatrix p) x :=
      (rectMatMulVec_idMatrix x).symm
    _ = rectMatMulVec (rectMatMul Binv B) x := by rw [hBinvB]
    _ = rectMatMulVec Binv (rectMatMulVec B x) :=
      rectMatMulVec_rectMatMul Binv B x
    _ = rectMatMulVec Binv (rectMatMulVec B y) := hxy'
    _ = rectMatMulVec (rectMatMul Binv B) y :=
      (rectMatMulVec_rectMatMul Binv B y).symm
    _ = rectMatMulVec (idMatrix p) y := by rw [hBinvB]
    _ = y := rectMatMulVec_idMatrix y
/-- A square full-row-rank constraint block alone guarantees the stacked
    full-column-rank condition, independently of the least-squares block. -/
theorem LSEFullRowRank.square_lseStackedFullColumnRank {m p : ℕ}
    (A : Fin m → Fin p → ℝ) {B : Fin p → Fin p → ℝ}
    (hB : LSEFullRowRank B) :
    LSEStackedFullColumnRank A B := by
  have hBinj := hB.square_rectMatMulVec_injective
  intro x y hxy
  apply hBinj
  ext i
  have hi := congrFun hxy (Fin.natAdd m i)
  rw [congrFun (lseStackedMatrix_mulVec A B x) (Fin.natAdd m i),
    congrFun (lseStackedMatrix_mulVec A B y) (Fin.natAdd m i)] at hi
  simpa only [Fin.append_right] using hi
/-- For square full-row-rank constraints, every feasible point is the unique
    feasible point and hence minimizes any least-squares objective. -/
theorem LSEFullRowRank.isLSEMinimizer_of_square_feasible {m p : ℕ}
    (A : Fin m → Fin p → ℝ) (b : Fin m → ℝ)
    {B : Fin p → Fin p → ℝ} (d : Fin p → ℝ) (x : Fin p → ℝ)
    (hB : LSEFullRowRank B) (hx : LSEFeasible B d x) :
    IsLSEMinimizer A b B d x := by
  refine ⟨hx, ?_⟩
  intro y hy
  have hxy : x = y := hB.square_rectMatMulVec_injective (by
    ext i
    rw [hx i, hy i])
  rw [hxy]
/-- Pointwise perturbations commute with the local stacked LSE matrix
    representation `[A; B]`. -/
theorem lseStackedMatrix_add {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ)
    (B DeltaB : Fin p → Fin n → ℝ) :
    lseStackedMatrix (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j) =
      fun i j => lseStackedMatrix A B i j + lseStackedMatrix DeltaA DeltaB i j := by
  ext i j
  refine Fin.addCases
    (motive := fun i : Fin (m + p) =>
      lseStackedMatrix (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) i j =
        lseStackedMatrix A B i j + lseStackedMatrix DeltaA DeltaB i j)
    ?left ?right i
  · intro i
    simp [lseStackedMatrix, Fin.append_left]
  · intro i
    simp [lseStackedMatrix, Fin.append_right]
/-- The squared Frobenius norm of the stacked LSE matrix splits across the two
    row blocks. -/
theorem frobNormSqRect_lseStackedMatrix {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) :
    frobNormSqRect (lseStackedMatrix A B) =
      frobNormSqRect A + frobNormSqRect B := by
  unfold frobNormSqRect lseStackedMatrix
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- The Frobenius norm of the stacked LSE matrix is bounded by the sum of the
    Frobenius norms of the row blocks. -/
theorem frobNormRect_lseStackedMatrix_le_add {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) :
    frobNormRect (lseStackedMatrix A B) ≤ frobNormRect A + frobNormRect B := by
  have hsq :
      frobNormSqRect (lseStackedMatrix A B) ≤
        (frobNormRect A + frobNormRect B) ^ 2 := by
    rw [frobNormSqRect_lseStackedMatrix, ← frobNormRect_sq A,
      ← frobNormRect_sq B]
    have hmul_nonneg : 0 ≤ frobNormRect A * frobNormRect B :=
      mul_nonneg (frobNormRect_nonneg A) (frobNormRect_nonneg B)
    nlinarith
  calc
    frobNormRect (lseStackedMatrix A B)
        = Real.sqrt (frobNormSqRect (lseStackedMatrix A B)) := rfl
    _ ≤ Real.sqrt ((frobNormRect A + frobNormRect B) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = |frobNormRect A + frobNormRect B| := Real.sqrt_sq_eq_abs _
    _ = frobNormRect A + frobNormRect B :=
        abs_of_nonneg (add_nonneg (frobNormRect_nonneg A)
          (frobNormRect_nonneg B))
/-- Higham, 2nd ed., Chapter 20, equation (20.24), prose after the display:
    the null-intersection condition
    `null(A) ∩ null(B) = {0}` is equivalent to full column rank of
    `[A^T, B^T]^T`, represented locally as injectivity of `[A; B]`. -/
theorem LSENullIntersectionTrivial.iff_lseStackedFullColumnRank {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ) :
    LSENullIntersectionTrivial A B ↔ LSEStackedFullColumnRank A B := by
  constructor
  · intro hnull x y hxy
    have hdiff_zero :
        rectMatMulVec (lseStackedMatrix A B) (fun j => x j - y j) = 0 := by
      rw [rectMatMulVec_sub (lseStackedMatrix A B) x y]
      ext i
      exact sub_eq_zero.mpr (congrFun hxy i)
    have hparts := (lseStackedMatrix_mulVec_eq_zero_iff A B
      (fun j => x j - y j)).1 hdiff_zero
    have hzero := hnull (fun j => x j - y j) hparts.1 hparts.2
    ext j
    have hj := congrFun hzero j
    dsimp at hj
    linarith
  · intro hfull v hAv hBv
    have hstack_zero :
        rectMatMulVec (lseStackedMatrix A B) v = 0 :=
      (lseStackedMatrix_mulVec_eq_zero_iff A B v).2 ⟨hAv, hBv⟩
    have hzero_action :
        rectMatMulVec (lseStackedMatrix A B) v =
          rectMatMulVec (lseStackedMatrix A B) (0 : Fin n → ℝ) := by
      rw [hstack_zero]
      ext i
      simp [rectMatMulVec]
    exact hfull hzero_action
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 support:
    source-stacked-full-column-rank form of the Moore--Penrose/transpose-range
    reduced-left-inverse route.  This replaces the local null-intersection
    predicate by the printed full-column-rank condition for `[A^T, B^T]^T`. -/
theorem
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_transpose_range_lseStackedFullColumnRank
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B hB.rightInverse) z) = z :=
  LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_transpose_range_null_nullIntersection
    A hB APplus hMP hBAPt
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
/-- Higham, 2nd ed., Chapter 20, equation (20.24):
    source-stacked-full-column-rank Moore--Penrose/transpose-range route to
    the matrix identity `(AP)^+ AP = P`. -/
theorem
    LSEFullRowRank.theorem20_8_APplus_AP_eq_projection_of_MP_transpose_range_lseStackedFullColumnRank
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B) :
    rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
      theorem20_8Projection B hB.rightInverse :=
  LSEFullRowRank.theorem20_8_APplus_AP_eq_projection_of_MP_transpose_range_nullIntersection
    A hB APplus hMP hBAPt
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-stacked-full-column-rank projected action for the
    Moore--Penrose/transpose-range route. -/
theorem
    LSEFullRowRank.theorem20_8_projected_action_of_MP_transpose_range_lseStackedFullColumnRank
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (v : Fin n → ℝ) :
    rectMatMulVec APplus
        (rectMatMulVec (theorem20_8AP A B hB.rightInverse) v) =
      rectMatMulVec (theorem20_8Projection B hB.rightInverse) v :=
  _root_.NumStability.theorem20_8_projected_action_of_AP_left_inverse_on_nullspace
    A B hB.rightInverse APplus hB.rightInverse_spec
    (LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_transpose_range_lseStackedFullColumnRank
      A hB APplus hMP hBAPt hstack)
    v
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-stacked-full-column-rank exact same-residual correction-vector
    identity for the Moore--Penrose/transpose-range route. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_transpose_range_lseStackedFullColumnRank_same_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (r rHigh : Fin m → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hsame : r = rHigh) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B hB.rightInverse APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i) j := by
  have hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec (theorem20_8AP A B hB.rightInverse)
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec (theorem20_8Projection B hB.rightInverse)
          (fun k : Fin n => y k - x k) :=
    LSEFullRowRank.theorem20_8_projected_action_of_MP_transpose_range_lseStackedFullColumnRank
      A hB APplus hMP hBAPt hstack (fun k => y k - x k)
  exact
    _root_.NumStability.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_same_higham_residual_projected_action
      A DeltaA b Deltab B DeltaB hB.rightInverse APplus d Deltad x y
      r rHigh hAPaction hx hy hr hres hsame
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-stacked-full-column-rank projected-difference handoff for the
    Moore--Penrose/transpose-range route. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_MP_transpose_range_lseStackedFullColumnRank_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B hB.rightInverse)
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j :=
  LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_MP_transpose_range_null_nullIntersection_reduced_difference_eq
    A DeltaA Deltab hB DeltaB APplus Deltad y x hMP hBAPt
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
    hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source-stacked-full-column-rank exact correction-vector identity for the
    Moore--Penrose/transpose-range route. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_transpose_range_lseStackedFullColumnRank_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B hB.rightInverse) APplus)
    (hBAPt :
      rectMatMul B (finiteTranspose (theorem20_8AP A B hB.rightInverse)) =
        (fun _i : Fin p => fun _j : Fin m => 0))
    (hstack : LSEStackedFullColumnRank A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B hB.rightInverse)
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec hB.rightInverse
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B hB.rightInverse APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j :=
  LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_transpose_range_null_nullIntersection_reduced_difference_eq
    A DeltaA b Deltab hB DeltaB APplus d Deltad y x hx hy hMP hBAPt
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
    hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source stacked-full-column-rank form of the rank-tolerant Gram-`B`
    Moore--Penrose left-inverse route.  The printed rank condition for
    `[A^T, B^T]^T` supplies the null-intersection hypothesis. -/
theorem
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_gram_projection_lseStackedFullColumnRank
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus)
    (hstack : LSEStackedFullColumnRank A B) :
    ∀ z : Fin n → ℝ,
      rectMatMulVec B z = (fun _i : Fin p => 0) →
        rectMatMulVec APplus
          (rectMatMulVec
            (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) z) = z :=
  LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_gram_projection_nullIntersection
    A hB APplus hMP
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source stacked-full-column-rank projected-difference handoff using the
    Gram pseudoinverse for `B` and an abstract rank-tolerant `(AP)^+`. -/
theorem
    LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_MP_gram_projection_lseStackedFullColumnRank_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus)
    (hstack : LSEStackedFullColumnRank A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec (undetAplusOfGramNonsingInv B)
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    rectMatMulVec (theorem20_8Projection B (undetAplusOfGramNonsingInv B))
        (fun k : Fin n => y k - x k) =
      fun j : Fin n =>
        rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j -
          rectMatMulVec APplus
            (rectMatMulVec A
              (rectMatMulVec (undetAplusOfGramNonsingInv B)
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l))) j :=
  LSEFullRowRank.theorem20_8_projected_difference_eq_APplus_of_MP_gram_projection_nullIntersection_reduced_difference_eq
    A DeltaA Deltab hB DeltaB APplus Deltad y x hMP
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
    hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source stacked-full-column-rank exact correction-vector identity using
    the Gram pseudoinverse for `B` and an abstract rank-tolerant `(AP)^+`. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_gram_projection_lseStackedFullColumnRank_reduced_difference_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (y x : Fin n → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus)
    (hstack : LSEStackedFullColumnRank A B)
    (hAPdiff :
      rectMatMulVec (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
          (fun k : Fin n => y k - x k) =
        fun i : Fin m =>
          (rectMatMulVec DeltaA y i - Deltab i) -
            rectMatMulVec A
              (rectMatMulVec (undetAplusOfGramNonsingInv B)
                (fun l : Fin p =>
                  Deltad l - rectMatMulVec DeltaB y l)) i) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => rectMatMulVec DeltaA y i - Deltab i) j :=
  LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_gram_projection_nullIntersection_reduced_difference_eq
    A DeltaA b Deltab hB DeltaB APplus d Deltad y x hx hy hMP
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
    hAPdiff
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source stacked-full-column-rank projected action for the Gram-`B`
    rank-tolerant Moore--Penrose route. -/
theorem
    LSEFullRowRank.theorem20_8_projected_action_of_MP_gram_projection_lseStackedFullColumnRank
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus)
    (hstack : LSEStackedFullColumnRank A B)
    (v : Fin n → ℝ) :
    rectMatMulVec APplus
        (rectMatMulVec
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) v) =
      rectMatMulVec (theorem20_8Projection B (undetAplusOfGramNonsingInv B)) v := by
  have hright :
      rectMatMul B (undetAplusOfGramNonsingInv B) = idMatrix p :=
    higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
      B hB.rectGram_det_ne_zero
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_gram_projection_lseStackedFullColumnRank
      A hB APplus hMP hstack
  exact
    _root_.NumStability.theorem20_8_projected_action_of_AP_left_inverse_on_nullspace
      A B (undetAplusOfGramNonsingInv B) APplus hright hAPleft_null v
/-- Higham, 2nd ed., Chapter 20, equation (20.24):
    source stacked-full-column-rank matrix identity `(AP)^+ AP = P` for the
    Gram-`B` rank-tolerant Moore--Penrose route. -/
theorem
    LSEFullRowRank.theorem20_8_APplus_AP_eq_projection_of_MP_gram_projection_lseStackedFullColumnRank
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus)
    (hstack : LSEStackedFullColumnRank A B) :
    rectMatMul APplus
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) =
      theorem20_8Projection B (undetAplusOfGramNonsingInv B) := by
  have hright :
      rectMatMul B (undetAplusOfGramNonsingInv B) = idMatrix p :=
    higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
      B hB.rectGram_det_ne_zero
  have hAPleft_null :
      ∀ z : Fin n → ℝ,
        rectMatMulVec B z = (fun _i : Fin p => 0) →
          rectMatMulVec APplus
            (rectMatMulVec
              (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) z) = z :=
    LSEFullRowRank.theorem20_8_AP_left_inverse_on_nullspace_of_MP_gram_projection_lseStackedFullColumnRank
      A hB APplus hMP hstack
  exact
    _root_.NumStability.theorem20_8_APplus_AP_eq_projection_of_AP_left_inverse_on_nullspace
      A B (undetAplusOfGramNonsingInv B) APplus hright hAPleft_null
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    residual-explicit exact solution-difference identity for the Gram-`B`
    rank-tolerant Moore--Penrose route.

    Source full row rank of `B`, stacked full column rank of `[A; B]`, and a
    Moore--Penrose certificate for `(AP)^+` derive the projector identity
    `(AP)^+ AP = P`; feasibility and the perturbed Higham residual equation
    derive the reduced `AP*(y-x)` equation internally.  Thus this surface no
    longer exposes either reduced equation as a caller hypothesis. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_gram_projection_lseStackedFullColumnRank_perturbed_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ) (rHigh : Fin m → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus)
    (hstack : LSEStackedFullColumnRank A B)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m =>
              (b i - rectMatMulVec A x i) - rHigh i -
                rectMatMulVec DeltaA y i + Deltab i) j := by
  have hAPleft :
      rectMatMul APplus
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) =
        theorem20_8Projection B (undetAplusOfGramNonsingInv B) :=
    LSEFullRowRank.theorem20_8_APplus_AP_eq_projection_of_MP_gram_projection_lseStackedFullColumnRank
      A hB APplus hMP hstack
  exact
    _root_.NumStability.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_perturbed_higham_residual_eq
      A DeltaA b Deltab B DeltaB (undetAplusOfGramNonsingInv B) APplus
      d Deltad x y rHigh hAPleft hx hy hres
/-- Higham, 2nd ed., Chapter 20, equation (20.24):
    determinant-facing concrete Gram-pseudoinverse matrix identity
    `(AP)^+ AP = P`. -/
theorem
    LSEFullRowRank.theorem20_8_APplus_AP_eq_projection_of_gram_MP_gram_projection_lseStackedFullColumnRank
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (hdetAP :
      Matrix.det
        (rectGram (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hstack : LSEStackedFullColumnRank A B) :
    rectMatMul
        (undetAplusOfGramNonsingInv
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)))
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) =
      theorem20_8Projection B (undetAplusOfGramNonsingInv B) :=
  LSEFullRowRank.theorem20_8_APplus_AP_eq_projection_of_MP_gram_projection_lseStackedFullColumnRank
    A hB
    (undetAplusOfGramNonsingInv
      (theorem20_8AP A B (undetAplusOfGramNonsingInv B)))
    (higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero
      (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) hdetAP)
    hstack
/-- Higham, 2nd ed., Chapter 20, Theorem 20.8 and equation (20.24):
    source stacked-full-column-rank exact same-residual correction-vector
    identity for the Gram-`B` rank-tolerant Moore--Penrose route. -/
theorem
    LSEFullRowRank.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_MP_gram_projection_lseStackedFullColumnRank_same_higham_residual_eq
    {m n p : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    {B : Fin p → Fin n → ℝ} (hB : LSEFullRowRank B)
    (DeltaB : Fin p → Fin n → ℝ) (APplus : Fin n → Fin m → ℝ)
    (d Deltad : Fin p → ℝ) (x y : Fin n → ℝ)
    (r rHigh : Fin m → ℝ)
    (hx : LSEFeasible B d x)
    (hy : LSEFeasible (fun i j => B i j + DeltaB i j)
      (fun i => d i + Deltad i) y)
    (hMP :
      RectMoorePenrosePseudoinverse m n
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus)
    (hstack : LSEStackedFullColumnRank A B)
    (hr : lsResidualHigham A b x = r)
    (hres :
      lsResidualHigham (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) y = rHigh)
    (hsame : r = rHigh) :
    (fun j : Fin n => y j - x j) =
      fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B (undetAplusOfGramNonsingInv B) APplus)
            (fun i : Fin p => Deltad i - rectMatMulVec DeltaB y i) j +
          rectMatMulVec APplus
            (fun i : Fin m => Deltab i - rectMatMulVec DeltaA y i) j := by
  have hAPaction :
      rectMatMulVec APplus
          (rectMatMulVec
            (theorem20_8AP A B (undetAplusOfGramNonsingInv B))
            (fun k : Fin n => y k - x k)) =
        rectMatMulVec
          (theorem20_8Projection B (undetAplusOfGramNonsingInv B))
          (fun k : Fin n => y k - x k) :=
    LSEFullRowRank.theorem20_8_projected_action_of_MP_gram_projection_lseStackedFullColumnRank
      A hB APplus hMP hstack (fun k => y k - x k)
  exact
    _root_.NumStability.theorem20_8_solution_difference_eq_BAplus_add_APplus_of_same_higham_residual_projected_action
      A DeltaA b Deltab B DeltaB (undetAplusOfGramNonsingInv B) APplus
      d Deltad x y r rHigh hAPaction hx hy hr hres hsame
/-- A square finite matrix is lower triangular when all entries above the
    diagonal vanish.  This is the exact triangularity predicate used by
    Higham's generalized QR factorization in (20.27). -/
def IsLowerTriangular {n : ℕ} (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i.val < j.val → L i j = 0
/-- A relative entrywise perturbation of a lower-triangular matrix is still
    lower triangular.  Above the diagonal the reference entries are zero, so
    the absolute perturbation bound forces the perturbation entries to vanish
    there as well. -/
theorem IsLowerTriangular.add_of_entrywise_abs_le_mul_abs {n : ℕ}
    {T Delta : Fin n → Fin n → ℝ} {eta : ℝ}
    (hT : IsLowerTriangular T)
    (hDelta : ∀ i j : Fin n, |Delta i j| ≤ eta * |T i j|) :
    IsLowerTriangular (fun i j => T i j + Delta i j) := by
  intro i j hij
  have hTij : T i j = 0 := hT i j hij
  have hbound : |Delta i j| ≤ 0 := by
    simpa [hTij] using hDelta i j
  have hDeltaij : Delta i j = 0 := by
    exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg (Delta i j)))
  simp [hTij, hDeltaij]
/-- A relative entrywise perturbation with factor strictly below one preserves
    nonzero diagonal entries. -/
theorem diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one {n : ℕ}
    {T Delta : Fin n → Fin n → ℝ} {eta : ℝ}
    (hdiag : ∀ i : Fin n, T i i ≠ 0)
    (heta_lt : eta < 1)
    (hDelta : ∀ i j : Fin n, |Delta i j| ≤ eta * |T i j|) :
    ∀ i : Fin n, T i i + Delta i i ≠ 0 := by
  intro i hzero
  have hDelta_eq : Delta i i = -T i i := by
    linarith
  have habs_eq : |Delta i i| = |T i i| := by
    rw [hDelta_eq, abs_neg]
  have hle : |T i i| ≤ eta * |T i i| := by
    simpa [habs_eq] using hDelta i i
  have hpos : 0 < |T i i| := abs_pos.mpr (hdiag i)
  nlinarith
private theorem isInverse_rectMatMulVec_bijective {n : ℕ}
    (T Tinv : Fin n → Fin n → ℝ) (hInv : IsInverse n T Tinv) :
    Function.Bijective (rectMatMulVec T) := by
  constructor
  · intro x y hxy
    ext i
    calc
      x i = matMulVec n (idMatrix n) x i := by rw [matMulVec_id]
      _ = matMulVec n (matMul n Tinv T) x i := by
            have hmat : matMul n Tinv T = idMatrix n := by
              ext a b
              exact hInv.1 a b
            rw [hmat]
      _ = matMulVec n Tinv (matMulVec n T x) i := by
            exact matMulVec_matMul n Tinv T x i
      _ = matMulVec n Tinv (matMulVec n T y) i := by
            have hxy' : matMulVec n T x = matMulVec n T y := by
              simpa [rectMatMulVec, matMulVec] using hxy
            rw [hxy']
      _ = matMulVec n (matMul n Tinv T) y i := by
            exact (matMulVec_matMul n Tinv T y i).symm
      _ = matMulVec n (idMatrix n) y i := by
            have hmat : matMul n Tinv T = idMatrix n := by
              ext a b
              exact hInv.1 a b
            rw [hmat]
      _ = y i := by rw [matMulVec_id]
  · intro b
    refine ⟨matMulVec n Tinv b, ?_⟩
    ext i
    calc
      rectMatMulVec T (matMulVec n Tinv b) i
          = matMulVec n T (matMulVec n Tinv b) i := by
            rfl
      _ = matMulVec n (matMul n T Tinv) b i := by
            exact (matMulVec_matMul n T Tinv b i).symm
      _ = matMulVec n (idMatrix n) b i := by
            have hmat : matMul n T Tinv = idMatrix n := by
              ext a b
              exact hInv.2 a b
            rw [hmat]
      _ = b i := by rw [matMulVec_id]
/-- A finite lower-triangular real matrix with nonzero diagonal is a
    nonsingular square solve map.

    This is the determinant-to-solve-map bridge used for Higham's statement
    after Theorem 20.9 that the lower-triangular GQR blocks `S` and `L22` are
    nonsingular. -/
theorem rectMatMulVec_bijective_of_lowerTriangular_diag_ne_zero {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hlower : IsLowerTriangular T)
    (hdiag : ∀ i : Fin n, T i i ≠ 0) :
    Function.Bijective (rectMatMulVec T) := by
  have hdet : Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
    det_ne_zero_of_lower_triangular_diag_ne_zero n T hlower hdiag
  rcases exists_isInverse_of_det_ne_zero n T hdet with ⟨Tinv, hInv⟩
  exact isInverse_rectMatMulVec_bijective T Tinv hInv
/-- A square matrix whose rectangular matrix-vector action is injective has
    nonzero determinant. -/
theorem rectMatMulVec_det_ne_zero_of_injective {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hinj : Function.Injective (rectMatMulVec T)) :
    Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  let M : Matrix (Fin n) (Fin n) ℝ := T
  have hM_inj : Function.Injective M.mulVec := by
    intro x y hxy
    apply hinj
    ext i
    have hi := congrFun hxy i
    simpa [M, rectMatMulVec, Matrix.mulVec] using hi
  have hunitM : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hM_inj
  have hdetUnit : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunitM
  have hdetNe : M.det ≠ 0 := isUnit_iff_ne_zero.mp hdetUnit
  simpa [M] using hdetNe
/-- A finite lower-triangular real matrix with nonzero determinant has nonzero
    diagonal entries.  This is the transpose form of
    `diag_ne_zero_of_upper_triangular_det_ne_zero`. -/
theorem diag_ne_zero_of_lower_triangular_det_ne_zero {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hlower : IsLowerTriangular T)
    (hdet : Matrix.det (T : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∀ i : Fin n, T i i ≠ 0 := by
  let M : Matrix (Fin n) (Fin n) ℝ := T
  have hupper : ∀ i j : Fin n, j.val < i.val → T j i = 0 := by
    intro i j hji
    exact hlower j i hji
  have hdetT :
      Matrix.det ((fun i j : Fin n => T j i) :
        Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    have hdetTranspose : Matrix.det M.transpose ≠ 0 := by
      rw [Matrix.det_transpose]
      simpa [M] using hdet
    have hmat :
        ((fun i j : Fin n => T j i) : Matrix (Fin n) (Fin n) ℝ) =
          M.transpose := by
      ext i j
      simp [M, Matrix.transpose_apply]
    rw [hmat]
    exact hdetTranspose
  have hdiagT := diag_ne_zero_of_upper_triangular_det_ne_zero n
    (fun i j : Fin n => T j i) hupper hdetT
  intro i
  exact hdiagT i
/-- A finite lower-triangular real matrix with injective square solve map has
    nonzero diagonal entries. -/
theorem rectMatMulVec_diag_ne_zero_of_lowerTriangular_injective {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hlower : IsLowerTriangular T)
    (hinj : Function.Injective (rectMatMulVec T)) :
    ∀ i : Fin n, T i i ≠ 0 :=
  diag_ne_zero_of_lower_triangular_det_ne_zero hlower
    (rectMatMulVec_det_ne_zero_of_injective hinj)
/-- A finite lower-triangular real matrix with bijective square solve map has
    nonzero diagonal entries. -/
theorem rectMatMulVec_diag_ne_zero_of_lowerTriangular_bijective {n : ℕ}
    {T : Fin n → Fin n → ℝ}
    (hlower : IsLowerTriangular T)
    (hbij : Function.Bijective (rectMatMulVec T)) :
    ∀ i : Fin n, T i i ≠ 0 :=
  rectMatMulVec_diag_ne_zero_of_lowerTriangular_injective hlower hbij.1
/-- The transpose of a square upper-triangular QR block is lower triangular.

    This is the first triangularity bridge in Higham's Chapter 20 construction
    of the generalized QR factorization in Theorem 20.9: a QR factorization of
    `Bᵀ` supplies an upper-triangular `R`, whose transpose becomes the lower
    triangular `S` in `B Q = [S 0]`. -/
theorem isLowerTriangular_matTranspose_of_isUpperTriangular {n : ℕ}
    {R : Fin n → Fin n → ℝ}
    (hR : IsUpperTriangular n R) :
    IsLowerTriangular (matTranspose R) := by
  intro i j hij
  unfold matTranspose
  exact hR j i hij
/-- Permutation matrix for a finite index equivalence.  This is the orthogonal
    left-factor used to make the row permutations in the Chapter 20 GQR block
    constructions explicit. -/
def finPermMatrix {n : ℕ} (σ : Fin n ≃ Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if σ i = j then 1 else 0
/-- Left multiplication by a permutation matrix permutes the rows of a
    rectangular matrix. -/
theorem matMulRectLeft_finPermMatrix {m n : ℕ}
    (σ : Fin m ≃ Fin m) (A : Fin m → Fin n → ℝ) :
    matMulRectLeft (finPermMatrix σ) A = rectPermuteRows σ A := by
  ext i j
  unfold matMulRectLeft finPermMatrix rectPermuteRows
  simp
/-- A finite permutation matrix is orthogonal. -/
theorem finPermMatrix_orthogonal {n : ℕ} (σ : Fin n ≃ Fin n) :
    IsOrthogonal n (finPermMatrix σ) := by
  constructor
  · intro i j
    unfold finPermMatrix matTranspose
    calc
      (∑ x : Fin n,
          (if σ x = i then (1 : ℝ) else 0) *
            if σ x = j then (1 : ℝ) else 0)
          = ∑ x : Fin n,
              if σ x = i then if σ x = j then (1 : ℝ) else 0 else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hxi : σ x = i <;> simp [hxi]
      _ = if i = j then 1 else 0 := by
          calc
            (∑ x : Fin n,
                if σ x = i then if σ x = j then (1 : ℝ) else 0 else 0)
                = ∑ y : Fin n,
                    if y = i then if y = j then (1 : ℝ) else 0 else 0 := by
                    exact Equiv.sum_comp σ
                      (fun y : Fin n =>
                        if y = i then if y = j then (1 : ℝ) else 0 else 0)
            _ = if i = j then 1 else 0 := by
                by_cases hij : i = j <;> simp [hij]
  · intro i j
    unfold finPermMatrix matTranspose
    calc
      (∑ x : Fin n,
          (if σ i = x then (1 : ℝ) else 0) *
            if σ j = x then (1 : ℝ) else 0)
          = ∑ x : Fin n,
              if σ i = x then if σ j = x then (1 : ℝ) else 0 else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hxi : σ i = x <;> simp [hxi]
      _ = if i = j then 1 else 0 := by
          calc
            (∑ x : Fin n,
                if σ i = x then if σ j = x then (1 : ℝ) else 0 else 0)
                = (if σ j = σ i then (1 : ℝ) else 0) := by
                    rw [Finset.sum_ite_eq]
                    simp
            _ = if i = j then 1 else 0 := by
                by_cases hij : i = j
                · subst j
                  simp
                · have hsig : σ j ≠ σ i := by
                    intro h
                    exact hij ((Equiv.apply_eq_iff_eq σ).1 h.symm)
                  simp [hij, hsig]
/-- The zero-tail transformed QR block `[R;0]` is just `R`. -/
theorem lsQRTallBlock_zero {n : ℕ} (R : Fin n → Fin n → ℝ) :
    lsQRTallBlock (k := 0) R = R := by
  ext i j
  unfold lsQRTallBlock
  refine Fin.addCases ?_ ?_ i
  · intro i
    change Fin.append R (fun _ : Fin 0 => fun _ : Fin n => 0)
        (Fin.castAdd 0 i) j = R i j
    rw [Fin.append_left]
  · intro i
    exact Fin.elim0 i
private theorem isRightInverse_of_isLeftInverse_square {n : ℕ}
    {T Tinv : Fin n → Fin n → ℝ}
    (hLeft : IsLeftInverse n T Tinv) :
    IsRightInverse n T Tinv := by
  have hmatLeft :
      (Matrix.of Tinv : Matrix (Fin n) (Fin n) ℝ) *
          (Matrix.of T : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.of_apply, idMatrix] using hLeft i j
  have hmatRight :
      (Matrix.of T : Matrix (Fin n) (Fin n) ℝ) *
          (Matrix.of Tinv : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    mul_eq_one_comm.mp hmatLeft
  intro i j
  have hentry := congrArg
    (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hmatRight
  simpa [Matrix.mul_apply, Matrix.of_apply, idMatrix] using hentry
private theorem isOrthogonal_of_column_orthonormal {n : ℕ}
    {Q : Fin n → Fin n → ℝ}
    (hcols : ∀ a b : Fin n,
      (∑ i : Fin n, Q i a * Q i b) = if a = b then 1 else 0) :
    IsOrthogonal n Q := by
  have hleft : IsLeftInverse n Q (matTranspose Q) := by
    intro a b
    simpa [matTranspose] using hcols a b
  exact ⟨hleft, isRightInverse_of_isLeftInverse_square hleft⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    a rectangular exact factorization `Bᵀ = Q₁ R` with orthonormal columns can
    be completed to a square orthogonal `Q` satisfying
    `Qᵀ Bᵀ = [R; 0]`.

    This removes the supplied square-orthogonal factor from the `Bᵀ` QR part of
    the GQR construction.  It is exact finite-dimensional algebra; the
    rectangular factorization itself is still an input to this theorem. -/
theorem exists_orthogonal_completion_tall_qr_block {p q : ℕ}
    (Bt : Fin (p + q) → Fin p → ℝ)
    (Q1 : Fin (p + q) → Fin p → ℝ)
    (R : Fin p → Fin p → ℝ)
    (hQ1 : GramSchmidtOrthonormalColumns Q1)
    (hfactor : Bt = matMulRect (p + q) p p Q1 R) :
    ∃ Q : Fin (p + q) → Fin (p + q) → ℝ,
      IsOrthogonal (p + q) Q ∧
        (∀ i j, Q i (Fin.castAdd q j) = Q1 i j) ∧
        matMulRectLeft (matTranspose Q) Bt = lsQRTallBlock (k := q) R := by
  classical
  let s : Set (Fin (p + q)) :=
    {a | ∃ j : Fin p, a = Fin.castAdd q j}
  let X : Fin (p + q) → Fin (p + q) → ℝ :=
    fun i a =>
      if ha : ∃ j : Fin p, a = Fin.castAdd q j then
        Q1 i (Classical.choose ha)
      else
        0
  have hX : ∀ a b : s,
      (∑ i : Fin (p + q), X i a * X i b) =
        if a = b then 1 else 0 := by
    intro a b
    rcases a.2 with ⟨ja, hja⟩
    rcases b.2 with ⟨jb, hjb⟩
    have hXa : ∀ i : Fin (p + q), X i a = Q1 i ja := by
      intro i
      have ha : ∃ j : Fin p, (a : Fin (p + q)) = Fin.castAdd q j :=
        ⟨ja, hja⟩
      have hchoose : Classical.choose ha = ja := by
        apply Fin.castAdd_injective p q
        simp [hja]
      simp [X, ha, hchoose]
    have hXb : ∀ i : Fin (p + q), X i b = Q1 i jb := by
      intro i
      have hb : ∃ j : Fin p, (b : Fin (p + q)) = Fin.castAdd q j :=
        ⟨jb, hjb⟩
      have hchoose : Classical.choose hb = jb := by
        apply Fin.castAdd_injective p q
        simp [hjb]
      simp [X, hb, hchoose]
    have hsubeq : a = b ↔ ja = jb := by
      constructor
      · intro hab
        apply Fin.castAdd_injective p q
        calc
          Fin.castAdd q ja = (a : Fin (p + q)) := hja.symm
          _ = (b : Fin (p + q)) := congrArg Subtype.val hab
          _ = Fin.castAdd q jb := hjb
      · intro h
        apply Subtype.ext
        calc
          (a : Fin (p + q)) = Fin.castAdd q ja := hja
          _ = Fin.castAdd q jb := by rw [h]
          _ = (b : Fin (p + q)) := hjb.symm
    calc
      (∑ i : Fin (p + q), X i a * X i b)
          = ∑ i : Fin (p + q), Q1 i ja * Q1 i jb := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hXa i, hXb i]
      _ = idMatrix p ja jb := hQ1 ja jb
      _ = if a = b then 1 else 0 := by
          by_cases h : ja = jb
          · subst jb
            have hab : a = b := hsubeq.mpr rfl
            simp [idMatrix, hab]
          · have hab : a ≠ b := fun hab => h (hsubeq.mp hab)
            simp [idMatrix, h, hab]
  obtain ⟨Q, hQpreserve, hQcols⟩ :=
    partialColOrthonormal_exists_fullColOrthonormal X s hX
  refine ⟨Q, isOrthogonal_of_column_orthonormal hQcols, ?_, ?_⟩
  · intro i j
    have hmem : Fin.castAdd q j ∈ s := ⟨j, rfl⟩
    have hp := hQpreserve (Fin.castAdd q j) hmem i
    have hcast : ∃ k : Fin p, Fin.castAdd q j = Fin.castAdd q k :=
      ⟨j, rfl⟩
    have hchoose : Classical.choose hcast = j := by
      apply Fin.castAdd_injective p q
      exact (Classical.choose_spec hcast).symm
    simpa [X, hcast, hchoose] using hp
  · subst Bt
    ext row col
    refine Fin.addCases
      (motive := fun row : Fin (p + q) =>
        matMulRectLeft (matTranspose Q)
            (matMulRect (p + q) p p Q1 R) row col =
          lsQRTallBlock (k := q) R row col)
      ?top ?bottom row
    · intro row
      have hpreserve : ∀ i : Fin (p + q), Q i (Fin.castAdd q row) = Q1 i row :=
        fun i => by
          have hmem : Fin.castAdd q row ∈ s := ⟨row, rfl⟩
          have hp := hQpreserve (Fin.castAdd q row) hmem i
          have hcast : ∃ k : Fin p, Fin.castAdd q row = Fin.castAdd q k :=
            ⟨row, rfl⟩
          have hchoose : Classical.choose hcast = row := by
            apply Fin.castAdd_injective p q
            exact (Classical.choose_spec hcast).symm
          simpa [X, hcast, hchoose] using hp
      have hsum_rearrange :
          (∑ i : Fin (p + q),
              Q i (Fin.castAdd q row) *
                (∑ k : Fin p, Q1 i k * R k col)) =
            ∑ k : Fin p,
              (∑ i : Fin (p + q), Q i (Fin.castAdd q row) * Q1 i k) *
                R k col := by
        calc
          (∑ i : Fin (p + q),
              Q i (Fin.castAdd q row) *
                (∑ k : Fin p, Q1 i k * R k col))
              =
            ∑ i : Fin (p + q), ∑ k : Fin p,
              Q i (Fin.castAdd q row) * (Q1 i k * R k col) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
          _ =
            ∑ k : Fin p, ∑ i : Fin (p + q),
              Q i (Fin.castAdd q row) * (Q1 i k * R k col) := by
              rw [Finset.sum_comm]
          _ =
            ∑ k : Fin p,
              (∑ i : Fin (p + q), Q i (Fin.castAdd q row) * Q1 i k) *
                R k col := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              ring
      calc
        matMulRectLeft (matTranspose Q)
            (matMulRect (p + q) p p Q1 R) (Fin.castAdd q row) col
            =
          ∑ k : Fin p,
            (∑ i : Fin (p + q), Q i (Fin.castAdd q row) * Q1 i k) *
              R k col := by
              unfold matMulRectLeft matTranspose matMulRect
              exact hsum_rearrange
        _ =
          ∑ k : Fin p, idMatrix p row k * R k col := by
              apply Finset.sum_congr rfl
              intro k _
              have horth :
                  (∑ i : Fin (p + q), Q1 i row * Q1 i k) =
                    idMatrix p row k := by
                simpa [GramSchmidtOrthonormalColumns, rectangularGram] using
                  hQ1 row k
              rw [show (∑ i : Fin (p + q), Q i (Fin.castAdd q row) * Q1 i k) =
                  ∑ i : Fin (p + q), Q1 i row * Q1 i k from by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [hpreserve i]]
              rw [horth]
        _ = R row col := by
              simp [idMatrix]
        _ = lsQRTallBlock (k := q) R (Fin.castAdd q row) col := by
              simp [lsQRTallBlock]
    · intro row
      have hsum_rearrange :
          (∑ i : Fin (p + q),
              Q i (Fin.natAdd p row) *
                (∑ k : Fin p, Q1 i k * R k col)) =
            ∑ k : Fin p,
              (∑ i : Fin (p + q), Q i (Fin.natAdd p row) * Q1 i k) *
                R k col := by
        calc
          (∑ i : Fin (p + q),
              Q i (Fin.natAdd p row) *
                (∑ k : Fin p, Q1 i k * R k col))
              =
            ∑ i : Fin (p + q), ∑ k : Fin p,
              Q i (Fin.natAdd p row) * (Q1 i k * R k col) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
          _ =
            ∑ k : Fin p, ∑ i : Fin (p + q),
              Q i (Fin.natAdd p row) * (Q1 i k * R k col) := by
              rw [Finset.sum_comm]
          _ =
            ∑ k : Fin p,
              (∑ i : Fin (p + q), Q i (Fin.natAdd p row) * Q1 i k) *
                R k col := by
              apply Finset.sum_congr rfl
              intro k _
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              ring
      have htail_orth : ∀ k : Fin p,
          (∑ i : Fin (p + q), Q i (Fin.natAdd p row) * Q1 i k) = 0 := by
        intro k
        have hne : Fin.natAdd p row ≠ Fin.castAdd q k := by
          intro h
          have hval := congrArg Fin.val h
          have hp_le : p ≤ k.val := by
            calc
              p ≤ p + row.val := Nat.le_add_right p row.val
              _ = k.val := by simpa using hval
          exact (Nat.not_le_of_gt k.isLt) hp_le
        have horth := hQcols (Fin.natAdd p row) (Fin.castAdd q k)
        have hsumQ :
            (∑ i : Fin (p + q), Q i (Fin.natAdd p row) *
              Q i (Fin.castAdd q k)) = 0 := by
          simpa [hne] using horth
        have hpreserve : ∀ i : Fin (p + q), Q i (Fin.castAdd q k) = Q1 i k :=
          fun i => by
            have hmem : Fin.castAdd q k ∈ s := ⟨k, rfl⟩
            have hp := hQpreserve (Fin.castAdd q k) hmem i
            have hcast : ∃ j : Fin p, Fin.castAdd q k = Fin.castAdd q j :=
              ⟨k, rfl⟩
            have hchoose : Classical.choose hcast = k := by
              apply Fin.castAdd_injective p q
              exact (Classical.choose_spec hcast).symm
            simpa [X, hcast, hchoose] using hp
        calc
          (∑ i : Fin (p + q), Q i (Fin.natAdd p row) * Q1 i k)
              =
            ∑ i : Fin (p + q), Q i (Fin.natAdd p row) *
              Q i (Fin.castAdd q k) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hpreserve i]
          _ = 0 := hsumQ
      calc
        matMulRectLeft (matTranspose Q)
            (matMulRect (p + q) p p Q1 R) (Fin.natAdd p row) col
            =
          ∑ k : Fin p,
            (∑ i : Fin (p + q), Q i (Fin.natAdd p row) * Q1 i k) *
              R k col := by
              unfold matMulRectLeft matTranspose matMulRect
              exact hsum_rearrange
        _ = 0 := by
              simp [htail_orth]
        _ = lsQRTallBlock (k := q) R (Fin.natAdd p row) col := by
              simp [lsQRTallBlock]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    exact MGS data for `Bᵀ`, once its computed columns are known
    orthonormal, supplies the completed tall QR block `Qᵀ Bᵀ = [R;0]`.

    This removes the arbitrary supplied rectangular factorization from the
    previous completion theorem.  The remaining exposed QR-side dependency is
    the local orthonormal-columns proof for the MGS `Q` factor. -/
theorem exists_transpose_tall_qr_of_mgs_orthonormal {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ)
    (hdiag : ∀ k : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun j : Fin (p + q) => fun i : Fin p => B i j) k.val k) ≠ 0)
    (horth : GramSchmidtOrthonormalColumns
      (modifiedGramSchmidtQ
        (fun j : Fin (p + q) => fun i : Fin p => B i j))) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (R : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsUpperTriangular p R ∧
        matMulRectLeft (matTranspose Q)
          (fun j : Fin (p + q) => fun i : Fin p => B i j) =
          lsQRTallBlock (k := q) R := by
  let Bt : Fin (p + q) → Fin p → ℝ :=
    fun j => fun i => B i j
  let R : Fin p → Fin p → ℝ := modifiedGramSchmidtR Bt
  have hfactor :
      Bt = matMulRect (p + q) p p (modifiedGramSchmidtQ Bt) R := by
    exact modifiedGramSchmidt_exact_factorization Bt hdiag
  have hRupper : IsUpperTriangular p R :=
    IsUpperTrapezoidal.to_upperTriangular
      (modifiedGramSchmidtR_upper_trapezoidal Bt)
  obtain ⟨Q, hQorth, _hpreserve, hblock⟩ :=
    exists_orthogonal_completion_tall_qr_block Bt
      (modifiedGramSchmidtQ Bt) R horth hfactor
  refine ⟨Q, R, hQorth, hRupper, ?_⟩
  simpa [Bt] using hblock
/-- Higham, 2nd ed., Chapter 20, Theorem 20.9 construction step:
    exact MGS data for `Bᵀ` with nonzero stage normalizers supplies the
    completed tall QR block `Qᵀ Bᵀ = [R;0]`.

    This discharges the previous explicit MGS orthonormality dependency using
    the exact MGS orthonormal-columns theorem. -/
theorem exists_transpose_tall_qr_of_mgs {p q : ℕ}
    (B : Fin p → Fin (p + q) → ℝ)
    (hdiag : ∀ k : Fin p,
      gsColumnNorm2
        (modifiedGramSchmidtVectors
          (fun j : Fin (p + q) => fun i : Fin p => B i j) k.val k) ≠ 0) :
    ∃ (Q : Fin (p + q) → Fin (p + q) → ℝ) (R : Fin p → Fin p → ℝ),
      IsOrthogonal (p + q) Q ∧
        IsUpperTriangular p R ∧
        matMulRectLeft (matTranspose Q)
          (fun j : Fin (p + q) => fun i : Fin p => B i j) =
          lsQRTallBlock (k := q) R := by
  have horth : GramSchmidtOrthonormalColumns
      (modifiedGramSchmidtQ
        (fun j : Fin (p + q) => fun i : Fin p => B i j)) :=
    modifiedGramSchmidtQ_orthonormal_columns
      (fun j : Fin (p + q) => fun i : Fin p => B i j) hdiag
  exact exists_transpose_tall_qr_of_mgs_orthonormal B hdiag horth
/-- Finite-index associativity equivalence used to pass between Lean's
    `k + (p + q)` row shape and Higham's associated `((k + p) + q)` display. -/
def finAddAssocEquiv (k p q : ℕ) :
    Fin ((k + p) + q) ≃ Fin (k + (p + q)) where
  toFun := Fin.cast (Nat.add_assoc k p q)
  invFun := Fin.cast (Nat.add_assoc k p q).symm
  left_inv := by
    intro i
    ext
    simp [Fin.cast]
  right_inv := by
    intro i
    ext
    simp [Fin.cast]
/-- Finite-index commutativity equivalence for row reindexing between
    `r + q` and `q + r` shapes.  It preserves the numeric index value. -/
def finAddCommEquiv (r q : ℕ) : Fin (r + q) ≃ Fin (q + r) where
  toFun := Fin.cast (Nat.add_comm r q)
  invFun := Fin.cast (Nat.add_comm q r)
  left_inv := by
    intro i
    ext
    simp [Fin.cast]
  right_inv := by
    intro i
    ext
    simp [Fin.cast]
/-- Orthonormal columns are preserved by a finite row-index equivalence. -/
theorem GramSchmidtOrthonormalColumns.reindexRowsEquiv {m m' n : ℕ}
    (e : Fin m ≃ Fin m') {Q : Fin m → Fin n → ℝ}
    (hQ : GramSchmidtOrthonormalColumns Q) :
    GramSchmidtOrthonormalColumns
      (fun i : Fin m' => fun j : Fin n => Q (e.symm i) j) := by
  intro a b
  unfold rectangularGram
  calc
    (∑ i : Fin m', Q (e.symm i) a * Q (e.symm i) b)
        = ∑ i : Fin m, Q i a * Q i b := by
            exact Equiv.sum_comp e.symm
              (fun i : Fin m => Q i a * Q i b)
    _ = idMatrix n a b := hQ a b
/-- Orthogonality is preserved by conjugating rows and columns through a finite
    index equivalence. -/
theorem IsOrthogonal.reindexRowsColsEquiv {m m' : ℕ}
    (e : Fin m ≃ Fin m') {U : Fin m' → Fin m' → ℝ}
    (hU : IsOrthogonal m' U) :
    IsOrthogonal m (fun i j : Fin m => U (e i) (e j)) := by
  constructor
  · intro i j
    unfold matTranspose
    calc
      (∑ k : Fin m, U (e k) (e i) * U (e k) (e j))
          = ∑ k' : Fin m', U k' (e i) * U k' (e j) := by
              exact Equiv.sum_comp e
                (fun k' : Fin m' => U k' (e i) * U k' (e j))
      _ = if e i = e j then 1 else 0 := hU.col_orthonormal (e i) (e j)
      _ = if i = j then 1 else 0 := by
          by_cases hij : i = j
          · subst j
            simp
          · have he : e i ≠ e j := fun heq =>
              hij ((Equiv.apply_eq_iff_eq e).1 heq)
            simp [hij, he]
  · intro i j
    unfold matTranspose
    calc
      (∑ k : Fin m, U (e i) (e k) * U (e j) (e k))
          = ∑ k' : Fin m', U (e i) k' * U (e j) k' := by
              exact Equiv.sum_comp e
                (fun k' : Fin m' => U (e i) k' * U (e j) k')
      _ = if e i = e j then 1 else 0 := by
          have hrow := hU.right_inv (e i) (e j)
          simpa [matTranspose] using hrow
      _ = if i = j then 1 else 0 := by
          by_cases hij : i = j
          · subst j
            simp
          · have he : e i ≠ e j := fun heq =>
              hij ((Equiv.apply_eq_iff_eq e).1 heq)
            simp [hij, he]
/-- Completion helper for the tall associated (20.28) route: an orthonormal
    rectangular factor can be extended to a square orthogonal matrix whose
    bottom columns are the original columns in reverse order.

    The reversed placement is the row-side companion to applying QR/MGS to the
    column-reversed `A Q₂` block: after the later matrix-action step, the upper
    triangular QR factor becomes the lower-triangular `L₂₂` block. -/
theorem exists_orthogonal_completion_bottom_reversed_columns {r q : ℕ}
    (Q2 : Fin (r + q) → Fin q → ℝ)
    (hQ2 : GramSchmidtOrthonormalColumns Q2) :
    ∃ U : Fin (r + q) → Fin (r + q) → ℝ,
      IsOrthogonal (r + q) U ∧
        ∀ i j, U i (Fin.natAdd r j) = Q2 i (Fin.rev j) := by
  classical
  let s : Set (Fin (r + q)) :=
    {a | ∃ j : Fin q, a = Fin.natAdd r j}
  let X : Fin (r + q) → Fin (r + q) → ℝ :=
    fun i a =>
      if ha : ∃ j : Fin q, a = Fin.natAdd r j then
        Q2 i (Fin.rev (Classical.choose ha))
      else
        0
  have hX : ∀ a b : s,
      (∑ i : Fin (r + q), X i a * X i b) =
        if a = b then 1 else 0 := by
    intro a b
    rcases a.2 with ⟨ja, hja⟩
    rcases b.2 with ⟨jb, hjb⟩
    have hXa : ∀ i : Fin (r + q), X i a = Q2 i (Fin.rev ja) := by
      intro i
      have ha : ∃ j : Fin q, (a : Fin (r + q)) = Fin.natAdd r j :=
        ⟨ja, hja⟩
      have hchoose : Classical.choose ha = ja := by
        apply (Fin.natAdd_inj r).mp
        calc
          Fin.natAdd r (Classical.choose ha) = (a : Fin (r + q)) :=
            (Classical.choose_spec ha).symm
          _ = Fin.natAdd r ja := hja
      simp [X, ha, hchoose]
    have hXb : ∀ i : Fin (r + q), X i b = Q2 i (Fin.rev jb) := by
      intro i
      have hb : ∃ j : Fin q, (b : Fin (r + q)) = Fin.natAdd r j :=
        ⟨jb, hjb⟩
      have hchoose : Classical.choose hb = jb := by
        apply (Fin.natAdd_inj r).mp
        calc
          Fin.natAdd r (Classical.choose hb) = (b : Fin (r + q)) :=
            (Classical.choose_spec hb).symm
          _ = Fin.natAdd r jb := hjb
      simp [X, hb, hchoose]
    have hsubeq : a = b ↔ ja = jb := by
      constructor
      · intro hab
        apply (Fin.natAdd_inj r).mp
        calc
          Fin.natAdd r ja = (a : Fin (r + q)) := hja.symm
          _ = (b : Fin (r + q)) := congrArg Subtype.val hab
          _ = Fin.natAdd r jb := hjb
      · intro h
        apply Subtype.ext
        calc
          (a : Fin (r + q)) = Fin.natAdd r ja := hja
          _ = Fin.natAdd r jb := by rw [h]
          _ = (b : Fin (r + q)) := hjb.symm
    calc
      (∑ i : Fin (r + q), X i a * X i b)
          =
        ∑ i : Fin (r + q), Q2 i (Fin.rev ja) * Q2 i (Fin.rev jb) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hXa i, hXb i]
      _ = idMatrix q (Fin.rev ja) (Fin.rev jb) :=
            hQ2 (Fin.rev ja) (Fin.rev jb)
      _ = if a = b then 1 else 0 := by
          by_cases h : ja = jb
          · subst jb
            have hab : a = b := hsubeq.mpr rfl
            simp [idMatrix, hab]
          · have hab : a ≠ b := fun hab => h (hsubeq.mp hab)
            have hrev : Fin.rev ja ≠ Fin.rev jb :=
              fun hrev => h (Fin.rev_injective hrev)
            simp [idMatrix, hrev, hab]
  obtain ⟨U, hUpreserve, hUcols⟩ :=
    partialColOrthonormal_exists_fullColOrthonormal X s hX
  refine ⟨U, isOrthogonal_of_column_orthonormal hUcols, ?_⟩
  intro i j
  have hmem : Fin.natAdd r j ∈ s := ⟨j, rfl⟩
  have hp := hUpreserve (Fin.natAdd r j) hmem i
  have hcast : ∃ k : Fin q, Fin.natAdd r j = Fin.natAdd r k :=
    ⟨j, rfl⟩
  have hchoose : Classical.choose hcast = j := by
    apply (Fin.natAdd_inj r).mp
    exact (Classical.choose_spec hcast).symm
  simpa [X, hcast, hchoose] using hp
/-- Constraint residual `Bx - d`, the lower residual block in the weighted
    problem (20.26). -/
noncomputable def lseConstraintResidual {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ) (x : Fin n → ℝ) :
    Fin p → ℝ :=
  fun i => rectMatMulVec B x i - d i
/-- A vector padded by zero leading coordinates has the same Euclidean norm as
    its trailing block. -/
theorem vecNorm2_zeroLeft_append {p q : ℕ}
    (y : Fin q → ℝ) :
    vecNorm2 (Fin.append (0 : Fin p → ℝ) y) = vecNorm2 y := by
  unfold vecNorm2 vecNorm2Sq
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- Frobenius norm of a rectangular matrix with zero columns prepended. -/
theorem frobNormRect_zeroLeftCols_append {m p q : ℕ}
    (C : Fin m → Fin q → ℝ) :
    frobNormRect (fun i : Fin m =>
      Fin.append (fun _ : Fin p => 0) (C i)) = frobNormRect C := by
  unfold frobNormRect
  apply congrArg Real.sqrt
  unfold frobNormSqRect
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- Frobenius norm of a rectangular matrix with zero columns appended. -/
theorem frobNormRect_zeroRightCols_append {m p q : ℕ}
    (C : Fin m → Fin p → ℝ) :
    frobNormRect (fun i : Fin m =>
      Fin.append (C i) (fun _ : Fin q => 0)) = frobNormRect C := by
  unfold frobNormRect
  apply congrArg Real.sqrt
  unfold frobNormSqRect
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- Frobenius norm of a rectangular matrix with zero rows prepended. -/
theorem frobNormRect_zeroTopRows_append {r q n : ℕ}
    (C : Fin q → Fin n → ℝ) :
    frobNormRect (Fin.append (fun _ : Fin r => fun _ : Fin n => 0) C) =
      frobNormRect C := by
  unfold frobNormRect
  apply congrArg Real.sqrt
  unfold frobNormSqRect
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- The bottom row block has Frobenius squared norm no larger than the full
    rectangular matrix. -/
theorem frobNormSqRect_bottomRows_le {r q n : ℕ}
    (M : Fin (r + q) → Fin n → ℝ) :
    frobNormSqRect (fun i : Fin q => M (Fin.natAdd r i)) ≤
      frobNormSqRect M := by
  unfold frobNormSqRect
  rw [Fin.sum_univ_add]
  have htop_nonneg :
      0 ≤ ∑ i : Fin r, ∑ j : Fin n, M (Fin.castAdd q i) j ^ 2 := by
    exact Finset.sum_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  linarith
/-- The bottom row block has Frobenius norm no larger than the full
    rectangular matrix. -/
theorem frobNormRect_bottomRows_le {r q n : ℕ}
    (M : Fin (r + q) → Fin n → ℝ) :
    frobNormRect (fun i : Fin q => M (Fin.natAdd r i)) ≤
      frobNormRect M := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt (frobNormSqRect_bottomRows_le M)
/-- The trailing column block has Frobenius norm no larger than the full
    rectangular matrix. -/
theorem frobNormSqRect_trailingCols_le {m p q : ℕ}
    (M : Fin m → Fin (p + q) → ℝ) :
    frobNormSqRect (fun i : Fin m => fun j : Fin q =>
      M i (Fin.natAdd p j)) ≤ frobNormSqRect M := by
  unfold frobNormSqRect
  apply Finset.sum_le_sum
  intro i _
  have hsplit :
      (∑ j : Fin (p + q), M i j ^ 2) =
        (∑ j : Fin p, M i (Fin.castAdd q j) ^ 2) +
          (∑ j : Fin q, M i (Fin.natAdd p j) ^ 2) := by
    rw [Fin.sum_univ_add]
  have hleft_nonneg :
      0 ≤ ∑ j : Fin p, M i (Fin.castAdd q j) ^ 2 := by
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  linarith
/-- The trailing column block has Frobenius norm no larger than the full
    rectangular matrix. -/
theorem frobNormRect_trailingCols_le {m p q : ℕ}
    (M : Fin m → Fin (p + q) → ℝ) :
    frobNormRect (fun i : Fin m => fun j : Fin q =>
      M i (Fin.natAdd p j)) ≤ frobNormRect M := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt (frobNormSqRect_trailingCols_le M)
/-- Column permutations preserve injectivity of a rectangular matrix-vector
    map.  This is the coordinate-change step needed before applying exact QR
    to the column-reversed `A Q₂` block in the Chapter 20 GQR construction. -/
theorem rectMatMulVec_injective_rectPermuteCols {m n : ℕ}
    (π : Fin n ≃ Fin n) {A : Fin m → Fin n → ℝ}
    (hA : Function.Injective (rectMatMulVec A)) :
    Function.Injective (rectMatMulVec (rectPermuteCols π A)) := by
  intro x y hxy
  have hxy' :
      rectMatMulVec A (vecPermute π.symm x) =
        rectMatMulVec A (vecPermute π.symm y) := by
    calc
      rectMatMulVec A (vecPermute π.symm x)
          = rectMatMulVec (rectPermuteCols π A) x := by
              exact (rectMatMulVec_permuteCols π A x).symm
      _ = rectMatMulVec (rectPermuteCols π A) y := hxy
      _ = rectMatMulVec A (vecPermute π.symm y) := by
              exact rectMatMulVec_permuteCols π A y
  have hperm : vecPermute π.symm x = vecPermute π.symm y := hA hxy'
  have hrecover := congrArg (vecPermute π) hperm
  simpa [vecPermute_vecPermute_symm] using hrecover
/-- A real rectangular table with a left inverse has positive complexified
    operator norm on a nonempty domain. -/
theorem complexMatrixOp2_realRectToCMatrix_pos_of_rect_left_inverse
    {m n : ℕ} [Nonempty (Fin n)]
    (A : Fin m → Fin n → ℝ) (Aleft : Fin n → Fin m → ℝ)
    (hleft : rectMatMul Aleft A = idMatrix n) :
    0 < complexMatrixOp2 (realRectToCMatrix Aleft) := by
  classical
  let j0 : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
  let e : Fin n → ℝ := finiteBasisVec j0
  let op : ℝ := complexMatrixOp2 (realRectToCMatrix Aleft)
  have hOp : rectOpNorm2Le Aleft op :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le Aleft le_rfl
  have he : vecNorm2 e = 1 := by
    simpa [e] using vecNorm2_finiteBasisVec j0
  have hleft_vec : rectMatMulVec Aleft (rectMatMulVec A e) = e := by
    calc
      rectMatMulVec Aleft (rectMatMulVec A e)
          = rectMatMulVec (rectMatMul Aleft A) e := by
              exact (rectMatMulVec_rectMatMul Aleft A e).symm
      _ = rectMatMulVec (idMatrix n) e := by rw [hleft]
      _ = e := rectMatMulVec_idMatrix e
  have hbound := hOp (rectMatMulVec A e)
  have hle : (1 : ℝ) ≤ op * vecNorm2 (rectMatMulVec A e) := by
    simpa [op, hleft_vec, he] using hbound
  have hop_ne : op ≠ 0 := by
    intro hop
    have hbad : (1 : ℝ) ≤ 0 := by
      simpa [hop] using hle
    linarith
  have hop_nonneg : 0 ≤ op := by
    dsimp [op]
    exact complexMatrixOp2_nonneg (realRectToCMatrix Aleft)
  exact lt_of_le_of_ne hop_nonneg (Ne.symm hop_ne)
/-- A real rectangular table with a left inverse has positive complexified
    operator norm on a nonempty domain. -/
theorem complexMatrixOp2_realRectToCMatrix_pos_of_rect_has_left_inverse
    {m n : ℕ} [Nonempty (Fin n)]
    (A : Fin m → Fin n → ℝ) (Aleft : Fin n → Fin m → ℝ)
    (hleft : rectMatMul Aleft A = idMatrix n) :
    0 < complexMatrixOp2 (realRectToCMatrix A) := by
  classical
  let j0 : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
  let e : Fin n → ℝ := finiteBasisVec j0
  let op : ℝ := complexMatrixOp2 (realRectToCMatrix A)
  have hOp : rectOpNorm2Le A op :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le A le_rfl
  have he : vecNorm2 e = 1 := by
    simpa [e] using vecNorm2_finiteBasisVec j0
  have hleft_vec : rectMatMulVec Aleft (rectMatMulVec A e) = e := by
    calc
      rectMatMulVec Aleft (rectMatMulVec A e)
          = rectMatMulVec (rectMatMul Aleft A) e := by
              exact (rectMatMulVec_rectMatMul Aleft A e).symm
      _ = rectMatMulVec (idMatrix n) e := by rw [hleft]
      _ = e := rectMatMulVec_idMatrix e
  have hAe_ne_zero : rectMatMulVec A e ≠ 0 := by
    intro hAe
    have he_zero : e = 0 := by
      ext i
      have hi := congrFun hleft_vec i
      rw [hAe] at hi
      simpa [rectMatMulVec] using hi.symm
    have hbad : (1 : ℝ) = 0 := by
      simpa [he_zero, vecNorm2, vecNorm2Sq] using he.symm
    norm_num at hbad
  have hbound := hOp e
  have hop_ne : op ≠ 0 := by
    intro hop
    have hAe_norm_zero : vecNorm2 (rectMatMulVec A e) = 0 := by
      apply le_antisymm
      · simpa [op, hop, he] using hbound
      · exact vecNorm2_nonneg _
    have hAe_zero : rectMatMulVec A e = 0 := by
      funext i
      exact (vecNorm2_eq_zero_iff (rectMatMulVec A e)).mp hAe_norm_zero i
    exact hAe_ne_zero hAe_zero
  have hop_nonneg : 0 ≤ op := by
    dsimp [op]
    exact complexMatrixOp2_nonneg (realRectToCMatrix A)
  exact lt_of_le_of_ne hop_nonneg (Ne.symm hop_ne)
/-- Higham, 2nd ed., Chapter 20, equations (20.29)-(20.30): the horizontally
    partitioned matrix `[A1 A2]` that appears after the column-pivoted QR
    partition. -/
noncomputable def lseEliminationBlockMatrix {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ) :
    Fin m → Fin (p + q) → ℝ :=
  fun i => Fin.append (A1 i) (A2 i)
/-- Matrix-vector multiplication by the partitioned matrix `[A1 A2]` in
    (20.30) splits into the two block actions. -/
theorem lseEliminationBlockMatrix_mulVec {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (x1 : Fin p → ℝ) (x2 : Fin q → ℝ) :
    rectMatMulVec (lseEliminationBlockMatrix A1 A2) (Fin.append x1 x2) =
      fun i : Fin m => rectMatMulVec A1 x1 i + rectMatMulVec A2 x2 i := by
  ext i
  unfold rectMatMulVec lseEliminationBlockMatrix
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]
/-- Higham, 2nd ed., Chapter 20, equation (20.29): with supplied inverse
    action for `R1`, the eliminated leading variables are
    `x1 = R1^{-1}(qtd - R2 x2)`, where `qtd` stands for `Q^T d`. -/
noncomputable def lseEliminationBackSubstitution {p q : ℕ}
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (x2 : Fin q → ℝ) : Fin p → ℝ :=
  rectMatMulVec R1inv (fun i => qtd i - rectMatMulVec R2 x2 i)
/-- The back-substitution vector from (20.29) satisfies the transformed
    constraint `R1 x1 + R2 x2 = qtd` whenever the supplied `R1inv` is a left
    inverse for the displayed triangular factor `R1`. -/
theorem lseEliminationBlockConstraint_eq_qtd_of_left_inverse {p q : ℕ}
    (R1 R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (x2 : Fin q → ℝ)
    (hleft : ∀ v : Fin p → ℝ, rectMatMulVec R1 (rectMatMulVec R1inv v) = v) :
    rectMatMulVec (lseEliminationBlockMatrix R1 R2)
        (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) =
      qtd := by
  ext i
  rw [congrFun
    (lseEliminationBlockMatrix_mulVec R1 R2
      (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) i]
  unfold lseEliminationBackSubstitution
  have hi := congrFun
    (hleft (fun k : Fin p => qtd k - rectMatMulVec R2 x2 k)) i
  rw [hi]
  ring
/-- Higham, 2nd ed., Chapter 20, equation (20.30): action of the Schur
    complement coefficient
    `(A2 - A1 R1^{-1} R2) x2`. -/
noncomputable def lseEliminationReducedAction {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (x2 : Fin q → ℝ) : Fin m → ℝ :=
  fun i =>
    rectMatMulVec A2 x2 i -
      rectMatMulVec A1 (rectMatMulVec R1inv (rectMatMulVec R2 x2)) i
/-- Higham, 2nd ed., Chapter 20, equation (20.30): right-hand side
    `b - A1 R1^{-1} qtd`, with `qtd = Q^T d`. -/
noncomputable def lseEliminationReducedRhs {m p : ℕ}
    (A1 : Fin m → Fin p → ℝ) (R1inv : Fin p → Fin p → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) : Fin m → ℝ :=
  fun i => b i - rectMatMulVec A1 (rectMatMulVec R1inv qtd) i
/-- Exact residual reduction for Higham's elimination method in (20.29)-(20.30):
    substituting `x1 = R1^{-1}(qtd - R2 x2)` into `[A1 A2][x1; x2] - b`
    gives the unconstrained residual
    `(A2 - A1 R1^{-1} R2)x2 - (b - A1 R1^{-1}qtd)`.

    This is exact algebra under supplied partition and inverse-action data; it
    does not construct the pivoted QR factorization in (20.29). -/
theorem lseEliminationResidual_eq_reduced {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ) :
    lsResidual (lseEliminationBlockMatrix A1 A2) b
        (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) =
      fun i : Fin m =>
        lseEliminationReducedAction A1 A2 R1inv R2 x2 i -
          lseEliminationReducedRhs A1 R1inv qtd b i := by
  ext i
  have hback :
      lseEliminationBackSubstitution R1inv R2 qtd x2 =
        fun j : Fin p =>
          rectMatMulVec R1inv qtd j -
            rectMatMulVec R1inv (rectMatMulVec R2 x2) j := by
    ext j
    unfold lseEliminationBackSubstitution
    exact congrFun
      (rectMatMulVec_sub R1inv qtd (rectMatMulVec R2 x2)) j
  have hA1back :
      rectMatMulVec A1 (lseEliminationBackSubstitution R1inv R2 qtd x2) i =
        rectMatMulVec A1 (rectMatMulVec R1inv qtd) i -
          rectMatMulVec A1
            (rectMatMulVec R1inv (rectMatMulVec R2 x2)) i := by
    rw [hback]
    exact congrFun
      (rectMatMulVec_sub A1 (rectMatMulVec R1inv qtd)
        (rectMatMulVec R1inv (rectMatMulVec R2 x2))) i
  calc
    lsResidual (lseEliminationBlockMatrix A1 A2) b
        (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) i
        =
          (rectMatMulVec A1
              (lseEliminationBackSubstitution R1inv R2 qtd x2) i +
            rectMatMulVec A2 x2 i) - b i := by
            unfold lsResidual
            rw [congrFun
              (lseEliminationBlockMatrix_mulVec A1 A2
                (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) i]
    _ = lseEliminationReducedAction A1 A2 R1inv R2 x2 i -
          lseEliminationReducedRhs A1 R1inv qtd b i := by
            rw [hA1back]
            unfold lseEliminationReducedAction lseEliminationReducedRhs
            ring
/-- Squared objective for the reduced unconstrained problem in (20.30). -/
noncomputable def lseEliminationReducedObjective {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ) : ℝ :=
  vecNorm2Sq
    (fun i : Fin m =>
      lseEliminationReducedAction A1 A2 R1inv R2 x2 i -
        lseEliminationReducedRhs A1 R1inv qtd b i)
/-- Exact squared-objective reduction for Higham's elimination method in
    (20.29)-(20.30). -/
theorem lseEliminationObjective_eq_reduced {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ) :
    lsObjective (lseEliminationBlockMatrix A1 A2) b
        (Fin.append (lseEliminationBackSubstitution R1inv R2 qtd x2) x2) =
      lseEliminationReducedObjective A1 A2 R1inv R2 qtd b x2 := by
  unfold lsObjective lseEliminationReducedObjective
  rw [lseEliminationResidual_eq_reduced]
/-- A vector `x2` solves the reduced unconstrained least-squares problem
    displayed in Higham's equation (20.30). -/
def IsLSEEliminationReducedMinimizer {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (b : Fin m → ℝ) (x2 : Fin q → ℝ) : Prop :=
  ∀ z2 : Fin q → ℝ,
    lseEliminationReducedObjective A1 A2 R1inv R2 qtd b x2 ≤
      lseEliminationReducedObjective A1 A2 R1inv R2 qtd b z2
/-- Conversely to `lseEliminationBlockConstraint_eq_qtd_of_left_inverse`,
    a feasible partitioned vector has its leading block equal to the
    back-substitution value from (20.29), provided the supplied inverse action
    also satisfies `R1inv * R1 = I`. -/
theorem lseEliminationBackSubstitution_eq_of_block_constraint {p q : ℕ}
    (R1 R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (qtd : Fin p → ℝ) (x1 : Fin p → ℝ) (x2 : Fin q → ℝ)
    (hright : ∀ v : Fin p → ℝ, rectMatMulVec R1inv (rectMatMulVec R1 v) = v)
    (hconstraint :
      rectMatMulVec (lseEliminationBlockMatrix R1 R2) (Fin.append x1 x2) =
        qtd) :
    x1 = lseEliminationBackSubstitution R1inv R2 qtd x2 := by
  have hsplit := lseEliminationBlockMatrix_mulVec R1 R2 x1 x2
  have hR1 :
      rectMatMulVec R1 x1 =
        fun i : Fin p => qtd i - rectMatMulVec R2 x2 i := by
    ext i
    have hi := congrFun hconstraint i
    have hsplit_i := congrFun hsplit i
    rw [hsplit_i] at hi
    linarith
  calc
    x1 = rectMatMulVec R1inv (rectMatMulVec R1 x1) := by
      exact (hright x1).symm
    _ = lseEliminationBackSubstitution R1inv R2 qtd x2 := by
      rw [hR1]
      rfl
/-- Feasible points have feasible difference directions. -/
theorem LSEFeasible.direction_zero {p n : ℕ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hx : LSEFeasible B d x) (hy : LSEFeasible B d y) :
    rectMatMulVec B (fun j => y j - x j) = 0 := by
  ext i
  change rectMatMulVec B (fun j => y j - x j) i = 0
  rw [congrFun (rectMatMulVec_sub B y x) i, hy i, hx i]
  ring
/-- Adding a feasible direction, one in the nullspace of `B`, preserves the
    equality constraint. -/
theorem LSEFeasible.add_null_direction {p n : ℕ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x v : Fin n → ℝ}
    (hx : LSEFeasible B d x) (hv : rectMatMulVec B v = 0) (t : ℝ) :
    LSEFeasible B d (fun j => x j + t * v j) := by
  intro i
  have hvi : rectMatMulVec B v i = 0 := by
    simpa using congrFun hv i
  rw [congrFun (rectMatMulVec_add B x (fun j => t * v j)) i]
  rw [hx i, congrFun (rectMatMulVec_smul B t v) i, hvi]
  ring
private theorem lse_linear_term_eq_zero_of_quadratic_nonneg
    {a c : ℝ} (ha : 0 ≤ a)
    (hquad : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * a) :
    c = 0 := by
  by_contra hc
  let t : ℝ := -c / (a + 1)
  have hden_pos : 0 < a + 1 := by linarith
  have hden_ne : a + 1 ≠ 0 := ne_of_gt hden_pos
  have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_ne_zero hc
  have hcalc :
      2 * t * c + t ^ 2 * a =
        -(c ^ 2 * (a + 2)) / (a + 1) ^ 2 := by
    dsimp [t]
    field_simp [hden_ne]
    ring
  have hnum_pos : 0 < c ^ 2 * (a + 2) := by nlinarith
  have hden_sq_pos : 0 < (a + 1) ^ 2 := sq_pos_of_pos hden_pos
  have hneg : -(c ^ 2 * (a + 2)) / (a + 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hnum_pos) hden_sq_pos
  have ht := hquad t
  rw [hcalc] at ht
  linarith
private noncomputable def lseDotDual {n : ℕ}
    (g : Fin n → ℝ) : Module.Dual ℝ (Fin n → ℝ) where
  toFun v := ∑ j : Fin n, g j * v j
  map_add' := by
    intro x y
    simp_rw [Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    calc
      ∑ j : Fin n, g j * (a * x j) = a * ∑ j : Fin n, g j * x j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (RingHom.id ℝ) a * ∑ j : Fin n, g j * x j := rfl
private theorem lseConstraintLinearMap_basis {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (j : Fin n) :
    lseConstraintLinearMap B (Pi.single j (1 : ℝ) : Fin n → ℝ) =
      fun r : Fin p => B r j := by
  classical
  ext r
  change (∑ k : Fin n, B r k *
      ((Pi.single j (1 : ℝ) : Fin n → ℝ) k)) = B r j
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk]
    ring
  · intro hj
    simp at hj
private theorem lseDotDual_basis {n : ℕ} (g : Fin n → ℝ) (j : Fin n) :
    lseDotDual g (Pi.single j (1 : ℝ) : Fin n → ℝ) = g j := by
  classical
  change (∑ k : Fin n, g k *
      ((Pi.single j (1 : ℝ) : Fin n → ℝ) k)) = g j
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk]
    ring
  · intro hj
    simp at hj
private theorem lseDual_eval_eq_sum {p : ℕ}
    (psi : Module.Dual ℝ (Fin p → ℝ)) (y : Fin p → ℝ) :
    psi y = ∑ r : Fin p, y r *
      psi (Pi.single r (1 : ℝ) : Fin p → ℝ) := by
  classical
  calc
    psi y = psi (∑ r : Fin p, Pi.single r (y r)) := by
      rw [Finset.univ_sum_single]
    _ = ∑ r : Fin p, psi (Pi.single r (y r)) := by
      rw [map_sum]
    _ = ∑ r : Fin p, y r *
        psi (Pi.single r (1 : ℝ) : Fin p → ℝ) := by
      apply Finset.sum_congr rfl
      intro r _
      have hsingle :
          Pi.single r (y r) =
            y r • (Pi.single r (1 : ℝ) : Fin p → ℝ) := by
        ext s
        by_cases hsr : s = r
        · subst s
          simp
        · simp [Pi.single_eq_of_ne hsr]
      rw [hsingle, map_smul]
      rfl
private noncomputable def lseKernelFactorDual {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (hB : LSEFullRowRank B)
    (g : Fin n → ℝ)
    (hker : ∀ v : Fin n → ℝ, rectMatMulVec B v = 0 →
      lseDotDual g v = 0) :
    Module.Dual ℝ (Fin p → ℝ) where
  toFun y := lseDotDual g (Classical.choose (hB y))
  map_add' := by
    intro y z
    let xy : Fin n → ℝ := Classical.choose (hB y)
    let xz : Fin n → ℝ := Classical.choose (hB z)
    let xyz : Fin n → ℝ := Classical.choose (hB (y + z))
    have hxy_lm : lseConstraintLinearMap B xy = y :=
      Classical.choose_spec (hB y)
    have hxz_lm : lseConstraintLinearMap B xz = z :=
      Classical.choose_spec (hB z)
    have hxyz_lm : lseConstraintLinearMap B xyz = y + z :=
      Classical.choose_spec (hB (y + z))
    let w : Fin n → ℝ := xyz - (xy + xz)
    have hBw_lm : lseConstraintLinearMap B w = 0 := by
      dsimp [w]
      rw [map_sub, map_add, hxyz_lm, hxy_lm, hxz_lm]
      ext r
      simp
    have hBw : rectMatMulVec B w = 0 := by
      simpa [lseConstraintLinearMap] using hBw_lm
    have hw0 : lseDotDual g w = 0 := hker w hBw
    have hxyz_eq : lseDotDual g xyz = lseDotDual g (xy + xz) := by
      have hw0' : lseDotDual g (xyz - (xy + xz)) = 0 := by
        simpa [w] using hw0
      rw [map_sub] at hw0'
      exact sub_eq_zero.mp hw0'
    calc
      lseDotDual g (Classical.choose (hB (y + z)))
          = lseDotDual g xyz := rfl
      _ = lseDotDual g (xy + xz) := hxyz_eq
      _ = lseDotDual g xy + lseDotDual g xz := by rw [map_add]
      _ = lseDotDual g (Classical.choose (hB y)) +
          lseDotDual g (Classical.choose (hB z)) := rfl
  map_smul' := by
    intro a y
    let xy : Fin n → ℝ := Classical.choose (hB y)
    let xay : Fin n → ℝ := Classical.choose (hB (a • y))
    have hxy_lm : lseConstraintLinearMap B xy = y :=
      Classical.choose_spec (hB y)
    have hxay_lm : lseConstraintLinearMap B xay = a • y :=
      Classical.choose_spec (hB (a • y))
    let w : Fin n → ℝ := xay - a • xy
    have hBw_lm : lseConstraintLinearMap B w = 0 := by
      dsimp [w]
      rw [map_sub, map_smul, hxay_lm, hxy_lm]
      ext r
      simp
    have hBw : rectMatMulVec B w = 0 := by
      simpa [lseConstraintLinearMap] using hBw_lm
    have hw0 : lseDotDual g w = 0 := hker w hBw
    have hxay_eq : lseDotDual g xay = lseDotDual g (a • xy) := by
      have hw0' : lseDotDual g (xay - a • xy) = 0 := by
        simpa [w] using hw0
      rw [map_sub] at hw0'
      exact sub_eq_zero.mp hw0'
    calc
      lseDotDual g (Classical.choose (hB (a • y)))
          = lseDotDual g xay := rfl
      _ = lseDotDual g (a • xy) := hxay_eq
      _ = a • lseDotDual g xy := by rw [map_smul]
      _ = a •
          lseDotDual g (Classical.choose (hB y)) := rfl
private theorem lseKernelFactorDual_apply_constraint {p n : ℕ}
    (B : Fin p → Fin n → ℝ) (hB : LSEFullRowRank B)
    (g : Fin n → ℝ)
    (hker : ∀ v : Fin n → ℝ, rectMatMulVec B v = 0 →
      lseDotDual g v = 0)
    (v : Fin n → ℝ) :
    lseKernelFactorDual B hB g hker (rectMatMulVec B v) =
      lseDotDual g v := by
  let x : Fin n → ℝ := Classical.choose (hB (rectMatMulVec B v))
  have hx_lm :
      lseConstraintLinearMap B x = rectMatMulVec B v :=
    Classical.choose_spec (hB (rectMatMulVec B v))
  let w : Fin n → ℝ := x - v
  have hBw_lm : lseConstraintLinearMap B w = 0 := by
    dsimp [w]
    rw [map_sub, hx_lm]
    ext r
    simp [lseConstraintLinearMap]
  have hBw : rectMatMulVec B w = 0 := by
    simpa [lseConstraintLinearMap] using hBw_lm
  have hw0 : lseDotDual g w = 0 := hker w hBw
  have hx_eq : lseDotDual g x = lseDotDual g v := by
    have hw0' : lseDotDual g (x - v) = 0 := by
      simpa [w] using hw0
    rw [map_sub] at hw0'
    exact sub_eq_zero.mp hw0'
  calc
    lseKernelFactorDual B hB g hker (rectMatMulVec B v)
        = lseDotDual g x := rfl
    _ = lseDotDual g v := hx_eq
/-- An exact equality-constrained least-squares minimizer has zero objective
    first variation along every feasible direction `v` satisfying `B v = 0`. -/
theorem IsLSEMinimizer.feasible_direction_stationarity {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x v : Fin n → ℝ}
    (hmin : IsLSEMinimizer A b B d x)
    (hv : rectMatMulVec B v = 0) :
    ∑ j : Fin n, v j * (∑ i : Fin m, A i j * lsResidual A b x i) = 0 := by
  let c : ℝ :=
    ∑ j : Fin n, v j * (∑ i : Fin m, A i j * lsResidual A b x i)
  let a : ℝ := vecNorm2Sq (rectMatMulVec A v)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact vecNorm2Sq_nonneg (rectMatMulVec A v)
  have hquad : ∀ t : ℝ, 0 ≤ 2 * t * c + t ^ 2 * a := by
    intro t
    let tv : Fin n → ℝ := fun j => t * v j
    have hfeas : LSEFeasible B d (fun j => x j + tv j) := by
      dsimp [tv]
      exact LSEFeasible.add_null_direction hmin.1 hv t
    have hobj := hmin.2 (fun j => x j + tv j) hfeas
    have hexp := lsObjective_add_direction_eq A b x tv
    have hcross :
        (∑ j : Fin n, tv j *
          (∑ i : Fin m, A i j * lsResidual A b x i)) = t * c := by
      dsimp [tv, c]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hnorm : vecNorm2Sq (rectMatMulVec A tv) = t ^ 2 * a := by
      dsimp [tv, a]
      rw [rectMatMulVec_smul, vecNorm2Sq_smul]
    rw [hexp, hcross, hnorm] at hobj
    nlinarith
  exact lse_linear_term_eq_zero_of_quadratic_nonneg ha hquad
/-- Higham, 2nd ed., Chapter 20, Problem 20.10, sufficiency direction:
    feasibility together with a Lagrange multiplier satisfying
    `A^T (b - A*x) = B^T lambda` implies that `x` solves the LSE problem
    (20.23).  The converse multiplier-existence direction is a separate
    dual-space factorization obligation. -/
theorem IsLSEMinimizer.of_lagrange_normal_equations {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x : Fin n → ℝ} {lambda : Fin p → ℝ}
    (hfeas : LSEFeasible B d x)
    (hlambda : ∀ j : Fin n,
      ∑ i : Fin m, A i j * lsResidualHigham A b x i =
        ∑ r : Fin p, B r j * lambda r) :
    IsLSEMinimizer A b B d x := by
  refine ⟨hfeas, ?_⟩
  intro y hy
  let v : Fin n → ℝ := fun j => y j - x j
  have hy_eq : y = fun j => x j + v j := by
    ext j
    dsimp [v]
    ring
  have hBv : rectMatMulVec B v = 0 := by
    dsimp [v]
    exact LSEFeasible.direction_zero hfeas hy
  have hhigham :
      (∑ j : Fin n,
        v j * (∑ i : Fin m, A i j * lsResidualHigham A b x i)) = 0 := by
    calc
      (∑ j : Fin n,
        v j * (∑ i : Fin m, A i j * lsResidualHigham A b x i))
          = ∑ j : Fin n,
              v j * (∑ r : Fin p, B r j * lambda r) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hlambda j]
      _ = ∑ r : Fin p, lambda r * rectMatMulVec B v r := by
            calc
              (∑ j : Fin n, v j * (∑ r : Fin p, B r j * lambda r))
                  = ∑ j : Fin n, ∑ r : Fin p,
                      v j * (B r j * lambda r) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [Finset.mul_sum]
              _ = ∑ r : Fin p, ∑ j : Fin n,
                      v j * (B r j * lambda r) := by
                    rw [Finset.sum_comm]
              _ = ∑ r : Fin p, lambda r * rectMatMulVec B v r := by
                    apply Finset.sum_congr rfl
                    intro r _
                    unfold rectMatMulVec
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
      _ = 0 := by
            apply Finset.sum_eq_zero
            intro r _
            have hr : rectMatMulVec B v r = 0 := by
              simpa using congrFun hBv r
            rw [hr]
            ring
  have hcross :
      (∑ j : Fin n,
        v j * (∑ i : Fin m, A i j * lsResidual A b x i)) = 0 := by
    have hsign :
        (∑ j : Fin n,
          v j * (∑ i : Fin m, A i j * lsResidual A b x i)) =
          - (∑ j : Fin n,
            v j * (∑ i : Fin m, A i j * lsResidualHigham A b x i)) := by
      calc
        (∑ j : Fin n,
          v j * (∑ i : Fin m, A i j * lsResidual A b x i))
            = ∑ j : Fin n,
                v j * (-(∑ i : Fin m,
                  A i j * lsResidualHigham A b x i)) := by
              apply Finset.sum_congr rfl
              intro j _
              congr 1
              rw [lsResidualHigham_eq_neg_lsResidual A b x]
              simp
        _ = - (∑ j : Fin n,
            v j * (∑ i : Fin m, A i j * lsResidualHigham A b x i)) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
    rw [hsign, hhigham]
    ring
  have hexp := lsObjective_add_direction_eq A b x v
  rw [← hy_eq] at hexp
  rw [hexp, hcross]
  have hnonneg : 0 ≤ vecNorm2Sq (rectMatMulVec A v) :=
    vecNorm2Sq_nonneg (rectMatMulVec A v)
  nlinarith
/-- Higham, 2nd ed., Chapter 20, Problem 20.10, necessity direction under
    the source full-row-rank constraint qualification: an LSE minimizer admits
    Lagrange multipliers satisfying the normal equations
    `A^T (b - A*x) = B^T lambda`, together with feasibility `B*x = d`. -/
theorem IsLSEMinimizer.exists_lagrange_normal_equations_of_fullRowRank
    {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x : Fin n → ℝ}
    (hmin : IsLSEMinimizer A b B d x)
    (hB : LSEFullRowRank B) :
    ∃ lambda : Fin p → ℝ,
      LSEFeasible B d x ∧
        ∀ j : Fin n,
          ∑ i : Fin m, A i j * lsResidualHigham A b x i =
            ∑ r : Fin p, B r j * lambda r := by
  let g : Fin n → ℝ :=
    fun j => ∑ i : Fin m, A i j * lsResidual A b x i
  have hker : ∀ v : Fin n → ℝ, rectMatMulVec B v = 0 →
      lseDotDual g v = 0 := by
    intro v hv
    have hstat := hmin.feasible_direction_stationarity hv
    simpa [lseDotDual, g, mul_comm] using hstat
  let psi : Module.Dual ℝ (Fin p → ℝ) :=
    lseKernelFactorDual B hB g hker
  let lambda : Fin p → ℝ :=
    fun r => -psi (Pi.single r (1 : ℝ) : Fin p → ℝ)
  refine ⟨lambda, hmin.1, ?_⟩
  intro j
  have hpsi_j : psi (fun r : Fin p => B r j) = g j := by
    have hBbasis :
        rectMatMulVec B (Pi.single j (1 : ℝ) : Fin n → ℝ) =
          fun r : Fin p => B r j := by
      simpa [lseConstraintLinearMap] using
        lseConstraintLinearMap_basis B j
    have happly :=
      lseKernelFactorDual_apply_constraint B hB g hker
        (Pi.single j (1 : ℝ) : Fin n → ℝ)
    have hdot := lseDotDual_basis g j
    change lseKernelFactorDual B hB g hker
        (fun r : Fin p => B r j) = g j
    rw [← hBbasis]
    exact happly.trans hdot
  have hhigham :
      (∑ i : Fin m, A i j * lsResidualHigham A b x i) = -g j := by
    calc
      (∑ i : Fin m, A i j * lsResidualHigham A b x i)
          = ∑ i : Fin m, A i j * (-lsResidual A b x i) := by
            rw [lsResidualHigham_eq_neg_lsResidual A b x]
      _ = - (∑ i : Fin m, A i j * lsResidual A b x i) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = -g j := rfl
  have hsum_lambda :
      (∑ r : Fin p, B r j * lambda r) =
        -psi (fun r : Fin p => B r j) := by
    have hpsi_sum := lseDual_eval_eq_sum psi (fun r : Fin p => B r j)
    dsimp [lambda]
    calc
      (∑ r : Fin p, B r j *
          -psi (Pi.single r (1 : ℝ) : Fin p → ℝ))
          =
            - (∑ r : Fin p, B r j *
              psi (Pi.single r (1 : ℝ) : Fin p → ℝ)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro r _
            ring
      _ = -psi (fun r : Fin p => B r j) := by
            rw [← hpsi_sum]
  calc
    (∑ i : Fin m, A i j * lsResidualHigham A b x i)
        = -g j := hhigham
    _ = -psi (fun r : Fin p => B r j) := by rw [hpsi_j]
    _ = ∑ r : Fin p, B r j * lambda r := hsum_lambda.symm
/-- Higham, 2nd ed., Chapter 20, Problem 20.10: under full row rank of the
    constraint matrix, solving the equality-constrained least-squares problem
    (20.23) is equivalent to feasibility plus the Lagrange-multiplier normal
    equations `A^T (b - A*x) = B^T lambda`. -/
theorem isLSEMinimizer_iff_exists_lagrange_normal_equations_of_fullRowRank
    {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x : Fin n → ℝ}
    (hB : LSEFullRowRank B) :
    IsLSEMinimizer A b B d x ↔
      ∃ lambda : Fin p → ℝ,
        LSEFeasible B d x ∧
          ∀ j : Fin n,
            ∑ i : Fin m, A i j * lsResidualHigham A b x i =
              ∑ r : Fin p, B r j * lambda r := by
  constructor
  · intro hmin
    exact hmin.exists_lagrange_normal_equations_of_fullRowRank hB
  · rintro ⟨lambda, hfeas, hnormal⟩
    exact IsLSEMinimizer.of_lagrange_normal_equations
      (lambda := lambda) hfeas hnormal
/-- Matrix of a finite-dimensional real linear map in the standard coordinate
    basis.  The row index is the output coordinate and the column index is the
    input coordinate. -/
noncomputable def linearMapBasisMatrix {m n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) : Fin m → Fin n → ℝ :=
  fun i j => L (finiteBasisVec j) i
/-- A finite-dimensional real linear map acts as multiplication by its
    standard-basis matrix. -/
theorem linearMap_apply_eq_rectMatMulVec_basisMatrix {m n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (v : Fin n → ℝ) :
    L v = rectMatMulVec (linearMapBasisMatrix L) v := by
  have hv : v = ∑ j : Fin n, v j • finiteBasisVec j := by
    ext k
    simp [finiteBasisVec]
  ext i
  calc
    L v i = L (∑ j : Fin n, v j • finiteBasisVec j) i :=
      congrArg (fun z => L z i) hv
    _ = (∑ j : Fin n, L (v j • finiteBasisVec j)) i := by
        rw [map_sum]
    _ = ∑ j : Fin n, (L (v j • finiteBasisVec j)) i := by
        simp
    _ = ∑ j : Fin n, v j * L (finiteBasisVec j) i := by
        simp [map_smul]
    _ = ∑ j : Fin n, L (finiteBasisVec j) i * v j := by
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = rectMatMulVec (linearMapBasisMatrix L) v i := by
        simp [rectMatMulVec, linearMapBasisMatrix]
/-- Euclidean operator-2 bound for a finite-dimensional real linear map,
    using the repository's `complexMatrixOp2` model on its standard-basis
    matrix. -/
theorem linearMap_vecNorm2_le_complexMatrixOp2_basisMatrix {m n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (v : Fin n → ℝ) :
    vecNorm2 (L v) ≤
      complexMatrixOp2 (realRectToCMatrix (linearMapBasisMatrix L)) *
        vecNorm2 v := by
  rw [linearMap_apply_eq_rectMatMulVec_basisMatrix L v]
  exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
    (linearMapBasisMatrix L) le_rfl v
/-- Higham, 2nd ed., Chapter 20, Section 20.9:
    the second condition in (20.24), `null(A) ∩ null(B) = {0}`, guarantees
    uniqueness of an equality-constrained least-squares minimizer once
    existence is represented. -/
theorem IsLSEMinimizer.eq_of_nullIntersectionTrivial {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hnull : LSENullIntersectionTrivial A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer A b B d y) :
    x = y := by
  let v : Fin n → ℝ := fun j => y j - x j
  have hBv : rectMatMulVec B v = 0 := by
    dsimp [v]
    exact LSEFeasible.direction_zero hx.1 hy.1
  have hstat := hx.feasible_direction_stationarity hBv
  have hy_eq : y = fun j => x j + v j := by
    ext j
    dsimp [v]
    ring
  have hxy : lsObjective A b x ≤ lsObjective A b y := hx.2 y hy.1
  have hyx : lsObjective A b y ≤ lsObjective A b x := hy.2 x hx.1
  have hobj_eq : lsObjective A b y = lsObjective A b x :=
    le_antisymm hyx hxy
  have hexp := lsObjective_add_direction_eq A b x v
  rw [← hy_eq] at hexp
  have hAv_sq : vecNorm2Sq (rectMatMulVec A v) = 0 := by
    have hnonneg : 0 ≤ vecNorm2Sq (rectMatMulVec A v) :=
      vecNorm2Sq_nonneg (rectMatMulVec A v)
    nlinarith [hobj_eq, hexp, hstat]
  have hAv_norm : vecNorm2 (rectMatMulVec A v) = 0 := by
    have hsquare : vecNorm2 (rectMatMulVec A v) ^ 2 = 0 := by
      rw [vecNorm2_sq, hAv_sq]
    exact sq_eq_zero_iff.mp hsquare
  have hAv : rectMatMulVec A v = 0 := by
    ext i
    change rectMatMulVec A v i = 0
    exact (vecNorm2_eq_zero_iff (rectMatMulVec A v)).mp hAv_norm i
  have hvzero : v = 0 := hnull v hAv hBv
  ext j
  have hvj : v j = 0 := by
    simpa using congrFun hvzero j
  dsimp [v] at hvj
  linarith
/-- Higham, 2nd ed., Chapter 20, equation (20.24), uniqueness bridge:
    once an equality-constrained least-squares minimizer exists, uniqueness is
    equivalent to the null-intersection condition `null(A) ∩ null(B) = {0}`.

    The reverse implication is the source uniqueness guarantee.  The forward
    implication records the exact finite-dimensional necessity proof: a common
    null vector can be added to any minimizer without changing feasibility or
    objective value. -/
theorem exists_unique_isLSEMinimizer_iff_nullIntersectionTrivial_of_exists
    {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    (hex : ∃ x : Fin n → ℝ, IsLSEMinimizer A b B d x) :
    (∃! x : Fin n → ℝ, IsLSEMinimizer A b B d x) ↔
      LSENullIntersectionTrivial A B := by
  constructor
  · intro huniq
    rcases huniq with ⟨x, hx, hunique⟩
    intro v hAv hBv
    let y : Fin n → ℝ := fun j => x j + v j
    have hy_feas : LSEFeasible B d y := by
      intro i
      have hvi : rectMatMulVec B v i = 0 := by
        simpa using congrFun hBv i
      dsimp [y]
      rw [congrFun (rectMatMulVec_add B x v) i, hx.1 i, hvi]
      ring
    have hcross :
        (∑ j : Fin n,
          v j * (∑ i : Fin m, A i j * lsResidual A b x i)) = 0 := by
      calc
        (∑ j : Fin n,
          v j * (∑ i : Fin m, A i j * lsResidual A b x i))
            = ∑ j : Fin n, ∑ i : Fin m,
                v j * (A i j * lsResidual A b x i) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
        _ = ∑ i : Fin m, ∑ j : Fin n,
                v j * (A i j * lsResidual A b x i) := by
              rw [Finset.sum_comm]
        _ = ∑ i : Fin m,
                lsResidual A b x i * rectMatMulVec A v i := by
              apply Finset.sum_congr rfl
              intro i _
              unfold rectMatMulVec
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = 0 := by
              apply Finset.sum_eq_zero
              intro i _
              have hAvi : rectMatMulVec A v i = 0 := by
                simpa using congrFun hAv i
              rw [hAvi]
              ring
    have hAv_sq : vecNorm2Sq (rectMatMulVec A v) = 0 := by
      rw [hAv]
      simp [vecNorm2Sq]
    have hobj_y : lsObjective A b y = lsObjective A b x := by
      dsimp [y]
      rw [lsObjective_add_direction_eq A b x v, hcross, hAv_sq]
      ring
    have hy : IsLSEMinimizer A b B d y := by
      refine ⟨hy_feas, ?_⟩
      intro z hz
      rw [hobj_y]
      exact hx.2 z hz
    have hyx : y = x := hunique y hy
    ext j
    change v j = 0
    have hj := congrFun hyx j
    dsimp [y] at hj
    linarith
  · intro hnull
    rcases hex with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact IsLSEMinimizer.eq_of_nullIntersectionTrivial hnull hy hx
/-- Higham, 2nd ed., Chapter 20, equation (20.24), stacked-rank uniqueness
    bridge:
    once an equality-constrained least-squares minimizer exists, uniqueness is
    equivalent to the local full-column-rank condition for `[A^T, B^T]^T`,
    represented here as injectivity of the vertical stack `[A; B]`.

    This is the source full-column-rank wording combined with the exact
    null-intersection uniqueness bridge. -/
theorem exists_unique_isLSEMinimizer_iff_lseStackedFullColumnRank_of_exists
    {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    (hex : ∃ x : Fin n → ℝ, IsLSEMinimizer A b B d x) :
    (∃! x : Fin n → ℝ, IsLSEMinimizer A b B d x) ↔
      LSEStackedFullColumnRank A B :=
  (exists_unique_isLSEMinimizer_iff_nullIntersectionTrivial_of_exists
    (A := A) (b := b) (B := B) (d := d) hex).trans
    (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B)
/-- Higham, 2nd ed., Chapter 20, equation (20.24), direct stacked-rank
    uniqueness consequence:
    the local full-column-rank condition for `[A^T, B^T]^T`, represented by
    injectivity of `[A; B]`, makes any two exact LSE minimizers equal.

    This is the source uniqueness statement at the stacked-matrix surface.  It
    does not prove full-row-rank consistency or GQR factor construction. -/
theorem IsLSEMinimizer.eq_of_lseStackedFullColumnRank
    {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hstack : LSEStackedFullColumnRank A B)
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer A b B d y) :
    x = y :=
  IsLSEMinimizer.eq_of_nullIntersectionTrivial
    ((LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hstack)
    hx hy
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    Householder `gamma_tilde_mn` coefficient for the `A` and `b` perturbation
    bounds, using the Chapter 19 Householder QR coefficient with the local
    matrix dimensions `m = r + q` and `n = p + q`. -/
noncomputable def theorem20_10_householder_gammaA
    (fp : FPModel) (r p q : ℕ) : ℝ :=
  H19.Theorem19_4.gamma_tilde fp (r + q) (p + q)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    Householder `gamma_tilde_np` coefficient for the `B`, `Delta x`, and
    `Delta d` bounds.  The GQR method first triangularizes `Bᵀ`, whose local
    dimensions are `(p + q) × p`. -/
noncomputable def theorem20_10_householder_gammaB
    (fp : FPModel) (_r p q : ℕ) : ℝ :=
  H19.Theorem19_4.gamma_tilde fp (p + q) p
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    conservative scalar coefficient currently proved for the rounded
    Householder RHS transform in the `A Q₂` panel. -/
noncomputable def theorem20_10_householder_rhs_conservative_gamma
    (fp : FPModel) (r _p q : ℕ) : ℝ :=
  Real.sqrt (r + q : ℝ) *
    ((2 : ℝ) *
      (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) *
      gamma fp (q * householderConstructApplyGammaIndex (r + q)))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    conservative `A`/`b` coefficient for the rounded-Householder-RHS Part A
    route.  It preserves the printed Householder `A`-matrix coefficient while
    making the larger verified RHS coefficient explicit. -/
noncomputable def theorem20_10_householder_gammaA_conservativeRhs
    (fp : FPModel) (r p q : ℕ) : ℝ :=
  max (theorem20_10_householder_gammaA fp r p q)
    (theorem20_10_householder_rhs_conservative_gamma fp r p q)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    conservative composed `A`/`b` coefficient for the constructed rounded
    Householder GQR Part A certificate.

    The two terms are the original Householder matrix/RHS budgets plus the
    second triangular-solve perturbation layer. -/
noncomputable def theorem20_10_householder_composed_partA_gammaA
    (fp : FPModel) (r p q : ℕ) : ℝ :=
  max
    (theorem20_10_householder_gammaA fp r p q +
      gamma fp q * (1 + theorem20_10_householder_gammaA fp r p q))
    (theorem20_10_householder_rhs_conservative_gamma fp r p q +
      gamma fp q *
        (1 + theorem20_10_householder_rhs_conservative_gamma fp r p q))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    conservative composed `B`/`DeltaX` coefficient for the constructed rounded
    Householder GQR Part A certificate. -/
noncomputable def theorem20_10_householder_composed_partA_gammaB
    (fp : FPModel) (r p q : ℕ) : ℝ :=
  theorem20_10_householder_gammaB fp r p q +
    gamma fp p * (1 + theorem20_10_householder_gammaB fp r p q)
/-- Nonnegativity of the conservative `A` coefficient used by the
    Theorem 20.10(b) concrete Householder component branch. -/
theorem theorem20_10_householder_gammaA_conservativeRhs_nonneg
    {r p q : ℕ} (fp : FPModel)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q))) :
    0 ≤ theorem20_10_householder_gammaA_conservativeRhs fp r p q := by
  have hgammaA_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidA
  exact le_trans hgammaA_nonneg (le_max_left _ _)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    dimension-only linear unit-roundoff coefficient that dominates the
    conservative Householder component max-gamma coefficient under the usual
    `gamma <= 2*n*u` half-radius guards.

    The three branches correspond to the printed `A` Householder coefficient,
    the verified conservative RHS coefficient, and the `Bᵀ` Householder
    coefficient. -/
noncomputable def theorem20_10_householder_componentUnitRoundoffCoefficient
    (r p q : ℕ) : ℝ :=
  max
    (max
      ((2 : ℝ) *
        (((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ))
      ((4 : ℝ) * Real.sqrt (r + q : ℝ) *
        (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) *
        ((q * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ)))
    ((2 : ℝ) *
      (((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ)))
/-- Nonnegativity of the dimension-only coefficient used by the
    Theorem 20.10(b) conservative unit-roundoff threshold wrapper. -/
theorem theorem20_10_householder_componentUnitRoundoffCoefficient_nonneg
    (r p q : ℕ) :
    0 ≤ theorem20_10_householder_componentUnitRoundoffCoefficient r p q := by
  dsimp [theorem20_10_householder_componentUnitRoundoffCoefficient]
  positivity
/-- Positivity of the dimension-only unit-roundoff coefficient in the
    Theorem 20.10(b) component source-rank branch.  The `Bᵀ` Householder
    component is already positive when the constraint block has at least one
    row. -/
theorem theorem20_10_householder_componentUnitRoundoffCoefficient_pos
    {r p q : ℕ} (hp : 0 < p) :
    0 < theorem20_10_householder_componentUnitRoundoffCoefficient r p q := by
  have hK_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hidx_nat :
      0 < p * householderConstructApplyGammaIndex (p + q) :=
    Nat.mul_pos hp hK_pos
  have hidx :
      0 < (((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ)) := by
    exact_mod_cast hidx_nat
  have hcapB :
      0 < (2 : ℝ) *
        (((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ)) :=
    mul_pos (by norm_num) hidx
  dsimp [theorem20_10_householder_componentUnitRoundoffCoefficient]
  exact lt_of_lt_of_le hcapB (le_max_right _ _)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    linear unit-roundoff cap for the printed `A` Householder coefficient under
    the standard half-radius smallness condition. -/
theorem theorem20_10_householder_gammaA_le_linear_unit_roundoff_of_small
    {r p q : ℕ} (fp : FPModel)
    (hsmallA :
      ((((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ) *
        fp.u ≤ 1 / 2)) :
    theorem20_10_householder_gammaA fp r p q ≤
      (2 * (((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ)) *
        fp.u := by
  simpa [theorem20_10_householder_gammaA] using
    H19.Theorem19_4.gamma_tilde_le_two_index_mul_unit_roundoff_of_small
      fp (r + q) (p + q) hsmallA
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    linear unit-roundoff cap for the `Bᵀ` Householder coefficient under the
    standard half-radius smallness condition. -/
theorem theorem20_10_householder_gammaB_le_linear_unit_roundoff_of_small
    {r p q : ℕ} (fp : FPModel)
    (hsmallB :
      ((((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ) *
        fp.u) ≤ 1 / 2)) :
    theorem20_10_householder_gammaB fp r p q ≤
      (2 * (((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ)) *
        fp.u) := by
  simpa [theorem20_10_householder_gammaB] using
    H19.Theorem19_4.gamma_tilde_le_two_index_mul_unit_roundoff_of_small
      fp (p + q) p hsmallB
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    linear unit-roundoff cap for the verified conservative RHS coefficient
    used by the rounded Householder `A Q₂` path. -/
theorem theorem20_10_householder_rhs_conservative_gamma_le_linear_unit_roundoff_of_small
    {r p q : ℕ} (fp : FPModel)
    (hm : 0 < r + q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    theorem20_10_householder_rhs_conservative_gamma fp r p q ≤
      ((4 : ℝ) * Real.sqrt (r + q : ℝ) *
        (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) *
        ((q * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ)) *
        fp.u := by
  let idx : ℕ := householderQRRhsPanelGammaClosedGrowthIndex (r + q) q
  let K : ℕ := householderConstructApplyGammaIndex (r + q)
  let F : ℝ :=
    (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ)
  have hprinted_le_idx : q * K ≤ idx := by
    change q * householderConstructApplyGammaIndex (r + q) ≤
      householderQRRhsPanelGammaClosedGrowthIndex (r + q) q
    rw [householderQRRhsPanelGammaClosedGrowthIndex_eq_factor_mul_printedIndex]
    exact Nat.le_mul_of_pos_left _
      (householderQRRhsPanelGammaClosedGrowthFactor_pos
        (m := r + q) (p := q) hm)
  have hqK_le_idx_real :
      (((q * K : ℕ) : ℝ) * fp.u) ≤ (idx : ℝ) * fp.u := by
    have hidx : (((q * K : ℕ) : ℝ)) ≤ (idx : ℝ) := by
      exact_mod_cast hprinted_le_idx
    exact mul_le_mul_of_nonneg_right hidx fp.u_nonneg
  have hqK_half :
      (((q * K : ℕ) : ℝ) * fp.u) ≤ 1 / 2 := by
    exact le_trans hqK_le_idx_real (by simpa [idx] using hhalf)
  have hgamma :
      gamma fp (q * K) ≤ 2 * (((q * K : ℕ) : ℝ) * fp.u) :=
    gamma_le_two_mul_n_u_of_nu_le_half fp (q * K) hqK_half
  have hscale_nonneg :
      0 ≤ Real.sqrt (r + q : ℝ) * ((2 : ℝ) * F) := by
    positivity
  calc
    theorem20_10_householder_rhs_conservative_gamma fp r p q
        = (Real.sqrt (r + q : ℝ) * ((2 : ℝ) * F)) *
            gamma fp (q * K) := by
            simp [theorem20_10_householder_rhs_conservative_gamma, K, F,
              mul_assoc, mul_comm]
    _ ≤ (Real.sqrt (r + q : ℝ) * ((2 : ℝ) * F)) *
          (2 * (((q * K : ℕ) : ℝ) * fp.u)) :=
        mul_le_mul_of_nonneg_left hgamma hscale_nonneg
    _ = ((4 : ℝ) * Real.sqrt (r + q : ℝ) * F *
          ((q * K : ℕ) : ℝ)) * fp.u := by ring
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the conservative component max-gamma coefficient is bounded by the
    dimension-only unit-roundoff coefficient under explicit half-radius guards
    for the three accumulated gamma terms. -/
theorem theorem20_10_householder_component_max_gamma_le_componentUnitRoundoffCoefficient_mul_u_of_small
    {r p q : ℕ} (fp : FPModel)
    (hm : 0 < r + q)
    (hsmallA :
      ((((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ) *
        fp.u ≤ 1 / 2))
    (hsmallB :
      ((((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ) *
        fp.u) ≤ 1 / 2))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
        (theorem20_10_householder_gammaB fp r p q) ≤
      theorem20_10_householder_componentUnitRoundoffCoefficient r p q * fp.u := by
  let capA : ℝ :=
    (2 : ℝ) *
      (((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ)
  let capRhs : ℝ :=
    (4 : ℝ) * Real.sqrt (r + q : ℝ) *
      (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) *
      ((q * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ)
  let capB : ℝ :=
    (2 : ℝ) *
      (((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ))
  let cap : ℝ :=
    theorem20_10_householder_componentUnitRoundoffCoefficient r p q
  have hcapA_le : capA ≤ cap := by
    dsimp [cap, capA, capRhs, capB,
      theorem20_10_householder_componentUnitRoundoffCoefficient]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hcapRhs_le : capRhs ≤ cap := by
    dsimp [cap, capA, capRhs, capB,
      theorem20_10_householder_componentUnitRoundoffCoefficient]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hcapB_le : capB ≤ cap := by
    dsimp [cap, capA, capRhs, capB,
      theorem20_10_householder_componentUnitRoundoffCoefficient]
    exact le_max_right _ _
  have hAraw :
      theorem20_10_householder_gammaA fp r p q ≤ capA * fp.u := by
    simpa [capA] using
      (theorem20_10_householder_gammaA_le_linear_unit_roundoff_of_small
        fp hsmallA)
  have hRhsraw :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤
        capRhs * fp.u := by
    simpa [capRhs] using
      (theorem20_10_householder_rhs_conservative_gamma_le_linear_unit_roundoff_of_small
        fp hm hhalf)
  have hBraw :
      theorem20_10_householder_gammaB fp r p q ≤ capB * fp.u := by
    simpa [capB] using
      (theorem20_10_householder_gammaB_le_linear_unit_roundoff_of_small
        fp hsmallB)
  have hA :
      theorem20_10_householder_gammaA fp r p q ≤ cap * fp.u := by
    exact le_trans hAraw
      (mul_le_mul_of_nonneg_right hcapA_le fp.u_nonneg)
  have hRhs :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤
        cap * fp.u := by
    exact le_trans hRhsraw
      (mul_le_mul_of_nonneg_right hcapRhs_le fp.u_nonneg)
  have hB :
      theorem20_10_householder_gammaB fp r p q ≤ cap * fp.u := by
    exact le_trans hBraw
      (mul_le_mul_of_nonneg_right hcapB_le fp.u_nonneg)
  have hAcons :
      theorem20_10_householder_gammaA_conservativeRhs fp r p q ≤
        cap * fp.u := by
    dsimp [theorem20_10_householder_gammaA_conservativeRhs]
    exact max_le hA hRhs
  exact max_le hAcons hB

end NumStability
