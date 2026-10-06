/-
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
§8.2 "Forward Error Analysis", Lemma 8.8 (p. 144).

  Lemma 8.8.  If the upper triangular matrix `U ∈ ℝⁿˣⁿ` is row diagonally
  dominant then `(|U⁻¹||U|)_{ij} ≤ i + j − 1` and `cond(U) ≤ 2n − 1`.

This file closes the **entrywise** half `(|U⁻¹||U|)_{ij} ≤ i + j − 1`, which
previously had no Lean surface (only the `cond(U) ≤ 2n − 1` half was formalized,
as `higham8_8_rowDiagDominantUpper_condSkeel_bound`).  The proof follows the
book: normalize `U = D V` with `V = diag(U)⁻¹ U` unit upper triangular, whose
entries and inverse entries are bounded by `1` (row diagonal dominance), then
`(|U⁻¹||U|)_{ij} = (|V⁻¹||V|)_{ij}` is a sum of products of factors `≤ 1`
supported on `i ≤ k ≤ j`.

Indexing note: the printed statement is 1-indexed, `(|U⁻¹||U|)_{ij} ≤ i+j−1`.
The repository indexes matrices by `Fin n` (0-based `i.val`), so the 1-indexed
`i+j−1` becomes `(i.val + 1) + (j.val + 1) − 1 = i.val + j.val + 1`.

IMPORT-ONLY: reuses `higham8_8_rowDiagDominantUpper`,
`higham8_8_rowDiagDominantUpper_condSkeel_bound` (HighamChapter8), and the
triangular-inverse machinery (`inv_upper_tri`, `inv_diag_entry`,
`unitUpperTri_inv_entry_le_one_of_row_sum_le_one`, TriangularForwardBound).
-/
import NumStability.Algorithms.HighamChapter8

namespace NumStability

open scoped BigOperators

/-- The comparison-product entry `(|U⁻¹||U|)_{ij} = ∑_k |U⁻¹_{ik}| |U_{kj}|`. -/
noncomputable def lemma88_comparisonProductEntry (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ k : Fin n, |U_inv i k| * |U k j|

/-- **Lemma 8.8, entrywise half (sharp count form).**

For a row-diagonally-dominant upper-triangular `U` with inverse `U_inv`, the
comparison-product entry is bounded by the number of indices `k` with
`i ≤ k ≤ j`, i.e. `(|U⁻¹||U|)_{ij} ≤ (j − i + 1)` (as a natural-number count
`j.val + 1 − i.val`, which is `0` when `i > j`).  This is the strongest honest
form: each surviving term `|V⁻¹_{ik}||V_{kj}|` is a product of two factors
bounded by `1`, and the support is exactly `i ≤ k ≤ j`. -/
theorem lemma88_comparisonProductEntry_card_le (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (hRD : higham8_8_rowDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    ∀ i j : Fin n,
      lemma88_comparisonProductEntry n U U_inv i j ≤
        ((j.val + 1 - i.val : ℕ) : ℝ) := by
  rcases hRD with ⟨hUT, hDiag, hRow⟩
  rcases hInv with ⟨hLInv, hRInv⟩
  have hInv_ut := inv_upper_tri n U U_inv hUT hDiag hLInv
  -- Normalization  V = diag(U)⁻¹ U,  V_inv = U_inv diag(U).
  set V : Fin n → Fin n → ℝ := fun a b => U a b / U a a with hVdef
  set V_inv : Fin n → Fin n → ℝ := fun a b => U_inv a b * U b b with hVinvdef
  have hVT : ∀ a b : Fin n, b.val < a.val → V a b = 0 := by
    intro a b hab; simp [hVdef, hUT a b hab]
  have hV_unit : ∀ a : Fin n, V a a = 1 := by
    intro a; simp [hVdef, hDiag a]
  have hV_row : ∀ a : Fin n,
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |V a j| ≤ 1 := by
    intro a
    calc
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |V a j|
          = (1 / |U a a|) *
              ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |U a j| := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _; simp [hVdef, div_eq_mul_inv, mul_comm]
      _ ≤ (1 / |U a a|) * |U a a| :=
            mul_le_mul_of_nonneg_left (hRow a) (one_div_nonneg.mpr (abs_nonneg _))
      _ = 1 := by
            rw [one_div, inv_mul_cancel₀]; exact abs_ne_zero.mpr (hDiag a)
  have hVinv_ut : ∀ a b : Fin n, b.val < a.val → V_inv a b = 0 := by
    intro a b hab; simp [hVinvdef, hInv_ut a b hab]
  have hVinv_diag : ∀ a : Fin n, V_inv a a = 1 := by
    intro a
    simp [hVinvdef, inv_diag_entry n U U_inv hUT hDiag hLInv hInv_ut a, hDiag a]
  have hVRInv : IsRightInverse n V V_inv := by
    intro a b
    simp only [hVdef, hVinvdef]
    have hsimp :
        ∑ k : Fin n, (U a k / U a a) * (U_inv k b * U b b) =
          (U b b / U a a) * ∑ k : Fin n, U a k * U_inv k b := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl
      intro k _; field_simp [hDiag a]
    rw [hsimp, hRInv a b]
    by_cases hab : a = b
    · subst hab; simp [hDiag a]
    · simp [hab]
  -- Individual entries of V are ≤ 1 in magnitude.
  have hV_entry_le_one : ∀ a b : Fin n, |V a b| ≤ 1 := by
    intro a b
    rcases lt_trichotomy b.val a.val with hlt | heq | hgt
    · rw [hVT a b hlt, abs_zero]; norm_num
    · have hab : a = b := Fin.ext heq.symm
      subst hab; rw [hV_unit, abs_one]
    · -- a.val < b.val:  |V a b| = |U a b| / |U a a| ≤ 1.
      have hmem : b ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩
      have hsingle :
          |U a b| ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => a.val < j.val), |U a j| :=
        Finset.single_le_sum (f := fun j => |U a j|)
          (fun j _ => abs_nonneg _) hmem
      have hbound : |U a b| ≤ |U a a| := le_trans hsingle (hRow a)
      have hpos : 0 < |U a a| := abs_pos.mpr (hDiag a)
      have : |V a b| = |U a b| / |U a a| := by rw [hVdef]; simp [abs_div]
      rw [this]
      rw [div_le_one hpos]; exact hbound
  -- Inverse entries of V are ≤ 1 in magnitude (reused book lemma).
  have hVinv_le_one :=
    unitUpperTri_inv_entry_le_one_of_row_sum_le_one
      n V V_inv hVT hV_unit hV_row hVRInv hVinv_ut hVinv_diag
  -- Fix a row / column and bound the entry.
  intro i j
  have hVinv_all : ∀ k : Fin n, |V_inv i k| ≤ 1 := by
    intro k
    rcases Nat.lt_or_ge k.val i.val with hki | hik
    · rw [hVinv_ut i k hki, abs_zero]; norm_num
    · exact hVinv_le_one i k hik
  -- Term-by-term reduction  |U⁻¹_{ik}||U_{kj}| = |V⁻¹_{ik}||V_{kj}|.
  have hterm : ∀ k : Fin n, |U_inv i k| * |U k j| = |V_inv i k| * |V k j| := by
    intro k
    have hkk : |U k k| ≠ 0 := abs_ne_zero.mpr (hDiag k)
    have hVe : |V k j| = |U k j| / |U k k| := by rw [hVdef]; simp [abs_div]
    have hVie : |V_inv i k| = |U_inv i k| * |U k k| := by rw [hVinvdef]; rw [abs_mul]
    rw [hVe, hVie]; field_simp
  -- Nonneg, per-term ≤ 1, and support ⊆ {k : i ≤ k ≤ j}.
  set g : Fin n → ℝ := fun k => |V_inv i k| * |V k j| with hgdef
  have hg_nonneg : ∀ k, 0 ≤ g k := fun k => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hg_le_one : ∀ k, g k ≤ 1 := by
    intro k
    have := mul_le_mul (hVinv_all k) (hV_entry_le_one k j)
      (abs_nonneg _) (le_trans (abs_nonneg _) (hVinv_all k))
    simpa [hgdef] using this
  have hg_zero_out : ∀ k ∈ Finset.univ,
      k ∉ Finset.Icc i j → g k = 0 := by
    intro k _ hk
    rw [Finset.mem_Icc, not_and_or] at hk
    rcases hk with hlo | hhi
    · -- ¬ i ≤ k  ⇒  k < i  ⇒  V_inv i k = 0
      have hki : k.val < i.val := Fin.lt_def.mp (not_le.mp hlo)
      simp [hgdef, hVinv_ut i k hki]
    · -- ¬ k ≤ j  ⇒  j < k  ⇒  V k j = 0
      have hjk : j.val < k.val := Fin.lt_def.mp (not_le.mp hhi)
      simp [hgdef, hVT k j hjk]
  calc
    lemma88_comparisonProductEntry n U U_inv i j
        = ∑ k : Fin n, g k := by
          unfold lemma88_comparisonProductEntry
          exact Finset.sum_congr rfl (fun k _ => hterm k)
    _ = ∑ k ∈ Finset.Icc i j, g k := by
          symm
          exact Finset.sum_subset (Finset.subset_univ _) hg_zero_out
    _ ≤ ∑ _k ∈ Finset.Icc i j, (1 : ℝ) :=
          Finset.sum_le_sum (fun k _ => hg_le_one k)
    _ = ((Finset.Icc i j).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ((j.val + 1 - i.val : ℕ) : ℝ) := by rw [Fin.card_Icc]

/-- **Lemma 8.8, entrywise half (printed strength).**

`(|U⁻¹||U|)_{ij} ≤ i + j − 1` in the book's 1-indexed convention, i.e.
`≤ i.val + j.val + 1` in the repository's 0-based `Fin n` indexing.  Follows
from the sharp count bound `j.val + 1 − i.val ≤ i.val + j.val + 1`. -/
theorem lemma88_comparisonProductEntry_le (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (hRD : higham8_8_rowDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    ∀ i j : Fin n,
      lemma88_comparisonProductEntry n U U_inv i j ≤
        ((i.val : ℝ) + (j.val : ℝ) + 1) := by
  intro i j
  have hsharp := lemma88_comparisonProductEntry_card_le n U U_inv hRD hInv i j
  refine le_trans hsharp ?_
  have hnat : (j.val + 1 - i.val : ℕ) ≤ i.val + j.val + 1 := by omega
  calc
    ((j.val + 1 - i.val : ℕ) : ℝ) ≤ ((i.val + j.val + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = (i.val : ℝ) + (j.val : ℝ) + 1 := by push_cast; ring

/-- **Lemma 8.8 (complete, source-facing).**

For a row-diagonally-dominant upper-triangular `U`:
* entrywise, `(|U⁻¹||U|)_{ij} ≤ i + j − 1`  (printed 1-indexing; here
  `i.val + j.val + 1`), and
* `cond(U) = ‖ |U⁻¹||U| ‖∞ ≤ 2n − 1`.

The entrywise half is `lemma88_comparisonProductEntry_le` above; the condition
number half is the previously-formalized
`higham8_8_rowDiagDominantUpper_condSkeel_bound`. -/
theorem lemma88_rowDiagDominantUpper (n : ℕ) (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (hRD : higham8_8_rowDiagDominantUpper n U)
    (hInv : IsInverse n U U_inv) :
    (∀ i j : Fin n,
        lemma88_comparisonProductEntry n U U_inv i j ≤
          ((i.val : ℝ) + (j.val : ℝ) + 1)) ∧
      condSkeel n hn U U_inv ≤ 2 * (n : ℝ) - 1 :=
  ⟨lemma88_comparisonProductEntry_le n U U_inv hRD hInv,
    higham8_8_rowDiagDominantUpper_condSkeel_bound n hn U U_inv hRD hInv⟩

end NumStability
