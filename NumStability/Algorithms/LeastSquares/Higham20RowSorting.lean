import NumStability.Algorithms.LeastSquares.Higham20EliminationActual

namespace NumStability

open scoped BigOperators

namespace Higham20RowSorting

/-!
# Higham, p. 395: executable row sorting and the Cox--Higham cap

This file implements the row policy printed after Theorem 20.7: sort the
source rows by decreasing infinity norm, then run the exact active-max column
pivoted, signed-Householder trace.  The growth proof is the argument of
Cox--Higham Lemma 4.2: an off-pivot row grows by at most `1 + sqrt 2` per
stage, while its one pivot-row update contributes the single `sqrt m` factor.
-/

/-- The actual row permutation: decreasing source row infinity norm, with the
deterministic tie-breaking supplied by `Tuple.sort`. -/
noncomputable def rowSortPerm {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) : Fin m ≃ Fin m :=
  Tuple.sort (fun i : Fin m => -theorem20_7_initialRowMax hn A i)

/-- Matrix obtained by the executable simultaneous row reordering. -/
noncomputable def rowSortedMatrix {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => A (rowSortPerm hn A i) j

/-- Right-hand side obtained by the same row reordering. -/
noncomputable def rowSortedRhs {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : Fin m → ℝ :=
  fun i => b (rowSortPerm hn A i)

theorem rowSortPerm_descending {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) {i r : Fin m} (hir : i.val ≤ r.val) :
    theorem20_7_initialRowMax hn A (rowSortPerm hn A r) ≤
      theorem20_7_initialRowMax hn A (rowSortPerm hn A i) := by
  have hmono :=
    (Tuple.monotone_sort
      (fun q : Fin m => -theorem20_7_initialRowMax hn A q)) hir
  exact neg_le_neg_iff.mp hmono

theorem rowSortedMatrix_rowMax {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i =
      theorem20_7_initialRowMax hn A (rowSortPerm hn A i) := by
  exact theorem20_7_initialRowMax_permuteRows hn A (rowSortPerm hn A) i

theorem rowSortedMatrix_descending {m n : ℕ} (hn : 0 < n)
    (A : Fin m → Fin n → ℝ) {i r : Fin m} (hir : i.val ≤ r.val) :
    theorem20_7_initialRowMax hn (rowSortedMatrix hn A) r ≤
      theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i := by
  rw [rowSortedMatrix_rowMax, rowSortedMatrix_rowMax]
  exact rowSortPerm_descending hn A hir

/-- Exact active-max signed-Householder trace run on the sorted matrix. -/
noncomputable def exactASeq {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : ℕ → Fin m → Fin n → ℝ :=
  Higham20EliminationActual.exactPivotedQRMatrixSeq hmn (le_refl n)
    (rowSortedMatrix hn A)

noncomputable def exactPSeq {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : ℕ → Fin m → Fin m → ℝ :=
  Higham20EliminationActual.exactPivotedQRPseq hmn (le_refl n)
    (rowSortedMatrix hn A)

noncomputable def exactSwappedPanel {m n : ℕ} (hn : 0 < n)
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Fin m → Fin n → ℝ :=
  Higham20EliminationActual.exactPivotedQRSwappedPanel hmn (le_refl n)
    (rowSortedMatrix hn A) k

theorem exactASeq_zero {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : exactASeq hn hmn A 0 = rowSortedMatrix hn A :=
  rfl

theorem exactASeq_succ {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n) :
    exactASeq hn hmn A (k + 1) =
      matMulRect m m n (exactPSeq hn hmn A k)
        (exactSwappedPanel hn hmn A k) := by
  exact Higham20EliminationActual.exactPivotedQRMatrixSeq_succ_of_lt
    hmn (le_refl n) (rowSortedMatrix hn A) k hk

theorem exactSwappedPanel_pivot_max {m n : ℕ} (hn : 0 < n)
    (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) :
    ∀ l : Fin n, k ≤ l.val →
      householderTrailingColumnNorm2Sq
          ⟨k, lt_of_lt_of_le hk hmn⟩ (exactSwappedPanel hn hmn A k) l ≤
        householderTrailingColumnNorm2Sq
          ⟨k, lt_of_lt_of_le hk hmn⟩ (exactSwappedPanel hn hmn A k)
          ⟨k, hk⟩ := by
  exact Higham20EliminationActual.exactPivotedQRSwappedPanel_pivot_max
    hmn (le_refl n) (rowSortedMatrix hn A) k hk

theorem exactSwappedPanel_active_entry_bound {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (r : Fin m) (hr : k ≤ r.val)
    (j : Fin n) (hj : k ≤ j.val) {B : ℝ}
    (hbound : ∀ q : Fin n, k ≤ q.val → |exactASeq hn hmn A k r q| ≤ B) :
    |exactSwappedPanel hn hmn A k r j| ≤ B := by
  let S := Higham20EliminationActual.exactPivotedQRSwapSeq
    hmn (le_refl n) (rowSortedMatrix hn A) k
  have hactive : k ≤ (S j).val :=
    Higham20EliminationActual.exactPivotedQRSwapSeq_maps_active
      hmn (le_refl n) (rowSortedMatrix hn A) k j hj
  simpa [exactSwappedPanel,
    Higham20EliminationActual.exactPivotedQRSwappedPanel,
    Wave13.columnPermuteMatrix, S, exactASeq] using hbound (S j) hactive

/-- One genuine off-pivot Cox--Higham stage.  This is derived from the
executed active-max column exchange and the signed Householder multiplier
bound, rather than postulated as a growth premise. -/
theorem exactASeq_offPivot_step {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (r : Fin m) (hr : k < r.val)
    (j : Fin n) (hj : k ≤ j.val) {B : ℝ}
    (hbound : ∀ q : Fin n, k ≤ q.val → |exactASeq hn hmn A k r q| ≤ B) :
    |exactASeq hn hmn A (k + 1) r j| ≤ (1 + Real.sqrt 2) * B := by
  let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
  let q : Fin n := ⟨k, hk⟩
  let As := exactSwappedPanel hn hmn A k
  let x : Fin m → ℝ := fun i => As i q
  let alpha := signedHouseholderAlpha
    (Real.sqrt (householderTrailingNorm2Sq m p x)) (x p)
  let v := householderTrailingActiveVector m p x alpha
  let beta := householderBetaSpec m v
  have hP : exactPSeq hn hmn A k = householder m v beta := by
    simp [exactPSeq, Higham20EliminationActual.exactPivotedQRPseq,
      Higham20EliminationActual.exactPivotedQRRawVector,
      Higham20EliminationActual.exactPivotedQRBeta,
      exactSwappedPanel, As, x, p, q, alpha, v, beta, hk]
  have hvr : v r = As r q := by
    have hnot : ¬ r.val < k := not_lt.mpr (le_of_lt hr)
    have hrp : r ≠ p := by
      intro h
      have : r.val = k := by simpa [p] using congrArg Fin.val h
      omega
    simp [v, x, p, q, householderTrailingActiveVector,
      householderActiveVector, householderTrailingPart, hnot, hrp]
  have hinner :
      (∑ i : Fin m, v i * As i j) =
        ∑ i : Fin m, v i * householderTrailingPart m p (fun a => As a j) i := by
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : i.val < k
    · have hvzero : v i = 0 := by
        simpa [v, p] using
          householderTrailingActiveVector_zero_prefix m p x alpha i
            (by simpa [p] using hi)
      simp [hvzero]
    · simp [householderTrailingPart, p, hi]
  have hcoeff : |beta * (∑ i : Fin m, v i * As i j)| ≤ Real.sqrt 2 := by
    rw [hinner]
    simpa [beta, v, alpha, x, q,
      householderTrailingColumnNorm2Sq] using
      (abs_householderBeta_mul_inner_column_le_sqrt_two_of_signed_pivot_max
        p q j As (exactSwappedPanel_pivot_max hn hmn A k hk) hj)
  have hAsj : |As r j| ≤ B := by
    exact exactSwappedPanel_active_entry_bound hn hmn A k hk r
      (le_of_lt hr) j hj hbound
  have hAsq : |As r q| ≤ B := by
    exact exactSwappedPanel_active_entry_bound hn hmn A k hk r
      (le_of_lt hr) q (le_refl k) hbound
  rw [exactASeq_succ hn hmn A k hk]
  change |matMulVec m (exactPSeq hn hmn A k) (fun i => As i j) r| ≤ _
  rw [hP, congrFun (householder_matMulVec_eq m v beta (fun i => As i j)) r,
    hvr]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    abs_sub_mul_le_one_add_sqrt_two_mul_bound hAsj hAsq hcoeff

/-- Active rows of the actual sorted trace grow geometrically by the
Cox--Higham off-pivot factor. -/
theorem exactASeq_active_bound {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ) :
    ∀ k : ℕ, k < n → ∀ r : Fin m, k ≤ r.val →
      ∀ j : Fin n, k ≤ j.val →
        |exactASeq hn hmn A k r j| ≤
          (1 + Real.sqrt 2) ^ k *
            theorem20_7_initialRowMax hn (rowSortedMatrix hn A) r := by
  intro k
  induction k with
  | zero =>
      intro _hk r _hr j _hj
      simpa [exactASeq_zero] using
        theorem20_7_initialRowMax_entry_le hn (rowSortedMatrix hn A) r j
  | succ k ih =>
      intro hk r hr j hj
      have hkn : k < n := lt_trans (Nat.lt_succ_self k) hk
      have hkr : k < r.val := Nat.lt_of_succ_le hr
      have hkj : k ≤ j.val := le_trans (Nat.le_succ k) hj
      have hstep := exactASeq_offPivot_step hn hmn A k hkn r hkr j hkj
        (B := (1 + Real.sqrt 2) ^ k *
          theorem20_7_initialRowMax hn (rowSortedMatrix hn A) r)
        (fun q hq => ih hkn r (le_of_lt hkr) q hq)
      calc
        |exactASeq hn hmn A (k + 1) r j| ≤
            (1 + Real.sqrt 2) *
              ((1 + Real.sqrt 2) ^ k *
                theorem20_7_initialRowMax hn (rowSortedMatrix hn A) r) := hstep
        _ = (1 + Real.sqrt 2) ^ (k + 1) *
              theorem20_7_initialRowMax hn (rowSortedMatrix hn A) r := by
            rw [pow_succ]
            ring

/-- The one pivot-row update of the actual trace contributes the single
ambient `sqrt m` factor. -/
theorem exactASeq_pivotRow_bound {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (j : Fin n) (hj : k ≤ j.val) :
    |exactASeq hn hmn A (k + 1) ⟨k, lt_of_lt_of_le hk hmn⟩ j| ≤
      Real.sqrt (m : ℝ) *
        ((1 + Real.sqrt 2) ^ k *
          theorem20_7_initialRowMax hn (rowSortedMatrix hn A)
            ⟨k, lt_of_lt_of_le hk hmn⟩) := by
  let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
  let As := exactSwappedPanel hn hmn A k
  let raw := Higham20EliminationActual.exactPivotedQRRawVector
    hmn (le_refl n) (rowSortedMatrix hn A) k
  let beta := Higham20EliminationActual.exactPivotedQRBeta
    hmn (le_refl n) (rowSortedMatrix hn A) k
  let B := (1 + Real.sqrt 2) ^ k *
    theorem20_7_initialRowMax hn (rowSortedMatrix hn A) p
  have hB : 0 ≤ B := by
    exact mul_nonneg (pow_nonneg coxHighamGrowthFactor_nonneg k)
      (theorem20_7_initialRowMax_nonneg hn (rowSortedMatrix hn A) p)
  have hprefix : ∀ i : Fin m, i.val < p.val → raw i = 0 := by
    intro i hi
    exact Higham20EliminationActual.exactPivotedQRRawVector_zero_prefix
      hmn (le_refl n) (rowSortedMatrix hn A) k hk i (by simpa [p] using hi)
  have horth : IsOrthogonal m (householder m raw beta) := by
    simpa [raw, beta, exactPSeq,
      Higham20EliminationActual.exactPivotedQRPseq] using
      (Higham20EliminationActual.exactPivotedQRPseq_orthogonal
        hmn (le_refl n) (rowSortedMatrix hn A) k)
  have hcoord :
      |matMulVec m (householder m raw beta) (fun i => As i j) p| ≤
        vecNorm2 (householderTrailingPart m p (fun i => As i j)) :=
    abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal
      m p raw beta (fun i => As i j) hprefix horth
  have htailEntry : ∀ i : Fin m,
      |householderTrailingPart m p (fun r => As r j) i| ≤ B := by
    intro i
    by_cases hi : i.val < k
    · simpa [householderTrailingPart, p, hi] using hB
    · have hki : k ≤ i.val := Nat.le_of_not_gt hi
      have hrowSort :
          theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i ≤
            theorem20_7_initialRowMax hn (rowSortedMatrix hn A) p := by
        exact rowSortedMatrix_descending hn A (by simpa [p] using hki)
      have hpow : 0 ≤ (1 + Real.sqrt 2 : ℝ) ^ k :=
        pow_nonneg coxHighamGrowthFactor_nonneg k
      have hAs : |As i j| ≤ B := by
        have hlocal := exactSwappedPanel_active_entry_bound hn hmn A k hk i hki j hj
          (B := (1 + Real.sqrt 2) ^ k *
            theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i)
          (fun q hq => exactASeq_active_bound hn hmn A k hk i hki q hq)
        exact hlocal.trans
          (mul_le_mul_of_nonneg_left hrowSort hpow)
      simpa [householderTrailingPart, p, hi] using hAs
  have htail :
      vecNorm2 (householderTrailingPart m p (fun i => As i j)) ≤
        Real.sqrt (m : ℝ) * B :=
    vecNorm2_le_sqrt_card_mul_of_abs_le
      (householderTrailingPart m p (fun i => As i j)) hB htailEntry
  rw [exactASeq_succ hn hmn A k hk]
  change |matMulVec m (exactPSeq hn hmn A k) (fun i => As i j) p| ≤ _
  have hPeq : exactPSeq hn hmn A k = householder m raw beta := by
    rfl
  rw [hPeq]
  exact hcoord.trans htail

/-- A completed row is unchanged by later left reflectors; the executed
column exchange can only relabel entries, so a uniform completed-row bound is
preserved. -/
theorem exactASeq_completedRow_step {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (r : Fin m) (hr : r.val < k)
    {B : ℝ} (hbound : ∀ q : Fin n, |exactASeq hn hmn A k r q| ≤ B)
    (j : Fin n) : |exactASeq hn hmn A (k + 1) r j| ≤ B := by
  let S := Higham20EliminationActual.exactPivotedQRSwapSeq
    hmn (le_refl n) (rowSortedMatrix hn A) k
  let raw := Higham20EliminationActual.exactPivotedQRRawVector
    hmn (le_refl n) (rowSortedMatrix hn A) k
  let beta := Higham20EliminationActual.exactPivotedQRBeta
    hmn (le_refl n) (rowSortedMatrix hn A) k
  let As := exactSwappedPanel hn hmn A k
  have hprefix : ∀ i : Fin m, i.val < k → raw i = 0 := by
    intro i hi
    exact Higham20EliminationActual.exactPivotedQRRawVector_zero_prefix
      hmn (le_refl n) (rowSortedMatrix hn A) k hk i hi
  have hpres :
      matMulVec m (householder m raw beta) (fun i => As i j) r = As r j :=
    matMulVec_householder_eq_self_of_zero_prefix
      m k raw (fun i => As i j) beta hprefix r hr
  have hAs : |As r j| ≤ B := by
    simpa [As, exactSwappedPanel,
      Higham20EliminationActual.exactPivotedQRSwappedPanel,
      Wave13.columnPermuteMatrix, S, exactASeq] using hbound (S j)
  rw [exactASeq_succ hn hmn A k hk]
  change |matMulVec m (exactPSeq hn hmn A k) (fun i => As i j) r| ≤ B
  have hPeq : exactPSeq hn hmn A k = householder m raw beta := by rfl
  rw [hPeq, hpres]
  exact hAs

/-- At its completion stage, a row satisfies the source's single-`sqrt m`
bound in every displayed column (earlier columns are already zero). -/
theorem exactASeq_pivotCompletion_allCols {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (j : Fin n) :
    |exactASeq hn hmn A (k + 1) ⟨k, lt_of_lt_of_le hk hmn⟩ j| ≤
      Real.sqrt (m : ℝ) *
        ((1 + Real.sqrt 2) ^ k *
          theorem20_7_initialRowMax hn (rowSortedMatrix hn A)
            ⟨k, lt_of_lt_of_le hk hmn⟩) := by
  by_cases hj : j.val < k
  · have hzero :
        exactASeq hn hmn A (k + 1) ⟨k, lt_of_lt_of_le hk hmn⟩ j = 0 := by
      exact Higham20EliminationActual.exactPivotedQRMatrixSeq_prefix_lower_zero
        hmn (le_refl n) (rowSortedMatrix hn A) (k + 1)
        (Nat.succ_le_iff.mpr hk) ⟨k, lt_of_lt_of_le hk hmn⟩ j
        (lt_trans hj (Nat.lt_succ_self k)) hj
    rw [hzero, abs_zero]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (pow_nonneg coxHighamGrowthFactor_nonneg k)
        (theorem20_7_initialRowMax_nonneg hn (rowSortedMatrix hn A)
          ⟨k, lt_of_lt_of_le hk hmn⟩))
  · exact exactASeq_pivotRow_bound hn hmn A k hk j (Nat.le_of_not_gt hj)

/-- Once row `k` has been completed, its source bound persists through every
later executed stage. -/
theorem exactASeq_completedRow_bound {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) :
    ∀ t : ℕ, k + 1 ≤ t → t ≤ n → ∀ j : Fin n,
      |exactASeq hn hmn A t ⟨k, lt_of_lt_of_le hk hmn⟩ j| ≤
        Real.sqrt (m : ℝ) *
          ((1 + Real.sqrt 2) ^ k *
            theorem20_7_initialRowMax hn (rowSortedMatrix hn A)
              ⟨k, lt_of_lt_of_le hk hmn⟩) := by
  let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
  let C := Real.sqrt (m : ℝ) *
    ((1 + Real.sqrt 2) ^ k *
      theorem20_7_initialRowMax hn (rowSortedMatrix hn A) p)
  intro t hkt htn
  induction t, hkt using Nat.le_induction with
  | base =>
      intro j
      simpa [p, C] using exactASeq_pivotCompletion_allCols hn hmn A k hk j
  | succ t hbase ih =>
      intro j
      have htlt : t < n := lt_of_lt_of_le (Nat.lt_succ_self t) htn
      have hpk : p.val < t := by simpa [p] using hbase
      exact exactASeq_completedRow_step hn hmn A t htlt p hpk
        (B := C) (fun q => ih (Nat.le_of_lt htlt) q) j

/-- Every recorded entry of the actual exact sorted trace satisfies the
single source envelope.  Active rows use the geometric off-pivot estimate;
once a row becomes the pivot row, its one `sqrt m` completion estimate is
preserved by every later reflector. -/
theorem exactASeq_uniform_printed_bound {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (t : ℕ) (ht : t ≤ n) (i : Fin m) (j : Fin n) :
    |exactASeq hn hmn A t i j| ≤
      Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1) *
        theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i := by
  have hmpos : 0 < m := lt_of_lt_of_le hn hmn
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
  have hsqrtm : (1 : ℝ) ≤ Real.sqrt m := by
    have h := Real.sqrt_le_sqrt hmR
    simpa using h
  have hbase : (1 : ℝ) ≤ 1 + Real.sqrt 2 := by
    linarith [Real.sqrt_nonneg (2 : ℝ)]
  by_cases hit : i.val < t
  · have hin : i.val < n := lt_of_lt_of_le hit ht
    have hdone := exactASeq_completedRow_bound hn hmn A i.val hin t
      (Nat.succ_le_iff.mpr hit) ht j
    have hpow : (1 + Real.sqrt 2 : ℝ) ^ i.val ≤
        (1 + Real.sqrt 2) ^ (n - 1) := by
      exact pow_le_pow_right₀ hbase (by omega)
    have hrow : 0 ≤ theorem20_7_initialRowMax hn
        (rowSortedMatrix hn A) i :=
      theorem20_7_initialRowMax_nonneg hn (rowSortedMatrix hn A) i
    calc
      |exactASeq hn hmn A t i j| ≤
          Real.sqrt (m : ℝ) *
            ((1 + Real.sqrt 2) ^ i.val *
              theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i) := by
        simpa using hdone
      _ ≤ Real.sqrt (m : ℝ) *
            ((1 + Real.sqrt 2) ^ (n - 1) *
              theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow hrow) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · have hti : t ≤ i.val := Nat.le_of_not_gt hit
    by_cases hjt : j.val < t
    · have hzero : exactASeq hn hmn A t i j = 0 := by
        exact Higham20EliminationActual.exactPivotedQRMatrixSeq_prefix_lower_zero
          hmn (le_refl n) (rowSortedMatrix hn A) t ht i j
          hjt (lt_of_lt_of_le hjt hti)
      rw [hzero, abs_zero]
      exact mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _)
          (pow_nonneg coxHighamGrowthFactor_nonneg _))
        (theorem20_7_initialRowMax_nonneg hn (rowSortedMatrix hn A) i)
    · have htj : t ≤ j.val := Nat.le_of_not_gt hjt
      have htn : t < n := lt_of_le_of_lt htj j.isLt
      have hactive := exactASeq_active_bound hn hmn A t htn i hti j htj
      have hpow : (1 + Real.sqrt 2 : ℝ) ^ t ≤
          (1 + Real.sqrt 2) ^ (n - 1) := by
        exact pow_le_pow_right₀ hbase (by omega)
      have hrow : 0 ≤ theorem20_7_initialRowMax hn
          (rowSortedMatrix hn A) i :=
        theorem20_7_initialRowMax_nonneg hn (rowSortedMatrix hn A) i
      have hpowrow :
          (1 + Real.sqrt 2 : ℝ) ^ t *
              theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i ≤
            (1 + Real.sqrt 2) ^ (n - 1) *
              theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i :=
        mul_le_mul_of_nonneg_right hpow hrow
      calc
        |exactASeq hn hmn A t i j| ≤
            (1 + Real.sqrt 2) ^ t *
              theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i := hactive
        _ ≤ (1 + Real.sqrt 2) ^ (n - 1) *
              theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i := hpowrow
        _ = 1 * ((1 + Real.sqrt 2) ^ (n - 1) *
              theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i) := by ring
        _ ≤ Real.sqrt (m : ℝ) *
              ((1 + Real.sqrt 2) ^ (n - 1) *
                theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i) := by
          exact mul_le_mul_of_nonneg_right hsqrtm
            (mul_nonneg (pow_nonneg coxHighamGrowthFactor_nonneg _)
              hrow)
        _ = _ := by ring

/-! ## Literal printed matrix growth scale -/

/-- The numerator `max_{j,k} |aᵢⱼ^(k)|` of the printed `alpha_i`, taken over
all `n+1` states actually recorded by the executable exact trace. -/
noncomputable def exactPrintedAlphaScale {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (i : Fin m) : ℝ :=
  Wave18D.rowInftyGrowthFactor (exactASeq hn hmn A) n i

/-- The literal dimensionless matrix row-growth ratio after applying the
source's decreasing-row-norm policy. -/
noncomputable def exactPrintedAlpha {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (i : Fin m) : ℝ :=
  exactPrintedAlphaScale hn hmn A i /
    theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i

theorem exactPrintedAlphaScale_le_cap_mul_rowMax {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (i : Fin m) :
    exactPrintedAlphaScale hn hmn A i ≤
      (Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1)) *
        theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold exactPrintedAlphaScale Wave18D.rowInftyGrowthFactor
  refine ciSup_le fun t => ?_
  unfold Wave18D.rowInftyNorm
  refine ciSup_le fun j => ?_
  simpa [mul_assoc] using
    exactASeq_uniform_printed_bound hn hmn A t.val
      (Nat.le_of_lt_succ t.isLt) i j

/-- The literal matrix growth numerator is nonnegative. -/
theorem exactPrintedAlphaScale_nonneg {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (i : Fin m) : 0 ≤ exactPrintedAlphaScale hn hmn A i := by
  exact Wave18D.rowInftyGrowthFactor_nonneg
    (exactASeq hn hmn A) n i ⟨0, hn⟩

/-- Cox--Higham's printed matrix ratio obeys the advertised cap for the
actual sorted exact trace.  A zero source row needs no artificial side
condition: the scale bound forces its numerator to vanish. -/
theorem exactPrintedAlpha_le_cap {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (i : Fin m) :
    exactPrintedAlpha hn hmn A i ≤
      Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1) := by
  let C := Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1)
  let rowMax := theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i
  have hC : 0 ≤ C :=
    mul_nonneg (Real.sqrt_nonneg _)
      (pow_nonneg coxHighamGrowthFactor_nonneg _)
  have hscale := exactPrintedAlphaScale_le_cap_mul_rowMax hn hmn A i
  by_cases hrow0 : rowMax = 0
  · have hscale0 : exactPrintedAlphaScale hn hmn A i = 0 := by
      apply le_antisymm
      · simpa [C, rowMax, hrow0] using hscale
      · exact exactPrintedAlphaScale_nonneg hn hmn A i
    simp [exactPrintedAlpha, rowMax, hrow0, hscale0, C, hC]
  · have hrowpos : 0 < rowMax := lt_of_le_of_ne
        (theorem20_7_initialRowMax_nonneg hn (rowSortedMatrix hn A) i)
        (Ne.symm hrow0)
    rw [exactPrintedAlpha, div_le_iff₀ (by simpa [rowMax] using hrowpos)]
    simpa [C, rowMax, mul_assoc] using hscale

/-! ## Paired exact right-hand-side trace and printed `phi` -/

/-- The right-hand side transformed by exactly the same executed reflectors
as `exactASeq`.  Column exchanges act only on the matrix. -/
noncomputable def exactBSeq {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) : ℕ → Fin m → ℝ
  | 0 => rowSortedRhs hn A b
  | k + 1 =>
      if _hk : k < n then
        matMulVec m (exactPSeq hn hmn A k) (exactBSeq hn hmn A b k)
      else
        exactBSeq hn hmn A b k

@[simp] theorem exactBSeq_zero {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) :
    exactBSeq hn hmn A b 0 = rowSortedRhs hn A b := rfl

theorem exactBSeq_succ {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (k : ℕ) (hk : k < n) :
    exactBSeq hn hmn A b (k + 1) =
      matMulVec m (exactPSeq hn hmn A k) (exactBSeq hn hmn A b k) := by
  simp [exactBSeq, hk]

/-- Denominator `‖a_k^(k)(k:m)‖₂` in the printed definition of `phi`,
after the executed active-max column exchange at stage `k`. -/
noncomputable def exactPivotTailNorm {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : ℝ :=
  if hk : k < n then
    vecNorm2
      (householderTrailingPart m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun r => exactSwappedPanel hn hmn A k r ⟨k, hk⟩))
  else 0

/-- Higham's literal
`phi = max_k ‖b^(k)(k:m)‖₂ / ‖a_k^(k)(k:m)‖₂` for the paired
executable exact trace. -/
noncomputable def exactPrintedPhi {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) : ℝ :=
  ⨆ k : Fin n,
    vecNorm2
        (householderTrailingPart m
          ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
          (exactBSeq hn hmn A b k.val)) /
      exactPivotTailNorm hn hmn A k.val

theorem exactPrintedPhi_nonneg {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) : 0 ≤ exactPrintedPhi hn hmn A b := by
  let k0 : Fin n := ⟨0, hn⟩
  have h0 : 0 ≤
      vecNorm2
          (householderTrailingPart m
            ⟨k0.val, lt_of_lt_of_le k0.isLt hmn⟩
            (exactBSeq hn hmn A b k0.val)) /
        exactPivotTailNorm hn hmn A k0.val :=
    div_nonneg (vecNorm2_nonneg _) (by
      simp only [exactPivotTailNorm, dif_pos k0.isLt]
      exact vecNorm2_nonneg _)
  exact h0.trans (le_ciSup
    (Finite.bddAbove_range (fun k : Fin n =>
      vecNorm2
          (householderTrailingPart m
            ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
            (exactBSeq hn hmn A b k.val)) /
        exactPivotTailNorm hn hmn A k.val)) k0)

/-- The defining maximum for `phi` supplies every active-tail comparison at
a nonzero exact pivot. -/
theorem exactBSeq_tail_le_phi_mul_pivotNorm {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (k : ℕ) (hk : k < n)
    (hpivot : 0 < exactPivotTailNorm hn hmn A k) :
    vecNorm2
        (householderTrailingPart m ⟨k, lt_of_lt_of_le hk hmn⟩
          (exactBSeq hn hmn A b k)) ≤
      exactPrintedPhi hn hmn A b * exactPivotTailNorm hn hmn A k := by
  let kf : Fin n := ⟨k, hk⟩
  have hratio :
      vecNorm2
          (householderTrailingPart m ⟨k, lt_of_lt_of_le hk hmn⟩
            (exactBSeq hn hmn A b k)) /
          exactPivotTailNorm hn hmn A k ≤
        exactPrintedPhi hn hmn A b := by
    exact le_ciSup
      (Finite.bddAbove_range (fun q : Fin n =>
        vecNorm2
            (householderTrailingPart m
              ⟨q.val, lt_of_lt_of_le q.isLt hmn⟩
              (exactBSeq hn hmn A b q.val)) /
          exactPivotTailNorm hn hmn A q.val)) kf
  exact (div_le_iff₀ hpivot).mp hratio

/-- Scaled form of the scalar Cox--Higham `sqrt 2` lemma. -/
lemma abs_two_div_mul_le_sqrt_two_mul_of_abs_le_phi_mul_sqrt_mul_sqrt
    {S T inner phi : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hden : 2 * T ≤ S)
    (hphi : 0 ≤ phi)
    (hinner : |inner| ≤ phi * (Real.sqrt S * Real.sqrt T)) :
    |(2 / S) * inner| ≤ Real.sqrt 2 * phi := by
  by_cases hphi0 : phi = 0
  · have hinner0 : inner = 0 := by
      apply abs_eq_zero.mp
      apply le_antisymm
      · simpa [hphi0] using hinner
      · exact abs_nonneg _
    simp [hphi0, hinner0]
  · have hphipos : 0 < phi := lt_of_le_of_ne hphi (Ne.symm hphi0)
    have hscaled : |inner / phi| ≤ Real.sqrt S * Real.sqrt T := by
      rw [abs_div, abs_of_pos hphipos, div_le_iff₀ hphipos]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hinner
    have hcore : |(2 / S) * (inner / phi)| ≤ Real.sqrt 2 :=
      abs_two_div_mul_le_sqrt_two_of_abs_le_sqrt_mul_sqrt
        hS hT hden hscaled
    have hin : inner = phi * (inner / phi) := by
      field_simp [hphi0]
    have hmul : (2 / S) * inner =
        phi * ((2 / S) * (inner / phi)) := by
      calc
        (2 / S) * inner = (2 / S) * (phi * (inner / phi)) :=
          congrArg (fun z : ℝ => (2 / S) * z) hin
        _ = phi * ((2 / S) * (inner / phi)) := by ring
    calc
      |(2 / S) * inner| = phi * |(2 / S) * (inner / phi)| := by
        rw [hmul]
        rw [abs_mul, abs_of_pos hphipos]
      _ ≤ phi * Real.sqrt 2 := mul_le_mul_of_nonneg_left hcore hphi
      _ = Real.sqrt 2 * phi := by ring

/-- A signed Householder update coefficient is at most `sqrt 2 * phi` when
the transformed vector's active tail is at most `phi` times the pivot-column
active norm.  This is the RHS analogue of Cox--Higham Lemma 2.1. -/
theorem abs_householderBeta_mul_inner_trailingPart_le_sqrt_two_mul
    (n : ℕ) (p : Fin n) (x y : Fin n → ℝ) (alpha phi : ℝ)
    (halpha : alpha * alpha = householderTrailingNorm2Sq n p x)
    (hsign : alpha * x p ≤ 0) (hphi : 0 ≤ phi)
    (hy : vecNorm2 (householderTrailingPart n p y) ≤
      phi * Real.sqrt (householderTrailingNorm2Sq n p x)) :
    |householderBetaSpec n (householderTrailingActiveVector n p x alpha) *
        (∑ i : Fin n,
          householderTrailingActiveVector n p x alpha i *
            householderTrailingPart n p y i)| ≤
      Real.sqrt 2 * phi := by
  let v := householderTrailingActiveVector n p x alpha
  let yTail := householderTrailingPart n p y
  let T := householderTrailingNorm2Sq n p x
  let inner := ∑ i : Fin n, v i * yTail i
  let S := ∑ i : Fin n, v i * v i
  have hS_nonneg : 0 ≤ S := by
    simpa [S, vecNorm2Sq, pow_two] using (vecNorm2Sq_nonneg v)
  have hT_nonneg : 0 ≤ T := by
    simpa [T, householderTrailingNorm2Sq] using
      (vecNorm2Sq_nonneg (householderTrailingPart n p x))
  have hden : 2 * T ≤ S := by
    simpa [S, T, v] using
      householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos
        n p x alpha halpha hsign
  have hcs : |inner| ≤ Real.sqrt S * vecNorm2 yTail := by
    simpa [inner, S, v, yTail, vecNorm2, vecNorm2Sq, pow_two] using
      (abs_vecInnerProduct_le_vecNorm2_mul v yTail)
  have hinner : |inner| ≤ phi * (Real.sqrt S * Real.sqrt T) := by
    calc
      |inner| ≤ Real.sqrt S * vecNorm2 yTail := hcs
      _ ≤ Real.sqrt S * (phi * Real.sqrt T) :=
        mul_le_mul_of_nonneg_left (by simpa [T, yTail] using hy)
          (Real.sqrt_nonneg _)
      _ = phi * (Real.sqrt S * Real.sqrt T) := by ring
  simpa [householderBetaSpec, S, inner, v, yTail] using
    abs_two_div_mul_le_sqrt_two_mul_of_abs_le_phi_mul_sqrt_mul_sqrt
      hS_nonneg hT_nonneg hden hphi hinner

/-- A Householder vector with zero prefix preserves the Euclidean norm of
every suffix beginning no later than that prefix. -/
theorem vecNorm2_trailingPart_matMulVec_householder_eq
    (n : ℕ) (p : Fin n) (v y : Fin n → ℝ) (beta : ℝ)
    (hvprefix : ∀ i : Fin n, i.val < p.val → v i = 0)
    (horth : IsOrthogonal n (householder n v beta)) :
    vecNorm2
        (householderTrailingPart n p
          (matMulVec n (householder n v beta) y)) =
      vecNorm2 (householderTrailingPart n p y) := by
  let yPrefix := householderPrefixPart n p y
  let yTail := householderTrailingPart n p y
  let P := householder n v beta
  have hsplit : (fun i : Fin n => yPrefix i + yTail i) = y := by
    simpa [yPrefix, yTail] using householderPrefixPart_add_trailingPart n p y
  have hprefixSupport : ∀ i : Fin n, p.val ≤ i.val → yPrefix i = 0 := by
    simpa [yPrefix] using householderPrefixPart_support n p y
  have hPprefix : matMulVec n P yPrefix = yPrefix := by
    simpa [P] using
      matMulVec_householder_eq_self_of_zero_prefix_support n p.val
        v yPrefix beta hvprefix hprefixSupport
  have hmulSplit : matMulVec n P y =
      fun i => matMulVec n P yPrefix i + matMulVec n P yTail i := by
    rw [← hsplit]
    exact matMulVec_add_right n P yPrefix yTail
  have hPtailPrefix : ∀ i : Fin n, i.val < p.val →
      matMulVec n P yTail i = 0 := by
    intro i hi
    have hvi : v i = 0 := hvprefix i hi
    have hyi : yTail i = 0 := by simp [yTail, householderTrailingPart, hi]
    rw [congrFun (householder_matMulVec_eq n v beta yTail) i]
    simp [hvi, hyi]
  have htailEq :
      householderTrailingPart n p (matMulVec n P y) = matMulVec n P yTail := by
    funext i
    by_cases hi : i.val < p.val
    · simp [householderTrailingPart, hi, hPtailPrefix i hi]
    · have hpi : p.val ≤ i.val := Nat.le_of_not_gt hi
      simp only [householderTrailingPart, hi]
      rw [congrFun hmulSplit i, congrFun hPprefix i]
      simp [hprefixSupport i hpi]
  rw [htailEq]
  exact vecNorm2_orthogonal P yTail horth

/-- The executed pivot-column denominator has the same single-`sqrt m`
source-row bound used at the pivot-row update. -/
theorem exactPivotTailNorm_le {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) :
    exactPivotTailNorm hn hmn A k ≤
      Real.sqrt (m : ℝ) *
        ((1 + Real.sqrt 2) ^ k *
          theorem20_7_initialRowMax hn (rowSortedMatrix hn A)
            ⟨k, lt_of_lt_of_le hk hmn⟩) := by
  let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
  let q : Fin n := ⟨k, hk⟩
  let As := exactSwappedPanel hn hmn A k
  let B := (1 + Real.sqrt 2) ^ k *
    theorem20_7_initialRowMax hn (rowSortedMatrix hn A) p
  have hB : 0 ≤ B :=
    mul_nonneg (pow_nonneg coxHighamGrowthFactor_nonneg k)
      (theorem20_7_initialRowMax_nonneg hn (rowSortedMatrix hn A) p)
  have htailEntry : ∀ i : Fin m,
      |householderTrailingPart m p (fun r => As r q) i| ≤ B := by
    intro i
    by_cases hi : i.val < k
    · simpa [householderTrailingPart, p, hi] using hB
    · have hki : k ≤ i.val := Nat.le_of_not_gt hi
      have hrowSort :
          theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i ≤
            theorem20_7_initialRowMax hn (rowSortedMatrix hn A) p :=
        rowSortedMatrix_descending hn A (by simpa [p] using hki)
      have hlocal := exactSwappedPanel_active_entry_bound hn hmn A k hk i hki q
        (le_refl k)
        (B := (1 + Real.sqrt 2) ^ k *
          theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i)
        (fun l hl => exactASeq_active_bound hn hmn A k hk i hki l hl)
      have hAs : |As i q| ≤ B := hlocal.trans
        (mul_le_mul_of_nonneg_left hrowSort
          (pow_nonneg coxHighamGrowthFactor_nonneg k))
      simpa [householderTrailingPart, p, hi] using hAs
  have htail :
      vecNorm2 (householderTrailingPart m p (fun r => As r q)) ≤
        Real.sqrt (m : ℝ) * B :=
    vecNorm2_le_sqrt_card_mul_of_abs_le
      (householderTrailingPart m p (fun r => As r q)) hB htailEntry
  simpa [exactPivotTailNorm, hk, p, q, As, B] using htail

/-- One off-pivot RHS update.  Its coefficient is controlled by the literal
`phi`; the row entry multiplying that coefficient is the actual pivot-column
entry selected by the matrix trace. -/
theorem exactBSeq_offPivot_step {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (k : ℕ) (hk : k < n)
    (hpivot : 0 < exactPivotTailNorm hn hmn A k)
    (r : Fin m) (hr : k < r.val) {B R : ℝ}
    (hb : |exactBSeq hn hmn A b k r| ≤ B)
    (hA : |exactSwappedPanel hn hmn A k r ⟨k, hk⟩| ≤ R) :
    |exactBSeq hn hmn A b (k + 1) r| ≤
      B + (Real.sqrt 2 * exactPrintedPhi hn hmn A b) * R := by
  let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
  let q : Fin n := ⟨k, hk⟩
  let As := exactSwappedPanel hn hmn A k
  let x : Fin m → ℝ := fun i => As i q
  let alpha := signedHouseholderAlpha
    (Real.sqrt (householderTrailingNorm2Sq m p x)) (x p)
  let v := householderTrailingActiveVector m p x alpha
  let beta := householderBetaSpec m v
  let y := exactBSeq hn hmn A b k
  let phi := exactPrintedPhi hn hmn A b
  have hP : exactPSeq hn hmn A k = householder m v beta := by
    simp [exactPSeq, Higham20EliminationActual.exactPivotedQRPseq,
      Higham20EliminationActual.exactPivotedQRRawVector,
      Higham20EliminationActual.exactPivotedQRBeta,
      exactSwappedPanel, As, x, p, q, alpha, v, beta, hk,
      householderTrailingColumnNorm2Sq]
  have hvr : v r = As r q := by
    have hnot : ¬ r.val < k := not_lt.mpr (le_of_lt hr)
    have hrp : r ≠ p := by
      intro h
      have : r.val = k := by simpa [p] using congrArg Fin.val h
      omega
    simp [v, x, p, q, householderTrailingActiveVector,
      householderActiveVector, householderTrailingPart, hnot, hrp]
  have hinner :
      (∑ i : Fin m, v i * y i) =
        ∑ i : Fin m, v i * householderTrailingPart m p y i := by
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : i.val < k
    · have hvzero : v i = 0 := by
        simpa [v, p] using
          householderTrailingActiveVector_zero_prefix m p x alpha i
            (by simpa [p] using hi)
      simp [hvzero]
    · simp [householderTrailingPart, p, hi]
  have hy : vecNorm2 (householderTrailingPart m p y) ≤
      phi * Real.sqrt (householderTrailingNorm2Sq m p x) := by
    have htail := exactBSeq_tail_le_phi_mul_pivotNorm
      hn hmn A b k hk hpivot
    simpa [p, q, As, x, y, phi, exactPivotTailNorm, hk,
      vecNorm2, householderTrailingNorm2Sq] using htail
  have hcoeff : |beta * (∑ i : Fin m, v i * y i)| ≤
      Real.sqrt 2 * phi := by
    rw [hinner]
    exact abs_householderBeta_mul_inner_trailingPart_le_sqrt_two_mul
      m p x y alpha phi
        (signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq m p x)
        (signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos m p x)
        (exactPrintedPhi_nonneg hn hmn A b) hy
  rw [exactBSeq_succ hn hmn A b k hk]
  change |matMulVec m (exactPSeq hn hmn A k) y r| ≤ _
  rw [hP, congrFun (householder_matMulVec_eq m v beta y) r, hvr]
  have hprod : |(beta * ∑ i : Fin m, v i * y i) * As r q| ≤
      (Real.sqrt 2 * phi) * R := by
    rw [abs_mul]
    exact mul_le_mul hcoeff (by simpa [As, q] using hA)
      (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
        (exactPrintedPhi_nonneg hn hmn A b))
  have htri :
      |y r - (beta * ∑ i : Fin m, v i * y i) * As r q| ≤
        |y r| + |(beta * ∑ i : Fin m, v i * y i) * As r q| := by
    simpa using (abs_sub_le (y r) 0
      ((beta * ∑ i : Fin m, v i * y i) * As r q))
  simpa [phi, mul_assoc, mul_left_comm, mul_comm] using
    htri.trans (add_le_add hb hprod)

/-- Printed denominator weight
`max (phi * max_j |a_ij|) |b_i|` on the simultaneously sorted data. -/
noncomputable def exactPrintedBetaWeight {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (i : Fin m) : ℝ :=
  max
    (exactPrintedPhi hn hmn A b *
      theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i)
    |rowSortedRhs hn A b i|

theorem exactPrintedBetaWeight_nonneg {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (i : Fin m) :
    0 ≤ exactPrintedBetaWeight hn hmn A b i := by
  exact (abs_nonneg (rowSortedRhs hn A b i)).trans
    (le_max_right _ _)

/-- Active rows of the paired RHS trace grow by the same geometric factor as
the matrix rows. -/
theorem exactBSeq_active_bound {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hpivots : ∀ k : ℕ, ∀ hk : k < n,
      0 < exactPivotTailNorm hn hmn A k) :
    ∀ k : ℕ, k ≤ n → ∀ r : Fin m, k ≤ r.val →
      |exactBSeq hn hmn A b k r| ≤
        (1 + Real.sqrt 2) ^ k * exactPrintedBetaWeight hn hmn A b r := by
  intro k
  induction k with
  | zero =>
      intro _hk r _hr
      simpa [exactPrintedBetaWeight] using
        (le_max_right
          (exactPrintedPhi hn hmn A b *
            theorem20_7_initialRowMax hn (rowSortedMatrix hn A) r)
          |rowSortedRhs hn A b r|)
  | succ k ih =>
      intro hk r hr
      have hkn : k < n := Nat.lt_of_succ_le hk
      have hkr : k < r.val := Nat.lt_of_succ_le hr
      let W := exactPrintedBetaWeight hn hmn A b r
      let R := (1 + Real.sqrt 2) ^ k *
        theorem20_7_initialRowMax hn (rowSortedMatrix hn A) r
      have hb : |exactBSeq hn hmn A b k r| ≤
          (1 + Real.sqrt 2) ^ k * W := by
        simpa [W] using ih (Nat.le_of_lt hkn) r (le_of_lt hkr)
      have hA :
          |exactSwappedPanel hn hmn A k r ⟨k, hkn⟩| ≤ R := by
        exact exactSwappedPanel_active_entry_bound hn hmn A k hkn r
          (le_of_lt hkr) ⟨k, hkn⟩ (le_refl k)
          (B := R) (fun q hq => by
            simpa [R] using
              exactASeq_active_bound hn hmn A k hkn r (le_of_lt hkr) q hq)
      have hstep := exactBSeq_offPivot_step hn hmn A b k hkn
        (hpivots k hkn) r hkr hb hA
      have hphirow :
          exactPrintedPhi hn hmn A b *
              theorem20_7_initialRowMax hn (rowSortedMatrix hn A) r ≤ W := by
        exact le_max_left _ _
      have hpow : 0 ≤ (1 + Real.sqrt 2 : ℝ) ^ k :=
        pow_nonneg coxHighamGrowthFactor_nonneg k
      have hsqrt : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
      have hsecond :
          (Real.sqrt 2 * exactPrintedPhi hn hmn A b) * R ≤
            Real.sqrt 2 * ((1 + Real.sqrt 2) ^ k * W) := by
        dsimp [R]
        have hmul := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hphirow hpow) hsqrt
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      calc
        |exactBSeq hn hmn A b (k + 1) r| ≤
            (1 + Real.sqrt 2) ^ k * W +
              (Real.sqrt 2 * exactPrintedPhi hn hmn A b) * R := hstep
        _ ≤ (1 + Real.sqrt 2) ^ k * W +
              Real.sqrt 2 * ((1 + Real.sqrt 2) ^ k * W) :=
          add_le_add_right hsecond _
        _ = (1 + Real.sqrt 2) ^ (k + 1) * W := by
          rw [pow_succ]
          ring

/-- The RHS pivot-row update contributes the same single ambient `sqrt m`
factor as the matrix pivot row. -/
theorem exactBSeq_pivotRow_bound {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (k : ℕ) (hk : k < n)
    (hpivot : 0 < exactPivotTailNorm hn hmn A k) :
    |exactBSeq hn hmn A b (k + 1) ⟨k, lt_of_lt_of_le hk hmn⟩| ≤
      Real.sqrt (m : ℝ) *
        ((1 + Real.sqrt 2) ^ k *
          exactPrintedBetaWeight hn hmn A b
            ⟨k, lt_of_lt_of_le hk hmn⟩) := by
  let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
  let raw := Higham20EliminationActual.exactPivotedQRRawVector
    hmn (le_refl n) (rowSortedMatrix hn A) k
  let beta := Higham20EliminationActual.exactPivotedQRBeta
    hmn (le_refl n) (rowSortedMatrix hn A) k
  let y := exactBSeq hn hmn A b k
  let phi := exactPrintedPhi hn hmn A b
  let rowMax := theorem20_7_initialRowMax hn (rowSortedMatrix hn A) p
  let W := exactPrintedBetaWeight hn hmn A b p
  have hprefix : ∀ i : Fin m, i.val < p.val → raw i = 0 := by
    intro i hi
    exact Higham20EliminationActual.exactPivotedQRRawVector_zero_prefix
      hmn (le_refl n) (rowSortedMatrix hn A) k hk i (by simpa [p] using hi)
  have horth : IsOrthogonal m (householder m raw beta) := by
    simpa [raw, beta, exactPSeq,
      Higham20EliminationActual.exactPivotedQRPseq] using
      (Higham20EliminationActual.exactPivotedQRPseq_orthogonal
        hmn (le_refl n) (rowSortedMatrix hn A) k)
  have hcoord : |matMulVec m (householder m raw beta) y p| ≤
      vecNorm2 (householderTrailingPart m p y) :=
    abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal
      m p raw beta y hprefix horth
  have htail : vecNorm2 (householderTrailingPart m p y) ≤
      phi * exactPivotTailNorm hn hmn A k := by
    simpa [p, y, phi] using
      exactBSeq_tail_le_phi_mul_pivotNorm hn hmn A b k hk hpivot
  have hpivotBound := exactPivotTailNorm_le hn hmn A k hk
  have hphi : 0 ≤ phi := by
    exact exactPrintedPhi_nonneg hn hmn A b
  have hphirow : phi * rowMax ≤ W := by
    exact le_max_left _ _
  have hsqrtpow : 0 ≤ Real.sqrt (m : ℝ) *
      (1 + Real.sqrt 2) ^ k :=
    mul_nonneg (Real.sqrt_nonneg _)
      (pow_nonneg coxHighamGrowthFactor_nonneg _)
  have hweighted : phi * exactPivotTailNorm hn hmn A k ≤
      Real.sqrt (m : ℝ) * ((1 + Real.sqrt 2) ^ k * W) := by
    calc
      phi * exactPivotTailNorm hn hmn A k ≤
          phi * (Real.sqrt (m : ℝ) *
            ((1 + Real.sqrt 2) ^ k * rowMax)) :=
        mul_le_mul_of_nonneg_left (by simpa [p, rowMax] using hpivotBound) hphi
      _ = (Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ k) *
            (phi * rowMax) := by ring
      _ ≤ (Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ k) * W :=
        mul_le_mul_of_nonneg_left hphirow hsqrtpow
      _ = Real.sqrt (m : ℝ) * ((1 + Real.sqrt 2) ^ k * W) := by ring
  rw [exactBSeq_succ hn hmn A b k hk]
  change |matMulVec m (exactPSeq hn hmn A k) y p| ≤ _
  have hPeq : exactPSeq hn hmn A k = householder m raw beta := by rfl
  rw [hPeq]
  simpa [p, W] using hcoord.trans (htail.trans hweighted)

/-- A completed RHS row is fixed by every later reflector. -/
theorem exactBSeq_completedRow_step {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (k : ℕ) (hk : k < n)
    (r : Fin m) (hr : r.val < k) {B : ℝ}
    (hbound : |exactBSeq hn hmn A b k r| ≤ B) :
    |exactBSeq hn hmn A b (k + 1) r| ≤ B := by
  let raw := Higham20EliminationActual.exactPivotedQRRawVector
    hmn (le_refl n) (rowSortedMatrix hn A) k
  let beta := Higham20EliminationActual.exactPivotedQRBeta
    hmn (le_refl n) (rowSortedMatrix hn A) k
  let y := exactBSeq hn hmn A b k
  have hprefix : ∀ i : Fin m, i.val < k → raw i = 0 := by
    intro i hi
    exact Higham20EliminationActual.exactPivotedQRRawVector_zero_prefix
      hmn (le_refl n) (rowSortedMatrix hn A) k hk i hi
  have hpres : matMulVec m (householder m raw beta) y r = y r :=
    matMulVec_householder_eq_self_of_zero_prefix
      m k raw y beta hprefix r hr
  rw [exactBSeq_succ hn hmn A b k hk]
  change |matMulVec m (exactPSeq hn hmn A k) y r| ≤ B
  have hPeq : exactPSeq hn hmn A k = householder m raw beta := by rfl
  rw [hPeq, hpres]
  exact hbound

/-- Once RHS row `k` is completed, its pivot bound persists through every
later recorded state. -/
theorem exactBSeq_completedRow_bound {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (k : ℕ) (hk : k < n)
    (hpivot : 0 < exactPivotTailNorm hn hmn A k) :
    ∀ t : ℕ, k + 1 ≤ t → t ≤ n →
      |exactBSeq hn hmn A b t ⟨k, lt_of_lt_of_le hk hmn⟩| ≤
        Real.sqrt (m : ℝ) *
          ((1 + Real.sqrt 2) ^ k *
            exactPrintedBetaWeight hn hmn A b
              ⟨k, lt_of_lt_of_le hk hmn⟩) := by
  let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
  let C := Real.sqrt (m : ℝ) *
    ((1 + Real.sqrt 2) ^ k * exactPrintedBetaWeight hn hmn A b p)
  intro t hkt htn
  induction t, hkt using Nat.le_induction with
  | base =>
      simpa [p, C] using exactBSeq_pivotRow_bound hn hmn A b k hk hpivot
  | succ t hbase ih =>
      have htlt : t < n := lt_of_lt_of_le (Nat.lt_succ_self t) htn
      have hpk : p.val < t := by simpa [p] using hbase
      exact exactBSeq_completedRow_step hn hmn A b t htlt p hpk
        (B := C) (ih (Nat.le_of_lt htlt))

/-- Every RHS state that is an input to one of the `n` Householder stages
satisfies the printed envelope.  In source notation these are
`b^(1), ..., b^(n)`; the post-stage output `b^(n+1)` is not an operand in a
Householder rounding step and is therefore not part of `max_k |b_i^(k)|`. -/
theorem exactBSeq_uniform_printed_bound {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hpivots : ∀ k : ℕ, ∀ hk : k < n,
      0 < exactPivotTailNorm hn hmn A k)
    (t : ℕ) (ht : t < n) (i : Fin m) :
    |exactBSeq hn hmn A b t i| ≤
      Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1) *
        exactPrintedBetaWeight hn hmn A b i := by
  have hmpos : 0 < m := lt_of_lt_of_le hn hmn
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
  have hsqrtm : (1 : ℝ) ≤ Real.sqrt m := by
    have h := Real.sqrt_le_sqrt hmR
    simpa using h
  have hbase : (1 : ℝ) ≤ 1 + Real.sqrt 2 := by
    linarith [Real.sqrt_nonneg (2 : ℝ)]
  have hW : 0 ≤ exactPrintedBetaWeight hn hmn A b i :=
    exactPrintedBetaWeight_nonneg hn hmn A b i
  by_cases hit : i.val < t
  · have hin : i.val < n := lt_trans hit ht
    have hdone := exactBSeq_completedRow_bound hn hmn A b i.val hin
      (hpivots i.val hin) t (Nat.succ_le_iff.mpr hit) (Nat.le_of_lt ht)
    have hpow : (1 + Real.sqrt 2 : ℝ) ^ i.val ≤
        (1 + Real.sqrt 2) ^ (n - 1) :=
      pow_le_pow_right₀ hbase (by omega)
    calc
      |exactBSeq hn hmn A b t i| ≤
          Real.sqrt (m : ℝ) *
            ((1 + Real.sqrt 2) ^ i.val *
              exactPrintedBetaWeight hn hmn A b i) := by
        simpa using hdone
      _ ≤ Real.sqrt (m : ℝ) *
            ((1 + Real.sqrt 2) ^ (n - 1) *
              exactPrintedBetaWeight hn hmn A b i) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow hW) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · have hti : t ≤ i.val := Nat.le_of_not_gt hit
    have hactive := exactBSeq_active_bound hn hmn A b hpivots t
      (Nat.le_of_lt ht) i hti
    have hpow : (1 + Real.sqrt 2 : ℝ) ^ t ≤
        (1 + Real.sqrt 2) ^ (n - 1) :=
      pow_le_pow_right₀ hbase (by omega)
    calc
      |exactBSeq hn hmn A b t i| ≤
          (1 + Real.sqrt 2) ^ t *
            exactPrintedBetaWeight hn hmn A b i := hactive
      _ ≤ (1 + Real.sqrt 2) ^ (n - 1) *
            exactPrintedBetaWeight hn hmn A b i :=
        mul_le_mul_of_nonneg_right hpow hW
      _ = 1 * ((1 + Real.sqrt 2) ^ (n - 1) *
            exactPrintedBetaWeight hn hmn A b i) := by ring
      _ ≤ Real.sqrt (m : ℝ) *
            ((1 + Real.sqrt 2) ^ (n - 1) *
              exactPrintedBetaWeight hn hmn A b i) :=
        mul_le_mul_of_nonneg_right hsqrtm
          (mul_nonneg (pow_nonneg coxHighamGrowthFactor_nonneg _) hW)
      _ = _ := by ring

/-- Source-faithful RHS numerator `max_k |b_i^(k)|`: the maximum is over the
`n` pre-step states used by the `n` Householder applications. -/
noncomputable def exactPrintedRhsRowGrowthScale {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (i : Fin m) : ℝ :=
  ⨆ t : Fin n, |exactBSeq hn hmn A b t.val i|

/-- Literal numerator of the printed `beta_i`. -/
noncomputable def exactPrintedBetaScale {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (i : Fin m) : ℝ :=
  max
    (exactPrintedPhi hn hmn A b * exactPrintedAlphaScale hn hmn A i)
    (exactPrintedRhsRowGrowthScale hn hmn A b i)

/-- Literal dimensionless printed RHS row-growth ratio. -/
noncomputable def exactPrintedBeta {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (i : Fin m) : ℝ :=
  exactPrintedBetaScale hn hmn A b i / exactPrintedBetaWeight hn hmn A b i

theorem exactPrintedRhsRowGrowthScale_le_cap_mul_weight {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hpivots : ∀ k : ℕ, ∀ hk : k < n,
      0 < exactPivotTailNorm hn hmn A k) (i : Fin m) :
    exactPrintedRhsRowGrowthScale hn hmn A b i ≤
      (Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1)) *
        exactPrintedBetaWeight hn hmn A b i := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold exactPrintedRhsRowGrowthScale
  refine ciSup_le fun t => ?_
  simpa [mul_assoc] using
    exactBSeq_uniform_printed_bound hn hmn A b hpivots t.val t.isLt i

theorem exactPrintedBetaScale_le_cap_mul_weight {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hpivots : ∀ k : ℕ, ∀ hk : k < n,
      0 < exactPivotTailNorm hn hmn A k) (i : Fin m) :
    exactPrintedBetaScale hn hmn A b i ≤
      (Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1)) *
        exactPrintedBetaWeight hn hmn A b i := by
  let C := Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1)
  let phi := exactPrintedPhi hn hmn A b
  let rowMax := theorem20_7_initialRowMax hn (rowSortedMatrix hn A) i
  let W := exactPrintedBetaWeight hn hmn A b i
  have hC : 0 ≤ C :=
    mul_nonneg (Real.sqrt_nonneg _)
      (pow_nonneg coxHighamGrowthFactor_nonneg _)
  have hphi : 0 ≤ phi := exactPrintedPhi_nonneg hn hmn A b
  have hphiA : phi * exactPrintedAlphaScale hn hmn A i ≤ C * W := by
    have hA := exactPrintedAlphaScale_le_cap_mul_rowMax hn hmn A i
    have h1 : phi * exactPrintedAlphaScale hn hmn A i ≤
        phi * (C * rowMax) := by
      exact mul_le_mul_of_nonneg_left (by simpa [C, rowMax] using hA) hphi
    have hrowW : phi * rowMax ≤ W := le_max_left _ _
    calc
      phi * exactPrintedAlphaScale hn hmn A i ≤ phi * (C * rowMax) := h1
      _ = C * (phi * rowMax) := by ring
      _ ≤ C * W := mul_le_mul_of_nonneg_left hrowW hC
  have hb : exactPrintedRhsRowGrowthScale hn hmn A b i ≤ C * W := by
    simpa [C, W] using
      exactPrintedRhsRowGrowthScale_le_cap_mul_weight hn hmn A b hpivots i
  exact max_le (by simpa [exactPrintedBetaScale, phi, W] using hphiA) hb

theorem exactPrintedBetaScale_nonneg {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (i : Fin m) :
    0 ≤ exactPrintedBetaScale hn hmn A b i := by
  apply le_max_of_le_right
  let t0 : Fin n := ⟨0, hn⟩
  exact (abs_nonneg (exactBSeq hn hmn A b t0.val i)).trans
    (le_ciSup
      (Finite.bddAbove_range
        (fun t : Fin n => |exactBSeq hn hmn A b t.val i|)) t0)

/-- The literal printed `beta_i` obeys the Cox--Higham cap; a zero denominator
is handled without an artificial positivity premise because the proved scale
bound forces its numerator to vanish as well. -/
theorem exactPrintedBeta_le_cap {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hpivots : ∀ k : ℕ, ∀ hk : k < n,
      0 < exactPivotTailNorm hn hmn A k) (i : Fin m) :
    exactPrintedBeta hn hmn A b i ≤
      Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1) := by
  let C := Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1)
  let W := exactPrintedBetaWeight hn hmn A b i
  have hC : 0 ≤ C :=
    mul_nonneg (Real.sqrt_nonneg _)
      (pow_nonneg coxHighamGrowthFactor_nonneg _)
  have hscale := exactPrintedBetaScale_le_cap_mul_weight
    hn hmn A b hpivots i
  by_cases hW0 : W = 0
  · have hscale0 : exactPrintedBetaScale hn hmn A b i = 0 := by
      apply le_antisymm
      · simpa [C, W, hW0] using hscale
      · exact exactPrintedBetaScale_nonneg hn hmn A b i
    simp [exactPrintedBeta, W, hW0, hscale0, C, hC]
  · have hWpos : 0 < W := lt_of_le_of_ne
        (exactPrintedBetaWeight_nonneg hn hmn A b i) (Ne.symm hW0)
    rw [exactPrintedBeta, div_le_iff₀ (by simpa [W] using hWpos)]
    simpa [C, W] using hscale

/-- Executable exact-trace closure of the p. 395 row-sorting claim. -/
theorem exactPrinted_max_alpha_beta_le_cap {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hpivots : ∀ k : ℕ, ∀ hk : k < n,
      0 < exactPivotTailNorm hn hmn A k) (i : Fin m) :
    max (exactPrintedAlpha hn hmn A i)
        (exactPrintedBeta hn hmn A b i) ≤
      Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1) := by
  exact max_le (exactPrintedAlpha_le_cap hn hmn A i)
    (exactPrintedBeta_le_cap hn hmn A b hpivots i)

/-! ## Row-order invariance of the printed scalar -/

/-- The exact accumulated orthogonal factor paired with `exactASeq` and
`exactBSeq`. -/
noncomputable def exactQ {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin m → ℝ :=
  Wave19.Qacc (exactPSeq hn hmn A) n

/-- The completed exact trapezoidal factor of the sorted trace. -/
noncomputable def exactR {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  exactASeq hn hmn A n

/-- The accumulated active-max column permutation of the sorted trace. -/
noncomputable def exactColumnPerm {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Theorem20_7.pivotPermAcc
    (Higham20EliminationActual.exactPivotedQRSwapSeq hmn (le_refl n)
      (rowSortedMatrix hn A)) n

/-- The accumulated exact factor is orthogonal. -/
theorem exactQ_orthogonal {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) :
    IsOrthogonal m (exactQ hn hmn A) := by
  simpa [exactQ, exactPSeq] using
    (Higham20EliminationActual.exactPivotedQR_factorization
      hmn (le_refl n) (rowSortedMatrix hn A)).1

/-- Exact pivoted factorization produced by the row-sorted executor. -/
theorem exactQR_factorization {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) :
    Wave13.columnPermuteMatrix (rowSortedMatrix hn A)
        (exactColumnPerm hn hmn A) =
      matMulRect m m n (exactQ hn hmn A) (exactR hn hmn A) := by
  simpa [exactQ, exactR, exactColumnPerm, exactPSeq, exactASeq] using
    (Higham20EliminationActual.exactPivotedQR_factorization
      hmn (le_refl n) (rowSortedMatrix hn A)).2

/-- Source full column rank is preserved by the executable row sorting. -/
theorem rectMatMulVec_rowSortedMatrix_injective {m n : ℕ}
    (hn : 0 < n) (A : Fin m → Fin n → ℝ)
    (hA : Function.Injective (rectMatMulVec A)) :
    Function.Injective (rectMatMulVec (rowSortedMatrix hn A)) := by
  intro x y hxy
  apply hA
  have hperm :
      vecPermute (rowSortPerm hn A) (rectMatMulVec A x) =
        vecPermute (rowSortPerm hn A) (rectMatMulVec A y) := by
    simpa [rowSortedMatrix] using hxy
  have hrecover := congrArg (vecPermute (rowSortPerm hn A).symm) hperm
  simpa [vecPermute_symm_vecPermute] using hrecover

/-- The completed exact rectangular `R` has an injective matrix-vector action
whenever the source matrix has full column rank. -/
theorem exactR_rectMatMulVec_injective_of_source_injective {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hA : Function.Injective (rectMatMulVec A)) :
    Function.Injective (rectMatMulVec (exactR hn hmn A)) := by
  let pi := exactColumnPerm hn hmn A
  let As := rowSortedMatrix hn A
  let Q := exactQ hn hmn A
  let R := exactR hn hmn A
  have hAs : Function.Injective (rectMatMulVec As) := by
    simpa [As] using rectMatMulVec_rowSortedMatrix_injective hn A hA
  have hApi : Function.Injective
      (rectMatMulVec (rectPermuteCols pi As)) :=
    rectMatMulVec_injective_rectPermuteCols pi hAs
  have hfactor : rectPermuteCols pi As = matMulRect m m n Q R := by
    simpa [pi, As, Q, R, rectPermuteCols, Wave13.columnPermuteMatrix] using
      exactQR_factorization hn hmn A
  intro x y hxy
  apply hApi
  calc
    rectMatMulVec (rectPermuteCols pi As) x =
        rectMatMulVec (matMulRect m m n Q R) x := by rw [hfactor]
    _ = matMulVec m Q (rectMatMulVec R x) := by
      simpa [matMulRect, matMulRectLeft] using
        rectMatMulVec_matMulRectLeft Q R x
    _ = matMulVec m Q (rectMatMulVec R y) := by rw [hxy]
    _ = rectMatMulVec (matMulRect m m n Q R) y := by
      simpa [matMulRect, matMulRectLeft] using
        (rectMatMulVec_matMulRectLeft Q R y).symm
    _ = rectMatMulVec (rectPermuteCols pi As) y := by rw [hfactor]

/-- The leading square block of the completed exact trapezoidal factor. -/
noncomputable def exactRTop {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => exactR hn hmn A (Fin.castLE hmn i) j

/-- Source full column rank makes every diagonal entry of the completed exact
top `R` block nonzero. -/
theorem exactR_diag_ne_zero_of_source_injective {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hA : Function.Injective (rectMatMulVec A)) (k : Fin n) :
    exactR hn hmn A ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩ k ≠ 0 := by
  let Rt := exactRTop hn hmn A
  have hupper : ∀ i j : Fin n, j.val < i.val → Rt i j = 0 := by
    intro i j hji
    simpa [Rt, exactRTop, exactR, exactASeq] using
      (Higham20EliminationActual.exactPivotedQRMatrixSeq_prefix_lower_zero
        hmn (le_refl n) (rowSortedMatrix hn A) n (le_refl n)
          (Fin.castLE hmn i) j j.isLt (by simpa using hji))
  have hbottom : ∀ i : Fin m, n ≤ i.val → ∀ j : Fin n,
      exactR hn hmn A i j = 0 := by
    intro i hi j
    exact Higham20EliminationActual.exactPivotedQRMatrixSeq_prefix_lower_zero
      hmn (le_refl n) (rowSortedMatrix hn A) n (le_refl n) i j
        j.isLt (lt_of_lt_of_le j.isLt hi)
  have hRinj := exactR_rectMatMulVec_injective_of_source_injective hn hmn A hA
  have hRtopInj : Function.Injective (rectMatMulVec Rt) := by
    intro x y hxy
    apply hRinj
    funext i
    by_cases hi : i.val < n
    · let ii : Fin n := ⟨i.val, hi⟩
      have hii := congrFun hxy ii
      simpa [Rt, exactRTop, ii] using hii
    · have hni : n ≤ i.val := Nat.le_of_not_gt hi
      unfold rectMatMulVec
      simp [hbottom i hni]
  have hdet : Matrix.det (Rt : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
    rectMatMulVec_det_ne_zero_of_injective hRtopInj
  have hdiag := diag_ne_zero_of_upper_triangular_det_ne_zero n Rt hupper hdet k
  simpa [Rt, exactRTop] using hdiag

private theorem daAcc_zero {m p : ℕ}
    (Pseq : ℕ → Fin m → Fin m → ℝ) :
    ∀ r (i : Fin m) (j : Fin p),
      Wave19.DAacc Pseq (fun _ _ _ => 0) r i j = 0 := by
  intro r
  induction r with
  | zero => simp [Wave19.DAacc]
  | succ r ih =>
      intro i j
      simp [Wave19.DAacc, ih, matMulRect]

/-- The terminal exact RHS state is literally `Qᵀ b` for the accumulated
factor of the same reflector trace. -/
theorem exactBSeq_final_eq_matTranspose_exactQ_mulVec {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) :
    exactBSeq hn hmn A b n =
      matMulVec m (matTranspose (exactQ hn hmn A)) (rowSortedRhs hn A b) := by
  let Bmat : ℕ → Fin m → Fin 1 → ℝ :=
    fun t i _ => exactBSeq hn hmn A b t i
  let Ezero : ℕ → Fin m → Fin 1 → ℝ := fun _ _ _ => 0
  have hP : ∀ k : ℕ, IsOrthogonal m (exactPSeq hn hmn A k) := by
    intro k
    simpa [exactPSeq] using
      (Higham20EliminationActual.exactPivotedQRPseq_orthogonal
        hmn (le_refl n) (rowSortedMatrix hn A) k)
  have hstep : ∀ k : ℕ, k < n → ∀ i j,
      Bmat (k + 1) i j =
        matMulRect m m 1 (exactPSeq hn hmn A k) (Bmat k) i j + Ezero k i j := by
    intro k hk i j
    dsimp [Bmat, Ezero]
    rw [exactBSeq_succ hn hmn A b k hk]
    simp [matMulRect, matMulVec]
  have htel := Wave19.entrywise_residual_telescope n Bmat
    (exactPSeq hn hmn A) Ezero hP hstep
  funext i
  have hi := htel i (0 : Fin 1)
  simpa [Bmat, Ezero, exactQ, daAcc_zero, matMulRect, matMulVec] using hi

/-- Later exact reflectors preserve the norm of every already exposed RHS
suffix. -/
theorem exactBSeq_trailing_norm_eq_later {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (k t : ℕ) (hk : k < n)
    (hkt : k ≤ t) (ht : t ≤ n) :
    vecNorm2
        (householderTrailingPart m ⟨k, lt_of_lt_of_le hk hmn⟩
          (exactBSeq hn hmn A b t)) =
      vecNorm2
        (householderTrailingPart m ⟨k, lt_of_lt_of_le hk hmn⟩
          (exactBSeq hn hmn A b k)) := by
  let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
  revert hkt ht
  induction t with
  | zero =>
      intro hkt _ht
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hkt
      subst k
      rfl
  | succ t ih =>
      intro hkt ht
      by_cases hEq : k = t + 1
      · subst k
        rfl
      · have hkt' : k ≤ t := by omega
        have htlt : t < n := lt_of_lt_of_le (Nat.lt_succ_self t) ht
        let raw := Higham20EliminationActual.exactPivotedQRRawVector
          hmn (le_refl n) (rowSortedMatrix hn A) t
        let beta := Higham20EliminationActual.exactPivotedQRBeta
          hmn (le_refl n) (rowSortedMatrix hn A) t
        have hprefix : ∀ i : Fin m, i.val < p.val → raw i = 0 := by
          intro i hi
          exact Higham20EliminationActual.exactPivotedQRRawVector_zero_prefix
            hmn (le_refl n) (rowSortedMatrix hn A) t htlt i
              (lt_of_lt_of_le (by simpa [p] using hi) hkt')
        have horth : IsOrthogonal m (householder m raw beta) := by
          simpa [raw, beta, exactPSeq,
            Higham20EliminationActual.exactPivotedQRPseq] using
            (Higham20EliminationActual.exactPivotedQRPseq_orthogonal
              hmn (le_refl n) (rowSortedMatrix hn A) t)
        have hstage := vecNorm2_trailingPart_matMulVec_householder_eq
          m p raw (exactBSeq hn hmn A b t) beta hprefix horth
        calc
          vecNorm2 (householderTrailingPart m p
              (exactBSeq hn hmn A b (t + 1))) =
              vecNorm2 (householderTrailingPart m p
                (exactBSeq hn hmn A b t)) := by
            rw [exactBSeq_succ hn hmn A b t htlt]
            have hPeq : exactPSeq hn hmn A t = householder m raw beta := by rfl
            rw [hPeq]
            exact hstage
          _ = vecNorm2 (householderTrailingPart m p
                (exactBSeq hn hmn A b k)) :=
            ih hkt' (Nat.le_of_lt htlt)

/-- If a vector is zero strictly below a pivot, the norm of its pivot suffix
is the magnitude of that pivot entry. -/
theorem vecNorm2_trailingPart_eq_abs_of_zero_below {m : ℕ}
    (p : Fin m) (y : Fin m → ℝ)
    (hzero : ∀ i : Fin m, p.val < i.val → y i = 0) :
    vecNorm2 (householderTrailingPart m p y) = |y p| := by
  unfold vecNorm2 vecNorm2Sq
  have hsum :
      (∑ i : Fin m, householderTrailingPart m p y i ^ 2) = y p ^ 2 := by
    classical
    rw [Finset.sum_eq_single p]
    · simp [householderTrailingPart]
    · intro i _hi hip
      by_cases hil : i.val < p.val
      · simp [householderTrailingPart, hil]
      · have hpi : p.val < i.val := by
          have hle : p.val ≤ i.val := Nat.le_of_not_gt hil
          have hne : p.val ≠ i.val := by
            intro heq
            exact hip (Fin.ext heq.symm)
          exact lt_of_le_of_ne hle hne
        simp [householderTrailingPart, hil, hzero i hpi]
    · simp
  rw [hsum, Real.sqrt_sq_eq_abs]

/-- The active pivot-column norm printed in `phi` is the magnitude of the
corresponding diagonal entry of the completed exact `R`. -/
theorem exactPivotTailNorm_eq_abs_exactR_diag {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < n) :
    exactPivotTailNorm hn hmn A k =
      |exactR hn hmn A ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩| := by
  let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
  let q : Fin n := ⟨k, hk⟩
  let x : Fin m → ℝ := fun r => exactSwappedPanel hn hmn A k r q
  let y : Fin m → ℝ := matMulVec m (exactPSeq hn hmn A k) x
  let raw := Higham20EliminationActual.exactPivotedQRRawVector
    hmn (le_refl n) (rowSortedMatrix hn A) k
  let beta := Higham20EliminationActual.exactPivotedQRBeta
    hmn (le_refl n) (rowSortedMatrix hn A) k
  have hprefix : ∀ i : Fin m, i.val < p.val → raw i = 0 := by
    intro i hi
    exact Higham20EliminationActual.exactPivotedQRRawVector_zero_prefix
      hmn (le_refl n) (rowSortedMatrix hn A) k hk i (by simpa [p] using hi)
  have horth : IsOrthogonal m (householder m raw beta) := by
    simpa [raw, beta, exactPSeq,
      Higham20EliminationActual.exactPivotedQRPseq] using
      (Higham20EliminationActual.exactPivotedQRPseq_orthogonal
        hmn (le_refl n) (rowSortedMatrix hn A) k)
  have hPeq : exactPSeq hn hmn A k = householder m raw beta := by rfl
  have hnorm : vecNorm2 (householderTrailingPart m p y) =
      vecNorm2 (householderTrailingPart m p x) := by
    rw [show y = matMulVec m (householder m raw beta) x by simp [y, hPeq]]
    exact vecNorm2_trailingPart_matMulVec_householder_eq
      m p raw x beta hprefix horth
  have hzero : ∀ i : Fin m, p.val < i.val → y i = 0 := by
    intro i hi
    simpa [y, x, p, q] using
      (Higham20EliminationActual.exactPivotedQRPseq_pivot_column_zero_below
        hmn (le_refl n) (rowSortedMatrix hn A) k hk i (by simpa [p] using hi))
  have hsingle : vecNorm2 (householderTrailingPart m p y) = |y p| :=
    vecNorm2_trailingPart_eq_abs_of_zero_below p y hzero
  have hycompletion : y p = exactASeq hn hmn A (k + 1) p q := by
    rw [exactASeq_succ hn hmn A k hk]
    rfl
  have hstable : exactR hn hmn A p q = exactASeq hn hmn A (k + 1) p q := by
    simpa [exactR, exactASeq, q] using
      (Higham20EliminationActual.exactPivotedQRMatrixSeq_completed_column_stable
        hmn (le_refl n) (rowSortedMatrix hn A) k n hk
          (Nat.succ_le_iff.mpr hk) (le_refl n) p)
  calc
    exactPivotTailNorm hn hmn A k =
        vecNorm2 (householderTrailingPart m p x) := by
      simp [exactPivotTailNorm, hk, p, q, x]
    _ = vecNorm2 (householderTrailingPart m p y) := hnorm.symm
    _ = |y p| := hsingle
    _ = |exactASeq hn hmn A (k + 1) p q| := by rw [hycompletion]
    _ = |exactR hn hmn A p q| := by rw [hstable]

/-- Ordinary source full column rank discharges the exact positive-pivot
domain required by the printed `phi` and `beta_i` ratios. -/
theorem exactPivotTailNorm_pos_of_source_injective {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hA : Function.Injective (rectMatMulVec A)) (k : ℕ) (hk : k < n) :
    0 < exactPivotTailNorm hn hmn A k := by
  rw [exactPivotTailNorm_eq_abs_exactR_diag hn hmn A k hk]
  exact abs_pos.mpr
    (exactR_diag_ne_zero_of_source_injective hn hmn A hA ⟨k, hk⟩)

/-- Source-facing p. 395 cap: full column rank derives nonbreakdown, so no
trace invariant is supplied by the caller. -/
theorem exactPrinted_max_alpha_beta_le_cap_of_source_injective {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (hA : Function.Injective (rectMatMulVec A))
    (i : Fin m) :
    max (exactPrintedAlpha hn hmn A i)
        (exactPrintedBeta hn hmn A b i) ≤
      Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1) := by
  exact exactPrinted_max_alpha_beta_le_cap hn hmn A b
    (fun k hk => exactPivotTailNorm_pos_of_source_injective hn hmn A hA k hk) i

/-- Literal finite `max_i` form of the Cox--Higham row-sorting cap. -/
theorem exactPrinted_iSup_max_alpha_beta_le_cap_of_source_injective {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (hA : Function.Injective (rectMatMulVec A)) :
    (⨆ i : Fin m,
      max (exactPrintedAlpha hn hmn A i)
        (exactPrintedBeta hn hmn A b i)) ≤
      Real.sqrt (m : ℝ) * (1 + Real.sqrt 2) ^ (n - 1) := by
  letI : Nonempty (Fin m) := ⟨⟨0, lt_of_lt_of_le hn hmn⟩⟩
  exact ciSup_le fun i =>
    exactPrinted_max_alpha_beta_le_cap_of_source_injective hn hmn A b hA i

/-- The QR-certificate form of Higham's printed scalar.  At step `k`, the
numerator is the norm of the trailing part of `Qᵀ b`, and the denominator is
the magnitude of the `k`th diagonal entry of the completed trapezoidal factor.
This form makes the simultaneous-row-permutation invariance algebraic. -/
noncomputable def qrCertificatePrintedPhi {m n : ℕ} (hmn : n ≤ m)
    (Q : Fin m → Fin m → ℝ) (R : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) : ℝ :=
  ⨆ k : Fin n,
    vecNorm2
        (householderTrailingPart m
          ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
          (matMulVec m (matTranspose Q) b)) /
      |R ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩ k|

/-- The stagewise literal `exactPrintedPhi` equals the terminal QR-certificate
form for the same executed trace. -/
theorem exactPrintedPhi_eq_qrCertificate {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) :
    exactPrintedPhi hn hmn A b =
      qrCertificatePrintedPhi hmn (exactQ hn hmn A) (exactR hn hmn A)
        (rowSortedRhs hn A b) := by
  unfold exactPrintedPhi qrCertificatePrintedPhi
  apply congrArg (fun f : Fin n → ℝ => ⨆ k : Fin n, f k)
  funext k
  have htail := exactBSeq_trailing_norm_eq_later hn hmn A b
    k.val n k.isLt (Nat.le_of_lt k.isLt) (le_refl n)
  rw [exactBSeq_final_eq_matTranspose_exactQ_mulVec hn hmn A b] at htail
  rw [exactPivotTailNorm_eq_abs_exactR_diag hn hmn A k.val k.isLt]
  exact congrArg
    (fun z : ℝ => z /
      |exactR hn hmn A ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩ k|)
    htail.symm

/-- Applying the same row permutation to an orthogonal factor and to a vector
does not change the transformed coordinates `Qᵀ b`. -/
theorem matTranspose_rectPermuteRows_mulVec_vecPermute {m : ℕ}
    (sigma : Fin m ≃ Fin m) (Q : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ) :
    matMulVec m (matTranspose (rectPermuteRows sigma Q))
        (vecPermute sigma b) =
      matMulVec m (matTranspose Q) b := by
  funext j
  unfold matMulVec matTranspose rectPermuteRows vecPermute
  exact Equiv.sum_comp sigma (fun i : Fin m => Q i j * b i)

/-- A row permutation of an orthogonal square factor is orthogonal. -/
theorem isOrthogonal_rectPermuteRows {m : ℕ}
    (sigma : Fin m ≃ Fin m) (Q : Fin m → Fin m → ℝ)
    (hQ : IsOrthogonal m Q) :
    IsOrthogonal m (rectPermuteRows sigma Q) := by
  apply IsOrthogonal.of_col_orthonormal
  intro i j
  unfold rectPermuteRows
  calc
    (∑ k : Fin m, Q (sigma k) i * Q (sigma k) j) =
        ∑ k : Fin m, Q k i * Q k j :=
      Equiv.sum_comp sigma (fun k : Fin m => Q k i * Q k j)
    _ = if i = j then 1 else 0 := hQ.col_orthonormal i j

/-- The QR factorization transports through a source-row permutation without
changing its column permutation or trapezoidal factor. -/
theorem qrFactorization_rectPermuteRows {m n : ℕ}
    (sigma : Fin m ≃ Fin m) (pi : Equiv.Perm (Fin n))
    (A : Fin m → Fin n → ℝ) (Q : Fin m → Fin m → ℝ)
    (R : Fin m → Fin n → ℝ)
    (hfactor : Wave13.columnPermuteMatrix A pi = matMulRect m m n Q R) :
    Wave13.columnPermuteMatrix (rectPermuteRows sigma A) pi =
      matMulRect m m n (rectPermuteRows sigma Q) R := by
  funext i j
  have hij := congrFun (congrFun hfactor (sigma i)) j
  simpa [Wave13.columnPermuteMatrix, rectPermuteRows, matMulRect] using hij

/-- Higham's printed `phi` is unchanged when the rows of `Q` and `b` are
permuted together.  The completed `R` factor is literally unchanged. -/
theorem qrCertificatePrintedPhi_rectPermuteRows {m n : ℕ}
    (hmn : n ≤ m) (sigma : Fin m ≃ Fin m)
    (Q : Fin m → Fin m → ℝ) (R : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) :
    qrCertificatePrintedPhi hmn (rectPermuteRows sigma Q) R
        (vecPermute sigma b) =
      qrCertificatePrintedPhi hmn Q R b := by
  unfold qrCertificatePrintedPhi
  rw [matTranspose_rectPermuteRows_mulVec_vecPermute]

/-- Executed-trace form of the p. 395 invariance statement: after rewriting
the literal stagewise scalar as its QR certificate, a simultaneous row
permutation of the matrix factor and right-hand side leaves it unchanged. -/
theorem exactPrintedPhi_transport_row_ordering {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (sigma : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    qrCertificatePrintedPhi hmn
        (rectPermuteRows sigma (exactQ hn hmn A)) (exactR hn hmn A)
        (vecPermute sigma (rowSortedRhs hn A b)) =
      exactPrintedPhi hn hmn A b := by
  rw [qrCertificatePrintedPhi_rectPermuteRows]
  exact (exactPrintedPhi_eq_qrCertificate hn hmn A b).symm

/-- Fully instantiated invariance certificate for the executed row-sorted
trace: any further simultaneous row permutation transports its exact QR
factorization and leaves the literal printed `phi` unchanged. -/
theorem exactPrintedPhi_independent_of_row_ordering {m n : ℕ}
    (hn : 0 < n) (hmn : n ≤ m) (sigma : Fin m ≃ Fin m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    IsOrthogonal m (rectPermuteRows sigma (exactQ hn hmn A)) ∧
      Wave13.columnPermuteMatrix
          (rectPermuteRows sigma (rowSortedMatrix hn A))
          (exactColumnPerm hn hmn A) =
        matMulRect m m n (rectPermuteRows sigma (exactQ hn hmn A))
          (exactR hn hmn A) ∧
      qrCertificatePrintedPhi hmn
          (rectPermuteRows sigma (exactQ hn hmn A)) (exactR hn hmn A)
          (vecPermute sigma (rowSortedRhs hn A b)) =
        exactPrintedPhi hn hmn A b := by
  exact ⟨isOrthogonal_rectPermuteRows sigma _ (exactQ_orthogonal hn hmn A),
    qrFactorization_rectPermuteRows sigma (exactColumnPerm hn hmn A)
      (rowSortedMatrix hn A) (exactQ hn hmn A) (exactR hn hmn A)
      (exactQR_factorization hn hmn A),
    exactPrintedPhi_transport_row_ordering hn hmn sigma A b⟩

/-- Certificate-level closure of the sentence on p. 395: simultaneous row
reordering preserves orthogonality and the pivoted QR factorization and leaves
the scalar `phi` exactly unchanged. -/
theorem printedPhi_independent_of_row_ordering {m n : ℕ}
    (hmn : n ≤ m) (sigma : Fin m ≃ Fin m)
    (pi : Equiv.Perm (Fin n)) (A : Fin m → Fin n → ℝ)
    (Q : Fin m → Fin m → ℝ) (R : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (hQ : IsOrthogonal m Q)
    (hfactor : Wave13.columnPermuteMatrix A pi = matMulRect m m n Q R) :
    IsOrthogonal m (rectPermuteRows sigma Q) ∧
      Wave13.columnPermuteMatrix (rectPermuteRows sigma A) pi =
        matMulRect m m n (rectPermuteRows sigma Q) R ∧
      qrCertificatePrintedPhi hmn (rectPermuteRows sigma Q) R
          (vecPermute sigma b) =
        qrCertificatePrintedPhi hmn Q R b := by
  exact ⟨isOrthogonal_rectPermuteRows sigma Q hQ,
    qrFactorization_rectPermuteRows sigma pi A Q R hfactor,
    qrCertificatePrintedPhi_rectPermuteRows hmn sigma Q R b⟩

end Higham20RowSorting

end NumStability
