import NumStability.Algorithms.LeastSquares.Higham20Theorem20_7ActualClosure

namespace NumStability

open scoped BigOperators

namespace Theorem20_7

/-!
# Rounded pivot-scale growth for the actual stored trace

The literal rounded recursion need not have exactly nonincreasing pivot
scales.  What it does have is a one-step relative growth estimate obtained
from the concrete constructor/application residual.  This is the honest
replacement for the exact sigma-ordering used by an exact-shadow analysis.
-/

/-- If the active-maximal constructor input is zero, every displayed active
entry is zero, not merely the selected pivot column. -/
theorem sourceConstructedPivotedStoredQRSwappedPanel_active_eq_zero_of_input_eq_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k = 0)
    (i : Fin m) (hi : k ≤ i.val) (j : Fin n) (hj : k ≤ j.val) :
    sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k i j = 0 := by
  let S := sourceConstructedPivotedStoredQRRowSwap fp hn hmn A k
  let b : Fin m → ℝ := fun q =>
    sourceConstructedPivotedStoredQRActivePanelPerm fp hn hmn A k q j
  have hnorm : vecNorm2 b ≤
      vecNorm2 (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k) := by
    exact sourceConstructedPivotedStoredQRActiveInput_pivot_max
      fp hn hmn A k hk j hj
  have hbNorm : vecNorm2 b = 0 := by
    apply le_antisymm
    · have hzero : vecNorm2 (0 : Fin m → ℝ) = 0 := by
        change vecNorm2 (fun _ : Fin m => 0) = 0
        exact vecNorm2_zero
      rw [hx, hzero] at hnorm
      exact hnorm
    · exact vecNorm2_nonneg b
  have hb : b = 0 := by
    funext q
    exact (vecNorm2_eq_zero_iff b).mp hbNorm q
  have hSinv : S (S i) = i := by
    simp [S, sourceConstructedPivotedStoredQRRowSwap,
      sourceConstructedRowSwap, hk]
  have hpoint := congrFun hb (S i)
  change sourceConstructedPivotedStoredQRActivePanelPerm
      fp hn hmn A k (S i) j = 0 at hpoint
  change (if (S (S i)).val < k then 0 else
      sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k
        (S (S i)) j) = 0 at hpoint
  rw [hSinv, if_neg (Nat.not_lt.mpr hi)] at hpoint
  exact hpoint

/-- A zero active maximum propagates to the next constructor input. -/
theorem sourceConstructedPivotedStoredQRActiveInput_succ_eq_zero_of_input_eq_zero
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk1 : k + 1 < n)
    (hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k = 0) :
    sourceConstructedPivotedStoredQRActiveInput fp hn hmn A (k + 1) = 0 := by
  let nextCol : Fin n := pivotedQRActiveCol (k + 1) hk1
  let nextSwap := sourceConstructedPivotedStoredQRSwapSeq
    fp hn hmn A (k + 1)
  let sourceCol : Fin n := nextSwap nextCol
  have hsourceCol : k + 1 ≤ sourceCol.val := by
    exact sourceConstructedPivotedStoredQRSwapSeq_maps_active
      fp hn hmn A (k + 1) nextCol (by simp [nextCol, pivotedQRActiveCol])
  have hstep :=
    fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_eq_swappedPanel_of_input_eq_zero
      fp hn hmn A k (Nat.lt_trans (Nat.lt_succ_self k) hk1) hx
  funext q
  let nextRowSwap := sourceConstructedPivotedStoredQRRowSwap
    fp hn hmn A (k + 1)
  by_cases hq : (nextRowSwap q).val < k + 1
  · simp [sourceConstructedPivotedStoredQRActiveInput,
      sourceConstructedActiveInput,
      sourceConstructedPivotedStoredQRActivePanelPerm,
      sourceConstructedActivePanelPerm, nextRowSwap, hq, hk1]
  · have hrow : k ≤ (nextRowSwap q).val := by omega
    have hzero :=
      sourceConstructedPivotedStoredQRSwappedPanel_active_eq_zero_of_input_eq_zero
        fp hn hmn A k (Nat.lt_trans (Nat.lt_succ_self k) hk1) hx
        (nextRowSwap q) hrow sourceCol (by omega)
    simp only [sourceConstructedPivotedStoredQRActiveInput, dif_pos hk1,
      sourceConstructedActiveInput,
      sourceConstructedPivotedStoredQRActivePanelPerm,
      sourceConstructedActivePanelPerm]
    change (if (nextRowSwap q).val < k + 1 then 0 else
      sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A (k + 1)
        (nextRowSwap q) nextCol) = 0
    rw [if_neg hq]
    change fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1)
        (nextRowSwap q) (nextSwap nextCol) = 0
    rw [congrFun (congrFun hstep (nextRowSwap q)) sourceCol]
    exact hzero

/-- In the nonzero branch, the next active constructor input is a masked row
permutation of one actually rounded work-panel column from the preceding
stage. -/
theorem sourceConstructedPivotedStoredQRActiveInput_succ_vecNorm2_le_appliedColumn
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk1 : k + 1 < n)
    (hx : sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k ≠ 0) :
    let hm : 0 < m := lt_of_lt_of_le hn hmn
    let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
    let nextCol : Fin n := pivotedQRActiveCol (k + 1) hk1
    let sourceCol := sourceConstructedPivotedStoredQRSwapSeq
      fp hn hmn A (k + 1) nextCol
    let b : Fin m → ℝ := fun q =>
      sourceConstructedPivotedStoredQRActivePanelPerm fp hn hmn A k q sourceCol
    vecNorm2 (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A (k + 1)) ≤
      vecNorm2 (fun q => fl_householderApply fp m
        (fl_householderNormalizedVector fp hm x) 1 b q) := by
  dsimp only
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let nextCol : Fin n := pivotedQRActiveCol (k + 1) hk1
  let nextSwap := sourceConstructedPivotedStoredQRSwapSeq
    fp hn hmn A (k + 1)
  let sourceCol : Fin n := nextSwap nextCol
  let b : Fin m → ℝ := fun q =>
    sourceConstructedPivotedStoredQRActivePanelPerm fp hn hmn A k q sourceCol
  let raw : Fin m → ℝ := fun q =>
    fl_householderApply fp m (fl_householderNormalizedVector fp hm x) 1 b q
  let currentRowSwap := sourceConstructedPivotedStoredQRRowSwap
    fp hn hmn A k
  let nextRowSwap := sourceConstructedPivotedStoredQRRowSwap
    fp hn hmn A (k + 1)
  let T : Equiv.Perm (Fin m) := nextRowSwap.trans currentRowSwap
  have hsourceCol : k + 1 ≤ sourceCol.val := by
    exact sourceConstructedPivotedStoredQRSwapSeq_maps_active
      fp hn hmn A (k + 1) nextCol (by simp [nextCol, pivotedQRActiveCol])
  have hstep := fl_sourceConstructedPivotedStoredQRMatrixSeq_succ_of_lt
    fp hn hmn A k (Nat.lt_trans (Nat.lt_succ_self k) hk1)
  have hpoint : ∀ q,
      |sourceConstructedPivotedStoredQRActiveInput fp hn hmn A (k + 1) q| ≤
        |vecPermute T raw q| := by
    intro q
    by_cases hq : (nextRowSwap q).val < k + 1
    · have hzero :
          sourceConstructedPivotedStoredQRActiveInput fp hn hmn A (k + 1) q = 0 := by
        simp [sourceConstructedPivotedStoredQRActiveInput,
          sourceConstructedActiveInput,
          sourceConstructedPivotedStoredQRActivePanelPerm,
          sourceConstructedActivePanelPerm, nextRowSwap, hq, hk1]
      rw [hzero, abs_zero]
      exact abs_nonneg _
    · have hrow : k ≤ (nextRowSwap q).val := by omega
      have hnotPrev : ¬ sourceCol.val < k := by omega
      have hnotPivot : ¬ sourceCol.val = k := by omega
      have hnextInput :
          sourceConstructedPivotedStoredQRActiveInput fp hn hmn A (k + 1) q =
            fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1)
              (nextRowSwap q) sourceCol := by
        simp only [sourceConstructedPivotedStoredQRActiveInput, dif_pos hk1,
          sourceConstructedActiveInput,
          sourceConstructedPivotedStoredQRActivePanelPerm,
          sourceConstructedActivePanelPerm]
        change (if (nextRowSwap q).val < k + 1 then 0 else
          fl_sourceConstructedPivotedStoredQRMatrixSeq fp hn hmn A (k + 1)
            (nextRowSwap q) (nextSwap nextCol)) = _
        rw [if_neg hq]
      rw [hnextInput, congrFun (congrFun hstep (nextRowSwap q)) sourceCol]
      change |fl_householderCoxHighamConstructedPanelStep fp hm k
          (pivotedQRActiveRow hmn k
            (Nat.lt_trans (Nat.lt_succ_self k) hk1))
          (pivotedQRActiveCol k
            (Nat.lt_trans (Nat.lt_succ_self k) hk1))
          (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k)
          (nextRowSwap q) sourceCol| ≤ _
      simp only [fl_householderCoxHighamConstructedPanelStep]
      have hxDirect : sourceConstructedActiveInput k
          (sourceConstructedRowSwap hm
            (pivotedQRActiveRow hmn k
              (Nat.lt_trans (Nat.lt_succ_self k) hk1)))
          (sourceConstructedPivotedStoredQRSwappedPanel fp hn hmn A k)
          (pivotedQRActiveCol k
            (Nat.lt_trans (Nat.lt_succ_self k) hk1)) ≠ 0 := by
        simpa [x, sourceConstructedPivotedStoredQRActiveInput,
          sourceConstructedPivotedStoredQRRowSwap,
          Nat.lt_trans (Nat.lt_succ_self k) hk1] using hx
      rw [dif_neg hxDirect]
      simp only [hnotPrev, if_false, Nat.not_lt.mpr hrow, hnotPivot]
      simpa [vecPermute, T, raw, b, x, currentRowSwap,
        sourceConstructedPivotedStoredQRActiveInput,
        sourceConstructedPivotedStoredQRActivePanelPerm,
        sourceConstructedPivotedStoredQRRowSwap,
        Nat.lt_trans (Nat.lt_succ_self k) hk1,
        fl_householderApplyMatrixRect]
  have hnorm := vecNorm2_le_of_abs_le
    (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A (k + 1))
    (fun q => |vecPermute T raw q|) hpoint
  rw [vecNorm2_abs] at hnorm
  have hperm : vecNorm2 (vecPermute T raw) = vecNorm2 raw := by
    unfold vecNorm2
    rw [vecNorm2Sq_permute]
  rw [hperm] at hnorm
  simpa [raw, b, x, hm] using hnorm

/-- Honest one-step rounded pivot-scale growth.  The zero branch propagates
exactly; the nonzero branch combines active maximality with the concrete
constructor/application residual norm. -/
theorem sourceConstructedPivotedStoredQRSigma_succ_le
    (fp : FPModel) {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ)
    (hvalid : gammaValid fp (11 * m + 23))
    (k : ℕ) (hk1 : k + 1 < n) :
    sourceConstructedPivotedStoredQRSigma fp hn hmn A (k + 1) ≤
      (1 + (fp.u + 2 * Real.sqrt 2 * gamma fp (11 * m + 23))) *
        sourceConstructedPivotedStoredQRSigma fp hn hmn A k := by
  let hm : 0 < m := lt_of_lt_of_le hn hmn
  let x := sourceConstructedPivotedStoredQRActiveInput fp hn hmn A k
  let sigma := sourceConstructedPivotedStoredQRSigma fp hn hmn A k
  let delta := fp.u + 2 * Real.sqrt 2 * gamma fp (11 * m + 23)
  by_cases hx : x = 0
  · have hnext :=
      sourceConstructedPivotedStoredQRActiveInput_succ_eq_zero_of_input_eq_zero
        fp hn hmn A k hk1 (by simpa [x] using hx)
    change vecNorm2
        (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A (k + 1)) ≤
      (1 + (fp.u + 2 * Real.sqrt 2 * gamma fp (11 * m + 23))) *
        vecNorm2 x
    rw [hnext, hx]
    change vecNorm2 (fun _ : Fin m => 0) ≤
      (1 + (fp.u + 2 * Real.sqrt 2 * gamma fp (11 * m + 23))) *
        vecNorm2 (fun _ : Fin m => 0)
    rw [vecNorm2_zero]
    simp
  · let nextCol : Fin n := pivotedQRActiveCol (k + 1) hk1
    let sourceCol := sourceConstructedPivotedStoredQRSwapSeq
      fp hn hmn A (k + 1) nextCol
    let b : Fin m → ℝ := fun q =>
      sourceConstructedPivotedStoredQRActivePanelPerm fp hn hmn A k q sourceCol
    let vraw := householderVector hm x
    let beta := householderBetaFromScale hm x
    let P := householder m vraw beta
    let e : Fin m → ℝ := fun q =>
      fl_householderApply fp m
          (fl_householderNormalizedVector fp hm x) 1 b q -
        matMulVec m P b q
    let raw : Fin m → ℝ := fun q =>
      fl_householderApply fp m
        (fl_householderNormalizedVector fp hm x) 1 b q
    have hsourceCol : k ≤ sourceCol.val := by
      have hge : k + 1 ≤ sourceCol.val :=
        sourceConstructedPivotedStoredQRSwapSeq_maps_active
          fp hn hmn A (k + 1) nextCol
            (by simp [nextCol, pivotedQRActiveCol])
      omega
    have hb : vecNorm2 b ≤ vecNorm2 x := by
      exact sourceConstructedPivotedStoredQRActiveInput_pivot_max
        fp hn hmn A k (Nat.lt_trans (Nat.lt_succ_self k) hk1)
          sourceCol hsourceCol
    have hP : IsOrthogonal m P := by
      apply householder_orthogonal
      simpa [P, vraw, beta] using
        householderBetaFromScale_mul_norm_sq hm x hx
    have he : vecNorm2 e ≤ delta * vecNorm2 x := by
      have h := fl_householderConstructApply_residual_vecNorm2_le_scaled
        fp hm x b hx 1 (by norm_num) (by simpa using hb) hvalid
      simpa [e, P, vraw, beta, delta] using h
    have hraw : vecNorm2 raw ≤ (1 + delta) * vecNorm2 x := by
      have h := rounded_orthogonal_column_norm_le
        P b e (vecNorm2 x) delta hP hb he
      have hrawEq : raw = fun q => matMulVec m P b q + e q := by
        funext q
        simp [raw, e]
      simpa [hrawEq] using h
    have hnext :=
      sourceConstructedPivotedStoredQRActiveInput_succ_vecNorm2_le_appliedColumn
        fp hn hmn A k hk1 (by simpa [x] using hx)
    change vecNorm2
        (sourceConstructedPivotedStoredQRActiveInput fp hn hmn A (k + 1)) ≤
      (1 + delta) * vecNorm2 x
    calc
      vecNorm2 (sourceConstructedPivotedStoredQRActiveInput
          fp hn hmn A (k + 1)) ≤ vecNorm2 raw := by
        simpa [hm, x, nextCol, sourceCol, b, raw] using hnext
      _ ≤ (1 + delta) * vecNorm2 x := hraw

end Theorem20_7

end NumStability
