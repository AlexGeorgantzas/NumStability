/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreSignedRank

/-! # Higham Chapter 28: signed rank-transfer helpers

This file supplies the finite rank identities used by the iterated signed
incidence argument.  Besides collapsing a finite signed sheet sum, it records
that the rank of a marked root is the number of roots of its deflated block
below the mark.  A truncated rank sheet then parametrizes exactly the roots
below an externally fixed threshold, away from the existing exceptional
sets.
-/

namespace NumStability

open MeasureTheory Set
open scoped BigOperators

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A finite signed prefix indexed by `Fin M` is the alternating count of the
prefix.  The weak bound is convenient when the ambient finite type has no
unused endpoint. -/
theorem sum_fin_ite_lt_eq_ginibreAlternatingCount
    (M r : ℕ) (hr : r ≤ M) :
    (∑ k : Fin M, if k.val < r then (-1 : ℝ) ^ k.val else 0) =
      ginibreAlternatingCount r := by
  change (∑ k : Fin M,
    (fun j : ℕ => if j < r then (-1 : ℝ) ^ j else 0) k) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j < r then (-1 : ℝ) ^ j else 0) M]
  unfold ginibreAlternatingCount
  calc
    (∑ j ∈ Finset.range M, if j < r then (-1 : ℝ) ^ j else 0) =
        ∑ j ∈ Finset.range r,
          if j < r then (-1 : ℝ) ^ j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hr)
      intro k hkM hkr
      simp only [Finset.mem_range] at hkM hkr
      simp [hkr]
    _ = ∑ j ∈ Finset.range r, (-1 : ℝ) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      simp [hj]

/-- The ordered-pair alternating count is the signed sum of the one-root
alternating prefixes at the second root. -/
theorem ginibreAlternatingPairCount_eq_sum_rankPrefixes (r : ℕ) :
    ginibreAlternatingPairCount r =
      ∑ j ∈ Finset.range r,
        (-1 : ℝ) ^ j * ginibreAlternatingCount j := by
  unfold ginibreAlternatingPairCount ginibreAlternatingCount
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add]
  ring

/-- Finite-sheet version of the preceding pair-prefix identity. -/
theorem sum_fin_ite_lt_eq_ginibreAlternatingPairCount
    (M r : ℕ) (hr : r ≤ M) :
    (∑ k : Fin M, if k.val < r then
        (-1 : ℝ) ^ k.val * ginibreAlternatingCount k.val else 0) =
      ginibreAlternatingPairCount r := by
  change (∑ k : Fin M,
    (fun j : ℕ => if j < r then
      (-1 : ℝ) ^ j * ginibreAlternatingCount j else 0) k) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j < r then
      (-1 : ℝ) ^ j * ginibreAlternatingCount j else 0) M]
  rw [ginibreAlternatingPairCount_eq_sum_rankPrefixes]
  calc
    (∑ j ∈ Finset.range M,
        if j < r then
          (-1 : ℝ) ^ j * ginibreAlternatingCount j else 0) =
        ∑ j ∈ Finset.range r,
          if j < r then
            (-1 : ℝ) ^ j * ginibreAlternatingCount j else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hr)
      intro k hkM hkr
      simp only [Finset.mem_range] at hkM hkr
      simp [hkr]
    _ = ∑ j ∈ Finset.range r,
        (-1 : ℝ) ^ j * ginibreAlternatingCount j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      simp [hj]

/-- The rank of the marked root in the full incidence matrix is already the
number of real roots of the deflated block strictly below that mark.  No
regularity hypothesis is needed. -/
theorem ginibreIncidenceRootRank_eq_deflatedBelowCount
    {m : ℕ} (q : GinibreIncidenceCoordinates m) :
    ginibreIncidenceRootRank q =
      realEigenvalueBelowCount
        (ginibreIncidenceDeflatedBlock q, ginibreIncidenceEigenvalue q) := by
  let D : RSqMat m := ginibreIncidenceDeflatedBlock q
  let l : ℝ := ginibreIncidenceEigenvalue q
  let P : Polynomial ℝ := D.charpoly
  have hPne : P ≠ 0 := (Matrix.charpoly_monic D).ne_zero
  have hlinear :
      (Polynomial.X - Polynomial.C l : Polynomial ℝ) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero l
  have hfullRoots :
      (ginibreIncidenceMatrix q).charpoly.roots = P.roots + {l} := by
    rw [ginibreIncidenceMatrix_charpoly_factor]
    change (D.charpoly * (Polynomial.X - Polynomial.C l)).roots = _
    rw [Polynomial.roots_mul (mul_ne_zero hPne hlinear),
      Polynomial.roots_X_sub_C]
  unfold ginibreIncidenceRootRank realEigenvalueBelowCount
  rw [ginibreCoordinatesFinMatrix_charpoly,
    ginibreCoordinatesMatrix_chart, hfullRoots,
    Multiset.filter_add, Multiset.card_add,
    Multiset.filter_singleton, if_neg (lt_irrefl l)]
  rfl

/-- The part of the `k`th regular incidence sheet whose marked root lies
strictly below an external threshold. -/
def ginibreIncidenceRankPieceBelow (m : ℕ) (k : Fin (m + 2)) (x : ℝ) :
    Set (GinibreIncidenceCoordinates m) :=
  ginibreIncidenceRankPiece m k ∩
    {q | ginibreIncidenceEigenvalue q < x}

theorem measurableSet_ginibreIncidenceRankPieceBelow
    (m : ℕ) (k : Fin (m + 2)) (x : ℝ) :
    MeasurableSet (ginibreIncidenceRankPieceBelow m k x) := by
  exact (measurableSet_ginibreIncidenceRankPiece m k).inter
    (measurableSet_lt measurable_ginibreIncidenceEigenvalue measurable_const)

/-- Ordinary signed-integral area formula on one regular rank sheet. -/
theorem integral_ginibreIncidence_rankPiece_eq_image
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure] (k : Fin (m + 2))
    (g : GinibreIncidenceCoordinates m → ℝ) :
    ∫ q in ginibreIncidenceRankPiece m k,
        |(ginibreIncidenceDerivativeLinearMap q).det| *
          g (ginibreIncidenceChart q) ∂μ =
      ∫ p in ginibreIncidenceChart '' ginibreIncidenceRankPiece m k,
        g p ∂μ := by
  have h := (integral_image_eq_integral_abs_det_fderiv_smul
    μ (measurableSet_ginibreIncidenceRankPiece m k)
    (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
    (injOn_ginibreIncidenceChart_rankPiece m k) g).symm
  simpa [smul_eq_mul] using h

/-- Ordinary signed-integral area formula on the part of one rank sheet
below an external spectral threshold. -/
theorem integral_ginibreIncidence_rankPieceBelow_eq_image
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure] (k : Fin (m + 2)) (x : ℝ)
    (g : GinibreIncidenceCoordinates m → ℝ) :
    ∫ q in ginibreIncidenceRankPieceBelow m k x,
        |(ginibreIncidenceDerivativeLinearMap q).det| *
          g (ginibreIncidenceChart q) ∂μ =
      ∫ p in ginibreIncidenceChart ''
          ginibreIncidenceRankPieceBelow m k x,
        g p ∂μ := by
  have hinj : Set.InjOn ginibreIncidenceChart
      (ginibreIncidenceRankPieceBelow m k x) :=
    (injOn_ginibreIncidenceChart_rankPiece m k).mono inter_subset_left
  have h := (integral_image_eq_integral_abs_det_fderiv_smul
    μ (measurableSet_ginibreIncidenceRankPieceBelow m k x)
    (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
    hinj g).symm
  simpa [smul_eq_mul] using h

/-- Away from the affine-boundary and critical-value sets, the truncated
`k`th rank sheet is occupied precisely when there are more than `k` real
roots below the fixed threshold. -/
theorem mem_ginibreIncidenceRankPieceBelow_image_iff_lt_belowCount
    {m : ℕ} (p : GinibreIncidenceCoordinates m)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet m)
    (hcritical :
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ)
    (k : Fin (m + 2)) (x : ℝ) :
    p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPieceBelow m k x ↔
      k.val < realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x) := by
  classical
  let P : Polynomial ℝ :=
    Matrix.charpoly (Matrix.of (ginibreCoordinatesFinMatrix p))
  have hPne : P ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  constructor
  · rintro ⟨q, ⟨hq, hqlt⟩, hchart⟩
    have hlroot : P.IsRoot (ginibreIncidenceEigenvalue q) := by
      simpa [P, hchart] using ginibreIncidenceEigenvalue_isRoot_charpoly q
    have hlmem : ginibreIncidenceEigenvalue q ∈ P.roots :=
      (Polynomial.mem_roots hPne).2 hlroot
    have hstrict := card_filter_lt_card_filter_of_mem P.roots hlmem hqlt
    have hrank : ginibreIncidenceRootRank q = k.val := hq.2
    have hrankCard :
        (P.roots.filter fun z => z < ginibreIncidenceEigenvalue q).card =
          k.val := by
      simpa [ginibreIncidenceRootRank, realEigenvalueBelowCount, P, hchart]
        using hrank
    rw [hrankCard] at hstrict
    simpa [realEigenvalueBelowCount, P] using hstrict
  · intro hk
    have hbelowLeFull :
        realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x) ≤
          realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p) := by
      unfold realEigenvalueBelowCount realEigenvalueCount
      exact Multiset.card_le_card (Multiset.filter_le _ _)
    have hkFull :
        k.val < realEigenvalueCount (m + 1)
          (ginibreCoordinatesFinMatrix p) :=
      hk.trans_le hbelowLeFull
    have himage :=
      (mem_ginibreIncidenceRankImage_iff_lt_rootCount
        p hboundary hcritical k).2 hkFull
    rcases himage with ⟨q, hq, hchart⟩
    refine ⟨q, ⟨hq, ?_⟩, hchart⟩
    by_contra hnlt
    have hxle : x ≤ ginibreIncidenceEigenvalue q := le_of_not_gt hnlt
    have hfilterLe :
        (P.roots.filter fun z => z < x).card ≤
          (P.roots.filter
            fun z => z < ginibreIncidenceEigenvalue q).card := by
      exact Multiset.card_le_card
        (Multiset.monotone_filter_right P.roots
          (fun z hz => lt_of_lt_of_le hz hxle))
    have hrank : ginibreIncidenceRootRank q = k.val := hq.2
    have hrankCard :
        (P.roots.filter fun z => z < ginibreIncidenceEigenvalue q).card =
          k.val := by
      simpa [ginibreIncidenceRootRank, realEigenvalueBelowCount, P, hchart]
        using hrank
    have hbelowLeRank :
        realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x) ≤
          k.val := by
      rw [hrankCard] at hfilterLe
      simpa [realEigenvalueBelowCount, P] using hfilterLe
    exact (Nat.not_lt_of_ge hbelowLeRank) hk

/-- Pointwise collapse of the signed regular-rank sheets above a generic
matrix to the alternating real-root count. -/
theorem sum_ginibreIncidenceRankImage_sign_eq_alternatingCount
    {m : ℕ} (p : GinibreIncidenceCoordinates m)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet m)
    (hcritical :
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ) :
    (∑ k : Fin (m + 2),
      if p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece m k then
        (-1 : ℝ) ^ k.val else 0) =
      ginibreAlternatingCount
        (realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p)) := by
  classical
  simp_rw [mem_ginibreIncidenceRankImage_iff_lt_rootCount
    p hboundary hcritical]
  apply sum_fin_ite_lt_eq_ginibreAlternatingCount
  have hdegree :
      realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p) ≤
        m + 1 := by
    unfold realEigenvalueCount
    exact (Polynomial.card_roots' _).trans_eq (by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  omega

/-- Pointwise collapse of signed rank sheets with the one-root prefix weight
to the alternating ordered-pair count. -/
theorem sum_ginibreIncidenceRankImage_pairPrefix_eq_alternatingPairCount
    {m : ℕ} (p : GinibreIncidenceCoordinates m)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet m)
    (hcritical :
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ) :
    (∑ k : Fin (m + 2),
      if p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece m k then
        (-1 : ℝ) ^ k.val * ginibreAlternatingCount k.val else 0) =
      ginibreAlternatingPairCount
        (realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p)) := by
  classical
  simp_rw [mem_ginibreIncidenceRankImage_iff_lt_rootCount
    p hboundary hcritical]
  apply sum_fin_ite_lt_eq_ginibreAlternatingPairCount
  have hdegree :
      realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p) ≤
        m + 1 := by
    unfold realEigenvalueCount
    exact (Polynomial.card_roots' _).trans_eq (by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  omega

/-- Pointwise collapse of the signed truncated rank sheets to the alternating
count of roots below the threshold. -/
theorem sum_ginibreIncidenceRankPieceBelow_image_sign_eq_alternatingCount
    {m : ℕ} (p : GinibreIncidenceCoordinates m)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet m)
    (hcritical :
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ)
    (x : ℝ) :
    (∑ k : Fin (m + 2),
      if p ∈ ginibreIncidenceChart ''
          ginibreIncidenceRankPieceBelow m k x then
        (-1 : ℝ) ^ k.val else 0) =
      ginibreAlternatingCount
        (realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x)) := by
  classical
  simp_rw [mem_ginibreIncidenceRankPieceBelow_image_iff_lt_belowCount
    p hboundary hcritical]
  apply sum_fin_ite_lt_eq_ginibreAlternatingCount
  have hle := realEigenvalueBelowCount_le
    (ginibreCoordinatesFinMatrix p, x)
  omega

end
end NumStability
