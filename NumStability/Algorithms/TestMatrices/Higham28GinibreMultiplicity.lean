/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreAtlas

/-! # Higham Chapter 28: incidence multiplicity equals real-root count

Away from the two Haar-null exceptional events proved by the incidence and
atlas modules, every real characteristic root has a unique regular affine
preimage.  Its number of roots lying strictly below it gives an explicit
finite rank label.  This module proves that the number of occupied rank sheets
is exactly the real characteristic-root count, including algebraic
multiplicity. -/

namespace NumStability

open MeasureTheory Set

noncomputable section

theorem ginibre_normalized_eigenpair
    {n : ℕ} (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (v : Fin n ⊕ Unit → ℝ) (l : ℝ)
    (heig : A.mulVec v = l • v) (hlast : v (Sum.inr ()) ≠ 0) :
    let y : Fin n → ℝ := fun i => v (Sum.inl i) / v (Sum.inr ())
    A.mulVec (ginibreAffineEigenvector y) =
      l • ginibreAffineEigenvector y := by
  dsimp only
  let c := v (Sum.inr ())
  have hc : c ≠ 0 := hlast
  have haff : ginibreAffineEigenvector (fun i => v (Sum.inl i) / c) =
      c⁻¹ • v := by
    funext i
    rcases i with i | i
    · simp [ginibreAffineEigenvector, div_eq_inv_mul]
    · rcases i with ⟨⟩
      simp [ginibreAffineEigenvector, c, hc]
  rw [haff, Matrix.mulVec_smul, heig]
  ext i
  simp [Pi.smul_apply]
  ring

theorem exists_regular_incidence_preimage_of_root
    {n : ℕ} (p : GinibreIncidenceCoordinates n) (l : ℝ)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet n)
    (hcritical : p ∉
      ginibreIncidenceChart '' (ginibreIncidenceRegularSet n)ᶜ)
    (hroot : (ginibreCoordinatesMatrix p).charpoly.IsRoot l) :
    ∃ q : GinibreIncidenceCoordinates n,
      q ∈ ginibreIncidenceRegularSet n ∧
      ginibreIncidenceChart q = p ∧
      ginibreIncidenceEigenvalue q = l := by
  have hhas : Module.End.HasEigenvalue
      (Matrix.toLin' (ginibreCoordinatesMatrix p)) l := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,
      Matrix.charpoly_toLin']
    exact hroot
  obtain ⟨v, hv⟩ := hhas.exists_hasEigenvector
  have hv_ne : v ≠ 0 := hv.2
  have heig : (ginibreCoordinatesMatrix p).mulVec v = l • v := by
    simpa [Matrix.toLin'_apply] using hv.apply_eq_smul
  have hlast : v (Sum.inr ()) ≠ 0 := by
    intro hz
    apply hboundary
    exact ⟨v, l, hv_ne, heig, hz⟩
  let y : Fin n → ℝ := fun i => v (Sum.inl i) / v (Sum.inr ())
  let q : GinibreIncidenceCoordinates n := (p.1, y)
  have heig' : (ginibreCoordinatesMatrix p).mulVec
      (ginibreAffineEigenvector y) = l • ginibreAffineEigenvector y :=
    ginibre_normalized_eigenpair (ginibreCoordinatesMatrix p) v l heig hlast
  have hlam : ginibreIncidenceEigenvalue q = l :=
    ginibreIncidenceEigenvalue_eq_of_affine_eigenpair p y l heig'
  have hchart : ginibreIncidenceChart q = p := by
    apply (ginibreIncidenceChart_fiber_iff_affine_eigenpair p y).2
    rw [hlam]
    exact heig'
  have hreg : q ∈ ginibreIncidenceRegularSet n := by
    by_contra hq
    apply hcritical
    exact ⟨q, hq, hchart⟩
  exact ⟨q, hreg, hchart, hlam⟩

/-- Number of regular affine-chart sheets above a matrix coordinate point,
after splitting the chart by real-root rank. -/
noncomputable def ginibreRegularFiberMultiplicity (n : ℕ)
    (p : GinibreIncidenceCoordinates n) : ℕ := by
  classical
  exact ∑ k : Fin (n + 2),
    if p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece n k then 1 else 0

theorem ginibreRegularFiberMultiplicity_eq_realEigenvalueCount
    {n : ℕ} (p : GinibreIncidenceCoordinates n)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet n)
    (hcritical : p ∉
      ginibreIncidenceChart '' (ginibreIncidenceRegularSet n)ᶜ) :
    ginibreRegularFiberMultiplicity n p =
      realEigenvalueCount (n + 1) (ginibreCoordinatesFinMatrix p) := by
  classical
  let P := Matrix.charpoly (Matrix.of (ginibreCoordinatesFinMatrix p))
  have hP : P ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  let r : ℝ → Fin (n + 2) := fun l =>
    ⟨realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, l), by
      have hle := realEigenvalueBelowCount_le
        (ginibreCoordinatesFinMatrix p, l)
      omega⟩
  let R : Finset ℝ := P.roots.toFinset
  let K : Finset (Fin (n + 2)) := Finset.univ.filter fun k =>
    p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece n k
  have hpre (l : ℝ) (hl : l ∈ P.roots) :
      ∃ q : GinibreIncidenceCoordinates n,
        q ∈ ginibreIncidenceRegularSet n ∧
        ginibreIncidenceChart q = p ∧
        ginibreIncidenceEigenvalue q = l := by
    apply exists_regular_incidence_preimage_of_root p l hboundary hcritical
    rw [← ginibreCoordinatesFinMatrix_charpoly]
    exact (Polynomial.mem_roots hP).1 hl
  have hKR : K = R.image r := by
    ext k
    constructor
    · intro hk
      rcases (Finset.mem_filter.1 hk).2 with ⟨q, hq, hchart⟩
      let l := ginibreIncidenceEigenvalue q
      have hlroot : P.IsRoot l := by
        simpa [P, hchart] using ginibreIncidenceEigenvalue_isRoot_charpoly q
      have hlR : l ∈ R := by
        simp only [R, Multiset.mem_toFinset]
        exact (Polynomial.mem_roots hP).2 hlroot
      apply Finset.mem_image.2
      refine ⟨l, hlR, ?_⟩
      apply Fin.ext
      simpa [r, l, ginibreIncidenceRootRank, hchart] using hq.2
    · intro hk
      rcases Finset.mem_image.1 hk with ⟨l, hlR, rfl⟩
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_⟩
      have hl : l ∈ P.roots := by
        simpa [R] using hlR
      obtain ⟨q, hreg, hchart, hlam⟩ := hpre l hl
      refine ⟨q, ?_, hchart⟩
      refine ⟨hreg, ?_⟩
      simpa [r, ginibreIncidenceRootRank, hchart, hlam]
  have hrinj : Set.InjOn r (R : Set ℝ) := by
    intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have haP : a ∈ P.roots := by simpa [R] using ha
      have hstrict := card_filter_lt_card_filter_of_mem P.roots haP hlt
      have : (r a).val < (r b).val := by
        simpa [r, realEigenvalueBelowCount, P] using hstrict
      rw [hab] at this
      exact (lt_irrefl _ this)
    · have hbP : b ∈ P.roots := by simpa [R] using hb
      have hstrict := card_filter_lt_card_filter_of_mem P.roots hbP hgt
      have : (r b).val < (r a).val := by
        simpa [r, realEigenvalueBelowCount, P] using hstrict
      rw [hab] at this
      exact (lt_irrefl _ this)
  have hnodup : P.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro l
    by_cases hl : l ∈ P.roots
    · obtain ⟨q, hreg, hchart, hlam⟩ := hpre l hl
      have hcount :=
        (mem_ginibreIncidenceRegularSet_iff_root_count_eq_one q).1 hreg
      have hchar : P = (ginibreIncidenceMatrix q).charpoly := by
        change (Matrix.of (ginibreCoordinatesFinMatrix p)).charpoly =
          (ginibreIncidenceMatrix q).charpoly
        rw [ginibreCoordinatesFinMatrix_charpoly]
        rw [← hchart, ginibreCoordinatesMatrix_chart]
      rw [hchar]
      simpa [hlam] using hcount.le
    · rw [Multiset.count_eq_zero.2 hl]
      omega
  have hcardImage : (R.image r).card = R.card :=
    Finset.card_image_iff.mpr hrinj
  calc
    ginibreRegularFiberMultiplicity n p = K.card := by
      simp [ginibreRegularFiberMultiplicity, K, Finset.sum_boole]
    _ = (R.image r).card := by rw [hKR]
    _ = R.card := hcardImage
    _ = P.roots.card := by
      simpa [R] using Multiset.toFinset_card_of_nodup hnodup
    _ = realEigenvalueCount (n + 1) (ginibreCoordinatesFinMatrix p) := rfl

end
end NumStability
