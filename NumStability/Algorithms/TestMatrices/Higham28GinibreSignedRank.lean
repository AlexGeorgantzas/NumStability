/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreMultiplicity
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic

/-! # Higham Chapter 28: signed root-rank decomposition

This file retains the parity of the rank of a distinguished real root.  The
finite alternating-rank identity replaces the unsigned root count by one- and
two-root signed sums.  The polynomial results below identify the rank sign
with the sign of the deflated characteristic determinant, allowing an
incidence Jacobian's absolute value to be removed at regular points.
-/

namespace NumStability

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

/-- Alternating sum over the occupied root ranks `0, ..., r-1`. -/
def ginibreAlternatingCount (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, (-1 : ℝ) ^ j

/-- Alternating sum over ordered pairs of occupied root ranks. -/
def ginibreAlternatingPairCount (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r,
    ∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)

private theorem two_mul_alternating_range (r : ℕ) :
    2 * (∑ i ∈ Finset.range r, (-1 : ℝ) ^ i) =
      1 - (-1 : ℝ) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

private theorem one_eq_rankSign_sub_pairPrefix (j : ℕ) :
    (1 : ℝ) = (-1 : ℝ) ^ j -
      2 * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j) := by
  rw [show (∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)) =
      (-1 : ℝ) ^ j * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i by
    simp_rw [pow_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  have h := two_mul_alternating_range j
  have hsign : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  symm
  calc
    (-1 : ℝ) ^ j -
        2 * ((-1 : ℝ) ^ j * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i) =
        (-1 : ℝ) ^ j -
          (-1 : ℝ) ^ j *
            (2 * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i) := by ring
    _ = (-1 : ℝ) ^ j - (-1 : ℝ) ^ j * (1 - (-1 : ℝ) ^ j) := by
      rw [h]
    _ = ((-1 : ℝ) ^ j) ^ 2 := by ring
    _ = 1 := hsign

/-- Every finite unsigned count is a one-rank alternating sum minus twice
the corresponding alternating pair sum. -/
theorem natCast_eq_alternating_sub_two_pairs (r : ℕ) :
    (r : ℝ) =
      ginibreAlternatingCount r -
        2 * ginibreAlternatingPairCount r := by
  unfold ginibreAlternatingCount ginibreAlternatingPairCount
  calc
    (r : ℝ) = ∑ _j ∈ Finset.range r, (1 : ℝ) := by simp
    _ = ∑ j ∈ Finset.range r,
        ((-1 : ℝ) ^ j -
          2 * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact one_eq_rankSign_sub_pairPrefix j
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-! ## The sign of a real polynomial between its roots -/

private theorem Polynomial.eval_pos_of_monic_of_roots_eq_zero
    {P : Polynomial ℝ} (hmonic : P.Monic) (hroots : P.roots = 0)
    (x : ℝ) : 0 < P.eval x := by
  rcases P.natDegree.eq_zero_or_pos with hdegree | hdegree
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hmonic hdegree]
    simp
  · have hdegree' : 0 < P.degree := by
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero]
      exact_mod_cast hdegree
    have htend : Tendsto (fun y : ℝ => P.eval y) atTop atTop :=
      P.tendsto_atTop_of_leadingCoeff_nonneg hdegree' (by
        rw [hmonic.leadingCoeff]
        norm_num)
    have hevent : ∀ᶠ y : ℝ in atTop, (1 : ℝ) ≤ P.eval y :=
      htend.eventually (eventually_ge_atTop 1)
    rcases (eventually_atTop.1 hevent) with ⟨y, hy⟩
    have hypos : 0 < P.eval y :=
      lt_of_lt_of_le zero_lt_one (hy y le_rfl)
    have hxne : P.eval x ≠ 0 := by
      intro hx
      have hxroot : P.IsRoot x := hx
      have hxmem : x ∈ P.roots :=
        (Polynomial.mem_roots hmonic.ne_zero).2 hxroot
      simpa [hroots] using hxmem
    have hxnonneg : 0 ≤ P.eval x := by
      by_contra hx
      have hxneg : P.eval x < 0 := lt_of_not_ge hx
      have hzrange : (0 : ℝ) ∈ Set.range (fun z : ℝ => P.eval z) :=
        mem_range_of_exists_le_of_exists_ge P.continuous
          ⟨x, hxneg.le⟩ ⟨y, hypos.le⟩
      rcases hzrange with ⟨z, hz⟩
      have hzroot : P.IsRoot z := hz
      have hzmem : z ∈ P.roots :=
        (Polynomial.mem_roots hmonic.ne_zero).2 hzroot
      simpa [hroots] using hzmem
    exact hxnonneg.lt_of_ne' hxne

private theorem Polynomial.exists_isRoot_of_monic_of_odd_natDegree
    {P : Polynomial ℝ} (hmonic : P.Monic) (hodd : Odd P.natDegree) :
    ∃ x : ℝ, P.IsRoot x := by
  have hdegreeNat : 0 < P.natDegree := hodd.pos
  have hdegree : 0 < P.degree := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero]
    exact_mod_cast hdegreeNat
  let Q : Polynomial ℝ := P.comp (-Polynomial.X)
  have hQdegree : 0 < Q.degree := by
    simpa only [Q, Polynomial.degree_comp_neg_X] using hdegree
  have hQlead : Q.leadingCoeff = -1 := by
    simp only [Q, Polynomial.comp_neg_X_leadingCoeff_eq,
      hmonic.leadingCoeff, mul_one, hodd.neg_one_pow]
  have hposTend : Tendsto (fun z : ℝ => P.eval z) atTop atTop :=
    P.tendsto_atTop_of_leadingCoeff_nonneg hdegree (by
      rw [hmonic.leadingCoeff]
      norm_num)
  have hnegTend : Tendsto (fun z : ℝ => Q.eval z) atTop atBot :=
    Q.tendsto_atBot_of_leadingCoeff_nonpos hQdegree (by
      rw [hQlead]
      norm_num)
  have hposEvent : ∀ᶠ z : ℝ in atTop, (1 : ℝ) ≤ P.eval z :=
    hposTend.eventually (eventually_ge_atTop 1)
  have hnegEvent : ∀ᶠ z : ℝ in atTop, Q.eval z ≤ (-1 : ℝ) :=
    hnegTend.eventually (eventually_le_atBot (-1))
  rcases (eventually_atTop.1 hposEvent) with ⟨a, ha⟩
  rcases (eventually_atTop.1 hnegEvent) with ⟨b, hb⟩
  have hapos : 0 < P.eval a :=
    lt_of_lt_of_le zero_lt_one (ha a le_rfl)
  have hbneg : P.eval (-b) < 0 := by
    have hb' := hb b le_rfl
    have hQeval : Q.eval b = P.eval (-b) := by
      simp [Q]
    rw [hQeval] at hb'
    linarith
  have hzrange : (0 : ℝ) ∈ Set.range (fun z : ℝ => P.eval z) :=
    mem_range_of_exists_le_of_exists_ge P.continuous
      ⟨-b, hbneg.le⟩ ⟨a, hapos.le⟩
  rcases hzrange with ⟨z, hz⟩
  exact ⟨z, hz⟩

/-- For a real monic polynomial, the sign of
`(-1)^degree * P(x)` is the parity of the number of real roots strictly below
`x`.  Roots are counted with algebraic multiplicity. -/
theorem Polynomial.negOnePow_card_roots_lt_mul_abs_eval
    {P : Polynomial ℝ} (hmonic : P.Monic) {x : ℝ}
    (hx : ¬P.IsRoot x) :
    (-1 : ℝ) ^ (P.roots.filter fun z => z < x).card *
        |(-1 : ℝ) ^ P.natDegree * P.eval x| =
      (-1 : ℝ) ^ P.natDegree * P.eval x := by
  induction hcard : P.roots.card using Nat.strong_induction_on
      generalizing P x with
  | h d ih =>
      by_cases hroots : P.roots = 0
      · have heven : Even P.natDegree := by
          rcases Nat.even_or_odd P.natDegree with heven | hodd
          · exact heven
          · obtain ⟨r, hr⟩ :=
              Polynomial.exists_isRoot_of_monic_of_odd_natDegree hmonic hodd
            have hrmem : r ∈ P.roots :=
              (Polynomial.mem_roots hmonic.ne_zero).2 hr
            simpa [hroots] using hrmem
        have hsign : (-1 : ℝ) ^ P.natDegree = 1 :=
          heven.neg_one_pow
        have hpos : 0 < (-1 : ℝ) ^ P.natDegree * P.eval x := by
          rw [hsign, one_mul]
          exact Polynomial.eval_pos_of_monic_of_roots_eq_zero
            hmonic hroots x
        have hfilter : (P.roots.filter fun z => z < x).card = 0 := by
          simp [hroots]
        rw [hfilter, pow_zero, one_mul, abs_of_pos hpos]
      · obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hroots
        let Q : Polynomial ℝ := P /ₘ (Polynomial.X - Polynomial.C r)
        have hrroot : P.IsRoot r := Polynomial.isRoot_of_mem_roots hr
        have hfactor : (Polynomial.X - Polynomial.C r) * Q = P := by
          exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hrroot
        have hdegreePos : 0 < P.natDegree := by
          apply Nat.pos_of_ne_zero
          intro hzero
          have hPone : P = 1 :=
            Polynomial.eq_one_of_monic_natDegree_zero hmonic hzero
          have : ¬(1 : Polynomial ℝ).IsRoot r := by simp
          exact this (hPone ▸ hrroot)
        have hdegreeNe : P.degree ≠ 0 := by
          rw [Polynomial.degree_eq_natDegree hmonic.ne_zero]
          exact_mod_cast hdegreePos.ne'
        have hQmonic : Q.Monic := by
          rw [Polynomial.Monic,
            Polynomial.leadingCoeff_divByMonic_X_sub_C P hdegreeNe r,
            hmonic.leadingCoeff]
        have hQne : Q ≠ 0 := hQmonic.ne_zero
        have hrootsFactor : P.roots = {r} + Q.roots := by
          rw [← hfactor, Polynomial.roots_mul
            (mul_ne_zero (Polynomial.X_sub_C_ne_zero r) hQne),
            Polynomial.roots_X_sub_C]
        have hQcard : Q.roots.card < d := by
          rw [hrootsFactor, Multiset.card_add, Multiset.card_singleton] at hcard
          omega
        have hxQ : ¬Q.IsRoot x := by
          intro hxQ
          apply hx
          rw [← hfactor, Polynomial.IsRoot, Polynomial.eval_mul, hxQ,
            mul_zero]
        have ihQ := ih Q.roots.card hQcard hQmonic hxQ rfl
        have hdegree : P.natDegree = Q.natDegree + 1 := by
          rw [← hfactor, Polynomial.natDegree_mul
            (Polynomial.X_sub_C_ne_zero r) hQne,
            Polynomial.natDegree_X_sub_C]
          omega
        have heval : P.eval x = (x - r) * Q.eval x := by
          rw [← hfactor, Polynomial.eval_mul]
          simp
        have hsignedEval :
            (-1 : ℝ) ^ P.natDegree * P.eval x =
              (r - x) * ((-1 : ℝ) ^ Q.natDegree * Q.eval x) := by
          rw [hdegree, heval, pow_succ]
          ring
        have hrne : r ≠ x := by
          intro hrx
          subst x
          exact hx hrroot
        rcases lt_or_gt_of_ne hrne with hrx | hxr
        · have hcount :
              (P.roots.filter fun z => z < x).card =
                (Q.roots.filter fun z => z < x).card + 1 := by
            rw [hrootsFactor, Multiset.filter_add, Multiset.card_add]
            rw [Multiset.filter_singleton, if_pos hrx]
            simp [add_comm]
          rw [hcount, hsignedEval, abs_mul, abs_of_neg (sub_neg.mpr hrx)]
          rw [pow_succ]
          calc
            (-1 : ℝ) ^ (Q.roots.filter fun z => z < x).card * -1 *
                (-(r - x) *
                  |(-1 : ℝ) ^ Q.natDegree * Q.eval x|) =
                (r - x) *
                  ((-1 : ℝ) ^ (Q.roots.filter fun z => z < x).card *
                    |(-1 : ℝ) ^ Q.natDegree * Q.eval x|) := by ring
            _ = (r - x) * ((-1 : ℝ) ^ Q.natDegree * Q.eval x) := by
              rw [ihQ]
        · have hcount :
              (P.roots.filter fun z => z < x).card =
                (Q.roots.filter fun z => z < x).card := by
            rw [hrootsFactor, Multiset.filter_add, Multiset.card_add]
            rw [Multiset.filter_singleton, if_neg (not_lt_of_ge hxr.le)]
            simp
          rw [hcount, hsignedEval, abs_mul, abs_of_pos (sub_pos.mpr hxr)]
          calc
            (-1 : ℝ) ^ (Q.roots.filter fun z => z < x).card *
                ((r - x) *
                  |(-1 : ℝ) ^ Q.natDegree * Q.eval x|) =
                (r - x) *
                  ((-1 : ℝ) ^ (Q.roots.filter fun z => z < x).card *
                    |(-1 : ℝ) ^ Q.natDegree * Q.eval x|) := by ring
            _ = (r - x) * ((-1 : ℝ) ^ Q.natDegree * Q.eval x) := by
              rw [ihQ]

/-! ## Removing the incidence Jacobian's absolute value -/

/-- At a regular incidence point, the parity of the marked root's rank is
exactly the sign of the deflated characteristic determinant. -/
theorem neg_one_pow_rootRank_mul_abs_det
    {m : ℕ} (q : GinibreIncidenceCoordinates m)
    (hq : q ∈ ginibreIncidenceRegularSet m) :
    (-1 : ℝ) ^ ginibreIncidenceRootRank q *
        |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det| =
      (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det := by
  let D : RSqMat m := ginibreIncidenceDeflatedBlock q
  let l : ℝ := ginibreIncidenceEigenvalue q
  let P : Polynomial ℝ := D.charpoly
  have hPmonic : P.Monic := Matrix.charpoly_monic D
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hx : ¬P.IsRoot l := by
    intro hroot
    have heval : P.eval l = 0 := hroot
    rw [show P = D.charpoly by rfl, Matrix.eval_charpoly] at heval
    have htangent : ginibreIncidenceTangentMatrix q =
        Matrix.scalar (Fin m) l - D := by
      ext i j
      simp [ginibreIncidenceTangentMatrix, D, l, Matrix.scalar_apply,
        Matrix.one_apply, Matrix.diagonal_apply]
    change (ginibreIncidenceTangentMatrix q).det ≠ 0 at hq
    apply hq
    rw [htangent]
    exact heval
  have hlinear :
      (Polynomial.X - Polynomial.C l : Polynomial ℝ) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero l
  have hfullRoots :
      (ginibreIncidenceMatrix q).charpoly.roots = P.roots + {l} := by
    rw [ginibreIncidenceMatrix_charpoly_factor]
    change (D.charpoly * (Polynomial.X - Polynomial.C l)).roots = _
    rw [Polynomial.roots_mul (mul_ne_zero hPne hlinear),
      Polynomial.roots_X_sub_C]
  have hrank : ginibreIncidenceRootRank q =
      (P.roots.filter fun z => z < l).card := by
    unfold ginibreIncidenceRootRank realEigenvalueBelowCount
    rw [ginibreCoordinatesFinMatrix_charpoly,
      ginibreCoordinatesMatrix_chart, hfullRoots,
      Multiset.filter_add, Multiset.card_add,
      Multiset.filter_singleton, if_neg (lt_irrefl l)]
    rfl
  have hdet :
      (-1 : ℝ) ^ P.natDegree * P.eval l =
        (D - l • (1 : RSqMat m)).det := by
    have hnat : P.natDegree = m := by
      change D.charpoly.natDegree = m
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    rw [show P = D.charpoly by rfl, Matrix.eval_charpoly, hnat]
    have hneg : D - l • (1 : RSqMat m) =
        -(Matrix.scalar (Fin m) l - D) := by
      ext i j
      simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
    rw [hneg, Matrix.det_neg, Fintype.card_fin]
  have hpoly :=
    Polynomial.negOnePow_card_roots_lt_mul_abs_eval hPmonic hx
  rw [hrank, ← hdet]
  exact hpoly

/-- Away from the existing affine-boundary and critical-value exceptional
sets, the occupied incidence rank sheets are precisely the ranks strictly
below the full real-root count. -/
theorem mem_ginibreIncidenceRankImage_iff_lt_rootCount
    {m : ℕ} (p : GinibreIncidenceCoordinates m)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet m)
    (hcritical :
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ)
    (k : Fin (m + 2)) :
    p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece m k ↔
      k.val <
        realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p) := by
  classical
  let P : Polynomial ℝ :=
    Matrix.charpoly (Matrix.of (ginibreCoordinatesFinMatrix p))
  let count : ℕ :=
    realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p)
  let K : Finset (Fin (m + 2)) := Finset.univ.filter fun j =>
    p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece m j
  have hPne : P ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hcountDegree : count ≤ m + 1 := by
    change P.roots.card ≤ m + 1
    exact (Polynomial.card_roots' P).trans_eq (by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  let countFin : Fin (m + 2) := ⟨count, by omega⟩
  let S : Finset (Fin (m + 2)) := Finset.Iio countFin
  have hKS : K ⊆ S := by
    intro j hj
    have hjImage := (Finset.mem_filter.1 hj).2
    rcases hjImage with ⟨q, hq, hchart⟩
    have hreg : q ∈ ginibreIncidenceRegularSet m := hq.1
    have hrank : ginibreIncidenceRootRank q = j.val := hq.2
    let l : ℝ := ginibreIncidenceEigenvalue q
    have hlroot : P.IsRoot l := by
      simpa [P, l, hchart] using ginibreIncidenceEigenvalue_isRoot_charpoly q
    have hlmem : l ∈ P.roots :=
      (Polynomial.mem_roots hPne).2 hlroot
    have hrankCard :
        (P.roots.filter fun z => z < l).card = j.val := by
      simpa [ginibreIncidenceRootRank, realEigenvalueBelowCount, P, l,
        hchart] using hrank
    have hstrict := card_filter_lt_card_filter_of_mem P.roots hlmem
      (show l < l + 1 by linarith)
    have hfilterLe :
        (P.roots.filter fun z => z < l + 1).card ≤ P.roots.card :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    have hjCount : j.val < count := by
      change j.val < P.roots.card
      rw [← hrankCard]
      exact hstrict.trans_le hfilterLe
    simpa [S, countFin] using hjCount
  have hKcard : K.card = count := by
    have hmult := ginibreRegularFiberMultiplicity_eq_realEigenvalueCount
      p hboundary hcritical
    simpa [K, count, ginibreRegularFiberMultiplicity, Finset.sum_boole]
      using hmult
  have hScard : S.card = count := by
    simp [S, countFin, Fin.card_Iio]
  have hKS_eq : K = S :=
    Finset.eq_of_subset_of_card_le hKS (by rw [hScard, hKcard])
  have hfinal : k ∈ K ↔ k.val < count := by
    rw [hKS_eq]
    simp only [S, Finset.mem_Iio]
    change k.val < count ↔ k.val < count
    rfl
  simpa [K, count] using hfinal

/-- Single-rank-sheet form of the incidence area identity.  Keeping this
identity before summing the sheets is what permits alternating signs to be
attached outside the nonnegative change-of-variables theorem. -/
theorem lintegral_ginibreIncidence_rankPiece_eq_image
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure] (k : Fin (m + 2))
    (g : GinibreIncidenceCoordinates m → ℝ≥0∞) :
    ∫⁻ q in ginibreIncidenceRankPiece m k,
        ENNReal.ofReal |(ginibreIncidenceDerivativeLinearMap q).det| *
          g (ginibreIncidenceChart q) ∂μ =
      ∫⁻ p in ginibreIncidenceChart '' ginibreIncidenceRankPiece m k,
        g p ∂μ := by
  exact (lintegral_image_eq_lintegral_abs_det_fderiv_mul
    μ (measurableSet_ginibreIncidenceRankPiece m k)
    (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
    (injOn_ginibreIncidenceChart_rankPiece m k) g).symm

end
end NumStability
