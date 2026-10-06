import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.RootMeasurability.GinibreRoots
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.SignedIncidence.GinibreSignedRank

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28GinibreRoots, NumStability.Algorithms.TestMatrices.Higham28GinibreSignedRank under the R09/R10 completion waves; reusable-tier destination per the reviewed route ledger.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section
namespace NumStability


open MeasureTheory Polynomial

private local instance instMeasurableSpaceGinibreRawMatrix_relocated_RealRootCounting (n : ℕ) : MeasurableSpace (GinibreRawMatrix n) := MeasurableSpace.pi

private local instance instOpensMeasurableSpaceGinibreRawMatrix_relocated_RealRootCounting (n : ℕ) : OpensMeasurableSpace (GinibreRawMatrix n) := Pi.opensMeasurableSpace

private local instance instBorelSpaceGinibreRawMatrix_relocated_RealRootCounting (n : ℕ) : BorelSpace (GinibreRawMatrix n) := Pi.borelSpace

private local instance instStandardBorelSpaceGinibreRawMatrix_relocated_RealRootCounting (n : ℕ) : StandardBorelSpace (GinibreRawMatrix n) :=
  StandardBorelSpace.pi_countable

private local instance instMeasurableSpaceForallFinComplex_numStability_relocated_RealRootCounting (n : ℕ) : MeasurableSpace (Fin n → ℂ) := MeasurableSpace.pi

private local instance instOpensMeasurableSpaceForallFinComplex_numStability_relocated_RealRootCounting (n : ℕ) : OpensMeasurableSpace (Fin n → ℂ) := Pi.opensMeasurableSpace

private local instance instBorelSpaceForallFinComplex_numStability_relocated_RealRootCounting (n : ℕ) : BorelSpace (Fin n → ℂ) := Pi.borelSpace

private local instance instStandardBorelSpaceForallFinComplex_numStability_relocated_RealRootCounting (n : ℕ) : StandardBorelSpace (Fin n → ℂ) :=
  StandardBorelSpace.pi_countable

private theorem card_filter_le_card_filter_of_imp
    {α : Type*} (s : Multiset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q]
    (hpq : ∀ x, p x → q x) :
    (s.filter p).card ≤ (s.filter q).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
      by_cases hpx : p x
      · have hqx : q x := hpq x hpx
        simpa [hpx, hqx] using ih
      · by_cases hqx : q x
        · simpa [hpx, hqx] using ih.trans (Nat.le_succ _)
        · simpa [hpx, hqx] using ih

/-- A root lying strictly between two thresholds forces a strict increase
of the number of roots below the threshold. -/
theorem card_filter_lt_card_filter_of_mem
    (s : Multiset ℝ) {a b : ℝ} (ha : a ∈ s) (hab : a < b) :
    (s.filter fun x => x < a).card < (s.filter fun x => x < b).card := by
  classical
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  have hmono :
      (t.filter fun x => x < a).card ≤ (t.filter fun x => x < b).card :=
    card_filter_le_card_filter_of_imp t (fun x => x < a) (fun x => x < b)
      (fun _ hx => hx.trans hab)
  simpa [hab, lt_irrefl] using Nat.lt_succ_of_le hmono

end NumStability
end

noncomputable section
namespace NumStability
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

end NumStability
end
