import HighamBench.P19Definitions

namespace HighamBench

private theorem p19VecNorm2_eq_euclideanNorm {n : ℕ} (x : P19Vector n) :
    p19VecNorm2 x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [p19VecNorm2, p19VecNorm2Sq, Real.norm_eq_abs, sq_abs]

private theorem p19VecNorm2_add_le {n : ℕ} (x y : P19Vector n) :
    p19VecNorm2 (x + y) ≤ p19VecNorm2 x + p19VecNorm2 y := by
  simp only [p19VecNorm2_eq_euclideanNorm]
  exact norm_add_le _ _

private theorem p19VecNorm2_nonneg {n : ℕ} (x : P19Vector n) :
    0 ≤ p19VecNorm2 x := by
  rw [p19VecNorm2_eq_euclideanNorm]
  exact norm_nonneg _

private theorem p19VecNorm2_pos {n : ℕ} {x : P19Vector n} (hx : x ≠ 0) :
    0 < p19VecNorm2 x := by
  rw [p19VecNorm2_eq_euclideanNorm, norm_pos_iff]
  intro hzero
  apply hx
  apply WithLp.toLp_injective 2
  simpa only [WithLp.toLp_zero] using hzero

private theorem p19FrobNorm_nonneg {m k : ℕ} (A : P19RectMatrix m k) :
    0 ≤ p19FrobNorm A := by
  exact @norm_nonneg _
    Matrix.frobeniusNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup A

private theorem p19OpNorm2_nonneg {n : ℕ} (A : P19Matrix n) :
    0 ≤ p19OpNorm2 A := by
  exact @norm_nonneg _
    Matrix.instL2OpNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup A

private theorem p19StaticKappa_nonneg (choice : P19StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P19Matrix n) :
    0 ≤ p19StaticKappa choice A Ainv := by
  cases choice with
  | frobenius =>
      exact mul_nonneg (p19FrobNorm_nonneg _) (p19FrobNorm_nonneg _)
  | inducedTwo =>
      exact mul_nonneg (p19OpNorm2_nonneg _) (p19OpNorm2_nonneg _)

theorem P19MGSSelectionLaw.exists_terminal_or_near
    {n : ℕ} {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (mgs : P19MGSSelectionLaw family) :
    ∃ k : P19Theorem31Dimension n,
      p19IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p19MGSNearDependence (family.iteration k)) := by
  have hprefix : ∀ (k : ℕ) (hkpos : 0 < k) (hkle : k ≤ n),
      p19IterationWellConditioned
          (family.iteration ⟨k, hkpos, hkle⟩) ∨
        ∃ j : P19Theorem31Dimension n,
          j.1 < k ∧
            p19IterationWellConditioned (family.iteration j) ∧
              p19MGSNearDependence (family.iteration j) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hkpos hkle
        by_cases hkone : k = 1
        · subst k
          left
          exact mgs.first_dimension_good
        · have hprevpos : 0 < k - 1 := by omega
          have hprevle : k - 1 ≤ n := by omega
          rcases ih (k - 1) (by omega) hprevpos hprevle with hprev | hnear
          · let prev : P19Theorem31Dimension n :=
                ⟨k - 1, hprevpos, hprevle⟩
            have hkprevlt : k - 1 < n := by omega
            let next : P19Theorem31Dimension n :=
              ⟨(k - 1) + 1, Nat.succ_pos _, Nat.succ_le_iff.mpr hkprevlt⟩
            by_cases hcurrent :
                p19IterationWellConditioned (family.iteration next)
            · left
              have hnext : next = ⟨k, hkpos, hkle⟩ := by
                apply Subtype.ext
                simp only [next]
                omega
              rw [hnext] at hcurrent
              exact hcurrent
            · right
              refine ⟨prev, by simp only [prev]; omega, hprev, ?_⟩
              exact mgs.loss_implies_near_dependence (k - 1) hprevpos
                hkprevlt hcurrent
          · right
            rcases hnear with ⟨j, hjlt, hjwell, hjnear⟩
            exact ⟨j, by omega, hjwell, hjnear⟩
  have hnpos := family.system.dimension_pos
  rcases hprefix n hnpos (le_refl n) with hlast | hnear
  · exact ⟨⟨n, hnpos, le_refl n⟩, hlast, Or.inl rfl⟩
  · rcases hnear with ⟨j, hjlt, hjwell, hjnear⟩
    exact ⟨j, hjwell, Or.inr hjnear⟩

theorem p19_t3_right_flexible_attainable_forward_error
    {n : ℕ} (semantics : P19FirstOrderSemantics)
    (choice : P19StaticSquareKappaChoice) :
    (∀ (right : P19StaticRightFamily n semantics)
        (mgs : P19MGSSelectionLaw right.family)
        (appendix : P19StaticRightAppendixCTheory choice right)
        (applicability : ∀ k : P19Theorem31Dimension n,
          p19IterationWellConditioned (right.family.iteration k) →
          (k.1 = n ∨ p19MGSNearDependence (right.family.iteration k)) →
          P19StaticRightConditions choice (right.iteration k)),
      ∃ k : P19Theorem31Dimension n,
        p19IterationWellConditioned (right.family.iteration k) ∧
          p19FirstOrderLe semantics
            (p19ForwardError right.family.system.xExact
              (right.family.iteration k).xHat)
            ((right.family.iteration k).dimensionFactor *
              p19StaticRightAttainableEnvelope choice right.preconditioner
                (right.iteration k).core.ug
                (right.iteration k).core.um
                (right.iteration k).core.ua
                (right.iteration k).core.etaR
                (right.iteration k).core.rhoAR)) ∧
      (∀ (flexible : P19StaticFlexibleFamily n semantics)
          (mgs : P19MGSSelectionLaw flexible.family)
          (appendix : P19StaticFlexibleAppendixDTheory choice flexible)
          (applicability : ∀ k : P19Theorem31Dimension n,
            p19IterationWellConditioned (flexible.family.iteration k) →
            (k.1 = n ∨
              p19MGSNearDependence (flexible.family.iteration k)) →
            P19StaticFlexibleConditions choice (flexible.iteration k)),
        ∃ k : P19Theorem31Dimension n,
          p19IterationWellConditioned (flexible.family.iteration k) ∧
            p19FirstOrderLe semantics
              (p19ForwardError flexible.family.system.xExact
                (flexible.family.iteration k).xHat)
              ((flexible.family.iteration k).dimensionFactor *
                p19StaticFlexibleAttainableEnvelope choice
                  flexible.preconditioner
                  (flexible.iteration k).core.ug
                  (flexible.iteration k).core.ua
                  (flexible.iteration k).core.rhoAR)) ∧
        ∀ (family : P19Theorem31Family n semantics)
          (preconditioner : P19StaticFixedRightPreconditioner family)
          (ug um ua etaR rhoAR : ℝ),
          p19StaticRightAttainableEnvelope choice preconditioner
              ug um ua etaR rhoAR =
            p19StaticFlexibleAttainableEnvelope choice preconditioner
                ug ua rhoAR +
              um * etaR *
                p19StaticRightPreconditionerKappa choice preconditioner := by
  -- PROOF_START P19-T3-H001
  refine ⟨?_, ?_, ?_⟩
  · intro right mgs appendix applicability
    obtain ⟨k, hwell, hstop⟩ := mgs.exists_terminal_or_near
    let conditions := applicability k hwell hstop
    let expansion := appendix.expansion k hwell hstop conditions
    have hx : right.family.system.xExact ≠ 0 := by
      intro hxzero
      apply right.family.system.b_nonzero
      rw [← right.family.system.exact_solution, hxzero]
      ext i
      simp [p19MatVec]
    have hdenom : 0 < p19VecNorm2 right.family.system.xExact :=
      p19VecNorm2_pos hx
    have hop :
        0 ≤ p19StaticRightOperatorKappa choice right.preconditioner :=
      p19StaticKappa_nonneg choice _ _
    have hpre :
        0 ≤ p19StaticRightPreconditionerKappa choice right.preconditioner :=
      p19StaticKappa_nonneg choice _ _
    have hsys : 0 ≤ p19StaticSystemKappa choice right.family :=
      p19StaticKappa_nonneg choice _ _
    have hug : 0 ≤ (right.iteration k).core.ug :=
      conditions.core.parameters_nonneg.1
    have hum : 0 ≤ (right.iteration k).core.um :=
      conditions.core.parameters_nonneg.2.1
    have hua : 0 ≤ (right.iteration k).core.ua :=
      conditions.core.parameters_nonneg.2.2.1
    have heta : 0 ≤ (right.iteration k).core.etaR :=
      conditions.core.parameters_nonneg.2.2.2.1
    have hrho : 0 ≤ (right.iteration k).core.rhoAR :=
      conditions.core.parameters_nonneg.2.2.2.2
    have hfactor : 0 ≤ (right.family.iteration k).dimensionFactor :=
      le_trans (by norm_num) (right.family.iteration k).dimensionFactor_one_le
    have hgmres :
        p19VecNorm2 expansion.gmresContribution /
              p19VecNorm2 right.family.system.xExact ≤
          (right.family.iteration k).dimensionFactor *
            (right.iteration k).core.ug *
              p19StaticRightOperatorKappa choice right.preconditioner *
                p19StaticRightPreconditionerKappa choice right.preconditioner := by
      calc
        _ ≤ (right.iteration k).core.gmresMagnitude *
              p19StaticRightOperatorKappa choice right.preconditioner *
                p19StaticRightPreconditionerKappa choice right.preconditioner :=
          expansion.gmres_gain_bound
        _ ≤ _ := by
          gcongr
          exact conditions.core.gmres_magnitude_bound
    have hreapply :
        p19VecNorm2 expansion.reapplicationContribution /
              p19VecNorm2 right.family.system.xExact ≤
          (right.family.iteration k).dimensionFactor *
            (right.iteration k).core.um *
              (right.iteration k).core.etaR *
                p19StaticRightPreconditionerKappa choice right.preconditioner := by
      calc
        _ ≤ (right.iteration k).reapplicationMagnitude *
              p19StaticRightPreconditionerKappa choice right.preconditioner :=
          expansion.reapplication_gain_bound
        _ ≤ _ := by
          gcongr
          exact conditions.reapplication_magnitude_bound
    have hmatrix :
        p19VecNorm2 expansion.matrixContribution /
              p19VecNorm2 right.family.system.xExact ≤
          (right.family.iteration k).dimensionFactor *
            (right.iteration k).core.ua *
              p19StaticSystemKappa choice right.family *
                (right.iteration k).core.rhoAR := by
      calc
        _ ≤ (right.iteration k).core.matrixMagnitude *
              p19StaticSystemKappa choice right.family *
                (right.iteration k).core.rhoAR := expansion.matrix_gain_bound
        _ ≤ _ := by
          gcongr
          exact conditions.core.matrix_magnitude_bound
    have hnorm :
        p19VecNorm2
            (expansion.gmresContribution +
              expansion.reapplicationContribution +
                expansion.matrixContribution + expansion.remainder) ≤
          p19VecNorm2 expansion.gmresContribution +
            p19VecNorm2 expansion.reapplicationContribution +
              p19VecNorm2 expansion.matrixContribution +
                p19VecNorm2 expansion.remainder := by
      calc
        _ ≤ p19VecNorm2
                (expansion.gmresContribution +
                  expansion.reapplicationContribution +
                    expansion.matrixContribution) +
              p19VecNorm2 expansion.remainder := p19VecNorm2_add_le _ _
        _ ≤ (p19VecNorm2
                (expansion.gmresContribution +
                  expansion.reapplicationContribution) +
              p19VecNorm2 expansion.matrixContribution) +
                p19VecNorm2 expansion.remainder := by
              gcongr
              exact p19VecNorm2_add_le _ _
        _ ≤ _ := by
              gcongr
              exact p19VecNorm2_add_le _ _
    refine ⟨k, hwell, ?_⟩
    refine ⟨p19VecNorm2 expansion.remainder /
        p19VecNorm2 right.family.system.xExact,
      expansion.remainder_second_order, ?_⟩
    rw [p19ForwardError, expansion.error_decomposition]
    calc
      p19VecNorm2
            (expansion.gmresContribution +
              expansion.reapplicationContribution +
                expansion.matrixContribution + expansion.remainder) /
          p19VecNorm2 right.family.system.xExact ≤
        (p19VecNorm2 expansion.gmresContribution +
            p19VecNorm2 expansion.reapplicationContribution +
              p19VecNorm2 expansion.matrixContribution +
                p19VecNorm2 expansion.remainder) /
          p19VecNorm2 right.family.system.xExact := by
            exact div_le_div_of_nonneg_right hnorm hdenom.le
      _ = p19VecNorm2 expansion.gmresContribution /
              p19VecNorm2 right.family.system.xExact +
            p19VecNorm2 expansion.reapplicationContribution /
              p19VecNorm2 right.family.system.xExact +
            p19VecNorm2 expansion.matrixContribution /
              p19VecNorm2 right.family.system.xExact +
            p19VecNorm2 expansion.remainder /
              p19VecNorm2 right.family.system.xExact := by ring
      _ ≤ (right.family.iteration k).dimensionFactor *
              (right.iteration k).core.ug *
                p19StaticRightOperatorKappa choice right.preconditioner *
                  p19StaticRightPreconditionerKappa choice right.preconditioner +
            (right.family.iteration k).dimensionFactor *
              (right.iteration k).core.um *
                (right.iteration k).core.etaR *
                  p19StaticRightPreconditionerKappa choice right.preconditioner +
            (right.family.iteration k).dimensionFactor *
              (right.iteration k).core.ua *
                p19StaticSystemKappa choice right.family *
                  (right.iteration k).core.rhoAR +
            p19VecNorm2 expansion.remainder /
              p19VecNorm2 right.family.system.xExact := by gcongr
      _ = (right.family.iteration k).dimensionFactor *
              p19StaticRightAttainableEnvelope choice right.preconditioner
                (right.iteration k).core.ug
                (right.iteration k).core.um
                (right.iteration k).core.ua
                (right.iteration k).core.etaR
                (right.iteration k).core.rhoAR +
            p19VecNorm2 expansion.remainder /
              p19VecNorm2 right.family.system.xExact := by
            simp only [p19StaticRightAttainableEnvelope]
            ring
      _ ≤ (right.family.iteration k).dimensionFactor *
              p19StaticRightAttainableEnvelope choice right.preconditioner
                (right.iteration k).core.ug
                (right.iteration k).core.um
                (right.iteration k).core.ua
                (right.iteration k).core.etaR
                (right.iteration k).core.rhoAR +
            |p19VecNorm2 expansion.remainder /
              p19VecNorm2 right.family.system.xExact| := by
            rw [abs_of_nonneg]
            exact div_nonneg (p19VecNorm2_nonneg _) hdenom.le
  · intro flexible mgs appendix applicability
    obtain ⟨k, hwell, hstop⟩ := mgs.exists_terminal_or_near
    let conditions := applicability k hwell hstop
    let expansion := appendix.expansion k hwell hstop conditions
    have hx : flexible.family.system.xExact ≠ 0 := by
      intro hxzero
      apply flexible.family.system.b_nonzero
      rw [← flexible.family.system.exact_solution, hxzero]
      ext i
      simp [p19MatVec]
    have hdenom : 0 < p19VecNorm2 flexible.family.system.xExact :=
      p19VecNorm2_pos hx
    have hop :
        0 ≤ p19StaticRightOperatorKappa choice flexible.preconditioner :=
      p19StaticKappa_nonneg choice _ _
    have hpre :
        0 ≤ p19StaticRightPreconditionerKappa choice flexible.preconditioner :=
      p19StaticKappa_nonneg choice _ _
    have hsys : 0 ≤ p19StaticSystemKappa choice flexible.family :=
      p19StaticKappa_nonneg choice _ _
    have hrho : 0 ≤ (flexible.iteration k).core.rhoAR :=
      conditions.core.parameters_nonneg.2.2.2.2
    have hgmres :
        p19VecNorm2 expansion.gmresContribution /
              p19VecNorm2 flexible.family.system.xExact ≤
          (flexible.family.iteration k).dimensionFactor *
            (flexible.iteration k).core.ug *
              p19StaticRightOperatorKappa choice flexible.preconditioner *
                p19StaticRightPreconditionerKappa choice flexible.preconditioner := by
      calc
        _ ≤ (flexible.iteration k).core.gmresMagnitude *
              p19StaticRightOperatorKappa choice flexible.preconditioner *
                p19StaticRightPreconditionerKappa choice flexible.preconditioner :=
          expansion.gmres_gain_bound
        _ ≤ _ := by
          gcongr
          exact conditions.core.gmres_magnitude_bound
    have hmatrix :
        p19VecNorm2 expansion.matrixContribution /
              p19VecNorm2 flexible.family.system.xExact ≤
          (flexible.family.iteration k).dimensionFactor *
            (flexible.iteration k).core.ua *
              p19StaticSystemKappa choice flexible.family *
                (flexible.iteration k).core.rhoAR := by
      calc
        _ ≤ (flexible.iteration k).core.matrixMagnitude *
              p19StaticSystemKappa choice flexible.family *
                (flexible.iteration k).core.rhoAR := expansion.matrix_gain_bound
        _ ≤ _ := by
          gcongr
          exact conditions.core.matrix_magnitude_bound
    have hnorm :
        p19VecNorm2
            (expansion.gmresContribution + expansion.matrixContribution +
              expansion.remainder) ≤
          p19VecNorm2 expansion.gmresContribution +
            p19VecNorm2 expansion.matrixContribution +
              p19VecNorm2 expansion.remainder := by
      calc
        _ ≤ p19VecNorm2
                (expansion.gmresContribution + expansion.matrixContribution) +
              p19VecNorm2 expansion.remainder := p19VecNorm2_add_le _ _
        _ ≤ _ := by
              gcongr
              exact p19VecNorm2_add_le _ _
    refine ⟨k, hwell, ?_⟩
    refine ⟨p19VecNorm2 expansion.remainder /
        p19VecNorm2 flexible.family.system.xExact,
      expansion.remainder_second_order, ?_⟩
    rw [p19ForwardError, expansion.error_decomposition]
    calc
      p19VecNorm2
            (expansion.gmresContribution + expansion.matrixContribution +
              expansion.remainder) /
          p19VecNorm2 flexible.family.system.xExact ≤
        (p19VecNorm2 expansion.gmresContribution +
            p19VecNorm2 expansion.matrixContribution +
              p19VecNorm2 expansion.remainder) /
          p19VecNorm2 flexible.family.system.xExact := by
            exact div_le_div_of_nonneg_right hnorm hdenom.le
      _ = p19VecNorm2 expansion.gmresContribution /
              p19VecNorm2 flexible.family.system.xExact +
            p19VecNorm2 expansion.matrixContribution /
              p19VecNorm2 flexible.family.system.xExact +
            p19VecNorm2 expansion.remainder /
              p19VecNorm2 flexible.family.system.xExact := by ring
      _ ≤ (flexible.family.iteration k).dimensionFactor *
              (flexible.iteration k).core.ug *
                p19StaticRightOperatorKappa choice flexible.preconditioner *
                  p19StaticRightPreconditionerKappa choice flexible.preconditioner +
            (flexible.family.iteration k).dimensionFactor *
              (flexible.iteration k).core.ua *
                p19StaticSystemKappa choice flexible.family *
                  (flexible.iteration k).core.rhoAR +
            p19VecNorm2 expansion.remainder /
              p19VecNorm2 flexible.family.system.xExact := by gcongr
      _ = (flexible.family.iteration k).dimensionFactor *
              p19StaticFlexibleAttainableEnvelope choice
                flexible.preconditioner
                (flexible.iteration k).core.ug
                (flexible.iteration k).core.ua
                (flexible.iteration k).core.rhoAR +
            p19VecNorm2 expansion.remainder /
              p19VecNorm2 flexible.family.system.xExact := by
            simp only [p19StaticFlexibleAttainableEnvelope]
            ring
      _ ≤ (flexible.family.iteration k).dimensionFactor *
              p19StaticFlexibleAttainableEnvelope choice
                flexible.preconditioner
                (flexible.iteration k).core.ug
                (flexible.iteration k).core.ua
                (flexible.iteration k).core.rhoAR +
            |p19VecNorm2 expansion.remainder /
              p19VecNorm2 flexible.family.system.xExact| := by
            rw [abs_of_nonneg]
            exact div_nonneg (p19VecNorm2_nonneg _) hdenom.le
  · intro family preconditioner ug um ua etaR rhoAR
    simp only [p19StaticRightAttainableEnvelope,
      p19StaticFlexibleAttainableEnvelope]
    ring

end HighamBench
