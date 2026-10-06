import HighamBench.P19Definitions

namespace HighamBench

private theorem p19VecNorm2_eq_euclideanNorm {n : ℕ}
    (x : P19Vector n) :
    p19VecNorm2 x = ‖WithLp.toLp (2 : ENNReal) x‖ := by
  unfold p19VecNorm2 p19VecNorm2Sq
  rw [EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, sq_abs]

private theorem p19VecNorm2_add_le {n : ℕ} (x y : P19Vector n) :
    p19VecNorm2 (x + y) ≤ p19VecNorm2 x + p19VecNorm2 y := by
  rw [p19VecNorm2_eq_euclideanNorm, p19VecNorm2_eq_euclideanNorm,
    p19VecNorm2_eq_euclideanNorm, WithLp.toLp_add]
  exact norm_add_le _ _

private theorem p19VecNorm2_pos {n : ℕ} {x : P19Vector n} (hx : x ≠ 0) :
    0 < p19VecNorm2 x := by
  rw [p19VecNorm2_eq_euclideanNorm]
  apply norm_pos_iff.mpr
  exact fun h ↦ hx (WithLp.toLp_injective (2 : ENNReal) h)

private theorem p19StaticKappa_nonneg
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    (A Ainv : P19Matrix n) :
    0 ≤ p19StaticKappa choice A Ainv := by
  cases choice
  · unfold p19StaticKappa p19ConditionNumberF p19FrobNorm
    letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) :=
      Matrix.frobeniusNormedAddCommGroup
    exact mul_nonneg (norm_nonneg Ainv) (norm_nonneg A)
  · unfold p19StaticKappa p19Kappa2 p19OpNorm2
    letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) :=
      Matrix.instL2OpNormedAddCommGroup
    exact mul_nonneg (norm_nonneg A) (norm_nonneg Ainv)

private theorem p19_exists_mgs_selected_iteration {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (mgs : P19MGSSelectionLaw family) :
    ∃ k : P19Theorem31Dimension n,
      p19IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p19MGSNearDependence (family.iteration k)) := by
  by_contra hnone
  push_neg at hnone
  have all_good : ∀ (k : ℕ) (hkpos : 0 < k) (hkn : k ≤ n),
      p19IterationWellConditioned
        (family.iteration ⟨k, hkpos, hkn⟩) := by
    intro k hkpos hkn
    induction k, hkpos using Nat.le_induction with
    | base => simpa using mgs.first_dimension_good
    | succ k hkone ih =>
        have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hkone
        have hklt : k < n := Nat.lt_of_succ_le hkn
        by_contra hbad
        have hnear := mgs.loss_implies_near_dependence k hkpos hklt (by
          simpa using hbad)
        exact (hnone ⟨k, hkpos, Nat.le_of_lt hklt⟩
          (ih (Nat.le_of_lt hklt))).2 hnear
  let last : P19Theorem31Dimension n :=
    ⟨n, family.system.dimension_pos, Nat.le_refl n⟩
  have hlast : p19IterationWellConditioned (family.iteration last) :=
    all_good n family.system.dimension_pos (Nat.le_refl n)
  exact (hnone last hlast).1 rfl

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
  constructor
  · intro right mgs appendix applicability
    obtain ⟨k, hwell, hstop⟩ :=
      p19_exists_mgs_selected_iteration right.family mgs
    have conditions := applicability k hwell hstop
    have expansion := appendix.expansion k hwell hstop conditions
    refine ⟨k, hwell, ?_⟩
    let denominator := p19VecNorm2 right.family.system.xExact
    let remainder := p19VecNorm2 expansion.remainder / denominator
    refine ⟨remainder, expansion.remainder_second_order, ?_⟩
    have hxne : right.family.system.xExact ≠ 0 := by
      intro hx
      apply right.family.system.b_nonzero
      rw [← right.family.system.exact_solution, hx]
      ext i
      simp [p19MatVec]
    have hden : 0 < denominator := p19VecNorm2_pos hxne
    have htriangle :
        p19VecNorm2
            (expansion.gmresContribution +
              expansion.reapplicationContribution +
              expansion.matrixContribution + expansion.remainder) ≤
          p19VecNorm2 expansion.gmresContribution +
            p19VecNorm2 expansion.reapplicationContribution +
            p19VecNorm2 expansion.matrixContribution +
            p19VecNorm2 expansion.remainder := by
      have h₁ := p19VecNorm2_add_le expansion.gmresContribution
        expansion.reapplicationContribution
      have h₂ := p19VecNorm2_add_le
        (expansion.gmresContribution + expansion.reapplicationContribution)
        expansion.matrixContribution
      have h₃ := p19VecNorm2_add_le
        (expansion.gmresContribution + expansion.reapplicationContribution +
          expansion.matrixContribution) expansion.remainder
      linarith
    have htotal :
        p19ForwardError right.family.system.xExact
            (right.family.iteration k).xHat ≤
          p19VecNorm2 expansion.gmresContribution / denominator +
            p19VecNorm2 expansion.reapplicationContribution / denominator +
            p19VecNorm2 expansion.matrixContribution / denominator +
            remainder := by
      unfold p19ForwardError
      rw [expansion.error_decomposition]
      change _ / denominator ≤ _
      have hdiv := (div_le_div_iff_of_pos_right hden).2 htriangle
      calc
        _ ≤ (p19VecNorm2 expansion.gmresContribution +
              p19VecNorm2 expansion.reapplicationContribution +
              p19VecNorm2 expansion.matrixContribution +
              p19VecNorm2 expansion.remainder) / denominator := hdiv
        _ = _ := by dsimp [remainder]; ring
    have hop : 0 ≤
        p19StaticRightOperatorKappa choice right.preconditioner :=
      p19StaticKappa_nonneg choice _ _
    have hpre : 0 ≤
        p19StaticRightPreconditionerKappa choice right.preconditioner :=
      p19StaticKappa_nonneg choice _ _
    have hsys : 0 ≤ p19StaticSystemKappa choice right.family :=
      p19StaticKappa_nonneg choice _ _
    have hgmres :
        p19VecNorm2 expansion.gmresContribution / denominator ≤
          (right.family.iteration k).dimensionFactor *
            ((right.iteration k).core.ug *
              p19StaticRightOperatorKappa choice right.preconditioner *
              p19StaticRightPreconditionerKappa choice
                right.preconditioner) := by
      calc
        _ ≤ (right.iteration k).core.gmresMagnitude *
              p19StaticRightOperatorKappa choice right.preconditioner *
              p19StaticRightPreconditionerKappa choice
                right.preconditioner := expansion.gmres_gain_bound
        _ = (right.iteration k).core.gmresMagnitude *
              (p19StaticRightOperatorKappa choice right.preconditioner *
                p19StaticRightPreconditionerKappa choice
                  right.preconditioner) := by ring
        _ ≤ ((right.family.iteration k).dimensionFactor *
              (right.iteration k).core.ug) *
              (p19StaticRightOperatorKappa choice right.preconditioner *
                p19StaticRightPreconditionerKappa choice
                  right.preconditioner) :=
            mul_le_mul_of_nonneg_right conditions.core.gmres_magnitude_bound
              (mul_nonneg hop hpre)
        _ = _ := by ring
    have hreapplication :
        p19VecNorm2 expansion.reapplicationContribution / denominator ≤
          (right.family.iteration k).dimensionFactor *
            ((right.iteration k).core.um *
              (right.iteration k).core.etaR *
              p19StaticRightPreconditionerKappa choice
                right.preconditioner) := by
      calc
        _ ≤ (right.iteration k).reapplicationMagnitude *
              p19StaticRightPreconditionerKappa choice
                right.preconditioner := expansion.reapplication_gain_bound
        _ ≤ ((right.family.iteration k).dimensionFactor *
              (right.iteration k).core.um *
              (right.iteration k).core.etaR) *
              p19StaticRightPreconditionerKappa choice
                right.preconditioner :=
            mul_le_mul_of_nonneg_right
              conditions.reapplication_magnitude_bound hpre
        _ = _ := by ring
    have hmatrix :
        p19VecNorm2 expansion.matrixContribution / denominator ≤
          (right.family.iteration k).dimensionFactor *
            ((right.iteration k).core.ua *
              p19StaticSystemKappa choice right.family *
              (right.iteration k).core.rhoAR) := by
      have hrho : 0 ≤ (right.iteration k).core.rhoAR :=
        conditions.core.parameters_nonneg.2.2.2.2
      calc
        _ ≤ (right.iteration k).core.matrixMagnitude *
              p19StaticSystemKappa choice right.family *
              (right.iteration k).core.rhoAR := expansion.matrix_gain_bound
        _ = (right.iteration k).core.matrixMagnitude *
              (p19StaticSystemKappa choice right.family *
                (right.iteration k).core.rhoAR) := by ring
        _ ≤ ((right.family.iteration k).dimensionFactor *
              (right.iteration k).core.ua) *
              (p19StaticSystemKappa choice right.family *
                (right.iteration k).core.rhoAR) :=
            mul_le_mul_of_nonneg_right conditions.core.matrix_magnitude_bound
              (mul_nonneg hsys hrho)
        _ = _ := by ring
    calc
      _ ≤ p19VecNorm2 expansion.gmresContribution / denominator +
            p19VecNorm2 expansion.reapplicationContribution / denominator +
            p19VecNorm2 expansion.matrixContribution / denominator +
            remainder := htotal
      _ ≤ (right.family.iteration k).dimensionFactor *
              ((right.iteration k).core.ug *
                p19StaticRightOperatorKappa choice right.preconditioner *
                p19StaticRightPreconditionerKappa choice
                  right.preconditioner) +
            (right.family.iteration k).dimensionFactor *
              ((right.iteration k).core.um *
                (right.iteration k).core.etaR *
                p19StaticRightPreconditionerKappa choice
                  right.preconditioner) +
            (right.family.iteration k).dimensionFactor *
              ((right.iteration k).core.ua *
                p19StaticSystemKappa choice right.family *
                (right.iteration k).core.rhoAR) + |remainder| := by
          gcongr
          exact le_abs_self remainder
      _ = (right.family.iteration k).dimensionFactor *
              p19StaticRightAttainableEnvelope choice right.preconditioner
                (right.iteration k).core.ug
                (right.iteration k).core.um
                (right.iteration k).core.ua
                (right.iteration k).core.etaR
                (right.iteration k).core.rhoAR + |remainder| := by
          unfold p19StaticRightAttainableEnvelope
          ring
  · constructor
    · intro flexible mgs appendix applicability
      obtain ⟨k, hwell, hstop⟩ :=
        p19_exists_mgs_selected_iteration flexible.family mgs
      have conditions := applicability k hwell hstop
      have expansion := appendix.expansion k hwell hstop conditions
      refine ⟨k, hwell, ?_⟩
      let denominator := p19VecNorm2 flexible.family.system.xExact
      let remainder := p19VecNorm2 expansion.remainder / denominator
      refine ⟨remainder, expansion.remainder_second_order, ?_⟩
      have hxne : flexible.family.system.xExact ≠ 0 := by
        intro hx
        apply flexible.family.system.b_nonzero
        rw [← flexible.family.system.exact_solution, hx]
        ext i
        simp [p19MatVec]
      have hden : 0 < denominator := p19VecNorm2_pos hxne
      have htriangle :
          p19VecNorm2
              (expansion.gmresContribution + expansion.matrixContribution +
                expansion.remainder) ≤
            p19VecNorm2 expansion.gmresContribution +
              p19VecNorm2 expansion.matrixContribution +
              p19VecNorm2 expansion.remainder := by
        have h₁ := p19VecNorm2_add_le expansion.gmresContribution
          expansion.matrixContribution
        have h₂ := p19VecNorm2_add_le
          (expansion.gmresContribution + expansion.matrixContribution)
          expansion.remainder
        linarith
      have htotal :
          p19ForwardError flexible.family.system.xExact
              (flexible.family.iteration k).xHat ≤
            p19VecNorm2 expansion.gmresContribution / denominator +
              p19VecNorm2 expansion.matrixContribution / denominator +
              remainder := by
        unfold p19ForwardError
        rw [expansion.error_decomposition]
        change _ / denominator ≤ _
        have hdiv := (div_le_div_iff_of_pos_right hden).2 htriangle
        calc
          _ ≤ (p19VecNorm2 expansion.gmresContribution +
                p19VecNorm2 expansion.matrixContribution +
                p19VecNorm2 expansion.remainder) / denominator := hdiv
          _ = _ := by dsimp [remainder]; ring
      have hop : 0 ≤
          p19StaticRightOperatorKappa choice flexible.preconditioner :=
        p19StaticKappa_nonneg choice _ _
      have hpre : 0 ≤
          p19StaticRightPreconditionerKappa choice flexible.preconditioner :=
        p19StaticKappa_nonneg choice _ _
      have hsys : 0 ≤ p19StaticSystemKappa choice flexible.family :=
        p19StaticKappa_nonneg choice _ _
      have hgmres :
          p19VecNorm2 expansion.gmresContribution / denominator ≤
            (flexible.family.iteration k).dimensionFactor *
              ((flexible.iteration k).core.ug *
                p19StaticRightOperatorKappa choice flexible.preconditioner *
                p19StaticRightPreconditionerKappa choice
                  flexible.preconditioner) := by
        calc
          _ ≤ (flexible.iteration k).core.gmresMagnitude *
                p19StaticRightOperatorKappa choice flexible.preconditioner *
                p19StaticRightPreconditionerKappa choice
                  flexible.preconditioner := expansion.gmres_gain_bound
          _ = (flexible.iteration k).core.gmresMagnitude *
                (p19StaticRightOperatorKappa choice flexible.preconditioner *
                  p19StaticRightPreconditionerKappa choice
                    flexible.preconditioner) := by ring
          _ ≤ ((flexible.family.iteration k).dimensionFactor *
                (flexible.iteration k).core.ug) *
                (p19StaticRightOperatorKappa choice flexible.preconditioner *
                  p19StaticRightPreconditionerKappa choice
                    flexible.preconditioner) :=
              mul_le_mul_of_nonneg_right conditions.core.gmres_magnitude_bound
                (mul_nonneg hop hpre)
          _ = _ := by ring
      have hmatrix :
          p19VecNorm2 expansion.matrixContribution / denominator ≤
            (flexible.family.iteration k).dimensionFactor *
              ((flexible.iteration k).core.ua *
                p19StaticSystemKappa choice flexible.family *
                (flexible.iteration k).core.rhoAR) := by
        have hrho : 0 ≤ (flexible.iteration k).core.rhoAR :=
          conditions.core.parameters_nonneg.2.2.2.2
        calc
          _ ≤ (flexible.iteration k).core.matrixMagnitude *
                p19StaticSystemKappa choice flexible.family *
                (flexible.iteration k).core.rhoAR := expansion.matrix_gain_bound
          _ = (flexible.iteration k).core.matrixMagnitude *
                (p19StaticSystemKappa choice flexible.family *
                  (flexible.iteration k).core.rhoAR) := by ring
          _ ≤ ((flexible.family.iteration k).dimensionFactor *
                (flexible.iteration k).core.ua) *
                (p19StaticSystemKappa choice flexible.family *
                  (flexible.iteration k).core.rhoAR) :=
              mul_le_mul_of_nonneg_right conditions.core.matrix_magnitude_bound
                (mul_nonneg hsys hrho)
          _ = _ := by ring
      calc
        _ ≤ p19VecNorm2 expansion.gmresContribution / denominator +
              p19VecNorm2 expansion.matrixContribution / denominator +
              remainder := htotal
        _ ≤ (flexible.family.iteration k).dimensionFactor *
                ((flexible.iteration k).core.ug *
                  p19StaticRightOperatorKappa choice flexible.preconditioner *
                  p19StaticRightPreconditionerKappa choice
                    flexible.preconditioner) +
              (flexible.family.iteration k).dimensionFactor *
                ((flexible.iteration k).core.ua *
                  p19StaticSystemKappa choice flexible.family *
                  (flexible.iteration k).core.rhoAR) + |remainder| := by
            gcongr
            exact le_abs_self remainder
        _ = (flexible.family.iteration k).dimensionFactor *
                p19StaticFlexibleAttainableEnvelope choice
                  flexible.preconditioner
                  (flexible.iteration k).core.ug
                  (flexible.iteration k).core.ua
                  (flexible.iteration k).core.rhoAR + |remainder| := by
            unfold p19StaticFlexibleAttainableEnvelope
            ring
    · intro family preconditioner ug um ua etaR rhoAR
      unfold p19StaticRightAttainableEnvelope
        p19StaticFlexibleAttainableEnvelope
      ring

end HighamBench
