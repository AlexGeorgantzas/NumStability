import HighamBench.P19Definitions

namespace HighamBench

private theorem p19VecNorm2_add_le {n : ℕ} (x y : P19Vector n) :
    p19VecNorm2 (x + y) ≤ p19VecNorm2 x + p19VecNorm2 y := by
  let x' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  let y' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  simpa [p19VecNorm2, p19VecNorm2Sq, EuclideanSpace.norm_eq,
    Real.norm_eq_abs, sq_abs, x', y'] using norm_add_le x' y'

private theorem p19VecNorm2_nonneg {n : ℕ} (x : P19Vector n) :
    0 ≤ p19VecNorm2 x := by
  exact Real.sqrt_nonneg _

section

open scoped Matrix.Norms.Frobenius

private theorem p19FrobNorm_nonneg {m k : ℕ} (A : P19RectMatrix m k) :
    0 ≤ p19FrobNorm A := by
  exact norm_nonneg A

end

section

open scoped Matrix.Norms.L2Operator

private theorem p19OpNorm2_nonneg {n : ℕ} (A : P19Matrix n) :
    0 ≤ p19OpNorm2 A := by
  exact norm_nonneg A

end

private theorem p19StaticKappa_nonneg
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    (A Ainv : P19Matrix n) : 0 ≤ p19StaticKappa choice A Ainv := by
  cases choice with
  | frobenius =>
      exact mul_nonneg (p19FrobNorm_nonneg Ainv) (p19FrobNorm_nonneg A)
  | inducedTwo =>
      exact mul_nonneg (p19OpNorm2_nonneg A) (p19OpNorm2_nonneg Ainv)

private theorem p19_mgs_selected_iteration
    {n : ℕ} {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (mgs : P19MGSSelectionLaw family) :
    ∃ k : P19Theorem31Dimension n,
      p19IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p19MGSNearDependence (family.iteration k)) := by
  classical
  let last : P19Theorem31Dimension n :=
    ⟨n, family.system.dimension_pos, Nat.le_refl n⟩
  by_cases hlast : p19IterationWellConditioned (family.iteration last)
  · exact ⟨last, hlast, Or.inl rfl⟩
  · let Bad : ℕ → Prop := fun j ↦
      ∃ h : 0 < j ∧ j ≤ n,
        ¬ p19IterationWellConditioned (family.iteration ⟨j, h⟩)
    have bad_exists : ∃ j, Bad j := by
      exact ⟨n, ⟨family.system.dimension_pos, Nat.le_refl n⟩, hlast⟩
    let j := Nat.find bad_exists
    have hjbad : Bad j := Nat.find_spec bad_exists
    obtain ⟨hj, hjnot⟩ := hjbad
    have hj_ne_one : j ≠ 1 := by
      intro hj1
      apply hjnot
      have heq : (⟨j, hj⟩ : P19Theorem31Dimension n) =
          ⟨1, Nat.zero_lt_one, family.system.dimension_pos⟩ := by
        exact Subtype.ext hj1
      rw [heq]
      exact mgs.first_dimension_good
    have hj_two : 2 ≤ j := by omega
    let k : ℕ := j - 1
    have hkpos : 0 < k := by
      dsimp [k]
      omega
    have hklt : k < n := by
      dsimp [k]
      omega
    let current : P19Theorem31Dimension n :=
      ⟨k, hkpos, Nat.le_of_lt hklt⟩
    have hcurrent :
        p19IterationWellConditioned (family.iteration current) := by
      by_contra hbadcurrent
      have hkbad : Bad k :=
        ⟨⟨hkpos, Nat.le_of_lt hklt⟩, hbadcurrent⟩
      have := Nat.find_min' bad_exists hkbad
      dsimp [j, k] at this
      omega
    have hnext :
        ¬ p19IterationWellConditioned
          (family.iteration
            ⟨k + 1, Nat.succ_pos k, Nat.succ_le_iff.mpr hklt⟩) := by
      have hk_succ : k + 1 = j := by
        dsimp [k]
        omega
      have heq :
          (⟨k + 1, Nat.succ_pos k, Nat.succ_le_iff.mpr hklt⟩ :
              P19Theorem31Dimension n) = ⟨j, hj⟩ := by
        exact Subtype.ext hk_succ
      rw [heq]
      exact hjnot
    refine ⟨current, hcurrent, Or.inr ?_⟩
    exact mgs.loss_implies_near_dependence k hkpos hklt hnext

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
    obtain ⟨k, hwell, hstop⟩ := p19_mgs_selected_iteration right.family mgs
    refine ⟨k, hwell, ?_⟩
    have conditions := applicability k hwell hstop
    have expansion := appendix.expansion k hwell hstop conditions
    let denominator := p19VecNorm2 right.family.system.xExact
    let remainderRatio := p19VecNorm2 expansion.remainder / denominator
    refine ⟨remainderRatio, ?_, ?_⟩
    · exact expansion.remainder_second_order
    · have htri :
          p19VecNorm2
              ((right.family.iteration k).xHat -
                right.family.system.xExact) ≤
            p19VecNorm2 expansion.gmresContribution +
              p19VecNorm2 expansion.reapplicationContribution +
                p19VecNorm2 expansion.matrixContribution +
                  p19VecNorm2 expansion.remainder := by
        rw [expansion.error_decomposition]
        have h₁ := p19VecNorm2_add_le expansion.gmresContribution
          expansion.reapplicationContribution
        have h₂ := p19VecNorm2_add_le
          (expansion.gmresContribution + expansion.reapplicationContribution)
          expansion.matrixContribution
        have h₃ := p19VecNorm2_add_le
          (expansion.gmresContribution + expansion.reapplicationContribution +
            expansion.matrixContribution) expansion.remainder
        linarith
      have hratio :
          p19ForwardError right.family.system.xExact
              (right.family.iteration k).xHat ≤
            p19VecNorm2 expansion.gmresContribution / denominator +
              p19VecNorm2 expansion.reapplicationContribution / denominator +
                p19VecNorm2 expansion.matrixContribution / denominator +
                  remainderRatio := by
        unfold p19ForwardError
        change
          p19VecNorm2
                ((right.family.iteration k).xHat -
                  right.family.system.xExact) /
              denominator ≤ _
        calc
          _ ≤ (p19VecNorm2 expansion.gmresContribution +
                  p19VecNorm2 expansion.reapplicationContribution +
                    p19VecNorm2 expansion.matrixContribution +
                      p19VecNorm2 expansion.remainder) /
                denominator :=
            div_le_div_of_nonneg_right htri
              (p19VecNorm2_nonneg right.family.system.xExact)
          _ = _ := by
            dsimp [remainderRatio]
            ring
      have hop :
          0 ≤ p19StaticRightOperatorKappa choice right.preconditioner := by
        exact p19StaticKappa_nonneg choice _ _
      have hpre :
          0 ≤ p19StaticRightPreconditionerKappa choice
            right.preconditioner := by
        exact p19StaticKappa_nonneg choice _ _
      have hsystem :
          0 ≤ p19StaticSystemKappa choice right.family := by
        exact p19StaticKappa_nonneg choice _ _
      have hgmres :
          p19VecNorm2 expansion.gmresContribution / denominator ≤
            (right.family.iteration k).dimensionFactor *
              (right.iteration k).core.ug *
                p19StaticRightOperatorKappa choice right.preconditioner *
                  p19StaticRightPreconditionerKappa choice
                    right.preconditioner := by
        calc
          _ ≤ (right.iteration k).core.gmresMagnitude *
                p19StaticRightOperatorKappa choice right.preconditioner *
                  p19StaticRightPreconditionerKappa choice
                    right.preconditioner := expansion.gmres_gain_bound
          _ ≤ _ := by
            gcongr
            exact conditions.core.gmres_magnitude_bound
      have hreapplication :
          p19VecNorm2 expansion.reapplicationContribution / denominator ≤
            (right.family.iteration k).dimensionFactor *
              (right.iteration k).core.um *
                (right.iteration k).core.etaR *
                  p19StaticRightPreconditionerKappa choice
                    right.preconditioner := by
        calc
          _ ≤ (right.iteration k).reapplicationMagnitude *
                p19StaticRightPreconditionerKappa choice
                  right.preconditioner := expansion.reapplication_gain_bound
          _ ≤ _ := by
            gcongr
            exact conditions.reapplication_magnitude_bound
      have hmatrix :
          p19VecNorm2 expansion.matrixContribution / denominator ≤
            (right.family.iteration k).dimensionFactor *
              (right.iteration k).core.ua *
                p19StaticSystemKappa choice right.family *
                  (right.iteration k).core.rhoAR := by
        calc
          _ ≤ (right.iteration k).core.matrixMagnitude *
                p19StaticSystemKappa choice right.family *
                  (right.iteration k).core.rhoAR :=
            expansion.matrix_gain_bound
          _ ≤ _ := by
            gcongr
            · exact conditions.core.parameters_nonneg.2.2.2.2
            · exact conditions.core.matrix_magnitude_bound
      calc
        p19ForwardError right.family.system.xExact
              (right.family.iteration k).xHat ≤
            p19VecNorm2 expansion.gmresContribution / denominator +
              p19VecNorm2 expansion.reapplicationContribution / denominator +
                p19VecNorm2 expansion.matrixContribution / denominator +
                  remainderRatio := hratio
        _ ≤ (right.family.iteration k).dimensionFactor *
                (right.iteration k).core.ug *
                  p19StaticRightOperatorKappa choice right.preconditioner *
                    p19StaticRightPreconditionerKappa choice
                      right.preconditioner +
              (right.family.iteration k).dimensionFactor *
                (right.iteration k).core.um *
                  (right.iteration k).core.etaR *
                    p19StaticRightPreconditionerKappa choice
                      right.preconditioner +
              (right.family.iteration k).dimensionFactor *
                (right.iteration k).core.ua *
                  p19StaticSystemKappa choice right.family *
                    (right.iteration k).core.rhoAR + remainderRatio := by
          linarith
        _ = (right.family.iteration k).dimensionFactor *
                p19StaticRightAttainableEnvelope choice right.preconditioner
                  (right.iteration k).core.ug
                  (right.iteration k).core.um
                  (right.iteration k).core.ua
                  (right.iteration k).core.etaR
                  (right.iteration k).core.rhoAR +
              |remainderRatio| := by
          rw [abs_of_nonneg]
          · simp only [p19StaticRightAttainableEnvelope]
            ring
          · exact div_nonneg (p19VecNorm2_nonneg expansion.remainder)
              (p19VecNorm2_nonneg right.family.system.xExact)
  · constructor
    · intro flexible mgs appendix applicability
      obtain ⟨k, hwell, hstop⟩ :=
        p19_mgs_selected_iteration flexible.family mgs
      refine ⟨k, hwell, ?_⟩
      have conditions := applicability k hwell hstop
      have expansion := appendix.expansion k hwell hstop conditions
      let denominator := p19VecNorm2 flexible.family.system.xExact
      let remainderRatio := p19VecNorm2 expansion.remainder / denominator
      refine ⟨remainderRatio, ?_, ?_⟩
      · exact expansion.remainder_second_order
      · have htri :
            p19VecNorm2
                ((flexible.family.iteration k).xHat -
                  flexible.family.system.xExact) ≤
              p19VecNorm2 expansion.gmresContribution +
                p19VecNorm2 expansion.matrixContribution +
                  p19VecNorm2 expansion.remainder := by
          rw [expansion.error_decomposition]
          have h₁ := p19VecNorm2_add_le expansion.gmresContribution
            expansion.matrixContribution
          have h₂ := p19VecNorm2_add_le
            (expansion.gmresContribution + expansion.matrixContribution)
            expansion.remainder
          linarith
        have hratio :
            p19ForwardError flexible.family.system.xExact
                (flexible.family.iteration k).xHat ≤
              p19VecNorm2 expansion.gmresContribution / denominator +
                p19VecNorm2 expansion.matrixContribution / denominator +
                  remainderRatio := by
          unfold p19ForwardError
          change
            p19VecNorm2
                  ((flexible.family.iteration k).xHat -
                    flexible.family.system.xExact) /
                denominator ≤ _
          calc
            _ ≤ (p19VecNorm2 expansion.gmresContribution +
                    p19VecNorm2 expansion.matrixContribution +
                      p19VecNorm2 expansion.remainder) /
                  denominator :=
              div_le_div_of_nonneg_right htri
                (p19VecNorm2_nonneg flexible.family.system.xExact)
            _ = _ := by
              dsimp [remainderRatio]
              ring
        have hop :
            0 ≤ p19StaticRightOperatorKappa choice
              flexible.preconditioner := by
          exact p19StaticKappa_nonneg choice _ _
        have hpre :
            0 ≤ p19StaticRightPreconditionerKappa choice
              flexible.preconditioner := by
          exact p19StaticKappa_nonneg choice _ _
        have hsystem :
            0 ≤ p19StaticSystemKappa choice flexible.family := by
          exact p19StaticKappa_nonneg choice _ _
        have hgmres :
            p19VecNorm2 expansion.gmresContribution / denominator ≤
              (flexible.family.iteration k).dimensionFactor *
                (flexible.iteration k).core.ug *
                  p19StaticRightOperatorKappa choice flexible.preconditioner *
                    p19StaticRightPreconditionerKappa choice
                      flexible.preconditioner := by
          calc
            _ ≤ (flexible.iteration k).core.gmresMagnitude *
                  p19StaticRightOperatorKappa choice flexible.preconditioner *
                    p19StaticRightPreconditionerKappa choice
                      flexible.preconditioner := expansion.gmres_gain_bound
            _ ≤ _ := by
              gcongr
              exact conditions.core.gmres_magnitude_bound
        have hmatrix :
            p19VecNorm2 expansion.matrixContribution / denominator ≤
              (flexible.family.iteration k).dimensionFactor *
                (flexible.iteration k).core.ua *
                  p19StaticSystemKappa choice flexible.family *
                    (flexible.iteration k).core.rhoAR := by
          calc
            _ ≤ (flexible.iteration k).core.matrixMagnitude *
                  p19StaticSystemKappa choice flexible.family *
                    (flexible.iteration k).core.rhoAR :=
              expansion.matrix_gain_bound
            _ ≤ _ := by
              gcongr
              · exact conditions.core.parameters_nonneg.2.2.2.2
              · exact conditions.core.matrix_magnitude_bound
        calc
          p19ForwardError flexible.family.system.xExact
                (flexible.family.iteration k).xHat ≤
              p19VecNorm2 expansion.gmresContribution / denominator +
                p19VecNorm2 expansion.matrixContribution / denominator +
                  remainderRatio := hratio
          _ ≤ (flexible.family.iteration k).dimensionFactor *
                  (flexible.iteration k).core.ug *
                    p19StaticRightOperatorKappa choice
                      flexible.preconditioner *
                      p19StaticRightPreconditionerKappa choice
                        flexible.preconditioner +
                (flexible.family.iteration k).dimensionFactor *
                  (flexible.iteration k).core.ua *
                    p19StaticSystemKappa choice flexible.family *
                      (flexible.iteration k).core.rhoAR +
                remainderRatio := by
            linarith
          _ = (flexible.family.iteration k).dimensionFactor *
                  p19StaticFlexibleAttainableEnvelope choice
                    flexible.preconditioner
                    (flexible.iteration k).core.ug
                    (flexible.iteration k).core.ua
                    (flexible.iteration k).core.rhoAR +
                |remainderRatio| := by
            rw [abs_of_nonneg]
            · simp only [p19StaticFlexibleAttainableEnvelope]
              ring
            · exact div_nonneg (p19VecNorm2_nonneg expansion.remainder)
                (p19VecNorm2_nonneg flexible.family.system.xExact)
    · intro family preconditioner ug um ua etaR rhoAR
      simp only [p19StaticRightAttainableEnvelope,
        p19StaticFlexibleAttainableEnvelope]
      ring

end HighamBench
