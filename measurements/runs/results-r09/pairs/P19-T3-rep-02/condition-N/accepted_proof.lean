import HighamBench.P19Definitions
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace HighamBench

open scoped Matrix.Norms.L2Operator Matrix.Norms.Frobenius

private lemma p19VecNorm2_eq_euclideanNorm {n : ℕ} (x : P19Vector n) :
    p19VecNorm2 x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [p19VecNorm2, p19VecNorm2Sq, Real.norm_eq_abs, sq_abs]

private lemma p19VecNorm2_nonneg {n : ℕ} (x : P19Vector n) :
    0 ≤ p19VecNorm2 x := by
  rw [p19VecNorm2_eq_euclideanNorm]
  exact norm_nonneg _

private lemma p19VecNorm2_pos {n : ℕ} {x : P19Vector n} (hx : x ≠ 0) :
    0 < p19VecNorm2 x := by
  rw [p19VecNorm2_eq_euclideanNorm, norm_pos_iff]
  simpa using hx

private lemma p19VecNorm2_add_le {n : ℕ} (x y : P19Vector n) :
    p19VecNorm2 (x + y) ≤ p19VecNorm2 x + p19VecNorm2 y := by
  simp_rw [p19VecNorm2_eq_euclideanNorm]
  simpa using
    norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
      (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))

private lemma p19OpNorm2_nonneg {n : ℕ} (A : P19Matrix n) :
    0 ≤ p19OpNorm2 A := by
  unfold p19OpNorm2
  rw [Matrix.l2_opNorm_def]
  exact norm_nonneg _

private lemma p19StaticKappa_nonneg
    (choice : P19StaticSquareKappaChoice) {n : ℕ}
    (A Ainv : P19Matrix n) : 0 ≤ p19StaticKappa choice A Ainv := by
  cases choice with
  | frobenius =>
      simp only [p19StaticKappa, p19ConditionNumberF]
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  | inducedTwo =>
      simp only [p19StaticKappa, p19Kappa2]
      exact mul_nonneg (p19OpNorm2_nonneg A) (p19OpNorm2_nonneg Ainv)

private lemma p19_exact_solution_norm_pos {n : ℕ}
    (system : P19Theorem31System n) : 0 < p19VecNorm2 system.xExact := by
  apply p19VecNorm2_pos
  intro hx
  apply system.b_nonzero
  rw [← system.exact_solution, hx]
  funext i
  simp [p19MatVec]

private lemma p19_firstOrderLe_of_four_contributions {n : ℕ}
    (semantics : P19FirstOrderSemantics)
    (error reference a b c remainder : P19Vector n) (A B C : ℝ)
    (hx : 0 < p19VecNorm2 reference)
    (hdecomp : error = a + b + c + remainder)
    (hremainder : semantics.secondOrder
      (p19VecNorm2 remainder / p19VecNorm2 reference))
    (ha : p19VecNorm2 a / p19VecNorm2 reference ≤ A)
    (hb : p19VecNorm2 b / p19VecNorm2 reference ≤ B)
    (hc : p19VecNorm2 c / p19VecNorm2 reference ≤ C) :
    p19FirstOrderLe semantics
      (p19VecNorm2 error / p19VecNorm2 reference) (A + B + C) := by
  refine ⟨p19VecNorm2 remainder / p19VecNorm2 reference, hremainder, ?_⟩
  have hab := p19VecNorm2_add_le a b
  have habc := p19VecNorm2_add_le (a + b) c
  have habcr := p19VecNorm2_add_le (a + b + c) remainder
  have hnorm :
      p19VecNorm2 error ≤
        p19VecNorm2 a + p19VecNorm2 b + p19VecNorm2 c +
        p19VecNorm2 remainder := by
    rw [hdecomp]
    linarith
  have hdiv :
      p19VecNorm2 error / p19VecNorm2 reference ≤
        (p19VecNorm2 a + p19VecNorm2 b + p19VecNorm2 c +
            p19VecNorm2 remainder) / p19VecNorm2 reference :=
    (div_le_div_iff_of_pos_right hx).2 hnorm
  have hrem_nonneg :
      0 ≤ p19VecNorm2 remainder / p19VecNorm2 reference :=
    div_nonneg (p19VecNorm2_nonneg remainder) hx.le
  rw [abs_of_nonneg hrem_nonneg]
  rw [add_div] at hdiv
  rw [add_div] at hdiv
  rw [add_div] at hdiv
  linarith

private lemma p19_select_mgs_iteration {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (mgs : P19MGSSelectionLaw family) :
    ∃ k : P19Theorem31Dimension n,
      p19IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p19MGSNearDependence (family.iteration k)) := by
  by_contra hnone
  have hall : ∀ (j : ℕ) (hjpos : 0 < j) (hjle : j ≤ n),
      p19IterationWellConditioned (family.iteration ⟨j, hjpos, hjle⟩) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hjpos hjle
        obtain hzero | hjpos' := Nat.eq_zero_or_pos (j - 1)
        · have hj : j = 1 := by omega
          subst j
          exact mgs.first_dimension_good
        · have hj_two : 2 ≤ j := by omega
          let current : P19Theorem31Dimension n :=
            ⟨j - 1, by omega, by omega⟩
          have hcurrent :
              p19IterationWellConditioned (family.iteration current) := by
            apply ih (j - 1) (by omega) (by omega) (by omega)
          by_contra hnext
          have hnear : p19MGSNearDependence (family.iteration current) := by
            have hloss := mgs.loss_implies_near_dependence
              (j - 1) (by omega) (by omega)
            apply hloss
            intro hgood
            apply hnext
            have hindex :
                (⟨(j - 1) + 1, by omega, by omega⟩ :
                    P19Theorem31Dimension n) = ⟨j, hjpos, hjle⟩ := by
              apply Subtype.ext
              simp
              omega
            exact hindex ▸ hgood
          exact hnone ⟨current, hcurrent, Or.inr hnear⟩
  let last : P19Theorem31Dimension n :=
    ⟨n, family.system.dimension_pos, le_rfl⟩
  have hlast : p19IterationWellConditioned (family.iteration last) := by
    exact hall n family.system.dimension_pos le_rfl
  exact hnone ⟨last, hlast, Or.inl rfl⟩

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
    obtain ⟨k, hwell, hterminal⟩ :=
      p19_select_mgs_iteration right.family mgs
    refine ⟨k, hwell, ?_⟩
    let conditions := applicability k hwell hterminal
    let expansion := appendix.expansion k hwell hterminal conditions
    have hx := p19_exact_solution_norm_pos right.family.system
    have hop :
        0 ≤ p19StaticRightOperatorKappa choice right.preconditioner := by
      unfold p19StaticRightOperatorKappa
      exact p19StaticKappa_nonneg choice _ _
    have hpre :
        0 ≤ p19StaticRightPreconditionerKappa choice right.preconditioner := by
      unfold p19StaticRightPreconditionerKappa
      exact p19StaticKappa_nonneg choice _ _
    have hsys : 0 ≤ p19StaticSystemKappa choice right.family := by
      unfold p19StaticSystemKappa
      exact p19StaticKappa_nonneg choice _ _
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
    have hgmres :
        p19VecNorm2 expansion.gmresContribution /
              p19VecNorm2 right.family.system.xExact ≤
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
            mul_le_mul_of_nonneg_right
              conditions.core.gmres_magnitude_bound (mul_nonneg hop hpre)
        _ = (right.family.iteration k).dimensionFactor *
            ((right.iteration k).core.ug *
              p19StaticRightOperatorKappa choice right.preconditioner *
              p19StaticRightPreconditionerKappa choice
                right.preconditioner) := by ring
    have hreapplication :
        p19VecNorm2 expansion.reapplicationContribution /
              p19VecNorm2 right.family.system.xExact ≤
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
        _ = (right.family.iteration k).dimensionFactor *
            ((right.iteration k).core.um *
              (right.iteration k).core.etaR *
              p19StaticRightPreconditionerKappa choice
                right.preconditioner) := by ring
    have hmatrix :
        p19VecNorm2 expansion.matrixContribution /
              p19VecNorm2 right.family.system.xExact ≤
          (right.family.iteration k).dimensionFactor *
            ((right.iteration k).core.ua *
              p19StaticSystemKappa choice right.family *
              (right.iteration k).core.rhoAR) := by
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
            mul_le_mul_of_nonneg_right
              conditions.core.matrix_magnitude_bound (mul_nonneg hsys hrho)
        _ = (right.family.iteration k).dimensionFactor *
            ((right.iteration k).core.ua *
              p19StaticSystemKappa choice right.family *
              (right.iteration k).core.rhoAR) := by ring
    have hbound := p19_firstOrderLe_of_four_contributions semantics
      ((right.family.iteration k).xHat - right.family.system.xExact)
      right.family.system.xExact
      expansion.gmresContribution expansion.reapplicationContribution
      expansion.matrixContribution expansion.remainder
      ((right.family.iteration k).dimensionFactor *
        ((right.iteration k).core.ug *
          p19StaticRightOperatorKappa choice right.preconditioner *
          p19StaticRightPreconditionerKappa choice right.preconditioner))
      ((right.family.iteration k).dimensionFactor *
        ((right.iteration k).core.um * (right.iteration k).core.etaR *
          p19StaticRightPreconditionerKappa choice right.preconditioner))
      ((right.family.iteration k).dimensionFactor *
        ((right.iteration k).core.ua *
          p19StaticSystemKappa choice right.family *
          (right.iteration k).core.rhoAR))
      hx expansion.error_decomposition expansion.remainder_second_order
      hgmres hreapplication hmatrix
    unfold p19ForwardError
    convert hbound using 1
    simp only [p19StaticRightAttainableEnvelope]
    ring
  · constructor
    · intro flexible mgs appendix applicability
      obtain ⟨k, hwell, hterminal⟩ :=
        p19_select_mgs_iteration flexible.family mgs
      refine ⟨k, hwell, ?_⟩
      let conditions := applicability k hwell hterminal
      let expansion := appendix.expansion k hwell hterminal conditions
      have hx := p19_exact_solution_norm_pos flexible.family.system
      have hop :
          0 ≤ p19StaticRightOperatorKappa choice
            flexible.preconditioner := by
        unfold p19StaticRightOperatorKappa
        exact p19StaticKappa_nonneg choice _ _
      have hpre :
          0 ≤ p19StaticRightPreconditionerKappa choice
            flexible.preconditioner := by
        unfold p19StaticRightPreconditionerKappa
        exact p19StaticKappa_nonneg choice _ _
      have hsys : 0 ≤ p19StaticSystemKappa choice flexible.family := by
        unfold p19StaticSystemKappa
        exact p19StaticKappa_nonneg choice _ _
      have hrho : 0 ≤ (flexible.iteration k).core.rhoAR :=
        conditions.core.parameters_nonneg.2.2.2.2
      have hgmres :
          p19VecNorm2 expansion.gmresContribution /
                p19VecNorm2 flexible.family.system.xExact ≤
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
              mul_le_mul_of_nonneg_right
                conditions.core.gmres_magnitude_bound (mul_nonneg hop hpre)
          _ = (flexible.family.iteration k).dimensionFactor *
              ((flexible.iteration k).core.ug *
                p19StaticRightOperatorKappa choice flexible.preconditioner *
                p19StaticRightPreconditionerKappa choice
                  flexible.preconditioner) := by ring
      have hmatrix :
          p19VecNorm2 expansion.matrixContribution /
                p19VecNorm2 flexible.family.system.xExact ≤
            (flexible.family.iteration k).dimensionFactor *
              ((flexible.iteration k).core.ua *
                p19StaticSystemKappa choice flexible.family *
                (flexible.iteration k).core.rhoAR) := by
        calc
          _ ≤ (flexible.iteration k).core.matrixMagnitude *
                p19StaticSystemKappa choice flexible.family *
                (flexible.iteration k).core.rhoAR :=
              expansion.matrix_gain_bound
          _ = (flexible.iteration k).core.matrixMagnitude *
                (p19StaticSystemKappa choice flexible.family *
                  (flexible.iteration k).core.rhoAR) := by ring
          _ ≤ ((flexible.family.iteration k).dimensionFactor *
                  (flexible.iteration k).core.ua) *
                (p19StaticSystemKappa choice flexible.family *
                  (flexible.iteration k).core.rhoAR) :=
              mul_le_mul_of_nonneg_right
                conditions.core.matrix_magnitude_bound (mul_nonneg hsys hrho)
          _ = (flexible.family.iteration k).dimensionFactor *
              ((flexible.iteration k).core.ua *
                p19StaticSystemKappa choice flexible.family *
                (flexible.iteration k).core.rhoAR) := by ring
      have hdecomp :
          (flexible.family.iteration k).xHat -
              flexible.family.system.xExact =
            expansion.gmresContribution + expansion.matrixContribution +
              (0 : P19Vector n) + expansion.remainder := by
        simpa using expansion.error_decomposition
      have hzero :
          p19VecNorm2 (0 : P19Vector n) /
              p19VecNorm2 flexible.family.system.xExact ≤ 0 := by
        simp [p19VecNorm2, p19VecNorm2Sq]
      have hbound := p19_firstOrderLe_of_four_contributions semantics
        ((flexible.family.iteration k).xHat - flexible.family.system.xExact)
        flexible.family.system.xExact
        expansion.gmresContribution expansion.matrixContribution
        (0 : P19Vector n) expansion.remainder
        ((flexible.family.iteration k).dimensionFactor *
          ((flexible.iteration k).core.ug *
            p19StaticRightOperatorKappa choice flexible.preconditioner *
            p19StaticRightPreconditionerKappa choice flexible.preconditioner))
        ((flexible.family.iteration k).dimensionFactor *
          ((flexible.iteration k).core.ua *
            p19StaticSystemKappa choice flexible.family *
            (flexible.iteration k).core.rhoAR))
        0 hx hdecomp expansion.remainder_second_order hgmres hmatrix hzero
      unfold p19ForwardError
      convert hbound using 1
      simp only [p19StaticFlexibleAttainableEnvelope]
      ring
    · intro family preconditioner ug um ua etaR rhoAR
      simp only [p19StaticRightAttainableEnvelope,
        p19StaticFlexibleAttainableEnvelope]
      ring

end HighamBench
