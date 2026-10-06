import HighamBench.P19Definitions

namespace HighamBench

open scoped Matrix.Norms.L2Operator Matrix.Norms.Frobenius

private lemma p19_vecNorm2_eq_euclideanNorm {n : ℕ} (x : P19Vector n) :
    p19VecNorm2 x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [p19VecNorm2, p19VecNorm2Sq, Real.norm_eq_abs, sq_abs]

private lemma p19_vecNorm2_add_le {n : ℕ} (x y : P19Vector n) :
    p19VecNorm2 (x + y) ≤ p19VecNorm2 x + p19VecNorm2 y := by
  rw [p19_vecNorm2_eq_euclideanNorm, p19_vecNorm2_eq_euclideanNorm,
    p19_vecNorm2_eq_euclideanNorm, WithLp.toLp_add]
  exact norm_add_le _ _

private lemma p19_vecNorm2_pos {n : ℕ} {x : P19Vector n} (hx : x ≠ 0) :
    0 < p19VecNorm2 x := by
  rw [p19_vecNorm2_eq_euclideanNorm, norm_pos_iff]
  exact fun h ↦ hx (WithLp.toLp_injective 2 h)

private lemma p19_exact_solution_ne_zero {n : ℕ}
    (system : P19Theorem31System n) : system.xExact ≠ 0 := by
  intro hx
  apply system.b_nonzero
  rw [← system.exact_solution, hx]
  funext i
  simp [p19MatVec]

private lemma p19_staticKappa_nonneg (choice : P19StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P19Matrix n) :
    0 ≤ p19StaticKappa choice A Ainv := by
  cases choice
  · simp only [p19StaticKappa, p19ConditionNumberF]
    apply mul_nonneg
    · unfold p19FrobNorm
      exact norm_nonneg _
    · unfold p19FrobNorm
      exact norm_nonneg _
  · simp only [p19StaticKappa, p19Kappa2]
    apply mul_nonneg
    · unfold p19OpNorm2
      rw [Matrix.l2_opNorm_def]
      exact ContinuousLinearMap.opNorm_nonneg _
    · unfold p19OpNorm2
      rw [Matrix.l2_opNorm_def]
      exact ContinuousLinearMap.opNorm_nonneg _

private lemma p19_selected_iteration {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (mgs : P19MGSSelectionLaw family) :
    ∃ k : P19Theorem31Dimension n,
      p19IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p19MGSNearDependence (family.iteration k)) := by
  let first : P19Theorem31Dimension n :=
    ⟨1, Nat.zero_lt_one, family.system.dimension_pos⟩
  let Good := {k : P19Theorem31Dimension n //
    p19IterationWellConditioned (family.iteration k)}
  have hfirst : p19IterationWellConditioned (family.iteration first) := by
    simpa [first] using mgs.first_dimension_good
  let firstGood : Good := ⟨first, hfirst⟩
  letI : Nonempty Good := ⟨firstGood⟩
  let embed : Good → Fin (n + 1) := fun q ↦
    ⟨q.1.1, Nat.lt_succ_of_le q.1.2.2⟩
  letI : Finite Good := Finite.of_injective embed (by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact Fin.mk.inj hab)
  obtain ⟨greatest, hgreatest⟩ :=
    Finite.exists_max (fun q : Good ↦ q.1.1)
  refine ⟨greatest.1, greatest.2, ?_⟩
  by_cases hatEnd : greatest.1.1 = n
  · exact Or.inl hatEnd
  · right
    have hklt : greatest.1.1 < n :=
      lt_of_le_of_ne greatest.1.2.2 hatEnd
    let next : P19Theorem31Dimension n :=
      ⟨greatest.1.1 + 1, Nat.succ_pos _, Nat.succ_le_iff.mpr hklt⟩
    have hnext : ¬ p19IterationWellConditioned (family.iteration next) := by
      intro hgood
      have hle := hgreatest ⟨next, hgood⟩
      simp only [next] at hle
      omega
    exact mgs.loss_implies_near_dependence greatest.1.1
      greatest.1.2.1 hklt hnext

private lemma p19_four_term_norm_bound {n : ℕ}
    (a b c d : P19Vector n) :
    p19VecNorm2 (a + b + c + d) ≤
      p19VecNorm2 a + p19VecNorm2 b + p19VecNorm2 c + p19VecNorm2 d := by
  calc
    p19VecNorm2 (a + b + c + d) ≤
        p19VecNorm2 (a + b + c) + p19VecNorm2 d :=
      p19_vecNorm2_add_le _ _
    _ ≤ (p19VecNorm2 (a + b) + p19VecNorm2 c) + p19VecNorm2 d := by
      gcongr
      exact p19_vecNorm2_add_le _ _
    _ ≤ p19VecNorm2 a + p19VecNorm2 b + p19VecNorm2 c +
        p19VecNorm2 d := by
      gcongr
      exact p19_vecNorm2_add_le _ _

private lemma p19_three_term_norm_bound {n : ℕ}
    (a b c : P19Vector n) :
    p19VecNorm2 (a + b + c) ≤
      p19VecNorm2 a + p19VecNorm2 b + p19VecNorm2 c := by
  calc
    p19VecNorm2 (a + b + c) ≤
        p19VecNorm2 (a + b) + p19VecNorm2 c :=
      p19_vecNorm2_add_le _ _
    _ ≤ p19VecNorm2 a + p19VecNorm2 b + p19VecNorm2 c := by
      gcongr
      exact p19_vecNorm2_add_le _ _

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
    obtain ⟨k, hwell, hstop⟩ := p19_selected_iteration right.family mgs
    let conditions := applicability k hwell hstop
    let expansion := appendix.expansion k hwell hstop conditions
    refine ⟨k, hwell, ?_⟩
    refine ⟨p19VecNorm2 expansion.remainder /
        p19VecNorm2 right.family.system.xExact,
      expansion.remainder_second_order, ?_⟩
    have hx : right.family.system.xExact ≠ 0 :=
      p19_exact_solution_ne_zero right.family.system
    have hden : 0 < p19VecNorm2 right.family.system.xExact :=
      p19_vecNorm2_pos hx
    have hnorm :
        p19VecNorm2
            ((right.family.iteration k).xHat -
              right.family.system.xExact) ≤
          p19VecNorm2 expansion.gmresContribution +
            p19VecNorm2 expansion.reapplicationContribution +
            p19VecNorm2 expansion.matrixContribution +
            p19VecNorm2 expansion.remainder := by
      rw [expansion.error_decomposition]
      exact p19_four_term_norm_bound _ _ _ _
    have hratio :
        p19ForwardError right.family.system.xExact
            (right.family.iteration k).xHat ≤
          p19VecNorm2 expansion.gmresContribution /
              p19VecNorm2 right.family.system.xExact +
            p19VecNorm2 expansion.reapplicationContribution /
              p19VecNorm2 right.family.system.xExact +
            p19VecNorm2 expansion.matrixContribution /
              p19VecNorm2 right.family.system.xExact +
            p19VecNorm2 expansion.remainder /
              p19VecNorm2 right.family.system.xExact := by
      rw [p19ForwardError]
      calc
        p19VecNorm2
              ((right.family.iteration k).xHat -
                right.family.system.xExact) /
              p19VecNorm2 right.family.system.xExact ≤
            (p19VecNorm2 expansion.gmresContribution +
                p19VecNorm2 expansion.reapplicationContribution +
                p19VecNorm2 expansion.matrixContribution +
                p19VecNorm2 expansion.remainder) /
              p19VecNorm2 right.family.system.xExact :=
          div_le_div_of_nonneg_right hnorm hden.le
        _ = _ := by ring
    rcases conditions.core.parameters_nonneg with
      ⟨hug, hum, hua, hetaR, hrhoAR⟩
    have hop : 0 ≤
        p19StaticRightOperatorKappa choice right.preconditioner :=
      p19_staticKappa_nonneg choice _ _
    have hmr : 0 ≤
        p19StaticRightPreconditionerKappa choice right.preconditioner :=
      p19_staticKappa_nonneg choice _ _
    have hsys : 0 ≤ p19StaticSystemKappa choice right.family :=
      p19_staticKappa_nonneg choice _ _
    have hgmres :
        p19VecNorm2 expansion.gmresContribution /
              p19VecNorm2 right.family.system.xExact ≤
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
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            conditions.core.gmres_magnitude_bound hop) hmr
    have hreapplication :
        p19VecNorm2 expansion.reapplicationContribution /
              p19VecNorm2 right.family.system.xExact ≤
          (right.family.iteration k).dimensionFactor *
              (right.iteration k).core.um *
              (right.iteration k).core.etaR *
              p19StaticRightPreconditionerKappa choice
                right.preconditioner := by
      calc
        _ ≤ (right.iteration k).reapplicationMagnitude *
              p19StaticRightPreconditionerKappa choice
                right.preconditioner := expansion.reapplication_gain_bound
        _ ≤ _ := mul_le_mul_of_nonneg_right
          conditions.reapplication_magnitude_bound hmr
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
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            conditions.core.matrix_magnitude_bound hsys) hrhoAR
    calc
      p19ForwardError right.family.system.xExact
          (right.family.iteration k).xHat ≤
        p19VecNorm2 expansion.gmresContribution /
              p19VecNorm2 right.family.system.xExact +
            p19VecNorm2 expansion.reapplicationContribution /
              p19VecNorm2 right.family.system.xExact +
            p19VecNorm2 expansion.matrixContribution /
              p19VecNorm2 right.family.system.xExact +
            p19VecNorm2 expansion.remainder /
              p19VecNorm2 right.family.system.xExact := hratio
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
            |p19VecNorm2 expansion.remainder /
              p19VecNorm2 right.family.system.xExact| := by
        linarith [le_abs_self
          (p19VecNorm2 expansion.remainder /
            p19VecNorm2 right.family.system.xExact)]
      _ = (right.family.iteration k).dimensionFactor *
              p19StaticRightAttainableEnvelope choice right.preconditioner
                (right.iteration k).core.ug
                (right.iteration k).core.um
                (right.iteration k).core.ua
                (right.iteration k).core.etaR
                (right.iteration k).core.rhoAR +
            |p19VecNorm2 expansion.remainder /
              p19VecNorm2 right.family.system.xExact| := by
        unfold p19StaticRightAttainableEnvelope
        ring
  · constructor
    · intro flexible mgs appendix applicability
      obtain ⟨k, hwell, hstop⟩ :=
        p19_selected_iteration flexible.family mgs
      let conditions := applicability k hwell hstop
      let expansion := appendix.expansion k hwell hstop conditions
      refine ⟨k, hwell, ?_⟩
      refine ⟨p19VecNorm2 expansion.remainder /
          p19VecNorm2 flexible.family.system.xExact,
        expansion.remainder_second_order, ?_⟩
      have hx : flexible.family.system.xExact ≠ 0 :=
        p19_exact_solution_ne_zero flexible.family.system
      have hden : 0 < p19VecNorm2 flexible.family.system.xExact :=
        p19_vecNorm2_pos hx
      have hnorm :
          p19VecNorm2
              ((flexible.family.iteration k).xHat -
                flexible.family.system.xExact) ≤
            p19VecNorm2 expansion.gmresContribution +
              p19VecNorm2 expansion.matrixContribution +
              p19VecNorm2 expansion.remainder := by
        rw [expansion.error_decomposition]
        exact p19_three_term_norm_bound _ _ _
      have hratio :
          p19ForwardError flexible.family.system.xExact
              (flexible.family.iteration k).xHat ≤
            p19VecNorm2 expansion.gmresContribution /
                p19VecNorm2 flexible.family.system.xExact +
              p19VecNorm2 expansion.matrixContribution /
                p19VecNorm2 flexible.family.system.xExact +
              p19VecNorm2 expansion.remainder /
                p19VecNorm2 flexible.family.system.xExact := by
        rw [p19ForwardError]
        calc
          p19VecNorm2
                ((flexible.family.iteration k).xHat -
                  flexible.family.system.xExact) /
                p19VecNorm2 flexible.family.system.xExact ≤
              (p19VecNorm2 expansion.gmresContribution +
                  p19VecNorm2 expansion.matrixContribution +
                  p19VecNorm2 expansion.remainder) /
                p19VecNorm2 flexible.family.system.xExact :=
            div_le_div_of_nonneg_right hnorm hden.le
          _ = _ := by ring
      rcases conditions.core.parameters_nonneg with
        ⟨hug, hum, hua, hetaR, hrhoAR⟩
      have hop : 0 ≤
          p19StaticRightOperatorKappa choice flexible.preconditioner :=
        p19_staticKappa_nonneg choice _ _
      have hmr : 0 ≤
          p19StaticRightPreconditionerKappa choice flexible.preconditioner :=
        p19_staticKappa_nonneg choice _ _
      have hsys : 0 ≤ p19StaticSystemKappa choice flexible.family :=
        p19_staticKappa_nonneg choice _ _
      have hgmres :
          p19VecNorm2 expansion.gmresContribution /
                p19VecNorm2 flexible.family.system.xExact ≤
            (flexible.family.iteration k).dimensionFactor *
                (flexible.iteration k).core.ug *
                p19StaticRightOperatorKappa choice
                  flexible.preconditioner *
                p19StaticRightPreconditionerKappa choice
                  flexible.preconditioner := by
        calc
          _ ≤ (flexible.iteration k).core.gmresMagnitude *
                p19StaticRightOperatorKappa choice
                  flexible.preconditioner *
                p19StaticRightPreconditionerKappa choice
                  flexible.preconditioner := expansion.gmres_gain_bound
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              conditions.core.gmres_magnitude_bound hop) hmr
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
                (flexible.iteration k).core.rhoAR :=
            expansion.matrix_gain_bound
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              conditions.core.matrix_magnitude_bound hsys) hrhoAR
      calc
        p19ForwardError flexible.family.system.xExact
            (flexible.family.iteration k).xHat ≤
          p19VecNorm2 expansion.gmresContribution /
                p19VecNorm2 flexible.family.system.xExact +
              p19VecNorm2 expansion.matrixContribution /
                p19VecNorm2 flexible.family.system.xExact +
              p19VecNorm2 expansion.remainder /
                p19VecNorm2 flexible.family.system.xExact := hratio
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
              |p19VecNorm2 expansion.remainder /
                p19VecNorm2 flexible.family.system.xExact| := by
          linarith [le_abs_self
            (p19VecNorm2 expansion.remainder /
              p19VecNorm2 flexible.family.system.xExact)]
        _ = (flexible.family.iteration k).dimensionFactor *
                p19StaticFlexibleAttainableEnvelope choice
                  flexible.preconditioner
                  (flexible.iteration k).core.ug
                  (flexible.iteration k).core.ua
                  (flexible.iteration k).core.rhoAR +
              |p19VecNorm2 expansion.remainder /
                p19VecNorm2 flexible.family.system.xExact| := by
          unfold p19StaticFlexibleAttainableEnvelope
          ring
    · intro family preconditioner ug um ua etaR rhoAR
      unfold p19StaticRightAttainableEnvelope
        p19StaticFlexibleAttainableEnvelope
      ring

end HighamBench
