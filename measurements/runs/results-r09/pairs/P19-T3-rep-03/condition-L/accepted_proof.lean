import HighamBench.P19Definitions

namespace HighamBench

open scoped Matrix.Norms.L2Operator Matrix.Norms.Frobenius

noncomputable def p19EuclideanVector {n : ℕ} (x : P19Vector n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 x

lemma p19VecNorm2_eq_norm {n : ℕ} (x : P19Vector n) :
    p19VecNorm2 x = ‖p19EuclideanVector x‖ := by
  rw [p19VecNorm2, EuclideanSpace.norm_eq]
  congr 1
  simp [p19VecNorm2Sq, p19EuclideanVector]

lemma p19EuclideanVector_add {n : ℕ} (x y : P19Vector n) :
    p19EuclideanVector (x + y) =
      p19EuclideanVector x + p19EuclideanVector y := by
  ext i
  rfl

lemma p19VecNorm2_add_le {n : ℕ} (x y : P19Vector n) :
    p19VecNorm2 (x + y) ≤ p19VecNorm2 x + p19VecNorm2 y := by
  rw [p19VecNorm2_eq_norm, p19VecNorm2_eq_norm,
    p19VecNorm2_eq_norm, p19EuclideanVector_add]
  exact norm_add_le _ _

lemma p19VecNorm2_pos {n : ℕ} (x : P19Vector n) (hx : x ≠ 0) :
    0 < p19VecNorm2 x := by
  rw [p19VecNorm2_eq_norm]
  exact norm_pos_iff.mpr (by
    intro h
    apply hx
    ext i
    have hi := congrFun (congrArg WithLp.ofLp h) i
    exact hi)

lemma p19VecNorm2_nonneg {n : ℕ} (x : P19Vector n) :
    0 ≤ p19VecNorm2 x := by
  rw [p19VecNorm2_eq_norm]
  exact norm_nonneg _

lemma p19Theorem31_xExact_ne_zero {n : ℕ}
    (system : P19Theorem31System n) : system.xExact ≠ 0 := by
  intro hx
  apply system.b_nonzero
  rw [← system.exact_solution, hx]
  ext i
  simp [p19MatVec]

lemma p19FrobNorm_nonneg {m k : ℕ} (A : P19RectMatrix m k) :
    0 ≤ p19FrobNorm A := by
  unfold p19FrobNorm
  exact norm_nonneg _

lemma p19OpNorm2_nonneg {n : ℕ} (A : P19Matrix n) :
    0 ≤ p19OpNorm2 A := by
  unfold p19OpNorm2
  exact @norm_nonneg (Matrix (Fin n) (Fin n) ℝ)
    (Matrix.instL2OpNormedAddCommGroup
      (𝕜 := ℝ) (m := Fin n) (n := Fin n)).toSeminormedAddCommGroup.toSeminormedAddGroup A

lemma p19StaticKappa_nonneg (choice : P19StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P19Matrix n) :
    0 ≤ p19StaticKappa choice A Ainv := by
  cases choice
  · simp only [p19StaticKappa, p19ConditionNumberF]
    exact mul_nonneg (p19FrobNorm_nonneg _) (p19FrobNorm_nonneg _)
  · simp only [p19StaticKappa, p19Kappa2]
    exact mul_nonneg (p19OpNorm2_nonneg _) (p19OpNorm2_nonneg _)

lemma p19StaticSystemKappa_nonneg (choice : P19StaticSquareKappaChoice)
    {n : ℕ} {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics) :
    0 ≤ p19StaticSystemKappa choice family := by
  exact p19StaticKappa_nonneg choice family.system.A family.system.Ainv

lemma p19StaticRightPreconditionerKappa_nonneg
    (choice : P19StaticSquareKappaChoice)
    {n : ℕ} {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family) :
    0 ≤ p19StaticRightPreconditionerKappa choice preconditioner := by
  exact p19StaticKappa_nonneg choice preconditioner.MR preconditioner.MRinv

lemma p19StaticRightOperatorKappa_nonneg
    (choice : P19StaticSquareKappaChoice)
    {n : ℕ} {semantics : P19FirstOrderSemantics}
    {family : P19Theorem31Family n semantics}
    (preconditioner : P19StaticFixedRightPreconditioner family) :
    0 ≤ p19StaticRightOperatorKappa choice preconditioner := by
  exact p19StaticKappa_nonneg choice
    (p19SquareRectMul family.system.A preconditioner.MRinv)
    (p19SquareRectMul preconditioner.MR family.system.Ainv)

lemma p19_exists_mgs_iteration {n : ℕ}
    {semantics : P19FirstOrderSemantics}
    (family : P19Theorem31Family n semantics)
    (mgs : P19MGSSelectionLaw family) :
    ∃ k : P19Theorem31Dimension n,
      p19IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p19MGSNearDependence (family.iteration k)) := by
  classical
  by_cases hall : ∀ k : P19Theorem31Dimension n,
      p19IterationWellConditioned (family.iteration k)
  · let last : P19Theorem31Dimension n :=
      ⟨n, family.system.dimension_pos, le_rfl⟩
    exact ⟨last, hall last, Or.inl rfl⟩
  · let Bad : ℕ → Prop := fun j ↦
      ∃ (hjpos : 0 < j) (hjle : j ≤ n),
        ¬ p19IterationWellConditioned
          (family.iteration ⟨j, hjpos, hjle⟩)
    have hbad : ∃ j, Bad j := by
      push_neg at hall
      obtain ⟨j, hj⟩ := hall
      exact ⟨j.1, j.2.1, j.2.2, hj⟩
    let j := Nat.find hbad
    have hjbad : Bad j := Nat.find_spec hbad
    obtain ⟨hjpos, hjle, hjnot⟩ := hjbad
    have hjne : j ≠ 1 := by
      intro h
      have heq : (⟨j, hjpos, hjle⟩ : P19Theorem31Dimension n) =
          ⟨1, Nat.zero_lt_one, family.system.dimension_pos⟩ := by
        apply Subtype.ext
        exact h
      rw [heq] at hjnot
      apply hjnot
      exact mgs.first_dimension_good
    have hjgt : 1 < j := by omega
    have hpredpos : 0 < j - 1 := by omega
    have hpredlt : j - 1 < n := by omega
    let current : P19Theorem31Dimension n :=
      ⟨j - 1, hpredpos, Nat.le_of_lt hpredlt⟩
    have hcurrent :
        p19IterationWellConditioned (family.iteration current) := by
      by_contra hnot
      have hbadpred : Bad (j - 1) :=
        ⟨hpredpos, Nat.le_of_lt hpredlt, hnot⟩
      exact (Nat.find_min hbad (by omega)) hbadpred
    have hnear : p19MGSNearDependence (family.iteration current) := by
      have hloss := mgs.loss_implies_near_dependence
        (j - 1) hpredpos hpredlt
      apply hloss
      intro hnext
      have heq : (⟨j, hjpos, hjle⟩ : P19Theorem31Dimension n) =
          ⟨j - 1 + 1, Nat.succ_pos (j - 1),
            Nat.succ_le_iff.mpr hpredlt⟩ := by
        apply Subtype.ext
        simp
        omega
      rw [heq] at hjnot
      apply hjnot
      exact hnext
    exact ⟨current, hcurrent, Or.inr hnear⟩

lemma p19StaticRightExpansion_forward_error
    (choice : P19StaticSquareKappaChoice)
    {n : ℕ} {semantics : P19FirstOrderSemantics}
    (right : P19StaticRightFamily n semantics)
    (k : P19Theorem31Dimension n)
    (conditions : P19StaticRightConditions choice (right.iteration k))
    (expansion : P19StaticRightAppendixCExpansion choice right k) :
    p19FirstOrderLe semantics
      (p19ForwardError right.family.system.xExact
        (right.family.iteration k).xHat)
      ((right.family.iteration k).dimensionFactor *
        p19StaticRightAttainableEnvelope choice right.preconditioner
          (right.iteration k).core.ug
          (right.iteration k).core.um
          (right.iteration k).core.ua
          (right.iteration k).core.etaR
          (right.iteration k).core.rhoAR) := by
  let d := (right.family.iteration k).dimensionFactor
  let D := p19VecNorm2 right.family.system.xExact
  let g := expansion.gmresContribution
  let r := expansion.reapplicationContribution
  let a := expansion.matrixContribution
  let e := expansion.remainder
  have hD : 0 < D := by
    exact p19VecNorm2_pos _ (p19Theorem31_xExact_ne_zero right.family.system)
  have hnorm :
      p19VecNorm2 ((right.family.iteration k).xHat -
          right.family.system.xExact) ≤
        p19VecNorm2 g + p19VecNorm2 r + p19VecNorm2 a +
          p19VecNorm2 e := by
    rw [expansion.error_decomposition]
    calc
      p19VecNorm2 (g + r + a + e) ≤
          p19VecNorm2 (g + r + a) + p19VecNorm2 e :=
        p19VecNorm2_add_le _ _
      _ ≤ (p19VecNorm2 (g + r) + p19VecNorm2 a) +
          p19VecNorm2 e := by
        gcongr
        exact p19VecNorm2_add_le _ _
      _ ≤ ((p19VecNorm2 g + p19VecNorm2 r) + p19VecNorm2 a) +
          p19VecNorm2 e := by
        gcongr
        exact p19VecNorm2_add_le _ _
  have htotal :
      p19ForwardError right.family.system.xExact
          (right.family.iteration k).xHat ≤
        p19VecNorm2 g / D + p19VecNorm2 r / D +
          p19VecNorm2 a / D + p19VecNorm2 e / D := by
    rw [p19ForwardError]
    calc
      p19VecNorm2 ((right.family.iteration k).xHat -
          right.family.system.xExact) / D ≤
          (p19VecNorm2 g + p19VecNorm2 r + p19VecNorm2 a +
            p19VecNorm2 e) / D :=
        (div_le_div_iff_of_pos_right hD).2 hnorm
      _ = p19VecNorm2 g / D + p19VecNorm2 r / D +
          p19VecNorm2 a / D + p19VecNorm2 e / D := by ring
  have hop := p19StaticRightOperatorKappa_nonneg choice right.preconditioner
  have hpre :=
    p19StaticRightPreconditionerKappa_nonneg choice right.preconditioner
  have hsys := p19StaticSystemKappa_nonneg choice right.family
  have hparams := conditions.core.parameters_nonneg
  have hg : p19VecNorm2 g / D ≤
      d * ((right.iteration k).core.ug *
        p19StaticRightOperatorKappa choice right.preconditioner *
        p19StaticRightPreconditionerKappa choice right.preconditioner) := by
    calc
      p19VecNorm2 g / D ≤
          (right.iteration k).core.gmresMagnitude *
            p19StaticRightOperatorKappa choice right.preconditioner *
            p19StaticRightPreconditionerKappa choice right.preconditioner :=
        expansion.gmres_gain_bound
      _ ≤ (d * (right.iteration k).core.ug) *
            p19StaticRightOperatorKappa choice right.preconditioner *
            p19StaticRightPreconditionerKappa choice right.preconditioner := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            conditions.core.gmres_magnitude_bound hop) hpre
      _ = d * ((right.iteration k).core.ug *
            p19StaticRightOperatorKappa choice right.preconditioner *
            p19StaticRightPreconditionerKappa choice right.preconditioner) := by
        ring
  have hr : p19VecNorm2 r / D ≤
      d * ((right.iteration k).core.um *
        (right.iteration k).core.etaR *
        p19StaticRightPreconditionerKappa choice right.preconditioner) := by
    calc
      p19VecNorm2 r / D ≤
          (right.iteration k).reapplicationMagnitude *
            p19StaticRightPreconditionerKappa choice right.preconditioner :=
        expansion.reapplication_gain_bound
      _ ≤ (d * (right.iteration k).core.um *
            (right.iteration k).core.etaR) *
            p19StaticRightPreconditionerKappa choice right.preconditioner := by
        exact mul_le_mul_of_nonneg_right
          conditions.reapplication_magnitude_bound hpre
      _ = d * ((right.iteration k).core.um *
            (right.iteration k).core.etaR *
            p19StaticRightPreconditionerKappa choice right.preconditioner) := by
        ring
  have ha : p19VecNorm2 a / D ≤
      d * ((right.iteration k).core.ua *
        p19StaticSystemKappa choice right.family *
        (right.iteration k).core.rhoAR) := by
    calc
      p19VecNorm2 a / D ≤
          (right.iteration k).core.matrixMagnitude *
            p19StaticSystemKappa choice right.family *
            (right.iteration k).core.rhoAR := expansion.matrix_gain_bound
      _ ≤ (d * (right.iteration k).core.ua) *
            p19StaticSystemKappa choice right.family *
            (right.iteration k).core.rhoAR := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            conditions.core.matrix_magnitude_bound hsys) hparams.2.2.2.2
      _ = d * ((right.iteration k).core.ua *
            p19StaticSystemKappa choice right.family *
            (right.iteration k).core.rhoAR) := by ring
  refine ⟨p19VecNorm2 e / D, expansion.remainder_second_order, ?_⟩
  rw [abs_of_nonneg (div_nonneg (p19VecNorm2_nonneg _) (le_of_lt hD))]
  calc
    p19ForwardError right.family.system.xExact
        (right.family.iteration k).xHat ≤
        p19VecNorm2 g / D + p19VecNorm2 r / D +
          p19VecNorm2 a / D + p19VecNorm2 e / D := htotal
    _ ≤ d * ((right.iteration k).core.ug *
            p19StaticRightOperatorKappa choice right.preconditioner *
            p19StaticRightPreconditionerKappa choice right.preconditioner) +
          d * ((right.iteration k).core.um *
            (right.iteration k).core.etaR *
            p19StaticRightPreconditionerKappa choice right.preconditioner) +
          d * ((right.iteration k).core.ua *
            p19StaticSystemKappa choice right.family *
            (right.iteration k).core.rhoAR) + p19VecNorm2 e / D := by
      gcongr
    _ = d * p19StaticRightAttainableEnvelope choice right.preconditioner
          (right.iteration k).core.ug (right.iteration k).core.um
          (right.iteration k).core.ua (right.iteration k).core.etaR
          (right.iteration k).core.rhoAR + p19VecNorm2 e / D := by
      simp only [p19StaticRightAttainableEnvelope]
      ring

lemma p19StaticFlexibleExpansion_forward_error
    (choice : P19StaticSquareKappaChoice)
    {n : ℕ} {semantics : P19FirstOrderSemantics}
    (flexible : P19StaticFlexibleFamily n semantics)
    (k : P19Theorem31Dimension n)
    (conditions :
      P19StaticFlexibleConditions choice (flexible.iteration k))
    (expansion : P19StaticFlexibleAppendixDExpansion choice flexible k) :
    p19FirstOrderLe semantics
      (p19ForwardError flexible.family.system.xExact
        (flexible.family.iteration k).xHat)
      ((flexible.family.iteration k).dimensionFactor *
        p19StaticFlexibleAttainableEnvelope choice flexible.preconditioner
          (flexible.iteration k).core.ug
          (flexible.iteration k).core.ua
          (flexible.iteration k).core.rhoAR) := by
  let d := (flexible.family.iteration k).dimensionFactor
  let D := p19VecNorm2 flexible.family.system.xExact
  let g := expansion.gmresContribution
  let a := expansion.matrixContribution
  let e := expansion.remainder
  have hD : 0 < D := by
    exact p19VecNorm2_pos _
      (p19Theorem31_xExact_ne_zero flexible.family.system)
  have hnorm :
      p19VecNorm2 ((flexible.family.iteration k).xHat -
          flexible.family.system.xExact) ≤
        p19VecNorm2 g + p19VecNorm2 a + p19VecNorm2 e := by
    rw [expansion.error_decomposition]
    calc
      p19VecNorm2 (g + a + e) ≤
          p19VecNorm2 (g + a) + p19VecNorm2 e :=
        p19VecNorm2_add_le _ _
      _ ≤ (p19VecNorm2 g + p19VecNorm2 a) + p19VecNorm2 e := by
        gcongr
        exact p19VecNorm2_add_le _ _
  have htotal :
      p19ForwardError flexible.family.system.xExact
          (flexible.family.iteration k).xHat ≤
        p19VecNorm2 g / D + p19VecNorm2 a / D +
          p19VecNorm2 e / D := by
    rw [p19ForwardError]
    calc
      p19VecNorm2 ((flexible.family.iteration k).xHat -
          flexible.family.system.xExact) / D ≤
          (p19VecNorm2 g + p19VecNorm2 a + p19VecNorm2 e) / D :=
        (div_le_div_iff_of_pos_right hD).2 hnorm
      _ = p19VecNorm2 g / D + p19VecNorm2 a / D +
          p19VecNorm2 e / D := by ring
  have hop :=
    p19StaticRightOperatorKappa_nonneg choice flexible.preconditioner
  have hpre :=
    p19StaticRightPreconditionerKappa_nonneg choice flexible.preconditioner
  have hsys := p19StaticSystemKappa_nonneg choice flexible.family
  have hparams := conditions.core.parameters_nonneg
  have hg : p19VecNorm2 g / D ≤
      d * ((flexible.iteration k).core.ug *
        p19StaticRightOperatorKappa choice flexible.preconditioner *
        p19StaticRightPreconditionerKappa choice flexible.preconditioner) := by
    calc
      p19VecNorm2 g / D ≤
          (flexible.iteration k).core.gmresMagnitude *
            p19StaticRightOperatorKappa choice flexible.preconditioner *
            p19StaticRightPreconditionerKappa choice flexible.preconditioner :=
        expansion.gmres_gain_bound
      _ ≤ (d * (flexible.iteration k).core.ug) *
            p19StaticRightOperatorKappa choice flexible.preconditioner *
            p19StaticRightPreconditionerKappa choice flexible.preconditioner := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            conditions.core.gmres_magnitude_bound hop) hpre
      _ = d * ((flexible.iteration k).core.ug *
            p19StaticRightOperatorKappa choice flexible.preconditioner *
            p19StaticRightPreconditionerKappa choice flexible.preconditioner) := by
        ring
  have ha : p19VecNorm2 a / D ≤
      d * ((flexible.iteration k).core.ua *
        p19StaticSystemKappa choice flexible.family *
        (flexible.iteration k).core.rhoAR) := by
    calc
      p19VecNorm2 a / D ≤
          (flexible.iteration k).core.matrixMagnitude *
            p19StaticSystemKappa choice flexible.family *
            (flexible.iteration k).core.rhoAR := expansion.matrix_gain_bound
      _ ≤ (d * (flexible.iteration k).core.ua) *
            p19StaticSystemKappa choice flexible.family *
            (flexible.iteration k).core.rhoAR := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            conditions.core.matrix_magnitude_bound hsys) hparams.2.2.2.2
      _ = d * ((flexible.iteration k).core.ua *
            p19StaticSystemKappa choice flexible.family *
            (flexible.iteration k).core.rhoAR) := by ring
  refine ⟨p19VecNorm2 e / D, expansion.remainder_second_order, ?_⟩
  rw [abs_of_nonneg (div_nonneg (p19VecNorm2_nonneg _) (le_of_lt hD))]
  calc
    p19ForwardError flexible.family.system.xExact
        (flexible.family.iteration k).xHat ≤
        p19VecNorm2 g / D + p19VecNorm2 a / D +
          p19VecNorm2 e / D := htotal
    _ ≤ d * ((flexible.iteration k).core.ug *
            p19StaticRightOperatorKappa choice flexible.preconditioner *
            p19StaticRightPreconditionerKappa choice flexible.preconditioner) +
          d * ((flexible.iteration k).core.ua *
            p19StaticSystemKappa choice flexible.family *
            (flexible.iteration k).core.rhoAR) + p19VecNorm2 e / D := by
      gcongr
    _ = d * p19StaticFlexibleAttainableEnvelope choice
          flexible.preconditioner (flexible.iteration k).core.ug
          (flexible.iteration k).core.ua
          (flexible.iteration k).core.rhoAR + p19VecNorm2 e / D := by
      simp only [p19StaticFlexibleAttainableEnvelope]
      ring

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
      p19_exists_mgs_iteration right.family mgs
    have conditions := applicability k hwell hstop
    have expansion := appendix.expansion k hwell hstop conditions
    exact ⟨k, hwell,
      p19StaticRightExpansion_forward_error choice right k conditions expansion⟩
  constructor
  · intro flexible mgs appendix applicability
    obtain ⟨k, hwell, hstop⟩ :=
      p19_exists_mgs_iteration flexible.family mgs
    have conditions := applicability k hwell hstop
    have expansion := appendix.expansion k hwell hstop conditions
    exact ⟨k, hwell,
      p19StaticFlexibleExpansion_forward_error choice flexible k
        conditions expansion⟩
  · intro family preconditioner ug um ua etaR rhoAR
    simp only [p19StaticRightAttainableEnvelope,
      p19StaticFlexibleAttainableEnvelope]
    ring

end HighamBench
