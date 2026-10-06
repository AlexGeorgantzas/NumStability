import HighamBench.P20Definitions

namespace HighamBench

lemma p20InfNormRect_nonneg {m n : ℕ} (A : P20Matrix m n) :
    0 ≤ p20InfNormRect A := by
  unfold p20InfNormRect
  positivity

lemma p20InfNormRect_add_le {m n : ℕ} (A B : P20Matrix m n) :
    p20InfNormRect (A + B) ≤ p20InfNormRect A + p20InfNormRect B := by
  letI := Matrix.linftyOpSeminormedAddCommGroup (m := Fin m) (n := Fin n) (α := ℝ)
  simpa only [p20InfNormRect, Matrix.linfty_opNorm_def] using norm_add_le A B

lemma p20InfNormRect_neg {m n : ℕ} (A : P20Matrix m n) :
    p20InfNormRect (-A) = p20InfNormRect A := by
  letI := Matrix.linftyOpSeminormedAddCommGroup (m := Fin m) (n := Fin n) (α := ℝ)
  simpa only [p20InfNormRect, Matrix.linfty_opNorm_def] using norm_neg A

lemma p20InfNormRect_sub_le {m n : ℕ} (A B : P20Matrix m n) :
    p20InfNormRect (A - B) ≤ p20InfNormRect A + p20InfNormRect B := by
  rw [sub_eq_add_neg]
  simpa only [p20InfNormRect_neg] using p20InfNormRect_add_le A (-B)

lemma p20InfNormRect_mul_le {m n q : ℕ}
    (A : P20Matrix m n) (B : P20Matrix n q) :
    p20InfNormRect (A * B) ≤ p20InfNormRect A * p20InfNormRect B := by
  letI := Matrix.linftyOpSeminormedAddCommGroup (m := Fin m) (n := Fin q) (α := ℝ)
  simpa only [p20InfNormRect, Matrix.linfty_opNorm_def] using
    Matrix.linfty_opNorm_mul A B

lemma p20UnitRoundoff_le_half (precision : ℕ) (hprecision : 0 < precision) :
    p20UnitRoundoff precision ≤ (2 : ℝ)⁻¹ := by
  unfold p20UnitRoundoff
  exact pow_le_of_le_one (by positivity) (by norm_num) (Nat.ne_of_gt hprecision)

lemma p20MaxFinite_nonneg (precision : ℕ) (maxExponent : ℤ)
    (hprecision : 0 < precision) :
    0 ≤ p20MaxFinite precision maxExponent := by
  have hu_nonneg : 0 ≤ p20UnitRoundoff precision := by
    unfold p20UnitRoundoff
    positivity
  have hu_le := p20UnitRoundoff_le_half precision hprecision
  unfold p20MaxFinite
  have : 0 ≤ 2 - 2 * p20UnitRoundoff precision := by
    norm_num at hu_le ⊢
    linarith
  positivity

lemma p20UnderflowEnvelope_nonneg (precision : ℕ) (minExponent : ℤ)
    (hasSubnormals : Bool) :
    0 ≤ p20UnderflowEnvelope precision minExponent hasSubnormals := by
  unfold p20UnderflowEnvelope
  cases hasSubnormals <;> simp only
  · unfold p20MinNormal
    positivity
  · unfold p20UnitRoundoff p20MinNormal
    positivity

lemma p20StaticScalingThreshold_nonneg (n : ℕ)
    (model : P20StaticNearestModel1) :
    0 ≤ p20StaticScalingThreshold n model := by
  rw [p20StaticScalingThreshold, p20ScalingThreshold]
  exact le_min
    (p20MaxFinite_nonneg _ _ model.inputFormat.precision_pos)
    (Real.sqrt_nonneg _)

theorem p20_t3_multiword_forward_error
    {m n q p : ℕ} (semantics : P20FirstOrderSemantics) :
    (∀ (run : P20StaticMultiwordRun m n q p),
      P20StaticSection4Derivation semantics run →
        p20FirstOrderLe semantics
          (p20StaticMultiwordForwardError run)
          (p20NormwiseEnvelope
            (p20MultiNarrowCoefficient n p
              (p20StaticInputUnitRoundoff run.model)
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticInputUnderflowEnvelope run.model)
              (p20StaticAccumUnderflowEnvelope run.model))
            run.A run.B)) ∧
      (∀ (run : P20StaticMultiwordRun m n q p),
        P20StaticSection4Derivation semantics run →
          p20FirstOrderLe semantics
            (p20StaticMultiwordForwardError run)
            (p20NormwiseEnvelope
              (p20MultiRangeFreeCoefficient n p
                (p20StaticInputUnitRoundoff run.model)
                (p20StaticAccumUnitRoundoff run.model))
              run.A run.B +
            p20NormwiseEnvelope
              (p20MultiInputUnderflowCoefficient n p
                (p20StaticInputUnitRoundoff run.model)
                (p20StaticScalingThreshold n run.model)
                (p20StaticInputUnderflowEnvelope run.model))
              run.A run.B +
            p20NormwiseEnvelope
              (p20MultiAccumUnderflowCoefficient n p
                (p20StaticScalingThreshold n run.model)
                (p20StaticAccumUnderflowEnvelope run.model))
              run.A run.B)) ∧
      (∀ run : P20StaticMultiwordRun m n q p,
        p20MultiInputRoundingCoefficient p
              (p20StaticInputUnitRoundoff run.model) =
            ((((p : ℝ) + 1) / 2) *
                p20StaticInputUnitRoundoff run.model ^ (p - 1)) *
              p20SingleInputRoundingCoefficient
                (p20StaticInputUnitRoundoff run.model) ∧
          (n : ℝ) *
              p20MultiInputUnderflowCoefficient n p
                (p20StaticInputUnitRoundoff run.model)
                (p20StaticScalingThreshold n run.model)
                (p20StaticInputUnderflowEnvelope run.model) =
            p20StaticInputUnitRoundoff run.model ^ (p - 1) *
              p20SingleInputUnderflowCoefficient n
                (p20StaticScalingThreshold n run.model)
                (p20StaticInputUnderflowEnvelope run.model)) := by
  -- PROOF_START P20-T3-H001
  have main : ∀ (run : P20StaticMultiwordRun m n q p),
      P20StaticSection4Derivation semantics run →
        p20FirstOrderLe semantics
          (p20StaticMultiwordForwardError run)
          (p20NormwiseEnvelope
            (p20MultiNarrowCoefficient n p
              (p20StaticInputUnitRoundoff run.model)
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticInputUnderflowEnvelope run.model)
              (p20StaticAccumUnderflowEnvelope run.model))
            run.A run.B) := by
    intro run derivation
    have h_error_decomposition :
        run.computed - run.A * run.B =
          p20StaticAccumulationError run -
            p20StaticOmittedWordTail run -
              run.A * derivation.BError -
                derivation.AError * run.B +
                  derivation.AError * derivation.BError := by
      rw [p20StaticAccumulationError, derivation.retained_partition]
      rw [derivation.A_decomposition, derivation.B_decomposition]
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
        add_mul, mul_add, Finset.sum_add_distrib]
      ring
    have h_norm_decomposition :
        p20StaticMultiwordForwardError run ≤
          p20InfNormRect (p20StaticAccumulationError run) +
            p20InfNormRect (p20StaticOmittedWordTail run) +
              p20InfNormRect (run.A * derivation.BError) +
                p20InfNormRect (derivation.AError * run.B) +
                  p20InfNormRect (derivation.AError * derivation.BError) := by
      rw [p20StaticMultiwordForwardError, h_error_decomposition]
      calc
        p20InfNormRect
            (p20StaticAccumulationError run -
                p20StaticOmittedWordTail run -
                  run.A * derivation.BError -
                    derivation.AError * run.B +
                      derivation.AError * derivation.BError) ≤
            p20InfNormRect
                (p20StaticAccumulationError run -
                    p20StaticOmittedWordTail run -
                      run.A * derivation.BError -
                        derivation.AError * run.B) +
              p20InfNormRect (derivation.AError * derivation.BError) :=
          p20InfNormRect_add_le _ _
        _ ≤ (p20InfNormRect
                (p20StaticAccumulationError run -
                    p20StaticOmittedWordTail run -
                      run.A * derivation.BError) +
              p20InfNormRect (derivation.AError * run.B)) +
                p20InfNormRect (derivation.AError * derivation.BError) := by
          gcongr
          exact p20InfNormRect_sub_le _ _
        _ ≤ ((p20InfNormRect
                (p20StaticAccumulationError run -
                  p20StaticOmittedWordTail run) +
              p20InfNormRect (run.A * derivation.BError)) +
                p20InfNormRect (derivation.AError * run.B)) +
                  p20InfNormRect (derivation.AError * derivation.BError) := by
          gcongr
          exact p20InfNormRect_sub_le _ _
        _ ≤ (((p20InfNormRect (p20StaticAccumulationError run) +
                p20InfNormRect (p20StaticOmittedWordTail run)) +
              p20InfNormRect (run.A * derivation.BError)) +
                p20InfNormRect (derivation.AError * run.B)) +
                  p20InfNormRect (derivation.AError * derivation.BError) := by
          gcongr
          exact p20InfNormRect_sub_le _ _
    have hu_nonneg :
        0 ≤ p20StaticInputUnitRoundoff run.model := by
      unfold p20StaticInputUnitRoundoff p20UnitRoundoff
      positivity
    have hzeta_nonneg : 0 ≤ p20StaticZeta run := by
      rw [p20StaticZeta]
      exact (pow_nonneg hu_nonneg p).trans (le_max_left _ _)
    have hA_nonneg : 0 ≤ p20InfNormRect run.A :=
      p20InfNormRect_nonneg _
    have hB_nonneg : 0 ≤ p20InfNormRect run.B :=
      p20InfNormRect_nonneg _
    have htheta_nonneg :
        0 ≤ p20StaticScalingThreshold n run.model :=
      p20StaticScalingThreshold_nonneg _ _
    have hgmin_nonneg :
        0 ≤ p20StaticInputUnderflowEnvelope run.model := by
      exact p20UnderflowEnvelope_nonneg _ _ _
    have hGmin_nonneg :
        0 ≤ p20StaticAccumUnderflowEnvelope run.model := by
      exact p20UnderflowEnvelope_nonneg _ _ _
    have hzeta_upper :
        p20StaticZeta run ≤
          p20StaticInputUnitRoundoff run.model ^ p +
            2 * (n : ℝ) *
              p20StaticInputUnitRoundoff run.model ^ (p - 1) *
                (p20StaticScalingThreshold n run.model)⁻¹ *
                  p20StaticInputUnderflowEnvelope run.model := by
      rw [p20StaticZeta]
      apply max_le
      · exact le_add_of_nonneg_right (by positivity)
      · exact le_add_of_nonneg_left (pow_nonneg hu_nonneg p)
    have h_input_coefficient :
        2 * p20StaticZeta run +
            p20StaticOmittedCoefficient p
              (p20StaticInputUnitRoundoff run.model) ≤
          p20MultiInputRoundingCoefficient p
              (p20StaticInputUnitRoundoff run.model) +
            p20MultiInputUnderflowCoefficient n p
              (p20StaticInputUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticInputUnderflowEnvelope run.model) := by
      calc
        _ ≤ 2 *
              (p20StaticInputUnitRoundoff run.model ^ p +
                2 * (n : ℝ) *
                  p20StaticInputUnitRoundoff run.model ^ (p - 1) *
                    (p20StaticScalingThreshold n run.model)⁻¹ *
                      p20StaticInputUnderflowEnvelope run.model) +
                p20StaticOmittedCoefficient p
                  (p20StaticInputUnitRoundoff run.model) := by
            gcongr
        _ = _ := by
          simp only [p20StaticOmittedCoefficient,
            p20MultiInputRoundingCoefficient,
            p20MultiInputUnderflowCoefficient]
          ring
    have h_A_BError :
        p20InfNormRect (run.A * derivation.BError) ≤
          p20StaticZeta run * p20InfNormRect run.A *
            p20InfNormRect run.B := by
      calc
        _ ≤ p20InfNormRect run.A * p20InfNormRect derivation.BError :=
          p20InfNormRect_mul_le _ _
        _ ≤ p20InfNormRect run.A *
            (p20StaticZeta run * p20InfNormRect run.B) := by
          gcongr
          exact derivation.B_error_bound
        _ = _ := by ring
    have h_AError_B :
        p20InfNormRect (derivation.AError * run.B) ≤
          p20StaticZeta run * p20InfNormRect run.A *
            p20InfNormRect run.B := by
      calc
        _ ≤ p20InfNormRect derivation.AError * p20InfNormRect run.B :=
          p20InfNormRect_mul_le _ _
        _ ≤ (p20StaticZeta run * p20InfNormRect run.A) *
            p20InfNormRect run.B := by
          gcongr
          exact derivation.A_error_bound
    have h_quadratic :
        p20InfNormRect (derivation.AError * derivation.BError) ≤
          p20StaticZeta run ^ 2 * p20InfNormRect run.A *
            p20InfNormRect run.B := by
      calc
        _ ≤ p20InfNormRect derivation.AError *
            p20InfNormRect derivation.BError := p20InfNormRect_mul_le _ _
        _ ≤ (p20StaticZeta run * p20InfNormRect run.A) *
            (p20StaticZeta run * p20InfNormRect run.B) := by
          exact mul_le_mul derivation.A_error_bound derivation.B_error_bound
            (p20InfNormRect_nonneg _)
            (mul_nonneg hzeta_nonneg hA_nonneg)
        _ = _ := by ring
    have h_underflow_count_term :
        4 * (derivation.underflowCount : ℝ) * (n : ℝ) *
              ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
                p20StaticAccumUnderflowEnvelope run.model ≤
          2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 *
              ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
                p20StaticAccumUnderflowEnvelope run.model := by
      calc
        _ = (derivation.underflowCount : ℝ) *
              (4 * (n : ℝ) *
                ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
                  p20StaticAccumUnderflowEnvelope run.model) := by ring
        _ ≤ ((n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2) *
              (4 * (n : ℝ) *
                ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
                  p20StaticAccumUnderflowEnvelope run.model) := by
            exact mul_le_mul_of_nonneg_right derivation.underflow_count_bound
              (by positivity)
        _ = _ := by ring
    have h_raw_accumulation_coefficient :
        p20StaticRawAccumulationCoefficient n p derivation.underflowCount
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model) ≤
          p20StaticAccumulationCoefficient n p
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model) := by
      unfold p20StaticRawAccumulationCoefficient
        p20StaticAccumulationCoefficient
        p20MultiAccumUnderflowCoefficient
      gcongr
    have h_accumulation_error :
        p20InfNormRect (p20StaticAccumulationError run) ≤
          p20NormwiseEnvelope
              (p20StaticAccumulationCoefficient n p
                (p20StaticAccumUnitRoundoff run.model)
                (p20StaticScalingThreshold n run.model)
                (p20StaticAccumUnderflowEnvelope run.model))
              run.A run.B +
            |derivation.accumulationRemainder| := by
      refine derivation.accumulation_error_bound.trans ?_
      gcongr
      unfold p20NormwiseEnvelope
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h_raw_accumulation_coefficient hA_nonneg)
        hB_nonneg
    have h_total_coefficient :
        p20StaticAccumulationCoefficient n p
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticAccumUnderflowEnvelope run.model) +
            p20StaticOmittedCoefficient p
              (p20StaticInputUnitRoundoff run.model) +
            2 * p20StaticZeta run ≤
          p20MultiNarrowCoefficient n p
              (p20StaticInputUnitRoundoff run.model)
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticInputUnderflowEnvelope run.model)
              (p20StaticAccumUnderflowEnvelope run.model) := by
      calc
        _ = p20StaticAccumulationCoefficient n p
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticAccumUnderflowEnvelope run.model) +
            (2 * p20StaticZeta run +
              p20StaticOmittedCoefficient p
                (p20StaticInputUnitRoundoff run.model)) := by ring
        _ ≤ p20StaticAccumulationCoefficient n p
                (p20StaticAccumUnitRoundoff run.model)
                (p20StaticScalingThreshold n run.model)
                (p20StaticAccumUnderflowEnvelope run.model) +
              (p20MultiInputRoundingCoefficient p
                  (p20StaticInputUnitRoundoff run.model) +
                p20MultiInputUnderflowCoefficient n p
                  (p20StaticInputUnitRoundoff run.model)
                  (p20StaticScalingThreshold n run.model)
                  (p20StaticInputUnderflowEnvelope run.model)) := by
            gcongr
        _ = _ := by
          simp only [p20StaticAccumulationCoefficient,
            p20MultiNarrowCoefficient, p20MultiRangeFreeCoefficient]
          ring
    let quadratic := p20StaticZeta run ^ 2 * p20InfNormRect run.A *
      p20InfNormRect run.B
    let remainder := |derivation.accumulationRemainder| +
      |derivation.omittedRemainder| + quadratic
    have h_components :
        p20StaticMultiwordForwardError run ≤
          (p20NormwiseEnvelope
                (p20StaticAccumulationCoefficient n p
                  (p20StaticAccumUnitRoundoff run.model)
                  (p20StaticScalingThreshold n run.model)
                  (p20StaticAccumUnderflowEnvelope run.model))
                run.A run.B +
              |derivation.accumulationRemainder|) +
            (p20NormwiseEnvelope
                (p20StaticOmittedCoefficient p
                  (p20StaticInputUnitRoundoff run.model)) run.A run.B +
              |derivation.omittedRemainder|) +
            p20StaticZeta run * p20InfNormRect run.A *
              p20InfNormRect run.B +
            p20StaticZeta run * p20InfNormRect run.A *
              p20InfNormRect run.B +
            quadratic := by
      dsimp only [quadratic]
      linarith [h_norm_decomposition, h_accumulation_error,
        derivation.omitted_tail_bound, h_A_BError, h_AError_B, h_quadratic]
    have h_forward :
        p20StaticMultiwordForwardError run ≤
          p20NormwiseEnvelope
              (p20MultiNarrowCoefficient n p
                (p20StaticInputUnitRoundoff run.model)
                (p20StaticAccumUnitRoundoff run.model)
                (p20StaticScalingThreshold n run.model)
                (p20StaticInputUnderflowEnvelope run.model)
                (p20StaticAccumUnderflowEnvelope run.model))
              run.A run.B + remainder := by
      calc
        _ ≤ _ := h_components
        _ = (p20StaticAccumulationCoefficient n p
                  (p20StaticAccumUnitRoundoff run.model)
                  (p20StaticScalingThreshold n run.model)
                  (p20StaticAccumUnderflowEnvelope run.model) +
                p20StaticOmittedCoefficient p
                  (p20StaticInputUnitRoundoff run.model) +
                2 * p20StaticZeta run) *
              p20InfNormRect run.A * p20InfNormRect run.B +
            remainder := by
              simp only [p20NormwiseEnvelope, remainder, quadratic]
              ring
        _ ≤ p20MultiNarrowCoefficient n p
                  (p20StaticInputUnitRoundoff run.model)
                  (p20StaticAccumUnitRoundoff run.model)
                  (p20StaticScalingThreshold n run.model)
                  (p20StaticInputUnderflowEnvelope run.model)
                  (p20StaticAccumUnderflowEnvelope run.model) *
                p20InfNormRect run.A * p20InfNormRect run.B +
              remainder := by
            gcongr
        _ = _ := rfl
    unfold p20FirstOrderLe
    refine ⟨remainder, ?_, ?_⟩
    · dsimp only [remainder]
      exact semantics.add_secondOrder
        (semantics.add_secondOrder
          (semantics.abs_secondOrder
            derivation.accumulation_remainder_second_order)
          (semantics.abs_secondOrder
            derivation.omitted_remainder_second_order))
        derivation.quadratic_second_order
    · have hquadratic_nonneg : 0 ≤ quadratic := by
        dsimp only [quadratic]
        positivity
      rw [abs_of_nonneg]
      · exact h_forward
      · dsimp only [remainder]
        positivity
  refine ⟨main, ?_, ?_⟩
  · intro run derivation
    simpa only [p20MultiNarrowCoefficient, p20NormwiseEnvelope,
      mul_add, add_mul] using main run derivation
  · intro run
    constructor
    · have hp : p - 1 + 1 = p := Nat.sub_add_cancel run.word_count_pos
      have hu_pow : p20StaticInputUnitRoundoff run.model ^ p =
          p20StaticInputUnitRoundoff run.model ^ (p - 1) *
            p20StaticInputUnitRoundoff run.model := by
        calc
          _ = p20StaticInputUnitRoundoff run.model ^ (p - 1 + 1) := by rw [hp]
          _ = _ := pow_succ _ _
      simp only [p20MultiInputRoundingCoefficient,
        p20SingleInputRoundingCoefficient]
      rw [hu_pow]
      ring
    · simp only [p20MultiInputUnderflowCoefficient,
        p20SingleInputUnderflowCoefficient]
      ring

end HighamBench
