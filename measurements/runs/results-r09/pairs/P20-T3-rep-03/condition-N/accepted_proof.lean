import HighamBench.P20Definitions

namespace HighamBench

private theorem p20InfNormRect_nonneg {m n : ℕ}
    (A : P20Matrix m n) : 0 ≤ p20InfNormRect A := by
  unfold p20InfNormRect
  positivity

private theorem p20InfNormRect_neg {m n : ℕ}
    (A : P20Matrix m n) : p20InfNormRect (-A) = p20InfNormRect A := by
  letI : SeminormedAddCommGroup (P20Matrix m n) :=
    Matrix.linftyOpSeminormedAddCommGroup
  simpa only [p20InfNormRect, Matrix.linfty_opNorm_def] using norm_neg A

private theorem p20InfNormRect_add_le {m n : ℕ}
    (A B : P20Matrix m n) :
    p20InfNormRect (A + B) ≤ p20InfNormRect A + p20InfNormRect B := by
  letI : SeminormedAddCommGroup (P20Matrix m n) :=
    Matrix.linftyOpSeminormedAddCommGroup
  simpa only [p20InfNormRect, Matrix.linfty_opNorm_def] using norm_add_le A B

private theorem p20InfNormRect_mul_le {m n q : ℕ}
    (A : P20Matrix m n) (B : P20Matrix n q) :
    p20InfNormRect (A * B) ≤ p20InfNormRect A * p20InfNormRect B := by
  letI : SeminormedAddCommGroup (P20Matrix m n) :=
    Matrix.linftyOpSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (P20Matrix n q) :=
    Matrix.linftyOpSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (P20Matrix m q) :=
    Matrix.linftyOpSeminormedAddCommGroup
  simpa only [p20InfNormRect, Matrix.linfty_opNorm_def] using
    Matrix.linfty_opNorm_mul A B

private theorem p20InfNormRect_five_le {m n : ℕ}
    (A B C D E : P20Matrix m n) :
    p20InfNormRect (A + B + C + D + E) ≤
      p20InfNormRect A + p20InfNormRect B + p20InfNormRect C +
        p20InfNormRect D + p20InfNormRect E := by
  calc
    p20InfNormRect (A + B + C + D + E) ≤
        p20InfNormRect (A + B + C + D) + p20InfNormRect E :=
      p20InfNormRect_add_le _ _
    _ ≤ (p20InfNormRect (A + B + C) + p20InfNormRect D) +
        p20InfNormRect E := by
      gcongr
      exact p20InfNormRect_add_le _ _
    _ ≤ ((p20InfNormRect (A + B) + p20InfNormRect C) +
        p20InfNormRect D) + p20InfNormRect E := by
      gcongr
      exact p20InfNormRect_add_le _ _
    _ ≤ (((p20InfNormRect A + p20InfNormRect B) +
        p20InfNormRect C) + p20InfNormRect D) + p20InfNormRect E := by
      gcongr
      exact p20InfNormRect_add_le _ _
    _ = _ := by ring

private theorem p20UnitRoundoff_pos (precision : ℕ) :
    0 < p20UnitRoundoff precision := by
  simp only [p20UnitRoundoff]
  positivity

private theorem p20UnitRoundoff_le_half {precision : ℕ}
    (hprecision : 0 < precision) :
    p20UnitRoundoff precision ≤ (1 / 2 : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hprecision)
  rw [p20UnitRoundoff, pow_succ]
  have hk : (2 : ℝ)⁻¹ ^ k ≤ 1 := by
    exact pow_le_one₀ (by positivity) (by norm_num)
  norm_num at hk ⊢
  nlinarith

private theorem p20MaxFinite_pos {precision : ℕ} {maxExponent : ℤ}
    (hprecision : 0 < precision) :
    0 < p20MaxFinite precision maxExponent := by
  have hu := p20UnitRoundoff_le_half hprecision
  have he : 0 < (2 : ℝ) ^ maxExponent := by positivity
  rw [p20MaxFinite]
  have hf : 0 < 2 - 2 * p20UnitRoundoff precision := by
    nlinarith
  exact mul_pos he hf

private theorem p20UnderflowEnvelope_nonneg
    (precision : ℕ) (minExponent : ℤ) (hasSubnormals : Bool) :
    0 ≤ p20UnderflowEnvelope precision minExponent hasSubnormals := by
  simp only [p20UnderflowEnvelope]
  split <;> simp only [p20MinNormal, p20UnitRoundoff] <;> positivity

private theorem p20StaticScalingThreshold_pos {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) :
    0 < p20StaticScalingThreshold n run.model := by
  rw [p20StaticScalingThreshold, p20ScalingThreshold]
  apply lt_min
  · exact p20MaxFinite_pos run.model.inputFormat.precision_pos
  · apply Real.sqrt_pos.2
    apply div_pos
    · exact p20MaxFinite_pos run.model.accumulationFormat.precision_pos
    · exact_mod_cast run.dimension_pos.2.1

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
  have hmain : ∀ (run : P20StaticMultiwordRun m n q p),
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
    have hcomputed :
        run.computed = p20StaticExactRetainedWordProduct run +
          p20StaticAccumulationError run := by
      rw [p20StaticAccumulationError]
      abel
    have herror :
        run.computed - run.A * run.B =
          p20StaticAccumulationError run +
            (-p20StaticOmittedWordTail run) +
            (-(run.A * derivation.BError)) +
            (-(derivation.AError * run.B)) +
            derivation.AError * derivation.BError := by
      rw [hcomputed, derivation.retained_partition,
        derivation.A_decomposition, derivation.B_decomposition]
      simp only [Matrix.add_mul, Matrix.mul_add]
      abel
    rw [p20StaticMultiwordForwardError, herror]
    have hfive := p20InfNormRect_five_le
      (p20StaticAccumulationError run)
      (-p20StaticOmittedWordTail run)
      (-(run.A * derivation.BError))
      (-(derivation.AError * run.B))
      (derivation.AError * derivation.BError)
    rw [p20InfNormRect_neg, p20InfNormRect_neg,
      p20InfNormRect_neg] at hfive
    have hA_mul_BError :
        p20InfNormRect (run.A * derivation.BError) ≤
          p20StaticZeta run * p20InfNormRect run.A *
            p20InfNormRect run.B := by
      calc
        p20InfNormRect (run.A * derivation.BError) ≤
            p20InfNormRect run.A * p20InfNormRect derivation.BError :=
          p20InfNormRect_mul_le _ _
        _ ≤ p20InfNormRect run.A *
            (p20StaticZeta run * p20InfNormRect run.B) :=
          mul_le_mul_of_nonneg_left derivation.B_error_bound
            (p20InfNormRect_nonneg _)
        _ = _ := by ring
    have hAError_mul_B :
        p20InfNormRect (derivation.AError * run.B) ≤
          p20StaticZeta run * p20InfNormRect run.A *
            p20InfNormRect run.B := by
      calc
        p20InfNormRect (derivation.AError * run.B) ≤
            p20InfNormRect derivation.AError * p20InfNormRect run.B :=
          p20InfNormRect_mul_le _ _
        _ ≤ (p20StaticZeta run * p20InfNormRect run.A) *
            p20InfNormRect run.B :=
          mul_le_mul_of_nonneg_right derivation.A_error_bound
            (p20InfNormRect_nonneg _)
        _ = _ := by ring
    have hzetaA_nonneg :
        0 ≤ p20StaticZeta run * p20InfNormRect run.A :=
      (p20InfNormRect_nonneg derivation.AError).trans
        derivation.A_error_bound
    have hAError_mul_BError :
        p20InfNormRect (derivation.AError * derivation.BError) ≤
          p20StaticZeta run ^ 2 * p20InfNormRect run.A *
            p20InfNormRect run.B := by
      calc
        p20InfNormRect (derivation.AError * derivation.BError) ≤
            p20InfNormRect derivation.AError *
              p20InfNormRect derivation.BError :=
          p20InfNormRect_mul_le _ _
        _ ≤ (p20StaticZeta run * p20InfNormRect run.A) *
            (p20StaticZeta run * p20InfNormRect run.B) :=
          mul_le_mul derivation.A_error_bound derivation.B_error_bound
            (p20InfNormRect_nonneg _) hzetaA_nonneg
        _ = _ := by ring
    have haccumulation := derivation.accumulation_error_bound
    have homitted := derivation.omitted_tail_bound
    rw [p20NormwiseEnvelope] at haccumulation homitted
    have hraw :
        p20InfNormRect
            (p20StaticAccumulationError run +
              -p20StaticOmittedWordTail run +
              -(run.A * derivation.BError) +
              -(derivation.AError * run.B) +
              derivation.AError * derivation.BError) ≤
          (p20StaticRawAccumulationCoefficient n p
                derivation.underflowCount
                (p20StaticAccumUnitRoundoff run.model)
                (p20StaticScalingThreshold n run.model)
                (p20StaticAccumUnderflowEnvelope run.model) +
              p20StaticOmittedCoefficient p
                (p20StaticInputUnitRoundoff run.model) +
              2 * p20StaticZeta run) *
              p20InfNormRect run.A * p20InfNormRect run.B +
            p20StaticZeta run ^ 2 * p20InfNormRect run.A *
              p20InfNormRect run.B +
            |derivation.accumulationRemainder| +
            |derivation.omittedRemainder| := by
      calc
        _ ≤ p20InfNormRect (p20StaticAccumulationError run) +
              p20InfNormRect (p20StaticOmittedWordTail run) +
              p20InfNormRect (run.A * derivation.BError) +
              p20InfNormRect (derivation.AError * run.B) +
              p20InfNormRect (derivation.AError * derivation.BError) := hfive
        _ ≤ _ := by
          nlinarith [haccumulation, homitted, hA_mul_BError,
            hAError_mul_B, hAError_mul_BError]
    have hu_nonneg :
        0 ≤ p20StaticInputUnitRoundoff run.model :=
      (p20UnitRoundoff_pos _).le
    have hg_nonneg :
        0 ≤ p20StaticInputUnderflowEnvelope run.model := by
      exact p20UnderflowEnvelope_nonneg _ _ _
    have hG_nonneg :
        0 ≤ p20StaticAccumUnderflowEnvelope run.model := by
      exact p20UnderflowEnvelope_nonneg _ _ _
    have htheta_pos := p20StaticScalingThreshold_pos run
    have hzeta_le :
        p20StaticZeta run ≤
          p20StaticInputUnitRoundoff run.model ^ p +
            2 * (n : ℝ) *
              p20StaticInputUnitRoundoff run.model ^ (p - 1) *
              (p20StaticScalingThreshold n run.model)⁻¹ *
              p20StaticInputUnderflowEnvelope run.model := by
      rw [p20StaticZeta]
      apply max_le
      · have hsecond :
            0 ≤ 2 * (n : ℝ) *
              p20StaticInputUnitRoundoff run.model ^ (p - 1) *
              (p20StaticScalingThreshold n run.model)⁻¹ *
              p20StaticInputUnderflowEnvelope run.model := by positivity
        linarith
      · have hfirst :
            0 ≤ p20StaticInputUnitRoundoff run.model ^ p := by positivity
        linarith
    have hinputCoefficient :
        p20StaticOmittedCoefficient p
              (p20StaticInputUnitRoundoff run.model) +
            2 * p20StaticZeta run ≤
          p20MultiInputRoundingCoefficient p
              (p20StaticInputUnitRoundoff run.model) +
            p20MultiInputUnderflowCoefficient n p
              (p20StaticInputUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticInputUnderflowEnvelope run.model) := by
      unfold p20StaticOmittedCoefficient
        p20MultiInputRoundingCoefficient
        p20MultiInputUnderflowCoefficient
      nlinarith
    have hcountFactor_nonneg :
        0 ≤ 4 * (n : ℝ) *
          ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
          p20StaticAccumUnderflowEnvelope run.model := by positivity
    have hcount_scaled := mul_le_mul_of_nonneg_right
      derivation.underflow_count_bound hcountFactor_nonneg
    have haccumulationCoefficient :
        p20StaticRawAccumulationCoefficient n p
              derivation.underflowCount
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticAccumUnderflowEnvelope run.model) ≤
          p20MultiAccumRoundingCoefficient n p
              (p20StaticAccumUnitRoundoff run.model) +
            p20MultiAccumUnderflowCoefficient n p
              (p20StaticScalingThreshold n run.model)
              (p20StaticAccumUnderflowEnvelope run.model) := by
      unfold p20StaticRawAccumulationCoefficient
        p20MultiAccumUnderflowCoefficient
      nlinarith
    have hcoefficient :
        p20StaticRawAccumulationCoefficient n p
                derivation.underflowCount
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
      unfold p20MultiNarrowCoefficient p20MultiRangeFreeCoefficient
      linarith
    let quadraticRemainder : ℝ :=
      p20StaticZeta run ^ 2 * p20InfNormRect run.A *
        p20InfNormRect run.B
    refine ⟨|derivation.accumulationRemainder| +
        |derivation.omittedRemainder| + |quadraticRemainder|, ?_, ?_⟩
    · exact semantics.add_secondOrder
        (semantics.add_secondOrder
          (semantics.abs_secondOrder
            derivation.accumulation_remainder_second_order)
          (semantics.abs_secondOrder
            derivation.omitted_remainder_second_order))
        (semantics.abs_secondOrder (by
          simpa only [quadraticRemainder] using
            derivation.quadratic_second_order))
    · rw [p20NormwiseEnvelope]
      have hnormProduct_nonneg :
          0 ≤ p20InfNormRect run.A * p20InfNormRect run.B :=
        mul_nonneg (p20InfNormRect_nonneg _) (p20InfNormRect_nonneg _)
      have hcoefficient_scaled :
          (p20StaticRawAccumulationCoefficient n p
                  derivation.underflowCount
                  (p20StaticAccumUnitRoundoff run.model)
                  (p20StaticScalingThreshold n run.model)
                  (p20StaticAccumUnderflowEnvelope run.model) +
                p20StaticOmittedCoefficient p
                  (p20StaticInputUnitRoundoff run.model) +
                2 * p20StaticZeta run) *
                p20InfNormRect run.A * p20InfNormRect run.B ≤
            p20MultiNarrowCoefficient n p
                (p20StaticInputUnitRoundoff run.model)
                (p20StaticAccumUnitRoundoff run.model)
                (p20StaticScalingThreshold n run.model)
                (p20StaticInputUnderflowEnvelope run.model)
                (p20StaticAccumUnderflowEnvelope run.model) *
              p20InfNormRect run.A * p20InfNormRect run.B := by
        calc
          _ = (p20StaticRawAccumulationCoefficient n p
                    derivation.underflowCount
                    (p20StaticAccumUnitRoundoff run.model)
                    (p20StaticScalingThreshold n run.model)
                    (p20StaticAccumUnderflowEnvelope run.model) +
                  p20StaticOmittedCoefficient p
                    (p20StaticInputUnitRoundoff run.model) +
                  2 * p20StaticZeta run) *
                (p20InfNormRect run.A * p20InfNormRect run.B) := by ring
          _ ≤ p20MultiNarrowCoefficient n p
                  (p20StaticInputUnitRoundoff run.model)
                  (p20StaticAccumUnitRoundoff run.model)
                  (p20StaticScalingThreshold n run.model)
                  (p20StaticInputUnderflowEnvelope run.model)
                  (p20StaticAccumUnderflowEnvelope run.model) *
                (p20InfNormRect run.A * p20InfNormRect run.B) :=
            mul_le_mul_of_nonneg_right hcoefficient hnormProduct_nonneg
          _ = _ := by ring
      have hquadratic_nonneg : 0 ≤ quadraticRemainder := by
        dsimp only [quadraticRemainder]
        exact mul_nonneg
          (mul_nonneg (sq_nonneg _) (p20InfNormRect_nonneg _))
          (p20InfNormRect_nonneg _)
      have hremainder_nonneg :
          0 ≤ |derivation.accumulationRemainder| +
            |derivation.omittedRemainder| + |quadraticRemainder| := by
        positivity
      rw [abs_of_nonneg hremainder_nonneg,
        abs_of_nonneg hquadratic_nonneg]
      dsimp only [quadraticRemainder] at hraw ⊢
      nlinarith
  refine ⟨hmain, ?_, ?_⟩
  · intro run derivation
    have h := hmain run derivation
    unfold p20MultiNarrowCoefficient at h
    unfold p20NormwiseEnvelope at h ⊢
    convert h using 1 <;> ring
  · intro run
    constructor
    · rw [p20MultiInputRoundingCoefficient,
          p20SingleInputRoundingCoefficient]
      have hp : p - 1 + 1 = p := Nat.sub_add_cancel run.word_count_pos
      have hpow : p20StaticInputUnitRoundoff run.model ^ p =
          p20StaticInputUnitRoundoff run.model ^ (p - 1) *
            p20StaticInputUnitRoundoff run.model := by
        calc
          p20StaticInputUnitRoundoff run.model ^ p =
              p20StaticInputUnitRoundoff run.model ^ (p - 1 + 1) := by
            exact congrArg (fun k : ℕ =>
              p20StaticInputUnitRoundoff run.model ^ k) hp.symm
          _ = _ := by rw [pow_succ]
      rw [hpow]
      ring
    · rw [p20MultiInputUnderflowCoefficient,
          p20SingleInputUnderflowCoefficient]
      ring

end HighamBench
