import HighamBench.P20Definitions

namespace HighamBench

open scoped Matrix.Norms.Operator

private lemma p20InfNormRect_eq_norm {a b : ℕ}
    (A : P20Matrix a b) : p20InfNormRect A = ‖A‖ := by
  rw [p20InfNormRect, Matrix.linfty_opNorm_def]

private lemma p20InfNormRect_nonneg {a b : ℕ}
    (A : P20Matrix a b) : 0 ≤ p20InfNormRect A := by
  rw [p20InfNormRect_eq_norm]
  exact norm_nonneg A

private lemma p20InfNormRect_add {a b : ℕ}
    (A B : P20Matrix a b) :
    p20InfNormRect (A + B) ≤ p20InfNormRect A + p20InfNormRect B := by
  simpa only [p20InfNormRect_eq_norm] using norm_add_le A B

private lemma p20InfNormRect_sub {a b : ℕ}
    (A B : P20Matrix a b) :
    p20InfNormRect (A - B) ≤ p20InfNormRect A + p20InfNormRect B := by
  simpa only [p20InfNormRect_eq_norm] using norm_sub_le A B

private lemma p20InfNormRect_mul {a b c : ℕ}
    (A : P20Matrix a b) (B : P20Matrix b c) :
    p20InfNormRect (A * B) ≤ p20InfNormRect A * p20InfNormRect B := by
  simpa only [p20InfNormRect_eq_norm] using Matrix.linfty_opNorm_mul A B

private lemma p20UnitRoundoff_nonneg (precision : ℕ) :
    0 ≤ p20UnitRoundoff precision := by
  unfold p20UnitRoundoff
  positivity

private lemma p20UnitRoundoff_le_one (precision : ℕ) :
    p20UnitRoundoff precision ≤ 1 := by
  unfold p20UnitRoundoff
  exact pow_le_one₀ (by norm_num) (by norm_num)

private lemma p20UnderflowEnvelope_nonneg (precision : ℕ)
    (minExponent : ℤ) (hasSubnormals : Bool) :
    0 ≤ p20UnderflowEnvelope precision minExponent hasSubnormals := by
  unfold p20UnderflowEnvelope
  split <;> simp only [p20MinNormal, p20UnitRoundoff] <;> positivity

private lemma p20MaxFinite_nonneg (precision : ℕ) (maxExponent : ℤ) :
    0 ≤ p20MaxFinite precision maxExponent := by
  unfold p20MaxFinite
  have hu := p20UnitRoundoff_le_one precision
  have hfactor : 0 ≤ 2 - 2 * p20UnitRoundoff precision := by linarith
  exact mul_nonneg (by positivity) hfactor

private lemma p20StaticScalingThreshold_nonneg (n : ℕ)
    (model : P20StaticNearestModel1) :
    0 ≤ p20StaticScalingThreshold n model := by
  unfold p20StaticScalingThreshold p20ScalingThreshold
  exact le_min (p20MaxFinite_nonneg _ _) (Real.sqrt_nonneg _)

private lemma p20StaticZeta_nonneg {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : 0 ≤ p20StaticZeta run := by
  unfold p20StaticZeta
  apply le_max_of_le_left
  exact pow_nonneg (p20UnitRoundoff_nonneg _) _

private lemma p20Static_forward_error_bound
    {m n q p : ℕ} (semantics : P20FirstOrderSemantics)
    (run : P20StaticMultiwordRun m n q p)
    (derivation : P20StaticSection4Derivation semantics run) :
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
  have hAapprox :
      p20StaticAWordApproximation run = run.A - derivation.AError := by
    exact eq_sub_of_add_eq derivation.A_decomposition.symm
  have hBapprox :
      p20StaticBWordApproximation run = run.B - derivation.BError := by
    exact eq_sub_of_add_eq derivation.B_decomposition.symm
  have hcomputed :
      run.computed = p20StaticAccumulationError run +
        p20StaticExactRetainedWordProduct run := by
    unfold p20StaticAccumulationError
    abel
  have herr :
      run.computed - run.A * run.B =
        p20StaticAccumulationError run - p20StaticOmittedWordTail run -
          run.A * derivation.BError - derivation.AError * run.B +
            derivation.AError * derivation.BError := by
    rw [hcomputed, derivation.retained_partition, hAapprox, hBapprox]
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hnorm :
      p20StaticMultiwordForwardError run ≤
        p20InfNormRect (p20StaticAccumulationError run) +
          p20InfNormRect (p20StaticOmittedWordTail run) +
          p20InfNormRect (run.A * derivation.BError) +
          p20InfNormRect (derivation.AError * run.B) +
          p20InfNormRect (derivation.AError * derivation.BError) := by
    unfold p20StaticMultiwordForwardError
    rw [herr]
    calc
      p20InfNormRect
          (((p20StaticAccumulationError run - p20StaticOmittedWordTail run) -
            run.A * derivation.BError) - derivation.AError * run.B +
              derivation.AError * derivation.BError) ≤
          p20InfNormRect
              (((p20StaticAccumulationError run - p20StaticOmittedWordTail run) -
                run.A * derivation.BError) - derivation.AError * run.B) +
            p20InfNormRect (derivation.AError * derivation.BError) :=
        p20InfNormRect_add _ _
      _ ≤
          (p20InfNormRect
              ((p20StaticAccumulationError run - p20StaticOmittedWordTail run) -
                run.A * derivation.BError) +
            p20InfNormRect (derivation.AError * run.B)) +
            p20InfNormRect (derivation.AError * derivation.BError) := by
        gcongr
        exact p20InfNormRect_sub _ _
      _ ≤
          ((p20InfNormRect
              (p20StaticAccumulationError run - p20StaticOmittedWordTail run) +
            p20InfNormRect (run.A * derivation.BError)) +
            p20InfNormRect (derivation.AError * run.B)) +
            p20InfNormRect (derivation.AError * derivation.BError) := by
        gcongr
        exact p20InfNormRect_sub _ _
      _ ≤
          (((p20InfNormRect (p20StaticAccumulationError run) +
            p20InfNormRect (p20StaticOmittedWordTail run)) +
            p20InfNormRect (run.A * derivation.BError)) +
            p20InfNormRect (derivation.AError * run.B)) +
            p20InfNormRect (derivation.AError * derivation.BError) := by
        gcongr
        exact p20InfNormRect_sub _ _
      _ = _ := by ring
  have hABError :
      p20InfNormRect (run.A * derivation.BError) ≤
        p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B := by
    calc
      p20InfNormRect (run.A * derivation.BError) ≤
          p20InfNormRect run.A * p20InfNormRect derivation.BError :=
        p20InfNormRect_mul _ _
      _ ≤ p20InfNormRect run.A *
          (p20StaticZeta run * p20InfNormRect run.B) := by
        exact mul_le_mul_of_nonneg_left derivation.B_error_bound
          (p20InfNormRect_nonneg _)
      _ = _ := by ring
  have hAErrorB :
      p20InfNormRect (derivation.AError * run.B) ≤
        p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B := by
    calc
      p20InfNormRect (derivation.AError * run.B) ≤
          p20InfNormRect derivation.AError * p20InfNormRect run.B :=
        p20InfNormRect_mul _ _
      _ ≤ (p20StaticZeta run * p20InfNormRect run.A) *
          p20InfNormRect run.B := by
        exact mul_le_mul_of_nonneg_right derivation.A_error_bound
          (p20InfNormRect_nonneg _)
  have hAErrorBError :
      p20InfNormRect (derivation.AError * derivation.BError) ≤
        p20StaticZeta run ^ 2 * p20InfNormRect run.A *
          p20InfNormRect run.B := by
    calc
      p20InfNormRect (derivation.AError * derivation.BError) ≤
          p20InfNormRect derivation.AError *
            p20InfNormRect derivation.BError := p20InfNormRect_mul _ _
      _ ≤ (p20StaticZeta run * p20InfNormRect run.A) *
          (p20StaticZeta run * p20InfNormRect run.B) := by
        exact mul_le_mul derivation.A_error_bound derivation.B_error_bound
          (p20InfNormRect_nonneg _) (mul_nonneg (p20StaticZeta_nonneg _)
            (p20InfNormRect_nonneg _))
      _ = _ := by ring
  have hu : 0 ≤ p20StaticInputUnitRoundoff run.model := by
    exact p20UnitRoundoff_nonneg _
  have htheta : 0 ≤ p20StaticScalingThreshold n run.model :=
    p20StaticScalingThreshold_nonneg _ _
  have hgmin : 0 ≤ p20StaticInputUnderflowEnvelope run.model := by
    exact p20UnderflowEnvelope_nonneg _ _ _
  have hGmin : 0 ≤ p20StaticAccumUnderflowEnvelope run.model := by
    exact p20UnderflowEnvelope_nonneg _ _ _
  have hraw :
      p20StaticRawAccumulationCoefficient n p derivation.underflowCount
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticAccumUnderflowEnvelope run.model) ≤
        p20StaticAccumulationCoefficient n p
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticAccumUnderflowEnvelope run.model) := by
    unfold p20StaticRawAccumulationCoefficient
      p20StaticAccumulationCoefficient p20MultiAccumUnderflowCoefficient
    apply add_le_add_right
    calc
      4 * (derivation.underflowCount : ℝ) * (n : ℝ) *
          ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
            p20StaticAccumUnderflowEnvelope run.model ≤
        4 * ((n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2) *
          (n : ℝ) * ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
            p20StaticAccumUnderflowEnvelope run.model := by
        gcongr
        exact derivation.underflow_count_bound
      _ = 2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 *
          ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
            p20StaticAccumUnderflowEnvelope run.model := by ring
  have hzeta :
      p20StaticZeta run ≤
        p20StaticInputUnitRoundoff run.model ^ p +
          2 * (n : ℝ) *
            p20StaticInputUnitRoundoff run.model ^ (p - 1) *
            (p20StaticScalingThreshold n run.model)⁻¹ *
            p20StaticInputUnderflowEnvelope run.model := by
    unfold p20StaticZeta
    apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · exact le_add_of_nonneg_left (by positivity)
  have hcoefficient :
      p20StaticRawAccumulationCoefficient n p derivation.underflowCount
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticAccumUnderflowEnvelope run.model) +
        p20StaticOmittedCoefficient p
          (p20StaticInputUnitRoundoff run.model) +
        p20StaticZeta run + p20StaticZeta run ≤
      p20MultiNarrowCoefficient n p
          (p20StaticInputUnitRoundoff run.model)
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticInputUnderflowEnvelope run.model)
          (p20StaticAccumUnderflowEnvelope run.model) := by
    calc
      p20StaticRawAccumulationCoefficient n p derivation.underflowCount
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model) +
          p20StaticOmittedCoefficient p
            (p20StaticInputUnitRoundoff run.model) +
          p20StaticZeta run + p20StaticZeta run ≤
        p20StaticAccumulationCoefficient n p
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model) +
          p20StaticOmittedCoefficient p
            (p20StaticInputUnitRoundoff run.model) +
          (p20StaticInputUnitRoundoff run.model ^ p +
            2 * (n : ℝ) *
              p20StaticInputUnitRoundoff run.model ^ (p - 1) *
              (p20StaticScalingThreshold n run.model)⁻¹ *
              p20StaticInputUnderflowEnvelope run.model) +
          (p20StaticInputUnitRoundoff run.model ^ p +
            2 * (n : ℝ) *
              p20StaticInputUnitRoundoff run.model ^ (p - 1) *
              (p20StaticScalingThreshold n run.model)⁻¹ *
              p20StaticInputUnderflowEnvelope run.model) := by
        linarith
      _ = _ := by
        unfold p20StaticAccumulationCoefficient p20StaticOmittedCoefficient
          p20MultiNarrowCoefficient p20MultiRangeFreeCoefficient
          p20MultiInputRoundingCoefficient p20MultiAccumRoundingCoefficient
          p20MultiInputUnderflowCoefficient
          p20MultiAccumUnderflowCoefficient
        ring
  have hlinear :
      p20NormwiseEnvelope
          (p20StaticRawAccumulationCoefficient n p derivation.underflowCount
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model)) run.A run.B +
        p20NormwiseEnvelope
          (p20StaticOmittedCoefficient p
            (p20StaticInputUnitRoundoff run.model)) run.A run.B +
        p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B +
        p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B ≤
      p20NormwiseEnvelope
        (p20MultiNarrowCoefficient n p
          (p20StaticInputUnitRoundoff run.model)
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticInputUnderflowEnvelope run.model)
          (p20StaticAccumUnderflowEnvelope run.model)) run.A run.B := by
    unfold p20NormwiseEnvelope
    calc
      _ =
          (p20StaticRawAccumulationCoefficient n p derivation.underflowCount
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticAccumUnderflowEnvelope run.model) +
            p20StaticOmittedCoefficient p
              (p20StaticInputUnitRoundoff run.model) +
            p20StaticZeta run + p20StaticZeta run) *
            (p20InfNormRect run.A * p20InfNormRect run.B) := by ring
      _ ≤
          p20MultiNarrowCoefficient n p
              (p20StaticInputUnitRoundoff run.model)
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticInputUnderflowEnvelope run.model)
              (p20StaticAccumUnderflowEnvelope run.model) *
            (p20InfNormRect run.A * p20InfNormRect run.B) := by
        exact mul_le_mul_of_nonneg_right hcoefficient
          (mul_nonneg (p20InfNormRect_nonneg _) (p20InfNormRect_nonneg _))
      _ = _ := by ring
  have hrough :
      p20StaticMultiwordForwardError run ≤
        p20NormwiseEnvelope
            (p20StaticRawAccumulationCoefficient n p derivation.underflowCount
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticAccumUnderflowEnvelope run.model)) run.A run.B +
          |derivation.accumulationRemainder| +
        p20NormwiseEnvelope
            (p20StaticOmittedCoefficient p
              (p20StaticInputUnitRoundoff run.model)) run.A run.B +
          |derivation.omittedRemainder| +
        p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B +
        p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B +
        p20StaticZeta run ^ 2 * p20InfNormRect run.A *
          p20InfNormRect run.B := by
    linarith [derivation.accumulation_error_bound,
      derivation.omitted_tail_bound]
  let remainder : ℝ :=
    |derivation.accumulationRemainder| + |derivation.omittedRemainder| +
      |p20StaticZeta run ^ 2 * p20InfNormRect run.A *
        p20InfNormRect run.B|
  refine ⟨remainder, ?_, ?_⟩
  · dsimp [remainder]
    exact semantics.add_secondOrder
      (semantics.add_secondOrder
        (semantics.abs_secondOrder
          derivation.accumulation_remainder_second_order)
        (semantics.abs_secondOrder derivation.omitted_remainder_second_order))
      (semantics.abs_secondOrder derivation.quadratic_second_order)
  · have hquadratic :
        p20StaticZeta run ^ 2 * p20InfNormRect run.A *
            p20InfNormRect run.B ≤
          |p20StaticZeta run ^ 2 * p20InfNormRect run.A *
            p20InfNormRect run.B| := le_abs_self _
    have hremainder_nonneg : 0 ≤ remainder := by
      dsimp [remainder]
      positivity
    rw [abs_of_nonneg hremainder_nonneg]
    dsimp [remainder]
    linarith

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
  constructor
  · intro run derivation
    exact p20Static_forward_error_bound semantics run derivation
  constructor
  · intro run derivation
    have h := p20Static_forward_error_bound semantics run derivation
    have henvelope :
        p20NormwiseEnvelope
            (p20MultiNarrowCoefficient n p
              (p20StaticInputUnitRoundoff run.model)
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticInputUnderflowEnvelope run.model)
              (p20StaticAccumUnderflowEnvelope run.model)) run.A run.B =
          p20NormwiseEnvelope
              (p20MultiRangeFreeCoefficient n p
                (p20StaticInputUnitRoundoff run.model)
                (p20StaticAccumUnitRoundoff run.model)) run.A run.B +
            p20NormwiseEnvelope
              (p20MultiInputUnderflowCoefficient n p
                (p20StaticInputUnitRoundoff run.model)
                (p20StaticScalingThreshold n run.model)
                (p20StaticInputUnderflowEnvelope run.model)) run.A run.B +
            p20NormwiseEnvelope
              (p20MultiAccumUnderflowCoefficient n p
                (p20StaticScalingThreshold n run.model)
                (p20StaticAccumUnderflowEnvelope run.model)) run.A run.B := by
      unfold p20MultiNarrowCoefficient p20NormwiseEnvelope
      ring
    rw [henvelope] at h
    exact h
  · intro run
    constructor
    · have hp : 1 ≤ p := run.word_count_pos
      have hpow :
          p20StaticInputUnitRoundoff run.model ^ p =
            p20StaticInputUnitRoundoff run.model ^ (p - 1) *
              p20StaticInputUnitRoundoff run.model := by
        calc
          p20StaticInputUnitRoundoff run.model ^ p =
              p20StaticInputUnitRoundoff run.model ^ ((p - 1) + 1) := by
                rw [Nat.sub_add_cancel hp]
          _ = p20StaticInputUnitRoundoff run.model ^ (p - 1) *
              p20StaticInputUnitRoundoff run.model := by rw [pow_succ]
      unfold p20MultiInputRoundingCoefficient
        p20SingleInputRoundingCoefficient
      rw [hpow]
      ring
    · unfold p20MultiInputUnderflowCoefficient
        p20SingleInputUnderflowCoefficient
      ring

end HighamBench
