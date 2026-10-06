import HighamBench.P20Definitions

namespace HighamBench

open scoped Matrix.Norms.Operator

private lemma p20InfNormRect_eq_norm {a b : ℕ}
    (A : P20Matrix a b) : p20InfNormRect A = ‖A‖ := by
  rw [p20InfNormRect, Matrix.linfty_opNorm_def]

private lemma p20InfNormRect_nonneg {a b : ℕ} (A : P20Matrix a b) :
    0 ≤ p20InfNormRect A := by
  rw [p20InfNormRect_eq_norm]
  exact norm_nonneg _

private lemma p20InfNormRect_add_le {a b : ℕ} (A B : P20Matrix a b) :
    p20InfNormRect (A + B) ≤ p20InfNormRect A + p20InfNormRect B := by
  simp only [p20InfNormRect_eq_norm]
  exact norm_add_le _ _

private lemma p20InfNormRect_sub_le {a b : ℕ} (A B : P20Matrix a b) :
    p20InfNormRect (A - B) ≤ p20InfNormRect A + p20InfNormRect B := by
  simp only [p20InfNormRect_eq_norm]
  exact norm_sub_le _ _

private lemma p20InfNormRect_mul_le {a b c : ℕ}
    (A : P20Matrix a b) (B : P20Matrix b c) :
    p20InfNormRect (A * B) ≤ p20InfNormRect A * p20InfNormRect B := by
  simp only [p20InfNormRect_eq_norm]
  exact Matrix.linfty_opNorm_mul _ _

private lemma p20InfNormRect_five_le {a b : ℕ}
    (A B C D E : P20Matrix a b) :
    p20InfNormRect (A - B - C - D + E) ≤
      p20InfNormRect A + p20InfNormRect B + p20InfNormRect C +
        p20InfNormRect D + p20InfNormRect E := by
  simp only [p20InfNormRect_eq_norm]
  calc
    ‖A - B - C - D + E‖ ≤ ‖A - B - C - D‖ + ‖E‖ := norm_add_le _ _
    _ ≤ (‖A - B - C‖ + ‖D‖) + ‖E‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ((‖A - B‖ + ‖C‖) + ‖D‖) + ‖E‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖) + ‖E‖ := by
      gcongr
      exact norm_sub_le _ _

private lemma p20Static_error_identity {m n q p : ℕ}
    (semantics : P20FirstOrderSemantics)
    (run : P20StaticMultiwordRun m n q p)
    (d : P20StaticSection4Derivation semantics run) :
    run.computed - run.A * run.B =
      p20StaticAccumulationError run - p20StaticOmittedWordTail run -
        d.AError * run.B - run.A * d.BError + d.AError * d.BError := by
  have hA : p20StaticAWordApproximation run = run.A - d.AError :=
    eq_sub_of_add_eq d.A_decomposition.symm
  have hB : p20StaticBWordApproximation run = run.B - d.BError :=
    eq_sub_of_add_eq d.B_decomposition.symm
  calc
    run.computed - run.A * run.B =
        (run.computed - p20StaticExactRetainedWordProduct run) +
          p20StaticExactRetainedWordProduct run - run.A * run.B := by abel
    _ = p20StaticAccumulationError run +
          p20StaticExactRetainedWordProduct run - run.A * run.B := by
      rfl
    _ = p20StaticAccumulationError run +
          ((run.A - d.AError) * (run.B - d.BError) -
            p20StaticOmittedWordTail run) - run.A * run.B := by
      rw [d.retained_partition, hA, hB]
    _ = p20StaticAccumulationError run - p20StaticOmittedWordTail run -
          d.AError * run.B - run.A * d.BError + d.AError * d.BError := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel

private lemma p20UnitRoundoff_nonneg (precision : ℕ) :
    0 ≤ p20UnitRoundoff precision := by
  unfold p20UnitRoundoff
  positivity

private lemma p20UnitRoundoff_le_one (precision : ℕ) :
    p20UnitRoundoff precision ≤ 1 := by
  unfold p20UnitRoundoff
  exact pow_le_one₀ (by norm_num) (by norm_num)

private lemma p20MaxFinite_nonneg (precision : ℕ) (maxExponent : ℤ) :
    0 ≤ p20MaxFinite precision maxExponent := by
  unfold p20MaxFinite
  have hu := p20UnitRoundoff_le_one precision
  have hpow : 0 ≤ (2 : ℝ) ^ maxExponent := by positivity
  exact mul_nonneg hpow (by linarith)

private lemma p20ScalingThreshold_nonneg (n precision accumulationPrecision : ℕ)
    (maxExponent accumulationMaxExponent : ℤ) :
    0 ≤ p20ScalingThreshold n
      (p20MaxFinite precision maxExponent)
      (p20MaxFinite accumulationPrecision accumulationMaxExponent) := by
  unfold p20ScalingThreshold
  exact le_min (p20MaxFinite_nonneg _ _)
    (Real.sqrt_nonneg _)

private lemma p20UnderflowEnvelope_nonneg (precision : ℕ)
    (minExponent : ℤ) (hasSubnormals : Bool) :
    0 ≤ p20UnderflowEnvelope precision minExponent hasSubnormals := by
  cases hasSubnormals <;>
    simp only [p20UnderflowEnvelope, p20MinNormal, p20UnitRoundoff] <;>
      positivity

private lemma p20StaticZeta_nonneg {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : 0 ≤ p20StaticZeta run := by
  unfold p20StaticZeta
  have hu : 0 ≤ p20StaticInputUnitRoundoff run.model := by
    unfold p20StaticInputUnitRoundoff
    exact p20UnitRoundoff_nonneg _
  exact (pow_nonneg hu p).trans (le_max_left _ _)

private lemma p20Static_input_coefficient_bound {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) :
    p20StaticOmittedCoefficient p
          (p20StaticInputUnitRoundoff run.model) +
        2 * p20StaticZeta run ≤
      p20MultiInputRoundingCoefficient p
          (p20StaticInputUnitRoundoff run.model) +
        p20MultiInputUnderflowCoefficient n p
          (p20StaticInputUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticInputUnderflowEnvelope run.model) := by
  let u := p20StaticInputUnitRoundoff run.model
  let theta := p20StaticScalingThreshold n run.model
  let gmin := p20StaticInputUnderflowEnvelope run.model
  have hu : 0 ≤ u := by
    dsimp [u, p20StaticInputUnitRoundoff]
    exact p20UnitRoundoff_nonneg _
  have htheta : 0 ≤ theta := by
    dsimp [theta, p20StaticScalingThreshold]
    exact p20ScalingThreshold_nonneg _ _ _ _ _
  have hgmin : 0 ≤ gmin := by
    dsimp [gmin, p20StaticInputUnderflowEnvelope]
    exact p20UnderflowEnvelope_nonneg _ _ _
  have ha : 0 ≤ u ^ p := pow_nonneg hu _
  have hb : 0 ≤
      2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin := by
    positivity
  have hzeta : p20StaticZeta run ≤
      u ^ p + 2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin := by
    change max (u ^ p)
      (2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin) ≤ _
    exact max_le (le_add_of_nonneg_right hb) (le_add_of_nonneg_left ha)
  calc
    p20StaticOmittedCoefficient p u + 2 * p20StaticZeta run ≤
        p20StaticOmittedCoefficient p u +
          2 * (u ^ p +
            2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin) := by
      gcongr
    _ = p20MultiInputRoundingCoefficient p u +
          p20MultiInputUnderflowCoefficient n p u theta gmin := by
      simp only [p20StaticOmittedCoefficient,
        p20MultiInputRoundingCoefficient,
        p20MultiInputUnderflowCoefficient]
      ring

private lemma p20Static_accumulation_coefficient_bound {m n q p : ℕ}
    (semantics : P20FirstOrderSemantics)
    (run : P20StaticMultiwordRun m n q p)
    (d : P20StaticSection4Derivation semantics run) :
    p20StaticRawAccumulationCoefficient n p d.underflowCount
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticAccumUnderflowEnvelope run.model) ≤
      p20StaticAccumulationCoefficient n p
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticAccumUnderflowEnvelope run.model) := by
  let theta := p20StaticScalingThreshold n run.model
  let Gmin := p20StaticAccumUnderflowEnvelope run.model
  have hGmin : 0 ≤ Gmin := by
    dsimp [Gmin, p20StaticAccumUnderflowEnvelope]
    exact p20UnderflowEnvelope_nonneg _ _ _
  have hfactor : 0 ≤
      4 * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin := by positivity
  have hcount :
      (d.underflowCount : ℝ) *
          (4 * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin) ≤
        ((n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2) *
          (4 * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin) :=
    mul_le_mul_of_nonneg_right d.underflow_count_bound hfactor
  have hunderflow :
      4 * (d.underflowCount : ℝ) * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin ≤
        p20MultiAccumUnderflowCoefficient n p theta Gmin := by
    calc
    4 * (d.underflowCount : ℝ) * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin =
        (d.underflowCount : ℝ) *
          (4 * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin) := by ring
    _ ≤ ((n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2) *
          (4 * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin) := hcount
    _ = p20MultiAccumUnderflowCoefficient n p theta Gmin := by
      simp only [p20MultiAccumUnderflowCoefficient]
      ring
  dsimp only [p20StaticRawAccumulationCoefficient,
    p20StaticAccumulationCoefficient]
  simpa only [theta, Gmin, add_comm] using
    add_le_add_left hunderflow
      (p20MultiAccumRoundingCoefficient n p
        (p20StaticAccumUnitRoundoff run.model))

private lemma p20Static_forward_error_bound {m n q p : ℕ}
    (semantics : P20FirstOrderSemantics)
    (run : P20StaticMultiwordRun m n q p)
    (d : P20StaticSection4Derivation semantics run) :
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
  let zeta := p20StaticZeta run
  let normA := p20InfNormRect run.A
  let normB := p20InfNormRect run.B
  have hzeta : 0 ≤ zeta := by
    exact p20StaticZeta_nonneg run
  have hnormA : 0 ≤ normA := p20InfNormRect_nonneg _
  have hnormB : 0 ≤ normB := p20InfNormRect_nonneg _
  have hAErrorB : p20InfNormRect (d.AError * run.B) ≤
      zeta * normA * normB := by
    calc
      p20InfNormRect (d.AError * run.B) ≤
          p20InfNormRect d.AError * normB :=
        p20InfNormRect_mul_le _ _
      _ ≤ (zeta * normA) * normB := by
        exact mul_le_mul_of_nonneg_right d.A_error_bound hnormB
  have hABError : p20InfNormRect (run.A * d.BError) ≤
      zeta * normA * normB := by
    calc
      p20InfNormRect (run.A * d.BError) ≤
          normA * p20InfNormRect d.BError :=
        p20InfNormRect_mul_le _ _
      _ ≤ normA * (zeta * normB) := by
        exact mul_le_mul_of_nonneg_left d.B_error_bound hnormA
      _ = zeta * normA * normB := by ring
  have hAErrorBError : p20InfNormRect (d.AError * d.BError) ≤
      zeta ^ 2 * normA * normB := by
    calc
      p20InfNormRect (d.AError * d.BError) ≤
          p20InfNormRect d.AError * p20InfNormRect d.BError :=
        p20InfNormRect_mul_le _ _
      _ ≤ (zeta * normA) * (zeta * normB) := by
        exact mul_le_mul d.A_error_bound d.B_error_bound
          (p20InfNormRect_nonneg _) (mul_nonneg hzeta hnormA)
      _ = zeta ^ 2 * normA * normB := by ring
  have hshape : p20StaticMultiwordForwardError run ≤
      p20InfNormRect (p20StaticAccumulationError run) +
        p20InfNormRect (p20StaticOmittedWordTail run) +
        p20InfNormRect (d.AError * run.B) +
        p20InfNormRect (run.A * d.BError) +
        p20InfNormRect (d.AError * d.BError) := by
    unfold p20StaticMultiwordForwardError
    rw [p20Static_error_identity semantics run d]
    exact p20InfNormRect_five_le _ _ _ _ _
  have hcoarse : p20StaticMultiwordForwardError run ≤
      p20NormwiseEnvelope
          (p20StaticRawAccumulationCoefficient n p d.underflowCount
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model)) run.A run.B +
        p20NormwiseEnvelope
          (p20StaticOmittedCoefficient p
            (p20StaticInputUnitRoundoff run.model)) run.A run.B +
        2 * zeta * normA * normB +
        zeta ^ 2 * normA * normB +
        |d.accumulationRemainder| + |d.omittedRemainder| := by
    dsimp only [normA, normB]
    linarith [d.accumulation_error_bound, d.omitted_tail_bound,
      hAErrorB, hABError, hAErrorBError]
  have hinput := p20Static_input_coefficient_bound run
  have haccum := p20Static_accumulation_coefficient_bound semantics run d
  have hcoefficient :
      p20StaticRawAccumulationCoefficient n p d.underflowCount
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model) +
          p20StaticOmittedCoefficient p
            (p20StaticInputUnitRoundoff run.model) +
          2 * zeta ≤
        p20MultiNarrowCoefficient n p
          (p20StaticInputUnitRoundoff run.model)
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticInputUnderflowEnvelope run.model)
          (p20StaticAccumUnderflowEnvelope run.model) := by
    calc
      _ = (p20StaticOmittedCoefficient p
              (p20StaticInputUnitRoundoff run.model) + 2 * zeta) +
            p20StaticRawAccumulationCoefficient n p d.underflowCount
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticAccumUnderflowEnvelope run.model) := by ring
      _ ≤ (p20MultiInputRoundingCoefficient p
              (p20StaticInputUnitRoundoff run.model) +
            p20MultiInputUnderflowCoefficient n p
              (p20StaticInputUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticInputUnderflowEnvelope run.model)) +
            p20StaticAccumulationCoefficient n p
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticAccumUnderflowEnvelope run.model) :=
        add_le_add hinput haccum
      _ = p20MultiNarrowCoefficient n p
          (p20StaticInputUnitRoundoff run.model)
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticInputUnderflowEnvelope run.model)
          (p20StaticAccumUnderflowEnvelope run.model) := by
        simp only [p20StaticAccumulationCoefficient,
          p20MultiNarrowCoefficient, p20MultiRangeFreeCoefficient]
        ring
  have hcoefficient_envelope :
      (p20StaticRawAccumulationCoefficient n p d.underflowCount
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model) +
          p20StaticOmittedCoefficient p
            (p20StaticInputUnitRoundoff run.model) + 2 * zeta) *
            normA * normB ≤
        p20MultiNarrowCoefficient n p
          (p20StaticInputUnitRoundoff run.model)
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticInputUnderflowEnvelope run.model)
          (p20StaticAccumUnderflowEnvelope run.model) * normA * normB := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoefficient hnormA) hnormB
  let quadratic := zeta ^ 2 * normA * normB
  have hquadratic_nonneg : 0 ≤ quadratic := by positivity
  refine ⟨|d.accumulationRemainder| + |d.omittedRemainder| + |quadratic|,
    ?_, ?_⟩
  · exact semantics.add_secondOrder
      (semantics.add_secondOrder
        (semantics.abs_secondOrder d.accumulation_remainder_second_order)
        (semantics.abs_secondOrder d.omitted_remainder_second_order))
      (semantics.abs_secondOrder (by
        simpa only [quadratic, zeta, normA, normB] using
          d.quadratic_second_order))
  · rw [abs_of_nonneg (by positivity :
        0 ≤ |d.accumulationRemainder| + |d.omittedRemainder| + |quadratic|)]
    rw [abs_of_nonneg hquadratic_nonneg]
    dsimp only [p20NormwiseEnvelope] at hcoarse ⊢
    dsimp only [quadratic]
    dsimp only [zeta, normA, normB] at hcoarse hcoefficient_envelope ⊢
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
  refine ⟨?_, ?_, ?_⟩
  · intro run d
    exact p20Static_forward_error_bound semantics run d
  · intro run d
    simpa only [p20MultiNarrowCoefficient, p20NormwiseEnvelope,
      add_mul] using p20Static_forward_error_bound semantics run d
  · intro run
    constructor
    · have hp : p - 1 + 1 = p := Nat.sub_add_cancel run.word_count_pos
      have hpow : p20StaticInputUnitRoundoff run.model ^ p =
          p20StaticInputUnitRoundoff run.model ^ (p - 1) *
            p20StaticInputUnitRoundoff run.model := by
        calc
          p20StaticInputUnitRoundoff run.model ^ p =
              p20StaticInputUnitRoundoff run.model ^ (p - 1 + 1) :=
            congrArg (fun k : ℕ =>
              p20StaticInputUnitRoundoff run.model ^ k) hp.symm
          _ = p20StaticInputUnitRoundoff run.model ^ (p - 1) *
              p20StaticInputUnitRoundoff run.model := by rw [pow_succ]
      simp only [p20MultiInputRoundingCoefficient,
        p20SingleInputRoundingCoefficient]
      rw [hpow]
      ring
    · simp only [p20MultiInputUnderflowCoefficient,
        p20SingleInputUnderflowCoefficient]
      ring

end HighamBench
