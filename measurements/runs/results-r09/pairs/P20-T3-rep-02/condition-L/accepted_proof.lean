import HighamBench.P20Definitions
import NumStability.Analysis.MatrixAlgebra

namespace HighamBench

lemma p20InfNormRect_eq_infNormRect {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    p20InfNormRect A = NumStability.infNormRect A := by
  rfl

lemma p20InfNormRect_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    0 ≤ p20InfNormRect A := by
  rw [p20InfNormRect_eq_infNormRect]
  exact NumStability.infNormRect_nonneg A

lemma p20RowSum_le_infNormRect {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : ∑ j : Fin n, |A i j| ≤ p20InfNormRect A := by
  rw [p20InfNormRect_eq_infNormRect]
  exact NumStability.row_sum_le_infNormRect A i

lemma p20InfNormRect_le_of_row_sum_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {c : ℝ}
    (hrows : ∀ i : Fin m, ∑ j : Fin n, |A i j| ≤ c) (hc : 0 ≤ c) :
    p20InfNormRect A ≤ c := by
  rw [p20InfNormRect_eq_infNormRect]
  exact NumStability.infNormRect_le_of_row_sum_le A hrows hc

lemma p20InfNormRect_add_le {m n : ℕ}
    (A B : P20Matrix m n) :
    p20InfNormRect (A + B) ≤ p20InfNormRect A + p20InfNormRect B := by
  apply p20InfNormRect_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |(A + B) i j|
          ≤ ∑ j : Fin n, (|A i j| + |B i j|) := by
              apply Finset.sum_le_sum
              intro j _
              simpa using abs_add_le (A i j) (B i j)
      _ = (∑ j : Fin n, |A i j|) + ∑ j : Fin n, |B i j| := by
              rw [Finset.sum_add_distrib]
      _ ≤ p20InfNormRect A + p20InfNormRect B :=
              add_le_add (p20RowSum_le_infNormRect A i)
                (p20RowSum_le_infNormRect B i)
  · exact add_nonneg (p20InfNormRect_nonneg A) (p20InfNormRect_nonneg B)

lemma p20InfNormRect_neg {m n : ℕ} (A : P20Matrix m n) :
    p20InfNormRect (-A) = p20InfNormRect A := by
  simp [p20InfNormRect]

lemma p20InfNormRect_sub_le {m n : ℕ}
    (A B : P20Matrix m n) :
    p20InfNormRect (A - B) ≤ p20InfNormRect A + p20InfNormRect B := by
  rw [sub_eq_add_neg]
  calc
    p20InfNormRect (A + -B)
        ≤ p20InfNormRect A + p20InfNormRect (-B) :=
          p20InfNormRect_add_le A (-B)
    _ = p20InfNormRect A + p20InfNormRect B := by
          rw [p20InfNormRect_neg]

lemma p20InfNormRect_mul_le {m n q : ℕ}
    (A : P20Matrix m n) (B : P20Matrix n q) :
    p20InfNormRect (A * B) ≤ p20InfNormRect A * p20InfNormRect B := by
  apply p20InfNormRect_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin q, |(A * B) i j|
          ≤ ∑ j : Fin q, ∑ k : Fin n, |A i k| * |B k j| := by
            apply Finset.sum_le_sum
            intro j _
            rw [Matrix.mul_apply]
            calc
              |∑ k : Fin n, A i k * B k j|
                  ≤ ∑ k : Fin n, |A i k * B k j| :=
                    Finset.abs_sum_le_sum_abs _ _
              _ = ∑ k : Fin n, |A i k| * |B k j| := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [abs_mul]
      _ = ∑ k : Fin n, |A i k| * ∑ j : Fin q, |B k j| := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
      _ ≤ ∑ k : Fin n, |A i k| * p20InfNormRect B := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left
              (p20RowSum_le_infNormRect B k) (abs_nonneg _)
      _ = (∑ k : Fin n, |A i k|) * p20InfNormRect B := by
            rw [Finset.sum_mul]
      _ ≤ p20InfNormRect A * p20InfNormRect B :=
            mul_le_mul_of_nonneg_right (p20RowSum_le_infNormRect A i)
              (p20InfNormRect_nonneg B)
  · exact mul_nonneg (p20InfNormRect_nonneg A) (p20InfNormRect_nonneg B)

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
  have forward_bound :
      ∀ (run : P20StaticMultiwordRun m n q p),
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
    let u := p20StaticInputUnitRoundoff run.model
    let U := p20StaticAccumUnitRoundoff run.model
    let theta := p20StaticScalingThreshold n run.model
    let gmin := p20StaticInputUnderflowEnvelope run.model
    let Gmin := p20StaticAccumUnderflowEnvelope run.model
    let zeta := p20StaticZeta run
    let anorm := p20InfNormRect run.A
    let bnorm := p20InfNormRect run.B
    let scale := anorm * bnorm

    have hu : 0 < u := by
      dsimp [u, p20StaticInputUnitRoundoff, p20UnitRoundoff]
      positivity
    have hU : 0 < U := by
      dsimp [U, p20StaticAccumUnitRoundoff, p20UnitRoundoff]
      positivity
    have hgmin : 0 ≤ gmin := by
      dsimp [gmin, p20StaticInputUnderflowEnvelope, p20UnderflowEnvelope,
        p20MinNormal, p20UnitRoundoff]
      split <;> positivity
    have hGmin : 0 ≤ Gmin := by
      dsimp [Gmin, p20StaticAccumUnderflowEnvelope, p20UnderflowEnvelope,
        p20MinNormal, p20UnitRoundoff]
      split <;> positivity
    have input_u_lt_one : u < 1 := by
      dsimp [u, p20StaticInputUnitRoundoff, p20UnitRoundoff]
      exact pow_lt_one₀ (by norm_num) (by norm_num)
        (Nat.ne_of_gt run.model.inputFormat.precision_pos)
    have accum_U_lt_one : U < 1 := by
      dsimp [U, p20StaticAccumUnitRoundoff, p20UnitRoundoff]
      exact pow_lt_one₀ (by norm_num) (by norm_num)
        (Nat.ne_of_gt run.model.accumulationFormat.precision_pos)
    have hinputMax :
        0 < p20MaxFinite run.model.inputFormat.precision
          run.model.inputFormat.maxExponent := by
      rw [p20MaxFinite]
      have hzpow : 0 < (2 : ℝ) ^ run.model.inputFormat.maxExponent := by
        positivity
      have hfactor : 0 < 2 - 2 * u := by linarith
      simpa [u, p20StaticInputUnitRoundoff] using mul_pos hzpow hfactor
    have haccumMax :
        0 < p20MaxFinite run.model.accumulationFormat.precision
          run.model.accumulationFormat.maxExponent := by
      rw [p20MaxFinite]
      have hzpow : 0 < (2 : ℝ) ^ run.model.accumulationFormat.maxExponent := by
        positivity
      have hfactor : 0 < 2 - 2 * U := by linarith
      simpa [U, p20StaticAccumUnitRoundoff] using mul_pos hzpow hfactor
    have hnreal : 0 < (n : ℝ) := by
      exact_mod_cast run.dimension_pos.2.1
    have htheta : 0 < theta := by
      dsimp [theta, p20StaticScalingThreshold, p20ScalingThreshold]
      rw [lt_min_iff]
      refine ⟨hinputMax, Real.sqrt_pos.2 ?_⟩
      exact div_pos haccumMax hnreal
    have hanorm : 0 ≤ anorm := p20InfNormRect_nonneg run.A
    have hbnorm : 0 ≤ bnorm := p20InfNormRect_nonneg run.B
    have hscale : 0 ≤ scale := mul_nonneg hanorm hbnorm
    have hzeta : 0 ≤ zeta := by
      dsimp [zeta, p20StaticZeta]
      exact le_trans (pow_nonneg (le_of_lt hu) p) (le_max_left _ _)

    have hAapprox :
        p20StaticAWordApproximation run = run.A - derivation.AError := by
      rw [derivation.A_decomposition]
      abel
    have hBapprox :
        p20StaticBWordApproximation run = run.B - derivation.BError := by
      rw [derivation.B_decomposition]
      abel
    have error_identity :
        run.computed - run.A * run.B =
          p20StaticAccumulationError run - p20StaticOmittedWordTail run -
            run.A * derivation.BError - derivation.AError * run.B +
              derivation.AError * derivation.BError := by
      unfold p20StaticAccumulationError
      rw [derivation.retained_partition, hAapprox, hBapprox]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply]
      simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring

    have herror_norm :
        p20StaticMultiwordForwardError run ≤
          p20InfNormRect (p20StaticAccumulationError run) +
            p20InfNormRect (p20StaticOmittedWordTail run) +
            zeta * scale + zeta * scale + zeta ^ 2 * scale := by
      rw [p20StaticMultiwordForwardError, error_identity]
      have h0 := p20InfNormRect_add_le
        (p20StaticAccumulationError run - p20StaticOmittedWordTail run -
          run.A * derivation.BError - derivation.AError * run.B)
        (derivation.AError * derivation.BError)
      have h1 := p20InfNormRect_sub_le
        (p20StaticAccumulationError run - p20StaticOmittedWordTail run -
          run.A * derivation.BError)
        (derivation.AError * run.B)
      have h2 := p20InfNormRect_sub_le
        (p20StaticAccumulationError run - p20StaticOmittedWordTail run)
        (run.A * derivation.BError)
      have h3 := p20InfNormRect_sub_le
        (p20StaticAccumulationError run)
        (p20StaticOmittedWordTail run)
      have hABerr :
          p20InfNormRect (run.A * derivation.BError) ≤ zeta * scale := by
        calc
          p20InfNormRect (run.A * derivation.BError)
              ≤ anorm * p20InfNormRect derivation.BError :=
                p20InfNormRect_mul_le run.A derivation.BError
          _ ≤ anorm * (zeta * bnorm) :=
                mul_le_mul_of_nonneg_left derivation.B_error_bound hanorm
          _ = zeta * scale := by
                dsimp [anorm, bnorm, scale, zeta]
                ring
      have hAerrB :
          p20InfNormRect (derivation.AError * run.B) ≤ zeta * scale := by
        calc
          p20InfNormRect (derivation.AError * run.B)
              ≤ p20InfNormRect derivation.AError * bnorm :=
                p20InfNormRect_mul_le derivation.AError run.B
          _ ≤ (zeta * anorm) * bnorm :=
                mul_le_mul_of_nonneg_right derivation.A_error_bound hbnorm
          _ = zeta * scale := by
                dsimp [anorm, bnorm, scale, zeta]
                ring
      have hAerrBerr :
          p20InfNormRect (derivation.AError * derivation.BError) ≤
            zeta ^ 2 * scale := by
        calc
          p20InfNormRect (derivation.AError * derivation.BError)
              ≤ p20InfNormRect derivation.AError *
                  p20InfNormRect derivation.BError :=
                p20InfNormRect_mul_le derivation.AError derivation.BError
          _ ≤ (zeta * anorm) * p20InfNormRect derivation.BError :=
                mul_le_mul_of_nonneg_right derivation.A_error_bound
                  (p20InfNormRect_nonneg derivation.BError)
          _ ≤ (zeta * anorm) * (zeta * bnorm) :=
                mul_le_mul_of_nonneg_left derivation.B_error_bound
                  (mul_nonneg hzeta hanorm)
          _ = zeta ^ 2 * scale := by
                dsimp [anorm, bnorm, scale, zeta]
                ring
      linarith

    have hrawAccum :
        p20StaticRawAccumulationCoefficient n p derivation.underflowCount
            U theta Gmin ≤
          p20StaticAccumulationCoefficient n p U theta Gmin := by
      have hfactor :
          0 ≤ 4 * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin := by
        positivity
      calc
        p20StaticRawAccumulationCoefficient n p derivation.underflowCount
            U theta Gmin =
            p20MultiAccumRoundingCoefficient n p U +
              (derivation.underflowCount : ℝ) *
                (4 * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin) := by
                  unfold p20StaticRawAccumulationCoefficient
                  ring
        _ ≤ p20MultiAccumRoundingCoefficient n p U +
              ((n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2) *
                (4 * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin) := by
                  exact add_le_add_right
                    (mul_le_mul_of_nonneg_right
                      derivation.underflow_count_bound hfactor) _
        _ = p20StaticAccumulationCoefficient n p U theta Gmin := by
                  unfold p20StaticAccumulationCoefficient
                    p20MultiAccumUnderflowCoefficient
                  ring

    have hsecondZeta :
        0 ≤ 2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin := by
      positivity
    have hzeta_upper :
        zeta ≤ u ^ p +
          2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin := by
      dsimp [zeta, p20StaticZeta, u, theta, gmin]
      apply max_le
      · exact le_add_of_nonneg_right hsecondZeta
      · exact le_add_of_nonneg_left (pow_nonneg (le_of_lt hu) p)
    have hinputCoefficient :
        p20StaticOmittedCoefficient p u + 2 * zeta ≤
          p20MultiInputRoundingCoefficient p u +
            p20MultiInputUnderflowCoefficient n p u theta gmin := by
      calc
        p20StaticOmittedCoefficient p u + 2 * zeta
            ≤ p20StaticOmittedCoefficient p u +
                2 * (u ^ p +
                  2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin) := by
                    gcongr
        _ = p20MultiInputRoundingCoefficient p u +
              p20MultiInputUnderflowCoefficient n p u theta gmin := by
                    unfold p20StaticOmittedCoefficient
                      p20MultiInputRoundingCoefficient
                      p20MultiInputUnderflowCoefficient
                    ring
    have htotalCoefficient :
        p20StaticRawAccumulationCoefficient n p derivation.underflowCount
              U theta Gmin +
            p20StaticOmittedCoefficient p u + 2 * zeta ≤
          p20MultiNarrowCoefficient n p u U theta gmin Gmin := by
      calc
        p20StaticRawAccumulationCoefficient n p derivation.underflowCount
              U theta Gmin +
            p20StaticOmittedCoefficient p u + 2 * zeta
            ≤ p20StaticAccumulationCoefficient n p U theta Gmin +
                (p20MultiInputRoundingCoefficient p u +
                  p20MultiInputUnderflowCoefficient n p u theta gmin) := by
                    linarith
        _ = p20MultiNarrowCoefficient n p u U theta gmin Gmin := by
              unfold p20StaticAccumulationCoefficient
                p20MultiNarrowCoefficient p20MultiRangeFreeCoefficient
              ring

    let quadratic := zeta ^ 2 * scale
    let remainder := |derivation.accumulationRemainder| +
      |derivation.omittedRemainder| + |quadratic|
    have hquadratic_second : semantics.secondOrder quadratic := by
      simpa [quadratic, zeta, scale, anorm, bnorm, mul_assoc] using
        derivation.quadratic_second_order
    have hremainder_second : semantics.secondOrder remainder := by
      dsimp [remainder]
      exact semantics.add_secondOrder
        (semantics.add_secondOrder
          (semantics.abs_secondOrder
            derivation.accumulation_remainder_second_order)
          (semantics.abs_secondOrder
            derivation.omitted_remainder_second_order))
        (semantics.abs_secondOrder hquadratic_second)
    refine ⟨remainder, hremainder_second, ?_⟩
    have hquadratic_nonneg : 0 ≤ quadratic := by
      dsimp [quadratic]
      exact mul_nonneg (sq_nonneg zeta) hscale
    have hmajor :
        p20StaticMultiwordForwardError run ≤
          p20MultiNarrowCoefficient n p u U theta gmin Gmin * scale +
            |derivation.accumulationRemainder| +
            |derivation.omittedRemainder| + quadratic := by
      have hacc : p20InfNormRect (p20StaticAccumulationError run) ≤
          p20StaticRawAccumulationCoefficient n p derivation.underflowCount
              U theta Gmin * scale +
            |derivation.accumulationRemainder| := by
        simpa [p20NormwiseEnvelope, U, theta, Gmin, scale, anorm, bnorm,
          mul_assoc] using
          derivation.accumulation_error_bound
      have homit : p20InfNormRect (p20StaticOmittedWordTail run) ≤
          p20StaticOmittedCoefficient p u * scale +
            |derivation.omittedRemainder| := by
        simpa [p20NormwiseEnvelope, u, scale, anorm, bnorm, mul_assoc] using
          derivation.omitted_tail_bound
      have hcoeffScale := mul_le_mul_of_nonneg_right htotalCoefficient hscale
      dsimp [quadratic]
      linarith
    change p20StaticMultiwordForwardError run ≤
      p20NormwiseEnvelope
          (p20MultiNarrowCoefficient n p u U theta gmin Gmin)
          run.A run.B + |remainder|
    rw [show |remainder| = remainder by
      apply abs_of_nonneg
      dsimp [remainder]
      positivity]
    dsimp [remainder]
    rw [abs_of_nonneg hquadratic_nonneg]
    simpa [p20NormwiseEnvelope, scale, anorm, bnorm, mul_assoc, add_assoc] using
      hmajor

  refine ⟨forward_bound, ?_, ?_⟩
  · intro run derivation
    convert forward_bound run derivation using 1 <;>
      unfold p20NormwiseEnvelope p20MultiNarrowCoefficient
        p20MultiRangeFreeCoefficient <;> ring
  · intro run
    constructor
    · unfold p20MultiInputRoundingCoefficient
        p20SingleInputRoundingCoefficient
      have hp : p = (p - 1) + 1 := by
        have hp_pos := run.word_count_pos
        omega
      have hpow :
          p20StaticInputUnitRoundoff run.model ^ p =
            p20StaticInputUnitRoundoff run.model ^ (p - 1) *
              p20StaticInputUnitRoundoff run.model := by
        calc
          p20StaticInputUnitRoundoff run.model ^ p =
              p20StaticInputUnitRoundoff run.model ^ ((p - 1) + 1) :=
            congrArg (fun k : ℕ => p20StaticInputUnitRoundoff run.model ^ k) hp
          _ = p20StaticInputUnitRoundoff run.model ^ (p - 1) *
                p20StaticInputUnitRoundoff run.model := by
            rw [pow_succ]
      rw [hpow]
      ring
    · unfold p20MultiInputUnderflowCoefficient
        p20SingleInputUnderflowCoefficient
      ring

end HighamBench
