import HighamBench.P20Definitions

namespace HighamBench

lemma p20InfNormRect_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    0 ≤ p20InfNormRect A := by
  unfold p20InfNormRect
  exact NNReal.coe_nonneg _

lemma p20RowSum_le_infNormRect {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    (∑ j : Fin n, |A i j|) ≤ p20InfNormRect A := by
  unfold p20InfNormRect
  let f : Fin m → NNReal := fun i => ∑ j : Fin n, ‖A i j‖₊
  have hnn : f i ≤ Finset.univ.sup f :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin m)))
      (f := f) (Finset.mem_univ i)
  have h : (f i : ℝ) ≤ ((Finset.univ.sup f : NNReal) : ℝ) := by
    exact_mod_cast hnn
  simpa [f, Real.norm_eq_abs, NNReal.coe_sum] using h

lemma p20InfNormRect_le_of_row_sum_le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {c : ℝ}
    (hrows : ∀ i : Fin m, (∑ j : Fin n, |A i j|) ≤ c)
    (hc : 0 ≤ c) :
    p20InfNormRect A ≤ c := by
  unfold p20InfNormRect
  let f : Fin m → NNReal := fun i => ∑ j : Fin n, ‖A i j‖₊
  have hrows_nn : ∀ i, f i ≤ Real.toNNReal c := by
    intro i
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal c hc]
    simpa [f, Real.norm_eq_abs, NNReal.coe_sum] using hrows i
  have hsup : Finset.univ.sup f ≤ Real.toNNReal c :=
    Finset.sup_le (fun i _ => hrows_nn i)
  have hreal : ((Finset.univ.sup f : NNReal) : ℝ) ≤ c := by
    rw [← Real.coe_toNNReal c hc]
    exact_mod_cast hsup
  simpa [f] using hreal

lemma p20InfNormRect_add_le {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) :
    p20InfNormRect (A + B) ≤ p20InfNormRect A + p20InfNormRect B := by
  apply p20InfNormRect_le_of_row_sum_le
  · intro i
    calc
      (∑ j : Fin n, |(A + B) i j|)
          ≤ ∑ j : Fin n, (|A i j| + |B i j|) := by
              apply Finset.sum_le_sum
              intro j _
              simpa using abs_add_le (A i j) (B i j)
      _ = (∑ j : Fin n, |A i j|) + ∑ j : Fin n, |B i j| :=
        Finset.sum_add_distrib
      _ ≤ p20InfNormRect A + p20InfNormRect B :=
        add_le_add (p20RowSum_le_infNormRect A i)
          (p20RowSum_le_infNormRect B i)
  · exact add_nonneg (p20InfNormRect_nonneg A) (p20InfNormRect_nonneg B)

lemma p20InfNormRect_sub_le {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) :
    p20InfNormRect (A - B) ≤ p20InfNormRect A + p20InfNormRect B := by
  apply p20InfNormRect_le_of_row_sum_le
  · intro i
    calc
      (∑ j : Fin n, |(A - B) i j|)
          ≤ ∑ j : Fin n, (|A i j| + |B i j|) := by
              apply Finset.sum_le_sum
              intro j _
              simpa using abs_sub (A i j) (B i j)
      _ = (∑ j : Fin n, |A i j|) + ∑ j : Fin n, |B i j| :=
        Finset.sum_add_distrib
      _ ≤ p20InfNormRect A + p20InfNormRect B :=
        add_le_add (p20RowSum_le_infNormRect A i)
          (p20RowSum_le_infNormRect B i)
  · exact add_nonneg (p20InfNormRect_nonneg A) (p20InfNormRect_nonneg B)

lemma p20InfNormRect_mul_le {m n q : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin q) ℝ) :
    p20InfNormRect (A * B) ≤ p20InfNormRect A * p20InfNormRect B := by
  apply p20InfNormRect_le_of_row_sum_le
  · intro i
    calc
      (∑ j : Fin q, |(A * B) i j|)
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
                  exact abs_mul (A i k) (B k j)
      _ = ∑ k : Fin n, |A i k| * (∑ j : Fin q, |B k j|) := by
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
      _ ≤ p20InfNormRect A * p20InfNormRect B := by
            exact mul_le_mul_of_nonneg_right
              (p20RowSum_le_infNormRect A i) (p20InfNormRect_nonneg B)
  · exact mul_nonneg (p20InfNormRect_nonneg A) (p20InfNormRect_nonneg B)

lemma p20UnitRoundoff_nonneg (precision : ℕ) :
    0 ≤ p20UnitRoundoff precision := by
  unfold p20UnitRoundoff
  positivity

lemma p20UnderflowEnvelope_nonneg (precision : ℕ) (minExponent : ℤ)
    (hasSubnormals : Bool) :
    0 ≤ p20UnderflowEnvelope precision minExponent hasSubnormals := by
  cases hasSubnormals <;>
    simp [p20UnderflowEnvelope, p20MinNormal, p20UnitRoundoff] <;>
    positivity

lemma p20MaxFinite_nonneg (precision : ℕ) (maxExponent : ℤ) :
    0 ≤ p20MaxFinite precision maxExponent := by
  have hu : p20UnitRoundoff precision ≤ 1 := by
    unfold p20UnitRoundoff
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hfactor : 0 ≤ 2 - 2 * p20UnitRoundoff precision := by
    linarith
  unfold p20MaxFinite
  exact mul_nonneg (by positivity) hfactor

lemma p20StaticScalingThreshold_nonneg (n : ℕ)
    (model : P20StaticNearestModel1) :
    0 ≤ p20StaticScalingThreshold n model := by
  unfold p20StaticScalingThreshold p20ScalingThreshold
  exact le_min
    (p20MaxFinite_nonneg _ _)
    (Real.sqrt_nonneg _)

lemma p20StaticInputUnderflowEnvelope_nonneg
    (model : P20StaticNearestModel1) :
    0 ≤ p20StaticInputUnderflowEnvelope model := by
  exact p20UnderflowEnvelope_nonneg _ _ _

lemma p20StaticAccumUnderflowEnvelope_nonneg
    (model : P20StaticNearestModel1) :
    0 ≤ p20StaticAccumUnderflowEnvelope model := by
  exact p20UnderflowEnvelope_nonneg _ _ _

lemma p20StaticForwardError_identity
    {m n q p : ℕ} {semantics : P20FirstOrderSemantics}
    (run : P20StaticMultiwordRun m n q p)
    (h : P20StaticSection4Derivation semantics run) :
    run.computed - run.A * run.B =
      p20StaticAccumulationError run - p20StaticOmittedWordTail run -
        run.A * h.BError - h.AError * run.B + h.AError * h.BError := by
  ext i j
  simp only [p20StaticAccumulationError, h.retained_partition,
    h.A_decomposition, h.B_decomposition, Matrix.sub_apply,
    Matrix.add_apply, Matrix.mul_apply]
  simp only [Finset.sum_add_distrib, mul_add, add_mul]
  ring

lemma p20StaticForwardError_norm_bound
    {m n q p : ℕ} {semantics : P20FirstOrderSemantics}
    (run : P20StaticMultiwordRun m n q p)
    (h : P20StaticSection4Derivation semantics run) :
    p20StaticMultiwordForwardError run ≤
      p20InfNormRect (p20StaticAccumulationError run) +
      p20InfNormRect (p20StaticOmittedWordTail run) +
      p20InfNormRect run.A * p20InfNormRect h.BError +
      p20InfNormRect h.AError * p20InfNormRect run.B +
      p20InfNormRect h.AError * p20InfNormRect h.BError := by
  unfold p20StaticMultiwordForwardError
  rw [p20StaticForwardError_identity run h]
  calc
    p20InfNormRect
        (p20StaticAccumulationError run - p20StaticOmittedWordTail run -
          run.A * h.BError - h.AError * run.B + h.AError * h.BError)
        ≤ p20InfNormRect
            (p20StaticAccumulationError run - p20StaticOmittedWordTail run -
              run.A * h.BError - h.AError * run.B) +
            p20InfNormRect (h.AError * h.BError) :=
          p20InfNormRect_add_le _ _
    _ ≤ (p20InfNormRect
            (p20StaticAccumulationError run - p20StaticOmittedWordTail run -
              run.A * h.BError) + p20InfNormRect (h.AError * run.B)) +
            p20InfNormRect (h.AError * h.BError) := by
          gcongr
          exact p20InfNormRect_sub_le _ _
    _ ≤ ((p20InfNormRect
            (p20StaticAccumulationError run - p20StaticOmittedWordTail run) +
              p20InfNormRect (run.A * h.BError)) +
            p20InfNormRect (h.AError * run.B)) +
            p20InfNormRect (h.AError * h.BError) := by
          gcongr
          exact p20InfNormRect_sub_le _ _
    _ ≤ (((p20InfNormRect (p20StaticAccumulationError run) +
              p20InfNormRect (p20StaticOmittedWordTail run)) +
              p20InfNormRect (run.A * h.BError)) +
            p20InfNormRect (h.AError * run.B)) +
            p20InfNormRect (h.AError * h.BError) := by
          gcongr
          exact p20InfNormRect_sub_le _ _
    _ ≤ p20InfNormRect (p20StaticAccumulationError run) +
          p20InfNormRect (p20StaticOmittedWordTail run) +
          p20InfNormRect run.A * p20InfNormRect h.BError +
          p20InfNormRect h.AError * p20InfNormRect run.B +
          p20InfNormRect h.AError * p20InfNormRect h.BError := by
          have hAB := p20InfNormRect_mul_le run.A h.BError
          have hEB := p20InfNormRect_mul_le h.AError run.B
          have hEE := p20InfNormRect_mul_le h.AError h.BError
          linarith

lemma p20StaticZeta_nonneg {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) :
    0 ≤ p20StaticZeta run := by
  unfold p20StaticZeta
  exact le_trans
    (pow_nonneg (p20UnitRoundoff_nonneg _) _)
    (le_max_left _ _)

lemma p20StaticForwardError_derivation_bound
    {m n q p : ℕ} {semantics : P20FirstOrderSemantics}
    (run : P20StaticMultiwordRun m n q p)
    (h : P20StaticSection4Derivation semantics run) :
    p20StaticMultiwordForwardError run ≤
      (p20NormwiseEnvelope
          (p20StaticRawAccumulationCoefficient n p h.underflowCount
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model)) run.A run.B +
        |h.accumulationRemainder|) +
      (p20NormwiseEnvelope
          (p20StaticOmittedCoefficient p
            (p20StaticInputUnitRoundoff run.model)) run.A run.B +
        |h.omittedRemainder|) +
      p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B +
      p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B +
      p20StaticZeta run ^ 2 * p20InfNormRect run.A *
        p20InfNormRect run.B := by
  have hz := p20StaticZeta_nonneg run
  have hA := p20InfNormRect_nonneg run.A
  have hB := p20InfNormRect_nonneg run.B
  have hAE := p20InfNormRect_nonneg h.AError
  have hBE := p20InfNormRect_nonneg h.BError
  have hAB :
      p20InfNormRect run.A * p20InfNormRect h.BError ≤
        p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B := by
    calc
      p20InfNormRect run.A * p20InfNormRect h.BError
          ≤ p20InfNormRect run.A *
              (p20StaticZeta run * p20InfNormRect run.B) :=
            mul_le_mul_of_nonneg_left h.B_error_bound hA
      _ = p20StaticZeta run * p20InfNormRect run.A *
            p20InfNormRect run.B := by ring
  have hEA :
      p20InfNormRect h.AError * p20InfNormRect run.B ≤
        p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B := by
    calc
      p20InfNormRect h.AError * p20InfNormRect run.B
          ≤ (p20StaticZeta run * p20InfNormRect run.A) *
              p20InfNormRect run.B :=
            mul_le_mul_of_nonneg_right h.A_error_bound hB
      _ = p20StaticZeta run * p20InfNormRect run.A *
            p20InfNormRect run.B := by ring
  have hEE :
      p20InfNormRect h.AError * p20InfNormRect h.BError ≤
        p20StaticZeta run ^ 2 * p20InfNormRect run.A *
          p20InfNormRect run.B := by
    calc
      p20InfNormRect h.AError * p20InfNormRect h.BError
          ≤ (p20StaticZeta run * p20InfNormRect run.A) *
              p20InfNormRect h.BError :=
            mul_le_mul_of_nonneg_right h.A_error_bound hBE
      _ ≤ (p20StaticZeta run * p20InfNormRect run.A) *
              (p20StaticZeta run * p20InfNormRect run.B) :=
            mul_le_mul_of_nonneg_left h.B_error_bound (mul_nonneg hz hA)
      _ = p20StaticZeta run ^ 2 * p20InfNormRect run.A *
            p20InfNormRect run.B := by ring
  linarith [p20StaticForwardError_norm_bound run h,
    h.accumulation_error_bound, h.omitted_tail_bound]

lemma p20StaticRawAccumulationCoefficient_le
    {m n q p : ℕ} {semantics : P20FirstOrderSemantics}
    (run : P20StaticMultiwordRun m n q p)
    (h : P20StaticSection4Derivation semantics run) :
    p20StaticRawAccumulationCoefficient n p h.underflowCount
        (p20StaticAccumUnitRoundoff run.model)
        (p20StaticScalingThreshold n run.model)
        (p20StaticAccumUnderflowEnvelope run.model) ≤
      p20StaticAccumulationCoefficient n p
        (p20StaticAccumUnitRoundoff run.model)
        (p20StaticScalingThreshold n run.model)
        (p20StaticAccumUnderflowEnvelope run.model) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg' n
  have hG := p20StaticAccumUnderflowEnvelope_nonneg run.model
  have hx :
      0 ≤ ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
        p20StaticAccumUnderflowEnvelope run.model :=
    mul_nonneg (sq_nonneg _) hG
  have hu :
      4 * (h.underflowCount : ℝ) * (n : ℝ) *
          ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
            p20StaticAccumUnderflowEnvelope run.model ≤
        2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 *
          ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
            p20StaticAccumUnderflowEnvelope run.model := by
    calc
      4 * (h.underflowCount : ℝ) * (n : ℝ) *
          ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
            p20StaticAccumUnderflowEnvelope run.model
          ≤ 4 * ((n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2) *
              (n : ℝ) * ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
                p20StaticAccumUnderflowEnvelope run.model := by
            gcongr
            exact h.underflow_count_bound
      _ = 2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 *
            ((p20StaticScalingThreshold n run.model)⁻¹) ^ 2 *
              p20StaticAccumUnderflowEnvelope run.model := by ring
  unfold p20StaticRawAccumulationCoefficient
    p20StaticAccumulationCoefficient p20MultiAccumUnderflowCoefficient
  linarith

lemma p20StaticInputCoefficient_bound
    {m n q p : ℕ} (run : P20StaticMultiwordRun m n q p) :
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
  have hu : 0 ≤ u := p20UnitRoundoff_nonneg _
  have ht : 0 ≤ theta := p20StaticScalingThreshold_nonneg n run.model
  have hg : 0 ≤ gmin := p20StaticInputUnderflowEnvelope_nonneg run.model
  have ha : 0 ≤ u ^ p := pow_nonneg hu _
  have hb : 0 ≤
      2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin := by
    positivity
  have hz :
      max (u ^ p)
          (2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin) ≤
        u ^ p +
          2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin := by
    exact max_le (le_add_of_nonneg_right hb) (le_add_of_nonneg_left ha)
  change
    ((p : ℝ) - 1) * u ^ p +
        2 * max (u ^ p)
          (2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin) ≤
      ((p : ℝ) + 1) * u ^ p +
        4 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin
  calc
    ((p : ℝ) - 1) * u ^ p +
        2 * max (u ^ p)
          (2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin)
        ≤ ((p : ℝ) - 1) * u ^ p +
            2 * (u ^ p +
              2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin) := by
          gcongr
    _ = ((p : ℝ) + 1) * u ^ p +
          4 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin := by ring

lemma p20StaticTotalCoefficient_bound
    {m n q p : ℕ} {semantics : P20FirstOrderSemantics}
    (run : P20StaticMultiwordRun m n q p)
    (h : P20StaticSection4Derivation semantics run) :
    p20StaticOmittedCoefficient p
          (p20StaticInputUnitRoundoff run.model) +
        p20StaticRawAccumulationCoefficient n p h.underflowCount
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticAccumUnderflowEnvelope run.model) +
        2 * p20StaticZeta run ≤
      p20MultiNarrowCoefficient n p
        (p20StaticInputUnitRoundoff run.model)
        (p20StaticAccumUnitRoundoff run.model)
        (p20StaticScalingThreshold n run.model)
        (p20StaticInputUnderflowEnvelope run.model)
        (p20StaticAccumUnderflowEnvelope run.model) := by
  have hi := p20StaticInputCoefficient_bound run
  have hc := p20StaticRawAccumulationCoefficient_le run h
  calc
    p20StaticOmittedCoefficient p
          (p20StaticInputUnitRoundoff run.model) +
        p20StaticRawAccumulationCoefficient n p h.underflowCount
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticAccumUnderflowEnvelope run.model) +
        2 * p20StaticZeta run =
      (p20StaticOmittedCoefficient p
          (p20StaticInputUnitRoundoff run.model) +
        2 * p20StaticZeta run) +
        p20StaticRawAccumulationCoefficient n p h.underflowCount
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
          (p20StaticAccumUnderflowEnvelope run.model) := add_le_add hi hc
    _ = p20MultiNarrowCoefficient n p
          (p20StaticInputUnitRoundoff run.model)
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticInputUnderflowEnvelope run.model)
          (p20StaticAccumUnderflowEnvelope run.model) := by
        unfold p20MultiNarrowCoefficient p20MultiRangeFreeCoefficient
          p20StaticAccumulationCoefficient
        ring

lemma p20StaticFirstOrder_narrow
    {m n q p : ℕ} (semantics : P20FirstOrderSemantics)
    (run : P20StaticMultiwordRun m n q p)
    (h : P20StaticSection4Derivation semantics run) :
    p20FirstOrderLe semantics
      (p20StaticMultiwordForwardError run)
      (p20NormwiseEnvelope
        (p20MultiNarrowCoefficient n p
          (p20StaticInputUnitRoundoff run.model)
          (p20StaticAccumUnitRoundoff run.model)
          (p20StaticScalingThreshold n run.model)
          (p20StaticInputUnderflowEnvelope run.model)
          (p20StaticAccumUnderflowEnvelope run.model)) run.A run.B) := by
  let quadratic := p20StaticZeta run ^ 2 * p20InfNormRect run.A *
    p20InfNormRect run.B
  let remainder := |h.accumulationRemainder| + |h.omittedRemainder| + quadratic
  have hquadratic_nonneg : 0 ≤ quadratic := by
    dsimp [quadratic]
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (p20InfNormRect_nonneg run.A))
      (p20InfNormRect_nonneg run.B)
  have hremainder_nonneg : 0 ≤ remainder := by
    dsimp [remainder]
    exact add_nonneg
      (add_nonneg (abs_nonneg _) (abs_nonneg _)) hquadratic_nonneg
  have hremainder_second : semantics.secondOrder remainder := by
    dsimp [remainder, quadratic]
    exact semantics.add_secondOrder
      (semantics.add_secondOrder
        (semantics.abs_secondOrder h.accumulation_remainder_second_order)
        (semantics.abs_secondOrder h.omitted_remainder_second_order))
      h.quadratic_second_order
  refine ⟨remainder, hremainder_second, ?_⟩
  rw [abs_of_nonneg hremainder_nonneg]
  have hnorms : 0 ≤ p20InfNormRect run.A * p20InfNormRect run.B :=
    mul_nonneg (p20InfNormRect_nonneg run.A) (p20InfNormRect_nonneg run.B)
  have hcoeff := p20StaticTotalCoefficient_bound run h
  have hcoefficient_envelope :
      p20NormwiseEnvelope
          (p20StaticRawAccumulationCoefficient n p h.underflowCount
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
      p20StaticRawAccumulationCoefficient n p h.underflowCount
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model) *
            p20InfNormRect run.A * p20InfNormRect run.B +
          p20StaticOmittedCoefficient p
            (p20StaticInputUnitRoundoff run.model) *
            p20InfNormRect run.A * p20InfNormRect run.B +
          p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B +
          p20StaticZeta run * p20InfNormRect run.A * p20InfNormRect run.B =
        (p20StaticOmittedCoefficient p
              (p20StaticInputUnitRoundoff run.model) +
            p20StaticRawAccumulationCoefficient n p h.underflowCount
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticAccumUnderflowEnvelope run.model) +
            2 * p20StaticZeta run) *
          (p20InfNormRect run.A * p20InfNormRect run.B) := by ring
      _ ≤ p20MultiNarrowCoefficient n p
              (p20StaticInputUnitRoundoff run.model)
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticInputUnderflowEnvelope run.model)
              (p20StaticAccumUnderflowEnvelope run.model) *
            (p20InfNormRect run.A * p20InfNormRect run.B) :=
          mul_le_mul_of_nonneg_right hcoeff hnorms
      _ = p20MultiNarrowCoefficient n p
              (p20StaticInputUnitRoundoff run.model)
              (p20StaticAccumUnitRoundoff run.model)
              (p20StaticScalingThreshold n run.model)
              (p20StaticInputUnderflowEnvelope run.model)
              (p20StaticAccumUnderflowEnvelope run.model) *
            p20InfNormRect run.A * p20InfNormRect run.B := by ring
  have hforward := p20StaticForwardError_derivation_bound run h
  dsimp [remainder, quadratic]
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
  · intro run h
    exact p20StaticFirstOrder_narrow semantics run h
  constructor
  · intro run h
    have hmain := p20StaticFirstOrder_narrow semantics run h
    have hrhs :
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
    rw [← hrhs]
    exact hmain
  · intro run
    constructor
    · have hp : 1 ≤ p := run.word_count_pos
      unfold p20MultiInputRoundingCoefficient
        p20SingleInputRoundingCoefficient
      let u : ℝ := p20StaticInputUnitRoundoff run.model
      change ((p : ℝ) + 1) * u ^ p =
        (((p : ℝ) + 1) / 2 * u ^ (p - 1)) * (2 * u)
      have hpow : u ^ p = u ^ (p - 1) * u := by
        calc
          u ^ p = u ^ ((p - 1) + 1) := by
            congr 1
            omega
          _ = u ^ (p - 1) * u := pow_succ _ _
      rw [hpow]
      ring
    · unfold p20MultiInputUnderflowCoefficient
        p20SingleInputUnderflowCoefficient
      ring

end HighamBench
