import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Sqrt

namespace HighamBench

open scoped BigOperators

noncomputable def p20InfNormVec {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ((Finset.univ.sup (fun i : Fin n => Real.toNNReal |x i|) : NNReal) : ℝ)

noncomputable def p20ScalingThreshold (n : ℕ) (fmax Fmax : ℝ) : ℝ :=
  min fmax (Real.sqrt (Fmax / (n : ℝ)))

def p20IsPowerOfTwo (lambda : ℝ) : Prop :=
  ∃ exponent : ℤ, lambda = (2 : ℝ) ^ exponent

noncomputable def p20InfNormRect {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  let rowSum : Fin m → NNReal :=
    fun i => ∑ j : Fin n, ‖A i j‖₊
  ((Finset.univ.sup rowSum : NNReal) : ℝ)

def p20MultiInputRoundingCoefficient (p : ℕ) (u : ℝ) : ℝ :=
  ((p : ℝ) + 1) * u ^ p

def p20SingleInputRoundingCoefficient (u : ℝ) : ℝ :=
  2 * u

noncomputable def p20SingleInputUnderflowCoefficient
    (n : ℕ) (theta gmin : ℝ) : ℝ :=
  4 * (n : ℝ) ^ 2 * theta⁻¹ * gmin

def p20MultiAccumRoundingCoefficient (n p : ℕ) (U : ℝ) : ℝ :=
  ((n : ℝ) + (p : ℝ) ^ 2) * U

def p20MultiRangeFreeCoefficient (n p : ℕ) (u U : ℝ) : ℝ :=
  p20MultiInputRoundingCoefficient p u +
    p20MultiAccumRoundingCoefficient n p U

noncomputable def p20MultiInputUnderflowCoefficient
    (n p : ℕ) (u theta gmin : ℝ) : ℝ :=
  4 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin

noncomputable def p20MultiAccumUnderflowCoefficient
    (n p : ℕ) (theta Gmin : ℝ) : ℝ :=
  2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 *
    (theta⁻¹) ^ 2 * Gmin

noncomputable def p20MultiNarrowCoefficient
    (n p : ℕ) (u U theta gmin Gmin : ℝ) : ℝ :=
  p20MultiRangeFreeCoefficient n p u U +
    p20MultiInputUnderflowCoefficient n p u theta gmin +
      p20MultiAccumUnderflowCoefficient n p theta Gmin

noncomputable def p20NormwiseEnvelope {m n q : ℕ}
    (coefficient : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  coefficient * p20InfNormRect A * p20InfNormRect B

abbrev P20Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

noncomputable def p20UnitRoundoff (precision : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ precision

noncomputable def p20MinNormal (minExponent : ℤ) : ℝ :=
  (2 : ℝ) ^ minExponent

noncomputable def p20MaxFinite (precision : ℕ) (maxExponent : ℤ) : ℝ :=
  (2 : ℝ) ^ maxExponent * (2 - 2 * p20UnitRoundoff precision)

noncomputable def p20UnderflowEnvelope (precision : ℕ)
    (minExponent : ℤ) (hasSubnormals : Bool) : ℝ :=
  match hasSubnormals with
  | false => p20MinNormal minExponent / 2
  | true => p20UnitRoundoff precision * p20MinNormal minExponent

def p20ScaleRows {m n : ℕ} (lambda : Fin m → ℝ)
    (A : P20Matrix m n) : P20Matrix m n :=
  fun i j => lambda i * A i j

def p20ScaleColumns {n q : ℕ} (B : P20Matrix n q)
    (mu : Fin q → ℝ) : P20Matrix n q :=
  fun i j => B i j * mu j

def p20MaximalPowerTwoScale (theta vectorNorm lambda : ℝ) : Prop :=
  p20IsPowerOfTwo lambda ∧ 0 < lambda ∧
    ((vectorNorm = 0 ∧ lambda = 1) ∨
      (0 < vectorNorm ∧ theta / (2 * vectorNorm) < lambda ∧
        lambda ≤ theta / vectorNorm))

def p20RetainedWordPairs (p : ℕ) : List (Fin p × Fin p) :=
  (List.ofFn fun i : Fin p =>
    (List.ofFn fun j : Fin p => (i, j)).filter
      (fun pair => decide (pair.1.val + pair.2.val < p))).flatten

noncomputable def p20UnscaleProduct {m q : ℕ} (lambda : Fin m → ℝ)
    (mu : Fin q → ℝ) (C : P20Matrix m q) : P20Matrix m q :=
  fun i j => (lambda i)⁻¹ * C i j * (mu j)⁻¹

structure P20FirstOrderSemantics where
  secondOrder : ℝ → Prop
  zero_secondOrder : secondOrder 0
  add_secondOrder : ∀ {x y}, secondOrder x → secondOrder y →
    secondOrder (x + y)
  abs_secondOrder : ∀ {x}, secondOrder x → secondOrder |x|

def p20FirstOrderLe (semantics : P20FirstOrderSemantics)
    (lhs rhs : ℝ) : Prop :=
  ∃ remainder : ℝ,
    semantics.secondOrder remainder ∧ lhs ≤ rhs + |remainder|

structure P20StaticBinaryFormat where
  precision : ℕ
  minExponent : ℤ
  maxExponent : ℤ
  hasSubnormals : Bool
  precision_pos : 0 < precision
  exponent_range_nonempty : minExponent ≤ maxExponent

def p20StaticRepresentable (format : P20StaticBinaryFormat)
    (x : ℝ) : Prop :=
  x = 0 ∨
    ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
      ∃ significand : ℕ, ∃ exponent : ℤ,
        x = sign * (significand : ℝ) *
            (2 : ℝ) ^
              (exponent - (format.precision - 1 : ℕ)) ∧
          ((2 ^ (format.precision - 1) ≤ significand ∧
              significand < 2 ^ format.precision ∧
              format.minExponent ≤ exponent ∧
              exponent ≤ format.maxExponent) ∨
            (format.hasSubnormals = true ∧
              exponent = format.minExponent ∧
              0 < significand ∧
              significand < 2 ^ (format.precision - 1)))

structure P20StaticNearestModel1 where
  inputFormat : P20StaticBinaryFormat
  accumulationFormat : P20StaticBinaryFormat
  accumulation_precision :
    inputFormat.precision ≤ accumulationFormat.precision
  accumulation_range :
    accumulationFormat.minExponent ≤ inputFormat.minExponent ∧
      inputFormat.maxExponent ≤ accumulationFormat.maxExponent
  inputRound : ℝ → ℝ
  inputDelta : ℝ → ℝ
  inputEta : ℝ → ℝ
  inputNoOverflow : ℝ → Prop
  input_rounding_equation : ∀ {x}, inputNoOverflow x →
    inputRound x = x * (1 + inputDelta x) + inputEta x
  input_delta_bound : ∀ {x}, inputNoOverflow x →
    |inputDelta x| ≤ p20UnitRoundoff inputFormat.precision
  input_eta_bound : ∀ {x}, inputNoOverflow x →
    |inputEta x| ≤
      p20UnderflowEnvelope inputFormat.precision inputFormat.minExponent
        inputFormat.hasSubnormals
  input_error_exclusive : ∀ {x}, inputNoOverflow x →
    inputEta x * inputDelta x = 0
  input_round_representable : ∀ {x}, inputNoOverflow x →
    p20StaticRepresentable inputFormat (inputRound x)
  input_round_nearest : ∀ {x}, inputNoOverflow x →
    ∀ {y}, p20StaticRepresentable inputFormat y →
      |inputRound x - x| ≤ |y - x|
  accumulationRound : ℝ → ℝ
  accumulationDelta : ℝ → ℝ
  accumulationEta : ℝ → ℝ
  accumulationNoOverflow : ℝ → Prop
  accumulation_rounding_equation : ∀ {x}, accumulationNoOverflow x →
    accumulationRound x =
      x * (1 + accumulationDelta x) + accumulationEta x
  accumulation_delta_bound : ∀ {x}, accumulationNoOverflow x →
    |accumulationDelta x| ≤
      p20UnitRoundoff accumulationFormat.precision
  accumulation_eta_bound : ∀ {x}, accumulationNoOverflow x →
    |accumulationEta x| ≤
      p20UnderflowEnvelope accumulationFormat.precision
        accumulationFormat.minExponent accumulationFormat.hasSubnormals
  accumulation_error_exclusive : ∀ {x}, accumulationNoOverflow x →
    accumulationEta x * accumulationDelta x = 0
  accumulation_round_representable : ∀ {x}, accumulationNoOverflow x →
    p20StaticRepresentable accumulationFormat (accumulationRound x)
  accumulation_round_nearest : ∀ {x}, accumulationNoOverflow x →
    ∀ {y}, p20StaticRepresentable accumulationFormat y →
      |accumulationRound x - x| ≤ |y - x|

noncomputable def p20StaticInputUnitRoundoff
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnitRoundoff model.inputFormat.precision

noncomputable def p20StaticAccumUnitRoundoff
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnitRoundoff model.accumulationFormat.precision

noncomputable def p20StaticInputUnderflowEnvelope
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnderflowEnvelope model.inputFormat.precision
    model.inputFormat.minExponent model.inputFormat.hasSubnormals

noncomputable def p20StaticAccumUnderflowEnvelope
    (model : P20StaticNearestModel1) : ℝ :=
  p20UnderflowEnvelope model.accumulationFormat.precision
    model.accumulationFormat.minExponent
    model.accumulationFormat.hasSubnormals

noncomputable def p20StaticScalingThreshold (n : ℕ)
    (model : P20StaticNearestModel1) : ℝ :=
  p20ScalingThreshold n
    (p20MaxFinite model.inputFormat.precision
      model.inputFormat.maxExponent)
    (p20MaxFinite model.accumulationFormat.precision
      model.accumulationFormat.maxExponent)

def p20RoundedFoldFrom (round : ℝ → ℝ) : ℝ → List ℝ → ℝ
  | acc, [] => acc
  | acc, term :: terms =>
      p20RoundedFoldFrom round (round (acc + term)) terms

def p20RoundedFoldNoOverflowFrom (allowed : ℝ → Prop)
    (round : ℝ → ℝ) : ℝ → List ℝ → Prop
  | _, [] => True
  | acc, term :: terms =>
      allowed (acc + term) ∧
        p20RoundedFoldNoOverflowFrom allowed round
          (round (acc + term)) terms

noncomputable def p20StaticAccumulatedInnerProduct {n : ℕ}
    (model : P20StaticNearestModel1) (x y : Fin n → ℝ) : ℝ :=
  p20RoundedFoldFrom model.accumulationRound 0
    ((List.ofFn fun k : Fin n =>
      model.accumulationRound (x k * y k)))

def p20StaticInnerProductNoOverflow {n : ℕ}
    (model : P20StaticNearestModel1) (x y : Fin n → ℝ) : Prop :=
  (∀ k, model.accumulationNoOverflow (x k * y k)) ∧
    p20RoundedFoldNoOverflowFrom model.accumulationNoOverflow
      model.accumulationRound 0
        (List.ofFn fun k : Fin n =>
          model.accumulationRound (x k * y k))

noncomputable def p20StaticRetainedWordProduct {m n q p : ℕ}
    (model : P20StaticNearestModel1) (u : ℝ)
    (Aword : Fin p → P20Matrix m n)
    (Bword : Fin p → P20Matrix n q) : P20Matrix m q :=
  fun row col =>
    p20RoundedFoldFrom model.accumulationRound 0
      ((p20RetainedWordPairs p).map (fun pair =>
        u ^ (pair.1.val + pair.2.val) *
          p20StaticAccumulatedInnerProduct model (Aword pair.1 row)
            (fun k => Bword pair.2 k col)))

structure P20StaticMultiwordRun (m n q p : ℕ) where
  dimension_pos : 0 < m ∧ 0 < n ∧ 0 < q
  word_count_pos : 0 < p
  model : P20StaticNearestModel1
  A : P20Matrix m n
  B : P20Matrix n q
  rowScale : Fin m → ℝ
  columnScale : Fin q → ℝ
  row_scaling_rule : ∀ i,
    p20MaximalPowerTwoScale (p20StaticScalingThreshold n model)
      (p20InfNormVec (A i)) (rowScale i)
  column_scaling_rule : ∀ j,
    p20MaximalPowerTwoScale (p20StaticScalingThreshold n model)
      (p20InfNormVec (fun i => B i j)) (columnScale j)
  scaled_A_bound : ∀ i j,
    |p20ScaleRows rowScale A i j| ≤ p20StaticScalingThreshold n model
  scaled_B_bound : ∀ i j,
    |p20ScaleColumns B columnScale i j| ≤
      p20StaticScalingThreshold n model
  Aword : Fin p → P20Matrix m n
  Bword : Fin p → P20Matrix n q
  Aword_equation : ∀ (i : Fin p) (row : Fin m) (col : Fin n),
    Aword i row col = model.inputRound
      ((p20ScaleRows rowScale A row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Aword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  Aword_no_overflow : ∀ (i : Fin p) (row : Fin m) (col : Fin n),
    model.inputNoOverflow
      ((p20ScaleRows rowScale A row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Aword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  Bword_equation : ∀ (i : Fin p) (row : Fin n) (col : Fin q),
    Bword i row col = model.inputRound
      ((p20ScaleColumns B columnScale row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Bword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  Bword_no_overflow : ∀ (i : Fin p) (row : Fin n) (col : Fin q),
    model.inputNoOverflow
      ((p20ScaleColumns B columnScale row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p20StaticInputUnitRoundoff model ^ k.val *
              Bword k row col)) /
        p20StaticInputUnitRoundoff model ^ i.val)
  accumulation_no_overflow : ∀ (i j : Fin p),
    i.val + j.val < p → ∀ (row : Fin m) (col : Fin q),
      p20StaticInnerProductNoOverflow model (Aword i row)
        (fun k => Bword j k col)
  retained_sum_no_overflow : ∀ (row : Fin m) (col : Fin q),
    p20RoundedFoldNoOverflowFrom model.accumulationNoOverflow
      model.accumulationRound 0
        ((p20RetainedWordPairs p).map (fun pair =>
          p20StaticInputUnitRoundoff model ^
              (pair.1.val + pair.2.val) *
            p20StaticAccumulatedInnerProduct model (Aword pair.1 row)
              (fun k => Bword pair.2 k col)))
  computed : P20Matrix m q
  computed_equation :
    computed = p20UnscaleProduct rowScale columnScale
      (p20StaticRetainedWordProduct model
        (p20StaticInputUnitRoundoff model) Aword Bword)

noncomputable def p20StaticAWordApproximation {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m n :=
  fun row col =>
    (run.rowScale row)⁻¹ *
      ∑ i : Fin p,
        p20StaticInputUnitRoundoff run.model ^ i.val *
          run.Aword i row col

noncomputable def p20StaticBWordApproximation {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix n q :=
  fun row col =>
    (∑ i : Fin p,
        p20StaticInputUnitRoundoff run.model ^ i.val *
          run.Bword i row col) *
      (run.columnScale col)⁻¹

noncomputable def p20StaticExactRetainedWordProduct {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m q :=
  p20UnscaleProduct run.rowScale run.columnScale
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => i.val + j.val < p))
          (fun j =>
            p20StaticInputUnitRoundoff run.model ^ (i.val + j.val) *
              (run.Aword i * run.Bword j) row col))

noncomputable def p20StaticOmittedWordTail {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m q :=
  p20UnscaleProduct run.rowScale run.columnScale
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => p ≤ i.val + j.val))
          (fun j =>
            p20StaticInputUnitRoundoff run.model ^ (i.val + j.val) *
              (run.Aword i * run.Bword j) row col))

noncomputable def p20StaticAccumulationError {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : P20Matrix m q :=
  run.computed - p20StaticExactRetainedWordProduct run

noncomputable def p20StaticMultiwordForwardError {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : ℝ :=
  p20InfNormRect (run.computed - run.A * run.B)

noncomputable def p20StaticZeta {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) : ℝ :=
  max (p20StaticInputUnitRoundoff run.model ^ p)
    (2 * (n : ℝ) * p20StaticInputUnitRoundoff run.model ^ (p - 1) *
      (p20StaticScalingThreshold n run.model)⁻¹ *
        p20StaticInputUnderflowEnvelope run.model)

def p20StaticOmittedCoefficient (p : ℕ) (u : ℝ) : ℝ :=
  ((p : ℝ) - 1) * u ^ p

noncomputable def p20StaticAccumulationCoefficient
    (n p : ℕ) (U theta Gmin : ℝ) : ℝ :=
  p20MultiAccumRoundingCoefficient n p U +
    p20MultiAccumUnderflowCoefficient n p theta Gmin

noncomputable def p20StaticRawAccumulationCoefficient
    (n p r : ℕ) (U theta Gmin : ℝ) : ℝ :=
  p20MultiAccumRoundingCoefficient n p U +
    4 * (r : ℝ) * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin

structure P20StaticSection4Derivation
    (semantics : P20FirstOrderSemantics) {m n q p : ℕ}
    (run : P20StaticMultiwordRun m n q p) where
  AError : P20Matrix m n
  BError : P20Matrix n q
  A_decomposition :
    run.A = p20StaticAWordApproximation run + AError
  B_decomposition :
    run.B = p20StaticBWordApproximation run + BError
  A_error_bound :
    p20InfNormRect AError ≤ p20StaticZeta run * p20InfNormRect run.A
  B_error_bound :
    p20InfNormRect BError ≤ p20StaticZeta run * p20InfNormRect run.B
  retained_partition :
    p20StaticExactRetainedWordProduct run =
      p20StaticAWordApproximation run *
          p20StaticBWordApproximation run -
        p20StaticOmittedWordTail run
  omittedRemainder : ℝ
  omitted_remainder_second_order :
    semantics.secondOrder omittedRemainder
  omitted_tail_bound :
    p20InfNormRect (p20StaticOmittedWordTail run) ≤
      p20NormwiseEnvelope
          (p20StaticOmittedCoefficient p
            (p20StaticInputUnitRoundoff run.model)) run.A run.B +
        |omittedRemainder|
  accumulationRemainder : ℝ
  accumulation_remainder_second_order :
    semantics.secondOrder accumulationRemainder
  underflowCount : ℕ
  underflow_count_bound :
    (underflowCount : ℝ) ≤
      (n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2
  accumulation_error_bound :
    p20InfNormRect (p20StaticAccumulationError run) ≤
      p20NormwiseEnvelope
          (p20StaticRawAccumulationCoefficient n p underflowCount
            (p20StaticAccumUnitRoundoff run.model)
            (p20StaticScalingThreshold n run.model)
            (p20StaticAccumUnderflowEnvelope run.model)) run.A run.B +
        |accumulationRemainder|
  quadratic_second_order :
    semantics.secondOrder
      (p20StaticZeta run ^ 2 * p20InfNormRect run.A *
        p20InfNormRect run.B)

end HighamBench
