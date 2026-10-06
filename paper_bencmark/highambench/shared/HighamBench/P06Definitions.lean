import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace HighamBench

open scoped BigOperators

noncomputable def p06VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

noncomputable def p06FrobNorm {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)

noncomputable def p06FiniteId {ι : Type*} [DecidableEq ι] : ι → ι → ℝ :=
  fun i j ↦ if i = j then 1 else 0

noncomputable def p06RectMatMul {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (R : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j ↦ ∑ k : Fin m, Q i k * R k j

noncomputable def p06MatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

def p06RectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (L : ℝ) : Prop :=
  ∀ x, p06VecNorm2 (p06MatVec A x) ≤ L * p06VecNorm2 x

noncomputable def p06HouseholderMatrix {m : ℕ}
    (v : Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j ↦ p06FiniteId i j - v i * v j

def p06Orthogonal {m : ℕ} (Q : Fin m → Fin m → ℝ) : Prop :=
  ∀ i j, (∑ k : Fin m, Q k i * Q k j) = p06FiniteId i j

def p06UpperTrapezoidal {m n : ℕ}
    (R : Fin m → Fin n → ℝ) : Prop :=
  ∀ i j, j.val < i.val → R i j = 0

noncomputable def p06GammaTilde (k : ℕ) (lambda u : ℝ) : ℝ :=
  Real.exp
      ((lambda * Real.sqrt (k : ℝ) * u + (k : ℝ) * u ^ 2) /
        (1 - u)) -
    1

noncomputable def p06QRLeadingCoefficient
    (c6 : ℕ) (lambda : ℝ) (m n : ℕ) (u : ℝ) : ℝ :=
  (c6 : ℝ) * lambda * Real.sqrt (n : ℝ) *
    p06GammaTilde m lambda u

noncomputable def p06P4 (lambda : ℝ) (m n : ℕ) : ℝ :=
  1 - 2 * (m : ℝ) * (n : ℝ) * Real.exp (-lambda ^ 2)

def p06SecondOrderAtZero (remainder : ℝ → ℝ) : Prop :=
  remainder =O[nhds 0] fun u : ℝ ↦ u ^ 2

def p06SecondOrderAtZeroRight (remainder : ℝ → ℝ) : Prop :=
  remainder =O[nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)] fun u : ℝ ↦ u ^ 2

def P06SecondOrderControl (remainder : ℝ → ℝ) (u0 : ℝ) : Prop :=
  ∃ constant : ℝ, 0 ≤ constant ∧
    p06SecondOrderAtZero remainder ∧
    ∀ u, |u| ≤ |u0| → |remainder u| ≤ constant * u ^ 2

def p06PriorErrors {Ω : Type*} {steps : ℕ}
    (error : Fin steps → Ω → ℝ) (k : Fin steps) (omega : Ω) :
    Fin k.val → ℝ :=
  fun i ↦ error ⟨i.val, lt_trans i.isLt k.isLt⟩ omega

def p06MeanIndependent {Ω : Type*} [MeasurableSpace Ω]
    (mu : MeasureTheory.Measure Ω) {steps : ℕ}
    (error : Fin steps → Ω → ℝ) : Prop :=
  ∀ (k : Fin steps) (g : (Fin k.val → ℝ) → ℝ),
    MeasureTheory.Integrable
        (fun omega ↦ g (p06PriorErrors error k omega)) mu →
      MeasureTheory.Integrable
        (fun omega ↦
          g (p06PriorErrors error k omega) * error k omega) mu →
      (∫ omega,
          g (p06PriorErrors error k omega) * error k omega ∂mu) =
        (∫ omega, g (p06PriorErrors error k omega) ∂mu) *
          ∫ omega, error k omega ∂mu

structure P06Model15 (Ω : Type*) [MeasurableSpace Ω] where
  probability : MeasureTheory.Measure Ω
  probability_univ : probability Set.univ = 1
  operationCount : ℕ
  exactValue : Fin operationCount → Ω → ℝ
  computedValue : Fin operationCount → Ω → ℝ
  error : Fin operationCount → Ω → ℝ
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  unitRoundoff_lt_one : unitRoundoff < 1
  relative_error : ∀ k omega,
    computedValue k omega = exactValue k omega * (1 + error k omega)
  error_bound : ∀ k omega, |error k omega| ≤ unitRoundoff
  error_measurable : ∀ k, Measurable (error k)
  error_integrable : ∀ k,
    MeasureTheory.Integrable (error k) probability
  error_mean_zero : ∀ k, ∫ omega, error k omega ∂probability = 0
  error_mean_independent : p06MeanIndependent probability error

def p06MatrixFamilyIsBigOAtZero {m : ℕ}
    (A : ℝ → Matrix (Fin m) (Fin m) ℝ) (scale : ℝ → ℝ) : Prop :=
  ∀ i j, (fun u ↦ A u i j) =O[nhds 0] scale

def p06MatrixSecondOrderAtZero {m : ℕ}
    (remainder : ℝ → Matrix (Fin m) (Fin m) ℝ) : Prop :=
  p06MatrixFamilyIsBigOAtZero remainder fun u ↦ u ^ 2

noncomputable def p06HouseholderProduct {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ) :
    ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => 1
  | k + 1 => P k * p06HouseholderProduct P k

noncomputable def p06PerturbedHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 1
  | u, omega, k + 1 =>
      (P k + DeltaP u k omega) *
        p06PerturbedHouseholderProduct P DeltaP u omega k

noncomputable def p06FirstOrderHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 0
  | u, omega, k + 1 =>
      P k * p06FirstOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega * p06HouseholderProduct P k

noncomputable def p06HigherOrderHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 0
  | u, omega, k + 1 =>
      P k * p06HigherOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega *
          p06FirstOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega *
          p06HigherOrderHouseholderProduct P DeltaP u omega k

noncomputable def p06HouseholderSequenceMatrix {m : ℕ}
    (v : ℕ → Fin m → ℝ) (j : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  p06HouseholderMatrix (v j)

structure P06HouseholderApplicationFamily
    (Omega : Type*) [MeasurableSpace Omega] (m r : ℕ)
    (model : P06Model15 Omega) where
  dimension_pos : 0 < m
  steps_pos : 0 < r
  b : Fin m → ℝ
  householderVector : ℕ → Fin m → ℝ
  localPerturbation :
    ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ
  computed : ℝ → Omega → Fin m → ℝ
  outputIndex : Fin m → Fin model.operationCount
  householder_normalized : ∀ j, j < r →
    ∑ i : Fin m, householderVector j i ^ 2 = 2
  householder_involutory : ∀ j, j < r →
    p06HouseholderSequenceMatrix householderVector j *
        p06HouseholderSequenceMatrix householderVector j = 1
  computed_product : ∀ u omega,
    computed u omega =
      p06MatVec
        (p06PerturbedHouseholderProduct
          (p06HouseholderSequenceMatrix householderVector)
          localPerturbation u omega r)
        b
  output_from_trace : ∀ omega i,
    computed model.unitRoundoff omega i =
      model.computedValue (outputIndex i) omega

structure P06Lemma42VectorAssumption
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (c5 : ℕ) (lambda : ℝ) where
  localEvent : Set Omega
  localEvent_measurable : MeasurableSet localEvent
  localEvent_iff : ∀ omega,
    omega ∈ localEvent ↔
      ∀ j : Fin r,
        p06RectOpNorm2Le
          (run.localPerturbation model.unitRoundoff j.val omega)
          ((c5 : ℝ) * p06GammaTilde m lambda model.unitRoundoff)
  local_first_order : ∀ omega, omega ∈ localEvent →
    ∀ j, j < r →
      p06MatrixFamilyIsBigOAtZero
        (fun u ↦ run.localPerturbation u j omega) (fun u ↦ u)
  probability_one : model.probability localEvent = 1

noncomputable def p06ApplicationExactState
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model) : Fin m → ℝ :=
  p06MatVec
    (p06HouseholderProduct
      (p06HouseholderSequenceMatrix run.householderVector) r)
    run.b

noncomputable def p06TransformedHouseholderInsertion
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (j : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.transpose (p06HouseholderProduct P (j + 1)) *
    DeltaP u j omega * p06HouseholderProduct P j

noncomputable def p06TransformedHouseholderInsertionSum
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (k : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ j ∈ Finset.range k,
    p06TransformedHouseholderInsertion P DeltaP u omega j

noncomputable def p06ApplicationQ
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.transpose
    (p06HouseholderProduct
      (p06HouseholderSequenceMatrix run.householderVector) r)

noncomputable def p06ApplicationFirstOrderMatrix
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) : Matrix (Fin m) (Fin m) ℝ :=
  p06FirstOrderHouseholderProduct
    (p06HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega r

noncomputable def p06ApplicationF
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) (j : Fin r) : Matrix (Fin m) (Fin m) ℝ :=
  p06TransformedHouseholderInsertion
    (p06HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega j.val

noncomputable def p06ApplicationFSum
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P06Model15 Omega}
    (run : P06HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) : Matrix (Fin m) (Fin m) ℝ :=
  p06TransformedHouseholderInsertionSum
    (p06HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega r

end HighamBench
