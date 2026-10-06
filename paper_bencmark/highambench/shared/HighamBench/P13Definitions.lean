import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Sign

namespace HighamBench

open scoped BigOperators

noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p13InterpolationValue {n : ℕ}
    (ell f : Fin n → ℝ) : ℝ :=
  ∑ i, ell i * f i

noncomputable def p13Condition {n : ℕ}
    (ell f : Fin n → ℝ) : ℝ :=
  (∑ i, |ell i * f i|) / |p13InterpolationValue ell f|

noncomputable def p13DirectBarycentricWeight {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) (j : Fin (n + 1)) : ℝ :=
  (∏ k : Fin (n + 1), if k = j then 1 else nodes j - nodes k)⁻¹

noncomputable def p13DirectBarycentricCoefficient {n : ℕ}
    (nodes : Fin (n + 1) → ℝ) (x : ℝ) (j : Fin (n + 1)) : ℝ :=
  p13DirectBarycentricWeight nodes j / (x - nodes j)

structure P13SecondBarycentricProblem (n : ℕ) where
  nodes : Fin (n + 1) → ℝ
  data : Fin (n + 1) → ℝ
  x : ℝ
  nodes_injective : Function.Injective nodes
  evaluation_off_nodes : ∀ j, x ≠ nodes j

def p13WeightCounterLength (n : ℕ) : ℕ := 2 * n

def p13NumeratorEvaluationCounterLength (n : ℕ) : ℕ := n + 3

def p13DenominatorEvaluationCounterLength (n : ℕ) : ℕ := n + 2

def p13NumeratorCounterLength (n : ℕ) : ℕ := 3 * n + 4

def p13DenominatorCounterLength (n : ℕ) : ℕ := 3 * n + 2

structure P13RelativeErrorCounter (u : ℝ) (k : ℕ) where
  value : ℝ
  localError : Fin k → ℝ
  reciprocal : Fin k → Bool
  localError_le : ∀ i, |localError i| ≤ u
  value_eq :
    value = ∏ i, if reciprocal i then (1 + localError i)⁻¹ else 1 + localError i
  gamma_le : GammaValid u k → |value - 1| ≤ gamma u k

structure P13SecondBarycentricExecution {n : ℕ}
    (problem : P13SecondBarycentricProblem n) (u : ℝ) where
  u_nonneg : 0 ≤ u
  weightCounter :
    ∀ _j : Fin (n + 1), P13RelativeErrorCounter u (p13WeightCounterLength n)
  numeratorEvaluationCounter :
    ∀ _j : Fin (n + 1),
      P13RelativeErrorCounter u (p13NumeratorEvaluationCounterLength n)
  denominatorEvaluationCounter :
    ∀ _j : Fin (n + 1),
      P13RelativeErrorCounter u (p13DenominatorEvaluationCounterLength n)
  quotientCounter : P13RelativeErrorCounter u 1
  numeratorCounter :
    ∀ _j : Fin (n + 1), P13RelativeErrorCounter u (p13NumeratorCounterLength n)
  denominatorCounter :
    ∀ _j : Fin (n + 1), P13RelativeErrorCounter u (p13DenominatorCounterLength n)
  weightGammaValid : GammaValid u (p13WeightCounterLength n)
  numeratorEvaluationGammaValid :
    GammaValid u (p13NumeratorEvaluationCounterLength n)
  denominatorEvaluationGammaValid :
    GammaValid u (p13DenominatorEvaluationCounterLength n)
  quotientGammaValid : GammaValid u 1
  numeratorGammaValid : GammaValid u (p13NumeratorCounterLength n)
  denominatorGammaValid : GammaValid u (p13DenominatorCounterLength n)
  numeratorCounter_eq : ∀ j : Fin (n + 1),
    (numeratorCounter j).value =
      (weightCounter j).value * (numeratorEvaluationCounter j).value *
        quotientCounter.value
  denominatorCounter_eq : ∀ j : Fin (n + 1),
    (denominatorCounter j).value =
      (weightCounter j).value * (denominatorEvaluationCounter j).value

noncomputable def p13SecondBarycentricNumerator {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13InterpolationValue
    (p13DirectBarycentricCoefficient problem.nodes problem.x) problem.data

noncomputable def p13SecondBarycentricDenominator {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13InterpolationValue
    (p13DirectBarycentricCoefficient problem.nodes problem.x) (fun _ => 1)

noncomputable def p13SecondBarycentricExact {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13SecondBarycentricNumerator problem /
    p13SecondBarycentricDenominator problem

noncomputable def p13SecondBarycentricComputed {n : ℕ}
    {problem : P13SecondBarycentricProblem n} {u : ℝ}
    (run : P13SecondBarycentricExecution problem u) : ℝ :=
  ((∑ j,
      p13DirectBarycentricCoefficient problem.nodes problem.x j *
        (run.weightCounter j).value * problem.data j *
          (run.numeratorEvaluationCounter j).value) /
    (∑ j,
      p13DirectBarycentricCoefficient problem.nodes problem.x j *
        (run.weightCounter j).value *
          (run.denominatorEvaluationCounter j).value)) *
    run.quotientCounter.value

noncomputable def p13SecondBarycentricRelativeError {n : ℕ}
    {problem : P13SecondBarycentricProblem n} {u : ℝ}
    (run : P13SecondBarycentricExecution problem u) : ℝ :=
  |p13SecondBarycentricExact problem - p13SecondBarycentricComputed run| /
    |p13SecondBarycentricExact problem|

noncomputable def p13SecondBarycentricDataCondition {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13Condition
    (p13DirectBarycentricCoefficient problem.nodes problem.x) problem.data

noncomputable def p13SecondBarycentricOneCondition {n : ℕ}
    (problem : P13SecondBarycentricProblem n) : ℝ :=
  p13Condition
    (p13DirectBarycentricCoefficient problem.nodes problem.x) (fun _ => 1)

noncomputable def p13SecondBarycentricFirstOrderCoefficient
    (n : ℕ) (conditionData conditionOne : ℝ) : ℝ :=
  (p13NumeratorCounterLength n : ℝ) * conditionData +
    (p13DenominatorCounterLength n : ℝ) * conditionOne

end HighamBench
