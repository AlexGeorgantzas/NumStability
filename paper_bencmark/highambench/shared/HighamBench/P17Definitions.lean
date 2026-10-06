import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace HighamBench

open scoped BigOperators

noncomputable def p17Gamma (n : ℕ) (u : ℝ) : ℝ :=
  (1 + u) ^ n - 1

noncomputable def p17UnitRoundoff (p : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ (p - 1)

noncomputable def p17ExactSum {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i, a i

noncomputable def p17SummationCondition {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  (∑ i, |a i|) / |p17ExactSum a|

structure P17FiniteProbability (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  prob_sum : ∑ ω, prob ω = 1

noncomputable def p17EventProb {Ω : Type*} [Fintype Ω]
    (P : P17FiniteProbability Ω) (E : Set Ω) : ℝ := by
  classical
  exact ∑ ω, if ω ∈ E then P.prob ω else 0

noncomputable def p17Expectation {Ω : Type*} [Fintype Ω]
    (P : P17FiniteProbability Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.prob ω * X ω

def p17HistoryMeasurable {m : ℕ} {Ω : Type*}
    (delta : Fin m → Ω → ℝ) (k : Fin m) (X : Ω → ℝ) : Prop :=
  ∀ ω₁ ω₂,
    (∀ j : Fin m, j.val < k.val → delta j ω₁ = delta j ω₂) →
      X ω₁ = X ω₂

structure P17Lemma310Run
    (n : ℕ) (Ω : Type*) [Fintype Ω] where
  probability : P17FiniteProbability Ω
  operation_count_pos : 0 < n
  unitRoundoff : ℝ
  biasRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  biasRoundoff_nonneg : 0 ≤ biasRoundoff
  delta : Fin n → Ω → ℝ
  beta : Fin n → Ω → ℝ
  alpha_bound : ∀ k ω, |delta k ω - beta k ω| ≤ unitRoundoff
  beta_bound : ∀ k ω, |beta k ω| ≤ biasRoundoff
  conditional_mean_from_alpha_history : ∀ k X,
    p17HistoryMeasurable (fun j ω => delta j ω - beta j ω) k X →
      p17Expectation probability (fun ω => X ω * delta k ω) =
        p17Expectation probability (fun ω => X ω * beta k ω)

noncomputable def p17ProductAlpha
    {n : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17Lemma310Run n Ω) (k : Fin n) (ω : Ω) : ℝ :=
  run.delta k ω - run.beta k ω

def p17SuffixIndexSet {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun k => i.val ≤ k.val

noncomputable def p17Lemma310BiasRemainder
    {n : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17Lemma310Run n Ω) (i : Fin n) (ω : Ω) : ℝ :=
  let I := p17SuffixIndexSet i
  ∑ K ∈ I.powerset.erase I,
    (∏ k ∈ K, (1 + p17ProductAlpha run k ω)) *
      ∏ k ∈ I \ K, run.beta k ω

noncomputable def p17RecursiveSum {m : ℕ}
    (a : Fin (m + 1) → ℝ) (delta : Fin m → ℝ) : ℝ :=
  Fin.foldl m
    (fun acc k => (acc + a k.succ) * (1 + delta k))
    (a 0)

noncomputable def p17RecursiveSumBefore {m : ℕ}
    (a : Fin (m + 1) → ℝ) (delta : Fin m → ℝ) (k : Fin m) : ℝ :=
  Fin.foldl k.val
    (fun acc j =>
      let q : Fin m := ⟨j.val, Nat.lt_trans j.isLt k.isLt⟩
      (acc + a q.succ) * (1 + delta q))
    (a 0)

noncomputable def p17RecursivePreRound {m : ℕ}
    (a : Fin (m + 1) → ℝ) (delta : Fin m → ℝ) (k : Fin m) : ℝ :=
  p17RecursiveSumBefore a delta k + a k.succ

structure P17LimitedPrecisionRecursiveSumRun
    (m : ℕ) (Ω : Type*) [Fintype Ω] where
  probability : P17FiniteProbability Ω
  p : ℕ
  r : ℕ
  p_pos : 0 < p
  r_pos : 0 < r
  a : Fin (m + 1) → ℝ
  delta : Fin m → Ω → ℝ
  beta : Fin m → Ω → ℝ
  truncate : ℝ → ℝ
  delta_bound : ∀ k ω, |delta k ω| ≤ p17UnitRoundoff p
  rounding_factor_nonneg : ∀ k ω, 0 ≤ 1 + delta k ω
  beta_bound : ∀ k ω, |beta k ω| ≤ p17UnitRoundoff (p + r)
  truncation_equation : ∀ k ω,
    truncate (p17RecursivePreRound a (fun j => delta j ω) k) =
      p17RecursivePreRound a (fun j => delta j ω) k * (1 + beta k ω)
  delta_zero : ∀ k ω,
    p17RecursivePreRound a (fun j => delta j ω) k = 0 → delta k ω = 0
  beta_zero : ∀ k ω,
    p17RecursivePreRound a (fun j => delta j ω) k = 0 → beta k ω = 0
  beta_history : ∀ k, p17HistoryMeasurable delta k (beta k)
  conditional_mean : ∀ k X,
    p17HistoryMeasurable delta k X →
      p17Expectation probability (fun ω => X ω * delta k ω) =
        p17Expectation probability (fun ω => X ω * beta k ω)

noncomputable def p17SuffixErrorProduct :
    (m : ℕ) → (Fin m → ℝ) → Fin m → ℝ
  | 0, _ => fun i => i.elim0
  | m + 1, delta =>
      Fin.lastCases (1 + delta (Fin.last m))
        (fun i =>
          p17SuffixErrorProduct m (fun j => delta j.castSucc) i *
            (1 + delta (Fin.last m)))

noncomputable def p17RecursiveCoefficient {m : ℕ}
    (error : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases (∏ k : Fin m, (1 + error k))
    (fun i => p17SuffixErrorProduct m error i)

noncomputable def p17Alpha
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω)
    (k : Fin m) (ω : Ω) : ℝ :=
  run.delta k ω - run.beta k ω

noncomputable def p17CoefficientRemainder
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω)
    (i : Fin (m + 1)) (ω : Ω) : ℝ :=
  p17RecursiveCoefficient (fun k => run.delta k ω) i -
    p17RecursiveCoefficient (fun k => p17Alpha run k ω) i

noncomputable def p17CenteredSummationError
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω) (ω : Ω) : ℝ :=
  ∑ i : Fin (m + 1),
    run.a i *
      (p17RecursiveCoefficient (fun k => p17Alpha run k ω) i - 1)

noncomputable def p17LimitedPrecisionRemainder
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17LimitedPrecisionRecursiveSumRun m Ω) (ω : Ω) : ℝ :=
  ∑ i : Fin (m + 1), run.a i * p17CoefficientRemainder run i ω

structure P17VarianceRecursiveSumRun
    (m : ℕ) (Ω : Type*) [Fintype Ω]
    extends P17LimitedPrecisionRecursiveSumRun m Ω where
  alpha_bound : ∀ k ω,
    |p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω| ≤
      p17UnitRoundoff p
  alpha_mean_independent : ∀ k X,
    p17HistoryMeasurable
        (fun j ω => p17Alpha toP17LimitedPrecisionRecursiveSumRun j ω) k X →
      p17Expectation probability
        (fun ω => X ω *
          p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω) = 0
  alpha_product_covariance_bound : ∀ i j,
    0 ≤ p17Expectation probability (fun ω =>
        (p17RecursiveCoefficient
              (fun k => p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω) i - 1) *
          (p17RecursiveCoefficient
              (fun k => p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω) j - 1)) ∧
      p17Expectation probability (fun ω =>
          (p17RecursiveCoefficient
                (fun k => p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω) i - 1) *
            (p17RecursiveCoefficient
                (fun k => p17Alpha toP17LimitedPrecisionRecursiveSumRun k ω) j - 1)) ≤
        p17Gamma m ((p17UnitRoundoff p) ^ 2)
  coefficient_remainder_bound : ∀ i ω,
    |p17CoefficientRemainder toP17LimitedPrecisionRecursiveSumRun i ω| ≤
      p17Gamma m
          (p17UnitRoundoff p + p17UnitRoundoff (p + r)) -
        p17Gamma m (p17UnitRoundoff p)

end HighamBench
