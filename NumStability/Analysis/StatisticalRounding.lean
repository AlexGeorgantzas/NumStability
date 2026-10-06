-- Analysis/StatisticalRounding.lean
--
-- Higham Chapter 2, Section 2.6: statistical rounding-error model.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.FiniteProbability

namespace NumStability

open scoped BigOperators

/-!
# Statistical Rounding-Error Model

Higham Chapter 2, Section 2.6 explains the common rule of thumb that
dimension-dependent worst-case constants behave like their square roots under
probabilistic rounding-error models.  The text explicitly warns that ordinary
rounding errors are not random; the theorem below therefore keeps the
probabilistic assumptions visible.
-/

noncomputable section

/-- The accumulated statistical rounding error `sum_i eps_i`. -/
def statisticalRoundingErrorSum {n : ℕ} {Ω : Type*} (eps : Fin n → Ω → ℝ)
    (ω : Ω) : ℝ :=
  ∑ i, eps i ω

/-- Weighted accumulated statistical rounding error `sum_i w_i eps_i`.

For Higham Chapter 4, Section 4.5, the deterministic weights represent the
intermediate-sum factors multiplying the random addition errors in the running
error identity. -/
def statisticalWeightedRoundingErrorSum {n : ℕ} {Ω : Type*}
    (w : Fin n → ℝ) (eps : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, w i * eps i ω

/-- Finite-probability version of Higham §2.6's independent, zero-mean
rounding-error heuristic.

Pairwise uncorrelated cross terms are the exact second-moment consequence used
for the `sqrt n` rule; independent models imply this under the usual mean-zero
assumption, but the theorem surface records only the needed finite-moment
facts. -/
structure StatisticalRoundingErrorModel {n : ℕ} {Ω : Type*} [Fintype Ω]
    (P : FiniteProbability Ω) (eps : Fin n → Ω → ℝ) (u : ℝ) : Prop where
  mean_zero : ∀ i, P.expectationReal (eps i) = 0
  pairwise_uncorrelated :
    ∀ i j, i ≠ j → P.expectationReal (fun ω => eps i ω * eps j ω) = 0
  second_moment_le : ∀ i, P.expectationReal (fun ω => (eps i ω) ^ 2) ≤ u ^ 2

namespace StatisticalRoundingErrorModel

variable {n : ℕ} {Ω : Type*} [Fintype Ω]
variable {P : FiniteProbability Ω} {eps : Fin n → Ω → ℝ} {u : ℝ}

theorem expectation_sum_eq_zero
    (h : StatisticalRoundingErrorModel P eps u) :
    P.expectationReal (statisticalRoundingErrorSum eps) = 0 := by
  classical
  unfold statisticalRoundingErrorSum
  rw [P.expectationReal_sum]
  simp [h.mean_zero]

/-- Weighted local rounding errors still have zero mean when the individual
addition errors have zero mean. -/
theorem expectation_weighted_sum_eq_zero
    (h : StatisticalRoundingErrorModel P eps u) (w : Fin n → ℝ) :
    P.expectationReal (statisticalWeightedRoundingErrorSum w eps) = 0 := by
  classical
  unfold statisticalWeightedRoundingErrorSum
  calc
    P.expectationReal (fun ω => ∑ i, w i * eps i ω)
        = ∑ i, P.expectationReal (fun ω => w i * eps i ω) := by
            rw [P.expectationReal_sum]
    _ = ∑ i, w i * P.expectationReal (eps i) := by
            apply Finset.sum_congr rfl
            intro i _
            exact P.expectationReal_const_mul (eps i) (w i)
    _ = 0 := by
            simp [h.mean_zero]

theorem expectation_sum_sq_eq_sum_second_moments
    (h : StatisticalRoundingErrorModel P eps u) :
    P.expectationReal (fun ω => (statisticalRoundingErrorSum eps ω) ^ 2) =
      ∑ i, P.expectationReal (fun ω => (eps i ω) ^ 2) := by
  classical
  have hpoint :
      ∀ ω, (statisticalRoundingErrorSum eps ω) ^ 2 =
        ∑ i, ∑ j, eps i ω * eps j ω := by
    intro ω
    unfold statisticalRoundingErrorSum
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    P.expectationReal (fun ω => (statisticalRoundingErrorSum eps ω) ^ 2)
        = P.expectationReal (fun ω => ∑ i, ∑ j, eps i ω * eps j ω) := by
            apply congrArg
            funext ω
            exact hpoint ω
    _ = ∑ i, P.expectationReal (fun ω => ∑ j, eps i ω * eps j ω) := by
            rw [P.expectationReal_sum]
    _ = ∑ i, ∑ j, P.expectationReal (fun ω => eps i ω * eps j ω) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [P.expectationReal_sum]
    _ = ∑ i, P.expectationReal (fun ω => (eps i ω) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_eq_single i]
            · apply congrArg
              funext ω
              ring
            · intro j _ hji
              exact h.pairwise_uncorrelated i j (Ne.symm hji)
            · intro hi
              exact False.elim (hi (Finset.mem_univ i))

/-- Weighted second-moment identity for the statistical rounding-error model.

This is the Chapter 4 Section 4.5 kernel: if addition errors are zero-mean and
pairwise uncorrelated, all cross terms in the mean-square running error vanish,
leaving only the deterministic squared intermediate-sum weights. -/
theorem expectation_weighted_sum_sq_eq_sum_weight_sq_second_moments
    (h : StatisticalRoundingErrorModel P eps u) (w : Fin n → ℝ) :
    P.expectationReal
        (fun ω => (statisticalWeightedRoundingErrorSum w eps ω) ^ 2) =
      ∑ i, (w i) ^ 2 *
        P.expectationReal (fun ω => (eps i ω) ^ 2) := by
  classical
  have hpoint :
      ∀ ω, (statisticalWeightedRoundingErrorSum w eps ω) ^ 2 =
        ∑ i, ∑ j, (w i * eps i ω) * (w j * eps j ω) := by
    intro ω
    unfold statisticalWeightedRoundingErrorSum
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    P.expectationReal
        (fun ω => (statisticalWeightedRoundingErrorSum w eps ω) ^ 2)
        = P.expectationReal
            (fun ω => ∑ i, ∑ j,
              (w i * eps i ω) * (w j * eps j ω)) := by
            apply congrArg
            funext ω
            exact hpoint ω
    _ = ∑ i, P.expectationReal
            (fun ω => ∑ j, (w i * eps i ω) * (w j * eps j ω)) := by
            rw [P.expectationReal_sum]
    _ = ∑ i, ∑ j, P.expectationReal
            (fun ω => (w i * eps i ω) * (w j * eps j ω)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [P.expectationReal_sum]
    _ = ∑ i, P.expectationReal (fun ω => (w i * eps i ω) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_eq_single i]
            · apply congrArg
              funext ω
              ring
            · intro j _ hji
              calc
                P.expectationReal
                    (fun ω => (w i * eps i ω) * (w j * eps j ω))
                    = P.expectationReal
                        (fun ω => (w i * w j) * (eps i ω * eps j ω)) := by
                        apply congrArg
                        funext ω
                        ring
                _ = (w i * w j) *
                      P.expectationReal
                        (fun ω => eps i ω * eps j ω) := by
                        exact P.expectationReal_const_mul
                          (fun ω => eps i ω * eps j ω) (w i * w j)
                _ = 0 := by
                        rw [h.pairwise_uncorrelated i j (Ne.symm hji)]
                        ring
            · intro hi
              exact False.elim (hi (Finset.mem_univ i))
    _ = ∑ i, (w i) ^ 2 *
          P.expectationReal (fun ω => (eps i ω) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              P.expectationReal (fun ω => (w i * eps i ω) ^ 2)
                  = P.expectationReal
                      (fun ω => (w i) ^ 2 * (eps i ω) ^ 2) := by
                      apply congrArg
                      funext ω
                      ring
              _ = (w i) ^ 2 *
                    P.expectationReal (fun ω => (eps i ω) ^ 2) := by
                      exact P.expectationReal_const_mul
                        (fun ω => (eps i ω) ^ 2) ((w i) ^ 2)

theorem expectation_sum_sq_le_card_mul_unit_sq
    (h : StatisticalRoundingErrorModel P eps u) :
    P.expectationReal (fun ω => (statisticalRoundingErrorSum eps ω) ^ 2) ≤
      (n : ℝ) * u ^ 2 := by
  classical
  calc
    P.expectationReal (fun ω => (statisticalRoundingErrorSum eps ω) ^ 2)
        = ∑ i, P.expectationReal (fun ω => (eps i ω) ^ 2) :=
            h.expectation_sum_sq_eq_sum_second_moments
    _ ≤ ∑ _i : Fin n, u ^ 2 :=
            Finset.sum_le_sum (fun i _ => h.second_moment_le i)
    _ = (n : ℝ) * u ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul]

/-- Weighted mean-square bound for deterministic intermediate-sum weights.

If every local addition error has second moment at most `u^2`, the weighted
absolute-error model has mean square at most `u^2 * sum_i w_i^2`. -/
theorem expectation_weighted_sum_sq_le_weight_sq_mul_unit_sq
    (h : StatisticalRoundingErrorModel P eps u) (w : Fin n → ℝ) :
    P.expectationReal
        (fun ω => (statisticalWeightedRoundingErrorSum w eps ω) ^ 2) ≤
      (∑ i, (w i) ^ 2) * u ^ 2 := by
  classical
  calc
    P.expectationReal
        (fun ω => (statisticalWeightedRoundingErrorSum w eps ω) ^ 2)
        = ∑ i, (w i) ^ 2 *
            P.expectationReal (fun ω => (eps i ω) ^ 2) :=
            h.expectation_weighted_sum_sq_eq_sum_weight_sq_second_moments w
    _ ≤ ∑ i, (w i) ^ 2 * u ^ 2 :=
            Finset.sum_le_sum (fun i _ =>
              mul_le_mul_of_nonneg_left (h.second_moment_le i)
                (sq_nonneg (w i)))
    _ = (∑ i, (w i) ^ 2) * u ^ 2 := by
            rw [Finset.sum_mul]

/-- Higham §2.6's square-root rule in finite second-moment form: under the
visible statistical rounding-error model, the RMS accumulated error is at most
`sqrt n * u`. -/
theorem rms_sum_le_sqrt_card_mul_unit
    (h : StatisticalRoundingErrorModel P eps u) (hu : 0 ≤ u) :
    Real.sqrt (P.expectationReal
      (fun ω => (statisticalRoundingErrorSum eps ω) ^ 2)) ≤
        Real.sqrt (n : ℝ) * u := by
  have hsecond := h.expectation_sum_sq_le_card_mul_unit_sq
  have hsqrt :=
    Real.sqrt_le_sqrt hsecond
  calc
    Real.sqrt (P.expectationReal
        (fun ω => (statisticalRoundingErrorSum eps ω) ^ 2))
        ≤ Real.sqrt ((n : ℝ) * u ^ 2) := hsqrt
    _ = Real.sqrt (n : ℝ) * u := by
        rw [Real.sqrt_mul (Nat.cast_nonneg n),
          Real.sqrt_sq_eq_abs, abs_of_nonneg hu]

/-- RMS form of the weighted mean-square estimate. -/
theorem rms_weighted_sum_le_sqrt_weight_sq_mul_unit
    (h : StatisticalRoundingErrorModel P eps u) (w : Fin n → ℝ)
    (hu : 0 ≤ u) :
    Real.sqrt (P.expectationReal
      (fun ω => (statisticalWeightedRoundingErrorSum w eps ω) ^ 2)) ≤
        Real.sqrt (∑ i, (w i) ^ 2) * u := by
  have hsecond := h.expectation_weighted_sum_sq_le_weight_sq_mul_unit_sq w
  have hsqrt := Real.sqrt_le_sqrt hsecond
  have hw_nonneg : 0 ≤ ∑ i, (w i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (w i))
  calc
    Real.sqrt (P.expectationReal
        (fun ω => (statisticalWeightedRoundingErrorSum w eps ω) ^ 2))
        ≤ Real.sqrt ((∑ i, (w i) ^ 2) * u ^ 2) := hsqrt
    _ = Real.sqrt (∑ i, (w i) ^ 2) * u := by
        rw [Real.sqrt_mul hw_nonneg, Real.sqrt_sq_eq_abs,
          abs_of_nonneg hu]

end StatisticalRoundingErrorModel

/-! ## Higham Chapter 4, Table 4.1 constants -/

/-- The two nonnegative-input distributions tabulated in Higham Table 4.1. -/
inductive Table41Distribution
  | uniform
  | exponential
  deriving DecidableEq

/-- The five summation-method columns tabulated in Higham Table 4.1. -/
inductive Table41Method
  | recursiveIncreasing
  | recursiveRandom
  | recursiveDecreasing
  | insertion
  | pairwise
  deriving DecidableEq

/-- The printed constants in Higham Table 4.1, encoded as exact rationals.

The full displayed estimate is
`constant * mu^2 * n^exponent * sigma^2`, with exponent `3` for recursive
summation and exponent `2` for insertion/pairwise summation. -/
def table41MeanSquareConstant :
    Table41Distribution → Table41Method → ℝ
  | Table41Distribution.uniform, Table41Method.recursiveIncreasing => 1 / 5
  | Table41Distribution.uniform, Table41Method.recursiveRandom => 33 / 100
  | Table41Distribution.uniform, Table41Method.recursiveDecreasing => 53 / 100
  | Table41Distribution.uniform, Table41Method.insertion => 13 / 5
  | Table41Distribution.uniform, Table41Method.pairwise => 27 / 10
  | Table41Distribution.exponential, Table41Method.recursiveIncreasing =>
      13 / 100
  | Table41Distribution.exponential, Table41Method.recursiveRandom => 33 / 100
  | Table41Distribution.exponential, Table41Method.recursiveDecreasing =>
      63 / 100
  | Table41Distribution.exponential, Table41Method.insertion => 13 / 5
  | Table41Distribution.exponential, Table41Method.pairwise => 4

/-- The power of `n` displayed in Higham Table 4.1. -/
def table41NExponent : Table41Method → ℕ
  | Table41Method.recursiveIncreasing => 3
  | Table41Method.recursiveRandom => 3
  | Table41Method.recursiveDecreasing => 3
  | Table41Method.insertion => 2
  | Table41Method.pairwise => 2

/-- Exact source-shaped Table 4.1 mean-square estimate expression. -/
noncomputable def table41MeanSquareEstimate
    (dist : Table41Distribution) (method : Table41Method)
    (mu : ℝ) (n : ℕ) (sigma : ℝ) : ℝ :=
  table41MeanSquareConstant dist method *
    mu ^ 2 * (n : ℝ) ^ table41NExponent method * sigma ^ 2

/-- The common positive scale multiplying Table 4.1 constants when two methods
have the same displayed power of `n`. -/
theorem table41MeanSquareScale_pos
    (mu sigma : ℝ) {n k : ℕ}
    (hmu : mu ≠ 0) (hn : 0 < n) (hsigma : sigma ≠ 0) :
    0 < mu ^ 2 * (n : ℝ) ^ k * sigma ^ 2 := by
  have hmu_sq : 0 < mu ^ 2 := sq_pos_of_ne_zero hmu
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn_pow : 0 < (n : ℝ) ^ k := pow_pos hn_real k
  have hsigma_sq : 0 < sigma ^ 2 := sq_pos_of_ne_zero hsigma
  exact mul_pos (mul_pos hmu_sq hn_pow) hsigma_sq

/-- Table 4.1: for uniformly distributed nonnegative inputs, recursive
summation constants rank increasing, then random, then decreasing. -/
theorem table41_recursive_constants_rank_uniform :
    table41MeanSquareConstant Table41Distribution.uniform
        Table41Method.recursiveIncreasing <
      table41MeanSquareConstant Table41Distribution.uniform
        Table41Method.recursiveRandom ∧
    table41MeanSquareConstant Table41Distribution.uniform
        Table41Method.recursiveRandom <
      table41MeanSquareConstant Table41Distribution.uniform
        Table41Method.recursiveDecreasing := by
  norm_num [table41MeanSquareConstant]

/-- Table 4.1: for exponentially distributed nonnegative inputs, recursive
summation constants rank increasing, then random, then decreasing. -/
theorem table41_recursive_constants_rank_exponential :
    table41MeanSquareConstant Table41Distribution.exponential
        Table41Method.recursiveIncreasing <
      table41MeanSquareConstant Table41Distribution.exponential
        Table41Method.recursiveRandom ∧
    table41MeanSquareConstant Table41Distribution.exponential
        Table41Method.recursiveRandom <
      table41MeanSquareConstant Table41Distribution.exponential
        Table41Method.recursiveDecreasing := by
  norm_num [table41MeanSquareConstant]

/-- Table 4.1: insertion has the smaller displayed constant than pairwise
summation for uniformly distributed nonnegative inputs. -/
theorem table41_insertion_constant_lt_pairwise_uniform :
    table41MeanSquareConstant Table41Distribution.uniform
        Table41Method.insertion <
      table41MeanSquareConstant Table41Distribution.uniform
        Table41Method.pairwise := by
  norm_num [table41MeanSquareConstant]

/-- Table 4.1: insertion has the smaller displayed constant than pairwise
summation for exponentially distributed nonnegative inputs. -/
theorem table41_insertion_constant_lt_pairwise_exponential :
    table41MeanSquareConstant Table41Distribution.exponential
        Table41Method.insertion <
      table41MeanSquareConstant Table41Distribution.exponential
        Table41Method.pairwise := by
  norm_num [table41MeanSquareConstant]

/-- Table 4.1: all recursive-summation columns have `n^3` scaling. -/
theorem table41_recursive_exponents_eq_three :
    table41NExponent Table41Method.recursiveIncreasing = 3 ∧
    table41NExponent Table41Method.recursiveRandom = 3 ∧
    table41NExponent Table41Method.recursiveDecreasing = 3 := by
  simp [table41NExponent]

/-- Table 4.1: insertion and pairwise summation have `n^2` scaling. -/
theorem table41_insertion_pairwise_exponents_eq_two :
    table41NExponent Table41Method.insertion = 2 ∧
    table41NExponent Table41Method.pairwise = 2 := by
  simp [table41NExponent]

/-- Table 4.1 full estimate ranking for uniformly distributed nonnegative
inputs: recursive summation in increasing order has the smallest displayed
recursive estimate, random order is next, and decreasing order is largest. -/
theorem table41_recursive_estimates_rank_uniform
    (mu sigma : ℝ) {n : ℕ}
    (hmu : mu ≠ 0) (hn : 0 < n) (hsigma : sigma ≠ 0) :
    table41MeanSquareEstimate Table41Distribution.uniform
        Table41Method.recursiveIncreasing mu n sigma <
      table41MeanSquareEstimate Table41Distribution.uniform
        Table41Method.recursiveRandom mu n sigma ∧
    table41MeanSquareEstimate Table41Distribution.uniform
        Table41Method.recursiveRandom mu n sigma <
      table41MeanSquareEstimate Table41Distribution.uniform
        Table41Method.recursiveDecreasing mu n sigma := by
  have hscale :
      0 < mu ^ 2 * (n : ℝ) ^ 3 * sigma ^ 2 :=
    table41MeanSquareScale_pos mu sigma hmu hn hsigma
  constructor
  · have h :=
      mul_lt_mul_of_pos_right table41_recursive_constants_rank_uniform.1 hscale
    simpa [table41MeanSquareEstimate, table41MeanSquareConstant,
      table41NExponent, mul_assoc] using h
  · have h :=
      mul_lt_mul_of_pos_right table41_recursive_constants_rank_uniform.2 hscale
    simpa [table41MeanSquareEstimate, table41MeanSquareConstant,
      table41NExponent, mul_assoc] using h

/-- Table 4.1 full estimate ranking for exponentially distributed nonnegative
inputs: recursive summation in increasing order has the smallest displayed
recursive estimate, random order is next, and decreasing order is largest. -/
theorem table41_recursive_estimates_rank_exponential
    (mu sigma : ℝ) {n : ℕ}
    (hmu : mu ≠ 0) (hn : 0 < n) (hsigma : sigma ≠ 0) :
    table41MeanSquareEstimate Table41Distribution.exponential
        Table41Method.recursiveIncreasing mu n sigma <
      table41MeanSquareEstimate Table41Distribution.exponential
        Table41Method.recursiveRandom mu n sigma ∧
    table41MeanSquareEstimate Table41Distribution.exponential
        Table41Method.recursiveRandom mu n sigma <
      table41MeanSquareEstimate Table41Distribution.exponential
        Table41Method.recursiveDecreasing mu n sigma := by
  have hscale :
      0 < mu ^ 2 * (n : ℝ) ^ 3 * sigma ^ 2 :=
    table41MeanSquareScale_pos mu sigma hmu hn hsigma
  constructor
  · have h :=
      mul_lt_mul_of_pos_right table41_recursive_constants_rank_exponential.1
        hscale
    simpa [table41MeanSquareEstimate, table41MeanSquareConstant,
      table41NExponent, mul_assoc] using h
  · have h :=
      mul_lt_mul_of_pos_right table41_recursive_constants_rank_exponential.2
        hscale
    simpa [table41MeanSquareEstimate, table41MeanSquareConstant,
      table41NExponent, mul_assoc] using h

/-- Table 4.1 full estimate comparison: for uniformly distributed nonnegative
inputs, insertion has the smaller displayed estimate than pairwise summation. -/
theorem table41_insertion_estimate_lt_pairwise_uniform
    (mu sigma : ℝ) {n : ℕ}
    (hmu : mu ≠ 0) (hn : 0 < n) (hsigma : sigma ≠ 0) :
    table41MeanSquareEstimate Table41Distribution.uniform
        Table41Method.insertion mu n sigma <
      table41MeanSquareEstimate Table41Distribution.uniform
        Table41Method.pairwise mu n sigma := by
  have hscale :
      0 < mu ^ 2 * (n : ℝ) ^ 2 * sigma ^ 2 :=
    table41MeanSquareScale_pos mu sigma hmu hn hsigma
  have h :=
    mul_lt_mul_of_pos_right table41_insertion_constant_lt_pairwise_uniform
      hscale
  simpa [table41MeanSquareEstimate, table41MeanSquareConstant,
    table41NExponent, mul_assoc] using h

/-- Table 4.1 full estimate comparison: for exponentially distributed
nonnegative inputs, insertion has the smaller displayed estimate than pairwise
summation. -/
theorem table41_insertion_estimate_lt_pairwise_exponential
    (mu sigma : ℝ) {n : ℕ}
    (hmu : mu ≠ 0) (hn : 0 < n) (hsigma : sigma ≠ 0) :
    table41MeanSquareEstimate Table41Distribution.exponential
        Table41Method.insertion mu n sigma <
      table41MeanSquareEstimate Table41Distribution.exponential
        Table41Method.pairwise mu n sigma := by
  have hscale :
      0 < mu ^ 2 * (n : ℝ) ^ 2 * sigma ^ 2 :=
    table41MeanSquareScale_pos mu sigma hmu hn hsigma
  have h :=
    mul_lt_mul_of_pos_right table41_insertion_constant_lt_pairwise_exponential
      hscale
  simpa [table41MeanSquareEstimate, table41MeanSquareConstant,
    table41NExponent, mul_assoc] using h

end

end NumStability
