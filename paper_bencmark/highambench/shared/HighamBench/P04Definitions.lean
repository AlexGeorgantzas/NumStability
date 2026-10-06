import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HighamBench

open scoped BigOperators

noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p04BlockFmaCoeff
    (uFma u : ℝ) (q n : ℕ) : ℝ :=
  gamma uFma q + gamma u n + gamma uFma q * gamma u n

noncomputable def p04EffectiveFmaRoundoff
    (uBar uFma uOut : ℝ) : ℝ :=
  if uFma < uOut then uOut
  else if uFma ≤ uBar then 0
  else uFma

inductive P04BlockEvaluationOrder where
  | leftToRight
  | rightToLeft
  | other (code : ℕ)
  deriving DecidableEq

noncomputable def p04BlockedDot {q b : ℕ}
    (x y : Fin q → Fin b → ℝ) : ℝ :=
  ∑ k : Fin q, ∑ j : Fin b, x k j * y k j

noncomputable def p04BlockedAbsDot {q b : ℕ}
    (x y : Fin q → Fin b → ℝ) : ℝ :=
  ∑ k : Fin q, ∑ j : Fin b, |x k j| * |y k j|

noncomputable def p04ErrorAt {q : ℕ} (error : Fin q → ℝ) (k : ℕ) : ℝ :=
  if h : k < q then error ⟨k, h⟩ else 0

noncomputable def p04InclusiveErrorProduct {q : ℕ}
    (error : Fin q → ℝ) (k : Fin q) : ℝ :=
  ∏ l ∈ Finset.Ico k.val q, (1 + p04ErrorAt error l)

noncomputable def p04StrictErrorProduct {q : ℕ}
    (error : Fin q → ℝ) (k : Fin q) : ℝ :=
  ∏ l ∈ Finset.Ico (k.val + 1) q, (1 + p04ErrorAt error l)

structure P04BlockFmaDotRun (n b q : ℕ) where
  dimension_pos : 0 < n
  block_size_pos : 0 < b
  block_count_pos : 0 < q
  dimension_eq : n = q * b
  x : Fin q → Fin b → ℝ
  y : Fin q → Fin b → ℝ
  uBar : ℝ
  uFma : ℝ
  uOut : ℝ
  uBar_nonneg : 0 ≤ uBar
  uFma_nonneg : 0 ≤ uFma
  uOut_nonneg : 0 ≤ uOut
  uBar_le_uFma : uBar ≤ uFma
  effective_gamma_valid :
    GammaValid (p04EffectiveFmaRoundoff uBar uFma uOut) q
  internal_gamma_valid : GammaValid uBar n
  order : P04BlockEvaluationOrder
  state : ℕ → ℝ
  carryTheta : Fin q → ℝ
  termTheta : Fin q → Fin b → ℝ
  delta : Fin q → ℝ
  state_zero : state 0 = 0
  state_step : ∀ k : Fin q,
    state (k.val + 1) =
      (state k.val * (1 + carryTheta k) +
        ∑ j : Fin b, x k j * y k j * (1 + termTheta k j)) *
          (1 + delta k)
  delta_bound : ∀ k,
    |delta k| ≤ p04EffectiveFmaRoundoff uBar uFma uOut
  carry_theta_bound : ∀ k, |carryTheta k| ≤ gamma uBar b
  term_theta_bound : ∀ k j,
    |termTheta k j| ≤ gamma uBar (if k.val = 0 then b else b + 1)
  right_to_left_carry_bound :
    order = P04BlockEvaluationOrder.rightToLeft →
      ∀ k, |carryTheta k| ≤ gamma uBar 1
  innerPathError : Fin q → Fin b → Fin n → ℝ
  inner_path_error_bound : ∀ k j r, |innerPathError k j r| ≤ uBar
  inner_path_factor : ∀ k j,
    (∏ r : Fin n, (1 + innerPathError k j r)) =
      (1 + termTheta k j) * p04StrictErrorProduct carryTheta k
  rightToLeftPathError : Fin q → Fin b → Fin (q + b - 1) → ℝ
  right_to_left_path_error_bound :
    order = P04BlockEvaluationOrder.rightToLeft →
      ∀ k j r, |rightToLeftPathError k j r| ≤ uBar
  right_to_left_path_factor :
    order = P04BlockEvaluationOrder.rightToLeft →
      ∀ k j,
        (∏ r : Fin (q + b - 1),
          (1 + rightToLeftPathError k j r)) =
            (1 + termTheta k j) *
              p04StrictErrorProduct carryTheta k

noncomputable def P04BlockFmaDotRun.computed
    {n b q : ℕ} (run : P04BlockFmaDotRun n b q) : ℝ :=
  run.state q

end HighamBench
