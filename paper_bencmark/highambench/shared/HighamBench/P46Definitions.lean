import Mathlib

open scoped BigOperators

namespace HighamBench

abbrev P46Vector (n : ℕ) := Fin n → ℝ
abbrev P46Matrix (n : ℕ) := Fin n → Fin n → ℝ

noncomputable def p46MatVec {n : ℕ}
    (A : P46Matrix n) (x : P46Vector n) : P46Vector n :=
  fun i => ∑ j : Fin n, A i j * x j

/-- The perturbed iterate and recursively updated residual formulas (8)-(9)
from P46. -/
structure P46ResidualRecurrence (n : ℕ) where
  A : P46Matrix n
  b : P46Vector n
  x : ℕ → P46Vector n
  r : ℕ → P46Vector n
  p : ℕ → P46Vector n
  alpha : ℕ → ℝ
  xi : ℕ → P46Vector n
  eta : ℕ → P46Vector n
  stepX : ∀ k,
    x (k + 1) = fun i => x k i + alpha k * p k i + xi (k + 1) i
  stepR : ∀ k,
    r (k + 1) = fun i =>
      r k i - alpha k * p46MatVec A (p k) i + eta (k + 1) i

/-- Difference between the true residual and the recursively updated residual. -/
noncomputable def P46ResidualRecurrence.gap {n : ℕ}
    (process : P46ResidualRecurrence n) (k : ℕ) : P46Vector n :=
  fun i => process.b i - p46MatVec process.A (process.x k) i - process.r k i

end HighamBench
