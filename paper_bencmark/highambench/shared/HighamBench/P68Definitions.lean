import Mathlib

namespace HighamBench

open scoped BigOperators

/-! Graillat–Jézéquel–Mary–Molina, two-bucket one-row adaptive SpMV. -/

structure P68FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)

noncomputable def p68Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P68GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p68RecursiveSum (fp : P68FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0

noncomputable def p68BlockDot (fp : P68FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n' (fun acc i => fp.fl_add acc
        (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p68AdaptiveRow (fp₁ fp₂ : P68FPModel) (n : ℕ)
    (a₁ x₁ a₂ x₂ : Fin n → ℝ) : ℝ :=
  p68RecursiveSum fp₁ 2 (Fin.cons
    (p68BlockDot fp₁ n a₁ x₁)
    (fun _ => p68BlockDot fp₂ n a₂ x₂))

/-- Algorithm 3.1 for a variable number of buckets in one sparse row. -/
noncomputable def p68AdaptiveRowMany (q n : ℕ) (outer : P68FPModel)
    (bucket : Fin q → P68FPModel)
    (a x : Fin q → Fin n → ℝ) : ℝ :=
  p68RecursiveSum outer q
    (fun k => p68BlockDot (bucket k) n (a k) (x k))

end HighamBench
