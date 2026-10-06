import Mathlib

namespace HighamBench

open scoped BigOperators

/-! Castaldo–Whaley–Chronopoulos, two-level superblock dot product. -/

structure P66FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)

noncomputable def p66Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P66GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p66RecursiveSum (fp : P66FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0

noncomputable def p66BlockDot (fp : P66FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n' (fun acc i => fp.fl_add acc
        (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p66SuperblockDot (fp : P66FPModel) (b : ℕ)
    (x y : Fin b → Fin b → ℝ) : ℝ :=
  p66RecursiveSum fp b (fun i => p66BlockDot fp b (x i) (y i))

/-- Proposition 3.1's two-level, b-by-b superblock summation. -/
noncomputable def p66SuperblockSum (fp : P66FPModel) (b : ℕ)
    (x : Fin b → Fin b → ℝ) : ℝ :=
  p66RecursiveSum fp b (fun i => p66RecursiveSum fp b (x i))

end HighamBench
