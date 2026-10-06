import Mathlib

namespace HighamBench

open scoped BigOperators

/-! Fasi–Higham–Lopez–Mary–Mikaitis, two-word matrix product, one entry. -/

structure P67FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)

noncomputable def p67Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P67GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p67RecursiveSum (fp : P67FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0

noncomputable def p67BlockDot (fp : P67FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n' (fun acc i => fp.fl_add acc
        (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

def p67AWord {n : ℕ} (a₀ a₁ : Fin n → ℝ) (t : Fin 4) : Fin n → ℝ :=
  if t.val < 2 then a₀ else a₁

def p67BWord {n : ℕ} (b₀ b₁ : Fin n → ℝ) (t : Fin 4) : Fin n → ℝ :=
  if t.val % 2 = 0 then b₀ else b₁

noncomputable def p67MultiwordDot (fp : P67FPModel) (n : ℕ)
    (a₀ a₁ b₀ b₁ : Fin n → ℝ) : ℝ :=
  p67RecursiveSum fp 4 (fun t =>
    p67BlockDot fp n (p67AWord a₀ a₁ t) (p67BWord b₀ b₁ t))

/-- One entry of a p-word product, with an enumeration of all p² word pairs. -/
noncomputable def p67MultiwordDotMany (fp : P67FPModel) (p n : ℕ)
    (pairs : Fin (p * p) ≃ Fin p × Fin p)
    (a b : Fin p → Fin n → ℝ) : ℝ :=
  p67RecursiveSum fp (p * p) (fun t =>
    p67BlockDot fp n (a (pairs t).1) (b (pairs t).2))

end HighamBench
