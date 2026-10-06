import Mathlib

namespace HighamBench

open scoped BigOperators

/-! Paper-local two-precision residual computation from Carson and Higham, Section 2. -/

structure P63FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_sub : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_sub x y = (x - y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)
  model_div : ∀ x y : ℝ, y ≠ 0 → ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_div x y = (x / y) * (1 + δ)

abbrev P63Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

noncomputable def p63Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P63GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p63MatMul {m n p : ℕ}
    (A : P63Matrix m n) (B : P63Matrix n p) : P63Matrix m p :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def p63RoundedDotProduct (fp : P63FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p63RoundedMatMul (fp : P63FPModel) {m n p : ℕ}
    (A : P63Matrix m n) (B : P63Matrix n p) : P63Matrix m p :=
  fun i j => p63RoundedDotProduct fp n (A i) (fun k => B k j)

noncomputable def p63RoundedMatVec (fp : P63FPModel) (n : ℕ)
    (A : P63Matrix n n) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => p63RoundedDotProduct fp n (A i) x

noncomputable def p63HighResidual (fp : P63FPModel) (n : ℕ)
    (A : P63Matrix n n) (x b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fp.fl_sub (b i) (p63RoundedMatVec fp n A x i)

noncomputable def p63StoredResidual (fpHi fpLo : P63FPModel) (n : ℕ)
    (A : P63Matrix n n) (x b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fpLo.fl_mul (p63HighResidual fpHi n A x b i) 1

end HighamBench
