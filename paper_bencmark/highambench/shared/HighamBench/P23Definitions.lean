import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

namespace HighamBench

open scoped BigOperators

/-- The standard relative-error model used in equations (2.1)--(2.2). -/
structure P23FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)

abbrev P23Matrix (n : ℕ) := Fin n → Fin n → ℝ

/-- Exact matrix multiplication in the paper's real-arithmetic analysis. -/
noncomputable def p23MatMul {n : ℕ}
    (A B : P23Matrix n) : P23Matrix n :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- Componentwise absolute value of a matrix. -/
noncomputable def p23AbsMatrix {n : ℕ}
    (A : P23Matrix n) : P23Matrix n :=
  fun i j => |A i j|

/-- The accumulated rounding-error constant from equation (2.2). -/
noncomputable def p23Gamma (u : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) * u) / (1 - (k : ℝ) * u)

/-- The usual guard under which `p23Gamma` is valid. -/
def P23GammaValid (u : ℝ) (k : ℕ) : Prop :=
  (k : ℝ) * u < 1

/-- Sequentially accumulated floating-point dot product. -/
noncomputable def p23RoundedDotProduct (fp : P23FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

/-- Matrix multiplication computed entry by entry with rounded dot products. -/
noncomputable def p23RoundedMatMul (fp : P23FPModel) {n : ℕ}
    (A B : P23Matrix n) : P23Matrix n :=
  fun i j => p23RoundedDotProduct fp n (A i) (fun k => B k j)

/-- Starting from `X`, perform `k` further exact multiplications by `X`. -/
noncomputable def p23PowerSteps {n : ℕ} (X : P23Matrix n) :
    ℕ → P23Matrix n
  | 0 => X
  | k + 1 => p23MatMul (p23PowerSteps X k) X

/-- Starting from `X`, perform `k` further rounded multiplications by `X`. -/
noncomputable def p23RoundedPowerSteps (fp : P23FPModel) {n : ℕ}
    (X : P23Matrix n) : ℕ → P23Matrix n
  | 0 => X
  | k + 1 => p23RoundedMatMul fp (p23RoundedPowerSteps fp X k) X

end HighamBench
