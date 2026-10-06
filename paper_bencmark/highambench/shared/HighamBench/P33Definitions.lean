import Mathlib

namespace HighamBench

open scoped BigOperators

/-- A paper-local relative-error model for the arithmetic used to form a residual. -/
structure P33FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ delta : ℝ,
    |delta| ≤ u ∧ fl_add x y = (x + y) * (1 + delta)
  model_sub : ∀ x y : ℝ, ∃ delta : ℝ,
    |delta| ≤ u ∧ fl_sub x y = (x - y) * (1 + delta)
  model_mul : ∀ x y : ℝ, ∃ delta : ℝ,
    |delta| ≤ u ∧ fl_mul x y = (x * y) * (1 + delta)
  model_div : ∀ x y : ℝ, y ≠ 0 → ∃ delta : ℝ,
    |delta| ≤ u ∧ fl_div x y = (x / y) * (1 + delta)

noncomputable def p33Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P33GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

/-- The rounded dot product over the stored nonzeros of one sparse row. -/
noncomputable def p33RoundedSparseRowProduct
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) : ℝ :=
  match s with
  | 0 => 0
  | s' + 1 =>
      Fin.foldl s'
        (fun acc j ↦ fp.fl_add acc (fp.fl_mul (a j.succ) (x j.succ)))
        (fp.fl_mul (a 0) (x 0))

/-- The computed residual component `fl(b_i - fl(a_i x))`. -/
noncomputable def p33RoundedResidual
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ) : ℝ :=
  fp.fl_sub b (p33RoundedSparseRowProduct fp s a x)

noncomputable def p33ExactResidual
    (s : ℕ) (a x : Fin s → ℝ) (b : ℝ) : ℝ :=
  b - ∑ j : Fin s, a j * x j

/-- The sparse-row residual error envelope stated at the end of Section 2.2. -/
noncomputable def p33ResidualErrorMajorant
    (fp : P33FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ) : ℝ :=
  p33Gamma fp.u (s + 1) * (|b| + ∑ j : Fin s, |a j| * |x j|)

end HighamBench
