import Mathlib

open scoped BigOperators

namespace HighamBench

abbrev P47Vector (n : ℕ) := Fin n → ℝ
abbrev P47Matrix (n : ℕ) := Fin n → Fin n → ℝ

noncomputable def p47MatMul {n : ℕ}
    (A B : P47Matrix n) : P47Matrix n :=
  fun i j => ∑ k : Fin n, A i k * B k j

def p47Id (n : ℕ) : P47Matrix n :=
  fun i j => if i = j then 1 else 0

/-- The column-residual matrix `AM-I` used throughout P47, Section 3. -/
noncomputable def p47ResidualMatrix {n : ℕ}
    (A M : P47Matrix n) : P47Matrix n :=
  fun i j => p47MatMul A M i j - p47Id n i j

noncomputable def p47VecNorm {n : ℕ} (x : P47Vector n) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

noncomputable def p47FrobNorm {n : ℕ} (A : P47Matrix n) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)

end HighamBench
