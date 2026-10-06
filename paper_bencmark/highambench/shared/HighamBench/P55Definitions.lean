import Mathlib

namespace HighamBench

abbrev P55Vector (k : ℕ) := Fin k → ℝ
abbrev P55Matrix (k : ℕ) := Matrix (Fin k) (Fin k) ℝ

def p55StrictLower {k : ℕ} (M : P55Matrix k) : Prop :=
  ∀ i j, i ≤ j → M i j = 0

def p55StrictUpper {k : ℕ} (M : P55Matrix k) : Prop :=
  ∀ i j, j ≤ i → M i j = 0

noncomputable def p55Outer {k : ℕ}
    (u v : P55Vector k) : P55Matrix k :=
  Matrix.vecMulVec u v

def p55LastBasis (k : ℕ) : P55Vector (k + 1) :=
  fun i => if i = Fin.last k then 1 else 0

end HighamBench
