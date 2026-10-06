import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace HighamBench

/-- The off-diagonal sign condition used in the paper's definition of an M-matrix. -/
def p38OffDiagonalNonpositive {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, i ≠ j → A i j ≤ 0

/-- A prescribed set of matrix entries is zero. -/
def p38HasZerosAt {n : ℕ}
    (P : Set (Fin n × Fin n)) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, (i, j) ∈ P → A i j = 0

end HighamBench
