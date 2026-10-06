import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace HighamBench

/-- The exact two-sided diagonal scaling used by P44, Algorithms 2.3--2.5. -/
def p44TwoSidedScale {n : ℕ}
    (r s : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => r i * A i j * s j

/-- The affine rank-one transformation `C = α A + β e eᵀ` in P44,
equation (5.1), written entrywise. -/
def p44RankOneScale {n : ℕ}
    (α β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => α * A i j + β

end HighamBench
