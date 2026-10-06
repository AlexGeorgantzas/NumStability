import Mathlib

namespace HighamBench

open scoped BigOperators

/-! Paper-local exact objects for Proposition 6.2.  A lower-triangular
Cholesky factor determines the diagonal entries and determinant through its
row energies and squared diagonal entries. -/

/-- The square of a Cholesky diagonal entry. -/
noncomputable def p35DiagSquare {n : ℕ} (L : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  (L i i) ^ 2

/-- The diagonal entry of `L * Lᵀ`, written as a lower-triangular row energy. -/
noncomputable def p35RowEnergy {n : ℕ} (L : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  p35DiagSquare L i +
    ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val), (L i k) ^ 2

/-- The Hadamard measure in Cholesky coordinates. -/
noncomputable def p35HadamardMeasure {n : ℕ} (L : Fin n → Fin n → ℝ) : ℝ :=
  (∏ i, p35DiagSquare L i) / ∏ i, p35RowEnergy L i

/-- A lower Cholesky factor is diagonal when every entry below its diagonal vanishes. -/
def p35IsDiagonalCholesky {n : ℕ} (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ i k, k.val < i.val → L i k = 0

/-- Row scaling of a lower Cholesky factor by a diagonal matrix. -/
noncomputable def p35ScaleRows {n : ℕ} (s : Fin n → ℝ)
    (L : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i k ↦ s i * L i k

end HighamBench
