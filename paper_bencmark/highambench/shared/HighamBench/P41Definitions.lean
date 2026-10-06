import Mathlib

open scoped BigOperators

namespace HighamBench

/-- The nilpotent shift matrix `J` from Theorem 2.1. -/
noncomputable def p41Shift (p : ℕ) : Matrix (Fin p) (Fin p) ℂ :=
  fun i j => if j.val = i.val + 1 then 1 else 0

/-- The augmented block matrix `[A W; 0 J]` from Theorem 2.1. -/
noncomputable def p41Augmented {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ) :
    Matrix (Fin n ⊕ Fin p) (Fin n ⊕ Fin p) ℂ :=
  Matrix.fromBlocks A W 0 (p41Shift p)

/-- The matrix phi-function `phi_ell(A) = sum_k A^k / (k + ell)!`. -/
noncomputable def p41Phi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) • A ^ k

/-- The source column `w_(j-r+1)`, using zero-based indices. -/
noncomputable def p41ReverseColumn {n p : ℕ}
    (W : Matrix (Fin n) (Fin p) ℂ) (j : Fin p) (r : Fin (j.val + 1)) :
    Fin n → ℂ :=
  fun i => W i ⟨j.val - r.val,
    (Nat.sub_le j.val r.val).trans_lt j.isLt⟩

end HighamBench
