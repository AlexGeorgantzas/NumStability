import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Analysis TestMatrices Companion Basic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Higham, 2nd ed., Section 28.6, pp. 522-523: the companion matrix for
coefficients `a₀,...,aₙ₋₁`.  A natural-indexed coefficient function avoids a
spurious nonempty-dimension hypothesis in the definition. -/
noncomputable def companionMatrix (n : ℕ) (a : ℕ → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    if i.val = 0 then a (n - 1 - j.val)
    else if i.val = j.val + 1 then 1
    else 0

/-- The power vector printed on p. 523, translated to zero-based indices. -/
noncomputable def companionEigenvector (n : ℕ) (z : ℂ) : Fin n → ℂ :=
  fun i => z ^ (n - 1 - i.val)

/-- Higham, Section 28.6, p. 523: if `z` satisfies the monic polynomial root
equation associated with the displayed companion matrix, then
`[z^(n-1), z^(n-2), ..., z, 1]ᵀ` is an eigenvector with eigenvalue `z`.
The hypothesis is the polynomial equation, not the eigenvector conclusion. -/
theorem companionMatrix_mulVec_companionEigenvector
    {n : ℕ} (a : ℕ → ℂ) (z : ℂ)
    (hroot : (∑ j : Fin n, a (n - 1 - j.val) * z ^ (n - 1 - j.val)) = z ^ n) :
    Matrix.mulVec (companionMatrix n a) (companionEigenvector n z) =
      z • companionEigenvector n z := by
  funext i
  by_cases hi : i.val = 0
  · simp only [Matrix.mulVec, dotProduct, companionMatrix, companionEigenvector,
      hi, if_pos]
    rw [hroot]
    have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    change z ^ n = z * z ^ (n - 1 - i.val)
    rw [hi, Nat.sub_zero, show n = (n - 1) + 1 by omega, pow_succ]
    exact mul_comm _ _
  · simp only [Matrix.mulVec, dotProduct, companionMatrix, companionEigenvector,
      hi, if_false]
    simp only [ite_mul, one_mul, zero_mul, Pi.smul_apply, smul_eq_mul]
    have hipos : 0 < i.val := Nat.pos_of_ne_zero hi
    let k : Fin n := ⟨i.val - 1, by omega⟩
    rw [Finset.sum_eq_single k]
    · simp only [k, Nat.sub_add_cancel hipos, ↓reduceIte]
      rw [show n - 1 - (i.val - 1) = (n - 1 - i.val) + 1 by omega, pow_succ]
      exact mul_comm _ _
    · intro j _ hjk
      have hneq : ¬i.val = j.val + 1 := by
        intro hij
        apply hjk
        apply Fin.ext
        simp only [k]
        omega
      simp [hneq]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim

end NumStability
