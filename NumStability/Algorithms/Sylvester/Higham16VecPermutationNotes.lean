-- Algorithms/Sylvester/Higham16VecPermutationNotes.lean
--
-- The two explicit vec-permutation identities recorded in the notes after
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., (16.27).

import NumStability.Algorithms.Sylvester.Higham16

namespace NumStability

open scoped BigOperators

private theorem higham16_sum_swap_indicator
    {R : Type} [AddCommMonoid R] (q : Fin n × Fin n)
    (f : (Fin n × Fin n) → R) :
    (∑ x : Fin n × Fin n, if q = (x.2, x.1) then f x else 0) =
      f (q.2, q.1) := by
  classical
  rw [Finset.sum_eq_single (q.2, q.1)]
  · simp
  · intro x _ hx
    have hneq : q ≠ (x.2, x.1) := by
      intro h
      apply hx
      apply Prod.ext
      · exact (congrArg Prod.snd h).symm
      · exact (congrArg Prod.fst h).symm
    simp [hneq]
  · simp

/-- The matrix unit `e_i e_j^T` used in Higham's explicit formula for the
    vec-permutation matrix. -/
def higham16MatrixUnit (n : Nat) (i j : Fin n) :
    Matrix (Fin n) (Fin n) Real :=
  fun a b => if a = i ∧ b = j then 1 else 0

/-- Higham, 2nd ed., p. 317, notes following (16.27):
    `Pi = sum_{i,j} (e_i e_j^T) kron (e_j e_i^T)`.

    The product index is the one used by Mathlib's column-stacking `vec`.
    Thus the right-hand side has its unique nonzero in row `(a,b)` at column
    `(b,a)`, exactly as `vecTransposePermutation` does. -/
theorem higham16_vecTransposePermutation_explicit_sum (n : Nat) :
    vecTransposePermutation n =
      ∑ i : Fin n, ∑ j : Fin n,
        Matrix.kronecker (higham16MatrixUnit n i j)
          (higham16MatrixUnit n j i) := by
  ext p q
  classical
  simp only [vecTransposePermutation, higham16MatrixUnit, Matrix.kronecker,
    Matrix.kroneckerMap, Matrix.sum_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single p.1]
  · rw [Finset.sum_eq_single p.2]
    · by_cases h1 : q.1 = p.2 <;> by_cases h2 : q.2 = p.1 <;>
        simp [Prod.ext_iff, h1, h2]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [Ne.symm hi]
  · simp

/-- Higham, 2nd ed., p. 317, notes following (16.27):
    `(A kron B) Pi = Pi (B kron A)`.

    This is the exact commutation identity for the concrete permutation
    matrix, rather than merely its action on one vectorized matrix. -/
theorem higham16_kronecker_mul_vecTransposePermutation (n : Nat)
    (A B : Matrix (Fin n) (Fin n) Real) :
    Matrix.kronecker A B * vecTransposePermutation n =
      vecTransposePermutation n * Matrix.kronecker B A := by
  ext p q
  classical
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap,
    vecTransposePermutation, Matrix.of_apply, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul]
  rw [higham16_sum_swap_indicator]
  simp [mul_comm]

/-- Source-facing alias for Higham's explicit sum formula for `Pi`. -/
alias H16_notes_vecTransposePermutation_explicit_sum :=
  higham16_vecTransposePermutation_explicit_sum

/-- Source-facing alias for Higham's Kronecker/vec-permutation commutation
    identity. -/
alias H16_notes_kronecker_mul_vecTransposePermutation :=
  higham16_kronecker_mul_vecTransposePermutation

end NumStability
