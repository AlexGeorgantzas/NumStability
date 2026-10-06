import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.VectorizationIdentities.KroneckerPermutation
import NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.VectorizationNotes.Notes

/-!
# Algorithms.Sylvester.Higham16VecPermutationNotes

Historical declaration-bearing facade. Genuine-private and ambient-context retention closure remains here with its original identity.
-/

-- Algorithms/Sylvester/Higham16VecPermutationNotes.lean
--
-- The two explicit vec-permutation identities recorded in the notes after
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., (16.27).



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





/-- Source-facing alias for Higham's Kronecker/vec-permutation commutation
    identity. -/
alias H16_notes_kronecker_mul_vecTransposePermutation :=
  higham16_kronecker_mul_vecTransposePermutation

end NumStability
