import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization

/-!
# Algorithms.MatrixEquations.Sylvester.Equation.VectorizationIdentities.KroneckerPermutation

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16VecPermutationNotes.lean
--
-- The two explicit vec-permutation identities recorded in the notes after
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., (16.27).



namespace NumStability

open scoped BigOperators



















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



























end NumStability
