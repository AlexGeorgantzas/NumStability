import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.VectorizationIdentities.KroneckerPermutation

/-!
# Source.Higham.Chapter16.Section01.SylvesterEquation.VectorizationNotes.Notes

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16VecPermutationNotes.lean
--
-- The two explicit vec-permutation identities recorded in the notes after
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., (16.27).



namespace NumStability

open scoped BigOperators






































































/-- Source-facing alias for Higham's explicit sum formula for `Pi`. -/
alias H16_notes_vecTransposePermutation_explicit_sum :=
  higham16_vecTransposePermutation_explicit_sum






end NumStability
