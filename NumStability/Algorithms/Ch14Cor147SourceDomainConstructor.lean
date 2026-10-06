-- Algorithms/Ch14Cor147SourceDomainConstructor.lean
--
-- Construct the fixed exact LU/inverse analysis objects used by the literal
-- Corollary 14.7 family from the corollary's own source-domain assumptions.

import NumStability.Algorithms.Ch14Cor147FinalDivisionFamilyClosure
import NumStability.Algorithms.HighamChapter9Theorem99Closure
import NumStability.Algorithms.Cholesky.CholeskyPerturbation

namespace NumStability.Ch14Ext

open NumStability

/-- Row diagonal dominance and nonsingularity construct all fixed exact
analysis objects required by `Ch14Cor147FinalizedRunFamily`.

The LU factors come from the real row-diagonally-dominant branch of Higham
Theorem 9.9.  Their upper factor has nonzero diagonal, so its two-sided upper-
triangular inverse is constructed internally.  Thus callers provide only the
actual finalized GJE family and the source data appearing in Corollary 14.7;
no exact factors or factor inverse are independent premises. -/
theorem ch14ext_cor147FinalizedRunFamily_exists_of_source_domain
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (gje : Ch14GJEFinalizedFamily I l n A b)
    (row_diag_dominant : IsRowDiagDominant n A)
    (determinant_ne_zero :
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (source_inverse : IsInverse n A A_inv)
    (exact_solution : forall i, matMulVec n A x i = b i)
    (exact_solution_nonzero : 0 < infNormVec x) :
    exists F : Ch14Cor147FinalizedRunFamily I l n A A_inv b x,
      F.gje = gje := by
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one gje.dimension_pos
  obtain ⟨L, U, hLU, _hAmax, _hReducedGrowth, _hUpperGrowth⟩ :=
    higham9_9_rowDiagDominant_exists_LUFactSpec_noPivotGrowthFactor_le_two
      hn A row_diag_dominant determinant_ne_zero
  have hUdiag : forall i : Fin n, U i i ≠ 0 :=
    hLU.det_ne_zero_iff_U_diag_ne_zero.mp determinant_ne_zero
  obtain ⟨U_inv, _hUinvUpper, hUright, hUleft⟩ :=
    upperTriangular_inverse_exists n U hLU.U_lower_zero hUdiag
  refine ⟨{
    gje := gje
    row_diag_dominant := row_diag_dominant
    determinant_ne_zero := determinant_ne_zero
    L := L
    U := U
    U_inv := U_inv
    exact_lu := hLU
    exact_upper_inverse := ⟨hUleft, hUright⟩
    source_inverse := source_inverse
    exact_solution := exact_solution
    exact_solution_nonzero := exact_solution_nonzero
  }, rfl⟩

/-- Choice-free interface for the source-domain constructor above.  The
selected exact factors are analysis-only objects; the operational GJE field is
definitionally the caller's actual finalized family. -/
noncomputable def ch14ext_cor147FinalizedRunFamily_of_source_domain
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (gje : Ch14GJEFinalizedFamily I l n A b)
    (row_diag_dominant : IsRowDiagDominant n A)
    (determinant_ne_zero :
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (source_inverse : IsInverse n A A_inv)
    (exact_solution : forall i, matMulVec n A x i = b i)
    (exact_solution_nonzero : 0 < infNormVec x) :
    Ch14Cor147FinalizedRunFamily I l n A A_inv b x :=
  Classical.choose
    (ch14ext_cor147FinalizedRunFamily_exists_of_source_domain gje
      row_diag_dominant determinant_ne_zero source_inverse exact_solution
      exact_solution_nonzero)

@[simp] theorem ch14ext_cor147FinalizedRunFamily_of_source_domain_gje
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (gje : Ch14GJEFinalizedFamily I l n A b)
    (row_diag_dominant : IsRowDiagDominant n A)
    (determinant_ne_zero :
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (source_inverse : IsInverse n A A_inv)
    (exact_solution : forall i, matMulVec n A x i = b i)
    (exact_solution_nonzero : 0 < infNormVec x) :
    (ch14ext_cor147FinalizedRunFamily_of_source_domain gje
      row_diag_dominant determinant_ne_zero source_inverse exact_solution
      exact_solution_nonzero).gje = gje :=
  Classical.choose_spec
    (ch14ext_cor147FinalizedRunFamily_exists_of_source_domain gje
      row_diag_dominant determinant_ne_zero source_inverse exact_solution
      exact_solution_nonzero)

end NumStability.Ch14Ext
