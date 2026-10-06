import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Vec
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.ComplexSchur.Existence
import NumStability.Analysis.LinearOperators.Schur.Complex.Triangulation
import NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.ComplexSolvability.SchurFactors

/-!
# Analysis.SylvesterSchurExistence

Historical declaration-bearing facade. Genuine-private and ambient-context retention closure remains here with its original identity.
-/

/-
Analysis/SylvesterSchurExistence.lean

Complex-path Schur existence for the Chapter 16 Sylvester equation
(Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Section 16.2, equations (16.4)-(16.6)).

MOTIVATION / HONEST SCOPE.

The real-valued Chapter 16 development
(`NumStability/Algorithms/Sylvester/Higham16.lean`,
`NumStability/Algorithms/Sylvester/Higham16Spectrum.lean`) proves the Bartels-Stewart
triangular solve only *conditionally* on SUPPLIED Schur factors: the theorem
`existsUnique_isSylvesterSolutionRect_schurTriangular` requires the caller to
hand over real orthogonal `U, V`, a real matrix `R` with `A = U R Uᵀ`, and a
real UPPER-TRIANGULAR `S` with `B = V S Vᵀ`.  That "supplied factors" hypothesis
is genuine and unavoidable there, because a real matrix in general has NO real
upper-triangular Schur form: the real Schur form of Higham (16.4) is only
*quasi*-triangular (2x2 real blocks for complex-conjugate eigenpairs).  The real
file therefore cannot discharge its own supplied-triangular hypothesis, and does
not claim to.

Over `ℂ`, by contrast, the classical Schur triangulation
`NumStability.schur_triangulation` (`NumStability/Analysis/SchurTriangulation.lean`)
gives, for EVERY complex square matrix, a genuine unitary `U` and a genuine
upper-triangular `T` with `Uᴴ A U = T`.  This file uses that primitive to turn
the complex analogue of the supplied-triangular hypothesis into an
*unconditional existence* statement, and then proves unique solvability of the
complex Sylvester equation `A X - X B = C`.

WHAT IS UNCONDITIONAL HERE (no supplied factors):

* `complexSylvester_schur_factors_exist` — for any `A : ℂ^{m×m}`,
  `B : ℂ^{n×n}` there exist a unitary `U` and upper-triangular `R` with
  `Uᴴ A U = R`, and a unitary `V` and upper-triangular `S` with `Vᴴ B V = S`.
  This is exactly the datum the real file must *assume*; over `ℂ` it is proved.

WHAT REMAINS AN EXPLICIT, NON-TAUTOLOGICAL HYPOTHESIS:

* the per-column shift nonsingularity `det (R - s_kk • I) ≠ 0`.  This is a
  condition on the DIAGONAL ENTRIES of the triangular factors, i.e. on the
  eigenvalues `λ_i(A) ≠ μ_k(B)` (the Sylvester separation / no-common-eigenvalue
  condition of (16.3)).  It is emphatically NOT the conclusion in disguise: it
  constrains only the (supplied-by-Schur) eigenvalues, not the solution `X`.  The
  headline theorem `complexSylvester_exists_unique_of_schur_shift` exposes it as
  a hypothesis phrased in terms of the Schur factors produced by the existence
  step, and states honestly that this is the residual assumption.

WHAT IS NOT CLAIMED:

* No real Schur form, no real quasi-triangular (2x2 block) solve of Higham
  (16.4)/(16.7)-(16.8): those are over `ℝ` and are genuinely different objects.
  This file does not touch, restate, or overclaim the real results.
* No floating-point rounding analysis; all arithmetic is exact over `ℂ`.
* No spectral converse claim beyond what the shift hypothesis encodes.

Everything is stated for the standard Mathlib matrix type `Matrix (Fin _) (Fin _)
ℂ` with ordinary matrix multiplication `*` and `Matrix.mulVec`, so that the
complex Schur primitive (`Uᴴ * A * U = T`) plugs in directly.
-/







open scoped BigOperators Matrix

namespace NumStability

-- ============================================================
-- The complex Sylvester operator and solution predicate
-- ============================================================































































































































private def complexSylvesterVecCoeffDualIndexEquiv (m n : ℕ) :
    (Fin n × Fin m) ≃ ((Fin n)ᵒᵈ ×ₗ Fin m) :=
  (Equiv.prodCongr OrderDual.toDual (Equiv.refl (Fin m))).trans toLex

/-- Reversing the block coordinate makes the complex triangular Sylvester vec
    coefficient upper triangular when both Schur factors are upper triangular. -/
theorem complexSylvesterVecCoeff_reindex_upperTriangular {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    (Matrix.reindex (complexSylvesterVecCoeffDualIndexEquiv m n)
        (complexSylvesterVecCoeffDualIndexEquiv m n)
        (complexSylvesterVecCoeff A B)).BlockTriangular id := by
  let e := complexSylvesterVecCoeffDualIndexEquiv m n
  intro x y hyx
  rcases (Prod.Lex.lt_iff.mp hyx) with hblock | ⟨_, hrow⟩
  · have hBzero :
        B ((e.symm y).1) ((e.symm x).1) = 0 := by
      exact hB _ _ (by simpa [e, complexSylvesterVecCoeffDualIndexEquiv] using hblock)
    have hblock_ne :
        (e.symm x).1 ≠ (e.symm y).1 := by
      intro hxy
      have : (ofLex y).1 = (ofLex x).1 := by
        simpa [e, complexSylvesterVecCoeffDualIndexEquiv] using
          congrArg OrderDual.toDual hxy.symm
      exact ne_of_lt hblock this
    simp [e, complexSylvesterVecCoeff, Matrix.reindex_apply, Matrix.sub_apply,
      Matrix.kronecker, Matrix.transpose_apply, hBzero, hblock_ne]
  · have hAzero :
        A ((e.symm x).2) ((e.symm y).2) = 0 := by
      exact hA _ _ hrow
    have hrow_ne :
        (e.symm x).2 ≠ (e.symm y).2 := by
      intro hxy
      have : (ofLex y).2 = (ofLex x).2 := by
        simpa [e, complexSylvesterVecCoeffDualIndexEquiv] using hxy.symm
      exact ne_of_lt hrow this
    simp [e, complexSylvesterVecCoeff, Matrix.reindex_apply, Matrix.sub_apply,
      Matrix.kronecker, Matrix.transpose_apply, hAzero, hrow_ne]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), supplied complex
    triangular case: the vec/Kronecker Sylvester coefficient determinant is
    the product of the pairwise Schur diagonal differences. -/
theorem complexSylvesterVecCoeff_det_eq_prod_of_upperTriangular {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B) =
      ∏ p : Prod (Fin n) (Fin m), (A p.2 p.2 - B p.1 p.1) := by
  let e := complexSylvesterVecCoeffDualIndexEquiv m n
  have htri :
      (Matrix.reindex e e (complexSylvesterVecCoeff A B)).BlockTriangular id :=
    complexSylvesterVecCoeff_reindex_upperTriangular A B hA hB
  have hdet_reindex :
      Matrix.det (Matrix.reindex e e (complexSylvesterVecCoeff A B)) =
        Matrix.det (complexSylvesterVecCoeff A B) :=
    Matrix.det_reindex_self e (complexSylvesterVecCoeff A B)
  rw [← hdet_reindex, Matrix.det_of_upperTriangular htri]
  have hdiag :
      (fun x : (Fin n)ᵒᵈ ×ₗ Fin m =>
        Matrix.reindex e e (complexSylvesterVecCoeff A B) x x) =
      fun x : (Fin n)ᵒᵈ ×ₗ Fin m =>
        A ((e.symm x).2) ((e.symm x).2) -
          B ((e.symm x).1) ((e.symm x).1) := by
    funext x
    simp [e, complexSylvesterVecCoeff, Matrix.reindex_apply, Matrix.kronecker,
      Matrix.transpose_apply]
  rw [hdiag]
  exact e.symm.prod_comp
    (fun p : Prod (Fin n) (Fin m) => A p.2 p.2 - B p.1 p.1)

/-- Reversing the block coordinate also makes every scalar shift of the
    complex triangular Sylvester vec coefficient upper triangular. -/
theorem complexSylvesterVecCoeff_shifted_reindex_upperTriangular {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    (Matrix.reindex (complexSylvesterVecCoeffDualIndexEquiv m n)
        (complexSylvesterVecCoeffDualIndexEquiv m n)
        (complexSylvesterVecCoeff A B -
          Matrix.scalar (Prod (Fin n) (Fin m)) μ)).BlockTriangular id := by
  let e := complexSylvesterVecCoeffDualIndexEquiv m n
  have htri :
      (Matrix.reindex e e (complexSylvesterVecCoeff A B)).BlockTriangular id :=
    complexSylvesterVecCoeff_reindex_upperTriangular A B hA hB
  intro x y hyx
  have hcoeff :
      Matrix.reindex e e (complexSylvesterVecCoeff A B) x y = 0 :=
    htri hyx
  have hxy : e.symm x ≠ e.symm y := by
    intro h
    exact ne_of_gt hyx (e.symm.injective h)
  have hscalar :
      Matrix.reindex e e (Matrix.scalar (Prod (Fin n) (Fin m)) μ) x y = 0 := by
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ hxy]
  change
    Matrix.reindex e e
        (complexSylvesterVecCoeff A B - Matrix.scalar (Prod (Fin n) (Fin m)) μ) x y =
      0
  calc
    Matrix.reindex e e
        (complexSylvesterVecCoeff A B - Matrix.scalar (Prod (Fin n) (Fin m)) μ) x y
        = Matrix.reindex e e (complexSylvesterVecCoeff A B) x y -
            Matrix.reindex e e (Matrix.scalar (Prod (Fin n) (Fin m)) μ) x y := by
          simp [Matrix.reindex_apply, Matrix.sub_apply]
    _ = 0 := by rw [hcoeff, hscalar, sub_zero]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), supplied complex
    triangular shifted case: the scalar-shifted vec/Kronecker Sylvester
    coefficient determinant is the product of shifted pairwise Schur diagonal
    differences. -/
theorem complexSylvesterVecCoeff_shifted_det_eq_prod_of_upperTriangular {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B -
        Matrix.scalar (Prod (Fin n) (Fin m)) μ) =
      ∏ p : Prod (Fin n) (Fin m), (A p.2 p.2 - B p.1 p.1 - μ) := by
  let e := complexSylvesterVecCoeffDualIndexEquiv m n
  have htri :
      (Matrix.reindex e e
        (complexSylvesterVecCoeff A B -
          Matrix.scalar (Prod (Fin n) (Fin m)) μ)).BlockTriangular id :=
    complexSylvesterVecCoeff_shifted_reindex_upperTriangular A B μ hA hB
  have hdet_reindex :
      Matrix.det (Matrix.reindex e e
        (complexSylvesterVecCoeff A B -
          Matrix.scalar (Prod (Fin n) (Fin m)) μ)) =
        Matrix.det (complexSylvesterVecCoeff A B -
          Matrix.scalar (Prod (Fin n) (Fin m)) μ) :=
    Matrix.det_reindex_self e
      (complexSylvesterVecCoeff A B - Matrix.scalar (Prod (Fin n) (Fin m)) μ)
  rw [← hdet_reindex, Matrix.det_of_upperTriangular htri]
  have hdiag :
      (fun x : (Fin n)ᵒᵈ ×ₗ Fin m =>
        Matrix.reindex e e
          (complexSylvesterVecCoeff A B -
            Matrix.scalar (Prod (Fin n) (Fin m)) μ) x x) =
      fun x : (Fin n)ᵒᵈ ×ₗ Fin m =>
        A ((e.symm x).2) ((e.symm x).2) -
          B ((e.symm x).1) ((e.symm x).1) - μ := by
    funext x
    simp [e, complexSylvesterVecCoeff, Matrix.reindex_apply, Matrix.sub_apply,
      Matrix.kronecker, Matrix.transpose_apply]
  rw [hdiag]
  exact e.symm.prod_comp
    (fun p : Prod (Fin n) (Fin m) => A p.2 p.2 - B p.1 p.1 - μ)

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), supplied complex
    triangular shifted case: shifted determinant nonsingularity is equivalent to
    separation of the shift from every pairwise Schur diagonal difference. -/
theorem complexSylvesterVecCoeff_shifted_det_ne_zero_iff_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B -
        Matrix.scalar (Prod (Fin n) (Fin m)) μ) ≠ 0 ↔
      ∀ i : Fin m, ∀ j : Fin n, A i i - B j j ≠ μ := by
  rw [complexSylvesterVecCoeff_shifted_det_eq_prod_of_upperTriangular A B μ hA hB]
  constructor
  · intro hdet i j hij
    have hfactor :=
      (Finset.prod_ne_zero_iff.mp hdet) (j, i) (Finset.mem_univ _)
    exact hfactor (sub_eq_zero.mpr hij)
  · intro hsep
    exact Finset.prod_ne_zero_iff.mpr
      (fun p _ => sub_ne_zero.mpr (hsep p.2 p.1))

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), supplied complex
    triangular shifted determinant-nonsingularity consequence from shifted
    diagonal-difference separation. -/
theorem complexSylvesterVecCoeff_shifted_det_ne_zero_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B)
    (hsep : ∀ i : Fin m, ∀ j : Fin n, A i i - B j j ≠ μ) :
    Matrix.det (complexSylvesterVecCoeff A B -
        Matrix.scalar (Prod (Fin n) (Fin m)) μ) ≠ 0 := by
  exact
    (complexSylvesterVecCoeff_shifted_det_ne_zero_iff_of_upperTriangular_diagonal_separation
      A B μ hA hB).mpr hsep

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), supplied complex
    triangular case: determinant nonsingularity is equivalent to pairwise
    separation of the triangular diagonal entries. -/
theorem complexSylvesterVecCoeff_det_ne_zero_iff_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 ↔
      ∀ i : Fin m, ∀ j : Fin n, A i i ≠ B j j := by
  rw [complexSylvesterVecCoeff_det_eq_prod_of_upperTriangular A B hA hB]
  constructor
  · intro hdet i j hij
    have hfactor :=
      (Finset.prod_ne_zero_iff.mp hdet) (j, i) (Finset.mem_univ _)
    exact hfactor (sub_eq_zero.mpr hij)
  · intro hsep
    exact Finset.prod_ne_zero_iff.mpr
      (fun p _ => sub_ne_zero.mpr (hsep p.2 p.1))

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), supplied complex
    triangular determinant-nonsingularity consequence from pairwise diagonal
    separation. -/
theorem complexSylvesterVecCoeff_det_ne_zero_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B)
    (hsep : ∀ i : Fin m, ∀ j : Fin n, A i i ≠ B j j) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 := by
  exact
    (complexSylvesterVecCoeff_det_ne_zero_iff_of_upperTriangular_diagonal_separation
      A B hA hB).mpr hsep










/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered alias for
    the supplied complex triangular vec/Kronecker determinant product. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_det_eq_prod_of_upperTriangular
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B) =
      ∏ p : Prod (Fin n) (Fin m), (A p.2 p.2 - B p.1 p.1) :=
  complexSylvesterVecCoeff_det_eq_prod_of_upperTriangular A B hA hB

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered alias for
    the supplied complex triangular shifted vec/Kronecker determinant product. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_shifted_det_eq_prod_of_upperTriangular
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B -
        Matrix.scalar (Prod (Fin n) (Fin m)) μ) =
      ∏ p : Prod (Fin n) (Fin m), (A p.2 p.2 - B p.1 p.1 - μ) :=
  complexSylvesterVecCoeff_shifted_det_eq_prod_of_upperTriangular A B μ hA hB

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered alias for
    the supplied complex triangular shifted determinant/separation equivalence. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_shifted_det_ne_zero_iff_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B -
        Matrix.scalar (Prod (Fin n) (Fin m)) μ) ≠ 0 ↔
      ∀ i : Fin m, ∀ j : Fin n, A i i - B j j ≠ μ :=
  complexSylvesterVecCoeff_shifted_det_ne_zero_iff_of_upperTriangular_diagonal_separation
    A B μ hA hB

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered alias for
    the supplied complex triangular shifted determinant nonsingularity
    consequence. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_shifted_det_ne_zero_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B)
    (hsep : ∀ i : Fin m, ∀ j : Fin n, A i i - B j j ≠ μ) :
    Matrix.det (complexSylvesterVecCoeff A B -
        Matrix.scalar (Prod (Fin n) (Fin m)) μ) ≠ 0 :=
  complexSylvesterVecCoeff_shifted_det_ne_zero_of_upperTriangular_diagonal_separation
    A B μ hA hB hsep

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered alias for
    the supplied complex triangular determinant/separation equivalence. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_det_ne_zero_iff_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 ↔
      ∀ i : Fin m, ∀ j : Fin n, A i i ≠ B j j :=
  complexSylvesterVecCoeff_det_ne_zero_iff_of_upperTriangular_diagonal_separation
    A B hA hB

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered alias for
    supplied complex triangular nonsingularity from diagonal separation. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_det_ne_zero_of_upperTriangular_diagonal_separation
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B)
    (hsep : ∀ i : Fin m, ∀ j : Fin n, A i i ≠ B j j) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 :=
  complexSylvesterVecCoeff_det_ne_zero_of_upperTriangular_diagonal_separation
    A B hA hB hsep

























































/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), supplied complex
    triangular spectral form: no common supplied right eigenpair of the two
    triangular factors implies nonsingularity of the vec/Kronecker Sylvester
    coefficient. -/
theorem complexSylvesterVecCoeff_det_ne_zero_of_upperTriangular_no_common_eigenpair
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B)
    (hno : ∀ μ : ℂ,
      ¬ ((∃ y : Fin m → ℂ,
            y ≠ 0 ∧ Matrix.mulVec A y = fun i => μ * y i) ∧
          (∃ z : Fin n → ℂ,
            z ≠ 0 ∧ Matrix.mulVec B z = fun j => μ * z j))) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 :=
  complexSylvesterVecCoeff_det_ne_zero_of_upperTriangular_diagonal_separation
    A B hA hB
    (complexUpperTriangular_diagonal_separation_of_no_common_eigenpair
      A B hA hB hno)

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered alias for
    the supplied complex triangular no-common-eigenpair determinant route. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_det_ne_zero_of_upperTriangular_no_common_eigenpair
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUpperTriangularC A) (hB : IsUpperTriangularC B)
    (hno : ∀ μ : ℂ,
      ¬ ((∃ y : Fin m → ℂ,
            y ≠ 0 ∧ Matrix.mulVec A y = fun i => μ * y i) ∧
          (∃ z : Fin n → ℂ,
            z ≠ 0 ∧ Matrix.mulVec B z = fun j => μ * z j))) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 :=
  complexSylvesterVecCoeff_det_ne_zero_of_upperTriangular_no_common_eigenpair
    A B hA hB hno

-- ============================================================
-- Complex Schur factors exist unconditionally
-- ============================================================




















-- ============================================================
-- The transformed equation R Y - Y S = C' in Schur coordinates
-- ============================================================



















































































-- ============================================================
-- The complex Bartels-Stewart column solve
-- ============================================================
























































































































































































-- ============================================================
-- Uniqueness and existence of the column solve
-- ============================================================

private theorem complex_mulVec_injective_of_det_ne_zero {m : ℕ}
    {M : Matrix (Fin m) (Fin m) ℂ} (hdet : M.det ≠ 0)
    {x y : Fin m → ℂ}
    (hxy : M.mulVec x = M.mulVec y) : x = y := by
  have h := congrArg (M⁻¹.mulVec) hxy
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

private theorem complex_mulVec_surjective_of_det_ne_zero {m : ℕ}
    {M : Matrix (Fin m) (Fin m) ℂ} (hdet : M.det ≠ 0)
    (c : Fin m → ℂ) :
    ∃ x : Fin m → ℂ, M.mulVec x = c := by
  refine ⟨M⁻¹.mulVec c, ?_⟩
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), complex uniqueness half:
    with upper-triangular `S` and every shifted column coefficient `R - s_kk I`
    nonsingular, two solutions of `R Y - Y S = C` coincide, by strong induction
    over columns using the column recurrence. -/
theorem complexSylvester_triangular_solution_unique {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C Y Z : Matrix (Fin m) (Fin n) ℂ)
    (hS : IsUpperTriangularC S)
    (hshift : ∀ k : Fin n, (complexShiftedCoeff R (S k k)).det ≠ 0)
    (hY : IsComplexSylvesterSolution R S C Y)
    (hZ : IsComplexSylvesterSolution R S C Z) :
    Y = Z := by
  have hcol : ∀ N : ℕ, ∀ k : Fin n, k.val < N →
      (fun i => Y i k) = (fun i => Z i k) := by
    intro N
    induction N with
    | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
        intro k hk
        by_cases hlt : k.val < N
        · exact ih k hlt
        · have hYk := complexSylvester_column_equation R S C Y hS hY k
          have hZk := complexSylvester_column_equation R S C Z hS hZ k
          have hrhs :
              (fun i => C i k +
                ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j) =
              (fun i => C i k +
                ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Z i j) := by
            funext i
            have hsum :
                (∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Y i j) =
                  ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * Z i j := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk : (j : ℕ) < (k : ℕ) :=
                Fin.lt_def.mp (Finset.mem_filter.mp hj).2
              have hjN : (j : ℕ) < N := by omega
              have hYZ : Y i j = Z i j := congrFun (ih j hjN) i
              rw [hYZ]
            rw [hsum]
          have hmv :
              (complexShiftedCoeff R (S k k)).mulVec (fun i => Y i k) =
                (complexShiftedCoeff R (S k k)).mulVec (fun i => Z i k) := by
            rw [hYk, hZk]; exact hrhs
          exact complex_mulVec_injective_of_det_ne_zero (hshift k) hmv
  funext i k
  exact congrFun (hcol n k k.isLt) i

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.6), complex
    Bartels-Stewart existence and uniqueness (supplied triangular `S`): with `S`
    upper-triangular and every shifted column coefficient `R - s_kk I`
    nonsingular, the transformed equation `R Y - Y S = C` has EXACTLY ONE
    solution, built by strong induction over columns from the column inverses.

    Here `S` upper-triangular and the shift nonsingularity are the honest
    residual hypotheses; existence of the triangular factor itself is discharged
    separately by `complexSylvester_schur_factors_exist`. -/
theorem complexSylvester_triangular_exists_unique {m n : ℕ}
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hS : IsUpperTriangularC S)
    (hshift : ∀ k : Fin n, (complexShiftedCoeff R (S k k)).det ≠ 0) :
    ∃! Y : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution R S C Y := by
  -- Build columns by strong induction. `y : Fin n → (Fin m → ℂ)` holds columns.
  have hpartial : ∀ N : ℕ,
      ∃ y : Fin n → Fin m → ℂ,
        ∀ k : Fin n, k.val < N →
          (complexShiftedCoeff R (S k k)).mulVec (y k) =
            fun i => C i k +
              ∑ j ∈ Finset.univ.filter (fun j => j < k), S j k * y j i := by
    intro N
    induction N with
    | zero =>
        refine ⟨fun _ _ => 0, ?_⟩
        intro k hk; exact absurd hk (Nat.not_lt_zero _)
    | succ N ih =>
        obtain ⟨y, hy⟩ := ih
        by_cases hN : N < n
        · obtain ⟨yk, hyk⟩ :=
            complex_mulVec_surjective_of_det_ne_zero (hshift ⟨N, hN⟩)
              (fun i => C i ⟨N, hN⟩ +
                ∑ j ∈ Finset.univ.filter (fun j => j < (⟨N, hN⟩ : Fin n)),
                  S j ⟨N, hN⟩ * y j i)
          refine ⟨Function.update y ⟨N, hN⟩ yk, ?_⟩
          intro k hk
          have hupdate_rhs : ∀ k' : Fin n, k'.val ≤ N →
              (fun i => C i k' +
                ∑ j ∈ Finset.univ.filter (fun j => j < k'),
                  S j k' * Function.update y ⟨N, hN⟩ yk j i) =
              (fun i => C i k' +
                ∑ j ∈ Finset.univ.filter (fun j => j < k'),
                  S j k' * y j i) := by
            intro k' hk'
            funext i
            have hsum :
                (∑ j ∈ Finset.univ.filter (fun j => j < k'),
                  S j k' * Function.update y ⟨N, hN⟩ yk j i) =
                ∑ j ∈ Finset.univ.filter (fun j => j < k'), S j k' * y j i := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk : (j : ℕ) < (k' : ℕ) :=
                Fin.lt_def.mp (Finset.mem_filter.mp hj).2
              have hjne : j ≠ (⟨N, hN⟩ : Fin n) := by
                intro hje
                have hjval : (j : ℕ) = N := by rw [hje]
                omega
              rw [Function.update_of_ne hjne]
            rw [hsum]
          by_cases hkval : k.val < N
          · have hkne : k ≠ (⟨N, hN⟩ : Fin n) := by
              intro hke
              have hkv : (k : ℕ) = N := by rw [hke]
              omega
            rw [Function.update_of_ne hkne, hupdate_rhs k (Nat.le_of_lt hkval)]
            exact hy k hkval
          · have hkeq : k = (⟨N, hN⟩ : Fin n) := by
              apply Fin.ext; show (k : ℕ) = N; omega
            rw [hkeq, Function.update_self, hupdate_rhs ⟨N, hN⟩ (Nat.le_refl N)]
            exact hyk
        · refine ⟨y, ?_⟩
          intro k hk
          have hkN : k.val < N := by
            have hkn : k.val < n := k.isLt; omega
          exact hy k hkN
  obtain ⟨y, hy⟩ := hpartial n
  refine ⟨Matrix.of fun i j => y j i, ?_, ?_⟩
  · apply (isComplexSylvesterSolution_iff_columns R S C
      (Matrix.of fun i j => y j i) hS).mpr
    intro k
    have := hy k k.isLt
    simpa [Matrix.of_apply] using this
  · intro Z hZ
    have hconstr : IsComplexSylvesterSolution R S C (Matrix.of fun i j => y j i) := by
      apply (isComplexSylvesterSolution_iff_columns R S C
        (Matrix.of fun i j => y j i) hS).mpr
      intro k
      have := hy k k.isLt
      simpa [Matrix.of_apply] using this
    exact complexSylvester_triangular_solution_unique R S C Z
      (Matrix.of fun i j => y j i) hS hshift hZ hconstr

-- ============================================================
-- Headline: complex Sylvester unique solvability with Schur factors supplied
-- by existence (not by hypothesis)
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.6), complex path,
    supplied-by-Schur factors: if unitary `U`, `V` conjugate `A`, `B` to
    upper-triangular `R`, `S`, and every shifted column coefficient
    `R - s_kk I` is nonsingular, then the complex Sylvester equation
    `A X - X B = C` has exactly one solution.

    This composes the unitary conjugation equivalence
    (`isComplexSylvesterSolution_conj_iff`) with the triangular column solve
    (`complexSylvester_triangular_exists_unique`).  The upper-triangular factors
    `R, S` here are provided UNCONDITIONALLY by
    `complexSylvester_schur_factors_exist`; only the shift nonsingularity (a
    condition on the eigenvalues on the diagonals of `R, S`) is assumed. -/
theorem complexSylvester_exists_unique_of_schur_factors {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hR : Uᴴ * A * U = R) (hS : Vᴴ * B * V = S)
    (hStri : IsUpperTriangularC S)
    (hshift : ∀ k : Fin n, (complexShiftedCoeff R (S k k)).det ≠ 0) :
    ∃! X : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution A B C X := by
  obtain ⟨Y, hYsol, hYuniq⟩ :=
    complexSylvester_triangular_exists_unique R S (Uᴴ * C * V) hStri hshift
  have hUU : U * Uᴴ = 1 := by
    have := hU.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hUhU : Uᴴ * U = 1 := by
    have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hVV : V * Vᴴ = 1 := by
    have := hV.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hVhV : Vᴴ * V = 1 := by
    have := hV.1; rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨U * Y * Vᴴ, ?_, ?_⟩
  · exact (isComplexSylvesterSolution_conj_iff A B U V R S C Y
      hU hV hR hS).mpr hYsol
  · intro X hX
    -- Recover the Schur-coordinate solution of X and match it to Y.
    set W : Matrix (Fin m) (Fin n) ℂ := Uᴴ * X * V with hW
    have hXexpand : U * W * Vᴴ = X := by
      rw [hW]
      have step : U * (Uᴴ * X * V) * Vᴴ = (U * Uᴴ) * X * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      rw [step, hUU, hVV, Matrix.one_mul, Matrix.mul_one]
    have hXsol : IsComplexSylvesterSolution A B C (U * W * Vᴴ) := by
      rw [hXexpand]; exact hX
    have hWsol : IsComplexSylvesterSolution R S (Uᴴ * C * V) W :=
      (isComplexSylvesterSolution_conj_iff A B U V R S C W hU hV hR hS).mp hXsol
    have hWY : W = Y := hYuniq W hWsol
    rw [← hXexpand, hWY]

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.6), complex Schur
    factors with explicit diagonal separation: if the Schur diagonals of `R`
    and `S` are pairwise distinct, then the complex Sylvester equation has a
    unique exact solution.  This packages the source-level eigenvalue
    separation condition into the shifted determinant hypotheses used by the
    column recurrence. -/
theorem complexSylvester_exists_unique_of_schur_diagonal_separation {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hA : Uᴴ * A * U = R) (hB : Vᴴ * B * V = S)
    (hRtri : IsUpperTriangularC R)
    (hStri : IsUpperTriangularC S)
    (hsep : ∀ i : Fin m, ∀ k : Fin n, R i i ≠ S k k) :
    ∃! X : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution A B C X := by
  exact complexSylvester_exists_unique_of_schur_factors A B U V R S C
    hU hV hA hB hStri
    (complexSylvester_shift_det_ne_zero_of_schur_diagonal_separation
      R S hRtri hsep)

/-- Higham, 2nd ed., Chapter 16.2, equations (16.3)-(16.6):
    source-numbered alias for the supplied complex Schur diagonal-separation
    exact unique-solve theorem. -/
alias H16_eq16_3_6_complexSylvester_exists_unique_of_schur_diagonal_separation :=
  complexSylvester_exists_unique_of_schur_diagonal_separation



































































/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6), complex
    Schur route from a no-common-right-eigenpair hypothesis: if the original
    matrices have no common supplied complex right eigenpair, then supplied
    unitary Schur factors have separated diagonals and the exact complex
    Sylvester equation has a unique solution. -/
theorem complexSylvester_exists_unique_of_schur_no_common_eigenpair {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hR : Uᴴ * A * U = R) (hS : Vᴴ * B * V = S)
    (hRtri : IsUpperTriangularC R)
    (hStri : IsUpperTriangularC S)
    (hno : ∀ μ : ℂ,
      ¬ ((∃ y : Fin m → ℂ,
            y ≠ 0 ∧ Matrix.mulVec A y = fun i => μ * y i) ∧
          (∃ z : Fin n → ℂ,
            z ≠ 0 ∧ Matrix.mulVec B z = fun j => μ * z j))) :
    ∃! X : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution A B C X :=
  complexSylvester_exists_unique_of_schur_diagonal_separation A B U V R S C
    hU hV hR hS hRtri hStri
    (complexSchur_diagonal_separation_of_no_common_eigenpair
      A B U V R S hU hV hR hS hRtri hStri hno)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6):
    source-numbered alias for the complex Schur unique-solve route from a
    no-common-right-eigenpair hypothesis on the original matrices. -/
theorem H16_eq16_3_complexSylvester_exists_unique_of_schur_no_common_eigenpair
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ)
    (R : Matrix (Fin m) (Fin m) ℂ) (S : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hR : Uᴴ * A * U = R) (hS : Vᴴ * B * V = S)
    (hRtri : IsUpperTriangularC R)
    (hStri : IsUpperTriangularC S)
    (hno : ∀ μ : ℂ,
      ¬ ((∃ y : Fin m → ℂ,
            y ≠ 0 ∧ Matrix.mulVec A y = fun i => μ * y i) ∧
          (∃ z : Fin n → ℂ,
            z ≠ 0 ∧ Matrix.mulVec B z = fun j => μ * z j))) :
    ∃! X : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution A B C X :=
  complexSylvester_exists_unique_of_schur_no_common_eigenpair
    A B U V R S C hU hV hR hS hRtri hStri hno

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6), complex
    Schur route with factors supplied by existence: if the original complex
    matrices have no common supplied right eigenpair, then the exact complex
    Sylvester equation has a unique solution. -/
theorem complexSylvester_exists_unique_of_no_common_eigenpair {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hno : ∀ μ : ℂ,
      ¬ ((∃ y : Fin m → ℂ,
            y ≠ 0 ∧ Matrix.mulVec A y = fun i => μ * y i) ∧
          (∃ z : Fin n → ℂ,
            z ≠ 0 ∧ Matrix.mulVec B z = fun j => μ * z j))) :
    ∃! X : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution A B C X := by
  obtain ⟨U, R, V, S, hU, hUR, hRtri, hV, hVS, hStri⟩ :=
    complexSylvester_schur_factors_exist A B
  exact complexSylvester_exists_unique_of_schur_no_common_eigenpair
    A B U V R S C hU hV hUR hVS hRtri hStri hno

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.3)-(16.6):
    source-numbered alias for the exact complex Sylvester unique-solve theorem
    from no common supplied right eigenpair, with Schur factors obtained by
    existence. -/
theorem H16_eq16_3_complexSylvester_exists_unique_of_no_common_eigenpair
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hno : ∀ μ : ℂ,
      ¬ ((∃ y : Fin m → ℂ,
            y ≠ 0 ∧ Matrix.mulVec A y = fun i => μ * y i) ∧
          (∃ z : Fin n → ℂ,
            z ≠ 0 ∧ Matrix.mulVec B z = fun j => μ * z j))) :
    ∃! X : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution A B C X :=
  complexSylvester_exists_unique_of_no_common_eigenpair A B C hno

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.3), complex
    route with factors supplied by Schur existence: if the original complex
    matrices have no common supplied right eigenpair, then the vec/Kronecker
    Sylvester coefficient `I_n kron A - B^T kron I_m` is nonsingular. -/
theorem complexSylvesterVecCoeff_det_ne_zero_of_no_common_eigenpair {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hno : ∀ μ : ℂ,
      ¬ ((∃ y : Fin m → ℂ,
            y ≠ 0 ∧ Matrix.mulVec A y = fun i => μ * y i) ∧
          (∃ z : Fin n → ℂ,
            z ≠ 0 ∧ Matrix.mulVec B z = fun j => μ * z j))) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 :=
  complexSylvesterVecCoeff_det_ne_zero_of_unique_homogeneous A B
    (complexSylvester_exists_unique_of_no_common_eigenpair A B
      (0 : Matrix (Fin m) (Fin n) ℂ) hno)

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.2)-(16.3):
    source-numbered alias for the complex vec/Kronecker determinant
    nonsingularity theorem from no common supplied right eigenpair. -/
theorem H16_eq16_3_complexSylvesterVecCoeff_det_ne_zero_of_no_common_eigenpair
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hno : ∀ μ : ℂ,
      ¬ ((∃ y : Fin m → ℂ,
            y ≠ 0 ∧ Matrix.mulVec A y = fun i => μ * y i) ∧
          (∃ z : Fin n → ℂ,
            z ≠ 0 ∧ Matrix.mulVec B z = fun j => μ * z j))) :
    Matrix.det (complexSylvesterVecCoeff A B) ≠ 0 :=
  complexSylvesterVecCoeff_det_ne_zero_of_no_common_eigenpair A B hno

/-- Higham, 2nd ed., Chapter 16.2, equations (16.4)-(16.6), complex path,
    HEADLINE unconditional-existence form.  For ANY complex square matrices
    `A`, `B` (no supplied factors), Schur triangulation produces unitary
    factors and upper-triangular `R`, `S`; and PROVIDED the resulting shifted
    column coefficients are nonsingular (i.e. no shared eigenvalue between the
    diagonals of `R` and `S`), the complex Sylvester equation `A X - X B = C`
    has exactly one solution.

    The Schur factors are existentially bound rather than assumed: this is the
    genuine content that the real file `Higham16Spectrum.lean` could only obtain
    conditionally on supplied triangular factors, because the real Schur form is
    merely quasi-triangular.  The shift hypothesis is stated in terms of the
    Schur factors and is not the conclusion in disguise — it constrains only the
    eigenvalues, not `X`. -/
theorem complexSylvester_exists_unique_of_schur_shift {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin n) ℂ)
    (hshift : ∀ (U : Matrix (Fin m) (Fin m) ℂ) (R : Matrix (Fin m) (Fin m) ℂ)
      (V : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin n) (Fin n) ℂ),
      U ∈ Matrix.unitaryGroup (Fin m) ℂ → Uᴴ * A * U = R → IsUpperTriangularC R →
      V ∈ Matrix.unitaryGroup (Fin n) ℂ → Vᴴ * B * V = S → IsUpperTriangularC S →
      ∀ k : Fin n, (complexShiftedCoeff R (S k k)).det ≠ 0) :
    ∃! X : Matrix (Fin m) (Fin n) ℂ, IsComplexSylvesterSolution A B C X := by
  obtain ⟨U, R, V, S, hUu, hUeq, hRtri, hVu, hVeq, hStri⟩ :=
    complexSylvester_schur_factors_exist A B
  exact complexSylvester_exists_unique_of_schur_factors A B U V R S C
    hUu hVu hUeq hVeq hStri
    (hshift U R V S hUu hUeq hRtri hVu hVeq hStri)

end NumStability
