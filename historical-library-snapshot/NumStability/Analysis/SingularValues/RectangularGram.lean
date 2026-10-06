import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.SingularValues.RectangularRankFactorization

/-!
# Rectangular right-Gram singular-value infrastructure

Exact right-Gram matrices, basis-indexed singular values, and rectangular SVD
reconstructions used by deterministic numerical-analysis results.
-/

namespace NumStability

open scoped BigOperators

/-- Exact right Gram matrix `A^T A` for a rectangular real matrix.  This is an
analysis object.  Implementation-facing theorems must separately certify any
computed Gram entries. -/
noncomputable def rectRightGram {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ i : Fin m, A i j * A i k

/-- The exact right Gram matrix is symmetric. -/
theorem rectRightGram_symmetric {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (rectRightGram A) := by
  intro j k
  unfold rectRightGram
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quadratic form of `A^T A` is the squared norm of `A x`. -/
theorem finiteQuadraticForm_rectRightGram_eq_sum_sq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    finiteQuadraticForm (rectRightGram A) x =
      ∑ i : Fin m, (∑ j : Fin n, A i j * x j) ^ 2 := by
  classical
  unfold finiteQuadraticForm finiteMatVec rectRightGram
  calc
    ∑ a : Fin n,
        x a *
          ∑ b : Fin n,
            (∑ i : Fin m, A i a * A i b) * x b
        =
          ∑ a : Fin n, ∑ b : Fin n, ∑ i : Fin m,
            (A i a * x a) * (A i b * x b) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_mul]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ =
          ∑ b : Fin n, ∑ a : Fin n, ∑ i : Fin m,
            (A i a * x a) * (A i b * x b) := by
            rw [Finset.sum_comm]
    _ =
          ∑ b : Fin n, ∑ i : Fin m, ∑ a : Fin n,
            (A i a * x a) * (A i b * x b) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m, ∑ b : Fin n, ∑ a : Fin n,
            (A i a * x a) * (A i b * x b) := by
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m, ∑ a : Fin n, ∑ b : Fin n,
            (A i a * x a) * (A i b * x b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
    _ =
          ∑ i : Fin m,
            (∑ a : Fin n, A i a * x a) *
              (∑ b : Fin n, A i b * x b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
    _ =
          ∑ i : Fin m, (∑ j : Fin n, A i j * x j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- The exact right Gram matrix is positive semidefinite. -/
theorem rectRightGram_finitePSD {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    finitePSD (rectRightGram A) := by
  intro x
  rw [finiteQuadraticForm_rectRightGram_eq_sum_sq A x]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Mathlib positive-semidefinite form of `rectRightGram_finitePSD`. -/
theorem rectRightGram_matrix_posSemidef {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    Matrix.PosSemidef ((rectRightGram A) : Matrix (Fin n) (Fin n) ℝ) :=
  finitePSD.to_matrix_posSemidef
    (rectRightGram A) (rectRightGram_symmetric A) (rectRightGram_finitePSD A)

/-- Exact singular-value squares, defined as the ordered zero-indexed Hermitian
eigenvalues of the exact right Gram `A^T A`.  This does not construct singular
vectors or an SVD. -/
noncomputable def rectSingularValueSq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => (rectRightGram_matrix_posSemidef A).1.eigenvalues₀
    (finCardIndex n j)

/-- Exact singular values, obtained by square-rooting the right-Gram
eigenvalues. -/
noncomputable def rectSingularValue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (rectSingularValueSq A j)

/-- Basis-indexed exact eigenvalues of the right Gram `A^T A`.  This index is
the one used by mathlib's Hermitian eigenvector basis; it is intentionally
separate from the ordered zero-indexed sequence `rectSingularValueSq`. -/
noncomputable def rectRightGramEigenvalue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => (rectRightGram_matrix_posSemidef A).1.eigenvalues j

/-- Exact right-Gram eigenvector table, represented as a real square matrix.
Its columns are the mathlib Hermitian eigenvectors of the exact analysis Gram
`A^T A`.  Implementation-facing theorems must separately certify any computed
singular-vector table. -/
noncomputable def rectRightGramEigenbasis {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    ((Matrix.IsHermitian.eigenvectorUnitary
      (rectRightGram_matrix_posSemidef A).1 :
      Matrix (Fin n) (Fin n) ℝ) i j)

/-- Basis-indexed exact singular values attached to
`rectRightGramEigenbasis`. -/
noncomputable def rectRightGramBasisSingularValue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (rectRightGramEigenvalue A j)

/-- The right-Gram eigenvector table is orthogonal. -/
theorem rectRightGramEigenbasis_isOrthogonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    IsOrthogonal n (rectRightGramEigenbasis A) := by
  constructor
  · intro i j
    let U :=
      Matrix.IsHermitian.eigenvectorUnitary
        (rectRightGram_matrix_posSemidef A).1
    have h := Unitary.coe_star_mul_self U
    have hij := congr_fun (congr_fun h i) j
    simpa [rectRightGramEigenbasis, U, Matrix.mul_apply, Matrix.one_apply,
      matTranspose, idMatrix] using hij
  · intro i j
    let U :=
      Matrix.IsHermitian.eigenvectorUnitary
        (rectRightGram_matrix_posSemidef A).1
    have h := Unitary.coe_mul_star_self U
    have hij := congr_fun (congr_fun h i) j
    simpa [rectRightGramEigenbasis, U, Matrix.mul_apply, Matrix.one_apply,
      matTranspose, idMatrix] using hij

/-- Column orthonormality of the right-Gram eigenvector table. -/
theorem rectRightGramEigenbasis_col_orthonormal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i j : Fin n) :
    ∑ k : Fin n,
        rectRightGramEigenbasis A k i *
          rectRightGramEigenbasis A k j =
      idMatrix n i j := by
  simpa [idMatrix] using
    (rectRightGramEigenbasis_isOrthogonal A).col_orthonormal i j

/-- Row orthonormality of the right-Gram eigenvector table. -/
theorem rectRightGramEigenbasis_row_orthonormal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i j : Fin n) :
    ∑ k : Fin n,
        rectRightGramEigenbasis A i k *
          rectRightGramEigenbasis A j k =
      idMatrix n i j := by
  simpa [idMatrix] using
    (rectRightGramEigenbasis_isOrthogonal A).row_orthonormal i j

/-- Basis-indexed right-Gram eigenvalues are nonnegative because
`A^T A` is positive semidefinite. -/
theorem rectRightGramEigenvalue_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ rectRightGramEigenvalue A j := by
  let hpsd := rectRightGram_matrix_posSemidef A
  simpa [rectRightGramEigenvalue, hpsd] using hpsd.eigenvalues_nonneg j

/-- Basis-indexed right-Gram singular values are nonnegative. -/
theorem rectRightGramBasisSingularValue_nonneg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ rectRightGramBasisSingularValue A j := by
  unfold rectRightGramBasisSingularValue
  exact Real.sqrt_nonneg _

/-- Squaring a basis-indexed right-Gram singular value recovers its
basis-indexed eigenvalue. -/
theorem rectRightGramBasisSingularValue_sq_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (j : Fin n) :
    (rectRightGramBasisSingularValue A j) ^ 2 =
      rectRightGramEigenvalue A j := by
  unfold rectRightGramBasisSingularValue
  exact Real.sq_sqrt (rectRightGramEigenvalue_nonneg A j)

/-- Each column of `rectRightGramEigenbasis` is an eigenvector of the exact
right Gram, with basis-indexed eigenvalue `rectRightGramEigenvalue`. -/
theorem rectRightGramEigenbasis_eigenvector {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a j : Fin n) :
    ∑ k : Fin n,
        rectRightGram A j k * rectRightGramEigenbasis A k a =
      rectRightGramEigenvalue A a * rectRightGramEigenbasis A j a := by
  let hG := (rectRightGram_matrix_posSemidef A).1
  have h := hG.mulVec_eigenvectorBasis a
  have hj := congr_fun h j
  simpa [rectRightGramEigenbasis, rectRightGramEigenvalue, hG, Matrix.mulVec,
    Matrix.IsHermitian.eigenvectorUnitary_apply] using hj

/-- Exact diagonalization of the right Gram by the right-Gram eigenvector table:
`V^T (A^T A) V` is diagonal with the basis-indexed eigenvalues. -/
theorem rectRightGramEigenbasis_diagonalizes {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b) =
      if a = b then rectRightGramEigenvalue A a else 0 := by
  have heig :
      ∀ j : Fin n,
        ∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b =
          rectRightGramEigenvalue A b *
            rectRightGramEigenbasis A j b := by
    intro j
    exact rectRightGramEigenbasis_eigenvector A b j
  have horth :
      ∑ j : Fin n,
          rectRightGramEigenbasis A j a *
            rectRightGramEigenbasis A j b =
        idMatrix n a b :=
    rectRightGramEigenbasis_col_orthonormal A a b
  calc
    ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b)
        =
          ∑ j : Fin n,
            rectRightGramEigenbasis A j a *
              (rectRightGramEigenvalue A b *
                rectRightGramEigenbasis A j b) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [heig j]
    _ =
          rectRightGramEigenvalue A b *
            (∑ j : Fin n,
              rectRightGramEigenbasis A j a *
                rectRightGramEigenbasis A j b) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = if a = b then rectRightGramEigenvalue A a else 0 := by
            by_cases hab : a = b
            · subst b
              simp [horth, idMatrix]
            · simp [horth, idMatrix, hab]

/-- Singular-value-square form of the right-Gram diagonalization. -/
theorem rectRightGramEigenbasis_diagonalizes_singularValueSq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b) =
      if a = b then (rectRightGramBasisSingularValue A a) ^ 2 else 0 := by
  rw [rectRightGramEigenbasis_diagonalizes]
  by_cases hab : a = b
  · simp [hab, rectRightGramBasisSingularValue_sq_eq]
  · simp [hab]

/-- The exact column `A v_a`, where `v_a` is a basis-indexed right-Gram
eigenvector. -/
noncomputable def rectRightGramProjectedColumn {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i a => ∑ j : Fin n, A i j * rectRightGramEigenbasis A j a

/-- Left singular-vector candidates obtained from the basis-indexed
right-Gram eigenbasis by `u_a = A v_a / tau_a`.  The main orthonormality and
reconstruction theorem below requires strict positivity of every displayed
basis-indexed singular value. -/
noncomputable def rectRightGramLeftSingularFromEigenbasis {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i a =>
    (1 / rectRightGramBasisSingularValue A a) *
      rectRightGramProjectedColumn A i a

/-- The dot product of projected columns `A v_a` and `A v_b` is the corresponding
right-Gram quadratic form. -/
theorem rectRightGramProjectedColumn_dot {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ i : Fin m,
        rectRightGramProjectedColumn A i a *
          rectRightGramProjectedColumn A i b =
      ∑ j : Fin n,
        rectRightGramEigenbasis A j a *
          (∑ k : Fin n,
            rectRightGram A j k * rectRightGramEigenbasis A k b) := by
  classical
  unfold rectRightGramProjectedColumn rectRightGram
  calc
    ∑ i : Fin m,
        (∑ j : Fin n, A i j * rectRightGramEigenbasis A j a) *
          (∑ k : Fin n, A i k * rectRightGramEigenbasis A k b)
        =
          ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
            (A i j * rectRightGramEigenbasis A j a) *
              (A i k * rectRightGramEigenbasis A k b) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
    _ =
          ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
            rectRightGramEigenbasis A j a *
              ((A i j * A i k) * rectRightGramEigenbasis A k b) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ =
          ∑ j : Fin n,
            rectRightGramEigenbasis A j a *
              (∑ k : Fin n,
                (∑ i : Fin m, A i j * A i k) *
                  rectRightGramEigenbasis A k b) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            calc
              ∑ i : Fin m,
                  rectRightGramEigenbasis A j a *
                    ((A i j * A i k) *
                      rectRightGramEigenbasis A k b)
                  =
                    rectRightGramEigenbasis A j a *
                      (∑ i : Fin m,
                        (A i j * A i k) *
                          rectRightGramEigenbasis A k b) := by
                    rw [Finset.mul_sum]
              _ =
                    rectRightGramEigenbasis A j a *
                      ((∑ i : Fin m, A i j * A i k) *
                        rectRightGramEigenbasis A k b) := by
                    rw [Finset.sum_mul]
    _ =
          ∑ j : Fin n,
            rectRightGramEigenbasis A j a *
              (∑ k : Fin n,
                (∑ i : Fin m, A i j * A i k) *
                  rectRightGramEigenbasis A k b) := rfl

/-- Diagonal form of `rectRightGramProjectedColumn_dot`. -/
theorem rectRightGramProjectedColumn_dot_diagonal {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a b : Fin n) :
    ∑ i : Fin m,
        rectRightGramProjectedColumn A i a *
          rectRightGramProjectedColumn A i b =
      if a = b then (rectRightGramBasisSingularValue A a) ^ 2 else 0 := by
  rw [rectRightGramProjectedColumn_dot]
  exact rectRightGramEigenbasis_diagonalizes_singularValueSq A a b

/-- The squared norm of the projected column `A v_a` is the corresponding
basis-indexed singular value squared. -/
theorem rectRightGramProjectedColumn_normSq_eq_singularValue_sq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n) :
    ∑ i : Fin m, (rectRightGramProjectedColumn A i a) ^ 2 =
      (rectRightGramBasisSingularValue A a) ^ 2 := by
  have h := rectRightGramProjectedColumn_dot_diagonal A a a
  simpa [pow_two] using h

/-- Eigenvalue form of the projected-column squared-norm identity. -/
theorem rectRightGramProjectedColumn_normSq_eq_eigenvalue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n) :
    ∑ i : Fin m, (rectRightGramProjectedColumn A i a) ^ 2 =
      rectRightGramEigenvalue A a := by
  rw [rectRightGramProjectedColumn_normSq_eq_singularValue_sq,
    rectRightGramBasisSingularValue_sq_eq]

/-- A zero basis-indexed right-Gram singular value forces the corresponding
projected column `A v_a` to vanish coordinatewise. -/
theorem rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n)
    (hτ : rectRightGramBasisSingularValue A a = 0)
    (i : Fin m) :
    rectRightGramProjectedColumn A i a = 0 := by
  have hsum :
      ∑ k : Fin m, (rectRightGramProjectedColumn A k a) ^ 2 = 0 := by
    simpa [hτ] using
      rectRightGramProjectedColumn_normSq_eq_singularValue_sq A a
  have hterm :
      (rectRightGramProjectedColumn A i a) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => sq_nonneg (rectRightGramProjectedColumn A k a))).mp
      hsum i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hterm

/-- Eigenvalue-zero variant of
`rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero`. -/
theorem rectRightGramProjectedColumn_eq_zero_of_eigenvalue_eq_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n)
    (hα : rectRightGramEigenvalue A a = 0)
    (i : Fin m) :
    rectRightGramProjectedColumn A i a = 0 := by
  apply rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero A a
  have hsq :
      (rectRightGramBasisSingularValue A a) ^ 2 = 0 := by
    simpa [hα] using rectRightGramBasisSingularValue_sq_eq A a
  exact sq_eq_zero_iff.mp hsq

/-- Zero-safe left singular-vector candidates.  When the basis-indexed singular
value vanishes we set the candidate column to zero; otherwise it is
`A v_a / tau_a`. -/
noncomputable def rectRightGramLeftSingularZeroSafe {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ := by
  classical
  exact fun i a =>
    if rectRightGramBasisSingularValue A a = 0 then 0
    else
      (1 / rectRightGramBasisSingularValue A a) *
        rectRightGramProjectedColumn A i a

/-- Away from zero singular values, the zero-safe left candidate is the usual
normalized projected column. -/
theorem rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (a : Fin n)
    (hτ : rectRightGramBasisSingularValue A a ≠ 0)
    (i : Fin m) :
    rectRightGramLeftSingularZeroSafe A i a =
      (1 / rectRightGramBasisSingularValue A a) *
        rectRightGramProjectedColumn A i a := by
  classical
  simp [rectRightGramLeftSingularZeroSafe, hτ]

/-- The zero-safe left candidates satisfy `tau_a u_a = A v_a` for every basis
index, including zero singular values. -/
theorem rectRightGramLeftSingularZeroSafe_factor_column
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (a : Fin n) :
    rectRightGramBasisSingularValue A a *
        rectRightGramLeftSingularZeroSafe A i a =
      rectRightGramProjectedColumn A i a := by
  classical
  by_cases hτ : rectRightGramBasisSingularValue A a = 0
  · have hy :
        rectRightGramProjectedColumn A i a = 0 :=
      rectRightGramProjectedColumn_eq_zero_of_singularValue_eq_zero A a hτ i
    simp [rectRightGramLeftSingularZeroSafe, hτ, hy]
  · rw [rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
      A a hτ i]
    field_simp [hτ]

/-- If every basis-indexed right-Gram singular value is strictly positive, the
left candidates `A v_a / tau_a` have orthonormal columns. -/
theorem rectRightGramLeftSingularFromEigenbasis_col_orthonormal_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a)
    (a b : Fin n) :
    ∑ i : Fin m,
        rectRightGramLeftSingularFromEigenbasis A i a *
          rectRightGramLeftSingularFromEigenbasis A i b =
      idMatrix n a b := by
  let τ := rectRightGramBasisSingularValue A
  have hdot := rectRightGramProjectedColumn_dot_diagonal A a b
  calc
    ∑ i : Fin m,
        rectRightGramLeftSingularFromEigenbasis A i a *
          rectRightGramLeftSingularFromEigenbasis A i b
        =
          (1 / τ a) * (1 / τ b) *
            (∑ i : Fin m,
              rectRightGramProjectedColumn A i a *
                rectRightGramProjectedColumn A i b) := by
            unfold rectRightGramLeftSingularFromEigenbasis
            calc
              ∑ i : Fin m,
                  1 / rectRightGramBasisSingularValue A a *
                      rectRightGramProjectedColumn A i a *
                    (1 / rectRightGramBasisSingularValue A b *
                      rectRightGramProjectedColumn A i b)
                  =
                    ∑ i : Fin m,
                      ((1 / τ a) * (1 / τ b)) *
                        (rectRightGramProjectedColumn A i a *
                          rectRightGramProjectedColumn A i b) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
              _ =
                    (1 / τ a) * (1 / τ b) *
                      (∑ i : Fin m,
                        rectRightGramProjectedColumn A i a *
                          rectRightGramProjectedColumn A i b) := by
                    rw [Finset.mul_sum]
    _ =
          (1 / τ a) * (1 / τ b) *
            (if a = b then τ a ^ 2 else 0) := by
            rw [hdot]
    _ = idMatrix n a b := by
            by_cases hab : a = b
            · subst b
              have hne : τ a ≠ 0 := ne_of_gt (hpos a)
              simp [idMatrix]
              field_simp [hne]
            · simp [idMatrix, hab]

/-- The zero-safe left candidates are orthonormal on any pair of strictly
positive basis-indexed singular values.  Positivity is needed only for the
displayed columns, not for every singular direction. -/
theorem rectRightGramLeftSingularZeroSafe_col_orthonormal_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {a b : Fin n}
    (ha : 0 < rectRightGramBasisSingularValue A a)
    (hb : 0 < rectRightGramBasisSingularValue A b) :
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramLeftSingularZeroSafe A i b =
      idMatrix n a b := by
  let τ := rectRightGramBasisSingularValue A
  have hane : τ a ≠ 0 := ne_of_gt ha
  have hbne : τ b ≠ 0 := ne_of_gt hb
  have hdot := rectRightGramProjectedColumn_dot_diagonal A a b
  calc
    ∑ i : Fin m,
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramLeftSingularZeroSafe A i b
        =
          (1 / τ a) * (1 / τ b) *
            (∑ i : Fin m,
              rectRightGramProjectedColumn A i a *
                rectRightGramProjectedColumn A i b) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
              A a hane i,
              rectRightGramLeftSingularZeroSafe_eq_inv_mul_of_singularValue_ne_zero
                A b hbne i]
            ring
    _ =
          (1 / τ a) * (1 / τ b) *
            (if a = b then τ a ^ 2 else 0) := by
            rw [hdot]
    _ = idMatrix n a b := by
            by_cases hab : a = b
            · subst b
              simp [idMatrix]
              field_simp [hane]
            · simp [idMatrix, hab]

/-- Expanding in the exact right-Gram eigenbasis reconstructs every row of
`A`. -/
theorem rectRightGramProjectedColumn_reconstruct {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    ∑ a : Fin n,
        rectRightGramProjectedColumn A i a *
          rectRightGramEigenbasis A j a =
      A i j := by
  unfold rectRightGramProjectedColumn
  calc
    ∑ a : Fin n,
        (∑ k : Fin n, A i k * rectRightGramEigenbasis A k a) *
          rectRightGramEigenbasis A j a
        =
          ∑ k : Fin n,
            A i k *
              (∑ a : Fin n,
                rectRightGramEigenbasis A k a *
                  rectRightGramEigenbasis A j a) := by
            calc
              ∑ a : Fin n,
                  (∑ k : Fin n, A i k *
                    rectRightGramEigenbasis A k a) *
                    rectRightGramEigenbasis A j a
                  =
                    ∑ a : Fin n, ∑ k : Fin n,
                      (A i k * rectRightGramEigenbasis A k a) *
                        rectRightGramEigenbasis A j a := by
                    apply Finset.sum_congr rfl
                    intro a _
                    rw [Finset.sum_mul]
              _ =
                    ∑ k : Fin n, ∑ a : Fin n,
                      (A i k * rectRightGramEigenbasis A k a) *
                        rectRightGramEigenbasis A j a := by
                    rw [Finset.sum_comm]
              _ =
                    ∑ k : Fin n,
                      A i k *
                        (∑ a : Fin n,
                          rectRightGramEigenbasis A k a *
                            rectRightGramEigenbasis A j a) := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro a _
                    ring
    _ =
          ∑ k : Fin n, A i k * idMatrix n k j := by
            apply Finset.sum_congr rfl
            intro k _
            rw [rectRightGramEigenbasis_row_orthonormal A k j]
    _ = A i j := by
            simp [idMatrix]

/-- Basis-indexed SVD-style reconstruction from the zero-safe left candidates.
This removes the full-positive hypothesis but remains basis-indexed rather than
ordered. -/
theorem rectRightGram_basisSVD_representation {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    A i j =
      ∑ a : Fin n,
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a := by
  rw [← rectRightGramProjectedColumn_reconstruct A i j]
  apply Finset.sum_congr rfl
  intro a _
  have hf := rectRightGramLeftSingularZeroSafe_factor_column A i a
  rw [← hf]
  ring

/-- Exact selected-index head from the zero-safe basis-indexed right-Gram
reconstruction.  This is an analysis object, not a computed SVD routine. -/
noncomputable def rectRightGramBasisSVDHead {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    s.sum fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a

/-- Exact complementary tail from the zero-safe basis-indexed right-Gram
reconstruction.  The complement is taken inside the finite right-index type. -/
noncomputable def rectRightGramBasisSVDTail {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    sᶜ.sum fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a

/-- The selected-index head plus the complementary tail reconstructs `A`
entrywise. -/
theorem rectRightGramBasisSVD_head_add_tail {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n))
    (i : Fin m) (j : Fin n) :
    rectRightGramBasisSVDHead A s i j +
        rectRightGramBasisSVDTail A s i j = A i j := by
  classical
  unfold rectRightGramBasisSVDHead rectRightGramBasisSVDTail
  let term : Fin n → ℝ :=
    fun a =>
      rectRightGramLeftSingularZeroSafe A i a *
        rectRightGramBasisSingularValue A a *
        rectRightGramEigenbasis A j a
  have hpartition :
      s.sum term + sᶜ.sum term =
        ∑ a : Fin n, term a := by
    rw [← Finset.sum_union disjoint_compl_right]
    rw [Finset.union_compl]
  rw [show
      s.sum (fun a =>
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramBasisSingularValue A a *
            rectRightGramEigenbasis A j a) +
        sᶜ.sum (fun a =>
          rectRightGramLeftSingularZeroSafe A i a *
            rectRightGramBasisSingularValue A a *
            rectRightGramEigenbasis A j a) =
        s.sum term + sᶜ.sum term by rfl]
  rw [hpartition]
  exact (rectRightGram_basisSVD_representation A i j).symm

/-- Rank factorization of the selected-index head through its selected
cardinality.  This is still exact-object algebra; it does not choose the
ordered top singular directions. -/
noncomputable def rectRightGramBasisSVDHeadRankFactorization {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (s : Finset (Fin n)) :
    RectRankFactorization m n s.card (rectRightGramBasisSVDHead A s) where
  left := fun i a =>
    rectRightGramLeftSingularZeroSafe A i (s.orderEmbOfFin rfl a)
  right := fun a j =>
    rectRightGramBasisSingularValue A (s.orderEmbOfFin rfl a) *
      rectRightGramEigenbasis A j (s.orderEmbOfFin rfl a)
  factorization := by
    classical
    intro i j
    unfold rectRightGramBasisSVDHead
    let e : Fin s.card → Fin n := fun a => s.orderEmbOfFin rfl a
    let term : Fin n → ℝ :=
      fun a =>
        rectRightGramLeftSingularZeroSafe A i a *
          rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a
    have hsum :
        s.sum term = ∑ a : Fin s.card, term (e a) := by
      have hsub :
          (∑ a : Fin s.card, term (e a)) = ∑ x : s, term x := by
        refine Fintype.sum_equiv (s.orderIsoOfFin rfl).toEquiv
          (fun a : Fin s.card => term (e a))
          (fun x : s => term x) ?_
        intro a
        simp [e]
      calc
        s.sum term = ∑ x : s, term x := by
              simpa using (Finset.sum_coe_sort s term).symm
        _ = ∑ a : Fin s.card, term (e a) := hsub.symm
    rw [hsum]
    apply Finset.sum_congr rfl
    intro a _
    simp [e, term]
    ring

/-- The exact equivalence used by mathlib to reindex the ordered Hermitian
eigenvalue sequence into the matrix's basis-index type.  For the right-Gram
matrix this is also the bridge between ordered singular values and the
basis-indexed eigenvector table. -/
noncomputable def rectRightGramOrderedEigenbasisEquiv (n : ℕ) :
    Fin (Fintype.card (Fin n)) ≃ Fin n :=
  Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))

/-- Ordered singular-value coordinate corresponding to a basis-indexed
right-Gram eigenvector.  This is the inverse of the same finite equivalence
used by mathlib's `eigenvalues` and `eigenvectorBasis` APIs, cast back to the
standard `Fin n` index type. -/
noncomputable def rectRightGramBasisOrderedIndex (n : ℕ) (b : Fin n) : Fin n :=
  Fin.cast (by simp) ((rectRightGramOrderedEigenbasisEquiv n).symm b)

/-- Casting the ordered coordinate back to mathlib's cardinality index recovers
the inverse eigenbasis reindexing. -/
theorem finCardIndex_rectRightGramBasisOrderedIndex (n : ℕ) (b : Fin n) :
    finCardIndex n (rectRightGramBasisOrderedIndex n b) =
      (rectRightGramOrderedEigenbasisEquiv n).symm b := by
  apply Fin.ext
  simp [finCardIndex, rectRightGramBasisOrderedIndex]

/-- A basis-indexed right-Gram singular value is the ordered singular value at
the basis column's inverse mathlib reindexing coordinate. -/
theorem rectRightGramBasisSingularValue_eq_orderedIndex {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin n) :
    rectRightGramBasisSingularValue A b =
      rectSingularValue A (rectRightGramBasisOrderedIndex n b) := by
  unfold rectRightGramBasisSingularValue rectSingularValue
    rectRightGramEigenvalue rectSingularValueSq
    rectRightGramBasisOrderedIndex rectRightGramOrderedEigenbasisEquiv
  simp [finCardIndex, Matrix.IsHermitian.eigenvalues]

/-- The positive basis-indexed singular values convert the left-candidate
definition back into the projected column identity `tau_a u_a=A v_a`. -/
theorem rectRightGramLeftSingularFromEigenbasis_factor_column_of_pos
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a)
    (i : Fin m) (a : Fin n) :
    rectRightGramBasisSingularValue A a *
        rectRightGramLeftSingularFromEigenbasis A i a =
      rectRightGramProjectedColumn A i a := by
  have hne : rectRightGramBasisSingularValue A a ≠ 0 :=
    ne_of_gt (hpos a)
  unfold rectRightGramLeftSingularFromEigenbasis
  field_simp [hne]

/-- Full-positive basis-indexed SVD-style reconstruction from the right-Gram
eigenbasis.  This is exact-object algebra under a visible positivity
hypothesis; it is not yet the ordered rank-deficient rectangular SVD split. -/
theorem rectRightGram_fullPositive_basisSVD_representation {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hpos : ∀ a : Fin n, 0 < rectRightGramBasisSingularValue A a)
    (i : Fin m) (j : Fin n) :
    A i j =
      ∑ a : Fin n,
        rectRightGramLeftSingularFromEigenbasis A i a *
          rectRightGramBasisSingularValue A a *
          rectRightGramEigenbasis A j a := by
  rw [← rectRightGramProjectedColumn_reconstruct A i j]
  apply Finset.sum_congr rfl
  intro a _
  have hf :=
    rectRightGramLeftSingularFromEigenbasis_factor_column_of_pos A hpos i a
  rw [← hf]
  ring

end NumStability
