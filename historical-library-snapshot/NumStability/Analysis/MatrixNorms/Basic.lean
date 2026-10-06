-- Analysis/MatrixNorms/Basic.lean
--
-- Foundational complex-matrix operations and norm definitions.

import Mathlib.Analysis.Matrix.PosDef
import NumStability.Analysis.OperatorNorms.Basic
import NumStability.Analysis.VectorNorms.Duality
import NumStability.Analysis.VectorNorms.Interpolation

/-!
# Basic complex-matrix norm infrastructure

Defines `CMatrix`, matrix multiplication and action, standard concrete matrix
norms, and the basic inequalities shared by the specialized norm families.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Concrete finite complex matrix, represented in the same lightweight style
    as the repository's real matrix code. -/
abbrev CMatrix (m n : ℕ) := Fin m → Fin n → ℂ

/-- Matrix-vector product as a source-facing vector map. -/
noncomputable def complexMatrixVecMul {m n : ℕ} (A : CMatrix m n) :
    ComplexVectorMap n m :=
  fun x i => ∑ j : Fin n, A i j * x j

/-- `Ainv` is a left inverse of `A` through the concrete complex matrix-vector
    action: `Ainv * A` acts as the identity on finite complex vectors. -/
def IsComplexMatrixLeftInverse {n : ℕ} (A Ainv : CMatrix n n) : Prop :=
  ∀ x : CVec n, complexMatrixVecMul Ainv (complexMatrixVecMul A x) = x

/-- `Ainv` is a right inverse of `A` through the concrete complex matrix-vector
    action: `A * Ainv` acts as the identity on finite complex vectors. -/
def IsComplexMatrixRightInverse {n : ℕ} (A Ainv : CMatrix n n) : Prop :=
  ∀ x : CVec n, complexMatrixVecMul A (complexMatrixVecMul Ainv x) = x

/-- Source-facing two-sided inverse predicate for concrete complex matrices. -/
def IsComplexMatrixInverse {n : ℕ} (A Ainv : CMatrix n n) : Prop :=
  IsComplexMatrixLeftInverse A Ainv ∧ IsComplexMatrixRightInverse A Ainv

/-- A two-sided concrete complex matrix inverse gives the left inverse used by
    the perturbation-radius condition-number theorem. -/
theorem isComplexMatrixLeftInverse_of_inverse {n : ℕ} {A Ainv : CMatrix n n}
    (h : IsComplexMatrixInverse A Ainv) :
    IsComplexMatrixLeftInverse A Ainv :=
  h.1

/-- A two-sided concrete complex matrix inverse gives the right inverse. -/
theorem isComplexMatrixRightInverse_of_inverse {n : ℕ} {A Ainv : CMatrix n n}
    (h : IsComplexMatrixInverse A Ainv) :
    IsComplexMatrixRightInverse A Ainv :=
  h.2

/-- Entrywise complex conjugation of a concrete finite complex matrix. -/
noncomputable def complexConjMatrix {m n : ℕ} (A : CMatrix m n) : CMatrix m n :=
  fun i j => star (A i j)

/-- Concrete finite matrix transpose. -/
noncomputable def complexMatrixTranspose {m n : ℕ} (A : CMatrix m n) : CMatrix n m :=
  fun j i => A i j

/-- Concrete finite matrix adjoint, matching Higham's `A^*`. -/
noncomputable def complexMatrixAdjoint {m n : ℕ} (A : CMatrix m n) : CMatrix n m :=
  complexMatrixTranspose (complexConjMatrix A)

/-- Matrix multiplication for the local `CMatrix` abbreviation.  This keeps
    source-facing Chapter 6 product statements independent of overloaded
    Mathlib matrix notation. -/
noncomputable def complexMatrixMul {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) : CMatrix m p :=
  fun i j => Finset.univ.sum (fun k : Fin n => A i k * B k j)

/-- Entrywise absolute value of a complex matrix, embedded back into `ℂ`.
    This is the local source-facing `|A|` used in Problem 6.15. -/
noncomputable def complexAbsMatrix {m n : ℕ} (A : CMatrix m n) : CMatrix m n :=
  fun i j => ((‖A i j‖ : ℝ) : ℂ)

@[simp]
lemma complexAbsMatrix_norm_apply {m n : ℕ} (A : CMatrix m n)
    (i : Fin m) (j : Fin n) :
    ‖complexAbsMatrix A i j‖ = ‖A i j‖ := by
  simp [complexAbsMatrix]

lemma complexMatrixVecMul_absMatrix_absVec_apply
    {m n : ℕ} (A : CMatrix m n) (x : CVec n) (i : Fin m) :
    complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x) i =
      ((Finset.univ.sum (fun j : Fin n => ‖A i j‖ * ‖x j‖) : ℝ) : ℂ) := by
  unfold complexMatrixVecMul complexAbsMatrix complexAbsVec
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Complex.ofReal_mul]

@[simp]
lemma complexMatrixVecMul_absMatrix_absVec_norm_apply
    {m n : ℕ} (A : CMatrix m n) (x : CVec n) (i : Fin m) :
    ‖complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x) i‖ =
      Finset.univ.sum (fun j : Fin n => ‖A i j‖ * ‖x j‖) := by
  rw [complexMatrixVecMul_absMatrix_absVec_apply]
  exact Complex.norm_of_nonneg
    (Finset.sum_nonneg fun j _hj => mul_nonneg (norm_nonneg _) (norm_nonneg _))

@[simp]
lemma complexAbsVec_complexMatrixVecMul_absMatrix_absVec
    {m n : ℕ} (A : CMatrix m n) (x : CVec n) :
    complexAbsVec (complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x)) =
      complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x) := by
  ext i
  have hsum_nonneg :
      0 ≤ Finset.univ.sum (fun j : Fin n => ‖A i j‖ * ‖x j‖) :=
    Finset.sum_nonneg fun j _hj => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [complexAbsVec, complexMatrixVecMul_absMatrix_absVec_apply]
  rw [Complex.norm_of_nonneg hsum_nonneg]

/-- Entrywise absolute matrix-vector domination: `|A x| <= |A| |x|`.
    This is the finite-dimensional inequality used in Appendix A for
    Problem 6.15. -/
lemma complexMatrixVecMul_componentwiseAbsLe_absMatrix
    {m n : ℕ} (A : CMatrix m n) (x : CVec n) :
    componentwiseAbsLe (complexMatrixVecMul A x)
      (complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x)) := by
  intro i
  have htriangle : ‖complexMatrixVecMul A x i‖ ≤
      Finset.univ.sum (fun j : Fin n => ‖A i j * x j‖) := by
    unfold complexMatrixVecMul
    exact norm_sum_le Finset.univ (fun j : Fin n => A i j * x j)
  have hterms : Finset.univ.sum (fun j : Fin n => ‖A i j * x j‖) =
      Finset.univ.sum (fun j : Fin n => ‖A i j‖ * ‖x j‖) := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [norm_mul]
  have hrow_nonneg : 0 ≤
      Finset.univ.sum (fun j : Fin n => ‖A i j‖ * ‖x j‖) := by
    exact Finset.sum_nonneg
      (fun j _hj => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hrow :
      ‖complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x) i‖ =
        Finset.univ.sum (fun j : Fin n => ‖A i j‖ * ‖x j‖) := by
    have hval :
        complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x) i =
          ((Finset.univ.sum (fun j : Fin n => ‖A i j‖ * ‖x j‖) : ℝ) : ℂ) := by
      unfold complexMatrixVecMul complexAbsMatrix complexAbsVec
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Complex.ofReal_mul]
    rw [hval]
    exact Complex.norm_of_nonneg hrow_nonneg
  calc
    ‖complexMatrixVecMul A x i‖
        ≤ Finset.univ.sum (fun j : Fin n => ‖A i j * x j‖) := htriangle
    _ = Finset.univ.sum (fun j : Fin n => ‖A i j‖ * ‖x j‖) := hterms
    _ = ‖complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x) i‖ := hrow.symm

/-- Multiplication by the conjugated matrix is conjugation of the original
    matrix-vector product after conjugating the input. -/
lemma complexMatrixVecMul_conjMatrix {m n : ℕ} (A : CMatrix m n) (x : CVec n) :
    complexMatrixVecMul (complexConjMatrix A) x =
      complexConjVec (complexMatrixVecMul A (complexConjVec x)) := by
  ext i
  unfold complexMatrixVecMul complexConjMatrix complexConjVec
  simp [mul_comm]

lemma complexMatrixVecMul_mul {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) (x : CVec p) :
    complexMatrixVecMul (complexMatrixMul A B) x =
      complexMatrixVecMul A (complexMatrixVecMul B x) := by
  ext i
  simp [complexMatrixVecMul, complexMatrixMul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

lemma complexMatrixMul_assoc {m n p q : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) (C : CMatrix p q) :
    complexMatrixMul (complexMatrixMul A B) C =
      complexMatrixMul A (complexMatrixMul B C) := by
  ext i j
  simp [complexMatrixMul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

lemma complexMatrixAdjoint_mul {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) :
    complexMatrixAdjoint (complexMatrixMul A B) =
      complexMatrixMul (complexMatrixAdjoint B) (complexMatrixAdjoint A) := by
  ext j i
  simp [complexMatrixAdjoint, complexMatrixTranspose, complexConjMatrix, complexMatrixMul,
    mul_comm]

@[simp]
lemma complexMatrixTranspose_transpose {m n : ℕ} (A : CMatrix m n) :
    complexMatrixTranspose (complexMatrixTranspose A) = A := by
  rfl

/-- Finite transpose pairing identity:
    `<A^T y, x> = <y, A x>` for the bilinear row pairing used in this file. -/
lemma complexMatrixTranspose_pairing {m n : ℕ} (A : CMatrix m n)
    (x : CVec n) (y : CVec m) :
    (∑ j : Fin n, complexMatrixVecMul (complexMatrixTranspose A) y j * x j) =
      ∑ i : Fin m, y i * complexMatrixVecMul A x i := by
  unfold complexMatrixVecMul complexMatrixTranspose
  calc
    (∑ j : Fin n, (∑ i : Fin m, A i j * y i) * x j)
        = ∑ j : Fin n, ∑ i : Fin m, (A i j * y i) * x j := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.sum_mul]
    _ = ∑ i : Fin m, ∑ j : Fin n, (A i j * y i) * x j := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin m, y i * ∑ j : Fin n, A i j * x j := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring

/-- Support of a fixed row of a complex matrix. -/
noncomputable def complexMatrixRowSupport {m n : ℕ} (A : CMatrix m n)
    (i : Fin m) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin n => A i j ≠ 0)

/-- Support of a fixed column of a complex matrix. -/
noncomputable def complexMatrixColumnSupport {m n : ℕ} (A : CMatrix m n)
    (j : Fin n) : Finset (Fin m) :=
  (Finset.univ.filter fun i : Fin m => A i j ≠ 0)

/-- Source-facing row sparsity: every row has at most `μ` nonzero entries. -/
def complexMatrixRowsSupportCardLe {m n : ℕ} (A : CMatrix m n) (μ : ℕ) : Prop :=
  ∀ i : Fin m, (complexMatrixRowSupport A i).card ≤ μ

/-- Source-facing column sparsity: every column has at most `μ` nonzero entries. -/
def complexMatrixColumnsSupportCardLe {m n : ℕ} (A : CMatrix m n) (μ : ℕ) : Prop :=
  ∀ j : Fin n, (complexMatrixColumnSupport A j).card ≤ μ

/-- Row-sparse coordinate estimate behind Higham Problem 6.14: if every row of
    `A` has at most `μ` nonzeros, then each coordinate of `A x` is controlled
    by the `L^p` norm of the corresponding rowwise product vector with the
    sparse Holder factor `μ^(1-1/p)`. -/
theorem complexMatrixVecMul_row_norm_le_sparseRow_rpow_mul_lpProduct
    {m n μ : ℕ} {p : ℝ} (hp : 1 ≤ p) {A : CMatrix m n}
    (hrows : complexMatrixRowsSupportCardLe A μ) (x : CVec n) (i : Fin m) :
    ‖complexMatrixVecMul A x i‖ ≤
      (μ : ℝ) ^ (1 - p⁻¹) *
        complexVecLpNorm (ENNReal.ofReal p) (fun j : Fin n => A i j * x j) := by
  let rowProd : CVec n := fun j : Fin n => A i j * x j
  have hsupport :
      (complexVecSupport rowProd).card ≤ μ := by
    calc
      (complexVecSupport rowProd).card
          ≤ (complexVecSupport (fun j : Fin n => A i j)).card := by
            simpa [rowProd] using
              complexVecSupport_mul_left_card_le (fun j : Fin n => A i j) x
      _ = (complexMatrixRowSupport A i).card := by
            rfl
      _ ≤ μ := hrows i
  have hsum :
      ‖complexMatrixVecMul A x i‖ ≤ complexVecOneNorm rowProd := by
    unfold complexMatrixVecMul complexVecOneNorm rowProd
    simpa using norm_sum_le Finset.univ (fun j : Fin n => A i j * x j)
  exact hsum.trans
    (complexVecOneNorm_le_supportCard_rpow_mul_complexVecLpNorm hp rowProd hsupport)

lemma complexMatrix_rowSupport_sum_le_columnsSupportCard_mul
    {m n μ : ℕ} {A : CMatrix m n}
    (hcols : complexMatrixColumnsSupportCardLe A μ) (f : Fin n → ℝ)
    (hf : ∀ j : Fin n, 0 ≤ f j) :
    (∑ i : Fin m, (complexMatrixRowSupport A i).sum f) ≤
      (μ : ℝ) * ∑ j : Fin n, f j := by
  classical
  have hswap :
      (∑ i : Fin m, (complexMatrixRowSupport A i).sum f) =
        ∑ j : Fin n, (complexMatrixColumnSupport A j).sum
          (fun _i : Fin m => f j) := by
    simp [complexMatrixRowSupport, complexMatrixColumnSupport, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite, nsmul_eq_mul]
  calc
    (∑ i : Fin m, (complexMatrixRowSupport A i).sum f)
        = ∑ j : Fin n, (complexMatrixColumnSupport A j).sum
          (fun _i : Fin m => f j) := hswap
    _ = ∑ j : Fin n,
          ((complexMatrixColumnSupport A j).card : ℝ) * f j := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [nsmul_eq_mul]
    _ ≤ ∑ j : Fin n, (μ : ℝ) * f j := by
            apply Finset.sum_le_sum
            intro j _hj
            have hcard : ((complexMatrixColumnSupport A j).card : ℝ) ≤ (μ : ℝ) := by
              exact_mod_cast hcols j
            exact mul_le_mul_of_nonneg_right hcard (hf j)
    _ = (μ : ℝ) * ∑ j : Fin n, f j := by
            rw [Finset.mul_sum]

/-- Concrete complex matrix 1-norm, the maximum absolute column sum. -/
noncomputable def complexMatrixOneNorm {m n : ℕ} (A : CMatrix m n) : ℝ :=
  let f : Fin n → NNReal := fun j => ∑ i : Fin m, ‖A i j‖₊
  ((Finset.univ.sup f : NNReal) : ℝ)

/-- The concrete matrix 1-norm is exactly the maximum of the column 1-norms. -/
theorem complexMatrixOneNorm_eq_max_column_oneNorm {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixOneNorm A =
      ((Finset.univ.sup (fun j : Fin n => ∑ i : Fin m, ‖A i j‖₊) : NNReal) : ℝ) := by
  rfl

lemma complexMatrixOneNorm_nonneg {m n : ℕ} (A : CMatrix m n) :
    0 ≤ complexMatrixOneNorm A := by
  unfold complexMatrixOneNorm
  exact NNReal.coe_nonneg _

lemma complexMatrixOneNorm_col_sum_le {m n : ℕ} (A : CMatrix m n) (j : Fin n) :
    (∑ i : Fin m, ‖A i j‖) ≤ complexMatrixOneNorm A := by
  unfold complexMatrixOneNorm
  let f : Fin n → NNReal := fun j => ∑ i : Fin m, ‖A i j‖₊
  have hnn : f j ≤ Finset.univ.sup f :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin n))) (f := f) (Finset.mem_univ j)
  have hreal : ((f j : NNReal) : ℝ) ≤ ((Finset.univ.sup f : NNReal) : ℝ) := by
    exact_mod_cast hnn
  simpa [f, NNReal.coe_sum] using hreal

/-- Equation (6.12), p = 1 lower-bound form: each column 1-norm is bounded
    by the induced matrix 1-norm. -/
theorem complexMatrixOneNorm_column_oneNorm_le {m n : ℕ}
    (A : CMatrix m n) (j : Fin n) :
    complexVecOneNorm (fun i : Fin m => A i j) ≤ complexMatrixOneNorm A := by
  simpa [complexVecOneNorm] using complexMatrixOneNorm_col_sum_le A j

/-- Entrywise absolute value preserves the concrete complex matrix 1-norm. -/
theorem complexMatrixOneNorm_absMatrix_eq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixOneNorm (complexAbsMatrix A) = complexMatrixOneNorm A := by
  unfold complexMatrixOneNorm
  apply congrArg (fun r : NNReal => (r : ℝ))
  refine Finset.sup_congr rfl ?_
  intro j _hj
  apply Finset.sum_congr rfl
  intro i _hi
  simp [complexAbsMatrix]

/-- Endpoint `p = 1` form of the absolute-matrix bounds in Higham
    Problem 6.15. -/
theorem complexMatrixOneNorm_absMatrix_bounds {m n : ℕ} (A : CMatrix m n) :
    complexMatrixOneNorm A ≤ complexMatrixOneNorm (complexAbsMatrix A) ∧
      complexMatrixOneNorm (complexAbsMatrix A) ≤ complexMatrixOneNorm A := by
  have h := complexMatrixOneNorm_absMatrix_eq A
  exact ⟨le_of_eq h.symm, le_of_eq h⟩

lemma complexMatrixOneNorm_le_of_col_sum_le {m n : ℕ} {A : CMatrix m n}
    {d : ℝ} (hd : 0 ≤ d)
    (hcols : ∀ j : Fin n, (∑ i : Fin m, ‖A i j‖) ≤ d) :
    complexMatrixOneNorm A ≤ d := by
  unfold complexMatrixOneNorm
  let f : Fin n → NNReal := fun j => ∑ i : Fin m, ‖A i j‖₊
  have hcols_nn : ∀ j, f j ≤ Real.toNNReal d := by
    intro j
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal d hd]
    simpa [f, NNReal.coe_sum] using hcols j
  have hsup : Finset.univ.sup f ≤ Real.toNNReal d :=
    Finset.sup_le (fun j _ => hcols_nn j)
  have hreal : ((Finset.univ.sup f : NNReal) : ℝ) ≤ d := by
    rw [← Real.coe_toNNReal d hd]
    exact_mod_cast hsup
  simpa [f] using hreal

/-- Concrete complex matrix infinity norm, the maximum absolute row sum. -/
noncomputable def complexMatrixInfNorm {m n : ℕ} (A : CMatrix m n) : ℝ :=
  let f : Fin m → NNReal := fun i => ∑ j : Fin n, ‖A i j‖₊
  ((Finset.univ.sup f : NNReal) : ℝ)

/-- The concrete matrix infinity norm is exactly the maximum of the row
    1-norms. -/
theorem complexMatrixInfNorm_eq_max_row_oneNorm {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixInfNorm A =
      ((Finset.univ.sup (fun i : Fin m => ∑ j : Fin n, ‖A i j‖₊) : NNReal) : ℝ) := by
  rfl

lemma complexMatrixInfNorm_nonneg {m n : ℕ} (A : CMatrix m n) :
    0 ≤ complexMatrixInfNorm A := by
  unfold complexMatrixInfNorm
  exact NNReal.coe_nonneg _

lemma complexMatrixInfNorm_row_sum_le {m n : ℕ} (A : CMatrix m n) (i : Fin m) :
    (∑ j : Fin n, ‖A i j‖) ≤ complexMatrixInfNorm A := by
  unfold complexMatrixInfNorm
  let f : Fin m → NNReal := fun i => ∑ j : Fin n, ‖A i j‖₊
  have hnn : f i ≤ Finset.univ.sup f :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin m))) (f := f) (Finset.mem_univ i)
  have hreal : ((f i : NNReal) : ℝ) ≤ ((Finset.univ.sup f : NNReal) : ℝ) := by
    exact_mod_cast hnn
  simpa [f, NNReal.coe_sum] using hreal

/-- Equation (6.13), p = infinity lower-bound form: each row 1-norm is
    bounded by the induced matrix infinity norm. -/
theorem complexMatrixInfNorm_row_oneNorm_le {m n : ℕ}
    (A : CMatrix m n) (i : Fin m) :
    complexVecOneNorm (fun j : Fin n => A i j) ≤ complexMatrixInfNorm A := by
  simpa [complexVecOneNorm] using complexMatrixInfNorm_row_sum_le A i

/-- Entrywise absolute value preserves the concrete complex matrix infinity
    norm. -/
theorem complexMatrixInfNorm_absMatrix_eq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixInfNorm (complexAbsMatrix A) = complexMatrixInfNorm A := by
  unfold complexMatrixInfNorm
  apply congrArg (fun r : NNReal => (r : ℝ))
  refine Finset.sup_congr rfl ?_
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  simp [complexAbsMatrix]

/-- Endpoint `p = infinity` form of the absolute-matrix bounds in Higham
    Problem 6.15. -/
theorem complexMatrixInfNorm_absMatrix_bounds {m n : ℕ} (A : CMatrix m n) :
    complexMatrixInfNorm A ≤ complexMatrixInfNorm (complexAbsMatrix A) ∧
      complexMatrixInfNorm (complexAbsMatrix A) ≤ complexMatrixInfNorm A := by
  have h := complexMatrixInfNorm_absMatrix_eq A
  exact ⟨le_of_eq h.symm, le_of_eq h⟩

lemma complexMatrixInfNorm_le_of_row_sum_le {m n : ℕ} {A : CMatrix m n}
    {d : ℝ} (hd : 0 ≤ d)
    (hrows : ∀ i : Fin m, (∑ j : Fin n, ‖A i j‖) ≤ d) :
    complexMatrixInfNorm A ≤ d := by
  unfold complexMatrixInfNorm
  let f : Fin m → NNReal := fun i => ∑ j : Fin n, ‖A i j‖₊
  have hrows_nn : ∀ i, f i ≤ Real.toNNReal d := by
    intro i
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal d hd]
    simpa [f, NNReal.coe_sum] using hrows i
  have hsup : Finset.univ.sup f ≤ Real.toNNReal d :=
    Finset.sup_le (fun i _ => hrows_nn i)
  have hreal : ((Finset.univ.sup f : NNReal) : ℝ) ≤ d := by
    rw [← Real.coe_toNNReal d hd]
    exact_mod_cast hsup
  simpa [f] using hreal

lemma complexMatrixVecMul_standardBasisCVec {m n : ℕ}
    (A : CMatrix m n) (j : Fin n) :
    complexMatrixVecMul A (standardBasisCVec j) = fun i : Fin m => A i j := by
  ext i
  unfold complexMatrixVecMul standardBasisCVec
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Problem 6.16 matrix expression: maximum over columns of the real-imaginary
    absolute column sum `Σ_i (|Re A_ij| + |Im A_ij|)`. -/
noncomputable def complexMatrixRealImagOneNorm {m n : ℕ} (A : CMatrix m n) : ℝ :=
  let f : Fin n → NNReal := fun j => ∑ i : Fin m, complexRealImagAbsNN (A i j)
  ((Finset.univ.sup f : NNReal) : ℝ)

lemma complexMatrixRealImagOneNorm_nonneg {m n : ℕ} (A : CMatrix m n) :
    0 ≤ complexMatrixRealImagOneNorm A := by
  unfold complexMatrixRealImagOneNorm
  exact NNReal.coe_nonneg _

lemma complexMatrixRealImagOneNorm_col_sum_le {m n : ℕ}
    (A : CMatrix m n) (j : Fin n) :
    (∑ i : Fin m, complexRealImagAbs (A i j)) ≤
      complexMatrixRealImagOneNorm A := by
  unfold complexMatrixRealImagOneNorm
  let f : Fin n → NNReal := fun j => ∑ i : Fin m, complexRealImagAbsNN (A i j)
  have hnn : f j ≤ Finset.univ.sup f :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin n))) (f := f) (Finset.mem_univ j)
  have hreal : ((f j : NNReal) : ℝ) ≤ ((Finset.univ.sup f : NNReal) : ℝ) := by
    exact_mod_cast hnn
  simpa [f, NNReal.coe_sum] using hreal

lemma complexMatrixRealImagOneNorm_column_value_of_sup
    {m n : ℕ} (A : CMatrix m n) (j : Fin n)
    (hsup :
      (Finset.univ.sup
        (fun j : Fin n => ∑ i : Fin m, complexRealImagAbsNN (A i j))) =
        ∑ i : Fin m, complexRealImagAbsNN (A i j)) :
    complexMatrixRealImagOneNorm A =
      complexVecRealImagOneNorm (fun i : Fin m => A i j) := by
  let f : Fin n → NNReal := fun j => ∑ i : Fin m, complexRealImagAbsNN (A i j)
  have hsup' : Finset.univ.sup f = f j := by
    simpa [f] using hsup
  unfold complexMatrixRealImagOneNorm complexVecRealImagOneNorm
  change ((Finset.univ.sup f : NNReal) : ℝ) =
    ∑ i : Fin m, complexRealImagAbs (A i j)
  rw [hsup']
  simp [f, NNReal.coe_sum]

lemma complexMatrixVecMul_realImagOneNorm_le {m n : ℕ}
    (A : CMatrix m n) (x : CVec n) :
    complexVecRealImagOneNorm (complexMatrixVecMul A x) ≤
      complexMatrixRealImagOneNorm A * complexVecRealImagOneNorm x := by
  unfold complexVecRealImagOneNorm complexMatrixVecMul
  calc
    (∑ i : Fin m, complexRealImagAbs (∑ j : Fin n, A i j * x j))
        ≤ ∑ i : Fin m, ∑ j : Fin n, complexRealImagAbs (A i j * x j) := by
          exact Finset.sum_le_sum (fun i _hi =>
            complexRealImagAbs_sum_le Finset.univ (fun j : Fin n => A i j * x j))
    _ ≤ ∑ i : Fin m, ∑ j : Fin n,
          complexRealImagAbs (A i j) * complexRealImagAbs (x j) := by
          exact Finset.sum_le_sum (fun i _hi =>
            Finset.sum_le_sum (fun j _hj => complexRealImagAbs_mul_le (A i j) (x j)))
    _ = ∑ j : Fin n, (∑ i : Fin m, complexRealImagAbs (A i j)) *
          complexRealImagAbs (x j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.sum_mul]
    _ ≤ ∑ j : Fin n, complexMatrixRealImagOneNorm A *
          complexRealImagAbs (x j) := by
          exact Finset.sum_le_sum (fun j _hj =>
            mul_le_mul_of_nonneg_right
              (complexMatrixRealImagOneNorm_col_sum_le A j)
              (complexRealImagAbs_nonneg (x j)))
    _ = complexMatrixRealImagOneNorm A *
          ∑ j : Fin n, complexRealImagAbs (x j) := by
          rw [Finset.mul_sum]

/-- The `i`th row of a complex matrix as a complex linear functional. -/
noncomputable def complexMatrixRowFunctional {m n : ℕ}
    (A : CMatrix m n) (i : Fin m) : CVec n → ℂ :=
  fun x => complexMatrixVecMul A x i

lemma complexMatrixRowFunctional_apply {m n : ℕ}
    (A : CMatrix m n) (i : Fin m) (x : CVec n) :
    complexMatrixRowFunctional A i x = ∑ j : Fin n, A i j * x j := by
  rfl

lemma complexMatrixRowFunctional_standardBasisCVec {m n : ℕ}
    (A : CMatrix m n) (i : Fin m) (j : Fin n) :
    complexMatrixRowFunctional A i (standardBasisCVec j) = A i j := by
  have h := congr_fun (complexMatrixVecMul_standardBasisCVec A j) i
  simpa [complexMatrixRowFunctional] using h

lemma complexMatrixRowFunctional_linear {m n : ℕ}
    (A : CMatrix m n) (i : Fin m) :
    IsComplexLinearForm (complexMatrixRowFunctional A i) := by
  constructor
  · intro x y
    unfold complexMatrixRowFunctional complexMatrixVecMul complexVecAdd
    calc
      (∑ j : Fin n, A i j * (x j + y j)) =
          ∑ j : Fin n, (A i j * x j + A i j * y j) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
      _ = (∑ j : Fin n, A i j * x j) + ∑ j : Fin n, A i j * y j := by
            rw [Finset.sum_add_distrib]
  · intro a x
    unfold complexMatrixRowFunctional complexMatrixVecMul complexVecSMul
    calc
      (∑ j : Fin n, A i j * (a * x j)) =
          ∑ j : Fin n, a * (A i j * x j) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
      _ = a * ∑ j : Fin n, A i j * x j := by
            rw [Finset.mul_sum]

/-- Hölder gives the row functional induced by a row vector a dual upper
    bound equal to the row's `L^q` norm, for finite conjugate exponents. -/
theorem complexMatrixRowFunctional_lpDualBound {m n : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : CMatrix m n) (i : Fin m) :
    DualFunctionalBound (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexMatrixRowFunctional A i)
      (complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) := by
  intro x
  rw [complexMatrixRowFunctional_apply]
  exact complexVecLpNorm_holder hpq (fun j : Fin n => A i j) x

/-- Finite complex `L^p`/`L^q` duality for a matrix row functional, packaged in
    the repository's least-dual-bound API. The nonempty source dimension is
    needed because the local `DualFunctionalBound` type is real-valued and does
    not itself require bounds to be nonnegative. -/
theorem complexMatrixRowFunctional_lpDualValue {m n : ℕ} (hn : 0 < n)
    {p q : ℝ} (hpq : p.HolderConjugate q) (A : CMatrix m n) (i : Fin m) :
    IsDualFunctionalNormValue (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexMatrixRowFunctional A i)
      (complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) := by
  refine ⟨complexMatrixRowFunctional_linear A i,
    complexMatrixRowFunctional_lpDualBound hpq A i, ?_⟩
  intro e he
  have he_nonneg : 0 ≤ e := by
    haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [ENNReal.one_le_ofReal]
      exact le_of_lt hpq.lt⟩
    obtain ⟨u, hu_unit⟩ :=
      exists_unit_complexVectorNorm
        (complexVecLpNorm_isComplexVectorNorm (n := n) (ENNReal.ofReal p)) hn
    have h := he u
    rw [hu_unit, mul_one] at h
    exact (norm_nonneg (complexMatrixRowFunctional A i u)).trans h
  exact complexVecLpNorm_le_of_rowFunctional_bound hpq
    (fun j : Fin n => A i j) he_nonneg
    (by
      intro x
      simpa [complexMatrixRowFunctional_apply] using he x)

/-- The maximum, over columns of a complex matrix, of an arbitrary target vector
    norm.  This is the right-hand side of Problem 6.11(a). -/
noncomputable def complexMatrixColumnMaxVectorNorm {m n : ℕ}
    (νβ : CVec m → ℝ) (A : CMatrix m n) : ℝ :=
  let f : Fin n → NNReal := fun j => Real.toNNReal (νβ (fun i : Fin m => A i j))
  ((Finset.univ.sup f : NNReal) : ℝ)

lemma complexMatrixColumnMaxVectorNorm_nonneg {m n : ℕ}
    (νβ : CVec m → ℝ) (A : CMatrix m n) :
    0 ≤ complexMatrixColumnMaxVectorNorm νβ A := by
  unfold complexMatrixColumnMaxVectorNorm
  exact NNReal.coe_nonneg _

lemma complexMatrixColumnMaxVectorNorm_col_le {m n : ℕ}
    {νβ : CVec m → ℝ} (hβ : IsComplexVectorNorm νβ) (A : CMatrix m n)
    (j : Fin n) :
    νβ (fun i : Fin m => A i j) ≤ complexMatrixColumnMaxVectorNorm νβ A := by
  unfold complexMatrixColumnMaxVectorNorm
  let f : Fin n → NNReal := fun j => Real.toNNReal (νβ (fun i : Fin m => A i j))
  have hnn : f j ≤ Finset.univ.sup f :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin n))) (f := f) (Finset.mem_univ j)
  have hreal : ((f j : NNReal) : ℝ) ≤ ((Finset.univ.sup f : NNReal) : ℝ) := by
    exact_mod_cast hnn
  simpa [f, Real.coe_toNNReal _ (hβ.nonneg _)] using hreal

lemma complexMatrixColumnMaxVectorNorm_le_of_col_le {m n : ℕ}
    {νβ : CVec m → ℝ} (hβ : IsComplexVectorNorm νβ) {A : CMatrix m n}
    {d : ℝ} (hd : 0 ≤ d)
    (hcols : ∀ j : Fin n, νβ (fun i : Fin m => A i j) ≤ d) :
    complexMatrixColumnMaxVectorNorm νβ A ≤ d := by
  unfold complexMatrixColumnMaxVectorNorm
  let f : Fin n → NNReal := fun j => Real.toNNReal (νβ (fun i : Fin m => A i j))
  have hcols_nn : ∀ j, f j ≤ Real.toNNReal d := by
    intro j
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal d hd,
      Real.coe_toNNReal _ (hβ.nonneg _)]
    exact hcols j
  have hsup : Finset.univ.sup f ≤ Real.toNNReal d :=
    Finset.sup_le (fun j _ => hcols_nn j)
  have hreal : ((Finset.univ.sup f : NNReal) : ℝ) ≤ d := by
    rw [← Real.coe_toNNReal d hd]
    exact_mod_cast hsup
  simpa [f] using hreal

/-- The maximum, over rows of a complex matrix, of supplied dual norm values.
    This is the right-hand side of Problem 6.11(b) in the local dual-functional
    API. -/
noncomputable def complexMatrixRowDualMaxNorm {m : ℕ} (drow : Fin m → ℝ) : ℝ :=
  let f : Fin m → NNReal := fun i => Real.toNNReal (drow i)
  ((Finset.univ.sup f : NNReal) : ℝ)

lemma complexMatrixRowDualMaxNorm_nonneg {m : ℕ} (drow : Fin m → ℝ) :
    0 ≤ complexMatrixRowDualMaxNorm drow := by
  unfold complexMatrixRowDualMaxNorm
  exact NNReal.coe_nonneg _

lemma complexMatrixRowDualMaxNorm_row_le {m n : ℕ}
    {να : CVec n → ℝ} (hα : IsComplexVectorNorm να) (hn : 0 < n)
    {A : CMatrix m n} {drow : Fin m → ℝ}
    (hrow : ∀ i : Fin m,
      IsDualFunctionalNormValue να (complexMatrixRowFunctional A i) (drow i))
    (i : Fin m) :
    drow i ≤ complexMatrixRowDualMaxNorm drow := by
  unfold complexMatrixRowDualMaxNorm
  let f : Fin m → NNReal := fun i => Real.toNNReal (drow i)
  have hnn : f i ≤ Finset.univ.sup f :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin m))) (f := f) (Finset.mem_univ i)
  have hdrow_nonneg : 0 ≤ drow i :=
    dualFunctionalNormValue_nonneg_of_nonempty hα hn (hrow i)
  have hreal : ((f i : NNReal) : ℝ) ≤ ((Finset.univ.sup f : NNReal) : ℝ) := by
    exact_mod_cast hnn
  simpa [f, Real.coe_toNNReal _ hdrow_nonneg] using hreal

lemma complexMatrixRowDualMaxNorm_row_le_of_nonneg {m : ℕ}
    {drow : Fin m → ℝ} (hrow_nonneg : ∀ i : Fin m, 0 ≤ drow i)
    (i : Fin m) :
    drow i ≤ complexMatrixRowDualMaxNorm drow := by
  unfold complexMatrixRowDualMaxNorm
  let f : Fin m → NNReal := fun i => Real.toNNReal (drow i)
  have hnn : f i ≤ Finset.univ.sup f :=
    Finset.le_sup (s := (Finset.univ : Finset (Fin m))) (f := f) (Finset.mem_univ i)
  have hreal : ((f i : NNReal) : ℝ) ≤ ((Finset.univ.sup f : NNReal) : ℝ) := by
    exact_mod_cast hnn
  simpa [f, Real.coe_toNNReal _ (hrow_nonneg i)] using hreal

lemma complexMatrixRowDualMaxNorm_le_of_row_le {m : ℕ}
    {drow : Fin m → ℝ} {d : ℝ}
    (hrow_nonneg : ∀ i : Fin m, 0 ≤ drow i) (hd : 0 ≤ d)
    (hrows : ∀ i : Fin m, drow i ≤ d) :
    complexMatrixRowDualMaxNorm drow ≤ d := by
  unfold complexMatrixRowDualMaxNorm
  let f : Fin m → NNReal := fun i => Real.toNNReal (drow i)
  have hrows_nn : ∀ i, f i ≤ Real.toNNReal d := by
    intro i
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal d hd,
      Real.coe_toNNReal _ (hrow_nonneg i)]
    exact hrows i
  have hsup : Finset.univ.sup f ≤ Real.toNNReal d :=
    Finset.sup_le (fun i _ => hrows_nn i)
  have hreal : ((Finset.univ.sup f : NNReal) : ℝ) ≤ d := by
    rw [← Real.coe_toNNReal d hd]
    exact_mod_cast hsup
  simpa [f] using hreal

/-- Entrywise absolute value does not change the maximum finite column `L^p`
    norm. -/
lemma complexMatrixColumnMaxLpNorm_absMatrix_eq
    {m n : ℕ} {p : ℝ} (hp : 0 < p) (A : CMatrix m n) :
    complexMatrixColumnMaxVectorNorm
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) (complexAbsMatrix A) =
      complexMatrixColumnMaxVectorNorm
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A := by
  unfold complexMatrixColumnMaxVectorNorm
  apply congrArg (fun r : NNReal => (r : ℝ))
  refine Finset.sup_congr rfl ?_
  intro j _hj
  apply congrArg Real.toNNReal
  simpa [complexAbsMatrix, complexAbsVec] using
    complexVecLpNorm_ofReal_abs_eq (n := m) (p := p) hp
      (fun i : Fin m => A i j)

/-- Entrywise absolute value does not change the maximum finite row dual
    `L^q` norm used in equation (6.13). -/
lemma complexMatrixRowDualMaxLpNorm_absMatrix_eq
    {m n : ℕ} {q : ℝ} (hq : 0 < q) (A : CMatrix m n) :
    complexMatrixRowDualMaxNorm
        (fun i : Fin m =>
          complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => complexAbsMatrix A i j)) =
      complexMatrixRowDualMaxNorm
        (fun i : Fin m =>
          complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) := by
  unfold complexMatrixRowDualMaxNorm
  apply congrArg (fun r : NNReal => (r : ℝ))
  refine Finset.sup_congr rfl ?_
  intro i _hi
  apply congrArg Real.toNNReal
  simpa [complexAbsMatrix, complexAbsVec] using
    complexVecLpNorm_ofReal_abs_eq (n := n) (p := q) hq
      (fun j : Fin n => A i j)

/-- Row support version of the finite `L^p`/`L^q` row estimate: after
    restricting the input vector to the support of one row, the `p`th power of
    the row output is bounded by the maximum row `L^q` norm to the `p` times the
    row-support power sum of `x`. -/
theorem complexMatrixVecMul_row_norm_rpow_le_rowDualMax_lpNorm_rpow_mul_rowSupport_powerSum
    {m n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : CMatrix m n) (x : CVec n) (i : Fin m) :
    ‖complexMatrixVecMul A x i‖ ^ p ≤
      (complexMatrixRowDualMaxNorm
        (fun i : Fin m =>
          complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j))) ^ p *
        (complexMatrixRowSupport A i).sum (fun j => ‖x j‖ ^ p) := by
  classical
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.lt⟩
  haveI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.symm.lt⟩
  let R : ℝ :=
    complexMatrixRowDualMaxNorm
      (fun i : Fin m =>
        complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j))
  let row : CVec n := fun j : Fin n => A i j
  let rowX : CVec n := fun j : Fin n => if A i j = 0 then 0 else x j
  have hrow_nonneg :
      ∀ i : Fin m,
        0 ≤ complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j) := by
    intro i
    unfold complexVecLpNorm
    exact norm_nonneg
      (WithLp.toLp (ENNReal.ofReal q) (fun j : Fin n => A i j))
  have hrow_le_R :
      complexVecLpNorm (ENNReal.ofReal q) row ≤ R := by
    simpa [R, row] using
      complexMatrixRowDualMaxNorm_row_le_of_nonneg hrow_nonneg i
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact complexMatrixRowDualMaxNorm_nonneg _
  have hrowX_nonneg :
      0 ≤ complexVecLpNorm (ENNReal.ofReal p) rowX := by
    unfold complexVecLpNorm
    exact norm_nonneg (WithLp.toLp (ENNReal.ofReal p) rowX)
  have hsum_eq :
      complexMatrixVecMul A x i = ∑ j : Fin n, row j * rowX j := by
    unfold complexMatrixVecMul
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hij : A i j = 0
    · simp [row, rowX, hij]
    · simp [row, rowX, hij]
  have hholder :
      ‖complexMatrixVecMul A x i‖ ≤
        R * complexVecLpNorm (ENNReal.ofReal p) rowX := by
    calc
      ‖complexMatrixVecMul A x i‖
          = ‖∑ j : Fin n, row j * rowX j‖ := by rw [hsum_eq]
      _ ≤ complexVecLpNorm (ENNReal.ofReal q) row *
            complexVecLpNorm (ENNReal.ofReal p) rowX :=
          complexVecLpNorm_holder hpq row rowX
      _ ≤ R * complexVecLpNorm (ENNReal.ofReal p) rowX :=
          mul_le_mul_of_nonneg_right hrow_le_R hrowX_nonneg
  have hrowX_power :
      complexVecLpNorm (ENNReal.ofReal p) rowX ^ p =
        (complexMatrixRowSupport A i).sum (fun j => ‖x j‖ ^ p) := by
    calc
      complexVecLpNorm (ENNReal.ofReal p) rowX ^ p
          = ∑ j : Fin n, ‖rowX j‖ ^ p :=
              complexVecLpNorm_rpow_eq_sum_rpow hpq.pos rowX
      _ = (complexMatrixRowSupport A i).sum (fun j => ‖x j‖ ^ p) := by
            unfold complexMatrixRowSupport
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases hij : A i j = 0
            · simp [rowX, hij, Real.zero_rpow hpq.pos.ne']
            · simp [rowX, hij]
  calc
    ‖complexMatrixVecMul A x i‖ ^ p
        ≤ (R * complexVecLpNorm (ENNReal.ofReal p) rowX) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) hholder hpq.nonneg
    _ = R ^ p * complexVecLpNorm (ENNReal.ofReal p) rowX ^ p := by
          rw [Real.mul_rpow hR_nonneg hrowX_nonneg]
    _ = R ^ p * (complexMatrixRowSupport A i).sum (fun j => ‖x j‖ ^ p) := by
          rw [hrowX_power]
    _ =
        (complexMatrixRowDualMaxNorm
          (fun i : Fin m =>
            complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j))) ^ p *
          (complexMatrixRowSupport A i).sum (fun j => ‖x j‖ ^ p) := by
          rfl

/-- The dual norm of a row functional with respect to the vector 1-norm is the
    infinity norm of that row. -/
theorem complexMatrixRowFunctional_oneNormDualValue {m n : ℕ}
    (hn : 0 < n) (A : CMatrix m n) (i : Fin m) :
    IsDualFunctionalNormValue complexVecOneNorm (complexMatrixRowFunctional A i)
      (complexVecInfNorm (fun j : Fin n => A i j)) := by
  refine ⟨complexMatrixRowFunctional_linear A i, ?_, ?_⟩
  · intro x
    calc
      ‖complexMatrixRowFunctional A i x‖
          = ‖∑ j : Fin n, A i j * x j‖ := by
            rw [complexMatrixRowFunctional_apply]
      _ ≤ ∑ j : Fin n, ‖A i j * x j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖A i j‖ * ‖x j‖ := by
            apply Finset.sum_congr rfl
            intro j _hj
            exact norm_mul (A i j) (x j)
      _ ≤ ∑ j : Fin n, complexVecInfNorm (fun k : Fin n => A i k) * ‖x j‖ := by
            apply Finset.sum_le_sum
            intro j _hj
            exact mul_le_mul_of_nonneg_right
              (complexVecInfNorm_coord_le (fun k : Fin n => A i k) j)
              (norm_nonneg (x j))
      _ = complexVecInfNorm (fun k : Fin n => A i k) * ∑ j : Fin n, ‖x j‖ := by
            rw [Finset.mul_sum]
      _ = complexVecInfNorm (fun k : Fin n => A i k) * complexVecOneNorm x := by
            rfl
  · intro e he
    let j0 : Fin n := ⟨0, hn⟩
    have he_nonneg : 0 ≤ e := by
      have h := he (standardBasisCVec j0)
      rw [complexMatrixRowFunctional_standardBasisCVec A i j0,
        complexVecOneNorm_standardBasisCVec j0, mul_one] at h
      exact (norm_nonneg (A i j0)).trans h
    apply complexVecInfNorm_le_of_coord_le _ he_nonneg
    intro j
    have h := he (standardBasisCVec j)
    rw [complexMatrixRowFunctional_standardBasisCVec A i j,
      complexVecOneNorm_standardBasisCVec j, mul_one] at h
    exact h

/-- The concrete `1 -> infinity` mixed matrix norm: maximum row infinity norm,
    equivalently the maximum absolute entry. -/
noncomputable def complexMatrixOneInfNorm {m n : ℕ} (A : CMatrix m n) : ℝ :=
  complexMatrixRowDualMaxNorm
    (fun i : Fin m => complexVecInfNorm (fun j : Fin n => A i j))

theorem complexMatrixOneInfNorm_eq_max_row_infNorm {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixOneInfNorm A =
      ((Finset.univ.sup
        (fun i : Fin m => Real.toNNReal (complexVecInfNorm (fun j : Fin n => A i j))) :
          NNReal) : ℝ) := by
  rfl

lemma complexMatrixOneInfNorm_nonneg {m n : ℕ} (A : CMatrix m n) :
    0 ≤ complexMatrixOneInfNorm A := by
  unfold complexMatrixOneInfNorm
  exact complexMatrixRowDualMaxNorm_nonneg _

theorem complexMatrixOneInfNorm_row_infNorm_le {m n : ℕ}
    (hn : 0 < n) (A : CMatrix m n) (i : Fin m) :
    complexVecInfNorm (fun j : Fin n => A i j) ≤ complexMatrixOneInfNorm A := by
  unfold complexMatrixOneInfNorm
  exact complexMatrixRowDualMaxNorm_row_le (A := A)
    (drow := fun i : Fin m => complexVecInfNorm (fun j : Fin n => A i j))
    complexVecOneNorm_isComplexVectorNorm hn
    (fun i => complexMatrixRowFunctional_oneNormDualValue hn A i) i

lemma complexMatrixVecMul_linear {m n : ℕ} (A : CMatrix m n) :
    IsComplexVectorMapLinear (complexMatrixVecMul A) := by
  constructor
  · intro x y
    ext i
    simp only [complexMatrixVecMul, complexVecAdd]
    calc
      (∑ j : Fin n, A i j * (x j + y j)) =
          ∑ j : Fin n, (A i j * x j + A i j * y j) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
      _ = (∑ j : Fin n, A i j * x j) + ∑ j : Fin n, A i j * y j := by
            rw [Finset.sum_add_distrib]
  · intro a x
    ext i
    simp only [complexMatrixVecMul, complexVecSMul]
    calc
      (∑ j : Fin n, A i j * (a * x j)) =
          ∑ j : Fin n, a * (A i j * x j) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
      _ = a * ∑ j : Fin n, A i j * x j := by
            rw [Finset.mul_sum]

/-- Coordinate matrix of a source-facing square matrix-vector map in an
    arbitrary basis of `C^n`. -/
noncomputable def complexMatrixVecMulCoordinateMatrix {n : ℕ}
    (A : CMatrix n n) (b : Module.Basis (Fin n) ℂ (CVec n)) : CMatrix n n :=
  LinearMap.toMatrix b b
    (complexVectorMapLinearMap (complexMatrixVecMul A) (complexMatrixVecMul_linear A))

/-- Matrix form of a mixed subordinate upper bound, using the concrete
    matrix-vector bridge. -/
def MixedSubordinateMatrixBound {n m : ℕ} (να : CVec n → ℝ) (νβ : CVec m → ℝ)
    (A : CMatrix m n) (c : ℝ) : Prop :=
  MixedSubordinateBound να νβ (complexMatrixVecMul A) c

/-- Matrix form of a mixed subordinate norm value, represented as the least
    admissible mixed bound for the concrete matrix-vector map. -/
def IsMixedSubordinateMatrixNormValue {n m : ℕ} (να : CVec n → ℝ)
    (νβ : CVec m → ℝ) (A : CMatrix m n) (c : ℝ) : Prop :=
  IsMixedSubordinateNormValue να νβ (complexMatrixVecMul A) c

/-- Source-facing matrix `p`-norm value predicate: `c` is the local least
    subordinate value for `A : C^n -> C^m` when both source and target use the
    finite-product complex `L^p` vector norm.  This is the local bridge for the
    printed `||A||_p` notation in Chapter 6. -/
def IsComplexMatrixLpNormValue {m n : ℕ} (p : ℝ≥0∞)
    (A : CMatrix m n) (c : ℝ) : Prop :=
  IsMixedSubordinateMatrixNormValue
    (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A c

-- Keep lazily generated equation theorems in their frozen semantic owner.
run_meta do
  for declName in #[
      ``NumStability.complexMatrixVecMulCoordinateMatrix,
      ``NumStability.IsMixedSubordinateMatrixNormValue,
      ``NumStability.IsComplexMatrixLpNormValue] do
    discard <| Lean.Meta.getEqnsFor? declName

/-- Source-facing upper-bound predicate for the matrix `p`-norm.  The
    Riesz-Thorin route naturally proves this bound first; the least-value
    predicate `IsComplexMatrixLpNormValue` can then be compared to it. -/
def HasComplexMatrixLpBound {m n : ℕ} (p : ℝ≥0∞)
    (A : CMatrix m n) (C : ℝ) : Prop :=
  0 ≤ C ∧
    MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A C

theorem mixedSubordinateMatrixBound_iff_map_bound
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {A : CMatrix m n} {c : ℝ} :
    MixedSubordinateMatrixBound να νβ A c ↔
      MixedSubordinateBound να νβ (complexMatrixVecMul A) c := by
  rfl

theorem mixedSubordinateMatrixNormValue_iff_map_value
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    {A : CMatrix m n} {c : ℝ} :
    IsMixedSubordinateMatrixNormValue να νβ A c ↔
      IsMixedSubordinateNormValue να νβ (complexMatrixVecMul A) c := by
  rfl

/-- Source-facing quadratic form `x^* A x` for complex square matrices. -/
noncomputable def complexMatrixQuadraticForm {n : ℕ}
    (A : CMatrix n n) (x : CVec n) : ℂ :=
  let M : Matrix (Fin n) (Fin n) ℂ := A
  dotProduct (star x) (M.mulVec x)

/-- Real part of the source-facing quadratic form `x^* A x`. For PSD matrices
    this is the real value appearing in Higham Problem 6.12. -/
noncomputable def complexMatrixQuadraticFormRe {n : ℕ}
    (A : CMatrix n n) (x : CVec n) : ℝ :=
  (complexMatrixQuadraticForm A x).re

lemma complexMatrixQuadraticForm_eq_pairing {n : ℕ}
    (A : CMatrix n n) (x : CVec n) :
    complexMatrixQuadraticForm A x =
      ∑ i : Fin n, star (x i) * complexMatrixVecMul A x i := by
  simp [complexMatrixQuadraticForm, complexMatrixVecMul, Matrix.mulVec, dotProduct]

lemma complexMatrixQuadraticFormRe_nonneg_of_posSemidef {n : ℕ}
    {A : CMatrix n n}
    (hA : Matrix.PosSemidef (A : Matrix (Fin n) (Fin n) ℂ)) (x : CVec n) :
    0 ≤ complexMatrixQuadraticFormRe A x := by
  simpa [complexMatrixQuadraticForm, complexMatrixQuadraticFormRe] using
    hA.re_dotProduct_nonneg x

lemma complexMatrixQuadraticFormRe_eq_norm_of_posSemidef {n : ℕ}
    {A : CMatrix n n}
    (hA : Matrix.PosSemidef (A : Matrix (Fin n) (Fin n) ℂ)) (x : CVec n) :
    complexMatrixQuadraticFormRe A x =
      ‖complexMatrixQuadraticForm A x‖ := by
  have hnonneg :
      0 ≤ complexMatrixQuadraticForm A x := by
    simpa [complexMatrixQuadraticForm] using
      hA.dotProduct_mulVec_nonneg x
  have hcoe := Complex.eq_coe_norm_of_nonneg hnonneg
  exact (congrArg Complex.re hcoe).trans (by simp)

lemma complexMatrixQuadraticForm_cauchy_of_posSemidef {n : ℕ}
    {A : CMatrix n n}
    (hA : Matrix.PosSemidef (A : Matrix (Fin n) (Fin n) ℂ))
    (u v : CVec n) :
    ‖∑ i : Fin n, star (v i) * complexMatrixVecMul A u i‖ ≤
      Real.sqrt (complexMatrixQuadraticFormRe A u) *
        Real.sqrt (complexMatrixQuadraticFormRe A v) := by
  let M : Matrix (Fin n) (Fin n) ℂ := A
  have hcore :
      ‖dotProduct (star v) (M.mulVec u)‖ ≤
        Real.sqrt ((dotProduct (star u) (M.mulVec u)).re) *
          Real.sqrt ((dotProduct (star v) (M.mulVec v)).re) := by
    letI : SeminormedAddCommGroup (Fin n → ℂ) := M.toSeminormedAddCommGroup hA
    letI : InnerProductSpace ℂ (Fin n → ℂ) := M.toInnerProductSpace hA
    have h := norm_inner_le_norm (𝕜 := ℂ) v u
    simpa [norm_eq_sqrt_re_inner, inner, dotProduct_comm, mul_comm, mul_left_comm,
      mul_assoc] using h
  simpa [complexMatrixQuadraticForm, complexMatrixQuadraticFormRe,
    complexMatrixVecMul, Matrix.mulVec, dotProduct] using hcore

theorem mixedSubordinateMatrixBound_pullback
    {n : ℕ} {μ : CVec n → ℝ} {S : ComplexVectorMap n n}
    {A T : CMatrix n n} {C : ℝ}
    (hconj : ∀ x : CVec n,
      S (complexMatrixVecMul A x) = complexMatrixVecMul T (S x))
    (hT : MixedSubordinateMatrixBound μ μ T C) :
    MixedSubordinateMatrixBound
      (fun x : CVec n => μ (S x)) (fun x : CVec n => μ (S x)) A C := by
  intro x
  change μ (S (complexMatrixVecMul A x)) ≤ C * μ (S x)
  rw [hconj x]
  exact hT (S x)

/-- A local mixed subordinate matrix norm value is nonnegative when the source
    dimension is nonempty. -/
lemma mixedSubordinateMatrixNormValue_nonneg_of_nonempty
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hn : 0 < n) (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    {A : CMatrix m n} {d : ℝ}
    (hA : IsMixedSubordinateMatrixNormValue να νβ A d) :
    0 ≤ d := by
  obtain ⟨u, hu⟩ := exists_unit_complexVectorNorm hα hn
  have h := hA.1 u
  rw [hu, mul_one] at h
  exact (hβ.nonneg (complexMatrixVecMul A u)).trans h

/-- If a finite-dimensional matrix map has any mixed subordinate upper bound,
    then it has a local least mixed subordinate norm value.  The value is
    Mathlib's operator norm of the corresponding bounded continuous linear map,
    translated back to the Chapter 6 least-bound predicate. -/
theorem exists_mixedSubordinateMatrixNormValue_of_bound_nonempty
    {n m : ℕ} {να : CVec n → ℝ} {νβ : CVec m → ℝ}
    (hn : 0 < n) (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (A : CMatrix m n) {C : ℝ}
    (hbound : MixedSubordinateMatrixBound να νβ A C) :
    ∃ c : ℝ, IsMixedSubordinateMatrixNormValue να νβ A c := by
  let instSrcNAG : NormedAddCommGroup (NormedCVec n να) :=
    NormedCVec.normedAddCommGroup hα
  letI : NormedAddCommGroup (NormedCVec n να) := instSrcNAG
  let instSrcModule : Module ℂ (NormedCVec n να) :=
    (NormedCVec.equiv n να).module ℂ
  letI : Module ℂ (NormedCVec n να) := instSrcModule
  let instSrcNS : NormedSpace ℂ (NormedCVec n να) :=
    NormedSpace.ofCore (𝕜 := ℂ) (NormedCVec.normedSpaceCore hα)
  letI : NormedSpace ℂ (NormedCVec n να) := instSrcNS
  let instTgtNAG : NormedAddCommGroup (NormedCVec m νβ) :=
    NormedCVec.normedAddCommGroup hβ
  letI : NormedAddCommGroup (NormedCVec m νβ) := instTgtNAG
  let instTgtModule : Module ℂ (NormedCVec m νβ) :=
    (NormedCVec.equiv m νβ).module ℂ
  letI : Module ℂ (NormedCVec m νβ) := instTgtModule
  let instTgtNS : NormedSpace ℂ (NormedCVec m νβ) :=
    NormedSpace.ofCore (𝕜 := ℂ) (NormedCVec.normedSpaceCore hβ)
  letI : NormedSpace ℂ (NormedCVec m νβ) := instTgtNS
  let instSrcFin : FiniteDimensional ℂ (NormedCVec n να) := by
    let e : CVec n ≃ₗ[ℂ] NormedCVec n να :=
      { toFun := fun x => ⟨x⟩
        invFun := NormedCVec.val
        left_inv := by intro x; rfl
        right_inv := by intro x; cases x; rfl
        map_add' := by intro x y; rfl
        map_smul' := by intro a x; rfl }
    exact LinearEquiv.finiteDimensional e
  letI : FiniteDimensional ℂ (NormedCVec n να) := instSrcFin
  let L : NormedCVec n να →ₗ[ℂ] NormedCVec m νβ :=
    { toFun := fun x => ⟨complexMatrixVecMul A x.val⟩
      map_add' := by
        intro x y
        apply NormedCVec.ext
        have h := (complexMatrixVecMul_linear A).map_add x.val y.val
        simpa [complexVecAdd] using h
      map_smul' := by
        intro a x
        apply NormedCVec.ext
        have h := (complexMatrixVecMul_linear A).map_smul a x.val
        simpa [complexVecSMul] using h }
  have hLbound : ∀ x : NormedCVec n να, ‖L x‖ ≤ C * ‖x‖ := by
    intro x
    simpa [L, NormedCVec.norm_eq] using hbound x.val
  let f : NormedCVec n να →L[ℂ] NormedCVec m νβ :=
    L.mkContinuous C hLbound
  refine ⟨‖f‖, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x
    have h := f.le_opNorm (⟨x⟩ : NormedCVec n να)
    simpa [f, L, NormedCVec.norm_eq] using h
  · intro d hd
    have hd_nonneg : 0 ≤ d := by
      obtain ⟨u, hu⟩ := exists_unit_complexVectorNorm hα hn
      have hu_pos : 0 < να u := by
        rw [hu]
        norm_num
      have hdu : νβ (complexMatrixVecMul A u) ≤ d * να u := hd u
      have hprod_nonneg : 0 ≤ d * να u :=
        (hβ.nonneg (complexMatrixVecMul A u)).trans hdu
      have hprod_nonneg' : 0 ≤ να u * d := by
        simpa [mul_comm] using hprod_nonneg
      exact nonneg_of_mul_nonneg_right hprod_nonneg' hu_pos
    apply ContinuousLinearMap.opNorm_le_bound f hd_nonneg
    intro x
    simpa [f, L, NormedCVec.norm_eq] using hd x.val
end NumStability
