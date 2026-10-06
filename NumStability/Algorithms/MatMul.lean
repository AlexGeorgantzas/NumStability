-- Algorithms/MatMul.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.MatVec

namespace NumStability

open scoped BigOperators

/-- Floating-point matrix-matrix product Ĉ = fl(AB).

    Computed column by column: each column j of Ĉ is the floating-point
    matrix-vector product of A with the jth column of B (Higham §3.5):
      Ĉ(:,j) = fl_matVec fp A B(:,j)

    This matches the "jik" and "jki" loop orderings Higham describes, which
    both compute C a column at a time and commit the same rounding errors as
    the standard triple-loop ordering. -/
noncomputable def fl_matMul (fp : FPModel) (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ) : Fin m → Fin p → ℝ :=
  fun i j => fl_matVec fp m n A (fun k => B k j) i

/-- **Matrix-matrix forward error bound** (Higham §3.5, equation 3.12).

    The componentwise forward error satisfies:
      |C - Ĉ| ≤ γ(n)|A||B|  (componentwise)

    Formally: for each entry (i, j),
      |fl_matMul fp A B i j - ∑ k, A i k * B k j| ≤ γ(n) * ∑ k, |A i k| * |B k j|

    Proof: `fl_matMul fp A B i j` is by definition `fl_matVec fp A (B(:,j)) i`,
    so `matVec_error_bound` applies directly. -/
theorem matMul_error_bound (fp : FPModel) (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hn : gammaValid fp n) :
    ∀ i : Fin m, ∀ j : Fin p,
      |fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j| ≤
        gamma fp n * ∑ k : Fin n, |A i k| * |B k j| :=
  fun i j => matVec_error_bound fp m n A (fun k => B k j) hn i

/-- **Matrix-matrix Frobenius forward-error majorant** (Higham §3.5, p. 78).

    The componentwise matrix multiplication bound (3.13) implies the Frobenius
    norm bound against the nonnegative majorant `|A||B|`:
      `||fl(AB)-AB||_F <= gamma_n || |A||B| ||_F`.

    The source's final normwise product-norm corollaries are exposed separately
    below when the needed square-matrix norm adapters are available. -/
theorem matMul_error_bound_frobNorm_majorant (fp : FPModel) (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hn : gammaValid fp n) :
    frobNormRect
      (fun i : Fin m => fun j : Fin p =>
        fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j) ≤
      gamma fp n *
        frobNormRect
          (fun i : Fin m => fun j : Fin p =>
            ∑ k : Fin n, |A i k| * |B k j|) := by
  let M : Fin m → Fin p → ℝ :=
    fun i j => ∑ k : Fin n, |A i k| * |B k j|
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hM_nonneg : ∀ i j, 0 ≤ M i j := by
    intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hscaled_nonneg : ∀ i j, 0 ≤ gamma fp n * M i j := by
    intro i j
    exact mul_nonneg hγ (hM_nonneg i j)
  have hentry : ∀ i j,
      |fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j| ≤
        gamma fp n * M i j := by
    intro i j
    simpa [M] using matMul_error_bound fp m n p A B hn i j
  calc
    frobNormRect
        (fun i : Fin m => fun j : Fin p =>
          fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j)
        ≤ frobNormRect (fun i : Fin m => fun j : Fin p => gamma fp n * M i j) :=
          frobNormRect_le_of_entry_abs_le
            (fun i : Fin m => fun j : Fin p =>
              fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j)
            (fun i : Fin m => fun j : Fin p => gamma fp n * M i j)
            hscaled_nonneg hentry
    _ = |gamma fp n| * frobNormRect M := by
          simpa [M] using
            (frobNormRect_smul (m := m) (n := p) (gamma fp n) M)
    _ = gamma fp n * frobNormRect M := by
          rw [abs_of_nonneg hγ]

/-- **Matrix-matrix operator-2 forward-error majorant** (Higham §3.5, p. 78).

The componentwise product bound (3.13) also gives a vector-action 2-norm
certificate.  If the nonnegative factors `|A|` and `|B|` have rectangular
operator-2 certificates `alpha` and `beta`, then the forward error
`E = fl(A*B)-A*B` satisfies

`||E*x||_2 <= gamma_n * alpha * beta * ||x||_2`.

This is the local predicate-form version of the source p = 2 normwise
corollary; the repository does not introduce a supremum-valued spectral norm
function for legacy function-shaped matrices. -/
theorem matMul_error_bound_rectOpNorm2Le_majorant (fp : FPModel)
    (m n p : ℕ) (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (alpha beta : ℝ) (hn : gammaValid fp n) (halpha : 0 ≤ alpha)
    (hA : rectOpNorm2Le (fun i : Fin m => fun k : Fin n => |A i k|) alpha)
    (hB : rectOpNorm2Le (fun k : Fin n => fun j : Fin p => |B k j|) beta) :
    rectOpNorm2Le
      (fun i : Fin m => fun j : Fin p =>
        fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j)
      (gamma fp n * alpha * beta) := by
  let γ : ℝ := gamma fp n
  let E : Fin m → Fin p → ℝ :=
    fun i j => fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j
  let M : Fin m → Fin p → ℝ :=
    fun i j => ∑ k : Fin n, |A i k| * |B k j|
  have hγ : 0 ≤ γ := gamma_nonneg fp hn
  have hM_nonneg : ∀ i j, 0 ≤ M i j := by
    intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hM_eq :
      M =
        rectMatMul
          (fun i : Fin m => fun k : Fin n => |A i k|)
          (fun k : Fin n => fun j : Fin p => |B k j|) := by
    ext i j
    simp [M, rectMatMul]
  have hMop : rectOpNorm2Le M (alpha * beta) := by
    rw [hM_eq]
    exact rectOpNorm2Le_rectMatMul
      (fun i : Fin m => fun k : Fin n => |A i k|)
      (fun k : Fin n => fun j : Fin p => |B k j|)
      halpha hA hB
  intro x
  let xabs : Fin p → ℝ := fun j => |x j|
  let rhsVec : Fin m → ℝ := fun i => γ * rectMatMulVec M xabs i
  have hentry : ∀ i : Fin m, |rectMatMulVec E x i| ≤ rhsVec i := by
    intro i
    calc
      |rectMatMulVec E x i|
          = |∑ j : Fin p, E i j * x j| := by rfl
      _ ≤ ∑ j : Fin p, |E i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin p, |E i j| * |x j| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_mul]
      _ ≤ ∑ j : Fin p, (γ * M i j) * |x j| := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_right
              (by
                simpa [E, M, γ] using
                  matMul_error_bound fp m n p A B hn i j)
              (abs_nonneg _)
      _ = γ * rectMatMulVec M xabs i := by
            simp [rectMatMulVec, xabs]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = rhsVec i := rfl
  calc
    vecNorm2 (rectMatMulVec E x)
        ≤ vecNorm2 rhsVec := vecNorm2_le_of_abs_le _ _ hentry
    _ = γ * vecNorm2 (rectMatMulVec M xabs) := by
          simp [rhsVec, vecNorm2_smul, abs_of_nonneg hγ]
    _ ≤ γ * ((alpha * beta) * vecNorm2 xabs) :=
          mul_le_mul_of_nonneg_left (hMop xabs) hγ
    _ = (gamma fp n * alpha * beta) * vecNorm2 x := by
          rw [vecNorm2_abs]
          simp [γ]
          ring

/-- **Matrix-matrix 1-norm forward-error bound** (Higham §3.5, p. 78).

    For square matrix multiplication, the componentwise bound (3.13) implies
      `||fl(AB)-AB||_1 <= gamma_n ||A||_1 ||B||_1`. -/
theorem matMul_error_bound_oneNorm (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    oneNorm
      (fun i : Fin n => fun j : Fin n =>
        fl_matMul fp n n n A B i j - ∑ k : Fin n, A i k * B k j) ≤
      gamma fp n * oneNorm A * oneNorm B := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hA : 0 ≤ oneNorm A := oneNorm_nonneg A
  have hB : 0 ≤ oneNorm B := oneNorm_nonneg B
  apply oneNorm_le_of_col_sum_le
  · intro j
    have hcomp_sum :
        (∑ i : Fin n,
          |fl_matMul fp n n n A B i j - ∑ k : Fin n, A i k * B k j|) ≤
          ∑ i : Fin n, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| :=
      Finset.sum_le_sum (fun i _ => matMul_error_bound fp n n n A B hn i j)
    have hdouble :
        (∑ i : Fin n, ∑ k : Fin n, |A i k| * |B k j|) =
          ∑ k : Fin n, |B k j| * ∑ i : Fin n, |A i k| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_mul]
      ring
    have hdouble_bound :
        (∑ i : Fin n, ∑ k : Fin n, |A i k| * |B k j|) ≤
          oneNorm A * ∑ k : Fin n, |B k j| := by
      rw [hdouble]
      calc
        ∑ k : Fin n, |B k j| * ∑ i : Fin n, |A i k|
            ≤ ∑ k : Fin n, |B k j| * oneNorm A :=
                Finset.sum_le_sum (fun k _ =>
                  mul_le_mul_of_nonneg_left (col_sum_le_oneNorm A k) (abs_nonneg _))
        _ = oneNorm A * ∑ k : Fin n, |B k j| := by
                rw [← Finset.sum_mul]
                ring
    calc
      (∑ i : Fin n,
          |fl_matMul fp n n n A B i j - ∑ k : Fin n, A i k * B k j|)
          ≤ ∑ i : Fin n, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| :=
            hcomp_sum
      _ = gamma fp n * (∑ i : Fin n, ∑ k : Fin n, |A i k| * |B k j|) := by
            rw [← Finset.mul_sum]
      _ ≤ gamma fp n * (oneNorm A * ∑ k : Fin n, |B k j|) :=
            mul_le_mul_of_nonneg_left hdouble_bound hγ
      _ ≤ gamma fp n * (oneNorm A * oneNorm B) := by
            have hcolB : ∑ k : Fin n, |B k j| ≤ oneNorm B :=
              col_sum_le_oneNorm B j
            have hprod : oneNorm A * (∑ k : Fin n, |B k j|) ≤
                oneNorm A * oneNorm B :=
              mul_le_mul_of_nonneg_left hcolB hA
            exact mul_le_mul_of_nonneg_left hprod hγ
      _ = gamma fp n * oneNorm A * oneNorm B := by ring
  · exact mul_nonneg (mul_nonneg hγ hA) hB

/-- **Rectangular matrix-matrix 1-norm forward-error bound**.

    For `A : Fin m -> Fin n -> ℝ` and `B : Fin n -> Fin p -> ℝ`, the
    componentwise bound (3.13) implies
      `||fl(AB)-AB||_1 <= gamma_n ||A||_1 ||B||_1`,
    with rectangular maximum-column-sum norms. -/
theorem matMul_error_bound_oneNormRect (fp : FPModel) (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hn : gammaValid fp n) :
    oneNormRect
      (fun i : Fin m => fun j : Fin p =>
        fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j) ≤
      gamma fp n * oneNormRect A * oneNormRect B := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hA : 0 ≤ oneNormRect A := oneNormRect_nonneg A
  have hB : 0 ≤ oneNormRect B := oneNormRect_nonneg B
  apply oneNormRect_le_of_col_sum_le
  · intro j
    have hcomp_sum :
        (∑ i : Fin m,
          |fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j|) ≤
          ∑ i : Fin m, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| :=
      Finset.sum_le_sum (fun i _ => matMul_error_bound fp m n p A B hn i j)
    have hdouble :
        (∑ i : Fin m, ∑ k : Fin n, |A i k| * |B k j|) =
          ∑ k : Fin n, |B k j| * ∑ i : Fin m, |A i k| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_mul]
      ring
    have hdouble_bound :
        (∑ i : Fin m, ∑ k : Fin n, |A i k| * |B k j|) ≤
          oneNormRect A * ∑ k : Fin n, |B k j| := by
      rw [hdouble]
      calc
        ∑ k : Fin n, |B k j| * ∑ i : Fin m, |A i k|
            ≤ ∑ k : Fin n, |B k j| * oneNormRect A :=
                Finset.sum_le_sum (fun k _ =>
                  mul_le_mul_of_nonneg_left
                    (col_sum_le_oneNormRect A k) (abs_nonneg _))
        _ = oneNormRect A * ∑ k : Fin n, |B k j| := by
                rw [← Finset.sum_mul]
                ring
    calc
      (∑ i : Fin m,
          |fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j|)
          ≤ ∑ i : Fin m, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| :=
            hcomp_sum
      _ = gamma fp n * (∑ i : Fin m, ∑ k : Fin n, |A i k| * |B k j|) := by
            rw [← Finset.mul_sum]
      _ ≤ gamma fp n * (oneNormRect A * ∑ k : Fin n, |B k j|) :=
            mul_le_mul_of_nonneg_left hdouble_bound hγ
      _ ≤ gamma fp n * (oneNormRect A * oneNormRect B) := by
            have hcolB : ∑ k : Fin n, |B k j| ≤ oneNormRect B :=
              col_sum_le_oneNormRect B j
            have hprod : oneNormRect A * (∑ k : Fin n, |B k j|) ≤
                oneNormRect A * oneNormRect B :=
              mul_le_mul_of_nonneg_left hcolB hA
            exact mul_le_mul_of_nonneg_left hprod hγ
      _ = gamma fp n * oneNormRect A * oneNormRect B := by ring
  · exact mul_nonneg (mul_nonneg hγ hA) hB

/-- **Rectangular matrix-matrix infinity-norm forward-error bound**.

    The same componentwise bound (3.13) also gives the maximum-row-sum
    induced-norm corollary
      `||fl(AB)-AB||_∞ <= gamma_n ||A||_∞ ||B||_∞`
    for compatible rectangular matrices. -/
theorem matMul_error_bound_infNormRect (fp : FPModel) (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hn : gammaValid fp n) :
    infNormRect
      (fun i : Fin m => fun j : Fin p =>
        fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j) ≤
      gamma fp n * infNormRect A * infNormRect B := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hA : 0 ≤ infNormRect A := infNormRect_nonneg A
  have hB : 0 ≤ infNormRect B := infNormRect_nonneg B
  apply infNormRect_le_of_row_sum_le
  · intro i
    have hcomp_sum :
        (∑ j : Fin p,
          |fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j|) ≤
          ∑ j : Fin p, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| :=
      Finset.sum_le_sum (fun j _ => matMul_error_bound fp m n p A B hn i j)
    have hdouble :
        (∑ j : Fin p, ∑ k : Fin n, |A i k| * |B k j|) =
          ∑ k : Fin n, |A i k| * ∑ j : Fin p, |B k j| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    have hdouble_bound :
        (∑ j : Fin p, ∑ k : Fin n, |A i k| * |B k j|) ≤
          (∑ k : Fin n, |A i k|) * infNormRect B := by
      rw [hdouble]
      calc
        ∑ k : Fin n, |A i k| * ∑ j : Fin p, |B k j|
            ≤ ∑ k : Fin n, |A i k| * infNormRect B :=
                Finset.sum_le_sum (fun k _ =>
                  mul_le_mul_of_nonneg_left
                    (row_sum_le_infNormRect B k) (abs_nonneg _))
        _ = (∑ k : Fin n, |A i k|) * infNormRect B := by
                rw [Finset.sum_mul]
    calc
      (∑ j : Fin p,
          |fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j|)
          ≤ ∑ j : Fin p, gamma fp n * ∑ k : Fin n, |A i k| * |B k j| :=
            hcomp_sum
      _ = gamma fp n * (∑ j : Fin p, ∑ k : Fin n, |A i k| * |B k j|) := by
            rw [← Finset.mul_sum]
      _ ≤ gamma fp n * ((∑ k : Fin n, |A i k|) * infNormRect B) :=
            mul_le_mul_of_nonneg_left hdouble_bound hγ
      _ ≤ gamma fp n * (infNormRect A * infNormRect B) := by
            have hrowA : ∑ k : Fin n, |A i k| ≤ infNormRect A :=
              row_sum_le_infNormRect A i
            have hprod : (∑ k : Fin n, |A i k|) * infNormRect B ≤
                infNormRect A * infNormRect B :=
              mul_le_mul_of_nonneg_right hrowA hB
            exact mul_le_mul_of_nonneg_left hprod hγ
      _ = gamma fp n * infNormRect A * infNormRect B := by ring
  · exact mul_nonneg (mul_nonneg hγ hA) hB

/-- **Rectangular matrix-matrix Frobenius forward-error bound**.

    For compatible rectangular matrices, the componentwise bound (3.13) and
    rectangular Frobenius submultiplicativity imply
      `||fl(AB)-AB||_F <= gamma_n ||A||_F ||B||_F`. -/
theorem matMul_error_bound_frobNormRect (fp : FPModel) (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hn : gammaValid fp n) :
    frobNormRect
      (fun i : Fin m => fun j : Fin p =>
        fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j) ≤
      gamma fp n * frobNormRect A * frobNormRect B := by
  let M : Fin m → Fin p → ℝ :=
    fun i j => ∑ k : Fin n, |A i k| * |B k j|
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hmajor :
      frobNormRect
        (fun i : Fin m => fun j : Fin p =>
          fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j) ≤
      gamma fp n * frobNormRect M := by
    simpa [M] using matMul_error_bound_frobNorm_majorant fp m n p A B hn
  have hAabs : frobNormRect (fun i : Fin m => fun k : Fin n => |A i k|) =
      frobNormRect A := by
    simpa using (frobNormRect_abs A)
  have hBabs : frobNormRect (fun k : Fin n => fun j : Fin p => |B k j|) =
      frobNormRect B := by
    simpa using (frobNormRect_abs B)
  have hM_eq :
      M =
        rectMatMul
          (fun i : Fin m => fun k : Fin n => |A i k|)
          (fun k : Fin n => fun j : Fin p => |B k j|) := by
    ext i j
    simp [M, rectMatMul]
  have hM_bound : frobNormRect M ≤ frobNormRect A * frobNormRect B := by
    rw [hM_eq]
    calc
      frobNormRect
          (rectMatMul
            (fun i : Fin m => fun k : Fin n => |A i k|)
            (fun k : Fin n => fun j : Fin p => |B k j|))
          ≤
            frobNormRect (fun i : Fin m => fun k : Fin n => |A i k|) *
              frobNormRect (fun k : Fin n => fun j : Fin p => |B k j|) :=
                frobNormRect_rectMatMul_le
                  (fun i : Fin m => fun k : Fin n => |A i k|)
                  (fun k : Fin n => fun j : Fin p => |B k j|)
      _ = frobNormRect A * frobNormRect B := by
            rw [hAabs, hBabs]
  calc
    frobNormRect
        (fun i : Fin m => fun j : Fin p =>
          fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j)
        ≤ gamma fp n * frobNormRect M := hmajor
    _ ≤ gamma fp n * (frobNormRect A * frobNormRect B) :=
          mul_le_mul_of_nonneg_left hM_bound hγ
    _ = gamma fp n * frobNormRect A * frobNormRect B := by ring

/-- **Matrix-matrix Frobenius forward-error bound** (Higham §3.5, p. 78).

    For square matrix multiplication, the componentwise bound (3.13) implies
      `||fl(AB)-AB||_F <= gamma_n ||A||_F ||B||_F`. -/
theorem matMul_error_bound_frobNorm (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    frobNorm
      (fun i : Fin n => fun j : Fin n =>
        fl_matMul fp n n n A B i j - ∑ k : Fin n, A i k * B k j) ≤
      gamma fp n * frobNorm A * frobNorm B := by
  let M : Fin n → Fin n → ℝ :=
    fun i j => ∑ k : Fin n, |A i k| * |B k j|
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hmajor :
      frobNormRect
        (fun i : Fin n => fun j : Fin n =>
          fl_matMul fp n n n A B i j - ∑ k : Fin n, A i k * B k j) ≤
      gamma fp n * frobNormRect M := by
    simpa [M] using matMul_error_bound_frobNorm_majorant fp n n n A B hn
  have hAabs_rect : frobNormRect (absMatrix n A) = frobNormRect A := by
    simpa [absMatrix] using (frobNormRect_abs A)
  have hBabs_rect : frobNormRect (absMatrix n B) = frobNormRect B := by
    simpa [absMatrix] using (frobNormRect_abs B)
  have hAabs : frobNorm (absMatrix n A) = frobNorm A := by
    rw [← frobNormRect_eq_frobNorm (absMatrix n A), hAabs_rect,
      frobNormRect_eq_frobNorm A]
  have hBabs : frobNorm (absMatrix n B) = frobNorm B := by
    rw [← frobNormRect_eq_frobNorm (absMatrix n B), hBabs_rect,
      frobNormRect_eq_frobNorm B]
  have hM_eq : M = matMul n (absMatrix n A) (absMatrix n B) := by
    ext i j
    simp [M, matMul, absMatrix]
  have hM_bound : frobNormRect M ≤ frobNorm A * frobNorm B := by
    rw [hM_eq, frobNormRect_eq_frobNorm]
    calc
      frobNorm (matMul n (absMatrix n A) (absMatrix n B))
          ≤ frobNorm (absMatrix n A) * frobNorm (absMatrix n B) :=
            frobNorm_matMul_le (absMatrix n A) (absMatrix n B)
      _ = frobNorm A * frobNorm B := by
            rw [hAabs, hBabs]
  rw [← frobNormRect_eq_frobNorm]
  calc
    frobNormRect
        (fun i : Fin n => fun j : Fin n =>
          fl_matMul fp n n n A B i j - ∑ k : Fin n, A i k * B k j)
        ≤ gamma fp n * frobNormRect M := hmajor
    _ ≤ gamma fp n * (frobNorm A * frobNorm B) :=
          mul_le_mul_of_nonneg_left hM_bound hγ
    _ = gamma fp n * frobNorm A * frobNorm B := by ring

/-- **Matrix-matrix operator-2 forward-error certificate via Frobenius norm**.

    For square matrix multiplication, the Frobenius product-norm error bound
    immediately gives the vector-action spectral certificate
      `||E x||₂ <= gamma_n ||A||_F ||B||_F ||x||₂`,
    where `E = fl(AB)-AB`.

    This is a useful Chapter 3 `p = 2` adapter, but it is deliberately weaker
    than Higham's source corollary with `||A||₂ ||B||₂`; the repository's local
    operator-2 API is currently predicate-based and does not yet expose that
    product-norm scalar theorem. -/
theorem matMul_error_bound_opNorm2Le_frob (fp : FPModel) (n : ℕ)
    (A B : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) :
    opNorm2Le
      (fun i : Fin n => fun j : Fin n =>
        fl_matMul fp n n n A B i j - ∑ k : Fin n, A i k * B k j)
      (gamma fp n * frobNorm A * frobNorm B) :=
  opNorm2Le_of_frobNorm_le
    (fun i : Fin n => fun j : Fin n =>
      fl_matMul fp n n n A B i j - ∑ k : Fin n, A i k * B k j)
    (matMul_error_bound_frobNorm fp n A B hn)

/-- **Matrix-matrix columnwise backward error** (Higham §3.5).

    Each computed column of Ĉ is the exact result for a slightly perturbed A:
      ∀ j, ∃ ΔAⱼ, (∀ i k, |ΔAⱼ i k| ≤ γ(n) * |A i k|) ∧
                   ∀ i, Ĉ i j = ∑ k, (A i k + ΔAⱼ i k) * B k j

    **Important**: the perturbation ΔAⱼ depends on j — each column has its
    own backward error matrix.  There is no single ΔA that simultaneously
    explains all columns (Higham §3.5 explicitly notes this: "The same cannot
    be said for Ĉ as a whole").

    Proof: apply `matVec_backward_error` to each column independently. -/
theorem matMul_backward_error_col (fp : FPModel) (m n p : ℕ)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hn : gammaValid fp n) :
    ∀ j : Fin p, ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i k, |ΔA i k| ≤ gamma fp n * |A i k|) ∧
      ∀ i, fl_matMul fp m n p A B i j = ∑ k : Fin n, (A i k + ΔA i k) * B k j :=
  fun j => matVec_backward_error fp m n A (fun k => B k j) hn

/-- **Problem 3.5, common left-factor backward error.**

For square nonsingular `B`, the componentwise forward-error matrix for
`fl(A*B)` can be moved to the left factor:

`fl(A*B) = (A + DeltaA) * B`,

with the source-style componentwise bound

`|DeltaA| <= gamma_n * |A| * |B| * |B_inv|`.

This is the global backward-error result that complements the columnwise
backward-error theorem above. -/
theorem matMul_backward_error_common_A_of_inverse (fp : FPModel) (n : ℕ)
    (A B B_inv : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) (hB : IsInverse n B B_inv) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i k,
        |ΔA i k| ≤
          gamma fp n *
            ∑ l : Fin n,
              (∑ r : Fin n, |A i r| * |B r l|) * |B_inv l k|) ∧
      ∀ i j,
        fl_matMul fp n n n A B i j =
          ∑ k : Fin n, (A i k + ΔA i k) * B k j := by
  let E : Fin n → Fin n → ℝ :=
    fun i j => fl_matMul fp n n n A B i j - ∑ k : Fin n, A i k * B k j
  let ΔA : Fin n → Fin n → ℝ := matMul n E B_inv
  refine ⟨ΔA, ?_, ?_⟩
  · intro i k
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    have hE :
        ∀ l : Fin n,
          |E i l| ≤ gamma fp n * ∑ r : Fin n, |A i r| * |B r l| := by
      intro l
      simpa [E] using matMul_error_bound fp n n n A B hn i l
    calc
      |ΔA i k|
          = |∑ l : Fin n, E i l * B_inv l k| := by rfl
      _ ≤ ∑ l : Fin n, |E i l * B_inv l k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l : Fin n, |E i l| * |B_inv l k| := by
          apply Finset.sum_congr rfl
          intro l _
          rw [abs_mul]
      _ ≤
          ∑ l : Fin n,
            (gamma fp n * ∑ r : Fin n, |A i r| * |B r l|) * |B_inv l k| := by
          apply Finset.sum_le_sum
          intro l _
          exact mul_le_mul_of_nonneg_right (hE l) (abs_nonneg _)
      _ =
          gamma fp n *
            ∑ l : Fin n,
              (∑ r : Fin n, |A i r| * |B r l|) * |B_inv l k| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
  · have hBinvB : matMul n B_inv B = idMatrix n := by
      ext i j
      exact hB.1 i j
    have hΔAB : matMul n ΔA B = E := by
      calc
        matMul n ΔA B = matMul n (matMul n E B_inv) B := rfl
        _ = matMul n E (matMul n B_inv B) := by
            rw [matMul_assoc]
        _ = matMul n E (idMatrix n) := by
            rw [hBinvB]
        _ = E := matMul_id_right n E
    intro i j
    calc
      fl_matMul fp n n n A B i j
          = (∑ k : Fin n, A i k * B k j) + E i j := by
              simp [E]
      _ = (∑ k : Fin n, A i k * B k j) + matMul n ΔA B i j := by
              rw [hΔAB]
      _ = ∑ k : Fin n, (A i k + ΔA i k) * B k j := by
              unfold matMul
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro k _
              ring

/-- **Problem 3.5, common right-factor backward error.**

For square nonsingular `A`, the same forward-error matrix can be moved to the
right factor:

`fl(A*B) = A * (B + DeltaB)`,

with componentwise bound

`|DeltaB| <= gamma_n * |A_inv| * |A| * |B|`. -/
theorem matMul_backward_error_common_B_of_inverse (fp : FPModel) (n : ℕ)
    (A A_inv B : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n) (hA : IsInverse n A A_inv) :
    ∃ ΔB : Fin n → Fin n → ℝ,
      (∀ k j,
        |ΔB k j| ≤
          gamma fp n *
            ∑ l : Fin n,
              |A_inv k l| * (∑ r : Fin n, |A l r| * |B r j|)) ∧
      ∀ i j,
        fl_matMul fp n n n A B i j =
          ∑ k : Fin n, A i k * (B k j + ΔB k j) := by
  let E : Fin n → Fin n → ℝ :=
    fun i j => fl_matMul fp n n n A B i j - ∑ k : Fin n, A i k * B k j
  let ΔB : Fin n → Fin n → ℝ := matMul n A_inv E
  refine ⟨ΔB, ?_, ?_⟩
  · intro k j
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    have hE :
        ∀ l : Fin n,
          |E l j| ≤ gamma fp n * ∑ r : Fin n, |A l r| * |B r j| := by
      intro l
      simpa [E] using matMul_error_bound fp n n n A B hn l j
    calc
      |ΔB k j|
          = |∑ l : Fin n, A_inv k l * E l j| := by rfl
      _ ≤ ∑ l : Fin n, |A_inv k l * E l j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l : Fin n, |A_inv k l| * |E l j| := by
          apply Finset.sum_congr rfl
          intro l _
          rw [abs_mul]
      _ ≤
          ∑ l : Fin n,
            |A_inv k l| * (gamma fp n * ∑ r : Fin n, |A l r| * |B r j|) := by
          apply Finset.sum_le_sum
          intro l _
          exact mul_le_mul_of_nonneg_left (hE l) (abs_nonneg _)
      _ =
          gamma fp n *
            ∑ l : Fin n,
              |A_inv k l| * (∑ r : Fin n, |A l r| * |B r j|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
  · have hAAinv : matMul n A A_inv = idMatrix n := by
      ext i j
      exact hA.2 i j
    have hAΔB : matMul n A ΔB = E := by
      calc
        matMul n A ΔB = matMul n A (matMul n A_inv E) := rfl
        _ = matMul n (matMul n A A_inv) E := by
            rw [matMul_assoc]
        _ = matMul n (idMatrix n) E := by
            rw [hAAinv]
        _ = E := matMul_id_left n E
    intro i j
    calc
      fl_matMul fp n n n A B i j
          = (∑ k : Fin n, A i k * B k j) + E i j := by
              simp [E]
      _ = (∑ k : Fin n, A i k * B k j) + matMul n A ΔB i j := by
              rw [hAΔB]
      _ = ∑ k : Fin n, A i k * (B k j + ΔB k j) := by
              unfold matMul
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro k _
              ring

/-- A valid abstract floating-point model for the matrix-multiplication
counterexample.  It rounds only the product `1 * 2` upward by relative error
`1/10`; every other primitive operation is exact. -/
noncomputable def matMulCounterexampleFP : FPModel where
  u := 1 / 10
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => if x = 1 ∧ y = 2 then x * y * (11 / 10) else x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by
    intro x
    ring
  model_add := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_sub := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_mul := by
    intro x y
    by_cases h : x = 1 ∧ y = 2
    · refine ⟨1 / 10, by norm_num, ?_⟩
      simp [h]
      ring
    · refine ⟨0, by norm_num, ?_⟩
      simp [h]
  model_div := by
    intro x y _hy
    refine ⟨0, by norm_num, by ring⟩
  model_sqrt := by
    intro x _hx
    refine ⟨0, by norm_num, by ring⟩

/-- The counterexample has a valid `gamma_1` guard. -/
theorem matMulCounterexampleFP_gammaValid_one :
    gammaValid matMulCounterexampleFP 1 := by
  norm_num [gammaValid, matMulCounterexampleFP]

/-- The `1 x 1` left factor used in the matrix-multiplication
counterexample. -/
noncomputable def matMulCounterexampleA : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => 1

/-- The `1 x 2` right factor used in the matrix-multiplication
counterexample. -/
noncomputable def matMulCounterexampleB : Fin 1 → Fin 2 → ℝ :=
  fun _ j => if j = 0 then 1 else 2

/-- The computed matrix in the matrix-multiplication counterexample. -/
noncomputable def matMulCounterexampleC : Fin 1 → Fin 2 → ℝ :=
  fun _ j => if j = 0 then 1 else 11 / 5

/-- The concrete rounded product computes `[1, 11/5]` from `[1] * [1, 2]`. -/
theorem fl_matMul_counterexample_eq :
    fl_matMul matMulCounterexampleFP 1 1 2
      matMulCounterexampleA matMulCounterexampleB =
    matMulCounterexampleC := by
  ext i j
  fin_cases i
  fin_cases j <;>
    norm_num [fl_matMul, fl_matVec, fl_dotProduct, matMulCounterexampleFP,
      matMulCounterexampleA, matMulCounterexampleB, matMulCounterexampleC]

/-- Higham, p. 78: the columnwise backward errors for matrix multiplication
cannot in general be combined into one common backward error for `A`.

For this valid model and input, the first column forces the single perturbation
of `A` to be zero, while the second column forces it to be `1/10`.  Hence no
common `ΔA` exists at all, even before asking for a small componentwise bound. -/
theorem fl_matMul_counterexample_not_global_backward_A :
    ¬ ∃ ΔA : Fin 1 → Fin 1 → ℝ,
      ∀ i j,
        fl_matMul matMulCounterexampleFP 1 1 2
          matMulCounterexampleA matMulCounterexampleB i j =
          ∑ k : Fin 1,
            (matMulCounterexampleA i k + ΔA i k) *
              matMulCounterexampleB k j := by
  rintro ⟨ΔA, h⟩
  have h0 := h 0 0
  have h1 := h 0 1
  norm_num [fl_matMul, fl_matVec, fl_dotProduct, matMulCounterexampleFP,
    matMulCounterexampleA, matMulCounterexampleB] at h0 h1
  linarith

/-- The same counterexample rules out a source-style small common backward
error matrix `ΔA` with `gamma_1` componentwise radius. -/
theorem fl_matMul_counterexample_not_global_backward_A_gamma :
    ¬ ∃ ΔA : Fin 1 → Fin 1 → ℝ,
      (∀ i k,
        |ΔA i k| ≤ gamma matMulCounterexampleFP 1 *
          |matMulCounterexampleA i k|) ∧
      ∀ i j,
        fl_matMul matMulCounterexampleFP 1 1 2
          matMulCounterexampleA matMulCounterexampleB i j =
          ∑ k : Fin 1,
            (matMulCounterexampleA i k + ΔA i k) *
              matMulCounterexampleB k j := by
  rintro ⟨ΔA, _hbound, hrep⟩
  exact fl_matMul_counterexample_not_global_backward_A ⟨ΔA, hrep⟩

/-- A signed magnitude chosen to align with a pivot's sign. -/
noncomputable def signedMagnitudeForPivot (u mag pivot : ℝ) : ℝ :=
  if 0 ≤ pivot then u * mag else -(u * mag)

theorem signedMagnitudeForPivot_mul_pivot_eq (u mag pivot : ℝ) :
    signedMagnitudeForPivot u mag pivot * pivot = u * (mag * |pivot|) := by
  by_cases hp : 0 ≤ pivot
  · simp [signedMagnitudeForPivot, hp, abs_of_nonneg hp]
    ring
  · have hp_neg : pivot < 0 := lt_of_not_ge hp
    simp [signedMagnitudeForPivot, hp, abs_of_neg hp_neg]
    ring

theorem pivot_mul_signedMagnitudeForPivot_eq (u mag pivot : ℝ) :
    pivot * signedMagnitudeForPivot u mag pivot = u * (|pivot| * mag) := by
  rw [mul_comm, signedMagnitudeForPivot_mul_pivot_eq]
  ring

theorem abs_signedMagnitudeForPivot_le (u mag pivot : ℝ)
    (hu : 0 ≤ u) (hmag : 0 ≤ mag) :
    |signedMagnitudeForPivot u mag pivot| ≤ u * mag := by
  have hnonneg : 0 ≤ u * mag := mul_nonneg hu hmag
  by_cases hp : 0 ≤ pivot
  · simp [signedMagnitudeForPivot, hp, abs_of_nonneg hnonneg]
  · simp [signedMagnitudeForPivot, hp, abs_neg, abs_of_nonneg hnonneg]

/-- Perturb `A` in row `i` so the `(i,j)` entry of `(A+Delta A)B - AB`
attains the componentwise majorant. -/
noncomputable def matMulSharpDeltaA (u : ℝ)
    {m n p : ℕ} (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (i : Fin m) (j : Fin p) : Fin m → Fin n → ℝ :=
  fun r k =>
    if r = i then signedMagnitudeForPivot u |A i k| (B k j) else 0

/-- Perturb `B` in column `j` so the `(i,j)` entry of `A(B+Delta B)-AB`
attains the componentwise majorant. -/
noncomputable def matMulSharpDeltaB (u : ℝ)
    {m n p : ℕ} (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (i : Fin m) (j : Fin p) : Fin n → Fin p → ℝ :=
  fun k s =>
    if s = j then signedMagnitudeForPivot u |B k j| (A i k) else 0

/-- Higham, p. 78: the componentwise matrix-multiplication bound (3.13) is
sharp with respect to perturbations in `A`.

For any entry `(i,j)` and any nonnegative perturbation radius `u`, there is a
componentwise perturbation `Delta A` with `|Delta A| <= u|A|` such that the
corresponding entry error is exactly `u * (|A||B|)_{ij}`. -/
theorem matMul_forward_bound_sharp_A {m n p : ℕ} (u : ℝ) (hu : 0 ≤ u)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (i : Fin m) (j : Fin p) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ r k, |ΔA r k| ≤ u * |A r k|) ∧
      |(∑ k : Fin n, (A i k + ΔA i k) * B k j) -
          ∑ k : Fin n, A i k * B k j| =
        u * ∑ k : Fin n, |A i k| * |B k j| := by
  refine ⟨matMulSharpDeltaA u A B i j, ?_, ?_⟩
  · intro r k
    by_cases hri : r = i
    · subst r
      simpa [matMulSharpDeltaA] using
        abs_signedMagnitudeForPivot_le u |A i k| (B k j) hu (abs_nonneg _)
    · simp [matMulSharpDeltaA, hri, mul_nonneg hu (abs_nonneg _)]
  · have hdiff :
        (∑ k : Fin n, (A i k + matMulSharpDeltaA u A B i j i k) * B k j) -
            ∑ k : Fin n, A i k * B k j =
          ∑ k : Fin n, matMulSharpDeltaA u A B i j i k * B k j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hterm : ∀ k : Fin n,
        matMulSharpDeltaA u A B i j i k * B k j =
          u * (|A i k| * |B k j|) := by
      intro k
      simp [matMulSharpDeltaA, signedMagnitudeForPivot_mul_pivot_eq]
    have hsum_nonneg :
        0 ≤ ∑ k : Fin n, u * (|A i k| * |B k j|) := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg hu (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    rw [hdiff]
    calc
      |∑ k : Fin n, matMulSharpDeltaA u A B i j i k * B k j|
          = |∑ k : Fin n, u * (|A i k| * |B k j|)| := by
              congr 1
              apply Finset.sum_congr rfl
              intro k _
              exact hterm k
      _ = ∑ k : Fin n, u * (|A i k| * |B k j|) :=
              abs_of_nonneg hsum_nonneg
      _ = u * ∑ k : Fin n, |A i k| * |B k j| := by
              rw [Finset.mul_sum]

/-- Higham, p. 78: the same componentwise sharpness can be attained by
perturbing `B` instead of `A`. -/
theorem matMul_forward_bound_sharp_B {m n p : ℕ} (u : ℝ) (hu : 0 ≤ u)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (i : Fin m) (j : Fin p) :
    ∃ ΔB : Fin n → Fin p → ℝ,
      (∀ k s, |ΔB k s| ≤ u * |B k s|) ∧
      |(∑ k : Fin n, A i k * (B k j + ΔB k j)) -
          ∑ k : Fin n, A i k * B k j| =
        u * ∑ k : Fin n, |A i k| * |B k j| := by
  refine ⟨matMulSharpDeltaB u A B i j, ?_, ?_⟩
  · intro k s
    by_cases hsj : s = j
    · subst s
      simpa [matMulSharpDeltaB] using
        abs_signedMagnitudeForPivot_le u |B k j| (A i k) hu (abs_nonneg _)
    · simp [matMulSharpDeltaB, hsj, mul_nonneg hu (abs_nonneg _)]
  · have hdiff :
        (∑ k : Fin n, A i k * (B k j + matMulSharpDeltaB u A B i j k j)) -
            ∑ k : Fin n, A i k * B k j =
          ∑ k : Fin n, A i k * matMulSharpDeltaB u A B i j k j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hterm : ∀ k : Fin n,
        A i k * matMulSharpDeltaB u A B i j k j =
          u * (|A i k| * |B k j|) := by
      intro k
      simp [matMulSharpDeltaB, pivot_mul_signedMagnitudeForPivot_eq]
    have hsum_nonneg :
        0 ≤ ∑ k : Fin n, u * (|A i k| * |B k j|) := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg hu (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    rw [hdiff]
    calc
      |∑ k : Fin n, A i k * matMulSharpDeltaB u A B i j k j|
          = |∑ k : Fin n, u * (|A i k| * |B k j|)| := by
              congr 1
              apply Finset.sum_congr rfl
              intro k _
              exact hterm k
      _ = ∑ k : Fin n, u * (|A i k| * |B k j|) :=
              abs_of_nonneg hsum_nonneg
      _ = u * ∑ k : Fin n, |A i k| * |B k j| := by
              rw [Finset.mul_sum]

end NumStability
