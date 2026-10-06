-- Algorithms/MatVec.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Error
import NumStability.Analysis.Rounding
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Analysis.Stability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.DotProduct

namespace NumStability

open scoped BigOperators

/-- Floating-point matrix-vector product ŷ = fl(Ax).

    Each output component ŷᵢ is computed as the floating-point inner product
    of the ith row of A with x (Higham §3.5, "sdot" / inner product form):
      ŷᵢ = fl_dotProduct fp n (A i) x

    This is the row-by-row accumulation matching Algorithm 3.1 applied m times. -/
noncomputable def fl_matVec (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => fl_dotProduct fp n (A i) x

/-- Floating-point matrix-vector product in saxpy form.

    This is the column-oriented loop Higham describes on p. 77:
      `y = 0`; for each column `j`, update every component by
      `y_i = fl_add y_i (fl_mul A_ij x_j)`.

    The generalized version starts from an arbitrary initial vector; the source
    algorithm is `fl_matVecSaxpy`, which initializes with zero. -/
noncomputable def fl_matVecSaxpyInit (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (y0 : Fin m → ℝ) :
    Fin m → ℝ :=
  Fin.foldl n
    (fun y j => fun i => fp.fl_add (y i) (fp.fl_mul (A i j) (x j)))
    y0

/-- Floating-point matrix-vector product in zero-initialized saxpy form. -/
noncomputable def fl_matVecSaxpy (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fl_matVecSaxpyInit fp m n A x (fun _ => 0)

/-- Each component of the saxpy vector fold is the corresponding scalar fold. -/
theorem fl_matVecSaxpyInit_apply (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (y0 : Fin m → ℝ)
    (i : Fin m) :
    fl_matVecSaxpyInit fp m n A x y0 i =
      Fin.foldl n
        (fun acc j => fp.fl_add acc (fp.fl_mul (A i j) (x j)))
        (y0 i) := by
  induction n generalizing y0 with
  | zero =>
      simp [fl_matVecSaxpyInit]
  | succ n ih =>
      unfold fl_matVecSaxpyInit
      rw [Fin.foldl_succ]
      change
        (Fin.foldl n
          (fun y j => fun i => fp.fl_add (y i) (fp.fl_mul (A i j.succ) (x j.succ)))
          (fun i => fp.fl_add (y0 i) (fp.fl_mul (A i 0) (x 0)))) i =
        Fin.foldl (n + 1)
          (fun acc j => fp.fl_add acc (fp.fl_mul (A i j) (x j)))
          (y0 i)
      rw [Fin.foldl_succ]
      simpa using
        ih (fun i j => A i j.succ) (fun j => x j.succ)
          (fun i => fp.fl_add (y0 i) (fp.fl_mul (A i 0) (x 0)))

/-- Higham, p. 77: the sdot and saxpy matrix-vector loops commit the same
rounded operations and produce the same computed vector in this model.

The first saxpy update from zero is exact by `FPModel.fl_add_zero`, matching
the repository's tight dot-product convention that starts from the first
rounded product rather than charging an extra addition by zero. -/
theorem fl_matVecSaxpy_eq_sdot (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    fl_matVecSaxpy fp m n A x = fl_matVec fp m n A x := by
  ext i
  cases n with
  | zero =>
      simp [fl_matVecSaxpy, fl_matVecSaxpyInit, fl_matVec, fl_dotProduct]
  | succ n =>
      rw [fl_matVecSaxpy, fl_matVecSaxpyInit_apply]
      unfold fl_matVec fl_dotProduct
      have hpeel :
          Fin.foldl (n + 1)
              (fun acc j => fp.fl_add acc (fp.fl_mul (A i j) (x j))) 0 =
            Fin.foldl n
              (fun acc j => fp.fl_add acc (fp.fl_mul (A i j.succ) (x j.succ)))
              (fp.fl_add 0 (fp.fl_mul (A i 0) (x 0))) :=
        Fin.foldl_succ _ _
      rw [hpeel, fp.fl_add_zero]

/-- **Matrix-vector componentwise backward error** (Higham §3.5, equation 3.10).

    The computed matrix-vector product satisfies:
      ŷ = (A + ΔA)x,   |ΔA| ≤ γ(n)|A|  (componentwise)

    Formally: there exists ΔA : Fin m → Fin n → ℝ such that
      ∀ i j, |ΔA i j| ≤ γ(n) * |A i j|
      ∀ i, fl_matVec fp m n A x i = ∑ j, (A i j + ΔA i j) * x j

    Proof sketch: apply `dotProduct_backward_stable_x` to each row independently.
    The witness ΔA is constructed row-by-row via Classical.choose. -/
theorem matVec_backward_error (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n * |A i j|) ∧
      ∀ i, fl_matVec fp m n A x i = ∑ j : Fin n, (A i j + ΔA i j) * x j := by
  -- Extract per-row witnesses via Classical.choose
  let Δrow : Fin m → Fin n → ℝ :=
    fun i => Classical.choose (dotProduct_backward_stable_x fp n (A i) x hn)
  have hrow : ∀ i, (∀ j, |Δrow i j| ≤ gamma fp n * |A i j|) ∧
      fl_dotProduct fp n (A i) x = ∑ j : Fin n, (A i j + Δrow i j) * x j :=
    fun i => Classical.choose_spec (dotProduct_backward_stable_x fp n (A i) x hn)
  exact ⟨Δrow, fun i j => (hrow i).1 j, fun i => (hrow i).2⟩

/-- **Matrix-vector forward error bound** (Higham §3.5, equation 3.11).

    The componentwise forward error satisfies:
      |y - ŷ| ≤ γ(n)|A||x|  (componentwise)

    Formally: for each output component i,
      |fl_matVec fp m n A x i - ∑ j, A i j * x j| ≤ γ(n) * ∑ j, |A i j| * |x j|

    Proof sketch: apply `dotProduct_error_bound` to each row. -/
theorem matVec_error_bound (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hn : gammaValid fp n) :
    ∀ i : Fin m,
      |fl_matVec fp m n A x i - ∑ j : Fin n, A i j * x j| ≤
        gamma fp n * ∑ j : Fin n, |A i j| * |x j| :=
  fun i => dotProduct_error_bound fp n (A i) x hn

/-- **Matrix-vector infinity-norm forward error bound** (Higham §3.5, p. 77).

    For a square matrix-vector product, the componentwise forward bound (3.12) implies
      `||fl(Ax) - Ax||_∞ <= gamma_n ||A||_∞ ||x||_∞`.

    The rectangular variants from the source remain separate norm adapter
    obligations. -/
theorem matVec_error_bound_infNorm (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn : gammaValid fp n) :
    infNormVec
      (fun i : Fin n => fl_matVec fp n n A x i - ∑ j : Fin n, A i j * x j) ≤
        gamma fp n * infNorm A * infNormVec x := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hc : 0 ≤ gamma fp n * infNorm A * infNormVec x :=
    mul_nonneg (mul_nonneg hγ (infNorm_nonneg A)) (infNormVec_nonneg x)
  apply infNormVec_le_of_abs_le
  · intro i
    have hcomp := matVec_error_bound fp n n A x hn i
    have hsum_bound :
        ∑ j : Fin n, |A i j| * |x j| ≤ infNorm A * infNormVec x := by
      calc
        ∑ j : Fin n, |A i j| * |x j|
            ≤ ∑ j : Fin n, |A i j| * infNormVec x := by
                exact Finset.sum_le_sum (fun j _ =>
                  mul_le_mul_of_nonneg_left (abs_le_infNormVec x j) (abs_nonneg _))
        _ = (∑ j : Fin n, |A i j|) * infNormVec x := by
                rw [Finset.sum_mul]
        _ ≤ infNorm A * infNormVec x :=
                mul_le_mul_of_nonneg_right (row_sum_le_infNorm A i) (infNormVec_nonneg x)
    calc
      |fl_matVec fp n n A x i - ∑ j : Fin n, A i j * x j|
          ≤ gamma fp n * ∑ j : Fin n, |A i j| * |x j| := hcomp
      _ ≤ gamma fp n * (infNorm A * infNormVec x) :=
          mul_le_mul_of_nonneg_left hsum_bound hγ
      _ = gamma fp n * infNorm A * infNormVec x := by ring
  · exact hc

/-- **Rectangular matrix-vector infinity-norm forward error bound**.

    For `A : Fin m -> Fin n -> ℝ`, the componentwise forward bound (3.12) implies
      `||fl(Ax) - Ax||_∞ <= gamma_n ||A||_∞ ||x||_∞`,
    where `||A||_∞` is the rectangular maximum absolute row sum. -/
theorem matVec_error_bound_infNormRect (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hn : gammaValid fp n) :
    infNormVec
      (fun i : Fin m => fl_matVec fp m n A x i - ∑ j : Fin n, A i j * x j) ≤
        gamma fp n * infNormRect A * infNormVec x := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hc : 0 ≤ gamma fp n * infNormRect A * infNormVec x :=
    mul_nonneg (mul_nonneg hγ (infNormRect_nonneg A)) (infNormVec_nonneg x)
  apply infNormVec_le_of_abs_le
  · intro i
    have hcomp := matVec_error_bound fp m n A x hn i
    have hsum_bound :
        ∑ j : Fin n, |A i j| * |x j| ≤ infNormRect A * infNormVec x := by
      calc
        ∑ j : Fin n, |A i j| * |x j|
            ≤ ∑ j : Fin n, |A i j| * infNormVec x := by
                exact Finset.sum_le_sum (fun j _ =>
                  mul_le_mul_of_nonneg_left (abs_le_infNormVec x j) (abs_nonneg _))
        _ = (∑ j : Fin n, |A i j|) * infNormVec x := by
                rw [Finset.sum_mul]
        _ ≤ infNormRect A * infNormVec x :=
                mul_le_mul_of_nonneg_right
                  (row_sum_le_infNormRect A i) (infNormVec_nonneg x)
    calc
      |fl_matVec fp m n A x i - ∑ j : Fin n, A i j * x j|
          ≤ gamma fp n * ∑ j : Fin n, |A i j| * |x j| := hcomp
      _ ≤ gamma fp n * (infNormRect A * infNormVec x) :=
          mul_le_mul_of_nonneg_left hsum_bound hγ
      _ = gamma fp n * infNormRect A * infNormVec x := by ring
  · exact hc

/-- **Matrix-vector 1-norm forward error bound** (Higham §3.5, p. 77).

    For a square matrix-vector product, the componentwise forward bound (3.12) implies
      `||fl(Ax) - Ax||_1 <= gamma_n ||A||_1 ||x||_1`.

    The vector 1-norm is written explicitly as `sum_i |v_i|`; `oneNorm` is the
    repository's matrix 1-norm wrapper, i.e. the maximum absolute column sum. -/
theorem matVec_error_bound_oneNorm (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn : gammaValid fp n) :
    (∑ i : Fin n, |fl_matVec fp n n A x i - ∑ j : Fin n, A i j * x j|) ≤
      gamma fp n * oneNorm A * (∑ j : Fin n, |x j|) := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hcomp_sum :
      (∑ i : Fin n, |fl_matVec fp n n A x i - ∑ j : Fin n, A i j * x j|) ≤
        ∑ i : Fin n, gamma fp n * ∑ j : Fin n, |A i j| * |x j| :=
    Finset.sum_le_sum (fun i _ => matVec_error_bound fp n n A x hn i)
  have hdouble :
      (∑ i : Fin n, ∑ j : Fin n, |A i j| * |x j|) =
        ∑ j : Fin n, |x j| * ∑ i : Fin n, |A i j| := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul]
    ring
  have hdouble_bound :
      (∑ i : Fin n, ∑ j : Fin n, |A i j| * |x j|) ≤
        oneNorm A * ∑ j : Fin n, |x j| := by
    rw [hdouble]
    calc
      ∑ j : Fin n, |x j| * ∑ i : Fin n, |A i j|
          ≤ ∑ j : Fin n, |x j| * oneNorm A :=
              Finset.sum_le_sum (fun j _ =>
                mul_le_mul_of_nonneg_left (col_sum_le_oneNorm A j) (abs_nonneg _))
      _ = oneNorm A * ∑ j : Fin n, |x j| := by
              rw [← Finset.sum_mul]
              ring
  calc
    (∑ i : Fin n, |fl_matVec fp n n A x i - ∑ j : Fin n, A i j * x j|)
        ≤ ∑ i : Fin n, gamma fp n * ∑ j : Fin n, |A i j| * |x j| := hcomp_sum
    _ = gamma fp n * (∑ i : Fin n, ∑ j : Fin n, |A i j| * |x j|) := by
          rw [← Finset.mul_sum]
    _ ≤ gamma fp n * (oneNorm A * ∑ j : Fin n, |x j|) :=
          mul_le_mul_of_nonneg_left hdouble_bound hγ
    _ = gamma fp n * oneNorm A * (∑ j : Fin n, |x j|) := by ring

/-- **Rectangular matrix-vector 1-norm forward error bound**.

    For `A : Fin m -> Fin n -> ℝ`, the componentwise forward bound (3.12) implies
      `||fl(Ax) - Ax||_1 <= gamma_n ||A||_1 ||x||_1`,
    where `||A||_1` is the rectangular maximum absolute column sum and the
    vector 1-norms are written as explicit sums. -/
theorem matVec_error_bound_oneNormRect (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hn : gammaValid fp n) :
    (∑ i : Fin m, |fl_matVec fp m n A x i - ∑ j : Fin n, A i j * x j|) ≤
      gamma fp n * oneNormRect A * (∑ j : Fin n, |x j|) := by
  have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hcomp_sum :
      (∑ i : Fin m, |fl_matVec fp m n A x i - ∑ j : Fin n, A i j * x j|) ≤
        ∑ i : Fin m, gamma fp n * ∑ j : Fin n, |A i j| * |x j| :=
    Finset.sum_le_sum (fun i _ => matVec_error_bound fp m n A x hn i)
  have hdouble :
      (∑ i : Fin m, ∑ j : Fin n, |A i j| * |x j|) =
        ∑ j : Fin n, |x j| * ∑ i : Fin m, |A i j| := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul]
    ring
  have hdouble_bound :
      (∑ i : Fin m, ∑ j : Fin n, |A i j| * |x j|) ≤
        oneNormRect A * ∑ j : Fin n, |x j| := by
    rw [hdouble]
    calc
      ∑ j : Fin n, |x j| * ∑ i : Fin m, |A i j|
          ≤ ∑ j : Fin n, |x j| * oneNormRect A :=
              Finset.sum_le_sum (fun j _ =>
                mul_le_mul_of_nonneg_left (col_sum_le_oneNormRect A j) (abs_nonneg _))
      _ = oneNormRect A * ∑ j : Fin n, |x j| := by
              rw [← Finset.sum_mul]
              ring
  calc
    (∑ i : Fin m, |fl_matVec fp m n A x i - ∑ j : Fin n, A i j * x j|)
        ≤ ∑ i : Fin m, gamma fp n * ∑ j : Fin n, |A i j| * |x j| := hcomp_sum
    _ = gamma fp n * (∑ i : Fin m, ∑ j : Fin n, |A i j| * |x j|) := by
          rw [← Finset.mul_sum]
    _ ≤ gamma fp n * (oneNormRect A * ∑ j : Fin n, |x j|) :=
          mul_le_mul_of_nonneg_left hdouble_bound hγ
    _ = gamma fp n * oneNormRect A * (∑ j : Fin n, |x j|) := by ring

/-- **Matrix-vector row-wise backward stability** (Higham §3.5).

    Each row of `fl_matVec` is computed by `fl_dotProduct`, which is relatively
    componentwise backward stable with bound γ(n).  This theorem makes that
    explicit: the per-row inner product algorithm satisfies
    `isRelComponentwiseBackwardStable` with the row of A as the perturbed input.

    The global backward error for the full matrix (3.10) is captured by
    `matVec_backward_error`, which constructs a perturbation ΔA row-by-row. -/
theorem matVec_row_isRelBackwardStable (fp : FPModel) (n : ℕ)
    (hn : gammaValid fp n) :
    isRelComponentwiseBackwardStable n
      (fun a x => ∑ j : Fin n, a j * x j)
      (fun a x => fl_dotProduct fp n a x)
      (gamma fp n) :=
  dotProduct_isRelBackwardStable fp n hn

/-- Higham Chapter 3's printed rectangular matrix-vector 2-norm bound:

`‖Ax - fl(Ax)‖₂ ≤ sqrt(min(m,n)) γ_n ‖A‖₂ ‖x‖₂`.

The proof starts from the concrete row-wise backward error `ΔA`, derives its
Frobenius bound from the componentwise estimate, and then uses Lemma 6.6(a)
to convert `‖A‖_F` to the exact rectangular operator 2-norm. -/
theorem matVec_error_bound_twoNormRect (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hn : gammaValid fp n) :
    vecNorm2
        (fun i : Fin m =>
          (∑ j : Fin n, A i j * x j) - fl_matVec fp m n A x i) ≤
      Real.sqrt (Nat.min m n : ℝ) * gamma fp n * rectOpNorm2 A *
        vecNorm2 x := by
  obtain ⟨ΔA, hΔA, hfl⟩ := matVec_backward_error fp m n A x hn
  let e : Fin m → ℝ := fun i =>
    fl_matVec fp m n A x i - ∑ j : Fin n, A i j * x j
  have he : e = rectMatMulVec ΔA x := by
    ext i
    dsimp [e]
    rw [hfl i]
    unfold rectMatMulVec
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hγnonneg : 0 ≤ gamma fp n := gamma_nonneg fp hn
  let B : Fin m → Fin n → ℝ := fun i j => gamma fp n * |A i j|
  have hBnonneg : ∀ i j, 0 ≤ B i j := by
    intro i j
    exact mul_nonneg hγnonneg (abs_nonneg (A i j))
  have hΔFraw : frobNormRect ΔA ≤ frobNormRect B :=
    frobNormRect_le_of_entry_abs_le ΔA B hBnonneg hΔA
  have hBF : frobNormRect B = gamma fp n * frobNormRect A := by
    calc
      frobNormRect B = |gamma fp n| *
          frobNormRect (fun i j => |A i j|) := by
            simpa [B] using
              (frobNormRect_smul (gamma fp n) (fun i j => |A i j|))
      _ = gamma fp n * frobNormRect A := by
            rw [abs_of_nonneg hγnonneg, frobNormRect_abs]
  have hΔF : frobNormRect ΔA ≤ gamma fp n * frobNormRect A := by
    rw [← hBF]
    exact hΔFraw
  have hsource_neg :
      (fun i : Fin m =>
        (∑ j : Fin n, A i j * x j) - fl_matVec fp m n A x i) =
        fun i => -e i := by
    ext i
    simp only [e]
    ring
  rw [hsource_neg, vecNorm2_neg, he]
  calc
    vecNorm2 (rectMatMulVec ΔA x)
        ≤ frobNormRect ΔA * vecNorm2 x :=
          vecNorm2_rectMatMulVec_le_frobNormRect_mul ΔA x
    _ ≤ (gamma fp n * frobNormRect A) * vecNorm2 x :=
          mul_le_mul_of_nonneg_right hΔF (vecNorm2_nonneg x)
    _ ≤ (gamma fp n *
          (Real.sqrt (Nat.min m n : ℝ) * rectOpNorm2 A)) * vecNorm2 x := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (frobNormRect_le_sqrt_min_mul_rectOpNorm2 A) hγnonneg)
            (vecNorm2_nonneg x)
    _ = Real.sqrt (Nat.min m n : ℝ) * gamma fp n * rectOpNorm2 A *
          vecNorm2 x := by ring

end NumStability
