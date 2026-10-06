import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.MatrixInversion

/-!
# Chapter14 Problem05 InverseBasedSolve MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, right-approximate-inverse
    residual bound.

If `X` has a small right inverse residual, `|A X - I| <= u |A||X|`, and
`x_hat = fl(X b)`, then
`|A x_hat - b| <= gamma_{n+1} |A||X||b|` componentwise. -/
theorem higham14_problem14_5_right_inverse_solve_residual_bound
    (n : ℕ) (fp : FPModel)
    (A X : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hRightRes : ∀ i j : Fin n,
      |inverseRightResidual n A X i j| ≤
        fp.u * ∑ k : Fin n, |A i k| * |X k j|) :
    let x_hat := fl_matVec fp n n X b
    ∀ i : Fin n,
      |∑ j : Fin n, A i j * x_hat j - b i| ≤
        gamma fp (n + 1) *
          ∑ j : Fin n, |A i j| * (∑ k : Fin n, |X j k| * |b k|) := by
  intro x_hat i
  have hn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  obtain ⟨ΔX, hΔX_bound, hΔX_eq⟩ := matVec_backward_error fp n n X b hn
  change |∑ j : Fin n, A i j * fl_matVec fp n n X b j - b i| ≤ _
  let S : ℝ := ∑ j : Fin n, |A i j| * (∑ k : Fin n, |X j k| * |b k|)
  have hcoeff : fp.u + gamma fp n ≤ gamma fp (n + 1) :=
    higham14_unit_roundoff_add_gamma_le_gamma_succ fp n hn1
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  have hxhat : ∀ j : Fin n,
      fl_matVec fp n n X b j =
        ∑ k : Fin n, (X j k + ΔX j k) * b k := hΔX_eq
  have hmain :
      ∑ j : Fin n, A i j * fl_matVec fp n n X b j - b i =
        (∑ k : Fin n, inverseRightResidual n A X i k * b k) +
          ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k) := by
    have hsplit :
        ∑ j : Fin n, A i j * fl_matVec fp n n X b j =
          ∑ j : Fin n, A i j * (∑ k : Fin n, X j k * b k) +
            ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hxhat j, ← mul_add]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hAXb :
        ∑ j : Fin n, A i j * (∑ k : Fin n, X j k * b k) =
          ∑ k : Fin n, (∑ j : Fin n, A i j * X j k) * b k := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    have hb :
        b i = ∑ k : Fin n, (if i = k then (1 : ℝ) else 0) * b k := by
      simp [Finset.sum_ite_eq, Finset.mem_univ]
    have hresExpand :
        (∑ k : Fin n, (∑ j : Fin n, A i j * X j k) * b k) -
          ∑ k : Fin n, (if i = k then (1 : ℝ) else 0) * b k =
        ∑ k : Fin n, inverseRightResidual n A X i k * b k := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp [inverseRightResidual, matMul, idMatrix]
      by_cases h : i = k
      · subst i
        simp
        ring_nf
      · simp [h]
    calc
      ∑ j : Fin n, A i j * fl_matVec fp n n X b j - b i
          = (∑ k : Fin n, (∑ j : Fin n, A i j * X j k) * b k +
              ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)) -
              ∑ k : Fin n, (if i = k then (1 : ℝ) else 0) * b k := by
            rw [hsplit, hAXb, hb]
      _ = ((∑ k : Fin n, (∑ j : Fin n, A i j * X j k) * b k) -
              ∑ k : Fin n, (if i = k then (1 : ℝ) else 0) * b k) +
            ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k) := by
            ring
      _ = (∑ k : Fin n, inverseRightResidual n A X i k * b k) +
            ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k) := by
            rw [hresExpand]
  have hres_part :
      |∑ k : Fin n, inverseRightResidual n A X i k * b k| ≤ fp.u * S := by
    calc
      |∑ k : Fin n, inverseRightResidual n A X i k * b k|
          ≤ ∑ k : Fin n, |inverseRightResidual n A X i k * b k| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |inverseRightResidual n A X i k| * |b k| := by
            apply Finset.sum_congr rfl
            intro k _
            exact abs_mul _ _
      _ ≤ ∑ k : Fin n, (fp.u * ∑ j : Fin n, |A i j| * |X j k|) * |b k| := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right (hRightRes i k) (abs_nonneg _)
      _ = fp.u * S := by
            simp only [S]
            calc
              ∑ k : Fin n, (fp.u * ∑ j : Fin n, |A i j| * |X j k|) * |b k|
                  = ∑ k : Fin n, ∑ j : Fin n,
                      fp.u * (|A i j| * |X j k|) * |b k| := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [Finset.mul_sum, Finset.sum_mul]
              _ = ∑ j : Fin n, ∑ k : Fin n,
                      fp.u * (|A i j| * |X j k|) * |b k| := by
                    rw [Finset.sum_comm]
              _ = ∑ j : Fin n, fp.u * (|A i j| * ∑ k : Fin n, |X j k| * |b k|) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    calc
                      ∑ k : Fin n, fp.u * (|A i j| * |X j k|) * |b k|
                          = ∑ k : Fin n, fp.u * (|A i j| * (|X j k| * |b k|)) := by
                            apply Finset.sum_congr rfl
                            intro k _
                            ring
                      _ = fp.u * (∑ k : Fin n, |A i j| * (|X j k| * |b k|)) := by
                            rw [← Finset.mul_sum]
                      _ = fp.u * (|A i j| * ∑ k : Fin n, |X j k| * |b k|) := by
                            congr 1
                            rw [← Finset.mul_sum]
              _ = fp.u * ∑ j : Fin n, |A i j| * (∑ k : Fin n, |X j k| * |b k|) := by
                    rw [Finset.mul_sum]
  have hround_part :
      |∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)| ≤
        gamma fp n * S := by
    calc
      |∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)|
          ≤ ∑ j : Fin n, |A i j * (∑ k : Fin n, ΔX j k * b k)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |A i j| * |∑ k : Fin n, ΔX j k * b k| := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul _ _
      _ ≤ ∑ j : Fin n, |A i j| * (∑ k : Fin n, |ΔX j k| * |b k|) := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            calc
              |∑ k : Fin n, ΔX j k * b k|
                  ≤ ∑ k : Fin n, |ΔX j k * b k| :=
                    Finset.abs_sum_le_sum_abs _ _
              _ = ∑ k : Fin n, |ΔX j k| * |b k| := by
                    apply Finset.sum_congr rfl
                    intro k _
                    exact abs_mul _ _
      _ ≤ ∑ j : Fin n, |A i j| *
            (∑ k : Fin n, (gamma fp n * |X j k|) * |b k|) := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right (hΔX_bound j k) (abs_nonneg _)
      _ = gamma fp n * S := by
            simp only [S]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            calc
              |A i j| * (∑ k : Fin n, gamma fp n * |X j k| * |b k|)
                  = |A i j| * (gamma fp n * (∑ k : Fin n, |X j k| * |b k|)) := by
                    congr 1
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro k _
                    ring
              _ = gamma fp n * (|A i j| * ∑ k : Fin n, |X j k| * |b k|) := by
                    ring
  calc
    |∑ j : Fin n, A i j * fl_matVec fp n n X b j - b i|
        = |(∑ k : Fin n, inverseRightResidual n A X i k * b k) +
            ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)| := by
          rw [hmain]
    _ ≤ |∑ k : Fin n, inverseRightResidual n A X i k * b k| +
          |∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)| :=
          abs_add_le _ _
    _ ≤ fp.u * S + gamma fp n * S :=
          add_le_add hres_part hround_part
    _ = (fp.u + gamma fp n) * S := by ring
    _ ≤ gamma fp (n + 1) * S :=
          mul_le_mul_of_nonneg_right hcoeff hS_nonneg

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, left-approximate-inverse
    residual bound.

If `Y` has a small left inverse residual, `|Y A - I| <= u |Y||A|`, and
`b = A x`, `y_hat = fl(Y b)`, then
`|A y_hat - b| <= gamma_{n+1} |A||Y||A||x|` componentwise. -/
theorem higham14_problem14_5_left_inverse_solve_residual_bound
    (n : ℕ) (fp : FPModel)
    (A Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeftRes : ∀ i j : Fin n,
      |inverseLeftResidual n A Y i j| ≤
        fp.u * ∑ k : Fin n, |Y i k| * |A k j|) :
    let b := matMulVec n A x
    let y_hat := fl_matVec fp n n Y b
    ∀ i : Fin n,
      |matMulVec n A y_hat i - b i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n A)
            (matMulVec n (absMatrix n Y)
              (matMulVec n (absMatrix n A) (absVec n x))) i := by
  intro b y_hat i
  have hn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  obtain ⟨ΔY, hΔY_bound, hΔY_eq⟩ :=
    matVec_backward_error fp n n Y (matMulVec n A x) hn
  change |matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
      matMulVec n A x i| ≤ _
  let R := inverseLeftResidual n A Y
  let S : ℝ :=
    matMulVec n (absMatrix n A)
      (matMulVec n (absMatrix n Y)
        (matMulVec n (absMatrix n A) (absVec n x))) i
  have hcoeff : fp.u + gamma fp n ≤ gamma fp (n + 1) :=
    higham14_unit_roundoff_add_gamma_le_gamma_succ fp n hn1
  have hS_nonneg : 0 ≤ S := by
    simp only [S, matMulVec, absMatrix, absVec]
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun l _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))))))
  have hyhat_vec :
      fl_matVec fp n n Y (matMulVec n A x) =
        matMulVec n (fun i j => Y i j + ΔY i j) (matMulVec n A x) := by
    ext j
    simpa [matMulVec] using hΔY_eq j
  have hYAx_split :
      matMulVec n Y (matMulVec n A x) =
        fun j => matMulVec n R x j + x j := by
    ext j
    rw [← matMulVec_matMul n Y A x j]
    simp only [R, inverseLeftResidual, matMulVec, matMul, idMatrix]
    have hdelta :
        (∑ l : Fin n, (if j = l then (1 : ℝ) else 0) * x l) = x j := by
      simp [Finset.sum_ite_eq, Finset.mem_univ]
    calc
      ∑ l : Fin n, (∑ k : Fin n, Y j k * A k l) * x l
          = ∑ l : Fin n,
              (((∑ k : Fin n, Y j k * A k l) -
                (if j = l then (1 : ℝ) else 0)) * x l +
                (if j = l then (1 : ℝ) else 0) * x l) := by
            apply Finset.sum_congr rfl
            intro l _
            ring
      _ = (∑ l : Fin n,
              ((∑ k : Fin n, Y j k * A k l) -
                (if j = l then (1 : ℝ) else 0)) * x l) +
            ∑ l : Fin n, (if j = l then (1 : ℝ) else 0) * x l := by
            rw [Finset.sum_add_distrib]
      _ = (∑ l : Fin n,
              ((∑ k : Fin n, Y j k * A k l) -
                (if j = l then (1 : ℝ) else 0)) * x l) + x j := by
            rw [hdelta]
  have hmain :
      matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
          matMulVec n A x i =
        matMulVec n A (matMulVec n R x) i +
          matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i := by
    calc
      matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
          matMulVec n A x i
          = matMulVec n A
              (matMulVec n (fun j k => Y j k + ΔY j k) (matMulVec n A x)) i -
              matMulVec n A x i := by
                rw [hyhat_vec]
      _ = matMulVec n A
              (fun j => matMulVec n Y (matMulVec n A x) j +
                matMulVec n ΔY (matMulVec n A x) j) i -
              matMulVec n A x i := by
                rw [matMulVec_add_left]
      _ = (matMulVec n A (matMulVec n Y (matMulVec n A x)) i +
              matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i) -
              matMulVec n A x i := by
                rw [matMulVec_add_right]
      _ = (matMulVec n A (fun j => matMulVec n R x j + x j) i +
              matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i) -
              matMulVec n A x i := by
                rw [hYAx_split]
      _ = ((matMulVec n A (matMulVec n R x) i + matMulVec n A x i) +
              matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i) -
              matMulVec n A x i := by
                rw [matMulVec_add_right]
      _ = matMulVec n A (matMulVec n R x) i +
            matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i := by
              ring
  have hres_part :
      |matMulVec n A (matMulVec n R x) i| ≤ fp.u * S := by
    calc
      |matMulVec n A (matMulVec n R x) i|
          ≤ ∑ j : Fin n, |A i j| * |matMulVec n R x j| :=
            abs_matMulVec_le n A (matMulVec n R x) i
      _ ≤ ∑ j : Fin n, |A i j| * (∑ k : Fin n, |R j k| * |x k|) := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left
              (abs_matMulVec_le n R x j) (abs_nonneg _)
      _ ≤ ∑ j : Fin n, |A i j| *
            (∑ k : Fin n, (fp.u * ∑ l : Fin n, |Y j l| * |A l k|) * |x k|) := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right
              (by simpa [R] using hLeftRes j k) (abs_nonneg _)
      _ = fp.u * S := by
            simp only [S, matMulVec, absMatrix, absVec]
            calc
              ∑ j : Fin n, |A i j| *
                  (∑ k : Fin n, (fp.u * ∑ l : Fin n, |Y j l| * |A l k|) *
                    |x k|)
                  = ∑ j : Fin n, |A i j| *
                      (fp.u * ∑ l : Fin n, |Y j l| *
                        (∑ k : Fin n, |A l k| * |x k|)) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    congr 1
                    calc
                      ∑ k : Fin n, (fp.u * ∑ l : Fin n, |Y j l| * |A l k|) *
                          |x k|
                          = ∑ k : Fin n, ∑ l : Fin n,
                              fp.u * (|Y j l| * |A l k|) * |x k| := by
                            apply Finset.sum_congr rfl
                            intro k _
                            rw [Finset.mul_sum, Finset.sum_mul]
                      _ = ∑ l : Fin n, ∑ k : Fin n,
                              fp.u * (|Y j l| * |A l k|) * |x k| := by
                            rw [Finset.sum_comm]
                      _ = fp.u * ∑ l : Fin n, |Y j l| *
                              (∑ k : Fin n, |A l k| * |x k|) := by
                            rw [Finset.mul_sum]
                            apply Finset.sum_congr rfl
                            intro l _
                            calc
                              ∑ k : Fin n, fp.u * (|Y j l| * |A l k|) * |x k|
                                  = fp.u *
                                      (∑ k : Fin n, |Y j l| * (|A l k| * |x k|)) := by
                                    rw [Finset.mul_sum]
                                    apply Finset.sum_congr rfl
                                    intro k _
                                    ring
                              _ = fp.u * (|Y j l| *
                                      (∑ k : Fin n, |A l k| * |x k|)) := by
                                    congr 1
                                    rw [← Finset.mul_sum]
              _ = ∑ j : Fin n, fp.u *
                    (|A i j| * ∑ l : Fin n, |Y j l| *
                      (∑ k : Fin n, |A l k| * |x k|)) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
              _ = fp.u * ∑ j : Fin n, |A i j| *
                    (∑ l : Fin n, |Y j l| *
                      (∑ k : Fin n, |A l k| * |x k|)) := by
                    rw [Finset.mul_sum]
  have hround_part :
      |matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i| ≤
        gamma fp n * S := by
    calc
      |matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i|
          ≤ ∑ j : Fin n, |A i j| *
              |matMulVec n ΔY (matMulVec n A x) j| :=
            abs_matMulVec_le n A (matMulVec n ΔY (matMulVec n A x)) i
      _ ≤ ∑ j : Fin n, |A i j| *
            (∑ k : Fin n, |ΔY j k| * |matMulVec n A x k|) := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left
              (abs_matMulVec_le n ΔY (matMulVec n A x) j) (abs_nonneg _)
      _ ≤ ∑ j : Fin n, |A i j| *
            (∑ k : Fin n, (gamma fp n * |Y j k|) *
              (∑ l : Fin n, |A k l| * |x l|)) := by
            apply Finset.sum_le_sum
            intro j _
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul
              (hΔY_bound j k)
              (abs_matMulVec_le n A x k)
              (abs_nonneg _)
              (mul_nonneg (gamma_nonneg fp hn) (abs_nonneg _))
      _ = gamma fp n * S := by
            change
              ∑ j : Fin n, |A i j| *
                  (∑ k : Fin n, (gamma fp n * |Y j k|) *
                    (∑ l : Fin n, |A k l| * |x l|)) =
                gamma fp n * ∑ j : Fin n, |A i j| *
                  (∑ k : Fin n, |Y j k| *
                    (∑ l : Fin n, |A k l| * |x l|))
            calc
              ∑ j : Fin n, |A i j| *
                  (∑ k : Fin n, (gamma fp n * |Y j k|) *
                    (∑ l : Fin n, |A k l| * |x l|))
                  = ∑ j : Fin n, gamma fp n *
                      (|A i j| * ∑ k : Fin n, |Y j k| *
                        (∑ l : Fin n, |A k l| * |x l|)) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    have hinner :
                        (∑ k : Fin n, (gamma fp n * |Y j k|) *
                          (∑ l : Fin n, |A k l| * |x l|)) =
                        gamma fp n * ∑ k : Fin n, |Y j k| *
                          (∑ l : Fin n, |A k l| * |x l|) := by
                      calc
                        ∑ k : Fin n, (gamma fp n * |Y j k|) *
                            (∑ l : Fin n, |A k l| * |x l|)
                            = ∑ k : Fin n, gamma fp n *
                              (|Y j k| * (∑ l : Fin n, |A k l| * |x l|)) := by
                              apply Finset.sum_congr rfl
                              intro k _
                              ring
                        _ = gamma fp n * ∑ k : Fin n, |Y j k| *
                              (∑ l : Fin n, |A k l| * |x l|) := by
                              rw [Finset.mul_sum]
                    rw [hinner]
                    ring
              _ = gamma fp n * ∑ j : Fin n, |A i j| *
                    (∑ k : Fin n, |Y j k| *
                      (∑ l : Fin n, |A k l| * |x l|)) := by
                    rw [Finset.mul_sum]
  have hfinal :
      |matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
        matMulVec n A x i| ≤ gamma fp (n + 1) * S := by
    calc
      |matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
          matMulVec n A x i|
          = |matMulVec n A (matMulVec n R x) i +
              matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i| := by
            rw [hmain]
      _ ≤ |matMulVec n A (matMulVec n R x) i| +
            |matMulVec n A (matMulVec n ΔY (matMulVec n A x)) i| :=
            abs_add_le _ _
      _ ≤ fp.u * S + gamma fp n * S :=
            add_le_add hres_part hround_part
      _ = (fp.u + gamma fp n) * S := by ring
      _ ≤ gamma fp (n + 1) * S :=
            mul_le_mul_of_nonneg_right hcoeff hS_nonneg
  change |matMulVec n A (fl_matVec fp n n Y (matMulVec n A x)) i -
      matMulVec n A x i| ≤ gamma fp (n + 1) * S
  exact hfinal

/-- Higham, 2nd ed., Chapter 14, Problem 14.5 support:
    expanding the left inverse residual gives `Y(Ax) = (YA-I)x + x`. -/
lemma higham14_inverseLeftResidual_mulVec_add_self (n : ℕ)
    (A Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    matMulVec n Y (matMulVec n A x) =
      fun j => matMulVec n (inverseLeftResidual n A Y) x j + x j := by
  ext j
  rw [← matMulVec_matMul n Y A x j]
  simp only [inverseLeftResidual, matMulVec, matMul, idMatrix]
  have hdelta :
      (∑ l : Fin n, (if j = l then (1 : ℝ) else 0) * x l) = x j := by
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  calc
    ∑ l : Fin n, (∑ k : Fin n, Y j k * A k l) * x l
        = ∑ l : Fin n,
            (((∑ k : Fin n, Y j k * A k l) -
              (if j = l then (1 : ℝ) else 0)) * x l +
              (if j = l then (1 : ℝ) else 0) * x l) := by
          apply Finset.sum_congr rfl
          intro l _
          ring
    _ = (∑ l : Fin n,
            ((∑ k : Fin n, Y j k * A k l) -
              (if j = l then (1 : ℝ) else 0)) * x l) +
          ∑ l : Fin n, (if j = l then (1 : ℝ) else 0) * x l := by
          rw [Finset.sum_add_distrib]
    _ = (∑ l : Fin n,
            ((∑ k : Fin n, Y j k * A k l) -
              (if j = l then (1 : ℝ) else 0)) * x l) + x j := by
          rw [hdelta]

/-- Higham, 2nd ed., Chapter 14, Problem 14.5 support:
    a componentwise residual envelope transfers to a componentwise forward-error
    envelope by left multiplication with `|A⁻¹|`. -/
theorem higham14_problem14_5_forward_error_of_residual_bound
    (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    (x x_hat b Eres : Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv)
    (hsolve : matMulVec n A x = b)
    (hres : ∀ i : Fin n, |matMulVec n A x_hat i - b i| ≤ Eres i) :
    ∀ i : Fin n,
      |x_hat i - x i| ≤ matMulVec n (absMatrix n A_inv) Eres i := by
  let r : Fin n → ℝ := fun k => matMulVec n A x_hat k - b k
  let d : Fin n → ℝ := fun j => x_hat j - x j
  have hr : r = matMulVec n A d := by
    ext i
    dsimp [r, d]
    rw [← congrFun hsolve i]
    unfold matMulVec
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmat : matMul n A_inv A = idMatrix n := by
    ext i j
    exact hLeft i j
  have hd : d = matMulVec n A_inv r := by
    rw [hr]
    ext i
    rw [← matMulVec_matMul n A_inv A d i]
    rw [hmat, matMulVec_id]
  intro i
  calc
    |x_hat i - x i| = |d i| := rfl
    _ = |matMulVec n A_inv r i| := by rw [hd]
    _ ≤ ∑ j : Fin n, |A_inv i j| * |r j| :=
        abs_matMulVec_le n A_inv r i
    _ ≤ ∑ j : Fin n, |A_inv i j| * Eres j := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hres j) (abs_nonneg _)
    _ = matMulVec n (absMatrix n A_inv) Eres i := by
        simp [matMulVec, absMatrix]

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, right-approximate-inverse
    forward-error consequence.

If `X` has a small right inverse residual and `A x = b`, then the residual
bound for `x_hat = fl(X b)` gives the componentwise forward-error envelope
`|x_hat-x| <= gamma_{n+1} |A⁻¹||A||X||b|`. -/
theorem higham14_problem14_5_right_inverse_solve_forward_error_bound
    (n : ℕ) (fp : FPModel)
    (A A_inv X : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeft : IsLeftInverse n A A_inv)
    (hsolve : matMulVec n A x = b)
    (hRightRes : ∀ i j : Fin n,
      |inverseRightResidual n A X i j| ≤
        fp.u * ∑ k : Fin n, |A i k| * |X k j|) :
    let x_hat := fl_matVec fp n n X b
    ∀ i : Fin n,
      |x_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n (absMatrix n X) (absVec n b))) i := by
  intro x_hat i
  let E : Fin n → ℝ :=
    matMulVec n (absMatrix n A)
      (matMulVec n (absMatrix n X) (absVec n b))
  have hres0 :=
    higham14_problem14_5_right_inverse_solve_residual_bound
      n fp A X b hn1 hRightRes
  have hres : ∀ k : Fin n,
      |matMulVec n A x_hat k - b k| ≤ gamma fp (n + 1) * E k := by
    intro k
    simpa [x_hat, E] using hres0 k
  have hfwd :=
    higham14_problem14_5_forward_error_of_residual_bound
      n A A_inv x x_hat b (fun k => gamma fp (n + 1) * E k)
      hLeft hsolve hres
  calc
    |x_hat i - x i|
        ≤ matMulVec n (absMatrix n A_inv)
            (fun k => gamma fp (n + 1) * E k) i := hfwd i
    _ = gamma fp (n + 1) * matMulVec n (absMatrix n A_inv) E i := by
        simp only [matMulVec, absMatrix]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, left-approximate-inverse
    forward-error consequence.

If `Y` has a small left inverse residual and `b = A x`, then
`y_hat = fl(Y b)` satisfies the componentwise forward-error envelope
`|y_hat-x| <= gamma_{n+1} |Y||A||x|`. -/
theorem higham14_problem14_5_left_inverse_solve_forward_error_bound
    (n : ℕ) (fp : FPModel)
    (A Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeftRes : ∀ i j : Fin n,
      |inverseLeftResidual n A Y i j| ≤
        fp.u * ∑ k : Fin n, |Y i k| * |A k j|) :
    let b := matMulVec n A x
    let y_hat := fl_matVec fp n n Y b
    ∀ i : Fin n,
      |y_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n Y)
            (matMulVec n (absMatrix n A) (absVec n x)) i := by
  intro b y_hat i
  have hn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  obtain ⟨ΔY, hΔY_bound, hΔY_eq⟩ :=
    matVec_backward_error fp n n Y (matMulVec n A x) hn
  change |fl_matVec fp n n Y (matMulVec n A x) i - x i| ≤ _
  let R := inverseLeftResidual n A Y
  let S : ℝ :=
    matMulVec n (absMatrix n Y)
      (matMulVec n (absMatrix n A) (absVec n x)) i
  have hcoeff : fp.u + gamma fp n ≤ gamma fp (n + 1) :=
    higham14_unit_roundoff_add_gamma_le_gamma_succ fp n hn1
  have hS_nonneg : 0 ≤ S := by
    simp only [S, matMulVec, absMatrix, absVec]
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  have hyhat_vec :
      fl_matVec fp n n Y (matMulVec n A x) =
        matMulVec n (fun i j => Y i j + ΔY i j) (matMulVec n A x) := by
    ext j
    simpa [matMulVec] using hΔY_eq j
  have hYAx_split :
      matMulVec n Y (matMulVec n A x) =
        fun j => matMulVec n R x j + x j := by
    simpa [R] using higham14_inverseLeftResidual_mulVec_add_self n A Y x
  have hmain :
      fl_matVec fp n n Y (matMulVec n A x) i - x i =
        matMulVec n R x i +
          matMulVec n ΔY (matMulVec n A x) i := by
    calc
      fl_matVec fp n n Y (matMulVec n A x) i - x i
          = matMulVec n
              (fun j k => Y j k + ΔY j k) (matMulVec n A x) i - x i := by
                rw [hyhat_vec]
      _ = (matMulVec n Y (matMulVec n A x) i +
              matMulVec n ΔY (matMulVec n A x) i) - x i := by
                rw [matMulVec_add_left]
      _ = ((matMulVec n R x i + x i) +
              matMulVec n ΔY (matMulVec n A x) i) - x i := by
                rw [hYAx_split]
      _ = matMulVec n R x i +
            matMulVec n ΔY (matMulVec n A x) i := by
              ring
  have hres_part :
      |matMulVec n R x i| ≤ fp.u * S := by
    calc
      |matMulVec n R x i|
          ≤ ∑ k : Fin n, |R i k| * |x k| :=
            abs_matMulVec_le n R x i
      _ ≤ ∑ k : Fin n, (fp.u * ∑ l : Fin n, |Y i l| * |A l k|) * |x k| := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_right
              (by simpa [R] using hLeftRes i k) (abs_nonneg _)
      _ = fp.u * S := by
            simp only [S, matMulVec, absMatrix, absVec]
            calc
              ∑ k : Fin n, (fp.u * ∑ l : Fin n, |Y i l| * |A l k|) * |x k|
                  = ∑ k : Fin n, ∑ l : Fin n,
                      fp.u * (|Y i l| * |A l k|) * |x k| := by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [Finset.mul_sum, Finset.sum_mul]
              _ = ∑ l : Fin n, ∑ k : Fin n,
                      fp.u * (|Y i l| * |A l k|) * |x k| := by
                    rw [Finset.sum_comm]
              _ = fp.u * ∑ l : Fin n, |Y i l| *
                      (∑ k : Fin n, |A l k| * |x k|) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro l _
                    calc
                      ∑ k : Fin n, fp.u * (|Y i l| * |A l k|) * |x k|
                          = fp.u *
                              (∑ k : Fin n, |Y i l| * (|A l k| * |x k|)) := by
                            rw [Finset.mul_sum]
                            apply Finset.sum_congr rfl
                            intro k _
                            ring
                      _ = fp.u * (|Y i l| *
                              (∑ k : Fin n, |A l k| * |x k|)) := by
                            congr 1
                            rw [← Finset.mul_sum]
  have hround_part :
      |matMulVec n ΔY (matMulVec n A x) i| ≤ gamma fp n * S := by
    calc
      |matMulVec n ΔY (matMulVec n A x) i|
          ≤ ∑ k : Fin n, |ΔY i k| * |matMulVec n A x k| :=
            abs_matMulVec_le n ΔY (matMulVec n A x) i
      _ ≤ ∑ k : Fin n, (gamma fp n * |Y i k|) *
            (∑ l : Fin n, |A k l| * |x l|) := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul
              (hΔY_bound i k)
              (abs_matMulVec_le n A x k)
              (abs_nonneg _)
              (mul_nonneg (gamma_nonneg fp hn) (abs_nonneg _))
      _ = gamma fp n * S := by
            change
              ∑ k : Fin n, (gamma fp n * |Y i k|) *
                  (∑ l : Fin n, |A k l| * |x l|) =
                gamma fp n * ∑ k : Fin n, |Y i k| *
                  (∑ l : Fin n, |A k l| * |x l|)
            calc
              ∑ k : Fin n, (gamma fp n * |Y i k|) *
                  (∑ l : Fin n, |A k l| * |x l|)
                  = ∑ k : Fin n, gamma fp n *
                      (|Y i k| * (∑ l : Fin n, |A k l| * |x l|)) := by
                    apply Finset.sum_congr rfl
                    intro k _
                    ring
              _ = gamma fp n * ∑ k : Fin n, |Y i k| *
                    (∑ l : Fin n, |A k l| * |x l|) := by
                    rw [Finset.mul_sum]
  have hfinal :
      |fl_matVec fp n n Y (matMulVec n A x) i - x i| ≤
        gamma fp (n + 1) * S := by
    calc
      |fl_matVec fp n n Y (matMulVec n A x) i - x i|
          = |matMulVec n R x i +
              matMulVec n ΔY (matMulVec n A x) i| := by
            rw [hmain]
      _ ≤ |matMulVec n R x i| +
            |matMulVec n ΔY (matMulVec n A x) i| :=
            abs_add_le _ _
      _ ≤ fp.u * S + gamma fp n * S :=
            add_le_add hres_part hround_part
      _ = (fp.u + gamma fp n) * S := by ring
      _ ≤ gamma fp (n + 1) * S :=
            mul_le_mul_of_nonneg_right hcoeff hS_nonneg
  change |fl_matVec fp n n Y (matMulVec n A x) i - x i| ≤
    gamma fp (n + 1) * S
  exact hfinal

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, right-approximate-inverse
    forward-error bound with an externally supplied first-order replacement
    envelope for `|X|`. -/
theorem higham14_problem14_5_right_inverse_solve_forward_error_bound_of_abs_X_le
    (n : ℕ) (fp : FPModel)
    (A A_inv X : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeft : IsLeftInverse n A A_inv)
    (hsolve : matMulVec n A x = b)
    (hRightRes : ∀ i j : Fin n,
      |inverseRightResidual n A X i j| ≤
        fp.u * ∑ k : Fin n, |A i k| * |X k j|)
    (X_bound : Fin n → Fin n → ℝ)
    (hX_bound : ∀ i j : Fin n, |X i j| ≤ X_bound i j) :
    let x_hat := fl_matVec fp n n X b
    ∀ i : Fin n,
      |x_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n X_bound (absVec n b))) i := by
  intro x_hat i
  have hbase :=
    higham14_problem14_5_right_inverse_solve_forward_error_bound
      n fp A A_inv X x b hn1 hLeft hsolve hRightRes
  have hX_mono : ∀ j : Fin n,
      matMulVec n (absMatrix n X) (absVec n b) j ≤
        matMulVec n X_bound (absVec n b) j := by
    intro j
    simp only [matMulVec, absMatrix, absVec]
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hX_bound j k) (abs_nonneg _)
  have hA_mono :=
    higham14_absMatrix_matMulVec_mono n A hX_mono
  have hAinv_mono :=
    higham14_absMatrix_matMulVec_mono n A_inv hA_mono
  calc
    |x_hat i - x i|
        ≤ gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n (absMatrix n X) (absVec n b))) i := hbase i
    _ ≤ gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n X_bound (absVec n b))) i :=
        mul_le_mul_of_nonneg_left (hAinv_mono i) (gamma_nonneg fp hn1)

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, right-approximate-inverse
    first-order replacement form: if `|X|` is bounded by `|A⁻¹|`, the forward
    envelope uses `|A⁻¹||A||A⁻¹||b|`. -/
theorem higham14_problem14_5_right_inverse_solve_forward_error_firstorder_replacement
    (n : ℕ) (fp : FPModel)
    (A A_inv X : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeft : IsLeftInverse n A A_inv)
    (hsolve : matMulVec n A x = b)
    (hRightRes : ∀ i j : Fin n,
      |inverseRightResidual n A X i j| ≤
        fp.u * ∑ k : Fin n, |A i k| * |X k j|)
    (hX_first : ∀ i j : Fin n, |X i j| ≤ |A_inv i j|) :
    let x_hat := fl_matVec fp n n X b
    ∀ i : Fin n,
      |x_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n (absMatrix n A_inv) (absVec n b))) i := by
  exact
    higham14_problem14_5_right_inverse_solve_forward_error_bound_of_abs_X_le
      n fp A A_inv X x b hn1 hLeft hsolve hRightRes
      (absMatrix n A_inv) (by
        intro i j
        simpa [absMatrix] using hX_first i j)

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, left-approximate-inverse
    forward-error bound with an externally supplied first-order replacement
    envelope for `|Y|`. -/
theorem higham14_problem14_5_left_inverse_solve_forward_error_bound_of_abs_Y_le
    (n : ℕ) (fp : FPModel)
    (A Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeftRes : ∀ i j : Fin n,
      |inverseLeftResidual n A Y i j| ≤
        fp.u * ∑ k : Fin n, |Y i k| * |A k j|)
    (Y_bound : Fin n → Fin n → ℝ)
    (hY_bound : ∀ i j : Fin n, |Y i j| ≤ Y_bound i j) :
    let b := matMulVec n A x
    let y_hat := fl_matVec fp n n Y b
    ∀ i : Fin n,
      |y_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n Y_bound
            (matMulVec n (absMatrix n A) (absVec n x)) i := by
  intro b y_hat i
  have hbase :=
    higham14_problem14_5_left_inverse_solve_forward_error_bound
      n fp A Y x hn1 hLeftRes
  have hAx_nonneg : ∀ k : Fin n,
      0 ≤ matMulVec n (absMatrix n A) (absVec n x) k :=
    higham14_absMatrix_matMulVec_nonneg n A (absVec n x)
      (fun k => abs_nonneg (x k))
  have hY_mono : ∀ j : Fin n,
      matMulVec n (absMatrix n Y)
          (matMulVec n (absMatrix n A) (absVec n x)) j ≤
        matMulVec n Y_bound
          (matMulVec n (absMatrix n A) (absVec n x)) j := by
    intro j
    simp only [matMulVec, absMatrix]
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hY_bound j k) (hAx_nonneg k)
  calc
    |y_hat i - x i|
        ≤ gamma fp (n + 1) *
          matMulVec n (absMatrix n Y)
            (matMulVec n (absMatrix n A) (absVec n x)) i := hbase i
    _ ≤ gamma fp (n + 1) *
          matMulVec n Y_bound
            (matMulVec n (absMatrix n A) (absVec n x)) i :=
        mul_le_mul_of_nonneg_left (hY_mono i) (gamma_nonneg fp hn1)

/-- Higham, 2nd ed., Chapter 14, Problem 14.5, left-approximate-inverse
    first-order replacement form: if `|Y|` is bounded by `|A⁻¹|`, the forward
    envelope uses `|A⁻¹||A||x|`. -/
theorem higham14_problem14_5_left_inverse_solve_forward_error_firstorder_replacement
    (n : ℕ) (fp : FPModel)
    (A A_inv Y : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLeftRes : ∀ i j : Fin n,
      |inverseLeftResidual n A Y i j| ≤
        fp.u * ∑ k : Fin n, |Y i k| * |A k j|)
    (hY_first : ∀ i j : Fin n, |Y i j| ≤ |A_inv i j|) :
    let b := matMulVec n A x
    let y_hat := fl_matVec fp n n Y b
    ∀ i : Fin n,
      |y_hat i - x i| ≤
        gamma fp (n + 1) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A) (absVec n x)) i := by
  exact
    higham14_problem14_5_left_inverse_solve_forward_error_bound_of_abs_Y_le
      n fp A Y x hn1 hLeftRes (absMatrix n A_inv) (by
        intro i j
        simpa [absMatrix] using hY_first i j)

/-- Higham, 2nd ed., Chapter 14, Problem 14.5 interpretation:
    with an exact right-hand side `b = A x`, the right first-order envelope
    applies one extra nonnegative `|A⁻¹||A|` amplification to the left
    first-order envelope.  Since `A⁻¹A = I`, the left envelope is
    componentwise bounded by that amplified envelope. -/
theorem higham14_problem14_5_left_firstorder_envelope_le_right_exact_rhs_envelope
    (n : ℕ) (A A_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv) :
    ∀ i : Fin n,
      matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A) (absVec n x)) i ≤
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A)
            (matMulVec n (absMatrix n A_inv)
              (matMulVec n (absMatrix n A) (absVec n x)))) i := by
  intro i
  let z : Fin n → ℝ :=
    matMulVec n (absMatrix n A_inv)
      (matMulVec n (absMatrix n A) (absVec n x))
  have hAx_nonneg : ∀ k : Fin n,
      0 ≤ matMulVec n (absMatrix n A) (absVec n x) k :=
    higham14_absMatrix_matMulVec_nonneg n A (absVec n x)
      (fun k => abs_nonneg (x k))
  have hz_nonneg : ∀ k : Fin n, 0 ≤ z k :=
    higham14_absMatrix_matMulVec_nonneg n A_inv
      (matMulVec n (absMatrix n A) (absVec n x)) hAx_nonneg
  have hdiag : 1 ≤ ∑ j : Fin n, |A_inv i j| * |A j i| := by
    have hsum_eq : (∑ j : Fin n, A_inv i j * A j i) = 1 := by
      simpa using hLeft i i
    calc
      1 = |∑ j : Fin n, A_inv i j * A j i| := by
            rw [hsum_eq, abs_one]
      _ ≤ ∑ j : Fin n, |A_inv i j * A j i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |A_inv i j| * |A j i| := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul _ _
  change z i ≤
    matMulVec n (absMatrix n A_inv) (matMulVec n (absMatrix n A) z) i
  calc
    z i = 1 * z i := by ring
    _ ≤ (∑ j : Fin n, |A_inv i j| * |A j i|) * z i :=
        mul_le_mul_of_nonneg_right hdiag (hz_nonneg i)
    _ = ∑ j : Fin n, (|A_inv i j| * |A j i|) * z i := by
        rw [Finset.sum_mul]
    _ ≤ ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k| * z k) := by
        apply Finset.sum_le_sum
        intro j _
        calc
          (|A_inv i j| * |A j i|) * z i
              = |A_inv i j| * (|A j i| * z i) := by ring
          _ ≤ |A_inv i j| * (∑ k : Fin n, |A j k| * z k) := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              exact Finset.single_le_sum
                (fun k _ => mul_nonneg (abs_nonneg _) (hz_nonneg k))
                (Finset.mem_univ i)
    _ = matMulVec n (absMatrix n A_inv) (matMulVec n (absMatrix n A) z) i := by
        simp [matMulVec, absMatrix]

end NumStability
