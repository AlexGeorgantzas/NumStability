-- Algorithms/Quadrature.lean
--
-- Higham Chapter 3, Problem 3.12.

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct

namespace NumStability

open scoped BigOperators

/-!
# Quadrature Error Bound

Higham Chapter 3, Problem 3.12 asks for a bound on a quadrature rule whose
function values are evaluated with relative error and whose weighted sum is
then accumulated in left-to-right order.  The local theorem separates the
analytic quadrature error `|I - J|`, the function-evaluation error `eta`, and
the floating-point dot-product error `gamma_n`.
-/

/-- Exact finite quadrature sum `J(f) = sum_i w_i f_i`. -/
noncomputable def quadratureRule (n : ℕ) (w f : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, w i * f i

/-- Computed quadrature sum using the repository's left-to-right dot product. -/
noncomputable def fl_quadrature (fp : FPModel) (n : ℕ)
    (w fhat : Fin n → ℝ) : ℝ :=
  fl_dotProduct fp n w fhat

/-- **Higham Problem 3.12.**

Assume the quadrature weights and nodes are represented as floating-point
inputs, the function values satisfy

`fhat_i = fl(f(x_i))` with `|fhat_i - f_i| <= eta |f_i|`,

and the weighted sum is evaluated left-to-right.  Then the computed quadrature
value is bounded by the analytic quadrature error plus a finite-sum arithmetic
budget:

`|I - Jhat| <= |I - J| + (eta + gamma_n * (1 + eta)) sum_i |w_i||f_i|`.

The first term is the mathematical quadrature error; the `eta` term is the
function-evaluation error; the `gamma_n` term is the floating-point summation
of the perturbed weighted values. -/
theorem fl_quadrature_error_bound_of_function_value_rel_error
    (fp : FPModel) (n : ℕ) (w f fhat : Fin n → ℝ) (I : ℝ)
    (hn : gammaValid fp n) {eta : ℝ} (_heta_nonneg : 0 ≤ eta)
    (hf : ∀ i : Fin n, |fhat i - f i| ≤ eta * |f i|) :
    |I - fl_quadrature fp n w fhat| ≤
      |I - quadratureRule n w f| +
        (eta + gamma fp n * (1 + eta)) *
          ∑ i : Fin n, |w i| * |f i| := by
  let J : ℝ := quadratureRule n w f
  let F : ℝ := ∑ i : Fin n, w i * fhat i
  let S : ℝ := ∑ i : Fin n, |w i| * |f i|
  have hgamma_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hf_abs : ∀ i : Fin n, |f i - fhat i| ≤ eta * |f i| := by
    intro i
    simpa [abs_sub_comm] using hf i
  have hfhat_abs : ∀ i : Fin n, |fhat i| ≤ (1 + eta) * |f i| := by
    intro i
    calc
      |fhat i| = |f i + (fhat i - f i)| := by ring_nf
      _ ≤ |f i| + |fhat i - f i| := abs_add_le _ _
      _ ≤ |f i| + eta * |f i| := by
          linarith [hf i]
      _ = (1 + eta) * |f i| := by ring
  have hJ_F :
      |J - F| ≤ eta * S := by
    calc
      |J - F|
          = |∑ i : Fin n, w i * (f i - fhat i)| := by
              simp [J, F, quadratureRule]
              rw [← Finset.sum_sub_distrib]
              apply congrArg abs
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ ≤ ∑ i : Fin n, |w i * (f i - fhat i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |w i| * |f i - fhat i| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul]
      _ ≤ ∑ i : Fin n, |w i| * (eta * |f i|) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hf_abs i) (abs_nonneg _)
      _ = eta * S := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
  have hFhat_sum :
      ∑ i : Fin n, |w i| * |fhat i| ≤ (1 + eta) * S := by
    calc
      ∑ i : Fin n, |w i| * |fhat i|
          ≤ ∑ i : Fin n, |w i| * ((1 + eta) * |f i|) := by
              apply Finset.sum_le_sum
              intro i _
              exact mul_le_mul_of_nonneg_left (hfhat_abs i) (abs_nonneg _)
      _ = (1 + eta) * S := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
  have hround :
      |F - fl_quadrature fp n w fhat| ≤ gamma fp n * ((1 + eta) * S) := by
    calc
      |F - fl_quadrature fp n w fhat|
          = |fl_quadrature fp n w fhat - F| := by rw [abs_sub_comm]
      _ ≤ gamma fp n * ∑ i : Fin n, |w i| * |fhat i| := by
          simpa [fl_quadrature, F] using dotProduct_error_bound fp n w fhat hn
      _ ≤ gamma fp n * ((1 + eta) * S) :=
          mul_le_mul_of_nonneg_left hFhat_sum hgamma_nonneg
  calc
    |I - fl_quadrature fp n w fhat|
        = |(I - J) + (J - F) + (F - fl_quadrature fp n w fhat)| := by ring_nf
    _ ≤ |I - J| + |J - F| + |F - fl_quadrature fp n w fhat| := by
        calc
          |(I - J) + (J - F) + (F - fl_quadrature fp n w fhat)|
              ≤ |(I - J) + (J - F)| + |F - fl_quadrature fp n w fhat| :=
                  abs_add_le _ _
          _ ≤ |I - J| + |J - F| + |F - fl_quadrature fp n w fhat| := by
              linarith [abs_add_le (I - J) (J - F)]
    _ ≤ |I - J| + eta * S + gamma fp n * ((1 + eta) * S) := by
        linarith [hJ_F, hround]
    _ = |I - quadratureRule n w f| +
        (eta + gamma fp n * (1 + eta)) * S := by
        simp [J]
        ring
    _ = |I - quadratureRule n w f| +
        (eta + gamma fp n * (1 + eta)) *
          ∑ i : Fin n, |w i| * |f i| := rfl

end NumStability
