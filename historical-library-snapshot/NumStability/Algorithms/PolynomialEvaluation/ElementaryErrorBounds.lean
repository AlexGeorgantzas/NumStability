import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms PolynomialEvaluation ElementaryErrorBounds

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

lemma fl_mul_abs_error_bound (fp : FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  have hdiff : fp.fl_mul x y - x * y = (x * y) * δ := by
    rw [hfl]
    ring
  calc
    |fp.fl_mul x y - x * y| = |x * y| * |δ| := by
      rw [hdiff, abs_mul]
    _ ≤ |x * y| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = fp.u * |x * y| := by ring

lemma fl_add_abs_error_bound (fp : FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  have hdiff : fp.fl_add x y - (x + y) = (x + y) * δ := by
    rw [hfl]
    ring
  calc
    |fp.fl_add x y - (x + y)| = |x + y| * |δ| := by
      rw [hdiff, abs_mul]
    _ ≤ |x + y| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = fp.u * |x + y| := by ring

lemma fl_mul_error_of_operand_error
    (fp : FPModel) (a yhat y eps : ℝ)
    (hy : |yhat - y| ≤ eps) :
    |fp.fl_mul a yhat - a * y| ≤
      fp.u * |a * yhat| + |a| * eps := by
  have hlocal := fl_mul_abs_error_bound fp a yhat
  have hdecomp :
      fp.fl_mul a yhat - a * y =
        (fp.fl_mul a yhat - a * yhat) + a * (yhat - y) := by
    ring
  have hprop : |a * (yhat - y)| ≤ |a| * eps := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg a)
  calc
    |fp.fl_mul a yhat - a * y|
        = |(fp.fl_mul a yhat - a * yhat) + a * (yhat - y)| := by
          rw [hdecomp]
    _ ≤ |fp.fl_mul a yhat - a * yhat| + |a * (yhat - y)| :=
          abs_add_le _ _
    _ ≤ fp.u * |a * yhat| + |a| * eps :=
          add_le_add hlocal hprop

lemma fl_add_error_of_operand_errors
    (fp : FPModel) (qhat q that t epsQ epsT : ℝ)
    (hq : |qhat - q| ≤ epsQ) (ht : |that - t| ≤ epsT) :
    |fp.fl_add qhat that - (q + t)| ≤
      fp.u * |qhat + that| + epsQ + epsT := by
  have hlocal := fl_add_abs_error_bound fp qhat that
  have hdecomp :
      fp.fl_add qhat that - (q + t) =
        (fp.fl_add qhat that - (qhat + that)) +
          (qhat - q) + (that - t) := by
    ring
  have htri :
      |(fp.fl_add qhat that - (qhat + that)) +
          (qhat - q) + (that - t)| ≤
        |fp.fl_add qhat that - (qhat + that)| +
          |qhat - q| + |that - t| := by
    have h1 :
        |(fp.fl_add qhat that - (qhat + that)) +
            (qhat - q) + (that - t)| ≤
          |(fp.fl_add qhat that - (qhat + that)) +
            (qhat - q)| + |that - t| :=
      abs_add_le _ _
    have h2 :
        |(fp.fl_add qhat that - (qhat + that)) +
            (qhat - q)| ≤
          |fp.fl_add qhat that - (qhat + that)| + |qhat - q| :=
      abs_add_le _ _
    linarith
  calc
    |fp.fl_add qhat that - (q + t)|
        = |(fp.fl_add qhat that - (qhat + that)) +
            (qhat - q) + (that - t)| := by
          rw [hdecomp]
    _ ≤ |fp.fl_add qhat that - (qhat + that)| +
          |qhat - q| + |that - t| := htri
    _ ≤ fp.u * |qhat + that| + epsQ + epsT := by
          linarith

end NumStability
