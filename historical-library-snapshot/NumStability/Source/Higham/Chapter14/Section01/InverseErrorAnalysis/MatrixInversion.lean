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
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter14 Section01 InverseErrorAnalysis MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 14, Section 14.1, equation (14.3):
    bounded-replacement form of the perturbed-inverse forward-error estimate.

    The exact theorem `ideal_forward_error` gives the pre-asymptotic envelope
    with `|Y|`.  This wrapper replaces `|Y|` by any componentwise upper envelope
    supplied by the caller, exposing the first-order substitution step without
    hiding it in an informal `O(ε^2)` term. -/
theorem higham14_eq14_3_forward_error_bound_of_abs_Y_le (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ)
    (ΔA Y_bound : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (hRInv : IsRightInverse n A A_inv)
    (hY : ∀ i j, ∑ k : Fin n, (A i k + ΔA i k) * Y k j =
      if i = j then 1 else 0)
    (hY_bound : ∀ i j : Fin n, |Y i j| ≤ Y_bound i j) :
    ∀ i j, |A_inv i j - Y i j| ≤
      ε * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * Y_bound k₂ j) := by
  intro i j
  have hbase :=
    ideal_forward_error n A A_inv Y ΔA ε hε hΔA hInv hRInv hY
  calc
    |A_inv i j - Y i j|
        ≤ ε * ∑ k₁ : Fin n, |A_inv i k₁| *
            (∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ j|) := hbase i j
    _ ≤ ε * ∑ k₁ : Fin n, |A_inv i k₁| *
            (∑ k₂ : Fin n, |A k₁ k₂| * Y_bound k₂ j) := by
        apply mul_le_mul_of_nonneg_left _ hε
        apply Finset.sum_le_sum
        intro k₁ _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        intro k₂ _
        exact mul_le_mul_of_nonneg_left (hY_bound k₂ j) (abs_nonneg _)

/-- Higham, 2nd ed., Chapter 14, Section 14.1, equation (14.3):
    first-order replacement form under an explicit componentwise hypothesis
    `|Y| ≤ |A⁻¹|`.

    This is the source-facing `|A⁻¹||A||A⁻¹|` envelope as a proved bounded
    replacement.  It does not claim to formalize the remaining asymptotic
    `O(ε^2)` calculus. -/
theorem higham14_eq14_3_forward_error_firstorder_replacement (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (hRInv : IsRightInverse n A A_inv)
    (hY : ∀ i j, ∑ k : Fin n, (A i k + ΔA i k) * Y k j =
      if i = j then 1 else 0)
    (hY_first : ∀ i j : Fin n, |Y i j| ≤ |A_inv i j|) :
    ∀ i j, |A_inv i j - Y i j| ≤
      ε * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * |A_inv k₂ j|) := by
  simpa [absMatrix] using
    (higham14_eq14_3_forward_error_bound_of_abs_Y_le
      n A A_inv Y ΔA (absMatrix n A_inv) ε hε hΔA hInv hRInv hY
      (by
        intro i j
        simpa [absMatrix] using hY_first i j))

/-- Higham, 2nd ed., Chapter 14, Section 14.1, equation (14.3):
    explicit first-order plus replacement-remainder form.

If a caller supplies `|Y| <= |A⁻¹| + R`, the exact perturbed-inverse
forward-error bound separates into the displayed first-order term and an
explicit `R` remainder term.  Taking `R = O(ε)` is the remaining asymptotic
step behind the book's informal `O(ε^2)` notation. -/
theorem higham14_eq14_3_forward_error_firstorder_plus_remainder (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ)
    (ΔA R : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (hRInv : IsRightInverse n A A_inv)
    (hY : ∀ i j, ∑ k : Fin n, (A i k + ΔA i k) * Y k j =
      if i = j then 1 else 0)
    (hY_bound : ∀ i j : Fin n, |Y i j| ≤ |A_inv i j| + R i j) :
    ∀ i j, |A_inv i j - Y i j| ≤
      ε * (∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * |A_inv k₂ j|)) +
      ε * (∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * R k₂ j)) := by
  intro i j
  have hbase :=
    higham14_eq14_3_forward_error_bound_of_abs_Y_le
      n A A_inv Y ΔA (fun i j => |A_inv i j| + R i j)
      ε hε hΔA hInv hRInv hY hY_bound i j
  calc
    |A_inv i j - Y i j|
        ≤ ε * ∑ k₁ : Fin n, |A_inv i k₁| *
            (∑ k₂ : Fin n, |A k₁ k₂| * (|A_inv k₂ j| + R k₂ j)) := hbase
    _ = ε * (∑ k₁ : Fin n, |A_inv i k₁| *
            (∑ k₂ : Fin n, |A k₁ k₂| * |A_inv k₂ j|)) +
        ε * (∑ k₁ : Fin n, |A_inv i k₁| *
            (∑ k₂ : Fin n, |A k₁ k₂| * R k₂ j)) := by
        rw [← mul_add]
        congr 1
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k₁ _
        rw [← mul_add]
        congr 1
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k₂ _
        ring

/-- Exact off-diagonal block used in Higham equation (14.14), Method 2B:
    `-X22 * L21 * X11`.  Here `L21` is the lower-left rectangular block, and
    `X11`, `X22` are diagonal-block inverse approximations/exact blocks. -/
noncomputable def higham14_method2BBlockUpdateExact {m r : ℕ}
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) : Fin r → Fin m → ℝ :=
  fun i j => -rectMatMul (rectMatMul X22 L21) X11 i j

/-- Method 2B off-diagonal block perturbation for equation (14.14):
    `X21_hat = -X22 * L21 * X11 + Delta21`. -/
noncomputable def higham14_method2BBlockUpdateDelta {m r : ℕ}
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) : Fin r → Fin m → ℝ :=
  fun i j => X21_hat i j -
    higham14_method2BBlockUpdateExact X22 L21 X11 i j

/-- Monotonicity of multiplication by an absolute-value matrix. -/
lemma higham14_absMatrix_matMulVec_mono (n : ℕ)
    (A : Fin n → Fin n → ℝ) {x y : Fin n → ℝ}
    (hxy : ∀ i : Fin n, x i ≤ y i) :
    ∀ i : Fin n,
      matMulVec n (absMatrix n A) x i ≤
        matMulVec n (absMatrix n A) y i := by
  intro i
  simp only [matMulVec, absMatrix]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hxy j) (abs_nonneg _)

/-- Nonnegativity of multiplication by an absolute-value matrix against a
    nonnegative vector. -/
lemma higham14_absMatrix_matMulVec_nonneg (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : ∀ i : Fin n, 0 ≤ x i) :
    ∀ i : Fin n, 0 ≤ matMulVec n (absMatrix n A) x i := by
  intro i
  simp only [matMulVec, absMatrix]
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg (abs_nonneg _) (hx j))

end NumStability
