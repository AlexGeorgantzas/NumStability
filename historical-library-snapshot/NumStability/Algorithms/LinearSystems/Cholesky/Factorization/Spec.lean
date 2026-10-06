import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms LinearSystems Cholesky Factorization Spec

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskySpec` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Cholesky factorization specification** (Higham §10.1, Theorem 10.1).

    A = R^T R where R is upper triangular with positive diagonal.
    Convention: (R^T R)_{ij} = ∑_k R_{ki} R_{kj} since (R^T)_{ik} = R_{ki}. -/
structure CholeskyFactSpec (n : ℕ) (A R : Fin n → Fin n → ℝ) : Prop where
  /-- R is upper triangular: entries below diagonal are 0. -/
  R_upper : ∀ i j : Fin n, j.val < i.val → R i j = 0
  /-- R has positive diagonal. -/
  R_diag_pos : ∀ i : Fin n, 0 < R i i
  /-- A = R^T R: the product recovers A exactly. -/
  product_eq : ∀ i j : Fin n, ∑ k : Fin n, R k i * R k j = A i j

/-- **Computed Cholesky factorization with backward error** (Higham §10.1, Theorem 10.3).

    Algorithm 10.2 (jik Cholesky) computes R̂ such that
    |R̂^T R̂ − A| ≤ ε · |R̂^T| · |R̂| componentwise,
    where ε = γ_{n+1} accounts for at most n+1 floating-point operations
    per entry (inner product of up to n terms + subtraction + sqrt/division). -/
structure CholeskyBackwardError (n : ℕ) (A R_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) : Prop where
  /-- R̂ is upper triangular. -/
  R_upper : ∀ i j : Fin n, j.val < i.val → R_hat i j = 0
  /-- Componentwise backward error: |R̂^T R̂ − A| ≤ ε|R̂^T||R̂|. -/
  backward_bound : ∀ i j : Fin n,
    |∑ k : Fin n, R_hat k i * R_hat k j - A i j| ≤
      ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j|

/-- **Nonnegativity of |R̂^T||R̂| product**.

    The componentwise product (|R̂^T||R̂|)_{ij} = ∑_k |R̂_{ki}||R̂_{kj}| is nonneg. -/
lemma absRT_R_product_nonneg (n : ℕ) (R_hat : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, 0 ≤ ∑ k : Fin n, |R_hat k i| * |R_hat k j| := by
  intro i j
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- **Cholesky backward error perturbation** (Higham §10.1, Theorem 10.3).

    The computed Cholesky factor R̂ satisfies R̂^T R̂ = A + ΔA where
    |ΔA_{ij}| ≤ ε · (|R̂^T||R̂|)_{ij} componentwise.

    This is equation (10.5) in Higham. -/
theorem cholesky_backward_error_perturbation (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ) (ε : ℝ) (_hε : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  refine ⟨fun i j => ∑ k : Fin n, R_hat k i * R_hat k j - A i j,
          fun i j => hChol.backward_bound i j, fun i j => ?_⟩
  ring

/-- **Cholesky backward error relative to |A|** (Higham §10.1).

    If (|R̂^T||R̂|)_{ij} ≤ c · |A_{ij}| componentwise (growth bounded by c),
    then |ΔA_{ij}| ≤ ε · c · |A_{ij}|. -/
theorem cholesky_backward_error_relative (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ) (ε c : ℝ) (hε : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |R_hat k i| * |R_hat k j| ≤ c * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * c * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_backward_error_perturbation n A R_hat ε hε hChol
  exact ⟨ΔA, fun i j => by
    have h1 := hΔA_bound i j
    have h2 := hGrowth i j
    calc |ΔA i j| ≤ ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j| := h1
      _ ≤ ε * (c * |A i j|) := by
          apply mul_le_mul_of_nonneg_left h2 hε
      _ = ε * c * |A i j| := by ring,
    hΔA_eq⟩

/-- **Nonneg Cholesky factors: |R̂^T||R̂| = R̂^T R̂**.

    When R̂ has nonneg entries, |R̂_{ki}| = R̂_{ki}, so the absolute
    factor product equals the actual product. -/
lemma nonneg_cholesky_absRTR_eq (n : ℕ) (R_hat : Fin n → Fin n → ℝ)
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    ∀ i j : Fin n, ∑ k : Fin n, |R_hat k i| * |R_hat k j| =
      ∑ k : Fin n, R_hat k i * R_hat k j := by
  intro i j
  apply Finset.sum_congr rfl; intro k _
  rw [abs_of_nonneg (hR_nn k i), abs_of_nonneg (hR_nn k j)]

/-- **Nonneg Cholesky factors: |R̂^T||R̂| = |R̂^T R̂|**.

    When R̂ ≥ 0, each product R̂_{ki} R̂_{kj} ≥ 0, so the sum is nonneg
    and (|R̂^T||R̂|)_{ij} = (R̂^T R̂)_{ij} = |(R̂^T R̂)_{ij}|. -/
lemma nonneg_cholesky_absRTR_eq_absProduct (n : ℕ) (R_hat : Fin n → Fin n → ℝ)
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    ∀ i j : Fin n, ∑ k : Fin n, |R_hat k i| * |R_hat k j| =
      |∑ k : Fin n, R_hat k i * R_hat k j| := by
  intro i j
  have h1 := nonneg_cholesky_absRTR_eq n R_hat hR_nn i j
  have h2 : 0 ≤ ∑ k : Fin n, R_hat k i * R_hat k j :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hR_nn k i) (hR_nn k j))
  rw [h1, abs_of_nonneg h2]

/-- **SPD optimal growth** (Higham §10.1, Problem 10.4).

    For SPD matrices, the growth factor for Cholesky is exactly 1.
    When R̂ ≥ 0 and ε < 1:
      (|R̂^T||R̂|)_{ij} ≤ |A_{ij}| / (1 − ε)

    This follows from: |R̂^T||R̂| = R̂^T R̂, and
    |R̂^T R̂ − A| ≤ ε · R̂^T R̂ rearranges to R̂^T R̂ · (1 − ε) ≤ A. -/
theorem cholesky_spd_optimal_growth (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ) (ε : ℝ) (hε_lt : ε < 1) (_hε_nn : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε)
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |R_hat k i| * |R_hat k j| ≤ |A i j| / (1 - ε) := by
  intro i j
  have habs_eq := nonneg_cholesky_absRTR_eq n R_hat hR_nn i j
  have hS_nn : 0 ≤ ∑ k : Fin n, R_hat k i * R_hat k j :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hR_nn k i) (hR_nn k j))
  have hbe := hChol.backward_bound i j
  rw [habs_eq] at hbe
  have h_upper := (abs_le.mp hbe).2
  have h1_ε_pos : (0 : ℝ) < 1 - ε := by linarith
  have hA_nn : 0 ≤ A i j := by nlinarith
  rw [habs_eq, abs_of_nonneg hA_nn]
  have hne : (1 : ℝ) - ε ≠ 0 := ne_of_gt h1_ε_pos
  rw [le_div_iff₀ h1_ε_pos]
  nlinarith

/-- **SPD backward stability** (Higham §10.1, equation 10.7, simplified).

    For SPD matrices with nonneg Cholesky factors and ε < 1:
      |ΔA_{ij}| ≤ ε/(1−ε) · |A_{ij}|

    This is the componentwise version of the perfect stability result. -/
theorem cholesky_spd_backward_stable (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ) (ε : ℝ) (hε_lt : ε < 1) (hε_nn : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε)
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε / (1 - ε) * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_backward_error_perturbation n A R_hat ε hε_nn hChol
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hgrowth := cholesky_spd_optimal_growth n A R_hat ε hε_lt hε_nn hChol hR_nn i j
  have h1 := hΔA_bound i j
  calc |ΔA i j| ≤ ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j| := h1
    _ ≤ ε * (|A i j| / (1 - ε)) := by
        apply mul_le_mul_of_nonneg_left hgrowth hε_nn
    _ = ε / (1 - ε) * |A i j| := by ring

/-- **SPD normwise backward stability** (Higham §10.1, equation 10.7).

    For SPD matrices with nonneg Cholesky factors and ε < 1:
      ‖ΔA‖∞ ≤ ε/(1−ε) · ‖A‖∞

    This follows from the componentwise bound |ΔA_{ij}| ≤ ε/(1−ε)|A_{ij}|
    by summing over rows and taking the maximum. -/
theorem cholesky_spd_backward_stable_normwise (n : ℕ) (_hn : 0 < n)
    (A R_hat : Fin n → Fin n → ℝ) (ε : ℝ) (hε_lt : ε < 1) (hε_nn : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε)
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      infNorm ΔA ≤ ε / (1 - ε) * infNorm A ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_spd_backward_stable n A R_hat ε hε_lt hε_nn hChol hR_nn
  refine ⟨ΔA, ?_, hΔA_eq⟩
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  have hc_nn : 0 ≤ ε / (1 - ε) := div_nonneg hε_nn (le_of_lt h1ε)
  -- infNorm(ΔA) = max_i ∑_j |ΔA_ij| ≤ ε/(1-ε) · max_i ∑_j |A_ij| = ε/(1-ε) · infNorm(A)
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |ΔA i j|
        ≤ ∑ j : Fin n, ε / (1 - ε) * |A i j| :=
          Finset.sum_le_sum (fun j _ => hΔA_bound i j)
      _ = ε / (1 - ε) * ∑ j : Fin n, |A i j| := (Finset.mul_sum _ _ _).symm
      _ ≤ ε / (1 - ε) * infNorm A := by
          apply mul_le_mul_of_nonneg_left _ hc_nn
          exact row_sum_le_infNorm A i
  · exact mul_nonneg hc_nn (infNorm_nonneg A)

end NumStability
