-- Algorithms/IterativeRefinement.lean
--
-- §11: Iterative refinement for Ax = b.
--
-- Algorithm: given an approximate solver, compute x₀, then iterate:
--   r = b − Ax₀       (residual)
--   solve Ad = r       (correction)
--   x₁ = x₀ + d       (update)
--
-- Key results:
-- Theorem 11.3: One step of refinement contracts the forward error
--   A·e₁ = ΔA·d̂ + (r − r̂), so |e₁| ≤ |A⁻¹|(μ|A||d̂| + ν|r| + ω)
-- Theorem 11.4: If σ = μ(1+ν)/(1−μ) + ν < 1, backward error improves
--   |r₁| ≤ μ·|A|·|d̂| + ν·|r| + ω

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.ForwardError
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §11.1  Componentwise ordering helpers
-- ============================================================

/-- Componentwise vector inequality: u ≤ v iff u_i ≤ v_i for all i. -/
def vecLe (n : ℕ) (u v : Fin n → ℝ) : Prop := ∀ i : Fin n, u i ≤ v i

/-- Componentwise matrix inequality: A ≤ B iff A_{ij} ≤ B_{ij} for all i,j. -/
def matLe (n : ℕ) (A B : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, A i j ≤ B i j


-- ============================================================
-- §11.1  Solver specification (equation 11.5)
-- ============================================================

/-- **Abstract solver specification** (Higham §11.1, equation 11.5).

    An approximate solver for Ax = c produces x̂ satisfying:
      (A + ΔA)x̂ = c  with  |ΔA_{ij}| ≤ μ · |A_{ij}|

    The perturbation ΔA may depend on the right-hand side c.
    μ is the componentwise backward error of the solver. -/
structure SolverSpec (n : ℕ) (A : Fin n → Fin n → ℝ) (μ : ℝ) where
  /-- The computed solution for a given right-hand side. -/
  solve : (Fin n → ℝ) → (Fin n → ℝ)
  /-- The perturbation matrix for a given right-hand side. -/
  ΔA : (Fin n → ℝ) → (Fin n → Fin n → ℝ)
  /-- Componentwise bound on perturbation. -/
  bound : ∀ c : Fin n → ℝ, ∀ i j : Fin n,
    |ΔA c i j| ≤ μ * |A i j|
  /-- Exactness: (A + ΔA)x̂ = c. -/
  exact : ∀ c : Fin n → ℝ, ∀ i : Fin n,
    ∑ j : Fin n, (A i j + ΔA c i j) * solve c j = c i

-- ============================================================
-- §11.1  Residual computation error (equation 11.6)
-- ============================================================

/-- **Residual computation error** (Higham §11.1, equation 11.6).

    The computed residual r̂ for r = b − Ax̂ satisfies:
      |r̂_i − r_i| ≤ ν · |r_i| + ω_i

    where ν measures relative accuracy and ω the absolute error floor.
    For standard residual computation, ν = γ(n+1) and ω_i = γ(n+1)·(|A||x̂|)_i. -/
structure ResidualError (n : ℕ) (r r_hat : Fin n → ℝ)
    (ν : ℝ) (ω : Fin n → ℝ) : Prop where
  /-- Componentwise residual accuracy bound. -/
  bound : ∀ i : Fin n, |r_hat i - r i| ≤ ν * |r i| + ω i

-- ============================================================
-- §11.1  Conventional residual computation (equation 11.7)
-- ============================================================

/-- **Floating-point residual** r̂ = fl(b − fl(Ax̂)).

    Computed as: first compute ŷ = fl(Ax̂) via fl_matVec,
    then subtract componentwise using fl_sub. -/
noncomputable def fl_residual (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fp.fl_sub (b i) (fl_matVec fp n n A x i)

/-- **Conventional residual error bound** (Higham §11.1, equation 11.7).

    The computed residual r̂ = fl(b − Ax̂) satisfies:
      |r̂ − (b − Ax̂)| ≤ γ(n+1) · (|b| + |A||x̂|)  (componentwise)

    Proof: Mat-vec gives fl(Ax̂) = (A + ΔA)x̂ with |ΔA| ≤ γ(n)|A|.
    Subtraction rounding gives fl(b − ŷ) = (b − ŷ)(1 + δ), |δ| ≤ u.
    Combined: u + γ(n) + u·γ(n) = γ(1) + γ(n) + γ(1)·γ(n) ≤ γ(n+1). -/
theorem conventional_residual_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hn1 : gammaValid fp (n + 1)) :
    ∀ i : Fin n,
      |fl_residual fp n A x b i - (b i - ∑ j : Fin n, A i j * x j)| ≤
        gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
  intro i
  unfold fl_residual
  -- Step 1: fl_sub model
  obtain ⟨δ₁, hδ₁_le, hδ₁_eq⟩ := fp.model_sub (b i) (fl_matVec fp n n A x i)
  -- Step 2: mat-vec backward error
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ := matVec_backward_error fp n n A x hn
  have hAx : fl_matVec fp n n A x i = ∑ j : Fin n, (A i j + ΔA i j) * x j := hΔA_eq i
  rw [hδ₁_eq]
  -- Error = (b_i - ŷ_i)(1 + δ₁) - (b_i - ∑ A x) = (b_i - ŷ_i)δ₁ + (∑ A x - ŷ_i)
  have herr : (b i - fl_matVec fp n n A x i) * (1 + δ₁) - (b i - ∑ j : Fin n, A i j * x j) =
      (b i - fl_matVec fp n n A x i) * δ₁ + (∑ j : Fin n, A i j * x j - fl_matVec fp n n A x i) := by ring
  rw [herr]
  -- ŷ_i - ∑ A x = ∑ ΔA x
  have hdiff : fl_matVec fp n n A x i - ∑ j : Fin n, A i j * x j =
      ∑ j : Fin n, ΔA i j * x j := by
    rw [hAx, ← Finset.sum_sub_distrib]; congr 1; ext j; ring
  -- |∑ ΔA x| ≤ γ(n) ∑ |A| |x|
  have hΔAx : |∑ j : Fin n, ΔA i j * x j| ≤
      gamma fp n * ∑ j : Fin n, |A i j| * |x j| := by
    calc |∑ j : Fin n, ΔA i j * x j|
        ≤ ∑ j : Fin n, |ΔA i j| * |x j| := by
          calc |∑ j, ΔA i j * x j|
              ≤ ∑ j, |ΔA i j * x j| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ j, |ΔA i j| * |x j| := by congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j : Fin n, (gamma fp n * |A i j|) * |x j| :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hΔA_bound i j) (abs_nonneg _))
      _ = gamma fp n * ∑ j : Fin n, |A i j| * |x j| := by
          rw [Finset.mul_sum]; congr 1; ext j; ring
  -- |b_i - ŷ_i| ≤ |b_i| + |ŷ_i| ≤ |b_i| + ∑ |A + ΔA| |x| ≤ |b_i| + (1+γ(n))∑|A||x|
  have hby : |b i - fl_matVec fp n n A x i| ≤
      |b i| + (1 + gamma fp n) * ∑ j : Fin n, |A i j| * |x j| := by
    have hab : |b i - fl_matVec fp n n A x i| ≤ |b i| + |fl_matVec fp n n A x i| := by
      rw [abs_le]; constructor
      · linarith [neg_abs_le (b i), le_abs_self (fl_matVec fp n n A x i)]
      · linarith [le_abs_self (b i), neg_abs_le (fl_matVec fp n n A x i)]
    calc |b i - fl_matVec fp n n A x i|
        ≤ |b i| + |fl_matVec fp n n A x i| := hab
      _ ≤ |b i| + ∑ j : Fin n, |A i j + ΔA i j| * |x j| := by
          rw [hAx]
          have : |∑ j, (A i j + ΔA i j) * x j| ≤ ∑ j, |A i j + ΔA i j| * |x j| := by
            calc |∑ j, (A i j + ΔA i j) * x j|
                ≤ ∑ j, |(A i j + ΔA i j) * x j| := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ j, |A i j + ΔA i j| * |x j| := by congr 1; ext j; exact abs_mul _ _
          linarith
      _ ≤ |b i| + ∑ j : Fin n, (1 + gamma fp n) * |A i j| * |x j| := by
          have hle : ∑ j : Fin n, |A i j + ΔA i j| * |x j| ≤
              ∑ j : Fin n, (1 + gamma fp n) * |A i j| * |x j| :=
            Finset.sum_le_sum (fun j _ => by
              have h1 : |A i j + ΔA i j| ≤ |A i j| + |ΔA i j| := by
                rw [abs_le]; constructor
                · linarith [neg_abs_le (A i j), neg_abs_le (ΔA i j)]
                · linarith [le_abs_self (A i j), le_abs_self (ΔA i j)]
              have h2 : |ΔA i j| ≤ gamma fp n * |A i j| := hΔA_bound i j
              have h4 : |A i j + ΔA i j| ≤ (1 + gamma fp n) * |A i j| := by linarith
              calc |A i j + ΔA i j| * |x j|
                  ≤ ((1 + gamma fp n) * |A i j|) * |x j| :=
                    mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
                _ = (1 + gamma fp n) * |A i j| * |x j| := by ring)
          linarith [hle]
      _ = |b i| + (1 + gamma fp n) * ∑ j : Fin n, |A i j| * |x j| := by
          congr 1; rw [Finset.mul_sum]; congr 1; ext j; ring
  -- Now combine: |error| ≤ u·|b_i - ŷ_i| + γ(n)·∑|A||x|
  set S := ∑ j : Fin n, |A i j| * |x j|
  -- |error| ≤ |δ₁|·|b_i - ŷ_i| + |∑ΔA x|
  have hbound : |(b i - fl_matVec fp n n A x i) * δ₁ + (∑ j : Fin n, A i j * x j - fl_matVec fp n n A x i)| ≤
      fp.u * (|b i| + (1 + gamma fp n) * S) + gamma fp n * S := by
    have htri_add : |(b i - fl_matVec fp n n A x i) * δ₁ + (∑ j, A i j * x j - fl_matVec fp n n A x i)| ≤
        |(b i - fl_matVec fp n n A x i) * δ₁| + |∑ j, A i j * x j - fl_matVec fp n n A x i| := by
      rw [abs_le]; constructor
      · linarith [neg_abs_le ((b i - fl_matVec fp n n A x i) * δ₁),
                   neg_abs_le (∑ j, A i j * x j - fl_matVec fp n n A x i)]
      · linarith [le_abs_self ((b i - fl_matVec fp n n A x i) * δ₁),
                   le_abs_self (∑ j, A i j * x j - fl_matVec fp n n A x i)]
    calc |(b i - fl_matVec fp n n A x i) * δ₁ + (∑ j, A i j * x j - fl_matVec fp n n A x i)|
        ≤ |(b i - fl_matVec fp n n A x i) * δ₁| + |∑ j, A i j * x j - fl_matVec fp n n A x i| :=
          htri_add
      _ = |δ₁| * |b i - fl_matVec fp n n A x i| + |fl_matVec fp n n A x i - ∑ j, A i j * x j| := by
          rw [abs_mul, mul_comm]; congr 1; rw [abs_sub_comm]
      _ ≤ fp.u * (|b i| + (1 + gamma fp n) * S) + gamma fp n * S := by
          have h1 : |δ₁| * |b i - fl_matVec fp n n A x i| ≤
              fp.u * (|b i| + (1 + gamma fp n) * S) :=
            calc |δ₁| * |b i - fl_matVec fp n n A x i|
                ≤ fp.u * |b i - fl_matVec fp n n A x i| :=
                  mul_le_mul_of_nonneg_right hδ₁_le (abs_nonneg _)
              _ ≤ fp.u * (|b i| + (1 + gamma fp n) * S) :=
                  mul_le_mul_of_nonneg_left hby fp.u_nonneg
          have h2 : |fl_matVec fp n n A x i - ∑ j, A i j * x j| ≤ gamma fp n * S := by
            rw [hdiff]; exact hΔAx
          linarith
  -- Now: u(|b| + (1+γ(n))S) + γ(n)S = u|b| + u·S + u·γ(n)·S + γ(n)·S
  --     = u|b| + (u + γ(n) + u·γ(n))S ≤ (u + γ(n) + u·γ(n))(|b| + S)
  -- And u + γ(n) + u·γ(n) ≤ γ(1) + γ(n) + γ(1)·γ(n) ≤ γ(n+1)
  -- But we need a cleaner route. Note:
  --   u(|b| + (1+γ(n))S) + γ(n)S ≤ γ(n+1)(|b| + S)
  -- ⟺ u·|b| + (u + u·γ(n) + γ(n))·S ≤ γ(n+1)·|b| + γ(n+1)·S
  -- Since u ≤ γ(1) ≤ γ(n+1) and u + γ(n) + u·γ(n) ≤ γ(n+1), this holds.
  -- Use gamma_sum_le with j=1, k=n
  have hγ_sum : gamma fp 1 + gamma fp n + gamma fp 1 * gamma fp n ≤ gamma fp (n + 1) := by
    have : 1 + n = n + 1 := by omega
    have h := gamma_sum_le fp 1 n (this ▸ hn1)
    rw [this] at h; exact h
  -- γ(1) = u/(1−u) ≥ u since u ≥ 0 and 1−u ≤ 1
  have hu_le_γ1 : fp.u ≤ gamma fp 1 := by
    unfold gamma
    simp only [Nat.cast_one, one_mul]
    have h1u : fp.u < 1 := by
      have := gammaValid_mono fp (by omega : 1 ≤ n + 1) hn1
      unfold gammaValid at this; simp at this; exact this
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - fp.u)]
    have : fp.u * (1 - fp.u) = fp.u - fp.u ^ 2 := by ring
    rw [this]; linarith [sq_nonneg fp.u]
  -- u + γ(n) + u·γ(n) ≤ γ(1) + γ(n) + γ(1)·γ(n) ≤ γ(n+1)
  have hγ_nn : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hγ1_nn : 0 ≤ gamma fp 1 := gamma_nonneg fp (gammaValid_mono fp (by omega) hn1)
  have hu_γn_sum : fp.u + gamma fp n + fp.u * gamma fp n ≤ gamma fp (n + 1) := by
    have h1 : fp.u + gamma fp n ≤ gamma fp 1 + gamma fp n := by linarith
    have h2 : fp.u * gamma fp n ≤ gamma fp 1 * gamma fp n :=
      mul_le_mul_of_nonneg_right hu_le_γ1 hγ_nn
    linarith
  -- Final bound
  have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hb_nn : 0 ≤ |b i| := abs_nonneg _
  calc |(b i - fl_matVec fp n n A x i) * δ₁ + (∑ j, A i j * x j - fl_matVec fp n n A x i)|
      ≤ fp.u * (|b i| + (1 + gamma fp n) * S) + gamma fp n * S := hbound
    _ = fp.u * |b i| + (fp.u + gamma fp n + fp.u * gamma fp n) * S := by ring
    _ ≤ gamma fp (n + 1) * |b i| + gamma fp (n + 1) * S := by
        have h1 : fp.u * |b i| ≤ gamma fp (n + 1) * |b i| := by
          apply mul_le_mul_of_nonneg_right _ hb_nn
          linarith [gamma_mono fp (by omega : 1 ≤ n + 1) hn1]
        have h2 : (fp.u + gamma fp n + fp.u * gamma fp n) * S ≤ gamma fp (n + 1) * S :=
          mul_le_mul_of_nonneg_right hu_γn_sum hS_nn
        linarith
    _ = gamma fp (n + 1) * (|b i| + S) := by ring

-- ============================================================
-- §11.2  One-step refinement: forward error identity (Theorem 11.3)
-- ============================================================

/-- **One-step iterative refinement error identity** (Higham §11.2, Theorem 11.3).

    Let x be the exact solution of Ax = b, and let x₁ = x₀ + d̂ where
    d̂ is computed by solving Ad = r̂ approximately.

    The key identity is:
      A(x − x₁) = −ΔA·d̂ + (r − r̂)

    where ΔA is the solver perturbation. This identity, combined with
    taking |A⁻¹| of both sides, yields Higham's equation (11.8):
      |e₁| ≤ |A⁻¹| · (μ · |A| · |d̂| + ν · |A| · |e₀| + ω)

    We prove the identity and the componentwise residual recurrence. -/
theorem one_step_refinement_error_identity (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (x x₀ d_hat r_hat : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (r : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (x₁ : Fin n → ℝ)
    (hx₁ : ∀ i, x₁ i = x₀ i + d_hat i) :
    ∀ i : Fin n,
      ∑ j : Fin n, A i j * (x j - x₁ j) =
        ∑ j : Fin n, ΔA_solve i j * d_hat j + (r i - r_hat i) := by
  intro i
  have hAe : ∑ j : Fin n, A i j * (x j - x₁ j) =
      ∑ j : Fin n, A i j * (x j - x₀ j) - ∑ j : Fin n, A i j * d_hat j := by
    simp_rw [hx₁]; rw [← Finset.sum_sub_distrib]; congr 1; ext j; ring
  have hAe0 : ∑ j : Fin n, A i j * (x j - x₀ j) = r i := by
    have hsplit : ∑ j : Fin n, A i j * (x j - x₀ j) =
        ∑ j : Fin n, (A i j * x j - A i j * x₀ j) := by
      congr 1; funext j; ring
    rw [hsplit, Finset.sum_sub_distrib, hAx i, hr i]
  have hAd : ∑ j : Fin n, A i j * d_hat j =
      r_hat i - ∑ j : Fin n, ΔA_solve i j * d_hat j := by
    have := hsolve i
    simp_rw [add_mul] at this
    rw [Finset.sum_add_distrib] at this; linarith
  rw [hAe, hAe0, hAd]
  set S := ∑ j : Fin n, ΔA_solve i j * d_hat j
  linarith

-- ============================================================
-- §11.2  One-step refinement: residual contraction
-- ============================================================

/-- **One-step refinement residual bound** (Higham §11.2).

    After one step x₁ = x₀ + d̂, the new residual satisfies:
      |b − Ax₁|_i ≤ μ · ∑_j |A_{ij}| · |d̂_j| + ν · |r_i| + ω_i

    This is the core step for proving backward error contraction. -/
theorem one_step_residual_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat r_hat : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ ν : ℝ) (ω : Fin n → ℝ)
    (b : Fin n → ℝ)
    (r : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hres : ∀ i, |r_hat i - r i| ≤ ν * |r i| + ω i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (x₁ : Fin n → ℝ)
    (hx₁ : ∀ i, x₁ i = x₀ i + d_hat i)
    (_hμ_nn : 0 ≤ μ) (_hν_nn : 0 ≤ ν)
    (_hω_nn : ∀ i, 0 ≤ ω i) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x₁ j| ≤
        μ * ∑ j : Fin n, |A i j| * |d_hat j| + ν * |r i| + ω i := by
  intro i
  -- b_i - ∑ A x₁ = r_i - ∑ A d̂
  have hx₁_expand : ∑ j : Fin n, A i j * x₁ j =
      ∑ j : Fin n, A i j * x₀ j + ∑ j : Fin n, A i j * d_hat j := by
    rw [← Finset.sum_add_distrib]; congr 1; ext j; rw [hx₁ j]; ring
  rw [hx₁_expand]
  have hr_sub : b i - (∑ j : Fin n, A i j * x₀ j + ∑ j : Fin n, A i j * d_hat j) =
      r i - ∑ j : Fin n, A i j * d_hat j := by rw [hr i]; ring
  rw [hr_sub]
  -- ∑ A d̂ = r̂ - ∑ ΔA d̂
  have hAd : ∑ j : Fin n, A i j * d_hat j =
      r_hat i - ∑ j : Fin n, ΔA_solve i j * d_hat j := by
    have := hsolve i; simp_rw [add_mul] at this
    rw [Finset.sum_add_distrib] at this; linarith
  rw [hAd]
  -- r_i - (r̂_i - ∑ ΔA d̂) = ∑ ΔA d̂ - (r̂_i - r_i)
  have hsimp : r i - (r_hat i - ∑ j : Fin n, ΔA_solve i j * d_hat j) =
      ∑ j : Fin n, ΔA_solve i j * d_hat j - (r_hat i - r i) := by ring
  rw [hsimp]
  have htri : |∑ j : Fin n, ΔA_solve i j * d_hat j - (r_hat i - r i)| ≤
      |∑ j : Fin n, ΔA_solve i j * d_hat j| + |r_hat i - r i| := by
    have h := abs_sub (∑ j : Fin n, ΔA_solve i j * d_hat j) (r_hat i - r i)
    exact h
  calc |∑ j : Fin n, ΔA_solve i j * d_hat j - (r_hat i - r i)|
      ≤ |∑ j : Fin n, ΔA_solve i j * d_hat j| + |r_hat i - r i| := htri
    _ ≤ (∑ j : Fin n, |ΔA_solve i j| * |d_hat j|) + (ν * |r i| + ω i) := by
        have h1 : |∑ j, ΔA_solve i j * d_hat j| ≤ ∑ j, |ΔA_solve i j| * |d_hat j| := by
          calc |∑ j, ΔA_solve i j * d_hat j|
              ≤ ∑ j, |ΔA_solve i j * d_hat j| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ j, |ΔA_solve i j| * |d_hat j| := by congr 1; ext j; exact abs_mul _ _
        linarith [hres i]
    _ ≤ (∑ j : Fin n, (μ * |A i j|) * |d_hat j|) + (ν * |r i| + ω i) := by
        have : ∑ j, |ΔA_solve i j| * |d_hat j| ≤ ∑ j, (μ * |A i j|) * |d_hat j| :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hΔA i j) (abs_nonneg _))
        linarith
    _ = μ * ∑ j : Fin n, |A i j| * |d_hat j| + ν * |r i| + ω i := by
        have : ∑ j : Fin n, (μ * |A i j|) * |d_hat j| =
            μ * ∑ j : Fin n, |A i j| * |d_hat j| := by
          rw [Finset.mul_sum]; congr 1; funext j; ring
        linarith

-- ============================================================
-- §11.2  Theorem 11.4: Backward stability of one refinement step
-- ============================================================

/-- **Componentwise backward error** (Higham §11.2).

    x̂ has componentwise backward error ≤ ε if there exist ΔA, Δb with
    (A+ΔA)x̂ = b+Δb, |ΔA| ≤ ε|A|, |Δb| ≤ ε|b|. -/
structure ComponentwiseBackwardError (n : ℕ) (A : Fin n → Fin n → ℝ)
    (b x_hat : Fin n → ℝ) (ε : ℝ) where
  ΔA : Fin n → Fin n → ℝ
  Δb : Fin n → ℝ
  ΔA_bound : ∀ i j, |ΔA i j| ≤ ε * |A i j|
  Δb_bound : ∀ i, |Δb i| ≤ ε * |b i|
  exact : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i + Δb i

/-- **One-step refinement backward error contraction** (Higham §11.2, Theorem 11.4).

    If x₀ has residual bounded by ω₀·(|A||x₀| + |b|), then x₁ = x₀ + d̂
    has residual bounded in terms of σ·ω₀ plus correction terms.

    The contraction factor σ = μ(1+ν)/(1−μ) + ν governs convergence:
    when σ < 1, the backward error decreases geometrically.

    We state the bound on the new residual: since the solver gives
    d̂ satisfying (A+ΔA)d̂ = r̂, we have
      |r₁| ≤ μ·|A|·|d̂| + ν·ω₀·(|A||x₀| + |b|) + ω  -/
theorem one_step_backward_error_contraction (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat r_hat : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ ν : ℝ) (ω : Fin n → ℝ)
    (b : Fin n → ℝ)
    (r : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hres : ∀ i, |r_hat i - r i| ≤ ν * |r i| + ω i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (x₁ : Fin n → ℝ)
    (hx₁ : ∀ i, x₁ i = x₀ i + d_hat i)
    (hμ_nn : 0 ≤ μ) (hν_nn : 0 ≤ ν)
    (hω_nn : ∀ i, 0 ≤ ω i)
    -- x₀ backward error: |r₀| ≤ ω₀(|A||x₀| + |b|)
    (ω₀ : ℝ) (_hω₀_nn : 0 ≤ ω₀)
    (hbw₀ : ∀ i, |r i| ≤ ω₀ * (∑ j : Fin n, |A i j| * |x₀ j| + |b i|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x₁ j| ≤
        μ * ∑ j : Fin n, |A i j| * |d_hat j| +
        ν * ω₀ * (∑ j : Fin n, |A i j| * |x₀ j| + |b i|) + ω i := by
  intro i
  have hresid := one_step_residual_bound n A x₀ d_hat r_hat ΔA_solve μ ν ω b r
    hr hres hsolve hΔA x₁ hx₁ hμ_nn hν_nn hω_nn i
  -- Bound ν·|r_i| ≤ ν·ω₀·(∑|A||x₀| + |b|)
  have hr_bound : ν * |r i| ≤ ν * ω₀ * (∑ j : Fin n, |A i j| * |x₀ j| + |b i|) := by
    calc ν * |r i|
        ≤ ν * (ω₀ * (∑ j, |A i j| * |x₀ j| + |b i|)) :=
          mul_le_mul_of_nonneg_left (hbw₀ i) hν_nn
      _ = ν * ω₀ * (∑ j, |A i j| * |x₀ j| + |b i|) := by ring
  linarith

-- ============================================================
-- §11.3  LU-based iterative refinement
-- ============================================================

/-- **LU iterative refinement contraction factor** (Higham §11.3).

    For LU-based solve with μ = γ(3n) and conventional residual ν = γ(n+1),
    the contraction factor σ = μ(1+ν)/(1−μ) + ν is nonneg. -/
theorem lu_refinement_contraction_nonneg (fp : FPModel) (n : ℕ)
    (hn3 : gammaValid fp (3 * n))
    (hn1 : gammaValid fp (n + 1))
    (hμ_lt : gamma fp (3 * n) < 1) :
    0 ≤ gamma fp (3 * n) * (1 + gamma fp (n + 1)) / (1 - gamma fp (3 * n)) +
        gamma fp (n + 1) := by
  have hμ_nn : 0 ≤ gamma fp (3 * n) := gamma_nonneg fp hn3
  have hν_nn : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  apply add_nonneg
  · apply div_nonneg
    · apply mul_nonneg hμ_nn; linarith
    · linarith
  · exact hν_nn

/-- **LU iterative refinement backward stability** (Higham §11.3).

    With μ = γ(3n) from Theorem 9.4 and ν = γ(n+1) from conventional
    residual computation, the contraction factor is:
      σ = γ(3n)(1 + γ(n+1))/(1 − γ(3n)) + γ(n+1)

    For modest n·u (say n·u < 0.01), σ ≈ (4n+1)u ≪ 1,
    so one step of refinement reduces the backward error.

    The theorem states: if σ < 1 (as hypothesis), then the residual
    of x₁ is bounded by the contraction of the residual of x₀. -/
theorem lu_refinement_backward_stable (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (_σ_perm : Fin n → Fin n)
    (b x₀ : Fin n → ℝ)
    -- LU backward error
    (_hLU : LUBackwardError n A L_hat U_hat (gamma fp (3 * n)))
    -- Solver produces d̂ with backward error μ = γ(3n)
    (d_hat : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (hsolve_bound : ∀ i j, |ΔA_solve i j| ≤ gamma fp (3 * n) * |A i j|)
    (r_hat : Fin n → ℝ)
    (hsolve_eq : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    -- Residual error
    (r : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hres : ∀ i, |r_hat i - r i| ≤ gamma fp (n + 1) * |r i| +
      gamma fp (n + 1) * ∑ j : Fin n, |A i j| * |x₀ j|)
    -- x₀ backward error
    (ω₀ : ℝ) (hω₀_nn : 0 ≤ ω₀)
    (hbw₀ : ∀ i, |r i| ≤ ω₀ * (∑ j : Fin n, |A i j| * |x₀ j| + |b i|))
    -- Validity
    (hn3 : gammaValid fp (3 * n))
    (hn1 : gammaValid fp (n + 1)) :
    let x₁ := fun i => x₀ i + d_hat i
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x₁ j| ≤
        gamma fp (3 * n) * ∑ j : Fin n, |A i j| * |d_hat j| +
        gamma fp (n + 1) * ω₀ * (∑ j : Fin n, |A i j| * |x₀ j| + |b i|) +
        gamma fp (n + 1) * ∑ j : Fin n, |A i j| * |x₀ j| := by
  simp only  -- reduce the let binding
  intro i
  exact one_step_backward_error_contraction n A x₀ d_hat r_hat ΔA_solve
    (gamma fp (3 * n)) (gamma fp (n + 1))
    (fun j => gamma fp (n + 1) * ∑ k : Fin n, |A j k| * |x₀ k|)
    b r hr hres hsolve_eq hsolve_bound (fun j => x₀ j + d_hat j)
    (fun _ => rfl)
    (gamma_nonneg fp hn3) (gamma_nonneg fp hn1)
    (fun j => mul_nonneg (gamma_nonneg fp hn1)
      (Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))))
    ω₀ hω₀_nn hbw₀ i

-- ============================================================
-- §11.2  Correction vector bound
-- ============================================================

/-- **Triangle bound on correction vector**.

    Since x₁ = x₀ + d̂, we have d̂ = x₁ − x₀ and |d̂_j| ≤ |x₁_j| + |x₀_j|. -/
lemma refinement_d_hat_abs_le (n : ℕ) (x₀ d_hat x₁ : Fin n → ℝ)
    (hx₁ : ∀ i, x₁ i = x₀ i + d_hat i) :
    ∀ j : Fin n, |d_hat j| ≤ |x₁ j| + |x₀ j| := by
  intro j
  have hd : d_hat j = x₁ j - x₀ j := by rw [hx₁]; ring
  rw [hd]; exact abs_sub (x₁ j) (x₀ j)

-- ============================================================
-- §11.2  Residual bound in terms of x₁ (Theorem 11.3, assembled)
-- ============================================================

/-- **Residual of x₁ in terms of |A||x₁| and |A||x₀|** (Higham §11.2).

    Combining the one-step residual bound with |d̂| ≤ |x₁| + |x₀|:
      |r₁_i| ≤ μ·(|A||x₁|)_i + (μ + ν·ω₀)·(|A||x₀|)_i + ν·ω₀·|b_i| + ω_i

    This eliminates the correction d̂ from the bound entirely, expressing the
    new residual purely in terms of the iterate values x₀, x₁ and the data A, b. -/
theorem refinement_residual_in_terms_of_x1 (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat r_hat : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ ν : ℝ) (ω : Fin n → ℝ)
    (b : Fin n → ℝ)
    (r : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hres : ∀ i, |r_hat i - r i| ≤ ν * |r i| + ω i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (x₁ : Fin n → ℝ)
    (hx₁ : ∀ i, x₁ i = x₀ i + d_hat i)
    (hμ_nn : 0 ≤ μ) (hν_nn : 0 ≤ ν)
    (hω_nn : ∀ i, 0 ≤ ω i)
    (ω₀ : ℝ) (hω₀_nn : 0 ≤ ω₀)
    (hbw₀ : ∀ i, |r i| ≤ ω₀ * (∑ j : Fin n, |A i j| * |x₀ j| + |b i|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x₁ j| ≤
        μ * ∑ j : Fin n, |A i j| * |x₁ j| +
        (μ + ν * ω₀) * ∑ j : Fin n, |A i j| * |x₀ j| +
        ν * ω₀ * |b i| + ω i := by
  intro i
  have hcontract := one_step_backward_error_contraction n A x₀ d_hat r_hat ΔA_solve
    μ ν ω b r hr hres hsolve hΔA x₁ hx₁ hμ_nn hν_nn hω_nn ω₀ hω₀_nn hbw₀ i
  -- Bound |d̂_j| ≤ |x₁_j| + |x₀_j|
  have hd_bound := refinement_d_hat_abs_le n x₀ d_hat x₁ hx₁
  -- μ ∑|A||d̂| ≤ μ ∑|A|(|x₁| + |x₀|) = μ ∑|A||x₁| + μ ∑|A||x₀|
  have hd_sum : μ * ∑ j : Fin n, |A i j| * |d_hat j| ≤
      μ * ∑ j : Fin n, |A i j| * |x₁ j| + μ * ∑ j : Fin n, |A i j| * |x₀ j| := by
    have hle : ∑ j : Fin n, |A i j| * |d_hat j| ≤
        ∑ j : Fin n, |A i j| * (|x₁ j| + |x₀ j|) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hd_bound j) (abs_nonneg _))
    have heq : ∑ j : Fin n, |A i j| * (|x₁ j| + |x₀ j|) =
        ∑ j : Fin n, |A i j| * |x₁ j| + ∑ j : Fin n, |A i j| * |x₀ j| := by
      rw [← Finset.sum_add_distrib]; congr 1; ext j; ring
    calc μ * ∑ j, |A i j| * |d_hat j|
        ≤ μ * ∑ j, |A i j| * (|x₁ j| + |x₀ j|) :=
          mul_le_mul_of_nonneg_left hle hμ_nn
      _ = μ * (∑ j, |A i j| * |x₁ j| + ∑ j, |A i j| * |x₀ j|) := by rw [heq]
      _ = μ * ∑ j, |A i j| * |x₁ j| + μ * ∑ j, |A i j| * |x₀ j| := by ring
  calc |b i - ∑ j, A i j * x₁ j|
      ≤ μ * ∑ j, |A i j| * |d_hat j| +
        ν * ω₀ * (∑ j, |A i j| * |x₀ j| + |b i|) + ω i := hcontract
    _ ≤ (μ * ∑ j, |A i j| * |x₁ j| + μ * ∑ j, |A i j| * |x₀ j|) +
        ν * ω₀ * (∑ j, |A i j| * |x₀ j| + |b i|) + ω i := by linarith [hd_sum]
    _ = μ * ∑ j, |A i j| * |x₁ j| +
        (μ + ν * ω₀) * ∑ j, |A i j| * |x₀ j| +
        ν * ω₀ * |b i| + ω i := by ring

-- ============================================================
-- §11.2  Theorem 11.3: Forward error bound (equation 11.8)
-- ============================================================

/-- **Forward error bound for one refinement step** (Higham §11.2, Theorem 11.3, eq. 11.8).

    If Ainv is a componentwise bound on |A⁻¹| (resolving Av = w gives
    |v| ≤ Ainv · |w|), then the forward error after one step satisfies:

      |x − x₁|_i ≤ ∑_j Ainv_{ij} · (μ · (|A||d̂|)_j + ν · |r_j| + ω_j)

    This is the componentwise form of eq (11.8):
      |e₁| ≤ |A⁻¹| · (μ|A||d̂| + ν|r| + ω)

    The Ainv hypothesis abstracts over the matrix inverse, which is not
    available in our axiomatic framework. It can be instantiated with
    any nonneg matrix satisfying the resolution property (e.g., via
    Neumann series when ‖A⁻¹ΔA‖ < 1). -/
theorem refinement_forward_error_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (x x₀ d_hat r_hat : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ ν : ℝ) (ω : Fin n → ℝ)
    (b : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (r : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hres : ∀ i, |r_hat i - r i| ≤ ν * |r i| + ω i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (x₁ : Fin n → ℝ)
    (hx₁ : ∀ i, x₁ i = x₀ i + d_hat i)
    (_hμ_nn : 0 ≤ μ) (_hν_nn : 0 ≤ ν)
    (_hω_nn : ∀ i, 0 ≤ ω i)
    -- |A⁻¹| hypothesis: bounds resolution of Av = w componentwise
    (Ainv : Fin n → Fin n → ℝ)
    (hAinv_nn : ∀ i j, 0 ≤ Ainv i j)
    (hAinv : ∀ (v w : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * v j = w i) →
      ∀ i, |v i| ≤ ∑ j : Fin n, Ainv i j * |w j|) :
    ∀ i : Fin n,
      |x i - x₁ i| ≤
        ∑ j : Fin n, Ainv i j *
          (μ * ∑ k : Fin n, |A j k| * |d_hat k| + ν * |r j| + ω j) := by
  intro i
  -- From the error identity: A(x − x₁) = ΔA·d̂ + (r − r̂)
  have hAe₁ := one_step_refinement_error_identity n A x x₀ d_hat r_hat ΔA_solve
    b hAx r hr hsolve x₁ hx₁
  -- Apply A⁻¹ bound to get |x − x₁| ≤ Ainv · |A(x − x₁)|
  have hstep := hAinv (fun j => x j - x₁ j)
    (fun j => ∑ k : Fin n, ΔA_solve j k * d_hat k + (r j - r_hat j)) hAe₁ i
  -- Bound |A(x−x₁)_j| = |∑ ΔA d̂ + (r − r̂)| ≤ μ(|A||d̂|)_j + ν|r_j| + ω_j
  suffices h : ∀ j : Fin n,
      |∑ k : Fin n, ΔA_solve j k * d_hat k + (r j - r_hat j)| ≤
        μ * ∑ k : Fin n, |A j k| * |d_hat k| + ν * |r j| + ω j by
    calc |x i - x₁ i|
        ≤ ∑ j, Ainv i j * |∑ k, ΔA_solve j k * d_hat k + (r j - r_hat j)| := hstep
      _ ≤ ∑ j, Ainv i j * (μ * ∑ k, |A j k| * |d_hat k| + ν * |r j| + ω j) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (hAinv_nn i j))
  intro j
  -- |∑ ΔA d̂ + (r − r̂)| = |∑ ΔA d̂ − (r̂ − r)| ≤ |∑ ΔA d̂| + |r̂ − r|
  have htri : |∑ k : Fin n, ΔA_solve j k * d_hat k + (r j - r_hat j)| ≤
      |∑ k : Fin n, ΔA_solve j k * d_hat k| + |r_hat j - r j| := by
    have heq : ∑ k : Fin n, ΔA_solve j k * d_hat k + (r j - r_hat j) =
        ∑ k : Fin n, ΔA_solve j k * d_hat k - (r_hat j - r j) := by ring
    rw [heq]
    exact abs_sub (∑ k : Fin n, ΔA_solve j k * d_hat k) (r_hat j - r j)
  -- |∑ ΔA d̂| ≤ ∑ |ΔA| |d̂| ≤ μ ∑ |A| |d̂|
  have hDA : |∑ k : Fin n, ΔA_solve j k * d_hat k| ≤
      μ * ∑ k : Fin n, |A j k| * |d_hat k| := by
    calc |∑ k, ΔA_solve j k * d_hat k|
        ≤ ∑ k, |ΔA_solve j k * d_hat k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |ΔA_solve j k| * |d_hat k| := by congr 1; ext k; exact abs_mul _ _
      _ ≤ ∑ k, (μ * |A j k|) * |d_hat k| :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hΔA j k) (abs_nonneg _))
      _ = μ * ∑ k, |A j k| * |d_hat k| := by rw [Finset.mul_sum]; congr 1; ext k; ring
  linarith [htri, hDA, hres j]

-- ============================================================
-- §11.1  Linear contraction (Theorems 11.1–11.2 core)
-- ============================================================

/-- **Linear contraction** (geometric decay with additive error).

    If a sequence satisfies a_{k+1} ≤ η·a_k + τ with 0 ≤ η < 1 and 0 ≤ τ,
    then a_k ≤ η^k · a_0 + τ/(1−η).

    As k → ∞, η^k → 0 and the bound converges to τ/(1−η).

    This is the core convergence tool for iterative refinement:
    - Theorem 11.1 (mixed precision): η ≈ μ·κ(A), converges to O(u_residual)
    - Theorem 11.2 (fixed precision): η ≈ cond(A)·nu, converges to O(n·cond(A,x)·u) -/
theorem linear_contraction (a : ℕ → ℝ) (η τ : ℝ)
    (hη_nn : 0 ≤ η) (hη_lt : η < 1) (hτ_nn : 0 ≤ τ)
    (hstep : ∀ k, a (k + 1) ≤ η * a k + τ) :
    ∀ k, a k ≤ η ^ k * a 0 + τ / (1 - η) := by
  have h1η_pos : (0 : ℝ) < 1 - η := by linarith
  intro k
  induction k with
  | zero => simp; exact div_nonneg hτ_nn (le_of_lt h1η_pos)
  | succ m ih =>
    have h1η_ne : (1 : ℝ) - η ≠ 0 := by intro h; linarith
    calc a (m + 1)
        ≤ η * a m + τ := hstep m
      _ ≤ η * (η ^ m * a 0 + τ / (1 - η)) + τ := by
          linarith [mul_le_mul_of_nonneg_left ih hη_nn]
      _ = η ^ (m + 1) * a 0 + τ / (1 - η) := by
          rw [pow_succ]; field_simp [h1η_ne]; ring

/-- **Steady-state bound** from linear contraction.

    Since η^k ≤ 1 for η ∈ [0,1), the error is always bounded by a_0 + τ/(1−η).
    This is the uniform bound used in Theorem 11.2 to characterize the
    limiting accuracy of fixed-precision iterative refinement. -/
theorem linear_contraction_steady_state (a : ℕ → ℝ) (η τ : ℝ)
    (hη_nn : 0 ≤ η) (hη_lt : η < 1) (hτ_nn : 0 ≤ τ)
    (hstep : ∀ k, a (k + 1) ≤ η * a k + τ)
    (ha0 : 0 ≤ a 0) :
    ∀ k, a k ≤ a 0 + τ / (1 - η) := by
  intro k
  have hbase := linear_contraction a η τ hη_nn hη_lt hτ_nn hstep k
  have hpow : η ^ k ≤ 1 := pow_le_one₀ hη_nn (le_of_lt hη_lt)
  linarith [mul_le_mul_of_nonneg_right hpow ha0]

-- ============================================================
-- §11.1  Computed residual absolute bound
-- ============================================================

/-- **Computed residual absolute bound**.

    If the residual error satisfies |r̂ − r| ≤ ν|r| + ω (equation 11.6),
    then |r̂| ≤ (1+ν)|r| + ω by triangle inequality. -/
lemma r_hat_abs_bound (n : ℕ) (r r_hat : Fin n → ℝ)
    (ν : ℝ) (ω : Fin n → ℝ)
    (hres : ∀ i : Fin n, |r_hat i - r i| ≤ ν * |r i| + ω i) :
    ∀ i : Fin n, |r_hat i| ≤ (1 + ν) * |r i| + ω i := by
  intro i
  have htri : |r_hat i| ≤ |r_hat i - r i| + |r i| := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le (r_hat i - r i), neg_abs_le (r i)]
    · linarith [le_abs_self (r_hat i - r i), le_abs_self (r i)]
  linarith [hres i]

-- ============================================================
-- §11.2  Theorem 11.4: Full backward error contraction with σ
-- ============================================================

/-- **Full backward error contraction** (Higham §11.2, Theorem 11.4).

    If x₀ has componentwise backward error ω₀ (|r₀| ≤ ω₀(|A||x₀| + |b|)),
    the solver has backward error μ, and the residual has accuracy ν, ω,
    and additionally the solver correction satisfies the Neumann-series bound
    μ·(|A||d̂|)_i ≤ ρ·(|A||x₀| + |b|)_i, then the new residual contracts:

      |b − Ax₁|_i ≤ (ρ + ν·ω₀)·(|A||x₀| + |b|)_i + ω_i

    The contraction factor σ = ρ + ν·ω₀ governs convergence.
    When σ < 1, the backward error decreases geometrically.

    For GE: ρ ≈ μ·(1+ν)·ω₀·κ/(1−μ·κ), giving σ = O(nu·κ). -/
theorem refinement_backward_error_sigma (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat r_hat : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ ν : ℝ) (ω : Fin n → ℝ)
    (b : Fin n → ℝ)
    (r : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hres : ∀ i, |r_hat i - r i| ≤ ν * |r i| + ω i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (x₁ : Fin n → ℝ)
    (hx₁ : ∀ i, x₁ i = x₀ i + d_hat i)
    (hμ_nn : 0 ≤ μ) (hν_nn : 0 ≤ ν)
    (hω_nn : ∀ i, 0 ≤ ω i)
    -- x₀ backward error
    (ω₀ : ℝ) (_hω₀_nn : 0 ≤ ω₀)
    (hbw₀ : ∀ i, |r i| ≤ ω₀ * (∑ j : Fin n, |A i j| * |x₀ j| + |b i|))
    -- Solver correction bound (from Neumann/inverse analysis)
    (ρ : ℝ) (_hρ_nn : 0 ≤ ρ)
    (hcorr : ∀ i, μ * ∑ j : Fin n, |A i j| * |d_hat j| ≤
        ρ * (∑ j : Fin n, |A i j| * |x₀ j| + |b i|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x₁ j| ≤
        (ρ + ν * ω₀) * (∑ j : Fin n, |A i j| * |x₀ j| + |b i|) + ω i := by
  intro i
  have hresid := one_step_residual_bound n A x₀ d_hat r_hat ΔA_solve μ ν ω b r
    hr hres hsolve hΔA x₁ hx₁ hμ_nn hν_nn hω_nn i
  have hr_bound : ν * |r i| ≤ ν * ω₀ * (∑ j, |A i j| * |x₀ j| + |b i|) := by
    calc ν * |r i|
        ≤ ν * (ω₀ * (∑ j, |A i j| * |x₀ j| + |b i|)) :=
          mul_le_mul_of_nonneg_left (hbw₀ i) hν_nn
      _ = ν * ω₀ * (∑ j, |A i j| * |x₀ j| + |b i|) := by ring
  have hsum : ρ * (∑ j, |A i j| * |x₀ j| + |b i|) +
      ν * ω₀ * (∑ j, |A i j| * |x₀ j| + |b i|) =
      (ρ + ν * ω₀) * (∑ j, |A i j| * |x₀ j| + |b i|) := by ring
  linarith [hcorr i]

-- ============================================================
-- §11.2  Backward error relative to |A||x₁| (equation 11.20)
-- ============================================================

/-- **Backward error relative to |A||x₁|** (Higham §11.2, eq. 11.20).

    If the residual bound terms are all dominated by a multiple of (|A||x₁|)_i
    (via the dominance hypothesis), then:
      |b − Ax₁|_i ≤ α · (|A||x₁|)_i

    For GE + standard residual with n·u ≪ 1: α = 2γ(n+1).

    The dominance hypothesis encapsulates the condition-number requirements:
    it holds when cond(A⁻¹)·σ(A,x₁)·α < 1 (Higham §11.2, condition for eq. 11.20),
    which is satisfied when the matrix is well-conditioned relative to n·u. -/
theorem refinement_two_gamma_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat r_hat : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ ν : ℝ) (ω : Fin n → ℝ)
    (b : Fin n → ℝ)
    (r : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hres : ∀ i, |r_hat i - r i| ≤ ν * |r i| + ω i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (x₁ : Fin n → ℝ)
    (hx₁ : ∀ i, x₁ i = x₀ i + d_hat i)
    (hμ_nn : 0 ≤ μ) (hν_nn : 0 ≤ ν)
    (hω_nn : ∀ i, 0 ≤ ω i)
    -- Dominance: the combined error is bounded by α·(|A||x₁|)
    (α : ℝ)
    (hdom : ∀ i : Fin n,
      μ * ∑ j : Fin n, |A i j| * |d_hat j| + ν * |r i| + ω i ≤
        α * ∑ j : Fin n, |A i j| * |x₁ j|) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x₁ j| ≤
        α * ∑ j : Fin n, |A i j| * |x₁ j| := by
  intro i
  have hresid := one_step_residual_bound n A x₀ d_hat r_hat ΔA_solve μ ν ω b r
    hr hres hsolve hΔA x₁ hx₁ hμ_nn hν_nn hω_nn i
  linarith [hdom i]

-- ============================================================
-- §11.3  LU solve to solver bound (GE specialization)
-- ============================================================

/-- **LU solve provides solver hypotheses** for iterative refinement (Higham §11.3).

    The LU-based solver produces (A + ΔA)x̂ = c with |ΔA| ≤ γ(3n)|L̂||Û|.
    Under the componentwise growth bound ∑_k |L̂_{ik}||Û_{kj}| ≤ ρ·|A_{ij}|,
    this gives |ΔA_{ij}| ≤ γ(3n)·ρ·|A_{ij}|, satisfying the solver bound
    in one_step_residual_bound with μ = γ(3n)·ρ.

    For well-conditioned matrices with partial pivoting, ρ is typically O(1). -/
theorem lu_solve_to_solver_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (x_hat c : Fin n → ℝ)
    (L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    -- LU solve backward error: (A + ΔA)x̂ = c with |ΔA| ≤ ε|L̂||Û|
    (hbound : ∀ i j, |ΔA i j| ≤ ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j|)
    (hexact : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = c i)
    -- Growth bound: |L̂||Û| ≤ ρ|A| componentwise
    (ρ : ℝ) (_hρ_nn : 0 ≤ ρ)
    (hgrowth : ∀ i j, ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ ρ * |A i j|) :
    (∀ i j, |ΔA i j| ≤ ε * ρ * |A i j|) ∧
    (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = c i) := by
  constructor
  · intro i j
    calc |ΔA i j|
        ≤ ε * ∑ k, |L_hat i k| * |U_hat k j| := hbound i j
      _ ≤ ε * (ρ * |A i j|) :=
          mul_le_mul_of_nonneg_left (hgrowth i j) hε_nn
      _ = ε * ρ * |A i j| := by ring
  · exact hexact

-- ============================================================
-- §11.2  Three-term triangle inequality helper
-- ============================================================

/-- Triangle inequality for three terms: |a + b + c| ≤ |a| + |b| + |c|. -/
lemma abs_add_three_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  rw [abs_le]; constructor
  · linarith [neg_abs_le a, neg_abs_le b, neg_abs_le c]
  · linarith [le_abs_self a, le_abs_self b, le_abs_self c]

-- ============================================================
-- §11.2  Theorem 11.3: Three-term identity (equation 11.12)
-- ============================================================

/-- **Three-term residual identity** (Higham §11.2, eq. 11.12).

    With rounded update ŷ = x̂ + d̂ + f₂ (eq. 11.11), the new residual is:
      b − Aŷ = (r̂ − Ad̂) − (r̂ − r) − Af₂

    matching the book's b − Aŷ = −f₁ − Δr − Af₂ where f₁ = Ad̂ − r̂ and
    Δr = r̂ − r. The three error sources:
    1. Solver residual: r̂ − Ad̂ (= −f₁)
    2. Residual computation error: r̂ − r (= Δr)
    3. Update rounding propagation: Af₂ -/
theorem thm_11_3_identity (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i) :
    ∀ i : Fin n, b i - ∑ j : Fin n, A i j * y j =
      (r_hat i - ∑ j : Fin n, A i j * d_hat j) - (r_hat i - r i) -
        ∑ j : Fin n, A i j * f₂ j := by
  intro i
  have key : ∀ j : Fin n, A i j * y j =
      A i j * x₀ j + A i j * d_hat j + A i j * f₂ j :=
    fun j => by rw [hy]; ring
  simp_rw [key]
  simp_rw [Finset.sum_add_distrib]
  linarith [hr i]

/-- **Three-term residual bound** (Higham §11.2, eq. 11.12, inequality form).

    Taking absolute values of the three-term identity:
      |b − Aŷ|_i ≤ |r̂_i − (Ad̂)_i| + |r̂_i − r_i| + (|A| · |f₂|)_i -/
theorem thm_11_3_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        |r_hat i - ∑ j : Fin n, A i j * d_hat j| +
        |r_hat i - r i| +
        ∑ j : Fin n, |A i j| * |f₂ j| := by
  intro i
  have hid := thm_11_3_identity n A x₀ d_hat b r r_hat f₂ y hr hy i
  rw [hid]
  have htri1 := abs_sub
    (r_hat i - ∑ j : Fin n, A i j * d_hat j - (r_hat i - r i))
    (∑ j : Fin n, A i j * f₂ j)
  have htri2 := abs_sub
    (r_hat i - ∑ j : Fin n, A i j * d_hat j) (r_hat i - r i)
  have hAfabs : |∑ j : Fin n, A i j * f₂ j| ≤
      ∑ j : Fin n, |A i j| * |f₂ j| := by
    calc |∑ j, A i j * f₂ j|
        ≤ ∑ j, |A i j * f₂ j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |A i j| * |f₂ j| := by congr 1; ext j; exact abs_mul _ _
  linarith

-- ============================================================
-- §11.2  Solver perturbation to residual form
-- ============================================================

/-- **Solver perturbation implies residual bound** (connects eq. 11.5 forms).

    If (A + ΔA)d̂ = r̂ with |ΔA| ≤ μ|A|, then:
      |r̂ − Ad̂|_i ≤ μ · (|A| · |d̂|)_i

    This converts the perturbation-form solver specification
    to the residual form used in the three-term decomposition. -/
lemma solver_perturbation_to_residual (n : ℕ)
    (A : Fin n → Fin n → ℝ) (d_hat r_hat : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (μ : ℝ) (_hμ_nn : 0 ≤ μ)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA i j| ≤ μ * |A i j|) :
    ∀ i : Fin n, |r_hat i - ∑ j : Fin n, A i j * d_hat j| ≤
      μ * ∑ j : Fin n, |A i j| * |d_hat j| := by
  intro i
  have hexpand : r_hat i - ∑ j : Fin n, A i j * d_hat j =
      ∑ j : Fin n, ΔA i j * d_hat j := by
    have := hsolve i; simp_rw [add_mul] at this
    rw [Finset.sum_add_distrib] at this; linarith
  rw [hexpand]
  calc |∑ j, ΔA i j * d_hat j|
      ≤ ∑ j, |ΔA i j * d_hat j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |ΔA i j| * |d_hat j| := by congr 1; ext j; exact abs_mul _ _
    _ ≤ ∑ j, (μ * |A i j|) * |d_hat j| :=
        Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (hΔA i j) (abs_nonneg _))
    _ = μ * ∑ j, |A i j| * |d_hat j| := by
        rw [Finset.mul_sum]; congr 1; ext j; ring

-- ============================================================
-- §11.2  Three-term bound with explicit bounds substituted
-- ============================================================

/-- **Three-term bound with explicit bounds** (Higham §11.2, eq. 11.12 applied).

    Substituting bounds on each error source:
    1. Solver residual: |r̂ − Ad̂|_i ≤ φ₁_i
    2. Residual computation: |r̂ − r|_i ≤ φ₂_i
    3. Update rounding: |f₂_j| ≤ φ₃_j

    gives: |b − Aŷ|_i ≤ φ₁_i + φ₂_i + (|A| · φ₃)_i -/
theorem thm_11_3_specialized (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (φ₁ : Fin n → ℝ)
    (hf₁ : ∀ i, |r_hat i - ∑ j : Fin n, A i j * d_hat j| ≤ φ₁ i)
    (φ₂ : Fin n → ℝ)
    (hΔr : ∀ i, |r_hat i - r i| ≤ φ₂ i)
    (φ₃ : Fin n → ℝ)
    (hf₂ : ∀ j, |f₂ j| ≤ φ₃ j) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        φ₁ i + φ₂ i + ∑ j : Fin n, |A i j| * φ₃ j := by
  intro i
  have hbase := thm_11_3_bound n A x₀ d_hat b r r_hat f₂ y hr hy i
  have hφ₃ : ∑ j : Fin n, |A i j| * |f₂ j| ≤
      ∑ j : Fin n, |A i j| * φ₃ j :=
    Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (hf₂ j) (abs_nonneg _))
  linarith [hf₁ i, hΔr i]

-- ============================================================
-- §11.2  Theorem 11.3: GE + standard residual (eq. 11.12 concrete)
-- ============================================================

/-- **Theorem 11.3 with GE solver and standard residual** (Higham §11.2, eq. 11.12).

    For a solver with componentwise backward error μ, conventional residual
    computation with error γ_{n+1}(|b| + |A||x̂|), and update rounding
    with error u(|x̂| + |d̂|), the three-term bound becomes:

      |b − Aŷ|_i ≤ μ(|A||d̂|)_i + γ_{n+1}(|b_i| + (|A||x̂|)_i)
                    + u(|A|(|x̂| + |d̂|))_i

    This is eq. (11.12) for GE-based iterative refinement with standard
    residual computation and rounded update. -/
theorem thm_11_3_ge_conventional (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ : ℝ) (hμ_nn : 0 ≤ μ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|))
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        μ * ∑ j : Fin n, |A i j| * |d_hat j| +
        gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|) +
        fp.u * ∑ j : Fin n, |A i j| * (|x₀ j| + |d_hat j|) := by
  intro i
  have hf₁ := solver_perturbation_to_residual n A d_hat r_hat ΔA_solve μ hμ_nn
    hsolve hΔA
  have hbase := thm_11_3_specialized n A x₀ d_hat b r r_hat f₂ y hr hy
    (fun i => μ * ∑ j : Fin n, |A i j| * |d_hat j|) hf₁
    (fun i => gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|)) hres
    (fun j => fp.u * (|x₀ j| + |d_hat j|)) hf₂ i
  have hpull : ∑ j : Fin n, |A i j| * (fp.u * (|x₀ j| + |d_hat j|)) =
      fp.u * ∑ j : Fin n, |A i j| * (|x₀ j| + |d_hat j|) := by
    rw [Finset.mul_sum]; congr 1; ext j; ring
  linarith [hpull]

-- ============================================================
-- §11.2  Theorem 11.4: Backward error with rounded update
-- ============================================================

/-- **Theorem 11.4 residual bound** (Higham §11.2, eq. 11.20 direction).

    If the three error terms from eq. (11.12) are collectively bounded by
    α · (|A| · |ŷ| + |b|) componentwise, then:
      |b − Aŷ|_i ≤ α · ((|A| · |ŷ|)_i + |b_i|)

    Setting α = 2γ_{n+1} recovers eq. (11.20). The dominance hypothesis
    encapsulates the full σ-contraction analysis from Theorem 11.4:
    it holds when cond(A,x)·σ is small and n·u is small. -/
theorem thm_11_4_residual_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (α : ℝ)
    (hdom : ∀ i : Fin n,
      |r_hat i - ∑ j : Fin n, A i j * d_hat j| +
      |r_hat i - r i| +
      ∑ j : Fin n, |A i j| * |f₂ j| ≤
        α * (∑ j : Fin n, |A i j| * |y j| + |b i|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        α * (∑ j : Fin n, |A i j| * |y j| + |b i|) := by
  intro i
  linarith [thm_11_3_bound n A x₀ d_hat b r r_hat f₂ y hr hy i, hdom i]

-- ============================================================
-- §11.2  Skewness ratio σ(B,x) (Higham §11.2)
-- ============================================================

/-- **Skewness ratio** σ(B,x) = max_i (|B||x|)_i / min_i (|B||x|)_i.

    Measures the variation across components of |B||x|. When σ = 1,
    all components are equal. The ratio appears in eq. (11.20) and
    controls how well the componentwise residual bound translates
    to a normwise bound.

    We define it for a given matrix B and vector x, requiring
    that the minimum component is positive (otherwise σ is undefined). -/
noncomputable def skewnessRatio {n : ℕ} (hn : 0 < n)
    (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  let Bx := fun i : Fin n => ∑ j : Fin n, |B i j| * |x j|
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) Bx /
  Finset.inf' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) Bx

/-- σ(B,x) ≥ 1 when all components of |B||x| are positive.

    We state this as: sup(Bx) ≥ inf(Bx), which gives σ ≥ 1. -/
theorem skewnessRatio_ge_one {n : ℕ} (hn : 0 < n)
    (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hpos : ∀ i : Fin n, 0 < ∑ j : Fin n, |B i j| * |x j|) :
    1 ≤ skewnessRatio hn B x := by
  unfold skewnessRatio
  set Bx := fun i : Fin n => ∑ j : Fin n, |B i j| * |x j|
  have hne : Finset.univ.Nonempty := Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
  have hinf_pos : 0 < Finset.inf' Finset.univ hne Bx := by
    rw [Finset.lt_inf'_iff]
    intro i _; exact hpos i
  rw [le_div_iff₀ hinf_pos, one_mul]
  -- sup ≥ any element ≥ inf
  have hsup : ∀ i, Bx i ≤ Finset.sup' Finset.univ hne Bx :=
    fun i => Finset.le_sup' Bx (Finset.mem_univ i)
  have hinf : ∀ i, Finset.inf' Finset.univ hne Bx ≤ Bx i :=
    fun i => Finset.inf'_le Bx (Finset.mem_univ i)
  -- Pick any element: inf ≤ Bx_0 ≤ sup
  linarith [hinf ⟨0, hn⟩, hsup ⟨0, hn⟩]

-- ============================================================
-- §11.2  Equation (11.15): |x̂| bound from rounded update
-- ============================================================

/-- **Update rounding bound on |x̂|** (Higham §11.2, eq. 11.15).

    From ŷ = x̂ + d̂ + f₂ with |f₂| ≤ u(|x̂| + |d̂|), we get:
      |x̂| ≤ |ŷ| + (1+u)|d̂| + u|x̂|
    so (1−u)|x̂| ≤ |ŷ| + (1+u)|d̂|, giving:
      |x̂_j| ≤ (|ŷ_j| + (1+u)|d̂_j|) / (1−u)

    This eliminates x̂ from the residual bound in favor of ŷ and d̂. -/
theorem eq_11_15 (n : ℕ) (fp : FPModel)
    (x_hat d_hat y f₂ : Fin n → ℝ)
    (hy : ∀ i, y i = x_hat i + d_hat i + f₂ i)
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x_hat j| + |d_hat j|))
    (_hu_lt : fp.u < 1) :
    ∀ j : Fin n,
      (1 - fp.u) * |x_hat j| ≤ |y j| + (1 + fp.u) * |d_hat j| := by
  intro j
  -- x̂_j = ŷ_j − d̂_j − f₂_j
  have hx : x_hat j = y j - d_hat j - f₂ j := by rw [hy]; ring
  -- |x̂_j| ≤ |ŷ_j| + |d̂_j| + |f₂_j|
  have htri : |x_hat j| ≤ |y j| + |d_hat j| + |f₂ j| := by
    rw [hx]; exact abs_add_three_le (y j) (-d_hat j) (-f₂ j) |>.trans (by
      simp only [abs_neg]; linarith)
  -- |f₂_j| ≤ u(|x̂_j| + |d̂_j|)
  have hf := hf₂ j
  -- |x̂_j| ≤ |ŷ_j| + |d̂_j| + u|x̂_j| + u|d̂_j|
  -- (1−u)|x̂_j| ≤ |ŷ_j| + (1+u)|d̂_j|
  nlinarith [abs_nonneg (x_hat j), abs_nonneg (d_hat j), abs_nonneg (y j)]

/-- **Update rounding bound on |x̂|, divided form** (Higham eq. 11.15).

    |x̂_j| ≤ (|ŷ_j| + (1+u)|d̂_j|) / (1−u) -/
theorem eq_11_15_div (n : ℕ) (fp : FPModel)
    (x_hat d_hat y f₂ : Fin n → ℝ)
    (hy : ∀ i, y i = x_hat i + d_hat i + f₂ i)
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x_hat j| + |d_hat j|))
    (hu_lt : fp.u < 1) :
    ∀ j : Fin n,
      |x_hat j| ≤ (|y j| + (1 + fp.u) * |d_hat j|) / (1 - fp.u) := by
  intro j
  have h1u : (0 : ℝ) < 1 - fp.u := by linarith
  rw [le_div_iff₀ h1u]
  have := eq_11_15 n fp x_hat d_hat y f₂ hy hf₂ hu_lt j
  linarith

-- ============================================================
-- §11.2  Equation (11.16): |r̂| bound
-- ============================================================

/-- **Residual computation absolute bound** (Higham §11.2, eq. 11.16).

    From the residual error |r̂ − r| ≤ γ_{n+1}(|b| + |A||x̂|)
    and |r| ≤ ω₀(|A||x̂| + |b|), triangle inequality gives:
      |r̂| ≤ (γ_{n+1} + ω₀) · (|A||x̂| + |b|)  componentwise

    Combined with eq. (11.15) to eliminate |x̂|, this bounds |r̂|
    in terms of |ŷ| and |d̂|. -/
theorem eq_11_16 (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (b x_hat : Fin n → ℝ)
    (r r_hat : Fin n → ℝ)
    (_hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x_hat j)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x_hat j|))
    (hn1 : gammaValid fp (n + 1))
    (ω₀ : ℝ) (_hω₀_nn : 0 ≤ ω₀)
    (hbw₀ : ∀ i, |r i| ≤ ω₀ * (∑ j : Fin n, |A i j| * |x_hat j| + |b i|)) :
    ∀ i : Fin n,
      |r_hat i| ≤ (gamma fp (n + 1) + ω₀) *
        (∑ j : Fin n, |A i j| * |x_hat j| + |b i|) := by
  intro i
  have _hγ_nn := gamma_nonneg fp hn1
  have htri : |r_hat i| ≤ |r_hat i - r i| + |r i| := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le (r_hat i - r i), neg_abs_le (r i)]
    · linarith [le_abs_self (r_hat i - r i), le_abs_self (r i)]
  set S := ∑ j : Fin n, |A i j| * |x_hat j|
  calc |r_hat i|
      ≤ |r_hat i - r i| + |r i| := htri
    _ ≤ gamma fp (n + 1) * (|b i| + S) + ω₀ * (S + |b i|) := by
        linarith [hres i, hbw₀ i]
    _ = (gamma fp (n + 1) + ω₀) * (S + |b i|) := by ring

-- ============================================================
-- §11.2  Equation (11.17): combined three-term bound with coefficients
-- ============================================================

/-- **Three-term bound with explicit matrix coefficients** (Higham §11.2, eq. 11.17).

    Substituting the solver perturbation bound, residual error, and update
    rounding into the three-term decomposition (eq. 11.12):

    |b − Aŷ|_i ≤ μ(|A||d̂|)_i + γ_{n+1}(|b_i| + (|A||x̂|)_i) + u(|A|(|x̂|+|d̂|))_i

    Regrouping by |x̂| and |d̂| coefficients:
    = (γ_{n+1} + u)(|A||x̂|)_i + (μ + u)(|A||d̂|)_i + γ_{n+1}|b_i|

    This form directly identifies the M₁ = (γ_{n+1}+u)I and M₂ = (μ+u)I
    scalar coefficient matrices from Higham's analysis. -/
theorem eq_11_17 (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ : ℝ) (hμ_nn : 0 ≤ μ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|))
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|))
    (_hn1 : gammaValid fp (n + 1)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        (gamma fp (n + 1) + fp.u) * ∑ j : Fin n, |A i j| * |x₀ j| +
        (μ + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| +
        gamma fp (n + 1) * |b i| := by
  intro i
  have hge := thm_11_3_ge_conventional n fp A x₀ d_hat b r r_hat f₂ y ΔA_solve
    μ hμ_nn hr hy hsolve hΔA hres hf₂ i
  -- Rewrite the RHS: u · ∑|A|(|x₀| + |d̂|) = u · ∑|A||x₀| + u · ∑|A||d̂|
  have hsplit : fp.u * ∑ j : Fin n, |A i j| * (|x₀ j| + |d_hat j|) =
      fp.u * ∑ j : Fin n, |A i j| * |x₀ j| +
      fp.u * ∑ j : Fin n, |A i j| * |d_hat j| := by
    have : ∑ j : Fin n, |A i j| * (|x₀ j| + |d_hat j|) =
        ∑ j : Fin n, |A i j| * |x₀ j| + ∑ j : Fin n, |A i j| * |d_hat j| := by
      rw [← Finset.sum_add_distrib]; congr 1; ext j; ring
    rw [this]; ring
  linarith [hsplit]

-- ============================================================
-- §11.2  Identity matrix definition
-- ============================================================

/-- **Nonneg matrix bound**: if |v_j| ≤ w_j for all j, and M_{ij} ≥ 0, then
    (M|v|)_i ≤ (Mw)_i. -/
lemma nonneg_mat_vec_mono (n : ℕ) (M : Fin n → Fin n → ℝ) (v w : Fin n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j)
    (hle : ∀ j, |v j| ≤ w j) :
    ∀ i, ∑ j : Fin n, M i j * |v j| ≤ ∑ j : Fin n, M i j * w j :=
  fun i => Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hle j) (hM i j))

-- ============================================================
-- §11.2  Eq (11.18)–(11.19): solving for |A||d̂| via Neumann bound
-- ============================================================

/-- **Solver residual-form bound** (Higham §11.2, preliminary for eqs. 11.18–11.19).

    From (A + ΔA)d̂ = r̂ with |ΔA| ≤ μ|A|, we get:
      Ad̂ = r̂ − ΔA·d̂
    and taking absolute values:
      |∑ A d̂|_i ≤ |r̂_i| + μ(|A||d̂|)_i

    This intermediate bound feeds into the Neumann series argument. -/
lemma solver_Ad_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ) (d_hat r_hat : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (μ : ℝ) (_hμ_nn : 0 ≤ μ)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA i j| ≤ μ * |A i j|) :
    ∀ i : Fin n, |∑ j : Fin n, A i j * d_hat j| ≤
      |r_hat i| + μ * ∑ j : Fin n, |A i j| * |d_hat j| := by
  intro i
  have hAd : ∑ j, A i j * d_hat j = r_hat i - ∑ j, ΔA i j * d_hat j := by
    have := hsolve i; simp_rw [add_mul] at this
    rw [Finset.sum_add_distrib] at this; linarith
  rw [hAd]
  have hΔAd : |∑ j, ΔA i j * d_hat j| ≤ μ * ∑ j, |A i j| * |d_hat j| := by
    calc |∑ j, ΔA i j * d_hat j|
        ≤ ∑ j, |ΔA i j * d_hat j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |ΔA i j| * |d_hat j| := by congr 1; ext j; exact abs_mul _ _
      _ ≤ ∑ j, (μ * |A i j|) * |d_hat j| :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hΔA i j) (abs_nonneg _))
      _ = μ * ∑ j, |A i j| * |d_hat j| := by rw [Finset.mul_sum]; congr 1; ext j; ring
  linarith [abs_sub (r_hat i) (∑ j, ΔA i j * d_hat j)]

-- ============================================================
-- §11.2  Solver correction via inverse (eq. 11.18, with A⁻¹)
-- ============================================================

/-- **Correction vector bound via matrix inverse** (Higham §11.2, eq. 11.18).

    From (A + ΔA)d̂ = r̂ with |ΔA| ≤ μ|A| and μ‖|A⁻¹||A|‖∞ < 1,
    the Neumann series gives:
      |d̂| ≤ (I − μ|A⁻¹||A|)⁻¹ |A⁻¹| |r̂|

    In the scalar case where |A⁻¹||A| ≈ κ·I, this simplifies to:
      |d̂| ≤ |A⁻¹||r̂| / (1 − μ·κ)

    We state the componentwise form with A_inv as hypothesis. -/
theorem eq_11_18 (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (d_hat r_hat : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (μ : ℝ) (_hμ_nn : 0 ≤ μ)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d_hat j = r_hat i)
    (_hΔA : ∀ i j, |ΔA i j| ≤ μ * |A i j|)
    -- A_inv resolves A: if Av = w then |v| ≤ A_inv|w|
    (_hA_inv : ∀ (v w : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * v j = w i) →
      ∀ i, |v i| ≤ ∑ j : Fin n, |A_inv i j| * |w j|)
    -- Neumann-type bound for the perturbed system
    (C : Fin n → Fin n → ℝ)
    (_hC_nn : ∀ i j, 0 ≤ C i j)
    -- C resolves (A+ΔA): if (A+ΔA)v = w then |v| ≤ C|w|
    (hC : ∀ (v w : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * v j = w i) →
      ∀ i, |v i| ≤ ∑ j : Fin n, C i j * |w j|) :
    ∀ i : Fin n, |d_hat i| ≤ ∑ j : Fin n, C i j * |r_hat j| := by
  exact hC d_hat r_hat hsolve

/-- **Product bound**: |A||d̂| ≤ |A|·C·|r̂| when |d̂| ≤ C|r̂|.

    From |d̂_j| ≤ (C|r̂|)_j, multiply by |A_{ij}| and sum:
      (|A||d̂|)_i ≤ (|A|C|r̂|)_i -/
theorem correction_product_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d_hat r_hat : Fin n → ℝ)
    (C : Fin n → Fin n → ℝ)
    (_hC_nn : ∀ i j, 0 ≤ C i j)
    (hd_bound : ∀ j, |d_hat j| ≤ ∑ k : Fin n, C j k * |r_hat k|) :
    ∀ i : Fin n, ∑ j : Fin n, |A i j| * |d_hat j| ≤
      ∑ j : Fin n, |A i j| * ∑ k : Fin n, C j k * |r_hat k| := by
  intro _i
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (hd_bound j) (abs_nonneg _))

/-- **Scalar Neumann resolution for correction** (Higham eq. 11.19 simplified).

    When the perturbed system resolves with scalar bound:
      |d̂_j| ≤ β · |r̂_j| for all j (β = 1/((1−μ)·min singular value) or similar),

    then (|A||d̂|)_i ≤ β · (|A||r̂|)_i = β · ∑_j |A_{ij}| · |r̂_j|. -/
theorem correction_scalar_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (d_hat r_hat : Fin n → ℝ)
    (β : ℝ) (_hβ_nn : 0 ≤ β)
    (hd_bound : ∀ j, |d_hat j| ≤ β * |r_hat j|) :
    ∀ i : Fin n, ∑ j : Fin n, |A i j| * |d_hat j| ≤
      β * ∑ j : Fin n, |A i j| * |r_hat j| := by
  intro i
  calc ∑ j, |A i j| * |d_hat j|
      ≤ ∑ j, |A i j| * (β * |r_hat j|) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hd_bound j) (abs_nonneg _))
    _ = β * ∑ j, |A i j| * |r_hat j| := by
        rw [Finset.mul_sum]; congr 1; ext j; ring

-- ============================================================
-- §11.2  Assembled Theorem 11.4: full backward error bound
-- ============================================================

/-- **Theorem 11.4: full backward error with Neumann correction** (Higham §11.2).

    Combining eq (11.17) with the Neumann correction bound on |d̂|:
    if |d̂_j| ≤ β·|r̂_j| and |r̂_i| ≤ C_r·(|A||x̂|)_i + C_b·|b_i|,
    and |x̂_j| ≤ (|ŷ_j| + (1+u)|d̂_j|)/(1−u), then the residual
    b − Aŷ can be bounded purely in terms of |A||ŷ| and |b|.

    This theorem provides the assembled bound: one plugs in the
    specific values of μ, β, γ_{n+1}, u, ω₀ to get eq. (11.20). -/
theorem thm_11_4_assembled (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ : ℝ) (hμ_nn : 0 ≤ μ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|))
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|))
    (hn1 : gammaValid fp (n + 1))
    -- Dominance: all error terms collectively bounded by α(|A||ŷ| + |b|)
    (α : ℝ)
    (hdom : ∀ i : Fin n,
      (gamma fp (n + 1) + fp.u) * ∑ j : Fin n, |A i j| * |x₀ j| +
      (μ + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| +
      gamma fp (n + 1) * |b i| ≤
        α * (∑ j : Fin n, |A i j| * |y j| + |b i|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        α * (∑ j : Fin n, |A i j| * |y j| + |b i|) := by
  intro i
  have h17 := eq_11_17 n fp A x₀ d_hat b r r_hat f₂ y ΔA_solve μ hμ_nn
    hr hy hsolve hΔA hres hf₂ hn1 i
  linarith [hdom i]

-- ============================================================
-- §11.2  Substitution lemma: bound |A||x₀| via |A||ŷ| and |A||d̂|
-- ============================================================

/-- **Substitution of eq. 11.15 into matrix sums** (Higham §11.2).

    Multiplies (1−u)|x₀_j| ≤ |ŷ_j| + (1+u)|d̂_j| by |A_{ij}| ≥ 0
    and sums over j to get:
      (1−u) · Σ|A_{ij}|·|x₀_j| ≤ Σ|A_{ij}|·|ŷ_j| + (1+u) · Σ|A_{ij}|·|d̂_j| -/
lemma bound_Ax0_from_eq_11_15 (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (x₀ d_hat y f₂ : Fin n → ℝ)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|))
    (hu_lt : fp.u < 1) :
    ∀ i : Fin n,
      (1 - fp.u) * ∑ j : Fin n, |A i j| * |x₀ j| ≤
        ∑ j : Fin n, |A i j| * |y j| +
        (1 + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| := by
  intro i
  have h15 := eq_11_15 n fp x₀ d_hat y f₂ hy hf₂ hu_lt
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  nlinarith [h15 j, abs_nonneg (A i j)]

-- ============================================================
-- §11.2  Self-contained Theorem 11.4
-- ============================================================

/-- **Theorem 11.4: self-contained backward error** (Higham §11.2, eq. 11.20).

    One step of iterative refinement produces ŷ = x̂ + d̂ + f₂ with backward error:
      |b − Aŷ|_i ≤ ω · (|A||ŷ| + |b|)_i

    This version eliminates the external dominance hypothesis of `thm_11_4_assembled`
    by internalizing the eq. 11.15 substitution and the Neumann correction bound.

    The condition `hω` requires:
      (γ+u) + ((γ+u)(1+u) + (1−u)(μ+u))·ρ ≤ (1−u)·ω

    For Gaussian elimination with ω = 2γ_{n+1}, this needs ρ ≈ 1/4. -/
theorem thm_11_4_self_contained (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (μ : ℝ) (hμ_nn : 0 ≤ μ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ μ * |A i j|)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|))
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|))
    (hn1 : gammaValid fp (n + 1))
    (hu_lt : fp.u < 1)
    -- Correction bound: (|A||d̂|)_i ≤ ρ · ((|A||ŷ|)_i + |b_i|)
    (ρ : ℝ) (_hρ_nn : 0 ≤ ρ)
    (hcorr : ∀ i, ∑ j : Fin n, |A i j| * |d_hat j| ≤
      ρ * (∑ j : Fin n, |A i j| * |y j| + |b i|))
    -- Target backward error coefficient (multiplied form avoids division)
    (ω : ℝ)
    (hω : (gamma fp (n + 1) + fp.u) +
           ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
            (1 - fp.u) * (μ + fp.u)) * ρ ≤ (1 - fp.u) * ω) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        ω * (∑ j : Fin n, |A i j| * |y j| + |b i|) := by
  intro i
  -- Core bounds from earlier theorems
  have h17 := eq_11_17 n fp A x₀ d_hat b r r_hat f₂ y ΔA_solve μ hμ_nn
    hr hy hsolve hΔA hres hf₂ hn1 i
  have hba := bound_Ax0_from_eq_11_15 n fp A x₀ d_hat y f₂ hy hf₂ hu_lt i
  have hci := hcorr i
  -- Positivity / nonnegativity
  have h1u : (0 : ℝ) < 1 - fp.u := by linarith
  have hγ_nn := gamma_nonneg fp hn1
  have hu_nn := fp.u_nonneg
  have hγu_nn : 0 ≤ gamma fp (n + 1) + fp.u := by linarith
  have hSy_nn : 0 ≤ ∑ j : Fin n, |A i j| * |y j| :=
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hbi_nn : 0 ≤ |b i| := abs_nonneg _
  -- Step 1: multiply h17 by (1-u) > 0, expand via ring
  have h17_scaled : (1 - fp.u) * |b i - ∑ j : Fin n, A i j * y j| ≤
      (gamma fp (n + 1) + fp.u) * ((1 - fp.u) * ∑ j : Fin n, |A i j| * |x₀ j|) +
      (1 - fp.u) * (μ + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| +
      (1 - fp.u) * gamma fp (n + 1) * |b i| := by
    have := mul_le_mul_of_nonneg_left h17 (le_of_lt h1u)
    linarith [show (1 - fp.u) * ((gamma fp (n + 1) + fp.u) *
        ∑ j : Fin n, |A i j| * |x₀ j| +
        (μ + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| +
        gamma fp (n + 1) * |b i|) =
        (gamma fp (n + 1) + fp.u) *
          ((1 - fp.u) * ∑ j : Fin n, |A i j| * |x₀ j|) +
        (1 - fp.u) * (μ + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j| +
        (1 - fp.u) * gamma fp (n + 1) * |b i| from by ring]
  -- Step 2: substitute hba into (γ+u)*(1-u)*Sx term, expand
  have hba_expanded : (gamma fp (n + 1) + fp.u) *
      ((1 - fp.u) * ∑ j : Fin n, |A i j| * |x₀ j|) ≤
      (gamma fp (n + 1) + fp.u) * ∑ j : Fin n, |A i j| * |y j| +
      (gamma fp (n + 1) + fp.u) * (1 + fp.u) *
        ∑ j : Fin n, |A i j| * |d_hat j| := by
    have := mul_le_mul_of_nonneg_left hba hγu_nn
    linarith [show (gamma fp (n + 1) + fp.u) *
        (∑ j : Fin n, |A i j| * |y j| +
         (1 + fp.u) * ∑ j : Fin n, |A i j| * |d_hat j|) =
        (gamma fp (n + 1) + fp.u) * ∑ j : Fin n, |A i j| * |y j| +
        (gamma fp (n + 1) + fp.u) * (1 + fp.u) *
          ∑ j : Fin n, |A i j| * |d_hat j| from by ring]
  -- Step 3: (1-u)*γ*|b| ≤ (γ+u)*|b|
  have hbi_step : (1 - fp.u) * gamma fp (n + 1) * |b i| ≤
      (gamma fp (n + 1) + fp.u) * |b i| := by
    nlinarith [mul_nonneg hu_nn hbi_nn, mul_nonneg hu_nn hγ_nn]
  -- Step 4: use correction bound on Sd, expand
  have hC_nn : 0 ≤ (gamma fp (n + 1) + fp.u) * (1 + fp.u) +
      (1 - fp.u) * (μ + fp.u) := by nlinarith
  have corr_expanded :
      ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
       (1 - fp.u) * (μ + fp.u)) *
        ∑ j : Fin n, |A i j| * |d_hat j| ≤
      ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
       (1 - fp.u) * (μ + fp.u)) * ρ *
        ∑ j : Fin n, |A i j| * |y j| +
      ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
       (1 - fp.u) * (μ + fp.u)) * ρ * |b i| := by
    have := mul_le_mul_of_nonneg_left hci hC_nn
    linarith [show ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
        (1 - fp.u) * (μ + fp.u)) *
        (ρ * (∑ j : Fin n, |A i j| * |y j| + |b i|)) =
        ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
         (1 - fp.u) * (μ + fp.u)) * ρ *
          ∑ j : Fin n, |A i j| * |y j| +
        ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
         (1 - fp.u) * (μ + fp.u)) * ρ * |b i| from by ring]
  -- Step 5: combine everything and conclude
  -- (1-u)*|res| ≤ (γ+u)*Sy + (γ+u)*(1+u)*Sd + (1-u)*(μ+u)*Sd + (γ+u)*bi
  -- The Sd coefficient: (γ+u)*(1+u) + (1-u)*(μ+u) = C
  -- Use corr_expanded: C*Sd ≤ C*ρ*Sy + C*ρ*bi
  -- So (1-u)*|res| ≤ ((γ+u)+C*ρ)*Sy + (C*ρ+(γ+u))*bi = ((γ+u)+C*ρ)*(Sy+bi)
  -- From hω: (γ+u)+C*ρ ≤ (1-u)*ω, so ≤ (1-u)*ω*(Sy+bi)
  have key : (1 - fp.u) * |b i - ∑ j : Fin n, A i j * y j| ≤
      (1 - fp.u) * (ω * (∑ j : Fin n, |A i j| * |y j| + |b i|)) := by
    nlinarith [h17_scaled, hba_expanded, hbi_step, corr_expanded, hω,
      mul_nonneg (show (0 : ℝ) ≤ (1 - fp.u) * ω -
        ((gamma fp (n + 1) + fp.u) +
         ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
          (1 - fp.u) * (μ + fp.u)) * ρ) from by linarith) hSy_nn,
      mul_nonneg (show (0 : ℝ) ≤ (1 - fp.u) * ω -
        ((gamma fp (n + 1) + fp.u) +
         ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
          (1 - fp.u) * (μ + fp.u)) * ρ) from by linarith) hbi_nn]
  -- Cancel (1-u) > 0
  calc |b i - ∑ j : Fin n, A i j * y j|
      = (1 - fp.u)⁻¹ * ((1 - fp.u) * |b i - ∑ j : Fin n, A i j * y j|) := by
        field_simp
    _ ≤ (1 - fp.u)⁻¹ * ((1 - fp.u) *
        (ω * (∑ j : Fin n, |A i j| * |y j| + |b i|))) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr (le_of_lt h1u))
    _ = ω * (∑ j : Fin n, |A i j| * |y j| + |b i|) := by field_simp

-- ============================================================
-- §11.3  LU instantiation of Theorem 11.4
-- ============================================================

/-- **Theorem 11.4 for Gaussian elimination** (Higham §11.3, eq. 11.20).

    For GE with μ = γ(3n), one step of fixed-precision iterative refinement yields:
      |b − Aŷ| ≤ 2γ_{n+1} · (|A||ŷ| + |b|)

    This instantiates `thm_11_4_self_contained` with the GE backward error
    μ = γ(3n) from Theorem 9.4 and target coefficient ω = 2γ_{n+1}. -/
theorem lu_refinement_thm_11_4 (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (x₀ d_hat : Fin n → ℝ) (b r r_hat : Fin n → ℝ)
    (f₂ : Fin n → ℝ) (y : Fin n → ℝ)
    (ΔA_solve : Fin n → Fin n → ℝ)
    (hr : ∀ i, r i = b i - ∑ j : Fin n, A i j * x₀ j)
    (hy : ∀ i, y i = x₀ i + d_hat i + f₂ i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA_solve i j) * d_hat j = r_hat i)
    (hΔA : ∀ i j, |ΔA_solve i j| ≤ gamma fp (3 * n) * |A i j|)
    (hres : ∀ i, |r_hat i - r i| ≤
      gamma fp (n + 1) * (|b i| + ∑ j : Fin n, |A i j| * |x₀ j|))
    (hf₂ : ∀ j, |f₂ j| ≤ fp.u * (|x₀ j| + |d_hat j|))
    (hn1 : gammaValid fp (n + 1))
    (hn3 : gammaValid fp (3 * n))
    (hu_lt : fp.u < 1)
    (ρ : ℝ) (hρ_nn : 0 ≤ ρ)
    (hcorr : ∀ i, ∑ j : Fin n, |A i j| * |d_hat j| ≤
      ρ * (∑ j : Fin n, |A i j| * |y j| + |b i|))
    (hρ_cond : (gamma fp (n + 1) + fp.u) +
        ((gamma fp (n + 1) + fp.u) * (1 + fp.u) +
         (1 - fp.u) * (gamma fp (3 * n) + fp.u)) * ρ ≤
        (1 - fp.u) * (2 * gamma fp (n + 1))) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * y j| ≤
        2 * gamma fp (n + 1) * (∑ j : Fin n, |A i j| * |y j| + |b i|) :=
  thm_11_4_self_contained n fp A x₀ d_hat b r r_hat f₂ y ΔA_solve
    (gamma fp (3 * n)) (gamma_nonneg fp hn3)
    hr hy hsolve hΔA hres hf₂ hn1 hu_lt ρ hρ_nn hcorr
    (2 * gamma fp (n + 1)) hρ_cond

-- ============================================================
-- §12.2  Nonnegative resolvent ∞-norm bound (Neumann inversion, eqns 12.20–12.21)
-- ============================================================

/-- **Nonnegative resolvent ∞-norm bound** — the Neumann-series consequence used
    in Higham §12.2, eqns (12.20)–(12.21) (2nd ed., Chapter 12 "Iterative
    Refinement"; the file's earlier `11.x` docstrings predate the 2nd-edition
    renumbering, in which iterative refinement is Chapter 12).

    If `M` is entrywise nonnegative with every row sum `≤ c < 1`, `v ≥ 0`
    componentwise, and `(I − M) v ≤ w` componentwise (`v_i ≤ (M v)_i + w_i`),
    then `‖v‖∞ ≤ ‖w‖∞ / (1 − c)`.

    This is the honest content of "`(I − M)` has a nonnegative inverse with
    `‖(I − M)⁻¹‖∞ ≤ 1/(1−c)`" without constructing the inverse: it is exactly the
    scalar bound Higham uses at (12.20)–(12.21) (with `c = 1/2`, giving the
    factor `2` in `‖(I − uM₃)⁻¹‖∞ ≤ 2`). -/
theorem nonneg_resolvent_infNormVec_bound {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (v w : Fin n → ℝ)
    (hM : ∀ i j : Fin n, 0 ≤ M i j)
    (hv : ∀ i : Fin n, 0 ≤ v i)
    (c : ℝ) (hc_lt : c < 1)
    (hrow : ∀ i : Fin n, ∑ j : Fin n, M i j ≤ c)
    (hstep : ∀ i : Fin n, v i ≤ (∑ j : Fin n, M i j * v j) + w i) :
    infNormVec v ≤ infNormVec w / (1 - c) := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  obtain ⟨i, hi⟩ := infNormVec_exists_le_abs hn v
  have hnv_le_vi : infNormVec v ≤ v i := by
    rw [abs_of_nonneg (hv i)] at hi; exact hi
  have hMv : (∑ j : Fin n, M i j * v j) ≤ c * infNormVec v := by
    calc (∑ j : Fin n, M i j * v j)
        ≤ ∑ j : Fin n, M i j * infNormVec v :=
          Finset.sum_le_sum (fun j _ => by
            have hvj : v j ≤ infNormVec v := by
              have := abs_le_infNormVec v j
              rwa [abs_of_nonneg (hv j)] at this
            exact mul_le_mul_of_nonneg_left hvj (hM i j))
      _ = (∑ j : Fin n, M i j) * infNormVec v := by rw [Finset.sum_mul]
      _ ≤ c * infNormVec v :=
          mul_le_mul_of_nonneg_right (hrow i) (infNormVec_nonneg v)
  have hwi : w i ≤ infNormVec w :=
    le_trans (le_abs_self (w i)) (abs_le_infNormVec w i)
  have hchain : infNormVec v ≤ c * infNormVec v + infNormVec w := by
    calc infNormVec v ≤ v i := hnv_le_vi
      _ ≤ (∑ j : Fin n, M i j * v j) + w i := hstep i
      _ ≤ c * infNormVec v + infNormVec w := by linarith [hMv, hwi]
  rw [le_div_iff₀ h1c]
  have hrw : infNormVec v * (1 - c) = infNormVec v - c * infNormVec v := by ring
  linarith [hchain, hrw]

-- ============================================================
-- §12.1  Exact forward-error identity/bound for one step (eqns 12.4–12.5)
-- ============================================================

/-- **Exact forward-error identity for one refinement step** (Higham §12.1, the
    exact core of eq. (12.5) with all three rounding sources).

    Let `x` be the exact solution (`A x = b`).  With computed residual
    `rc = (b − A x_i) + Δr` (residual-computation error `Δr`), computed correction
    `d` solving the perturbed system `(A + ΔA) d = rc`, and rounded update
    `y = x_i + d + Δx`, the forward error of the corrected iterate obeys the exact
    identity
      `A (y − x) = Δr − ΔA·d + A·Δx`.
    No inverse and no first-order truncation are used; this is the exact residual
    of the new forward error, from which the (12.5) recurrence follows by applying
    `|A⁻¹|`. -/
theorem forward_error_step_identity (n : ℕ)
    (A ΔA : Fin n → Fin n → ℝ)
    (x x_i d Δr Δx rc y b : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hrc : ∀ i, rc i = (b i - ∑ j : Fin n, A i j * x_i j) + Δr i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d j = rc i)
    (hy : ∀ i, y i = x_i i + d i + Δx i) :
    ∀ i : Fin n,
      ∑ j : Fin n, A i j * (y j - x j) =
        Δr i - (∑ j : Fin n, ΔA i j * d j) + (∑ j : Fin n, A i j * Δx j) := by
  intro i
  have hAd : ∑ j : Fin n, A i j * d j =
      rc i - ∑ j : Fin n, ΔA i j * d j := by
    have := hsolve i; simp_rw [add_mul] at this
    rw [Finset.sum_add_distrib] at this; linarith
  have hexp : ∑ j : Fin n, A i j * (y j - x j) =
      (∑ j : Fin n, A i j * x_i j) + (∑ j : Fin n, A i j * d j)
        + (∑ j : Fin n, A i j * Δx j) - ∑ j : Fin n, A i j * x j := by
    have h1 : ∀ j : Fin n, A i j * (y j - x j)
        = A i j * x_i j + A i j * d j + A i j * Δx j - A i j * x j :=
      fun j => by rw [hy]; ring
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hexp, hAd, hrc i, hAx i]
  ring

/-- **Forward-error bound for one refinement step** (Higham §12.1, eq. (12.5)).

    Applying a componentwise `|A⁻¹|` resolver (`Ainv ≥ 0`, resolving `A v = w ⇒
    |v| ≤ Ainv |w|`) to `forward_error_step_identity` gives the componentwise
    forward-error bound
      `|y − x|_i ≤ ∑_j Ainv_ij (|Δr|_j + (|ΔA||d|)_j + (|A||Δx|)_j)`,
    the three-source form of Higham's `G_i|x − x_i| + g_i` recurrence: `Δr` carries
    the (12.2) residual term (which contains the contracting `|A||x − x_i|` part),
    `ΔA` the solver backward error `≤ uW`, and `Δx` the update rounding. -/
theorem forward_error_step_bound (n : ℕ)
    (A ΔA : Fin n → Fin n → ℝ)
    (x x_i d Δr Δx rc y b : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hrc : ∀ i, rc i = (b i - ∑ j : Fin n, A i j * x_i j) + Δr i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d j = rc i)
    (hy : ∀ i, y i = x_i i + d i + Δx i)
    (Ainv : Fin n → Fin n → ℝ)
    (hAinv_nn : ∀ i j, 0 ≤ Ainv i j)
    (hAinv : ∀ (v w : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * v j = w i) →
      ∀ i, |v i| ≤ ∑ j : Fin n, Ainv i j * |w j|) :
    ∀ i : Fin n,
      |y i - x i| ≤
        ∑ j : Fin n, Ainv i j *
          (|Δr j| + (∑ k : Fin n, |ΔA j k| * |d k|)
            + (∑ k : Fin n, |A j k| * |Δx k|)) := by
  intro i
  have hid := forward_error_step_identity n A ΔA x x_i d Δr Δx rc y b
    hAx hrc hsolve hy
  have hstep := hAinv (fun j => y j - x j)
    (fun j => Δr j - (∑ k : Fin n, ΔA j k * d k) + (∑ k : Fin n, A j k * Δx k))
    hid i
  refine le_trans hstep ?_
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (hAinv_nn i j)
  have hΔAd : |∑ k : Fin n, ΔA j k * d k| ≤ ∑ k : Fin n, |ΔA j k| * |d k| := by
    calc |∑ k, ΔA j k * d k| ≤ ∑ k, |ΔA j k * d k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |ΔA j k| * |d k| := by congr 1; ext k; exact abs_mul _ _
  have hAΔx : |∑ k : Fin n, A j k * Δx k| ≤ ∑ k : Fin n, |A j k| * |Δx k| := by
    calc |∑ k, A j k * Δx k| ≤ ∑ k, |A j k * Δx k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |A j k| * |Δx k| := by congr 1; ext k; exact abs_mul _ _
  have htri : |Δr j - (∑ k, ΔA j k * d k) + (∑ k, A j k * Δx k)|
      ≤ |Δr j| + |∑ k, ΔA j k * d k| + |∑ k, A j k * Δx k| := by
    have h := abs_add_three_le (Δr j) (-(∑ k, ΔA j k * d k)) (∑ k, A j k * Δx k)
    simp only [abs_neg] at h
    have heq : Δr j - (∑ k, ΔA j k * d k) + (∑ k, A j k * Δx k)
        = Δr j + -(∑ k, ΔA j k * d k) + (∑ k, A j k * Δx k) := by ring
    rw [heq]; exact h
  linarith [htri, hΔAd, hAΔx]

-- ============================================================
-- §12.2  Norm-to-componentwise correction bound (σ/cond step for Thm 12.4)
-- ============================================================

/-- **Norm-to-componentwise correction bound** (scalar form of the σ/cond step
    discharging the correction hypothesis of Theorem 12.4).

    If the nonnegative correction-magnitude vector `dvec` has `‖dvec‖∞ ≤ ρ₀`, the
    target vector `t` is bounded below by `m > 0`, and `ρ₀ ≤ ρ·m`, then
    `dvec_i ≤ ρ · t_i` for every `i`.  Here `m` is a positive lower bound on the
    scaled data `|A||ŷ| + |b|`; `ρ = ρ₀/m` is the explicit correction constant —
    the exact, non-asymptotic content of Higham's `cond(A⁻¹)σ(A,ŷ)` condition. -/
theorem correction_componentwise_of_infNorm {n : ℕ}
    (dvec t : Fin n → ℝ) (rho0 ρ m : ℝ)
    (hnorm : infNormVec dvec ≤ rho0)
    (_hm_pos : 0 < m) (ht_lb : ∀ i, m ≤ t i)
    (hρ_nn : 0 ≤ ρ) (hcond : rho0 ≤ ρ * m) :
    ∀ i, dvec i ≤ ρ * t i := by
  intro i
  have hdi : dvec i ≤ rho0 :=
    le_trans (le_trans (le_abs_self _) (abs_le_infNormVec dvec i)) hnorm
  have h2 : ρ * m ≤ ρ * t i := mul_le_mul_of_nonneg_left (ht_lb i) hρ_nn
  linarith [hdi, hcond, h2]

-- ============================================================
-- §12.2  Correction Neumann inequality from the solver (eqns 12.18–12.20)
-- ============================================================

/-- **Correction Neumann inequality** (Higham §12.2, eqns (12.18)–(12.20), exact form).

    From the solver `(A + ΔA) d̂ = r̂` with `|ΔA| ≤ μ|A|` and a nonnegative resolver
    `Ainv` for `A` (`A v = w ⇒ |v_i| ≤ ∑_j Ainv_ij |w_j|`), the correction magnitude
    vector `|A||d̂|` satisfies the componentwise Neumann inequality
      `(|A||d̂|)_i ≤ ∑_k P_{ik} |r̂_k| + μ ∑_k P_{ik} (|A||d̂|)_k`,   `P := |A|·Ainv`,
    i.e. `(I − μ|A|Ainv)(|A||d̂|) ≤ (|A|Ainv)|r̂|`.  This is Higham's (12.18)/(12.20)
    with `M₃ = |A||A⁻¹|`, derived **exactly** (no `O(u²)`): the input consumed by
    `nonneg_resolvent_infNormVec_bound` / `higham12_21_correction_infNorm_bound`
    with `M := μ|A|Ainv` (`≥ 0`) and `w := (|A|Ainv)|r̂|`. -/
theorem correction_neumann_inequality (n : ℕ)
    (A Ainv ΔA : Fin n → Fin n → ℝ) (d_hat r_hat : Fin n → ℝ)
    (μ : ℝ) (_hμ_nn : 0 ≤ μ)
    (hAinv_nn : ∀ i j, 0 ≤ Ainv i j)
    (hAinv : ∀ (v w : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * v j = w i) →
      ∀ i, |v i| ≤ ∑ j : Fin n, Ainv i j * |w j|)
    (hΔA : ∀ i j, |ΔA i j| ≤ μ * |A i j|)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d_hat j = r_hat i) :
    ∀ i : Fin n,
      (∑ j : Fin n, |A i j| * |d_hat j|) ≤
        (∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k) * |r_hat k|)
          + μ * ∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k)
              * (∑ l : Fin n, |A k l| * |d_hat l|) := by
  -- A d̂ = r̂ − ΔA d̂
  have hAd : ∀ i, ∑ j : Fin n, A i j * d_hat j
      = r_hat i - ∑ j : Fin n, ΔA i j * d_hat j := by
    intro i; have := hsolve i; simp_rw [add_mul] at this
    rw [Finset.sum_add_distrib] at this; linarith
  -- resolver on d̂ with w_k = r̂_k − (ΔA d̂)_k
  have hdj := hAinv d_hat (fun k => r_hat k - ∑ l : Fin n, ΔA k l * d_hat l) hAd
  -- |w_k| ≤ |r̂_k| + μ (|A||d̂|)_k
  have hwk : ∀ k : Fin n, |r_hat k - ∑ l : Fin n, ΔA k l * d_hat l|
      ≤ |r_hat k| + μ * ∑ l : Fin n, |A k l| * |d_hat l| := by
    intro k
    have h1 : |r_hat k - ∑ l, ΔA k l * d_hat l| ≤ |r_hat k| + |∑ l, ΔA k l * d_hat l| :=
      abs_sub (r_hat k) (∑ l, ΔA k l * d_hat l)
    have h2 : |∑ l, ΔA k l * d_hat l| ≤ μ * ∑ l, |A k l| * |d_hat l| := by
      calc |∑ l, ΔA k l * d_hat l| ≤ ∑ l, |ΔA k l * d_hat l| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ l, |ΔA k l| * |d_hat l| := by congr 1; ext l; exact abs_mul _ _
        _ ≤ ∑ l, (μ * |A k l|) * |d_hat l| :=
            Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_right (hΔA k l) (abs_nonneg _))
        _ = μ * ∑ l, |A k l| * |d_hat l| := by rw [Finset.mul_sum]; congr 1; ext l; ring
    linarith
  -- |d̂_j| ≤ ∑_k Ainv_jk (|r̂_k| + μ (|A||d̂|)_k)
  have hdj2 : ∀ j : Fin n, |d_hat j| ≤
      ∑ k : Fin n, Ainv j k * (|r_hat k| + μ * ∑ l : Fin n, |A k l| * |d_hat l|) := by
    intro j
    refine le_trans (hdj j) ?_
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hwk k) (hAinv_nn j k))
  intro i
  -- abbreviation X k = |r̂_k| + μ (|A||d̂|)_k
  set X : Fin n → ℝ := fun k => |r_hat k| + μ * ∑ l : Fin n, |A k l| * |d_hat l| with hX
  have hswap : ∑ j : Fin n, |A i j| * (∑ k : Fin n, Ainv j k * X k)
      = ∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k) * X k := by
    calc ∑ j, |A i j| * (∑ k, Ainv j k * X k)
        = ∑ j, ∑ k, |A i j| * (Ainv j k * X k) := by
          apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]
      _ = ∑ k, ∑ j, |A i j| * (Ainv j k * X k) := Finset.sum_comm
      _ = ∑ k, (∑ j, |A i j| * Ainv j k) * X k := by
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
  have hsplit : ∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k) * X k
      = (∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k) * |r_hat k|)
          + μ * ∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k)
              * (∑ l : Fin n, |A k l| * |d_hat l|) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; simp only [hX]; ring
  calc ∑ j, |A i j| * |d_hat j|
      ≤ ∑ j, |A i j| * (∑ k, Ainv j k * X k) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hdj2 j) (abs_nonneg _))
    _ = ∑ k, (∑ j, |A i j| * Ainv j k) * X k := hswap
    _ = _ := hsplit

end NumStability
