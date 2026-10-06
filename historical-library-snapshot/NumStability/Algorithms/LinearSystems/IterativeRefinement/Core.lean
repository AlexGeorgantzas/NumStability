import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.MatVec
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Core

Retained R03 owner (reusable): every declaration stays at this exact path
under the frozen B0005 route; wave R03 adds this module docstring only.
-/


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
























































-- ============================================================
-- §11.2  Solver perturbation to residual form
-- ============================================================































-- ============================================================
-- §11.2  Three-term bound with explicit bounds substituted
-- ============================================================































-- ============================================================
-- §11.2  Theorem 11.3: GE + standard residual (eq. 11.12 concrete)
-- ============================================================










































-- ============================================================
-- §11.2  Theorem 11.4: Backward error with rounded update
-- ============================================================



























-- ============================================================
-- §11.2  Skewness ratio σ(B,x) (Higham §11.2)
-- ============================================================






































-- ============================================================
-- §11.2  Equation (11.15): |x̂| bound from rounded update
-- ============================================================













































-- ============================================================
-- §11.2  Equation (11.16): |r̂| bound
-- ============================================================


































-- ============================================================
-- §11.2  Equation (11.17): combined three-term bound with coefficients
-- ============================================================













































-- ============================================================
-- §11.2  Identity matrix definition
-- ============================================================









-- ============================================================
-- §11.2  Eq (11.18)–(11.19): solving for |A||d̂| via Neumann bound
-- ============================================================































-- ============================================================
-- §11.2  Solver correction via inverse (eq. 11.18, with A⁻¹)
-- ============================================================




































































-- ============================================================
-- §11.2  Assembled Theorem 11.4: full backward error bound
-- ============================================================







































-- ============================================================
-- §11.2  Substitution lemma: bound |A||x₀| via |A||ŷ| and |A||d̂|
-- ============================================================






















-- ============================================================
-- §11.2  Self-contained Theorem 11.4
-- ============================================================




































































































































-- ============================================================
-- §11.3  LU instantiation of Theorem 11.4
-- ============================================================






































-- ============================================================
-- §12.2  Nonnegative resolvent ∞-norm bound (Neumann inversion, eqns 12.20–12.21)
-- ============================================================















































-- ============================================================
-- §12.1  Exact forward-error identity/bound for one step (eqns 12.4–12.5)
-- ============================================================


























































































-- ============================================================
-- §12.2  Norm-to-componentwise correction bound (σ/cond step for Thm 12.4)
-- ============================================================





















-- ============================================================
-- §12.2  Correction Neumann inequality from the solver (eqns 12.18–12.20)
-- ============================================================











































































end NumStability
