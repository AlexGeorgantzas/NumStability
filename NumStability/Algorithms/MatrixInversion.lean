-- Algorithms/MatrixInversion.lean
--
-- Higham Chapter 14: Matrix Inversion.
-- §14.1: Ideal perturbation bounds for computed inverses.
-- §14.2: Triangular matrix inversion (Methods 1, 2, block variants).
-- §14.3: Full matrix inversion via LU factorization (Methods A, B, C, D).
--
-- The internally proved results derive residual/forward-error consequences
-- from explicit componentwise contracts.  Some higher-level algorithmic
-- kernels are exposed as abstract interfaces when their detailed loop error
-- analysis is not formalized in this module.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.RoundingProductBounds
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.HighamChapter8
import NumStability.Algorithms.HighamChapter9
import NumStability.Algorithms.LeastSquares.LSPerturbation

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §14.1  Δ-notation: product error bounds
-- ============================================================

/-- **Matrix product error bound** (Δ-notation, Higham §14.1).

    If Ĉ = fl(A₁ · A₂) then |Ĉ − A₁A₂| ≤ ε · (|A₁| · |A₂|).
    This predicate captures the general statement for any computed product. -/
def MatProdError (n : ℕ) (C_hat : Fin n → Fin n → ℝ)
    (C_exact : Fin n → Fin n → ℝ) (ε : ℝ)
    (absProduct : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, |C_hat i j - C_exact i j| ≤ ε * absProduct i j

/-- Componentwise matrix-product-shaped bounds imply an infinity-norm bound
    with the absolute product retained. -/
theorem higham14_infNorm_le_of_componentwise_abs_matmul_bound {n : ℕ}
    {R A B : Fin n → Fin n → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hR : ∀ i j : Fin n,
      |R i j| ≤ ε * ∑ k : Fin n, |A i k| * |B k j|) :
    infNorm R ≤
      ε * infNorm (matMul n (absMatrix n A) (absMatrix n B)) := by
  let M := matMul n (absMatrix n A) (absMatrix n B)
  have hM_nonneg : ∀ i j : Fin n, 0 ≤ M i j := by
    intro i j
    dsimp [M, matMul, absMatrix]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      ∑ j : Fin n, |R i j|
          ≤ ∑ j : Fin n, ε * M i j := by
            apply Finset.sum_le_sum
            intro j _
            simpa [M, matMul, absMatrix] using hR i j
      _ = ε * ∑ j : Fin n, M i j := by
            rw [Finset.mul_sum]
      _ = ε * ∑ j : Fin n, |M i j| := by
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            exact (abs_of_nonneg (hM_nonneg i j)).symm
      _ ≤ ε * infNorm M := by
            exact mul_le_mul_of_nonneg_left (row_sum_le_infNorm M i) hε
  · exact mul_nonneg hε (infNorm_nonneg M)

/-- Componentwise matrix-product-shaped bounds imply an infinity-norm bound
    in terms of the two ordinary infinity norms. -/
theorem higham14_infNorm_le_of_componentwise_matmul_bound {n : ℕ}
    (hn : 0 < n) {R A B : Fin n → Fin n → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hR : ∀ i j : Fin n,
      |R i j| ≤ ε * ∑ k : Fin n, |A i k| * |B k j|) :
    infNorm R ≤ ε * infNorm A * infNorm B := by
  have hbase :=
    higham14_infNorm_le_of_componentwise_abs_matmul_bound
      (n := n) (R := R) (A := A) (B := B) hε hR
  have hmul :
      infNorm (matMul n (absMatrix n A) (absMatrix n B)) ≤
        infNorm A * infNorm B := by
    simpa [infNorm_absMatrix hn A, infNorm_absMatrix hn B] using
      infNorm_matMul_le hn (absMatrix n A) (absMatrix n B)
  calc
    infNorm R ≤
        ε * infNorm (matMul n (absMatrix n A) (absMatrix n B)) := hbase
    _ ≤ ε * (infNorm A * infNorm B) :=
        mul_le_mul_of_nonneg_left hmul hε
    _ = ε * infNorm A * infNorm B := by ring

-- ============================================================
-- §14.1  Ideal perturbation bounds (eqs. 14.1–14.3)
-- ============================================================

/-- **Right residual of a computed inverse** (Higham eq. 14.1).

    If Y = (A + ΔA)⁻¹ with |ΔA| ≤ ε|A|, then AY − I = −ΔA · Y,
    so |AY − I| ≤ ε|A||Y|.

    We state the bound with |Y| rather than |A⁻¹| to avoid circularity;
    the first-order version |A⁻¹| + O(ε) follows from eq. 14.3. -/
theorem ideal_right_residual (n : ℕ)
    (A Y : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hY : ∀ i j, ∑ k : Fin n, (A i k + ΔA i k) * Y k j =
      if i = j then 1 else 0) :
    ∀ i j, |∑ k : Fin n, A i k * Y k j - if i = j then 1 else 0| ≤
      ε * ∑ k : Fin n, |A i k| * |Y k j| := by
  intro i j
  -- AY − I = (A+ΔA)Y − I − ΔAY = −ΔAY (since (A+ΔA)Y = I)
  -- So (AY − I)_{ij} = −∑_k ΔA_{ik} Y_{kj}
  have hAY : ∑ k : Fin n, A i k * Y k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔA i k * Y k j) := by
    have h := hY i j
    have hsplit : ∑ k : Fin n, A i k * Y k j + ∑ k : Fin n, ΔA i k * Y k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hAY, abs_neg]
  -- |∑_k ΔA_{ik} Y_{kj}| ≤ ∑_k |ΔA_{ik}| |Y_{kj}| ≤ ε ∑_k |A_{ik}| |Y_{kj}|
  calc |∑ k : Fin n, ΔA i k * Y k j|
      ≤ ∑ k : Fin n, |ΔA i k * Y k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔA i k| * |Y k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, (ε * |A i k|) * |Y k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔA i k) (abs_nonneg _)
    _ = ε * ∑ k : Fin n, |A i k| * |Y k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- **Left residual of a computed inverse** (Higham eq. 14.2).

    If Y = (A + ΔA)⁻¹ with |ΔA| ≤ ε|A|, then YA − I = −Y · ΔA,
    so |YA − I| ≤ ε|Y||A|. -/
theorem ideal_left_residual (n : ℕ)
    (A Y : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hY_left : ∀ i j, ∑ k : Fin n, Y i k * (A k j + ΔA k j) =
      if i = j then 1 else 0) :
    ∀ i j, |∑ k : Fin n, Y i k * A k j - if i = j then 1 else 0| ≤
      ε * ∑ k : Fin n, |Y i k| * |A k j| := by
  intro i j
  have hYA : ∑ k : Fin n, Y i k * A k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, Y i k * ΔA k j) := by
    have h := hY_left i j
    have hsplit : ∑ k : Fin n, Y i k * A k j + ∑ k : Fin n, Y i k * ΔA k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hYA, abs_neg]
  calc |∑ k : Fin n, Y i k * ΔA k j|
      ≤ ∑ k : Fin n, |Y i k * ΔA k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |Y i k| * |ΔA k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, |Y i k| * (ε * |A k j|) := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_left (hΔA k j) (abs_nonneg _)
    _ = ε * ∑ k : Fin n, |Y i k| * |A k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- **Forward error for a computed inverse** (Higham eq. 14.3).

    If Y = (A + ΔA)⁻¹ with |ΔA| ≤ ε|A|, and A_inv is the true inverse, then
    A⁻¹ − Y = A⁻¹ · ΔA · Y, so
    |A⁻¹ − Y| ≤ ε|A⁻¹||A||Y|.

    This is the componentwise first-order bound. Replacing |Y| by |A⁻¹| + O(ε²)
    gives the pure |A⁻¹||A||A⁻¹| form. -/
theorem ideal_forward_error (n : ℕ)
    (A A_inv Y : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hInv : IsLeftInverse n A A_inv)
    (_hRInv : IsRightInverse n A A_inv)
    (hY : ∀ i j, ∑ k : Fin n, (A i k + ΔA i k) * Y k j =
      if i = j then 1 else 0) :
    ∀ i j, |A_inv i j - Y i j| ≤
      ε * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ j|) := by
  intro i j
  -- A⁻¹ − Y = A⁻¹(AY − I) since A⁻¹·A = I gives A⁻¹ − Y = A⁻¹·(AY − I).
  -- More precisely: A⁻¹ − Y = A⁻¹ · (I − AY) ... wait, we need:
  -- From (A+ΔA)Y = I, we get AY = I − ΔA·Y.
  -- So A⁻¹ − Y: note A⁻¹ = A⁻¹·I = A⁻¹·(A+ΔA)·Y + A⁻¹·ΔA·Y ... no.
  -- Correctly: A⁻¹ − Y = A⁻¹ − (A+ΔA)⁻¹.
  -- Since (A+ΔA)Y = I, we have Y = (A+ΔA)⁻¹.
  -- A⁻¹ − Y = A⁻¹(I − A·Y) = A⁻¹(ΔA·Y) since AY = I − ΔA·Y.
  -- Wait: AY = (A+ΔA)Y − ΔA·Y = I − ΔA·Y, so I − AY = ΔA·Y.
  -- Hence A⁻¹ − Y = A⁻¹·(I − AY) is wrong dimensionally.
  -- Actually: from A·Y + ΔA·Y = I, we get A·Y = I − ΔA·Y.
  -- Multiply on left by A⁻¹: Y = A⁻¹ − A⁻¹·ΔA·Y.
  -- So A⁻¹ − Y = A⁻¹·ΔA·Y.
  -- Therefore (A⁻¹ − Y)_{ij} = ∑_{k₁} A⁻¹_{ik₁} (∑_{k₂} ΔA_{k₁k₂} Y_{k₂j}).
  have hDiff : A_inv i j - Y i j =
      ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j) := by
    -- From (A+ΔA)Y = I, expanding: AY + ΔAY = I
    -- Multiply by A⁻¹ on left: Y + A⁻¹·ΔA·Y = A⁻¹
    -- So A⁻¹(i,j) = Y(i,j) + (A⁻¹ΔAY)(i,j)
    have hAY_col : ∀ k₁ : Fin n,
        ∑ k₂ : Fin n, A k₁ k₂ * Y k₂ j + ∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j =
        (if k₁ = j then (1 : ℝ) else 0) := by
      intro k₁
      have h := hY k₁ j
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    -- A⁻¹(i,j) = ∑_{k₁} A⁻¹(i,k₁) · δ(k₁,j) = ∑_{k₁} A⁻¹(i,k₁) · (∑_{k₂} A(k₁,k₂)Y(k₂,j) + ∑_{k₂} ΔA(k₁,k₂)Y(k₂,j))
    have hAinv_ij : A_inv i j = ∑ k₁ : Fin n, A_inv i k₁ *
        (if k₁ = j then (1 : ℝ) else 0) := by
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    -- A⁻¹(i,j) = ∑_{k₁} A⁻¹(i,k₁) δ(k₁,j) from left inverse
    -- = Y(i,j) + (A⁻¹ΔAY)(i,j) by substituting δ = AY + ΔAY
    -- So A⁻¹(i,j) - Y(i,j) = (A⁻¹ΔAY)(i,j)
    -- Direct computation: A⁻¹·A·Y = Y (since A⁻¹A = I)
    have hAinvAY : ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, A k₁ k₂ * Y k₂ j) =
        Y i j := by
      -- (A⁻¹ · A · Y)(i,j) = (I · Y)(i,j) = Y(i,j)
      -- Unfold: ∑_{k₁} A⁻¹(i,k₁) · ∑_{k₂} A(k₁,k₂)Y(k₂,j)
      -- = ∑_{k₂} Y(k₂,j) · ∑_{k₁} A⁻¹(i,k₁)A(k₁,k₂) = ∑_{k₂} Y(k₂,j)·δ(i,k₂)
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      -- Goal: ∑ k₂, ∑ k₁, A_inv i k₁ * A k₁ k₂ * Y k₂ j = Y i j
      have : ∀ k₂ : Fin n,
          ∑ k₁ : Fin n, A_inv i k₁ * A k₁ k₂ * Y k₂ j =
          (∑ k₁ : Fin n, A_inv i k₁ * A k₁ k₂) * Y k₂ j := by
        intro k₂; rw [Finset.sum_mul]
      simp_rw [this]
      -- Use hInv: ∑ k, A_inv i k * A k k₂ = δ(i,k₂)
      have hIte : ∀ k₂ : Fin n,
          (∑ k₁ : Fin n, A_inv i k₁ * A k₁ k₂) * Y k₂ j =
          (if i = k₂ then (1 : ℝ) else 0) * Y k₂ j := by
        intro k₂; congr 1; exact hInv i k₂
      simp_rw [hIte]
      simp [Finset.mem_univ]
    -- From (A+ΔA)Y = I: for each k₁, ∑_k₂ A(k₁,k₂)Y(k₂,j) = δ(k₁,j) - ∑_k₂ ΔA(k₁,k₂)Y(k₂,j)
    -- So ∑_{k₁} A⁻¹(i,k₁) · δ(k₁,j) = Y(i,j) + ∑_{k₁} A⁻¹(i,k₁) · ∑_{k₂} ΔA(k₁,k₂)·Y(k₂,j)
    rw [hAinv_ij]
    -- LHS = ∑ A⁻¹(i,k₁) · (AY + ΔAY)(k₁,j) - Y(i,j)
    -- We rewrite each δ(k₁,j) using hAY_col
    have hRewrite : ∑ k₁ : Fin n, A_inv i k₁ * (if k₁ = j then (1 : ℝ) else 0) =
        ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, A k₁ k₂ * Y k₂ j) +
        ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k₁ _
      rw [← mul_add, ← hAY_col k₁]
    rw [hRewrite, hAinvAY]
    ring
  rw [hDiff]
  -- |∑_{k₁} A⁻¹(i,k₁) (∑_{k₂} ΔA(k₁,k₂) Y(k₂,j))| ≤ ∑ |A⁻¹| |ΔA| |Y|
  calc |∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j)|
      ≤ ∑ k₁ : Fin n, |A_inv i k₁ * (∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |A_inv i k₁| * |∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |A_inv i k₁| * (∑ k₂ : Fin n, |ΔA k₁ k₂| * |Y k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc |∑ k₂ : Fin n, ΔA k₁ k₂ * Y k₂ j|
            ≤ ∑ k₂ : Fin n, |ΔA k₁ k₂ * Y k₂ j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k₂ : Fin n, |ΔA k₁ k₂| * |Y k₂ j| := by
              apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |A_inv i k₁| * (∑ k₂ : Fin n, (ε * |A k₁ k₂|) * |Y k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum; intro k₂ _
        exact mul_le_mul_of_nonneg_right (hΔA k₁ k₂) (abs_nonneg _)
    _ = ε * ∑ k₁ : Fin n, |A_inv i k₁| * (∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k₁ _
        have : ∑ k₂ : Fin n, ε * |A k₁ k₂| * |Y k₂ j| =
            ε * ∑ k₂ : Fin n, |A k₁ k₂| * |Y k₂ j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k₂ _; ring
        rw [this]; ring

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

-- ============================================================
-- §14.1  Residual comparison: inversion vs GEPP
-- ============================================================

/-- **Residual bound for solving via matrix inversion** (Higham §14.1, p. 262).

    If X = A⁻¹ is formed exactly and the only rounding is in x̂ = fl(Xb),
    then the best possible residual bound is
      |b − Ax̂| ≤ γₙ|A||A⁻¹||b|.

    This is much worse than GEPP's |b − Ax̂| ≤ 2γₙ|L̂||Û||x̂|
    when A is ill-conditioned.

    We state the componentwise bound for each coordinate i. -/
theorem inversion_residual_bound (n : ℕ) (fp : FPModel)
    (A A_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hInv : IsRightInverse n A A_inv)
    (hn : gammaValid fp n) :
    let x_hat := fl_matVec fp n n A_inv b
    ∀ i, |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n *
        ∑ j : Fin n, |A i j| * (∑ k : Fin n, |A_inv j k| * |b k|) := by
  intro x_hat i
  -- x̂ = fl(A⁻¹b) satisfies backward error: x̂ = (A⁻¹ + ΔX)b with |ΔX| ≤ γₙ|A⁻¹|
  obtain ⟨ΔX, hΔX_bound, hΔX_eq⟩ := matVec_backward_error fp n n A_inv b hn
  -- b − Ax̂ = b − A(A⁻¹ + ΔX)b = b − (I + AΔX)b = −AΔXb
  -- since A · A⁻¹ = I by hInv
  change |b i - ∑ j : Fin n, A i j * fl_matVec fp n n A_inv b j| ≤ _
  have hRes : b i - ∑ j : Fin n, A i j * fl_matVec fp n n A_inv b j =
      -(∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)) := by
    -- x̂_j = ∑_k (A_inv j k + ΔX j k) * b k
    -- Ax̂ = A(A⁻¹+ΔX)b, so b − Ax̂ = b − A·A⁻¹·b − A·ΔX·b = −A·ΔX·b
    have hxhat : ∀ j : Fin n, fl_matVec fp n n A_inv b j =
        ∑ k : Fin n, (A_inv j k + ΔX j k) * b k := hΔX_eq
    -- Expand: ∑_j A_ij x̂_j = ∑_j A_ij ∑_k A_inv_jk b_k + ∑_j A_ij ∑_k ΔX_jk b_k
    have hExpand : ∑ j : Fin n, A i j * fl_matVec fp n n A_inv b j =
        ∑ j : Fin n, A i j * (∑ k : Fin n, A_inv j k * b k) +
        ∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [hxhat j, ← mul_add]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    -- First sum = (AA⁻¹b)_i = b_i
    have hFirst : ∑ j : Fin n, A i j * (∑ k : Fin n, A_inv j k * b k) = b i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have : ∀ k : Fin n,
          (∑ j : Fin n, A i j * A_inv j k) * b k =
          (if i = k then (1 : ℝ) else 0) * b k := by
        intro k; congr 1; exact hInv i k
      simp_rw [this]
      simp [Finset.mem_univ]
    rw [hExpand, hFirst]; ring
  rw [hRes, abs_neg]
  -- |∑_j A_ij (∑_k ΔX_jk b_k)| ≤ ∑_j |A_ij| ∑_k |ΔX_jk| |b_k| ≤ γₙ ∑ |A| |A⁻¹| |b|
  calc |∑ j : Fin n, A i j * (∑ k : Fin n, ΔX j k * b k)|
      ≤ ∑ j : Fin n, |A i j * (∑ k : Fin n, ΔX j k * b k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |A i j| * |∑ k : Fin n, ΔX j k * b k| := by
        apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |A i j| * (∑ k : Fin n, |ΔX j k| * |b k|) := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc |∑ k : Fin n, ΔX j k * b k|
            ≤ ∑ k : Fin n, |ΔX j k * b k| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k : Fin n, |ΔX j k| * |b k| := by
              apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |A i j| * (∑ k : Fin n, (gamma fp n * |A_inv j k|) * |b k|) := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔX_bound j k) (abs_nonneg _)
    _ = gamma fp n * ∑ j : Fin n, |A i j| * (∑ k : Fin n, |A_inv j k| * |b k|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        have : ∑ k : Fin n, (gamma fp n * |A_inv j k|) * |b k| =
            gamma fp n * ∑ k : Fin n, |A_inv j k| * |b k| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _; ring
        rw [this]; ring

-- ============================================================
-- §14.2  Triangular matrix inversion
-- ============================================================

-- §14.2.1  Method 1 (column-by-column forward substitution)

/-- **Method 1 right residual for triangular inversion** (Higham eq. 14.4).

    Method 1 computes L⁻¹ by solving Lx̂ⱼ = eⱼ for each column j.
    From Theorem 8.5 (forwardSub_backward_error), each column satisfies
    (L + ΔLⱼ)x̂ⱼ = eⱼ with |ΔLⱼ| ≤ γ(n)|L|.

    This gives the componentwise right residual:
      |LX̂ − I| ≤ γ(n)|L||X̂|. -/
theorem triInv_method1_right_residual (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n) :
    -- X̂ is computed column-by-column: column j = forwardSub(L, eⱼ)
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    -- For each column j: ∃ ΔLⱼ with |ΔLⱼ| ≤ γ(n)|L| and (L+ΔLⱼ)x̂ⱼ = eⱼ
    ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k : Fin n, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i : Fin n, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0 := by
  intro X_hat j
  exact forwardSub_backward_error fp n L (fun k => if k = j then 1 else 0) hL_diag hLT hn

/-- **Method 1 right residual — matrix form** (Higham eq. 14.4).

    Consequence: |LX̂ − I| ≤ γ(n)|L||X̂| componentwise. -/
theorem triInv_method1_right_residual_matrix (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
  intro X_hat i j
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ :=
    triInv_method1_right_residual n fp L hL_diag hLT hn j
  have hLX : ∑ k : Fin n, L i k * X_hat k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔL i k * X_hat k j) := by
    have h := hΔL_eq i
    have hsplit : ∑ k : Fin n, L i k * X_hat k j +
        ∑ k : Fin n, ΔL i k * X_hat k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hLX, abs_neg]
  calc |∑ k : Fin n, ΔL i k * X_hat k j|
      ≤ ∑ k : Fin n, |ΔL i k * X_hat k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔL i k| * |X_hat k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, (gamma fp n * |L i k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔL_bound i k) (abs_nonneg _)
    _ = gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- **Method 1 forward error** (Higham eq. 14.5).

    |X̂ − L⁻¹| ≤ γ(n)|L⁻¹||L||X̂|  (componentwise).

    Proof: From LX̂ = I + E with |E| ≤ γₙ|L||X̂|, multiply by L⁻¹ on the left:
    X̂ = L⁻¹ + L⁻¹E, so |X̂ − L⁻¹| = |L⁻¹E| ≤ |L⁻¹||E| ≤ γₙ|L⁻¹||L||X̂|. -/
theorem triInv_method1_forward_error (n : ℕ) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hn : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j : Fin n,
      |X_hat i j - L_inv i j| ≤
      gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := by
  intro X_hat i j
  -- Get residual: |LX̂ − I|_{k₁j} ≤ γ(n) ∑_{k₂} |L_{k₁k₂}| |X̂_{k₂j}|
  have hRes := triInv_method1_right_residual_matrix n fp L hL_diag hLT hn
  -- Define E_{k₁j} = (LX̂)_{k₁j} − δ_{k₁j}
  -- From LX̂ = I + E, multiply by L⁻¹: X̂ = L⁻¹ + L⁻¹E
  -- So X̂_{ij} − L⁻¹_{ij} = (L⁻¹E)_{ij} = ∑_{k₁} L⁻¹_{ik₁} E_{k₁j}
  have hDiff : X_hat i j - L_inv i j =
      ∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) := by
    -- RHS = ∑ k₁, L⁻¹(i,k₁) · (LX̂)(k₁,j) − ∑ k₁, L⁻¹(i,k₁) · δ(k₁,j)
    -- First part = (L⁻¹LX̂)(i,j) = X̂(i,j), second part = L⁻¹(i,j)
    have hRHS_expand : ∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) =
        ∑ k₁ : Fin n, L_inv i k₁ * (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j) -
        ∑ k₁ : Fin n, L_inv i k₁ * (if k₁ = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k₁ _; ring
    rw [hRHS_expand]
    -- Second sum = L⁻¹(i,j)
    have hSecond : ∑ k₁ : Fin n, L_inv i k₁ *
        (if k₁ = j then (1 : ℝ) else 0) = L_inv i j := by
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    -- First sum = (L⁻¹ · L · X̂)(i,j) = X̂(i,j)
    have hFirst : ∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j) = X_hat i j := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have hInvL : ∀ k₂ : Fin n,
          (∑ k₁ : Fin n, L_inv i k₁ * L k₁ k₂) = if i = k₂ then 1 else 0 :=
        fun k₂ => hInv i k₂
      simp_rw [hInvL]
      simp [Finset.mem_univ]
    rw [hFirst, hSecond]
  rw [hDiff]
  calc |∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)|
      ≤ ∑ k₁ : Fin n, |L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |L_inv i k₁| *
        |∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |L_inv i k₁| *
        (gamma fp n * ∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        exact mul_le_mul_of_nonneg_left (hRes k₁ j) (abs_nonneg _)
    _ = gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k₁ _; ring

/-- **Method 1 first-order forward error** (Higham eq. 14.6).

    |X̂ − L⁻¹| ≤ γ(n)|L⁻¹||L||L⁻¹| + O(u²).

    Since X̂ = L⁻¹ + O(u), replacing |X̂| by |L⁻¹| in eq. 14.5 gives
    this first-order bound. We state the "pre-replacement" form:
    for any X̂_bound satisfying |X̂| ≤ X̂_bound, we get the bound
    with X̂_bound in place of |X̂|. -/
theorem triInv_method1_forward_error_firstorder (n : ℕ) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (X_bound : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hn : gammaValid fp n)
    (hBound : ∀ i j : Fin n,
      |fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i| ≤
        X_bound i j) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j : Fin n,
      |X_hat i j - L_inv i j| ≤
      gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |L k₁ k₂| * X_bound k₂ j) := by
  intro X_hat i j
  have hFwd := triInv_method1_forward_error n fp L L_inv hL_diag hLT hInv hn i j
  calc |X_hat i j - L_inv i j|
      ≤ gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := hFwd
    _ ≤ gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * X_bound k₂ j) := by
        apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn)
        apply Finset.sum_le_sum; intro k₁ _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum; intro k₂ _
        exact mul_le_mul_of_nonneg_left (hBound k₂ j) (abs_nonneg _)

/-- **Method 1 normwise forward error** (Higham eq. 14.7).

    ‖X̂ − L⁻¹‖∞ ≤ γ(n) · ‖|L⁻¹||L||X̂|‖∞.

    When ‖X̂‖∞ ≈ ‖L⁻¹‖∞ (i.e. to first order), this gives
    relative error ≤ cₙu · cond(L⁻¹). -/
theorem triInv_method1_normwise_error (n : ℕ) (_hn0 : 0 < n) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hgv : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    infNorm (fun i j => X_hat i j - L_inv i j) ≤
      gamma fp n * infNorm (fun i j =>
        ∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|)) := by
  intro X_hat
  have hFwd := triInv_method1_forward_error n fp L L_inv hL_diag hLT hInv hgv
  -- infNorm is max_i ∑_j |M i j|. We bound each row sum then take the max.
  let M := fun i j => ∑ k₁ : Fin n, |L_inv i k₁| *
    (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|)
  have hnn : ∀ i j : Fin n, 0 ≤ M i j := by
    intro i' j'; apply Finset.sum_nonneg; intro k₁ _
    exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg
      (fun k₂ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  -- Each entry: |X̂ij − L⁻¹ij| ≤ γ(n) · M i j
  have hEntry : ∀ i j : Fin n, |X_hat i j - L_inv i j| ≤ gamma fp n * M i j :=
    fun i j => hFwd i j
  -- Row sum bound: ∑_j |X̂ij − L⁻¹ij| ≤ γ(n) · ∑_j M i j
  have hRow : ∀ i : Fin n, ∑ j : Fin n, |X_hat i j - L_inv i j| ≤
      gamma fp n * ∑ j : Fin n, M i j := by
    intro i
    calc ∑ j : Fin n, |X_hat i j - L_inv i j|
        ≤ ∑ j : Fin n, gamma fp n * M i j :=
          Finset.sum_le_sum (fun j _ => hEntry i j)
      _ = gamma fp n * ∑ j : Fin n, M i j :=
          (Finset.mul_sum Finset.univ _ (gamma fp n)).symm
  -- ∑_j M i j = ∑_j |M i j| since M ≥ 0
  have habs_eq : ∀ i j : Fin n, |M i j| = M i j :=
    fun i j => abs_of_nonneg (hnn i j)
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |(fun i j => X_hat i j - L_inv i j) i j|
        ≤ gamma fp n * ∑ j : Fin n, M i j := hRow i
      _ = gamma fp n * ∑ j : Fin n, |(fun i j => M i j) i j| := by
          congr 1; apply Finset.sum_congr rfl; intro j _; exact (habs_eq i j).symm
      _ ≤ gamma fp n * infNorm M := by
          apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hgv)
          exact row_sum_le_infNorm M i
  · exact mul_nonneg (gamma_nonneg fp hgv) (infNorm_nonneg M)

-- §14.2.1  Method 2 (reverse-order column computation via mat-vec multiply)

/-- Lower-triangular column split used by Method 2: in column `j`, entries
    above the diagonal vanish, so the column product separates into the diagonal
    term plus the strict trailing tail. -/
theorem lowerTri_column_sum_eq_diag_add_tail (n : ℕ)
    (L X_hat : Fin n → Fin n → ℝ)
    (hLT : ∀ a b : Fin n, b.val > a.val → L a b = 0) :
    ∀ i j : Fin n,
      (∑ k : Fin n, X_hat i k * L k j) =
        X_hat i j * L j j +
          ∑ k : Fin n, if j.val < k.val then X_hat i k * L k j else 0 := by
  intro i j
  classical
  rw [← Finset.add_sum_erase Finset.univ
    (fun k : Fin n => X_hat i k * L k j) (Finset.mem_univ j)]
  congr 1
  calc
    (∑ k ∈ Finset.univ.erase j, X_hat i k * L k j)
        = ∑ k ∈ Finset.univ.erase j,
            (if j.val < k.val then X_hat i k * L k j else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk_ne : k ≠ j := by
            simpa [Finset.mem_erase] using hk
          by_cases hjk : j.val < k.val
          · simp [hjk]
          · have hkj : j.val > k.val := by
              have hle : k.val ≤ j.val := Nat.le_of_not_gt hjk
              have hne_val : k.val ≠ j.val := by
                intro hval
                exact hk_ne (Fin.ext hval)
              omega
            rw [hLT k j hkj]
            simp [hjk]
    _ = ∑ k : Fin n, if j.val < k.val then X_hat i k * L k j else 0 := by
          rw [Finset.sum_erase]
          simp

/-- Source-shaped Method 2 off-diagonal identity from a strict trailing update.
    The update hypothesis uses only the tail `k > j`, avoiding the
    self-reference in the full column sum. -/
theorem triInv_method2_offdiag_trailing_update_identity (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hLT : ∀ a b : Fin n, b.val > a.val → L a b = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ) :
    ∀ j row : Fin n, row.val > j.val →
      ∃ δ Δ : ℝ, |δ| ≤ fp.u ∧
        (∑ k : Fin n, X_hat row k * L k j) -
            (if row = j then 1 else 0) =
          Δ * L j j - δ *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) := by
  intro j row hij
  obtain ⟨δ, hδ, hdiag⟩ := hDiag j
  obtain ⟨Δ, hupdate⟩ := hTrail j row hij
  refine ⟨δ, Δ, hδ, ?_⟩
  let tail : ℝ :=
    ∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0
  have hupdate_tail : X_hat row j = -X_hat j j * tail + Δ := by
    simpa [tail] using hupdate
  have hne : row ≠ j := by
    intro h
    exact (Nat.ne_of_gt hij) (congrArg Fin.val h)
  have hsplit :
      (∑ k : Fin n, X_hat row k * L k j) =
        X_hat row j * L j j + tail := by
    simpa [tail] using lowerTri_column_sum_eq_diag_add_tail n L X_hat hLT row j
  rw [if_neg hne, sub_zero, hsplit]
  calc
    X_hat row j * L j j + tail
        = (-X_hat j j * tail + Δ) * L j j + tail := by
            rw [hupdate_tail]
    _ = (-(X_hat j j * L j j) * tail + Δ * L j j) + tail := by ring
    _ = (-(1 + δ) * tail + Δ * L j j) + tail := by rw [hdiag]
    _ = Δ * L j j - δ * tail := by ring

/-- Source-shaped Method 2 off-diagonal residual bound from a strict trailing
    update.  The constant `η` is left abstract so later product-error analyses
    can instantiate the matvec/scalar rounding budget without using the current
    full-column `Method2Spec.offdiag_err` field. -/
theorem triInv_method2_offdiag_trailing_update_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ) {η : ℝ}
    (_hη : 0 ≤ η)
    (hLT : ∀ a b : Fin n, b.val > a.val → L a b = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ η *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ) :
    ∀ j row : Fin n, row.val > j.val →
      |(∑ k : Fin n, X_hat row k * L k j) -
          (if row = j then 1 else 0)| ≤
        (fp.u + η) *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) := by
  intro j row hij
  let tail : ℝ :=
    ∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0
  let tailAbs : ℝ :=
    ∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0
  obtain ⟨δ, hδ, hdiag⟩ := hDiag j
  obtain ⟨Δ, hΔ, hupdate⟩ := hTrail j row hij
  have hupdate_tail : X_hat row j = -X_hat j j * tail + Δ := by
    simpa [tail] using hupdate
  have hne : row ≠ j := by
    intro h
    exact (Nat.ne_of_gt hij) (congrArg Fin.val h)
  have hsplit :
      (∑ k : Fin n, X_hat row k * L k j) =
        X_hat row j * L j j + tail := by
    simpa [tail] using lowerTri_column_sum_eq_diag_add_tail n L X_hat hLT row j
  have hid :
      (∑ k : Fin n, X_hat row k * L k j) -
          (if row = j then 1 else 0) =
        Δ * L j j - δ * tail := by
    rw [if_neg hne, sub_zero, hsplit]
    calc
      X_hat row j * L j j + tail
          = (-X_hat j j * tail + Δ) * L j j + tail := by
              rw [hupdate_tail]
      _ = (-(X_hat j j * L j j) * tail + Δ * L j j) + tail := by ring
      _ = (-(1 + δ) * tail + Δ * L j j) + tail := by rw [hdiag]
      _ = Δ * L j j - δ * tail := by ring
  have htail_abs : |tail| ≤ tailAbs := by
    calc
      |tail| =
          |∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0| := by
            rfl
      _ ≤ ∑ k : Fin n,
            |if j.val < k.val then X_hat row k * L k j else 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = tailAbs := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hjk : j.val < k.val <;> simp [hjk, abs_mul]
  have hδ_tail : |δ * tail| ≤ fp.u * tailAbs := by
    calc
      |δ * tail| = |δ| * |tail| := abs_mul _ _
      _ ≤ fp.u * tailAbs :=
          mul_le_mul hδ htail_abs (abs_nonneg _) fp.u_nonneg
  rw [hid]
  calc
    |Δ * L j j - δ * tail|
        ≤ |Δ * L j j| + |δ * tail| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le (Δ * L j j) (-(δ * tail))
    _ ≤ η * tailAbs + fp.u * tailAbs := by
        exact add_le_add (by simpa [tailAbs] using hΔ) hδ_tail
    _ = (fp.u + η) * tailAbs := by ring

/-- Full-column budget form of `triInv_method2_offdiag_trailing_update_bound`:
    the strict trailing absolute product is bounded by the complete
    `|X_hat|*|L|` column budget used in Lemma 14.1. -/
theorem triInv_method2_offdiag_trailing_update_full_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ) {η : ℝ}
    (hη : 0 ≤ η)
    (hLT : ∀ a b : Fin n, b.val > a.val → L a b = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ η *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ) :
    ∀ j row : Fin n, row.val > j.val →
      |(∑ k : Fin n, X_hat row k * L k j) -
          (if row = j then 1 else 0)| ≤
        (fp.u + η) * (∑ k : Fin n, |X_hat row k| * |L k j|) := by
  intro j row hij
  have htail :=
    triInv_method2_offdiag_trailing_update_bound n fp L X_hat hη hLT hDiag hTrail
      j row hij
  have htail_le_full :
      (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ≤
        ∑ k : Fin n, |X_hat row k| * |L k j| := by
    apply Finset.sum_le_sum
    intro k _
    have hterm_nonneg : 0 ≤ |X_hat row k| * |L k j| :=
      mul_nonneg (abs_nonneg (X_hat row k)) (abs_nonneg (L k j))
    by_cases hjk : j.val < k.val <;> simp [hjk, hterm_nonneg]
  have hcoef : 0 ≤ fp.u + η := add_nonneg fp.u_nonneg hη
  exact le_trans htail (mul_le_mul_of_nonneg_left htail_le_full hcoef)

/-- **Specification for Method 2 triangular inversion**.

    Method 2 computes columns of X̂ ≈ L⁻¹ in reverse order j = n, n−1, …, 1.
    For each j:
      x̂ⱼⱼ = lⱼⱼ⁻¹(1 + δ),  |δ| ≤ u
      x̂(j+1:n, j) = x̂(j+1:n, j+1:n) · L(j+1:n, j)   (mat-vec multiply)
      x̂(j+1:n, j) = −x̂ⱼⱼ · x̂(j+1:n, j)              (scalar multiply)

    This is an abstract spec capturing the key error properties. -/
structure Method2Spec (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ) : Prop where
  /-- Diagonal entries: x̂ⱼⱼ = fl(1/lⱼⱼ), so x̂ⱼⱼlⱼⱼ = 1 + δ with |δ| ≤ u. -/
  diag_err : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
    X_hat j j * L j j = 1 + δ
  /-- Off-diagonal (below j): computed via mat-vec + scalar multiply with
      rounding errors bounded by Δ-notation. -/
  offdiag_err : ∀ j : Fin n, ∀ i : Fin n, i.val > j.val →
    ∃ Δ_mv : Fin n → ℝ,
      (∀ k : Fin n, |Δ_mv k| ≤ gamma fp n * |X_hat i k| * |L k j|) ∧
      X_hat i j = -X_hat j j * (∑ k : Fin n, X_hat i k * L k j) +
        Δ_mv j
  /-- Upper triangle is zero (since L is lower triangular, L⁻¹ is too). -/
  upper_zero : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0

/-- Higham, 2nd ed., Chapter 14, Section 14.2.1, Method 2:
    source-facing kernel certificate for the reverse-column strict-tail update.

    This packages the existing Method 2 diagonal/shape/error specification
    together with the exact stored below-diagonal update
    `fl_mul (-X_hat j j) (fl_dotProduct strictTail Lcol)`.  It is not yet the
    full loop proof; the remaining source obligation is to show the concrete
    reverse-column implementation produces this certificate. -/
structure Method2StrictTailKernelSpec (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ) : Prop where
  /-- Existing Method 2 diagonal, off-diagonal, and triangular-shape contract. -/
  method2 : Method2Spec fp n L X_hat
  /-- Below-diagonal entries are stored by the rounded strict-tail dot/scalar
      kernel described in the source Method 2 recurrence. -/
  strict_tail_dot_scalar : ∀ j row : Fin n, row.val > j.val →
    X_hat row j =
      fp.fl_mul (-X_hat j j)
        (fl_dotProduct fp n
          (fun k : Fin n => if j.val < k.val then X_hat row k else 0)
          (fun k : Fin n => L k j))

/-- Triangular-shape support for Method 2: if both `X_hat` and `L` are lower
    triangular, then the left residual `X_hat * L - I` is zero strictly above
    the diagonal. -/
theorem triInv_lower_left_residual_upper_zero (n : ℕ)
    (L X_hat : Fin n → Fin n → ℝ)
    (hX_lower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hL_lower : ∀ i j : Fin n, j.val > i.val → L i j = 0) :
    ∀ i j : Fin n, i.val < j.val →
      ∑ k : Fin n, X_hat i k * L k j -
        (if i = j then 1 else 0) = 0 := by
  intro i j hij
  have hne : i ≠ j := by
    intro h
    have hval : i.val = j.val := congrArg Fin.val h
    omega
  have hsum : ∑ k : Fin n, X_hat i k * L k j = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i.val < k.val
    · rw [hX_lower i k hik]
      ring
    · have hkj : j.val > k.val := by
        exact Nat.lt_of_le_of_lt (Nat.le_of_not_gt hik) hij
      rw [hL_lower k j hkj]
      ring
  simp [hsum, hne]

/-- Method 2's stored triangular shape makes the left residual vanish above
    the diagonal.  This closes the easy structural part of the Lemma 14.1
    residual; the below-diagonal induction remains separate. -/
theorem triInv_method2_left_residual_upper_zero (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat) :
    ∀ i j : Fin n, i.val < j.val →
      ∑ k : Fin n, X_hat i k * L k j -
        (if i = j then 1 else 0) = 0 :=
  triInv_lower_left_residual_upper_zero n L X_hat
    hSpec.upper_zero hLT

/-- Method 2's diagonal residual bound from the diagonal error field in
    `Method2Spec`: on the diagonal, triangularity reduces `(X_hat * L)_{jj}`
    to `X_hat j j * L j j = 1 + δ`, with `|δ| ≤ u`. -/
theorem triInv_method2_left_residual_diag_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat) :
    ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤ fp.u := by
  intro j
  obtain ⟨δ, hδ, hdiag⟩ := hSpec.diag_err j
  have hsum : ∑ k : Fin n, X_hat j k * L k j =
      X_hat j j * L j j := by
    apply Finset.sum_eq_single j
    · intro k _ hk
      by_cases hjk : j.val < k.val
      · rw [hSpec.upper_zero j k hjk]
        ring
      · have hkj : j.val > k.val := by
          have hle : k.val ≤ j.val := Nat.le_of_not_gt hjk
          have hne_val : k.val ≠ j.val := by
            intro hval
            exact hk (Fin.ext hval)
          omega
        rw [hLT k j hkj]
        ring
    · intro hnot
      simp at hnot
  simpa [hsum, hdiag] using hδ

/-- Lemma 14.1 support: Method 2's diagonal residual has the product-budget
    shape needed by the all-region assembly theorem.  The diagonal relation
    `X_hat j j * L j j = 1 + δ`, together with `|δ| ≤ u` and
    `gammaValid fp (n + 1)`, ensures the diagonal product budget is nonvacuous:
    the full column budget is at least `1 - u`, while
    `gamma_(n+1) * (1 - u) ≥ u`. -/
theorem triInv_method2_left_residual_diag_product_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat) :
    ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤
        gamma fp (n + 1) * ∑ k : Fin n, |X_hat j k| * |L k j| := by
  intro j
  have hdiag_res :=
    triInv_method2_left_residual_diag_bound n fp L X_hat hLT hSpec j
  obtain ⟨δ, hδ, hdiag⟩ := hSpec.diag_err j
  have hle1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp hle1 hn1
  have hgamma1_le : gamma fp 1 ≤ gamma fp (n + 1) :=
    gamma_mono fp hle1 hn1
  have hu_lt_one : fp.u < 1 := by
    have h := hvalid1
    unfold gammaValid at h
    norm_num at h
    exact h
  have hone_minus_nonneg : 0 ≤ 1 - fp.u := by linarith
  have hgamma1_mul : gamma fp 1 * (1 - fp.u) = fp.u := by
    have hden : (1 - fp.u) ≠ 0 := by linarith
    unfold gamma
    norm_num
    field_simp [hden]
  let S : ℝ := ∑ k : Fin n, |X_hat j k| * |L k j|
  have hdiag_term_le_S : |X_hat j j| * |L j j| ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (abs_nonneg (X_hat j k)) (abs_nonneg (L k j)))
      (Finset.mem_univ j)
  have hone_minus_le_prod : 1 - fp.u ≤ |X_hat j j| * |L j j| := by
    have habs_lower : 1 - |δ| ≤ |1 + δ| := by
      have htri : (1 : ℝ) ≤ |1 + δ| + |δ| := by
        simpa [abs_neg, add_assoc] using (abs_add_le (1 + δ) (-δ))
      linarith
    calc
      1 - fp.u ≤ 1 - |δ| := by linarith
      _ ≤ |1 + δ| := habs_lower
      _ = |X_hat j j * L j j| := by rw [hdiag]
      _ = |X_hat j j| * |L j j| := by rw [abs_mul]
  have hu_le_coeff_budget : fp.u ≤ gamma fp (n + 1) * S := by
    calc
      fp.u = gamma fp 1 * (1 - fp.u) := hgamma1_mul.symm
      _ ≤ gamma fp (n + 1) * (1 - fp.u) :=
        mul_le_mul_of_nonneg_right hgamma1_le hone_minus_nonneg
      _ ≤ gamma fp (n + 1) * S := by
        apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn1)
        exact le_trans hone_minus_le_prod hdiag_term_le_S
  exact le_trans hdiag_res hu_le_coeff_budget

/-- Lemma 14.1 support: diagonal Method 2 product-budget bound from only the
    diagonal rounded-reciprocal certificate and triangular shape.

This is the same diagonal edge as
`triInv_method2_left_residual_diag_product_bound`, but it avoids depending on
the older full-column `Method2Spec.offdiag_err` field. -/
theorem triInv_method2_left_residual_diag_product_bound_of_diag_upper
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hUpper : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0) :
    ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤
        gamma fp (n + 1) * ∑ k : Fin n, |X_hat j k| * |L k j| := by
  intro j
  obtain ⟨δ, hδ, hdiag⟩ := hDiag j
  have hsum : ∑ k : Fin n, X_hat j k * L k j =
      X_hat j j * L j j := by
    apply Finset.sum_eq_single j
    · intro k _ hk
      by_cases hjk : j.val < k.val
      · rw [hUpper j k hjk]
        ring
      · have hkj : j.val > k.val := by
          have hle : k.val ≤ j.val := Nat.le_of_not_gt hjk
          have hne_val : k.val ≠ j.val := by
            intro hval
            exact hk (Fin.ext hval)
          omega
        rw [hLT k j hkj]
        ring
    · intro hnot
      simp at hnot
  have hdiag_res : |∑ k : Fin n, X_hat j k * L k j - 1| ≤ fp.u := by
    simpa [hsum, hdiag] using hδ
  have hle1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp hle1 hn1
  have hgamma1_le : gamma fp 1 ≤ gamma fp (n + 1) :=
    gamma_mono fp hle1 hn1
  have hu_lt_one : fp.u < 1 := by
    have h := hvalid1
    unfold gammaValid at h
    norm_num at h
    exact h
  have hone_minus_nonneg : 0 ≤ 1 - fp.u := by linarith
  have hgamma1_mul : gamma fp 1 * (1 - fp.u) = fp.u := by
    have hden : (1 - fp.u) ≠ 0 := by linarith
    unfold gamma
    norm_num
    field_simp [hden]
  let S : ℝ := ∑ k : Fin n, |X_hat j k| * |L k j|
  have hdiag_term_le_S : |X_hat j j| * |L j j| ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (abs_nonneg (X_hat j k)) (abs_nonneg (L k j)))
      (Finset.mem_univ j)
  have hone_minus_le_prod : 1 - fp.u ≤ |X_hat j j| * |L j j| := by
    have habs_lower : 1 - |δ| ≤ |1 + δ| := by
      have htri : (1 : ℝ) ≤ |1 + δ| + |δ| := by
        simpa [abs_neg, add_assoc] using (abs_add_le (1 + δ) (-δ))
      linarith
    calc
      1 - fp.u ≤ 1 - |δ| := by linarith
      _ ≤ |1 + δ| := habs_lower
      _ = |X_hat j j * L j j| := by rw [hdiag]
      _ = |X_hat j j| * |L j j| := by rw [abs_mul]
  have hu_le_coeff_budget : fp.u ≤ gamma fp (n + 1) * S := by
    calc
      fp.u = gamma fp 1 * (1 - fp.u) := hgamma1_mul.symm
      _ ≤ gamma fp (n + 1) * (1 - fp.u) :=
        mul_le_mul_of_nonneg_right hgamma1_le hone_minus_nonneg
      _ ≤ gamma fp (n + 1) * S := by
        apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn1)
        exact le_trans hone_minus_le_prod hdiag_term_le_S
  exact le_trans hdiag_res hu_le_coeff_budget

/-- Lemma 14.1 support: regionwise Method 2 residual bounds assemble into
    the full componentwise left-residual bound.  This is only an assembly
    theorem: the diagonal and below-diagonal product-budget estimates remain
    explicit hypotheses, so the missing rounded-loop induction is not hidden. -/
theorem triInv_method2_left_residual_from_region_bounds (n : ℕ)
    (L X_hat : Fin n → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps)
    (hUpper : ∀ i j : Fin n, i.val < j.val →
      ∑ k : Fin n, X_hat i k * L k j -
        (if i = j then 1 else 0) = 0)
    (hDiag : ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤
        eps * ∑ k : Fin n, |X_hat j k| * |L k j|)
    (hLower : ∀ j row : Fin n, row.val > j.val →
      |∑ k : Fin n, X_hat row k * L k j -
          (if row = j then 1 else 0)| ≤
        eps * ∑ k : Fin n, |X_hat row k| * |L k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        eps * ∑ k : Fin n, |X_hat i k| * |L k j| := by
  intro i j
  by_cases hij : i.val < j.val
  · have hzero := hUpper i j hij
    have hS_nonneg :
        0 ≤ ∑ k : Fin n, |X_hat i k| * |L k j| := by
      exact Finset.sum_nonneg fun k _ =>
        mul_nonneg (abs_nonneg (X_hat i k)) (abs_nonneg (L k j))
    have hres_zero :
        |∑ k : Fin n, X_hat i k * L k j -
            (if i = j then 1 else 0)| = 0 := by
      rw [hzero]
      simp
    rw [hres_zero]
    exact mul_nonneg heps hS_nonneg
  · by_cases hji : j.val < i.val
    · exact hLower j i hji
    · have hij_eq : i = j := Fin.ext (by omega)
      subst i
      simpa using hDiag j

/-- Method 2 off-diagonal update residual unpacked from `Method2Spec`:
    for `i > j`, the update equation gives a local delta certificate for
    `X_hat i j + X_hat j j * (X_hat * L) i j`. -/
theorem triInv_method2_offdiag_update_delta_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hSpec : Method2Spec fp n L X_hat) :
    ∀ j i : Fin n, i.val > j.val →
      ∃ Δ : ℝ,
        |Δ| ≤ gamma fp n * |X_hat i j| * |L j j| ∧
        X_hat i j +
          X_hat j j * (∑ k : Fin n, X_hat i k * L k j) = Δ := by
  intro j i hij
  obtain ⟨Δ_mv, hΔ, hupdate⟩ := hSpec.offdiag_err j i hij
  refine ⟨Δ_mv j, ?_, ?_⟩
  · simpa using hΔ j
  · rw [hupdate]
    ring

/-- Method 2 off-diagonal update residual after multiplying by the diagonal
    entry `L j j`.  This combines `offdiag_err` with the diagonal error field
    and is a below-diagonal support lemma for the Lemma 14.1 induction. -/
theorem triInv_method2_offdiag_scaled_residual_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hSpec : Method2Spec fp n L X_hat) :
    ∀ j i : Fin n, i.val > j.val →
      ∃ δ : ℝ, |δ| ≤ fp.u ∧
        |X_hat i j * L j j +
          (1 + δ) * (∑ k : Fin n, X_hat i k * L k j)| ≤
        (gamma fp n * |X_hat i j| * |L j j|) * |L j j| := by
  intro j i hij
  obtain ⟨δ, hδ, hdiag⟩ := hSpec.diag_err j
  obtain ⟨Δ, hΔ, hΔeq⟩ :=
    triInv_method2_offdiag_update_delta_bound n fp L X_hat hSpec j i hij
  refine ⟨δ, hδ, ?_⟩
  have hmain :
      X_hat i j * L j j +
          (1 + δ) * (∑ k : Fin n, X_hat i k * L k j) =
        Δ * L j j := by
    calc
      X_hat i j * L j j +
          (1 + δ) * (∑ k : Fin n, X_hat i k * L k j)
          = (X_hat i j +
              X_hat j j * (∑ k : Fin n, X_hat i k * L k j)) * L j j := by
              rw [← hdiag]
              ring
      _ = Δ * L j j := by rw [hΔeq]
  rw [hmain]
  calc
    |Δ * L j j| = |Δ| * |L j j| := abs_mul _ _
    _ ≤ (gamma fp n * |X_hat i j| * |L j j|) * |L j j| :=
      mul_le_mul_of_nonneg_right hΔ (abs_nonneg _)

/-- **Abstract Lemma 14.1 interface** (Higham eq. 14.8): Method 2 left residual.

    The computed inverse X̂ from Method 2 satisfies the left residual bound:
      |X̂L − I| ≤ c'ₙu · (|X̂| · |L|).

    Higham proves this by induction on n using the 2×2 block partition
    L = [[α, 0], [y, M]], X̂ = [[β̂, 0], [ẑ, N̂]].

    This theorem is an abstract interface: the hypothesis `hLeftRes` is the
    Method 2 local/inductive analysis, and the theorem records the named
    contract for reuse by later matrix-inversion results. -/
theorem triInv_method2_left_residual (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ)
    (_hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (_hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (_hn : gammaValid fp n)
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j| :=
  hLeftRes

/-- Problem 14.2 / Lemma 14.1 normwise form:
    Method 2's componentwise left-residual interface implies the corresponding
    infinity-norm residual bound. -/
theorem triInv_method2_left_residual_normwise (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j|) :
    infNorm (fun i j =>
      ∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm X_hat * infNorm L := by
  have hComp :=
    triInv_method2_left_residual n fp L X_hat hL_diag hLT hn hLeftRes
  exact higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (R := fun i j => ∑ k : Fin n, X_hat i k * L k j -
      if i = j then 1 else 0)
    (A := X_hat) (B := L) (gamma_nonneg fp hn) hComp

-- §14.2.2  Block methods

/-- **Specification for block triangular inversion (Method 1B)**.

    Method 1B computes X̂ ≈ L⁻¹ in block form: for j = 1:N,
    diagonal blocks Xⱼⱼ = Lⱼⱼ⁻¹ by Method 1, then off-diagonal
    blocks by block forward substitution.

    The block indexing details are intentionally abstracted away; the reusable
    numerical content is the per-column backward-error contract produced by the
    diagonal block inversions and block forward substitutions. -/
structure BlockMethod1BSpec (fp : FPModel) (n N : ℕ)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ) : Prop where
  /-- The declared number of blocks is compatible with the matrix dimension. -/
  block_count_le_dim : N ≤ n
  /-- The computed inverse has the expected lower-triangular shape. -/
  lower_triangular_inverse : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0
  /-- Each computed column satisfies the backward-error contract obtained from
      the Method 1 diagonal block solve and the block forward substitutions. -/
  column_backward_error : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
    (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
    ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
      if i = j then 1 else 0

/-- **Method 1B row-to-column assembly** (Higham eqs. 14.11--14.13 support).

    If each row of a fixed computed column has its own local backward-error
    row certificate, assemble those rows into the full matrix perturbation
    certificate expected by `BlockMethod1BSpec.column_backward_error`. -/
theorem triInv_method1B_column_backward_error_of_row_certificates
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ) (j : Fin n)
    (hRows : ∀ i : Fin n, ∃ Δrow : Fin n → ℝ,
      (∀ k : Fin n, |Δrow k| ≤ gamma fp n * |L i k|) ∧
      ∑ k : Fin n, (L i k + Δrow k) * X_hat k j =
        if i = j then 1 else 0) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k : Fin n, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i : Fin n, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0 := by
  classical
  let ΔL : Fin n → Fin n → ℝ := fun i k => Classical.choose (hRows i) k
  refine ⟨ΔL, ?_, ?_⟩
  · intro i k
    simpa [ΔL] using (Classical.choose_spec (hRows i)).1 k
  · intro i
    simpa [ΔL] using (Classical.choose_spec (hRows i)).2

/-- **Method 1B specification from column backward errors** (Higham eqs.
    14.11--14.13 support).

    This source-facing packaging theorem records the exact data needed by the
    abstract block Method 1B interface: a compatible block count, lower
    triangular shape of the computed inverse, and per-column backward-error
    certificates.  The block-loop derivation of those column certificates
    remains a separate dependency. -/
theorem triInv_method1B_spec_of_column_backward_error
    (n N : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hCol : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0) :
    BlockMethod1BSpec fp n N L X_hat :=
  { block_count_le_dim := hBlockCount
    lower_triangular_inverse := hLower
    column_backward_error := hCol }

/-- **Method 1B specification from row-local certificates** (Higham eqs.
    14.11--14.13 support).

    This bridge reduces the open block-loop obligation to row-local
    backward-error certificates for each computed column. -/
theorem triInv_method1B_spec_of_row_certificates
    (n N : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hRows : ∀ j i : Fin n, ∃ Δrow : Fin n → ℝ,
      (∀ k : Fin n, |Δrow k| ≤ gamma fp n * |L i k|) ∧
      ∑ k : Fin n, (L i k + Δrow k) * X_hat k j =
        if i = j then 1 else 0) :
    BlockMethod1BSpec fp n N L X_hat :=
  triInv_method1B_spec_of_column_backward_error n N fp L X_hat
    hBlockCount hLower
    (fun j => triInv_method1B_column_backward_error_of_row_certificates
      n fp L X_hat j (hRows j))

/-- **Lemma 14.2** (Higham eq. 14.10): Method 1B right residual.

    |LX̂ − I| ≤ cₙu|L||X̂|.

    The block version achieves the same right residual bound as the
    unblocked Method 1. -/
theorem triInv_method1B_right_residual (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (_hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (_hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (_hn : gammaValid fp n)
    -- Hypothesis: each column of X̂ satisfies the same per-column backward error
    -- as Method 1 (forwardSub_backward_error).
    (hCol : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
  intro i j
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ := hCol j
  have hLX : ∑ k : Fin n, L i k * X_hat k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔL i k * X_hat k j) := by
    have h := hΔL_eq i
    have hsplit : ∑ k : Fin n, L i k * X_hat k j +
        ∑ k : Fin n, ΔL i k * X_hat k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hLX, abs_neg]
  calc |∑ k : Fin n, ΔL i k * X_hat k j|
      ≤ ∑ k : Fin n, |ΔL i k * X_hat k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔL i k| * |X_hat k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, (gamma fp n * |L i k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔL_bound i k) (abs_nonneg _)
    _ = gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- Method 1B right residual obtained from the block-method specification. -/
theorem triInv_method1B_right_residual_from_spec (n N : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hSpec : BlockMethod1BSpec fp n N L X_hat) :
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| :=
  triInv_method1B_right_residual n fp L X_hat hL_diag hLT hn
    hSpec.column_backward_error

/-- **Lemma 14.2 bridge**: Method 1B right residual from explicit column
    backward-error certificates.

    This theorem separates the residual consequence from the still-open block
    partition proof of the column certificates in equations (14.11)--(14.13). -/
theorem triInv_method1B_right_residual_of_column_backward_error
    (n N : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hCol : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| :=
  triInv_method1B_right_residual_from_spec n N fp L X_hat hL_diag hLT hn
    (triInv_method1B_spec_of_column_backward_error n N fp L X_hat
      hBlockCount hLower hCol)

/-- **Lemma 14.2 bridge**: Method 1B right residual from row-local
    backward-error certificates.

    This is a row-local companion to
    `triInv_method1B_right_residual_of_column_backward_error`; the remaining
    source obligation is to derive the row certificates from the block Method
    1B update loop. -/
theorem triInv_method1B_right_residual_of_row_certificates
    (n N : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hRows : ∀ j i : Fin n, ∃ Δrow : Fin n → ℝ,
      (∀ k : Fin n, |Δrow k| ≤ gamma fp n * |L i k|) ∧
      ∑ k : Fin n, (L i k + Δrow k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| :=
  triInv_method1B_right_residual_from_spec n N fp L X_hat hL_diag hLT hn
    (triInv_method1B_spec_of_row_certificates n N fp L X_hat
      hBlockCount hLower hRows)

/-- Problem 14.2 / Lemma 14.2 normwise form:
    Method 1B's componentwise right-residual bound implies the corresponding
    infinity-norm residual bound. -/
theorem triInv_method1B_right_residual_normwise (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hCol : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0) :
    infNorm (fun i j =>
      ∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm L * infNorm X_hat := by
  have hComp :=
    triInv_method1B_right_residual n fp L X_hat hL_diag hLT hn hCol
  exact higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (R := fun i j => ∑ k : Fin n, L i k * X_hat k j -
      if i = j then 1 else 0)
    (A := L) (B := X_hat) (gamma_nonneg fp hn) hComp

/-- Method 1B normwise right-residual bound obtained from the block-method
    specification. -/
theorem triInv_method1B_right_residual_normwise_from_spec
    (n N : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hSpec : BlockMethod1BSpec fp n N L X_hat) :
    infNorm (fun i j =>
      ∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm L * infNorm X_hat :=
  triInv_method1B_right_residual_normwise n hn0 fp L X_hat
    hL_diag hLT hn hSpec.column_backward_error

/-- Problem 14.2 / Lemma 14.2 normwise bridge:
    Method 1B's explicit column backward-error certificates imply the
    corresponding infinity-norm right-residual bound.

    This is the normwise companion of
    `triInv_method1B_right_residual_of_column_backward_error`; the open source
    obligation is still to derive the column certificates from the block Method
    1B loop in equations (14.11)--(14.13). -/
theorem triInv_method1B_right_residual_normwise_of_column_backward_error
    (n N : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hCol : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0) :
    infNorm (fun i j =>
      ∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm L * infNorm X_hat :=
  triInv_method1B_right_residual_normwise_from_spec n N hn0 fp L X_hat
    hL_diag hLT hn
    (triInv_method1B_spec_of_column_backward_error n N fp L X_hat
      hBlockCount hLower hCol)

/-- Problem 14.2 / Lemma 14.2 normwise bridge:
    Method 1B's row-local backward-error certificates imply the corresponding
    infinity-norm right-residual bound after assembling the rows into the
    column-certificate interface.

    This is the normwise companion of
    `triInv_method1B_right_residual_of_row_certificates`; the open source
    obligation is still to derive the row certificates from the block Method
    1B loop in equations (14.11)--(14.13). -/
theorem triInv_method1B_right_residual_normwise_of_row_certificates
    (n N : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hRows : ∀ j i : Fin n, ∃ Δrow : Fin n → ℝ,
      (∀ k : Fin n, |Δrow k| ≤ gamma fp n * |L i k|) ∧
      ∑ k : Fin n, (L i k + Δrow k) * X_hat k j =
        if i = j then 1 else 0) :
    infNorm (fun i j =>
      ∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm L * infNorm X_hat :=
  triInv_method1B_right_residual_normwise_from_spec n N hn0 fp L X_hat
    hL_diag hLT hn
    (triInv_method1B_spec_of_row_certificates n N fp L X_hat
      hBlockCount hLower hRows)

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

/-- Higham equation (14.14), Method 2B block-update decomposition:
    the computed off-diagonal block is the exact block product plus an explicit
    perturbation. -/
theorem higham14_eq14_14_method2B_block_update_decomposition {m r : ℕ}
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) (i : Fin r) (j : Fin m) :
    X21_hat i j =
      higham14_method2BBlockUpdateExact X22 L21 X11 i j +
        higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11 i j := by
  unfold higham14_method2BBlockUpdateDelta
  ring

/-- The Method 2B block-update perturbation inherits any supplied
    componentwise product-error bound for the rectangular triple product in
    equation (14.14). -/
theorem higham14_eq14_14_method2B_block_update_delta_bound {m r : ℕ}
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ)
    (ε : ℝ) (absBound : Fin r → Fin m → ℝ)
    (hBound : ∀ i : Fin r, ∀ j : Fin m,
      |X21_hat i j -
        higham14_method2BBlockUpdateExact X22 L21 X11 i j| ≤
          ε * absBound i j) :
    ∀ i : Fin r, ∀ j : Fin m,
      |higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11 i j| ≤
        ε * absBound i j := by
  intro i j
  simpa [higham14_method2BBlockUpdateDelta] using hBound i j

/-- Higham, 2nd ed., Chapter 14, equation (14.14), Method 2B:
    source-facing package for the rounded off-diagonal block update.

    The package records both the exact decomposition of the computed block into
    `-X22 * L21 * X11` plus an explicit perturbation and the componentwise
    product-error bound on that perturbation.  The instability analysis that
    uses this update certificate remains a separate source obligation. -/
structure Method2BBlockUpdateSpec {m r : ℕ}
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ)
    (ε : ℝ) (absBound : Fin r → Fin m → ℝ) : Prop where
  /-- The computed off-diagonal block is the exact Method 2B update plus
      the explicitly named perturbation. -/
  update_decomposition : ∀ i : Fin r, ∀ j : Fin m,
    X21_hat i j =
      higham14_method2BBlockUpdateExact X22 L21 X11 i j +
        higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11 i j
  /-- The explicit perturbation obeys the supplied componentwise product-error
      envelope for the rectangular triple product. -/
  delta_bound : ∀ i : Fin r, ∀ j : Fin m,
    |higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11 i j| ≤
      ε * absBound i j

/-- Higham, 2nd ed., Chapter 14, equation (14.14), Method 2B:
    build the source-facing block-update package from a rectangular
    triple-product error certificate. -/
theorem higham14_eq14_14_method2B_block_update_spec_of_product_error {m r : ℕ}
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ)
    (ε : ℝ) (absBound : Fin r → Fin m → ℝ)
    (hBound : ∀ i : Fin r, ∀ j : Fin m,
      |X21_hat i j -
        higham14_method2BBlockUpdateExact X22 L21 X11 i j| ≤
          ε * absBound i j) :
    Method2BBlockUpdateSpec X21_hat X22 L21 X11 ε absBound where
  update_decomposition :=
    higham14_eq14_14_method2B_block_update_decomposition
      X21_hat X22 L21 X11
  delta_bound :=
    higham14_eq14_14_method2B_block_update_delta_bound
      X21_hat X22 L21 X11 ε absBound hBound

/-- Higham equation (14.14), Method 2B residual identity:
    the off-diagonal left-residual block
    `X21_hat * L11 + X22 * L21` is exactly the block-update perturbation
    propagated through `L11`, provided `X11 * L11 = I`.

    This isolates the algebraic hinge used by the instability discussion:
    even if the block update has a local product-error certificate, that
    perturbation is subsequently multiplied by `L11` in the residual. -/
theorem higham14_eq14_14_method2B_offdiag_residual_eq_delta_mul {m r : ℕ}
    (L11 X11 : Fin m → Fin m → ℝ)
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (ε : ℝ) (absBound : Fin r → Fin m → ℝ)
    (hSpec : Method2BBlockUpdateSpec X21_hat X22 L21 X11 ε absBound)
    (hX11_left : IsLeftInverse m L11 X11) :
    ∀ i : Fin r, ∀ j : Fin m,
      rectMatMul X21_hat L11 i j + rectMatMul X22 L21 i j =
        rectMatMul
          (higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11)
          L11 i j := by
  intro i j
  let Δ := higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11
  let E := higham14_method2BBlockUpdateExact X22 L21 X11
  have hX21 : X21_hat = fun a b => E a b + Δ a b := by
    ext a b
    exact hSpec.update_decomposition a b
  have hX11L11 : rectMatMul X11 L11 = idMatrix m := by
    ext a b
    exact hX11_left a b
  have hE_mul :
      rectMatMul E L11 = fun a b => -rectMatMul X22 L21 a b := by
    unfold E higham14_method2BBlockUpdateExact
    calc
      rectMatMul (fun a b => -rectMatMul (rectMatMul X22 L21) X11 a b) L11
          = fun a b =>
              -rectMatMul (rectMatMul (rectMatMul X22 L21) X11) L11 a b := by
            exact rectMatMul_neg_left (rectMatMul (rectMatMul X22 L21) X11) L11
      _ = fun a b =>
              -rectMatMul (rectMatMul X22 L21) (rectMatMul X11 L11) a b := by
            rw [rectMatMul_assoc (rectMatMul X22 L21) X11 L11]
      _ = fun a b =>
              -rectMatMul (rectMatMul X22 L21) (idMatrix m) a b := by
            rw [hX11L11]
      _ = fun a b => -rectMatMul X22 L21 a b := by
            rw [rectMatMul_id_right (rectMatMul X22 L21)]
  have hX21_mul :
      rectMatMul X21_hat L11 i j =
        rectMatMul E L11 i j + rectMatMul Δ L11 i j := by
    calc
      rectMatMul X21_hat L11 i j =
          rectMatMul (fun a b => E a b + Δ a b) L11 i j := by
            rw [hX21]
      _ = rectMatMul E L11 i j + rectMatMul Δ L11 i j := by
            rw [rectMatMul_add_left E Δ L11]
  calc
    rectMatMul X21_hat L11 i j + rectMatMul X22 L21 i j
        = (rectMatMul E L11 i j + rectMatMul Δ L11 i j) +
            rectMatMul X22 L21 i j := by rw [hX21_mul]
    _ = (-rectMatMul X22 L21 i j + rectMatMul Δ L11 i j) +
            rectMatMul X22 L21 i j := by rw [hE_mul]
    _ = rectMatMul Δ L11 i j := by ring

/-- Higham equation (14.14), Method 2B obstruction wrapper:
    if the propagated block-update perturbation is larger than a proposed
    off-diagonal residual budget in one entry, then the whole off-diagonal
    residual block cannot satisfy that budget.

    This is a source-facing obstruction hinge, not the full instability
    theorem: the large propagated-delta hypothesis still has to be established
    for a concrete Method 2B instance. -/
theorem higham14_eq14_14_method2B_no_small_offdiag_residual_of_propagated_delta
    {m r : ℕ}
    (L11 X11 : Fin m → Fin m → ℝ)
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (ε : ℝ) (absBound sourceBudget : Fin r → Fin m → ℝ)
    (hSpec : Method2BBlockUpdateSpec X21_hat X22 L21 X11 ε absBound)
    (hX11_left : IsLeftInverse m L11 X11)
    {i0 : Fin r} {j0 : Fin m}
    (hLarge :
      sourceBudget i0 j0 <
        |rectMatMul
          (higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11)
          L11 i0 j0|) :
    ¬ (∀ i : Fin r, ∀ j : Fin m,
      |rectMatMul X21_hat L11 i j + rectMatMul X22 L21 i j| ≤
        sourceBudget i j) := by
  intro hSmall
  have hId :=
    higham14_eq14_14_method2B_offdiag_residual_eq_delta_mul
      L11 X11 X21_hat X22 L21 ε absBound hSpec hX11_left i0 j0
  have hEntry := hSmall i0 j0
  rw [hId] at hEntry
  exact not_lt_of_ge hEntry hLarge

/-- One-column diagonal-block specialization of the Method 2B residual
    obstruction.  In the scalar `L11` case, the propagated perturbation entry
    is the explicit product `Delta21 * L11`, so callers can supply a concrete
    scalar lower bound instead of a rectangular matrix product. -/
theorem higham14_eq14_14_method2B_no_small_offdiag_residual_of_scalar_propagated_delta
    {r : ℕ}
    (L11 X11 : Fin 1 → Fin 1 → ℝ)
    (X21_hat : Fin r → Fin 1 → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin 1 → ℝ)
    (ε : ℝ) (absBound sourceBudget : Fin r → Fin 1 → ℝ)
    (hSpec : Method2BBlockUpdateSpec X21_hat X22 L21 X11 ε absBound)
    (hX11_left : IsLeftInverse 1 L11 X11)
    {i0 : Fin r}
    (hLarge :
      sourceBudget i0 (0 : Fin 1) <
        |higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11
            i0 (0 : Fin 1) * L11 (0 : Fin 1) (0 : Fin 1)|) :
    ¬ (∀ i : Fin r, ∀ j : Fin 1,
      |rectMatMul X21_hat L11 i j + rectMatMul X22 L21 i j| ≤
        sourceBudget i j) := by
  apply
    higham14_eq14_14_method2B_no_small_offdiag_residual_of_propagated_delta
      L11 X11 X21_hat X22 L21 ε absBound sourceBudget hSpec hX11_left
      (i0 := i0) (j0 := (0 : Fin 1))
  simpa [rectMatMul] using hLarge

/-- Exact Method 2B off-diagonal block formula from the block equation
    `X21 * L11 + X22 * L21 = 0` and the diagonal-block inverse certificate
    `L11 * X11 = I`.  This is the exact algebra behind equation (14.14);
    the rounded update is represented separately by
    `higham14_method2BBlockUpdateDelta`. -/
theorem higham14_eq14_14_method2B_exact_offdiag_block_update {m r : ℕ}
    (L11 X11 : Fin m → Fin m → ℝ)
    (L21 X21 : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ)
    (hOffdiag : ∀ i : Fin r, ∀ j : Fin m,
      rectMatMul X21 L11 i j + rectMatMul X22 L21 i j = 0)
    (hX11 : IsRightInverse m L11 X11) :
    ∀ i : Fin r, ∀ j : Fin m,
      X21 i j = higham14_method2BBlockUpdateExact X22 L21 X11 i j := by
  intro i j
  have hzero :
      rectMatMul
          (fun a b => rectMatMul X21 L11 a b + rectMatMul X22 L21 a b)
          X11 i j = 0 := by
    unfold rectMatMul
    apply Finset.sum_eq_zero
    intro x _
    have hx := hOffdiag i x
    unfold rectMatMul at hx
    change (∑ k : Fin m, X21 i k * L11 k x) +
        (∑ k : Fin r, X22 i k * L21 k x) = 0 at hx
    change ((∑ k : Fin m, X21 i k * L11 k x) +
        (∑ k : Fin r, X22 i k * L21 k x)) * X11 x j = 0
    rw [hx]
    ring
  have hsplit :
      rectMatMul (rectMatMul X21 L11) X11 i j +
        rectMatMul (rectMatMul X22 L21) X11 i j = 0 := by
    simpa [rectMatMul_add_left] using hzero
  have hassoc : rectMatMul (rectMatMul X21 L11) X11 =
      rectMatMul X21 (rectMatMul L11 X11) :=
    rectMatMul_assoc X21 L11 X11
  have hright : rectMatMul L11 X11 = idMatrix m := by
    ext a b
    exact hX11 a b
  have hleft : rectMatMul (rectMatMul X21 L11) X11 i j = X21 i j := by
    rw [hassoc, hright]
    exact congrFun (congrFun (rectMatMul_id_right X21) i) j
  rw [hleft] at hsplit
  unfold higham14_method2BBlockUpdateExact
  linarith

/-- **Abstract Lemma 14.3 interface**: Method 2C left residual.

    |X̂L − I| ≤ cₙu|X̂||L|.

    Method 2C (LAPACK's xTRTRI) achieves the same left residual bound as
    the unblocked Method 2.

    This theorem is a named abstract interface: `hLeftRes` supplies the
    Method 2C block-loop residual analysis. -/
theorem triInv_method2C_left_residual (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (_hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (_hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (_hn : gammaValid fp n)
    -- Hypothesis: X̂ satisfies Method 2C spec (solve with L_jj from right,
    -- then back substitution with L_jj from right).
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j| :=
  hLeftRes

/-- Problem 14.2 / Lemma 14.3 normwise form:
    Method 2C's componentwise left-residual interface implies the corresponding
    infinity-norm residual bound. -/
theorem triInv_method2C_left_residual_normwise (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j|) :
    infNorm (fun i j =>
      ∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm X_hat * infNorm L := by
  have hComp :=
    triInv_method2C_left_residual n fp L X_hat hL_diag hLT hn hLeftRes
  exact higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (R := fun i j => ∑ k : Fin n, X_hat i k * L k j -
      if i = j then 1 else 0)
    (A := X_hat) (B := L) (gamma_nonneg fp hn) hComp

-- ============================================================
-- §14.3  Full matrix inversion via LU factorization
-- ============================================================

-- §14.3.1  Method A: solve Ax̂ⱼ = eⱼ for each column

/-- Computed inverse produced by Method A after an LU factorization: each
column solves `L_hat y = e_j`, then `U_hat x = y`. -/
noncomputable def methodAComputedInverse (fp : FPModel) (n : ℕ)
    (L_hat U_hat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    let b_j : Fin n → ℝ := fun k => if k = j then 1 else 0
    let y_hat := fl_forwardSub fp n L_hat b_j
    fl_backSub fp n U_hat y_hat i

/-- **Method A column-wise backward error** (Higham eq. 14.15).

    Method A computes X̂ ≈ A⁻¹ by solving Ax̂ⱼ = eⱼ for j = 1:n via LU.
    From Theorem 9.4, each column satisfies (A + ΔAⱼ)x̂ⱼ = eⱼ
    with |ΔAⱼ| ≤ (3γₙ + γₙ²)|L̂||Û|. -/
theorem methodA_column_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      let b_j : Fin n → ℝ := fun i => if i = j then 1 else 0
      let y_hat := fl_forwardSub fp n L_hat b_j
      let x_hat_j := fl_backSub fp n U_hat y_hat
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤ (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * x_hat_j k = b_j i := by
  intro j b_j y_hat x_hat_j
  exact lu_solve_backward_error fp n A L_hat U_hat b_j hL_diag hU_diag hLU hn

/-- Method A column-wise backward error specialized to the named computed
inverse matrix `methodAComputedInverse`. -/
theorem methodA_column_backward_error_computed_inverse (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤ (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n,
          (A i k + ΔA i k) *
            methodAComputedInverse fp n L_hat U_hat k j =
          if i = j then 1 else 0 := by
  intro j
  simpa [methodAComputedInverse] using
    methodA_column_backward_error n fp A L_hat U_hat
      hL_diag hU_diag hLU hn j

/-- Method A column-wise backward error with an exposed LU factorization
coefficient.  The LU factorization is certified at level `epsLU`, while the
forward and back triangular solves are still charged at `gamma fp n`. -/
theorem methodA_column_backward_error_factor_bound (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {epsLU : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat epsLU)
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      let b_j : Fin n → ℝ := fun i => if i = j then 1 else 0
      let y_hat := fl_forwardSub fp n L_hat b_j
      let x_hat_j := fl_backSub fp n U_hat y_hat
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤
          (epsLU + 2 * gamma fp n + gamma fp n ^ 2) *
            ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * x_hat_j k = b_j i := by
  intro j b_j y_hat x_hat_j
  exact
    lu_solve_backward_error_factor_gamma fp n A L_hat U_hat b_j
      hepsLU hL_diag hU_diag hLU hn

/-- Coefficient-exposed Method A column-wise backward error specialized to the
named computed inverse matrix `methodAComputedInverse`. -/
theorem methodA_column_backward_error_computed_inverse_factor_bound
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {epsLU : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat epsLU)
    (hn : gammaValid fp n) :
    ∀ j : Fin n,
      ∃ ΔA : Fin n → Fin n → ℝ,
        (∀ i k, |ΔA i k| ≤
          (epsLU + 2 * gamma fp n + gamma fp n ^ 2) *
            ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
        ∀ i, ∑ k : Fin n,
          (A i k + ΔA i k) *
            methodAComputedInverse fp n L_hat U_hat k j =
          if i = j then 1 else 0 := by
  intro j
  simpa [methodAComputedInverse] using
    methodA_column_backward_error_factor_bound n fp A L_hat U_hat
      hepsLU hL_diag hU_diag hLU hn j

/-- **Method A right residual** (Higham eq. 14.16).

    |AX̂ − I| ≤ c'ₙu|L̂||Û||X̂|.

    Each column has (A + ΔAⱼ)x̂ⱼ = eⱼ, so Ax̂ⱼ = eⱼ − ΔAⱼx̂ⱼ,
    hence |Ax̂ⱼ − eⱼ| = |ΔAⱼx̂ⱼ| ≤ (3γₙ+γₙ²)(|L̂||Û|)|x̂ⱼ|. -/
theorem methodA_right_residual (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_hat : Fin n → Fin n → ℝ)
    (_hn : gammaValid fp n)
    -- Each column j has backward error: (A+ΔAⱼ)x̂ⱼ = eⱼ with |ΔAⱼ| ≤ c|L̂||Û|
    (hCol : ∀ j : Fin n, ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i k, |ΔA i k| ≤ (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
      ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
          |X_hat k j| := by
  intro i j
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ := hCol j
  have hAX : ∑ k : Fin n, A i k * X_hat k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔA i k * X_hat k j) := by
    have h := hΔA_eq i
    have hsplit : ∑ k : Fin n, A i k * X_hat k j +
        ∑ k : Fin n, ΔA i k * X_hat k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hAX, abs_neg]
  calc |∑ k : Fin n, ΔA i k * X_hat k j|
      ≤ ∑ k : Fin n, |ΔA i k * X_hat k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔA i k| * |X_hat k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, ((3 * gamma fp n + gamma fp n ^ 2) *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔA_bound i k) (abs_nonneg _)
    _ = (3 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
            |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- Method A right residual with an externally supplied componentwise column
backward-error coefficient `c`. -/
theorem methodA_right_residual_of_column_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_hat : Fin n → Fin n → ℝ)
    (c : ℝ)
    (hCol : ∀ j : Fin n, ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i k, |ΔA i k| ≤ c *
        ∑ l : Fin n, |L_hat i l| * |U_hat l k|) ∧
      ∀ i, ∑ k : Fin n, (A i k + ΔA i k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      c * ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
        |X_hat k j| := by
  intro i j
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ := hCol j
  have hAX : ∑ k : Fin n, A i k * X_hat k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔA i k * X_hat k j) := by
    have h := hΔA_eq i
    have hsplit : ∑ k : Fin n, A i k * X_hat k j +
        ∑ k : Fin n, ΔA i k * X_hat k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hAX, abs_neg]
  calc |∑ k : Fin n, ΔA i k * X_hat k j|
      ≤ ∑ k : Fin n, |ΔA i k * X_hat k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔA i k| * |X_hat k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, (c *
          ∑ l : Fin n, |L_hat i l| * |U_hat l k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔA_bound i k) (abs_nonneg _)
    _ = c * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
            |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- **Method A forward error** (Higham eq. 14.17).

    |X̂ − A⁻¹| ≤ c'ₙu|A⁻¹||L̂||Û||X̂|. -/
theorem methodA_forward_error (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat X_hat : Fin n → Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (_hn : gammaValid fp n)
    -- Right residual hypothesis
    (hRes : ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
          |X_hat k j|) :
    ∀ i j : Fin n,
      |X_hat i j - A_inv i j| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k₁ : Fin n, |A_inv i k₁| *
          (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
            |X_hat k₂ j|) := by
  intro i j
  -- Define E_{k₁j} = (AX̂)_{k₁j} − δ_{k₁j}, the residual
  -- From AX̂ = I + E, multiply by A⁻¹: X̂ = A⁻¹ + A⁻¹E
  -- So X̂_{ij} − A⁻¹_{ij} = (A⁻¹E)_{ij}
  let c := 3 * gamma fp n + gamma fp n ^ 2
  have hDiff : X_hat i j - A_inv i j =
      ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) := by
    have hRHS_expand : ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) =
        ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j) -
        ∑ k₁ : Fin n, A_inv i k₁ * (if k₁ = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k₁ _; ring
    rw [hRHS_expand]
    have hSecond : ∑ k₁ : Fin n, A_inv i k₁ *
        (if k₁ = j then (1 : ℝ) else 0) = A_inv i j := by
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hFirst : ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j) = X_hat i j := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have hInvA : ∀ k₂ : Fin n,
          (∑ k₁ : Fin n, A_inv i k₁ * A k₁ k₂) = if i = k₂ then 1 else 0 :=
        fun k₂ => hInv i k₂
      simp_rw [hInvA]
      simp [Finset.mem_univ]
    rw [hFirst, hSecond]
  rw [hDiff]
  calc |∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)|
      ≤ ∑ k₁ : Fin n, |A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |A_inv i k₁| *
        |∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |A_inv i k₁| *
        (c * ∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        exact mul_le_mul_of_nonneg_left (hRes k₁ j) (abs_nonneg _)
    _ = c * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k₁ _; ring

/-- Method A forward error with an externally supplied residual coefficient
`c`. -/
theorem methodA_forward_error_of_residual_bound (n : ℕ)
    (A A_inv L_hat U_hat X_hat : Fin n → Fin n → ℝ)
    (c : ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hRes : ∀ i j : Fin n,
      |∑ k : Fin n, A i k * X_hat k j - if i = j then 1 else 0| ≤
      c * ∑ k : Fin n, (∑ l : Fin n, |L_hat i l| * |U_hat l k|) *
        |X_hat k j|) :
    ∀ i j : Fin n,
      |X_hat i j - A_inv i j| ≤
      c * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
  intro i j
  have hDiff : X_hat i j - A_inv i j =
      ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) := by
    have hRHS_expand : ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) =
        ∑ k₁ : Fin n, A_inv i k₁ * (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j) -
        ∑ k₁ : Fin n, A_inv i k₁ * (if k₁ = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k₁ _; ring
    rw [hRHS_expand]
    have hSecond : ∑ k₁ : Fin n, A_inv i k₁ *
        (if k₁ = j then (1 : ℝ) else 0) = A_inv i j := by
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    have hFirst : ∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j) = X_hat i j := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have hInvA : ∀ k₂ : Fin n,
          (∑ k₁ : Fin n, A_inv i k₁ * A k₁ k₂) = if i = k₂ then 1 else 0 :=
        fun k₂ => hInv i k₂
      simp_rw [hInvA]
      simp [Finset.mem_univ]
    rw [hFirst, hSecond]
  rw [hDiff]
  calc |∑ k₁ : Fin n, A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)|
      ≤ ∑ k₁ : Fin n, |A_inv i k₁ *
        (∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |A_inv i k₁| *
        |∑ k₂ : Fin n, A k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |A_inv i k₁| *
        (c * ∑ k₂ : Fin n,
          (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
            |X_hat k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        exact mul_le_mul_of_nonneg_left (hRes k₁ j) (abs_nonneg _)
    _ = c * ∑ k₁ : Fin n, |A_inv i k₁| *
        (∑ k₂ : Fin n, (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
          |X_hat k₂ j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k₁ _; ring

/-- Method A computed inverse entrywise forward-error certificate for the
repository nonsingular inverse, with a visible scalar budget `eta`. -/
theorem methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_budget
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {eta : ℝ}
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hBudget :
      ∀ i j : Fin n,
        (3 * gamma fp n + gamma fp n ^ 2) *
            ∑ k₁ : Fin n,
              |nonsingInv n A i k₁| *
                (∑ k₂ : Fin n,
                  (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp n L_hat U_hat k₂ j|) ≤ eta) :
    ∀ i j : Fin n,
      |nonsingInv n A i j -
          methodAComputedInverse fp n L_hat U_hat i j| ≤ eta := by
  intro i j
  have hInv : IsInverse n A (nonsingInv n A) :=
    isInverse_nonsingInv_of_det_ne_zero n A hdet
  have hCol :=
    methodA_column_backward_error_computed_inverse n fp A L_hat U_hat
      hL_diag hU_diag hLU hn
  have hRes :=
    methodA_right_residual n fp A L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) hn hCol
  have hFwd :=
    methodA_forward_error n fp A (nonsingInv n A) L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) hInv.1 hn hRes i j
  rw [abs_sub_comm]
  exact le_trans hFwd (hBudget i j)

/-- Method A computed inverse entrywise forward-error certificate with an
exposed LU factorization coefficient `epsLU`.  This is the implementation-facing
variant used when the LU factors are certified for a computed input matrix and
that input error has already been transferred into the `LUBackwardError`
coefficient. -/
theorem methodA_computed_inverse_entry_abs_sub_nonsingInv_le_of_lu_factor_budget
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    {epsLU eta : ℝ}
    (hepsLU : 0 ≤ epsLU)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat epsLU)
    (hn : gammaValid fp n)
    (hBudget :
      ∀ i j : Fin n,
        (epsLU + 2 * gamma fp n + gamma fp n ^ 2) *
            ∑ k₁ : Fin n,
              |nonsingInv n A i k₁| *
                (∑ k₂ : Fin n,
                  (∑ l : Fin n, |L_hat k₁ l| * |U_hat l k₂|) *
                    |methodAComputedInverse fp n L_hat U_hat k₂ j|) ≤ eta) :
    ∀ i j : Fin n,
      |nonsingInv n A i j -
          methodAComputedInverse fp n L_hat U_hat i j| ≤ eta := by
  intro i j
  have hInv : IsInverse n A (nonsingInv n A) :=
    isInverse_nonsingInv_of_det_ne_zero n A hdet
  have hCol :=
    methodA_column_backward_error_computed_inverse_factor_bound n fp A L_hat U_hat
      hepsLU hL_diag hU_diag hLU hn
  let c := epsLU + 2 * gamma fp n + gamma fp n ^ 2
  have hRes :=
    methodA_right_residual_of_column_bound n A L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) c hCol
  have hFwd :=
    methodA_forward_error_of_residual_bound n A (nonsingInv n A) L_hat U_hat
      (methodAComputedInverse fp n L_hat U_hat) c hInv.1 hRes i j
  rw [abs_sub_comm]
  exact le_trans hFwd (hBudget i j)

-- §14.3.2  Method B: compute U⁻¹ then solve XL̂ = X_U

/-- **Method B left residual** (Higham eq. 14.18).

    Method B: compute X_U ≈ U⁻¹ (by an analogue of Method 2 or 2C for upper
    triangular matrices), then solve for X in XL̂ = X_U by back substitution
    from the right.

    The left residual satisfies:
      |X̂A − I| ≤ c'ₙu|X̂||L̂||Û|.

    Note: eq. 14.18 is the left residual analogue of eq. 14.16.
    The LINPACK manual incorrectly states this as a right residual bound. -/
theorem methodB_left_residual (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    -- X_U satisfies right residual for U⁻¹: |X_U · Û − I| ≤ γₙ|X_U||Û|
    (hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    -- X̂ is computed by solving X̂L̂ = X_U from the right (back sub rows):
    -- |X̂L̂ − X_U| ≤ γₙ|X̂||L̂| (this is the Δ(X̂, L̂) term)
    (hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L_hat k j - X_U i j| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L_hat k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (3 * gamma fp n + gamma fp n ^ 2) *
        ∑ k₁ : Fin n, |X_hat i k₁| *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) := by
  intro i j
  let γ := gamma fp n
  -- Step 1: Decompose A = L̂Û − (L̂Û − A)
  -- X̂A = X̂L̂Û − X̂(L̂Û − A)
  -- Step 2: X̂L̂Û − I = (X̂L̂ − X_U)Û + (X_UÛ − I) = E₁Û + E₂
  -- where E₁ = X̂L̂ − X_U, E₂ = X_UÛ − I
  -- Bound |X_U| ≤ (1+γ)|X̂||L̂| from E₁ bound
  -- Total: |X̂A − I| ≤ (3γ + γ²)|X̂||L̂||Û|
  -- Abbreviate the componentwise product bound
  let B := fun i j => ∑ k₁ : Fin n, |X_hat i k₁| *
    (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)
  -- The LU backward error gives |L̂Û − A| ≤ γ|L̂||Û|
  have hLUerr := hLU.backward_bound
  -- Bound: X̂(A − L̂Û) contribution
  have hLU_contrib : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k *
        (A k j - ∑ l : Fin n, L_hat k l * U_hat l j)| ≤ γ * B i j := by
    intro i' j'
    calc |∑ k : Fin n, X_hat i' k *
          (A k j' - ∑ l : Fin n, L_hat k l * U_hat l j')|
        ≤ ∑ k : Fin n, |X_hat i' k| *
          |A k j' - ∑ l : Fin n, L_hat k l * U_hat l j'| := by
          calc _ ≤ ∑ k, |X_hat i' k * (A k j' - ∑ l, L_hat k l * U_hat l j')| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, |X_hat i' k| *
            (γ * ∑ l : Fin n, |L_hat k l| * |U_hat l j'|) := by
          apply Finset.sum_le_sum; intro k _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have h := hLUerr k j'
          rwa [abs_sub_comm] at h
      _ = γ * B i' j' := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _; ring
  -- Bound: E₁Û contribution where E₁ = X̂L̂ − X_U
  have hE1U_contrib : ∀ i j : Fin n,
      |∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) *
        U_hat k j| ≤ γ * B i j := by
    intro i' j'
    calc |∑ k : Fin n, (∑ l : Fin n, X_hat i' l * L_hat l k - X_U i' k) *
          U_hat k j'|
        ≤ ∑ k : Fin n, |∑ l : Fin n, X_hat i' l * L_hat l k - X_U i' k| *
          |U_hat k j'| := by
          calc _ ≤ ∑ k, |(∑ l, X_hat i' l * L_hat l k - X_U i' k) * U_hat k j'| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k : Fin n, (γ * ∑ l : Fin n, |X_hat i' l| * |L_hat l k|) *
          |U_hat k j'| := by
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_right (hXL_res i' k) (abs_nonneg _)
      _ = γ * B i' j' := by
          have hfact : ∀ k : Fin n,
              (γ * ∑ l, |X_hat i' l| * |L_hat l k|) * |U_hat k j'| =
              γ * ((∑ l, |X_hat i' l| * |L_hat l k|) * |U_hat k j'|) :=
            fun _ => by ring
          simp_rw [hfact, ← Finset.mul_sum, Finset.sum_mul]
          congr 1; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro l _
          simp_rw [mul_assoc]; rw [← Finset.mul_sum]
  -- Bound: E₂ contribution where E₂ = X_UÛ − I, with |X_U| ≤ (1+γ)|X̂||L̂|
  -- First bound |X_U|
  have hXU_bound : ∀ i' k : Fin n,
      |X_U i' k| ≤ (1 + γ) * ∑ l : Fin n, |X_hat i' l| * |L_hat l k| := by
    intro i' k
    have hXL_abs : |∑ l : Fin n, X_hat i' l * L_hat l k| ≤
        ∑ l : Fin n, |X_hat i' l| * |L_hat l k| := by
      calc _ ≤ ∑ l, |X_hat i' l * L_hat l k| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by apply Finset.sum_congr rfl; intro l _; exact abs_mul _ _
    have hE1 : |∑ l : Fin n, X_hat i' l * L_hat l k - X_U i' k| ≤
        γ * ∑ l : Fin n, |X_hat i' l| * |L_hat l k| := hXL_res i' k
    have key : |X_U i' k| ≤ |∑ l, X_hat i' l * L_hat l k| +
        |∑ l, X_hat i' l * L_hat l k - X_U i' k| := by
      have h := abs_add_le (X_U i' k - ∑ l, X_hat i' l * L_hat l k)
        (∑ l, X_hat i' l * L_hat l k)
      rw [sub_add_cancel] at h
      rw [abs_sub_comm] at h; linarith
    linarith
  -- Bound E₂ contribution: |E₂|_ij ≤ γ(1+γ)|X̂||L̂||Û|
  have hE2_contrib : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j -
        if i = j then (1 : ℝ) else 0| ≤
      γ * (1 + γ) * B i j := by
    intro i' j'
    calc |∑ k : Fin n, X_U i' k * U_hat k j' -
          if i' = j' then (1 : ℝ) else 0|
        ≤ γ * ∑ k : Fin n, |X_U i' k| * |U_hat k j'| := hXU_res i' j'
      _ ≤ γ * ∑ k : Fin n, ((1 + γ) * ∑ l : Fin n, |X_hat i' l| * |L_hat l k|) *
            |U_hat k j'| := by
          apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn)
          apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_right (hXU_bound i' k) (abs_nonneg _)
      _ = γ * (1 + γ) * B i' j' := by
          rw [show γ * ∑ k : Fin n,
            ((1 + γ) * ∑ l : Fin n, |X_hat i' l| * |L_hat l k|) * |U_hat k j'| =
            γ * (1 + γ) * ∑ k : Fin n,
              (∑ l : Fin n, |X_hat i' l| * |L_hat l k|) * |U_hat k j'| from by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _; ring]
          congr 1
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro l _
          simp_rw [mul_assoc]; rw [← Finset.mul_sum]
  -- Fubini: ∑_k(∑_l X̂L̂)Û = ∑_k X̂(∑_l L̂Û)
  have hFub : ∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k) * U_hat k j =
      ∑ k : Fin n, X_hat i k * ∑ l : Fin n, L_hat k l * U_hat l j := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro l _; ring
  -- Algebraic decomposition: target = E₂ + E₁Û + X̂(A−L̂Û)
  have hDecomp : ∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0) =
      (∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)) +
      (∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j) +
      (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j)) := by
    simp_rw [sub_mul, Finset.sum_sub_distrib, mul_sub, Finset.sum_sub_distrib]
    linarith [hFub]
  rw [hDecomp]
  have h1 := hE2_contrib i j
  have h2 := hE1U_contrib i j
  have h3 := hLU_contrib i j
  calc |(∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)) +
        (∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j) +
        (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j))|
      ≤ |∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)| +
        |(∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j) +
         (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j))| :=
      by rw [add_assoc]; exact abs_add_le _ _
    _ ≤ |∑ k : Fin n, X_U i k * U_hat k j - (if i = j then 1 else 0)| +
        |∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j| +
        |∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j)| := by
      have := abs_add_le (∑ k : Fin n, (∑ l : Fin n, X_hat i l * L_hat l k - X_U i k) * U_hat k j)
        (∑ k : Fin n, X_hat i k * (A k j - ∑ l : Fin n, L_hat k l * U_hat l j))
      linarith
    _ ≤ γ * (1 + γ) * B i j + γ * B i j + γ * B i j := by linarith
    _ = (3 * γ + γ ^ 2) * B i j := by ring

-- §14.3.3  Method C: solve UXL = I

/-- **Abstract Method C mixed residual interface** (Higham eq. 14.19).

    Method C solves UX̂L = I, computing X̂ a partial row and column at a time.
    The "mixed" residual satisfies:
      |ÛX̂L̂ − I| ≤ cₙu|Û||X̂||L̂|.

    From this, bounds on both the left and right residuals (weaker than A/B)
    can be obtained by multiplying by |U⁻¹| or |L⁻¹|.

    The hypothesis `hMixed` is the local Method C error analysis; later
    theorems in this file derive forward-error consequences from it. -/
theorem methodC_mixed_residual (n : ℕ) (fp : FPModel)
    (U_hat L_hat X_hat : Fin n → Fin n → ℝ)
    (_hn : gammaValid fp n)
    -- Hypothesis: X̂ is computed by Method C with the given error structure
    (hMixed : ∀ i j : Fin n,
      |∑ k₁ : Fin n, U_hat i k₁ *
        (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ j) -
          if i = j then 1 else 0| ≤
      gamma fp n * ∑ k₁ : Fin n, |U_hat i k₁| *
        (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ j|)) :
    ∀ i j : Fin n,
      |∑ k₁ : Fin n, U_hat i k₁ *
        (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ j) -
          if i = j then 1 else 0| ≤
      gamma fp n * ∑ k₁ : Fin n, |U_hat i k₁| *
        (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ j|) :=
  hMixed

/-- **Method C forward error relative to LU-inverse** (from eq. 14.19).

    From the mixed residual ÛX̂L̂ = I + E, multiplying by Û⁻¹ on the left
    and L̂⁻¹ on the right gives X̂ = Û⁻¹L̂⁻¹ + Û⁻¹EL̂⁻¹.
    The forward error relative to the LU-inverse satisfies:
      |X̂ − Û⁻¹L̂⁻¹| ≤ cₙu|Û⁻¹| · |Û||X̂||L̂| · |L̂⁻¹|. -/
theorem methodC_forward_error (n : ℕ) (fp : FPModel)
    (U_hat L_hat X_hat : Fin n → Fin n → ℝ)
    (U_inv L_inv : Fin n → Fin n → ℝ)
    (hUinv : IsLeftInverse n U_hat U_inv)
    (hLinv : IsRightInverse n L_hat L_inv)
    (_hn : gammaValid fp n)
    (hMixed : ∀ i j : Fin n,
      |∑ k₁ : Fin n, U_hat i k₁ *
        (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ j) -
          if i = j then 1 else 0| ≤
      gamma fp n * ∑ k₁ : Fin n, |U_hat i k₁| *
        (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ j|)) :
    ∀ i j : Fin n,
      |X_hat i j - matMul n U_inv L_inv i j| ≤
      gamma fp n *
        ∑ a : Fin n, |U_inv i a| *
          (∑ b : Fin n, (∑ k₁ : Fin n, |U_hat a k₁| *
            (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) *
              |L_inv b j|) := by
  intro i j
  let γ := gamma fp n
  -- Define E(a,b) = (ÛX̂L̂)_{ab} − δ_{ab}
  let E : Fin n → Fin n → ℝ := fun a b =>
    ∑ k₁ : Fin n, U_hat a k₁ * (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) -
      if a = b then 1 else 0
  -- Step 1: Apply L̂·L_inv = I to simplify ∑_b (∑_k₂ X̂·L̂)·L_inv = X̂
  have hLinv_app : ∀ k₁ : Fin n,
      ∑ b : Fin n, (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) * L_inv b j =
      X_hat k₁ j := by
    intro k₁
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [show ∀ (k₂ b : Fin n), X_hat k₁ k₂ * L_hat k₂ b * L_inv b j =
      X_hat k₁ k₂ * (L_hat k₂ b * L_inv b j) from fun _ _ => by ring]
    simp_rw [← Finset.mul_sum, hLinv _ j]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Step 2: Apply U_inv·Û = I to simplify ∑_a U_inv·(∑_k₁ Û·X̂) = X̂
  have hUinv_app :
      ∑ a : Fin n, U_inv i a * (∑ k₁ : Fin n, U_hat a k₁ * X_hat k₁ j) =
      X_hat i j := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hUinv i]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 3: Simplify ∑_b E(a,b)·L_inv(b,j) = ∑_k₁ Û(a,k₁)·X̂(k₁,j) − L_inv(a,j)
  have hEL : ∀ a : Fin n,
      ∑ b : Fin n, E a b * L_inv b j =
      ∑ k₁ : Fin n, U_hat a k₁ * X_hat k₁ j - L_inv a j := by
    intro a; simp only [E]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    congr 1
    · simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k₁ _
      simp_rw [show ∀ b : Fin n,
          U_hat a k₁ * (∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) * L_inv b j =
          U_hat a k₁ * ((∑ k₂ : Fin n, X_hat k₁ k₂ * L_hat k₂ b) * L_inv b j)
        from fun _ => by ring]
      rw [← Finset.mul_sum]
      congr 1; exact hLinv_app k₁
    · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  -- Step 4: Algebraic identity ∑_a U_inv·(∑_b E·L_inv) = X̂ − U_inv·L_inv
  have hIdentity : ∑ a : Fin n, U_inv i a * (∑ b : Fin n, E a b * L_inv b j) =
      X_hat i j - matMul n U_inv L_inv i j := by
    simp_rw [hEL, mul_sub, Finset.sum_sub_distrib]
    unfold matMul; linarith [hUinv_app]
  -- Step 5: Bound |U_inv · E · L_inv| ≤ γ · |U_inv| · |E| · |L_inv|
  rw [show X_hat i j - matMul n U_inv L_inv i j =
    ∑ a : Fin n, U_inv i a * (∑ b : Fin n, E a b * L_inv b j) from hIdentity.symm]
  calc |∑ a : Fin n, U_inv i a * (∑ b : Fin n, E a b * L_inv b j)|
      ≤ ∑ a : Fin n, |U_inv i a| * |∑ b : Fin n, E a b * L_inv b j| := by
        calc _ ≤ ∑ a, |U_inv i a * (∑ b, E a b * L_inv b j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = _ := by apply Finset.sum_congr rfl; intro a _; exact abs_mul _ _
    _ ≤ ∑ a : Fin n, |U_inv i a| *
        (∑ b : Fin n, |E a b| * |L_inv b j|) := by
        apply Finset.sum_le_sum; intro a _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc _ ≤ ∑ b, |E a b * L_inv b j| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by apply Finset.sum_congr rfl; intro b _; exact abs_mul _ _
    _ ≤ ∑ a : Fin n, |U_inv i a| *
        (∑ b : Fin n, (γ * ∑ k₁ : Fin n, |U_hat a k₁| *
          (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j|) := by
        apply Finset.sum_le_sum; intro a _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum; intro b _
        exact mul_le_mul_of_nonneg_right (hMixed a b) (abs_nonneg _)
    _ = γ * ∑ a : Fin n, |U_inv i a| *
        (∑ b : Fin n, (∑ k₁ : Fin n, |U_hat a k₁| *
          (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _
        have hfact : ∀ b : Fin n,
            (γ * ∑ k₁ : Fin n, |U_hat a k₁| *
              (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j| =
            γ * ((∑ k₁ : Fin n, |U_hat a k₁| *
              (∑ k₂ : Fin n, |X_hat k₁ k₂| * |L_hat k₂ b|)) * |L_inv b j|) :=
          fun _ => by ring
        simp_rw [hfact, ← Finset.mul_sum]; ring

-- §14.3.4  Method D: compute L⁻¹ and U⁻¹ separately, form product

/-- Product-formation perturbation for Higham's Method D, equation (14.20):
    `X_hat = X_U * X_L + Delta`. -/
noncomputable def higham14_methodDProductDelta {n : ℕ}
    (X_hat X_U X_L : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => X_hat i j - matMul n X_U X_L i j

/-- LU backward perturbation for Method D, using the repository sign convention
    `Delta_A = L_hat * U_hat - A`. -/
noncomputable def higham14_methodDLUBackwardDelta {n : ℕ}
    (A L_hat U_hat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n L_hat U_hat i j - A i j

/-- Left residual of the computed lower-triangular inverse used by Method D:
    `X_L * L_hat - I`. -/
noncomputable def higham14_methodDXLLeftResidual {n : ℕ}
    (X_L L_hat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n X_L L_hat i j - if i = j then 1 else 0

/-- Left residual of the computed upper-triangular inverse used by Method D:
    `X_U * U_hat - I`. -/
noncomputable def higham14_methodDXULeftResidual {n : ℕ}
    (X_U U_hat : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n X_U U_hat i j - if i = j then 1 else 0

/-- Higham equation (14.20), Method D product formation:
    the computed product is the exact product plus an explicit perturbation. -/
theorem higham14_eq14_20_methodD_product_decomposition {n : ℕ}
    (X_hat X_U X_L : Fin n → Fin n → ℝ) (i j : Fin n) :
    X_hat i j = matMul n X_U X_L i j +
      higham14_methodDProductDelta X_hat X_U X_L i j := by
  unfold higham14_methodDProductDelta
  ring

/-- The product perturbation in (14.20) inherits any `MatProdError` componentwise
    bound supplied by the local floating-point multiplication analysis. -/
theorem higham14_eq14_20_methodD_productDelta_bound {n : ℕ}
    (X_hat X_U X_L : Fin n → Fin n → ℝ)
    (ε : ℝ) (absProduct : Fin n → Fin n → ℝ)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) ε absProduct) :
    ∀ i j : Fin n,
      |higham14_methodDProductDelta X_hat X_U X_L i j| ≤ ε * absProduct i j := by
  intro i j
  simpa [higham14_methodDProductDelta] using hProd i j

/-- Higham equation (14.21), Method D LU substitution:
    using `A = L_hat * U_hat - Delta_A`, expand `X_hat * A`. -/
theorem higham14_eq14_21_methodD_lu_substitution {n : ℕ}
    (A L_hat U_hat X_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    ∑ k : Fin n, X_hat i k * A k j =
      ∑ k : Fin n, X_hat i k * (∑ l : Fin n, L_hat k l * U_hat l j) -
        ∑ k : Fin n, X_hat i k *
          higham14_methodDLUBackwardDelta A L_hat U_hat k j := by
  simp [higham14_methodDLUBackwardDelta, matMul, mul_sub, Finset.sum_sub_distrib]

/-- The LU perturbation in (14.21) inherits the componentwise LU backward-error
    bound. -/
theorem higham14_eq14_21_methodD_luDelta_bound {n : ℕ}
    (A L_hat U_hat : Fin n → Fin n → ℝ) (ε : ℝ)
    (hLU : LUBackwardError n A L_hat U_hat ε) :
    ∀ i j : Fin n,
      |higham14_methodDLUBackwardDelta A L_hat U_hat i j| ≤
        ε * ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
  intro i j
  simpa [higham14_methodDLUBackwardDelta, matMul] using hLU.backward_bound i j

/-- Higham equation (14.22), Method D left-residual expansion.

    With the perturbations from (14.20) and (14.21), the left residual splits
    into the upper-inverse residual, the lower-inverse residual propagated
    through `X_U` and `U_hat`, the product-formation perturbation, and the LU
    backward perturbation. -/
theorem higham14_eq14_22_methodD_left_residual_expansion {n : ℕ}
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    ∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0) =
      higham14_methodDXULeftResidual X_U U_hat i j +
      ∑ k₁ : Fin n, X_U i k₁ *
        (∑ k₂ : Fin n,
          higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j) +
      ∑ k₁ : Fin n, higham14_methodDProductDelta X_hat X_U X_L i k₁ *
        (∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j) -
      ∑ k : Fin n, X_hat i k *
        higham14_methodDLUBackwardDelta A L_hat U_hat k j := by
  have hAssoc :
      ∑ k : Fin n, (∑ l : Fin n, X_U i l * X_L l k) *
          (∑ m : Fin n, L_hat k m * U_hat m j) =
        ∑ k : Fin n, X_U i k *
          (∑ l : Fin n, (∑ m : Fin n, X_L k m * L_hat m l) * U_hat l j) := by
    have h1 :
        matMul n (matMul n X_U X_L) (matMul n L_hat U_hat) =
          matMul n X_U (matMul n X_L (matMul n L_hat U_hat)) :=
      matMul_assoc n X_U X_L (matMul n L_hat U_hat)
    have h2 :
        matMul n X_L (matMul n L_hat U_hat) =
          matMul n (matMul n X_L L_hat) U_hat :=
      (matMul_assoc n X_L L_hat U_hat).symm
    have h :
        matMul n (matMul n X_U X_L) (matMul n L_hat U_hat) =
          matMul n X_U (matMul n (matMul n X_L L_hat) U_hat) := by
      rw [h1, h2]
    exact congrFun (congrFun h i) j
  have hXU_res_expand :
      higham14_methodDXULeftResidual X_U U_hat i j +
        ∑ k₁ : Fin n, X_U i k₁ *
          (∑ k₂ : Fin n,
            higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j) =
        ∑ k : Fin n, X_U i k *
          (∑ l : Fin n, (∑ m : Fin n, X_L k m * L_hat m l) * U_hat l j) -
          (if i = j then 1 else 0) := by
    simp [higham14_methodDXULeftResidual, higham14_methodDXLLeftResidual,
      matMul, sub_mul, mul_sub, Finset.sum_sub_distrib]
  have hXhat_decomp :
      ∑ k : Fin n, X_hat i k * (∑ l : Fin n, L_hat k l * U_hat l j) =
        ∑ k : Fin n, (∑ l : Fin n, X_U i l * X_L l k) *
          (∑ m : Fin n, L_hat k m * U_hat m j) +
        ∑ k : Fin n, higham14_methodDProductDelta X_hat X_U X_L i k *
          (∑ m : Fin n, L_hat k m * U_hat m j) := by
    simp [higham14_methodDProductDelta, matMul, sub_mul,
      Finset.sum_sub_distrib]
  have hA := higham14_eq14_21_methodD_lu_substitution A L_hat U_hat X_hat i j
  rw [hA]
  rw [hXhat_decomp]
  rw [hAssoc]
  linarith [hXU_res_expand]

/-- Higham equation (14.22), Method D:
    the exact residual expansion gives an unconditional componentwise
    absolute-value budget by the triangle inequality. -/
theorem higham14_eq14_22_methodD_left_residual_abs_le_expanded_terms {n : ℕ}
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
      |higham14_methodDXULeftResidual X_U U_hat i j| +
      ∑ k₁ : Fin n, |X_U i k₁| *
        (∑ k₂ : Fin n,
          |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| * |U_hat k₂ j|) +
      ∑ k₁ : Fin n,
        |higham14_methodDProductDelta X_hat X_U X_L i k₁| *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) +
      ∑ k : Fin n,
        |X_hat i k| * |higham14_methodDLUBackwardDelta A L_hat U_hat k j| := by
  rw [higham14_eq14_22_methodD_left_residual_expansion]
  let rU := higham14_methodDXULeftResidual X_U U_hat i j
  let rL := ∑ k₁ : Fin n, X_U i k₁ *
    (∑ k₂ : Fin n,
      higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j)
  let rP := ∑ k₁ : Fin n,
    higham14_methodDProductDelta X_hat X_U X_L i k₁ *
      (∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j)
  let rA := ∑ k : Fin n,
    X_hat i k * higham14_methodDLUBackwardDelta A L_hat U_hat k j
  let bL := ∑ k₁ : Fin n, |X_U i k₁| *
    (∑ k₂ : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| * |U_hat k₂ j|)
  let bP := ∑ k₁ : Fin n,
    |higham14_methodDProductDelta X_hat X_U X_L i k₁| *
      (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)
  let bA := ∑ k : Fin n,
    |X_hat i k| * |higham14_methodDLUBackwardDelta A L_hat U_hat k j|
  change |rU + rL + rP - rA| ≤ |rU| + bL + bP + bA
  have hsplit : |rU + rL + rP - rA| ≤ |rU| + |rL| + |rP| + |rA| := by
    calc
      |rU + rL + rP - rA| = |((rU + rL) + rP) + (-rA)| := by ring_nf
      _ ≤ |(rU + rL) + rP| + |-rA| := abs_add_le _ _
      _ ≤ (|rU + rL| + |rP|) + |rA| := by
        have h := abs_add_le (rU + rL) rP
        rw [abs_neg]
        linarith
      _ ≤ ((|rU| + |rL|) + |rP|) + |rA| := by
        have h := abs_add_le rU rL
        linarith
      _ = |rU| + |rL| + |rP| + |rA| := by ring
  have hLinner : ∀ k₁ : Fin n,
      |∑ k₂ : Fin n,
        higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j| ≤
        ∑ k₂ : Fin n,
          |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| * |U_hat k₂ j| := by
    intro k₁
    calc
      |∑ k₂ : Fin n,
        higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j|
          ≤ ∑ k₂ : Fin n,
              |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k₂ : Fin n,
            |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| * |U_hat k₂ j| :=
          Finset.sum_abs_mul
            (fun k₂ : Fin n => higham14_methodDXLLeftResidual X_L L_hat k₁ k₂)
            (fun k₂ : Fin n => U_hat k₂ j)
  have hL : |rL| ≤ bL := by
    dsimp [rL, bL]
    calc
      |∑ k₁ : Fin n, X_U i k₁ *
        (∑ k₂ : Fin n,
          higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j)|
          ≤ ∑ k₁ : Fin n,
              |X_U i k₁ *
                (∑ k₂ : Fin n,
                  higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ *
                    U_hat k₂ j)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k₁ : Fin n, |X_U i k₁| *
            |∑ k₂ : Fin n,
              higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j| := by
          apply Finset.sum_congr rfl
          intro k₁ _
          exact abs_mul (X_U i k₁)
            (∑ k₂ : Fin n,
              higham14_methodDXLLeftResidual X_L L_hat k₁ k₂ * U_hat k₂ j)
      _ ≤ ∑ k₁ : Fin n, |X_U i k₁| *
            (∑ k₂ : Fin n,
              |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| *
                |U_hat k₂ j|) := by
          apply Finset.sum_le_sum
          intro k₁ _
          exact mul_le_mul_of_nonneg_left (hLinner k₁) (abs_nonneg _)
  have hPinner : ∀ k₁ : Fin n,
      |∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j| ≤
        ∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j| := by
    intro k₁
    calc
      |∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j|
          ≤ ∑ k₂ : Fin n, |L_hat k₁ k₂ * U_hat k₂ j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j| :=
          Finset.sum_abs_mul (fun k₂ : Fin n => L_hat k₁ k₂)
            (fun k₂ : Fin n => U_hat k₂ j)
  have hP : |rP| ≤ bP := by
    dsimp [rP, bP]
    calc
      |∑ k₁ : Fin n,
        higham14_methodDProductDelta X_hat X_U X_L i k₁ *
          (∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j)|
          ≤ ∑ k₁ : Fin n,
              |higham14_methodDProductDelta X_hat X_U X_L i k₁ *
                (∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k₁ : Fin n,
            |higham14_methodDProductDelta X_hat X_U X_L i k₁| *
              |∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j| := by
          apply Finset.sum_congr rfl
          intro k₁ _
          exact abs_mul (higham14_methodDProductDelta X_hat X_U X_L i k₁)
            (∑ k₂ : Fin n, L_hat k₁ k₂ * U_hat k₂ j)
      _ ≤ ∑ k₁ : Fin n,
            |higham14_methodDProductDelta X_hat X_U X_L i k₁| *
              (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) := by
          apply Finset.sum_le_sum
          intro k₁ _
          exact mul_le_mul_of_nonneg_left (hPinner k₁) (abs_nonneg _)
  have hA : |rA| ≤ bA := by
    dsimp [rA, bA]
    calc
      |∑ k : Fin n,
        X_hat i k * higham14_methodDLUBackwardDelta A L_hat U_hat k j|
          ≤ ∑ k : Fin n,
              |X_hat i k * higham14_methodDLUBackwardDelta A L_hat U_hat k j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n,
            |X_hat i k| * |higham14_methodDLUBackwardDelta A L_hat U_hat k j| :=
          Finset.sum_abs_mul (fun k : Fin n => X_hat i k)
            (fun k : Fin n => higham14_methodDLUBackwardDelta A L_hat U_hat k j)
  linarith

/-- Higham equation (14.23), dependency form:
    combine the exact (14.22) residual budget with the already exposed
    product, LU, and triangular-inverse componentwise error hypotheses.  This
    leaves only the scalar simplification to the printed `(4γ + 2γ^2)` envelope
    open. -/
theorem higham14_eq14_23_methodD_left_residual_expanded_budget {n : ℕ}
    (fp : FPModel)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j| +
        ∑ k₁ : Fin n, |X_U i k₁| *
          (∑ k₂ : Fin n,
            (gamma fp n * ∑ l : Fin n, |X_L k₁ l| * |L_hat l k₂|) *
              |U_hat k₂ j|) +
        ∑ k₁ : Fin n,
          (gamma fp n * ∑ l : Fin n, |X_U i l| * |X_L l k₁|) *
            (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) +
        ∑ k : Fin n,
          |X_hat i k| *
            (gamma fp n * ∑ l : Fin n, |L_hat k l| * |U_hat l j|) := by
  intro i j
  have hbase :=
    higham14_eq14_22_methodD_left_residual_abs_le_expanded_terms
      A L_hat U_hat X_U X_L X_hat i j
  have hU := hXU_res i j
  have hL :
      (∑ k₁ : Fin n, |X_U i k₁| *
        (∑ k₂ : Fin n,
          |higham14_methodDXLLeftResidual X_L L_hat k₁ k₂| * |U_hat k₂ j|)) ≤
      ∑ k₁ : Fin n, |X_U i k₁| *
        (∑ k₂ : Fin n,
          (gamma fp n * ∑ l : Fin n, |X_L k₁ l| * |L_hat l k₂|) *
            |U_hat k₂ j|) := by
    apply Finset.sum_le_sum
    intro k₁ _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Finset.sum_le_sum
    intro k₂ _
    exact mul_le_mul_of_nonneg_right (hXL_res k₁ k₂) (abs_nonneg _)
  have hP :
      (∑ k₁ : Fin n,
        |higham14_methodDProductDelta X_hat X_U X_L i k₁| *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)) ≤
      ∑ k₁ : Fin n,
        (gamma fp n * ∑ l : Fin n, |X_U i l| * |X_L l k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) := by
    apply Finset.sum_le_sum
    intro k₁ _
    apply mul_le_mul_of_nonneg_right
      (higham14_eq14_20_methodD_productDelta_bound X_hat X_U X_L
        (gamma fp n) (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)
        hProd i k₁)
    exact Finset.sum_nonneg fun k₂ _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hA :
      (∑ k : Fin n,
        |X_hat i k| * |higham14_methodDLUBackwardDelta A L_hat U_hat k j|) ≤
      ∑ k : Fin n,
        |X_hat i k| *
          (gamma fp n * ∑ l : Fin n, |L_hat k l| * |U_hat l j|) := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left
      (higham14_eq14_21_methodD_luDelta_bound A L_hat U_hat
        (gamma fp n) hLU k j)
      (abs_nonneg _)
  linarith

/-- Method D absolute-product associativity:
    `|X_U||X_L||L_hat||U_hat|` can be read either as the source product
    `( |X_U||X_L| ) ( |L_hat||U_hat| )` or as
    `|X_U| ( |X_L||L_hat| ) |U_hat|`. -/
theorem higham14_methodD_abs_product_assoc {n : ℕ}
    (X_U X_L L_hat U_hat : Fin n → Fin n → ℝ) (i j : Fin n) :
    (∑ q : Fin n, |X_U i q| *
        (∑ r : Fin n,
          (∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j|)) =
      ∑ p : Fin n,
        (∑ q : Fin n, |X_U i q| * |X_L q p|) *
          (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := by
  let XUa := absMatrix n X_U
  let XLa := absMatrix n X_L
  let La := absMatrix n L_hat
  let Ua := absMatrix n U_hat
  have hassoc₁ :
      matMul n (matMul n XUa XLa) (matMul n La Ua) =
        matMul n XUa (matMul n XLa (matMul n La Ua)) :=
    matMul_assoc n XUa XLa (matMul n La Ua)
  have hassoc₂ :
      matMul n XLa (matMul n La Ua) =
        matMul n (matMul n XLa La) Ua :=
    (matMul_assoc n XLa La Ua).symm
  have hassoc :
      matMul n (matMul n XUa XLa) (matMul n La Ua) =
        matMul n XUa (matMul n (matMul n XLa La) Ua) := by
    rw [hassoc₁, hassoc₂]
  have hentry := congrFun (congrFun hassoc i) j
  simpa [XUa, XLa, La, Ua, matMul, absMatrix, mul_assoc, mul_left_comm,
    mul_comm] using hentry.symm

/-- Method D diagonal lower bound:
    a componentwise left-residual certificate for `X_L * L_hat - I` implies
    `1 <= (1+gamma) * (|X_L||L_hat|)_{qq}` on each diagonal. -/
theorem higham14_methodD_abs_XL_L_diag_ge_inv_scale {n : ℕ}
    {γ : ℝ} (X_L L_hat : Fin n → Fin n → ℝ)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        γ * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (q : Fin n) :
    1 ≤ (1 + γ) * ∑ p : Fin n, |X_L q p| * |L_hat p q| := by
  let S := ∑ p : Fin n, |X_L q p| * |L_hat p q|
  let x := matMul n X_L L_hat q q
  have hx_abs : |x| ≤ S := by
    calc
      |x| = |∑ p : Fin n, X_L q p * L_hat p q| := by
        simp [x, matMul]
      _ ≤ ∑ p : Fin n, |X_L q p * L_hat p q| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = S := by
        simp [S]
  have hres : |x - 1| ≤ γ * S := by
    simpa [x, S, higham14_methodDXLLeftResidual, matMul] using hXL_res q q
  have htri : (1 : ℝ) ≤ |x| + |x - 1| := by
    have h := abs_add_le x (1 - x)
    have hone : |(1 : ℝ)| ≤ |x| + |1 - x| := by
      calc
        |(1 : ℝ)| = |x + (1 - x)| := by
          congr 1
          ring_nf
        _ ≤ |x| + |1 - x| := h
    simpa [abs_of_nonneg zero_le_one, abs_sub_comm] using hone
  calc
    (1 : ℝ) ≤ |x| + |x - 1| := htri
    _ ≤ S + γ * S := add_le_add hx_abs hres
    _ = (1 + γ) * S := by ring_nf

/-- Method D scalar bridge:
    the direct upper-residual product `|X_U||U_hat|` is dominated by
    `(1+gamma)|X_U||X_L||L_hat||U_hat|` when the lower inverse has the
    componentwise left-residual certificate. -/
theorem higham14_methodD_abs_XU_U_le_scaled_abs_product {n : ℕ}
    {γ : ℝ} (hγ : 0 ≤ γ)
    (X_U X_L L_hat U_hat : Fin n → Fin n → ℝ)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        γ * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (i j : Fin n) :
    (∑ q : Fin n, |X_U i q| * |U_hat q j|) ≤
      (1 + γ) *
        ∑ p : Fin n,
          (∑ q : Fin n, |X_U i q| * |X_L q p|) *
            (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := by
  let D := ∑ q : Fin n,
    |X_U i q| *
      ((∑ p : Fin n, |X_L q p| * |L_hat p q|) * |U_hat q j|)
  have hterm : (∑ q : Fin n, |X_U i q| * |U_hat q j|) ≤
      (1 + γ) * D := by
    calc
      (∑ q : Fin n, |X_U i q| * |U_hat q j|)
          ≤ ∑ q : Fin n,
              (1 + γ) *
                (|X_U i q| *
                  ((∑ p : Fin n, |X_L q p| * |L_hat p q|) *
                    |U_hat q j|)) := by
            apply Finset.sum_le_sum
            intro q _
            have hdiag :=
              higham14_methodD_abs_XL_L_diag_ge_inv_scale
                X_L L_hat hXL_res q
            have hnonneg : 0 ≤ |X_U i q| * |U_hat q j| :=
              mul_nonneg (abs_nonneg _) (abs_nonneg _)
            have hmul := mul_le_mul_of_nonneg_right hdiag hnonneg
            nlinarith [hmul]
      _ = (1 + γ) * D := by
            simp [D, Finset.mul_sum]
  have hD_le_product : D ≤
      ∑ q : Fin n, |X_U i q| *
        (∑ r : Fin n,
          (∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j|) := by
    apply Finset.sum_le_sum
    intro q _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hnonneg_r : ∀ r ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j| := by
      intro r _
      exact mul_nonneg
        (Finset.sum_nonneg fun p _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (abs_nonneg _)
    simpa using Finset.single_le_sum hnonneg_r (Finset.mem_univ q)
  have hscale : (1 + γ) * D ≤
      (1 + γ) *
        ∑ q : Fin n, |X_U i q| *
          (∑ r : Fin n,
            (∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j|) :=
    mul_le_mul_of_nonneg_left hD_le_product (by nlinarith)
  have hassoc :=
    higham14_methodD_abs_product_assoc X_U X_L L_hat U_hat i j
  calc
    (∑ q : Fin n, |X_U i q| * |U_hat q j|)
        ≤ (1 + γ) * D := hterm
    _ ≤ (1 + γ) *
        ∑ q : Fin n, |X_U i q| *
          (∑ r : Fin n,
            (∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j|) := hscale
    _ = (1 + γ) *
        ∑ p : Fin n,
          (∑ q : Fin n, |X_U i q| * |X_L q p|) *
            (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := by
          rw [hassoc]

/-- The product-formation certificate gives a usable absolute bound on entries
    of the computed Method D product. -/
theorem higham14_methodD_abs_Xhat_le_scaled_abs_product {n : ℕ}
    {γ : ℝ} (X_hat X_U X_L : Fin n → Fin n → ℝ)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) γ
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|))
    (i j : Fin n) :
    |X_hat i j| ≤
      (1 + γ) * ∑ k : Fin n, |X_U i k| * |X_L k j| := by
  let S := ∑ k : Fin n, |X_U i k| * |X_L k j|
  let x := matMul n X_U X_L i j
  have hx_abs : |x| ≤ S := by
    calc
      |x| = |∑ k : Fin n, X_U i k * X_L k j| := by
        simp [x, matMul]
      _ ≤ ∑ k : Fin n, |X_U i k * X_L k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = S := by
        simp [S]
  have hdiff : |X_hat i j - x| ≤ γ * S := by
    simpa [x, S] using hProd i j
  calc
    |X_hat i j| = |x + (X_hat i j - x)| := by ring_nf
    _ ≤ |x| + |X_hat i j - x| := abs_add_le _ _
    _ ≤ S + γ * S := add_le_add hx_abs hdiff
    _ = (1 + γ) * S := by ring_nf

/-- Higham equation (14.23), scalar coefficient form:
    the expanded Method D budget from (14.22), together with the lower/upper
    triangular inverse residual certificates, product error, and LU backward
    error, implies the printed `(4γ + 2γ^2)` componentwise envelope. -/
theorem higham14_eq14_23_methodD_left_residual_bound_from_expanded_budget {n : ℕ}
    (fp : FPModel)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          ∑ p : Fin n,
            (∑ q : Fin n, |X_U i q| * |X_L q p|) *
              (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := by
  intro i j
  let γ := gamma fp n
  let P :=
    ∑ p : Fin n,
      (∑ q : Fin n, |X_U i q| * |X_L q p|) *
        (∑ r : Fin n, |L_hat p r| * |U_hat r j|)
  let Uterm := γ * ∑ q : Fin n, |X_U i q| * |U_hat q j|
  let Lterm := ∑ q : Fin n, |X_U i q| *
    (∑ r : Fin n,
      (γ * ∑ p : Fin n, |X_L q p| * |L_hat p r|) * |U_hat r j|)
  let Pterm := ∑ p : Fin n,
    (γ * ∑ q : Fin n, |X_U i q| * |X_L q p|) *
      (∑ r : Fin n, |L_hat p r| * |U_hat r j|)
  let Aterm := ∑ p : Fin n,
    |X_hat i p| * (γ * ∑ r : Fin n, |L_hat p r| * |U_hat r j|)
  have hγ : 0 ≤ γ := gamma_nonneg fp hn
  have hbase :
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        Uterm + Lterm + Pterm + Aterm := by
    simpa [γ, Uterm, Lterm, Pterm, Aterm] using
      higham14_eq14_23_methodD_left_residual_expanded_budget
        fp A L_hat U_hat X_U X_L X_hat hLU hXL_res hXU_res hProd i j
  have hU_core :
      (∑ q : Fin n, |X_U i q| * |U_hat q j|) ≤ (1 + γ) * P := by
    simpa [γ, P] using
      higham14_methodD_abs_XU_U_le_scaled_abs_product
        hγ X_U X_L L_hat U_hat hXL_res i j
  have hU : Uterm ≤ (γ * (1 + γ)) * P := by
    calc
      Uterm ≤ γ * ((1 + γ) * P) := by
        simpa [Uterm] using mul_le_mul_of_nonneg_left hU_core hγ
      _ = (γ * (1 + γ)) * P := by ring_nf
  have hassoc := higham14_methodD_abs_product_assoc X_U X_L L_hat U_hat i j
  have hL_eq : Lterm = γ * P := by
    calc
      Lterm =
          γ * (∑ q : Fin n, |X_U i q| *
            (∑ r : Fin n,
              (∑ p : Fin n, |X_L q p| * |L_hat p r|) *
                |U_hat r j|)) := by
            simp [Lterm, Finset.mul_sum, mul_assoc,
              mul_left_comm, mul_comm]
      _ = γ * P := by
            rw [hassoc]
  have hL : Lterm ≤ γ * P := le_of_eq hL_eq
  have hPterm_eq : Pterm = γ * P := by
    simp [Pterm, P, Finset.mul_sum, Finset.sum_mul]
    ring_nf
  have hPterm : Pterm ≤ γ * P := le_of_eq hPterm_eq
  have hA_step : Aterm ≤
      ∑ p : Fin n,
        ((1 + γ) * ∑ q : Fin n, |X_U i q| * |X_L q p|) *
          (γ * ∑ r : Fin n, |L_hat p r| * |U_hat r j|) := by
    apply Finset.sum_le_sum
    intro p _
    apply mul_le_mul_of_nonneg_right
      (higham14_methodD_abs_Xhat_le_scaled_abs_product
        X_hat X_U X_L hProd i p)
    exact mul_nonneg hγ
      (Finset.sum_nonneg fun r _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hA_rhs_eq :
      (∑ p : Fin n,
        ((1 + γ) * ∑ q : Fin n, |X_U i q| * |X_L q p|) *
          (γ * ∑ r : Fin n, |L_hat p r| * |U_hat r j|)) =
        (γ * (1 + γ)) * P := by
    simp [P, Finset.mul_sum, Finset.sum_mul]
    ring_nf
  have hA : Aterm ≤ (γ * (1 + γ)) * P :=
    hA_step.trans (le_of_eq hA_rhs_eq)
  calc
    |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)|
        ≤ Uterm + Lterm + Pterm + Aterm := hbase
    _ ≤ (γ * (1 + γ)) * P + γ * P + γ * P +
        (γ * (1 + γ)) * P := by
          nlinarith [hU, hL, hPterm, hA]
    _ = (4 * γ + 2 * γ ^ 2) * P := by ring_nf

/-- Higham, 2nd ed., Chapter 14, equation (14.23), Method D:
    source-facing local-certificate route to the printed scalar coefficient.

    This wrapper exposes the proved path from the LU backward-error certificate,
    lower/upper triangular inverse residual certificates, and product-error
    certificate directly to the `(4γ + 2γ^2)` left-residual envelope.  The
    remaining source dependency is upstream: deriving the triangular inverse
    residual certificates for the chosen Method 2/2C kernels. -/
theorem higham14_eq14_23_methodD_left_residual_bound_of_local_certificates
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - (if i = j then 1 else 0)| ≤
        (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          ∑ p : Fin n,
            (∑ q : Fin n, |X_U i q| * |X_L q p|) *
              (∑ r : Fin n, |L_hat p r| * |U_hat r j|) :=
  higham14_eq14_23_methodD_left_residual_bound_from_expanded_budget
    fp A L_hat U_hat X_U X_L X_hat hLU hn hXL_res hXU_res hProd

/-- Higham, 2nd ed., Chapter 14, equation (14.23), Method D:
    normwise companion to the local-certificate residual route.

    The componentwise `(4γ + 2γ^2)` envelope above implies the corresponding
    infinity-norm bound with the two source absolute products retained. -/
theorem higham14_eq14_23_methodD_left_residual_infNorm_of_local_certificates
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        infNorm (matMul n (absMatrix n X_U) (absMatrix n X_L)) *
          infNorm (matMul n (absMatrix n L_hat) (absMatrix n U_hat)) := by
  let XUL := matMul n (absMatrix n X_U) (absMatrix n X_L)
  let LU := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  have hComp0 :=
    higham14_eq14_23_methodD_left_residual_bound_of_local_certificates
      n fp A L_hat U_hat X_U X_L X_hat hLU hn hXL_res hXU_res hProd
  have hCoeff_nonneg : 0 ≤ 4 * gamma fp n + 2 * gamma fp n ^ 2 := by
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    nlinarith [sq_nonneg (gamma fp n)]
  have hXUL_nonneg : ∀ i p : Fin n, 0 ≤ XUL i p := by
    intro i p
    simp [XUL, matMul, absMatrix,
      Finset.sum_nonneg, mul_nonneg, abs_nonneg]
  have hLU_nonneg : ∀ p j : Fin n, 0 ≤ LU p j := by
    intro p j
    simp [LU, matMul, absMatrix,
      Finset.sum_nonneg, mul_nonneg, abs_nonneg]
  have hComp : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
        (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          ∑ p : Fin n, |XUL i p| * |LU p j| := by
    intro i j
    calc
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0|
          ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
            ∑ p : Fin n,
              (∑ q : Fin n, |X_U i q| * |X_L q p|) *
                (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := hComp0 i j
      _ = (4 * gamma fp n + 2 * gamma fp n ^ 2) *
            ∑ p : Fin n, |XUL i p| * |LU p j| := by
          congr 1
          apply Finset.sum_congr rfl
          intro p _
          rw [abs_of_nonneg (hXUL_nonneg i p),
            abs_of_nonneg (hLU_nonneg p j)]
          rfl
  simpa [XUL, LU] using
    higham14_infNorm_le_of_componentwise_matmul_bound hn0
      (R := fun i j : Fin n =>
        ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0)
      (A := XUL) (B := LU) hCoeff_nonneg hComp

/-- Higham, 2nd ed., Chapter 14, equation (14.23), Method D:
    product-of-norms companion to the local-certificate residual route.

    This is the coarser but simpler infinity-norm form obtained by applying
    submultiplicativity to the two retained absolute-product norms. -/
theorem higham14_eq14_23_methodD_left_residual_infNorm_product_of_local_certificates
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (A L_hat U_hat X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |higham14_methodDXLLeftResidual X_L L_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |higham14_methodDXULeftResidual X_U U_hat i j| ≤
        gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|)) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        infNorm X_U * infNorm X_L * infNorm L_hat * infNorm U_hat := by
  let XUL := matMul n (absMatrix n X_U) (absMatrix n X_L)
  let LU := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  have hRetained :=
    higham14_eq14_23_methodD_left_residual_infNorm_of_local_certificates
      n hn0 fp A L_hat U_hat X_U X_L X_hat hLU hn hXL_res hXU_res hProd
  have hCoeff_nonneg : 0 ≤ 4 * gamma fp n + 2 * gamma fp n ^ 2 := by
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    nlinarith [sq_nonneg (gamma fp n)]
  have hXUL :
      infNorm XUL ≤ infNorm X_U * infNorm X_L := by
    simpa [XUL, infNorm_absMatrix hn0 X_U, infNorm_absMatrix hn0 X_L] using
      infNorm_matMul_le hn0 (absMatrix n X_U) (absMatrix n X_L)
  have hLUprod :
      infNorm LU ≤ infNorm L_hat * infNorm U_hat := by
    simpa [LU, infNorm_absMatrix hn0 L_hat, infNorm_absMatrix hn0 U_hat] using
      infNorm_matMul_le hn0 (absMatrix n L_hat) (absMatrix n U_hat)
  have hXUNonneg : 0 ≤ infNorm X_U := infNorm_nonneg X_U
  have hXLNonneg : 0 ≤ infNorm X_L := infNorm_nonneg X_L
  have hXULProdNonneg : 0 ≤ infNorm X_U * infNorm X_L :=
    mul_nonneg hXUNonneg hXLNonneg
  calc
    infNorm (fun i j : Fin n =>
        ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0)
        ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          infNorm XUL * infNorm LU := by
            simpa [XUL, LU] using hRetained
    _ ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          (infNorm X_U * infNorm X_L) * infNorm LU := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hXUL hCoeff_nonneg)
              (infNorm_nonneg LU)
    _ ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          (infNorm X_U * infNorm X_L) *
            (infNorm L_hat * infNorm U_hat) := by
            exact mul_le_mul_of_nonneg_left hLUprod
              (mul_nonneg hCoeff_nonneg hXULProdNonneg)
    _ = (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          infNorm X_U * infNorm X_L * infNorm L_hat * infNorm U_hat := by
            ring

/-- **Abstract Method D left residual interface** (Higham eq. 14.20–14.23).

    Method D: compute X_L ≈ L⁻¹ and X_U ≈ U⁻¹ separately,
    then form X̂ = fl(X_U · X_L).

    From eq. 14.20: X̂ = X_U · X_L + Δ(X_U, X_L).
    The left residual satisfies (eq. 14.23):
      |X̂A − I| ≤ c''ₙu|U⁻¹||L⁻¹||L̂||Û|.

    This theorem records the named residual contract once the separate
    triangular-inverse and matrix-product error terms have been combined by an
    external/local Method D analysis. -/
theorem methodD_left_residual (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_L X_hat : Fin n → Fin n → ℝ)
    (_hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (_hn : gammaValid fp n)
    -- X_L has left residual: |X_L · L̂ − I| ≤ γₙ|X_L||L̂|
    (_hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_L i k * L_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    -- X_U has right residual: |Û · X_U − I| ≤ γₙ|Û||X_U|
    -- (or equivalently left residual |X_U · Û − I| ≤ γₙ|X_U||Û|)
    (_hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    -- X̂ = fl(X_U · X_L) with product error
    (_hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|))
    -- The left residual bound, combining all four error terms.
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) :=
  hLeftRes

/-- Source-facing Higham equation (14.23) wrapper for the Method D left-residual
    bound.  The detailed floating-point composition of the terms in (14.22) is
    still supplied as the local hypothesis `hLeftRes`, while (14.20)--(14.22)
    are exported above as exact algebra. -/
theorem higham14_eq14_23_methodD_left_residual_bound (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_L i k * L_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|))
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|) :=
  methodD_left_residual n fp A L_hat U_hat X_U X_L X_hat
    hLU hn hXL_res hXU_res hProd hLeftRes

/-- Source-facing Higham equation (14.23), Method D:
    infinity-norm companion to `higham14_eq14_23_methodD_left_residual_bound`.

    This version keeps the two absolute-product matrix norms retained, matching
    the componentwise product structure supplied by the compatibility
    hypothesis `hLeftRes`. -/
theorem higham14_eq14_23_methodD_left_residual_infNorm_bound
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_L i k * L_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|))
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        infNorm (matMul n (absMatrix n X_U) (absMatrix n X_L)) *
          infNorm (matMul n (absMatrix n L_hat) (absMatrix n U_hat)) := by
  let XUL := matMul n (absMatrix n X_U) (absMatrix n X_L)
  let LU := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  have hComp0 :=
    higham14_eq14_23_methodD_left_residual_bound
      n fp A L_hat U_hat X_U X_L X_hat hLU hn hXL_res hXU_res hProd hLeftRes
  have hCoeff_nonneg : 0 ≤ 4 * gamma fp n + 2 * gamma fp n ^ 2 := by
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    nlinarith [sq_nonneg (gamma fp n)]
  have hXUL_nonneg : ∀ i p : Fin n, 0 ≤ XUL i p := by
    intro i p
    simp [XUL, matMul, absMatrix,
      Finset.sum_nonneg, mul_nonneg, abs_nonneg]
  have hLU_nonneg : ∀ p j : Fin n, 0 ≤ LU p j := by
    intro p j
    simp [LU, matMul, absMatrix,
      Finset.sum_nonneg, mul_nonneg, abs_nonneg]
  have hComp : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
        (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          ∑ p : Fin n, |XUL i p| * |LU p j| := by
    intro i j
    calc
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0|
          ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
            ∑ p : Fin n,
              (∑ q : Fin n, |X_U i q| * |X_L q p|) *
                (∑ r : Fin n, |L_hat p r| * |U_hat r j|) := hComp0 i j
      _ = (4 * gamma fp n + 2 * gamma fp n ^ 2) *
            ∑ p : Fin n, |XUL i p| * |LU p j| := by
          congr 1
          apply Finset.sum_congr rfl
          intro p _
          rw [abs_of_nonneg (hXUL_nonneg i p),
            abs_of_nonneg (hLU_nonneg p j)]
          rfl
  simpa [XUL, LU] using
    higham14_infNorm_le_of_componentwise_matmul_bound hn0
      (R := fun i j : Fin n =>
        ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0)
      (A := XUL) (B := LU) hCoeff_nonneg hComp

/-- Source-facing Higham equation (14.23), Method D:
    product-of-norms companion to `higham14_eq14_23_methodD_left_residual_bound`.

    This is the coarser normwise endpoint obtained by applying infinity-norm
    submultiplicativity to the two retained absolute products. -/
theorem higham14_eq14_23_methodD_left_residual_infNorm_product_bound
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (X_U X_L X_hat : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hXL_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_L i k * L_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_L i k| * |L_hat k j|)
    (hXU_res : ∀ i j : Fin n,
      |∑ k : Fin n, X_U i k * U_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_U i k| * |U_hat k j|)
    (hProd : MatProdError n X_hat (matMul n X_U X_L) (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_U i k| * |X_L k j|))
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l₁ : Fin n, |X_U i l₁| * |X_L l₁ k₁|) *
          (∑ k₂ : Fin n, |L_hat k₁ k₂| * |U_hat k₂ j|)) :
    infNorm (fun i j : Fin n =>
      ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0) ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        infNorm X_U * infNorm X_L * infNorm L_hat * infNorm U_hat := by
  let XUL := matMul n (absMatrix n X_U) (absMatrix n X_L)
  let LU := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  have hRetained :=
    higham14_eq14_23_methodD_left_residual_infNorm_bound
      n hn0 fp A L_hat U_hat X_U X_L X_hat hLU hn hXL_res hXU_res hProd hLeftRes
  have hCoeff_nonneg : 0 ≤ 4 * gamma fp n + 2 * gamma fp n ^ 2 := by
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    nlinarith [sq_nonneg (gamma fp n)]
  have hXUL :
      infNorm XUL ≤ infNorm X_U * infNorm X_L := by
    simpa [XUL, infNorm_absMatrix hn0 X_U, infNorm_absMatrix hn0 X_L] using
      infNorm_matMul_le hn0 (absMatrix n X_U) (absMatrix n X_L)
  have hLUprod :
      infNorm LU ≤ infNorm L_hat * infNorm U_hat := by
    simpa [LU, infNorm_absMatrix hn0 L_hat, infNorm_absMatrix hn0 U_hat] using
      infNorm_matMul_le hn0 (absMatrix n L_hat) (absMatrix n U_hat)
  have hXUNonneg : 0 ≤ infNorm X_U := infNorm_nonneg X_U
  have hXLNonneg : 0 ≤ infNorm X_L := infNorm_nonneg X_L
  have hXULProdNonneg : 0 ≤ infNorm X_U * infNorm X_L :=
    mul_nonneg hXUNonneg hXLNonneg
  calc
    infNorm (fun i j : Fin n =>
        ∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0)
        ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          infNorm XUL * infNorm LU := by
            simpa [XUL, LU] using hRetained
    _ ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          (infNorm X_U * infNorm X_L) * infNorm LU := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hXUL hCoeff_nonneg)
              (infNorm_nonneg LU)
    _ ≤ (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          (infNorm X_U * infNorm X_L) *
            (infNorm L_hat * infNorm U_hat) := by
            exact mul_le_mul_of_nonneg_left hLUprod
              (mul_nonneg hCoeff_nonneg hXULProdNonneg)
    _ = (4 * gamma fp n + 2 * gamma fp n ^ 2) *
          infNorm X_U * infNorm X_L * infNorm L_hat * infNorm U_hat := by
            ring

/-- **Abstract Method D SPD specialization** (Higham §14.3.4, p. 274).

    For A = RᵀR (Cholesky), Method D computes X_R ≈ R⁻¹ and forms
    X̂ = X_R · X_Rᵀ.  Using the symmetry, the left residual satisfies
      |X̂A − I| ≤ dₙu|X_R||X_Rᵀ||R̂ᵀ||R̂|.

    This is the specialization of methodD_left_residual with
    L̂ = R̂ᵀ, Û = R̂, X_L = X_Rᵀ, X_U = X_R.  The final specialized
    residual is supplied as `hLeftRes`. -/
theorem methodD_spd_left_residual (n : ℕ) (fp : FPModel)
    (A R_hat : Fin n → Fin n → ℝ)
    (X_R X_hat : Fin n → Fin n → ℝ)
    (_hSPD : IsSymPosDef n A)
    (_hn : gammaValid fp n)
    -- Cholesky: A + ΔA = R̂ᵀR̂ with |ΔA| ≤ γₙ|R̂ᵀ||R̂|
    (_hChol : ∀ i j : Fin n,
      |A i j - ∑ k : Fin n, R_hat k i * R_hat k j| ≤
      gamma fp n * ∑ k : Fin n, |R_hat k i| * |R_hat k j|)
    -- X_R has right residual for R̂⁻¹
    (_hXR_res : ∀ i j : Fin n,
      |∑ k : Fin n, R_hat i k * X_R k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |R_hat i k| * |X_R k j|)
    -- X̂ = fl(X_R · X_Rᵀ)
    (_hProd : MatProdError n X_hat
      (matMul n X_R (fun i j => X_R j i))
      (gamma fp n)
      (fun i j => ∑ k : Fin n, |X_R i k| * |X_R j k|))
    -- The left residual bound (specialization of methodD_left_residual
    -- with L̂ = R̂ᵀ, Û = R̂, X_L = X_Rᵀ, X_U = X_R).
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l : Fin n, |X_R i l| * |X_R k₁ l|) *
          (∑ k₂ : Fin n, |R_hat k₂ k₁| * |R_hat k₂ j|)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * A k j - if i = j then 1 else 0| ≤
      (4 * gamma fp n + 2 * gamma fp n ^ 2) *
        ∑ k₁ : Fin n, (∑ l : Fin n, |X_R i l| * |X_R k₁ l|) *
          (∑ k₂ : Fin n, |R_hat k₂ k₁| * |R_hat k₂ j|) :=
  hLeftRes

-- §14.3.5  Summary: all methods have comparable residual bounds

/-- **Eq. 14.24**: Bound on how left and right residuals of X_L can differ.

    |X_L · L̂ − I| ≤ |L̂⁻¹| · |L̂ · X_L − I| · |L̂|.

    This shows the left and right residuals can differ by a factor as large
    as |(L⁻¹)ᵢⱼ| ≤ 2^{n-1}, but for well-conditioned L they are similar. -/
theorem left_right_residual_comparison (n : ℕ)
    (L L_inv X_L : Fin n → Fin n → ℝ)
    (hInv : IsLeftInverse n L L_inv) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_L i k * L k j - if i = j then 1 else 0| ≤
      ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n,
          |∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂ -
            if k₁ = k₂ then 1 else 0| *
          |L k₂ j|) := by
  intro i j
  -- Algebraic identity: X_L·L − I = L⁻¹·(L·X_L − I)·L
  let E : Fin n → Fin n → ℝ := fun k₁ k₂ =>
    ∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂ - if k₁ = k₂ then (1 : ℝ) else 0
  -- Part B: ∑_{k₁} L⁻¹(i,k₁) · L(k₁,j) = δ(i,j)
  have hPartB : ∑ k₁ : Fin n, L_inv i k₁ * L k₁ j =
      if i = j then (1 : ℝ) else 0 := hInv i j
  -- Part A: (L⁻¹ · L · X_L · L)_{ij} = (X_L · L)_{ij}
  have hPartA : ∑ k₁ : Fin n, L_inv i k₁ *
      (∑ k₂ : Fin n, (∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂) * L k₂ j) =
      ∑ k : Fin n, X_L i k * L k j := by
    -- Rewrite inner: ∑_{k₂} (∑_{k₃} L·X_L) · L = ∑_{k₃} L · (X_L·L)
    have hInner : ∀ k₁ : Fin n,
        ∑ k₂ : Fin n, (∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂) * L k₂ j =
        ∑ k₃ : Fin n, L k₁ k₃ * (∑ k₂ : Fin n, X_L k₃ k₂ * L k₂ j) := by
      intro k₁
      simp_rw [Finset.sum_mul, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
    simp_rw [hInner]
    -- Goal: ∑_{k₁} L⁻¹ ik₁ * ∑_{k₃} L k₁k₃ * (X_L·L)_{k₃j}
    -- Distribute outer product using explicit have
    have hOuter : ∀ k₁ : Fin n,
        L_inv i k₁ * ∑ k₃ : Fin n, L k₁ k₃ *
          (∑ k₂ : Fin n, X_L k₃ k₂ * L k₂ j) =
        ∑ k₃ : Fin n, L_inv i k₁ * L k₁ k₃ *
          (∑ k₂ : Fin n, X_L k₃ k₂ * L k₂ j) := by
      intro k₁; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k₃ _; ring
    simp_rw [hOuter]
    rw [Finset.sum_comm]
    -- Factor out (∑ k₂, X_L·L) from inner sum over k₁
    have hFactor : ∀ k₃ : Fin n,
        ∑ k₁ : Fin n, L_inv i k₁ * L k₁ k₃ *
          (∑ k₂ : Fin n, X_L k₃ k₂ * L k₂ j) =
        (∑ k₁ : Fin n, L_inv i k₁ * L k₁ k₃) *
          (∑ k₂ : Fin n, X_L k₃ k₂ * L k₂ j) := by
      intro k₃; rw [Finset.sum_mul]
    simp_rw [hFactor]
    have hInvL : ∀ k₃ : Fin n,
        (∑ k₁ : Fin n, L_inv i k₁ * L k₁ k₃) = if i = k₃ then 1 else 0 :=
      fun k₃ => hInv i k₃
    simp_rw [hInvL, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq, Finset.mem_univ]
  -- RHS expansion: ∑ L⁻¹ · (∑ E · L) = Part A − Part B
  have hRHS : ∑ k₁ : Fin n, L_inv i k₁ *
      (∑ k₂ : Fin n, E k₁ k₂ * L k₂ j) =
      ∑ k : Fin n, X_L i k * L k j - (if i = j then (1 : ℝ) else 0) := by
    simp only [E]
    -- E k₁ k₂ = (∑ L·X_L) − δ, so E·L = (∑ L·X_L)·L − δ·L
    have hExpand : ∀ k₁ : Fin n,
        ∑ k₂ : Fin n, (∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂ -
          if k₁ = k₂ then (1 : ℝ) else 0) * L k₂ j =
        ∑ k₂ : Fin n, (∑ k₃ : Fin n, L k₁ k₃ * X_L k₃ k₂) * L k₂ j -
        L k₁ j := by
      intro k₁
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      congr 1
      -- ∑_{k₂} δ(k₁,k₂) · L(k₂,j) = L(k₁,j)
      have : ∀ k₂ : Fin n,
          (if k₁ = k₂ then (1 : ℝ) else 0) * L k₂ j =
          if k₁ = k₂ then L k₂ j else 0 := by
        intro k₂; split_ifs <;> ring
      simp_rw [this]
      simp [Finset.mem_univ]
    simp_rw [hExpand, mul_sub, Finset.sum_sub_distrib]
    rw [hPartA, hPartB]
  rw [← hRHS]
  -- Triangle inequality: |∑ L⁻¹ · (∑ E · L)| ≤ ∑ |L⁻¹| · |∑ E · L| ≤ ∑ |L⁻¹| · (∑ |E| · |L|)
  calc |∑ k₁ : Fin n, L_inv i k₁ * (∑ k₂ : Fin n, E k₁ k₂ * L k₂ j)|
      ≤ ∑ k₁ : Fin n, |L_inv i k₁ * (∑ k₂ : Fin n, E k₁ k₂ * L k₂ j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |L_inv i k₁| * |∑ k₂ : Fin n, E k₁ k₂ * L k₂ j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |E k₁ k₂| * |L k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc |∑ k₂ : Fin n, E k₁ k₂ * L k₂ j|
            ≤ ∑ k₂ : Fin n, |E k₁ k₂ * L k₂ j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k₂ : Fin n, |E k₁ k₂| * |L k₂ j| := by
              apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _

/-- Right inverse residual `AX - I`, used in Higham Chapter 14 problems. -/
noncomputable def inverseRightResidual (n : ℕ)
    (A X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n A X i j - idMatrix n i j

/-- Left inverse residual `XA - I`, used in Higham Chapter 14 problems. -/
noncomputable def inverseLeftResidual (n : ℕ)
    (A X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n X A i j - idMatrix n i j

/-- Higham, 2nd ed., Chapter 14, Problem 14.3 algebraic identity:
    `AX - I = A (XA - I) A⁻¹`. -/
theorem higham14_problem14_3_right_residual_eq_mul_left_residual (n : ℕ)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv) :
    inverseRightResidual n A X =
      matMul n (matMul n A (inverseLeftResidual n A X)) A_inv := by
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  let AinvM : Matrix (Fin n) (Fin n) ℝ := A_inv
  let XM : Matrix (Fin n) (Fin n) ℝ := X
  have hAAinv : AM * AinvM = 1 := by
    ext i j
    simpa [AM, AinvM, Matrix.mul_apply] using hRight i j
  have hmat :
      AM * XM - 1 = AM * (XM * AM - 1) * AinvM := by
    calc
      AM * XM - 1
          = AM * XM * (AM * AinvM) - AM * AinvM := by
              rw [hAAinv]
              simp
      _ = AM * (XM * AM - 1) * AinvM := by
              noncomm_ring
  ext i j
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hmat
  simpa [inverseRightResidual, inverseLeftResidual, matMul, idMatrix,
    AM, AinvM, XM, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply] using hentry

/-- Higham, 2nd ed., Chapter 14, Problem 14.3 algebraic identity:
    `XA - I = A⁻¹ (AX - I) A`. -/
theorem higham14_problem14_3_left_residual_eq_mul_right_residual (n : ℕ)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv) :
    inverseLeftResidual n A X =
      matMul n (matMul n A_inv (inverseRightResidual n A X)) A := by
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  let AinvM : Matrix (Fin n) (Fin n) ℝ := A_inv
  let XM : Matrix (Fin n) (Fin n) ℝ := X
  have hAinvA : AinvM * AM = 1 := by
    ext i j
    simpa [AM, AinvM, Matrix.mul_apply] using hLeft i j
  have hmat :
      XM * AM - 1 = AinvM * (AM * XM - 1) * AM := by
    calc
      XM * AM - 1
          = AinvM * AM * XM * AM - AinvM * AM := by
              rw [hAinvA]
              simp
      _ = AinvM * (AM * XM - 1) * AM := by
              noncomm_ring
  ext i j
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hmat
  simpa [inverseRightResidual, inverseLeftResidual, matMul, idMatrix,
    AM, AinvM, XM, Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply] using hentry

/-- Higham, 2nd ed., Chapter 14, Problem 14.3, infinity-norm half:
    `‖AX - I‖∞ / ‖XA - I‖∞ ≤ κ∞(A)`. -/
theorem higham14_problem14_3_right_over_left_residual_infNorm_le_kappa
    (n : ℕ) (hn : 0 < n)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv)
    (hLeftResPos : 0 < infNorm (inverseLeftResidual n A X)) :
    infNorm (inverseRightResidual n A X) /
        infNorm (inverseLeftResidual n A X) ≤
      kappaInf n hn A A_inv := by
  have hres_eq :=
    higham14_problem14_3_right_residual_eq_mul_left_residual
      n A A_inv X hRight
  have hnorm :
      infNorm (inverseRightResidual n A X) ≤
        (infNorm A * infNorm (inverseLeftResidual n A X)) * infNorm A_inv := by
    calc
      infNorm (inverseRightResidual n A X)
          = infNorm (matMul n (matMul n A (inverseLeftResidual n A X)) A_inv) := by
              rw [hres_eq]
      _ ≤ infNorm (matMul n A (inverseLeftResidual n A X)) * infNorm A_inv :=
              infNorm_matMul_le hn (matMul n A (inverseLeftResidual n A X)) A_inv
      _ ≤ (infNorm A * infNorm (inverseLeftResidual n A X)) * infNorm A_inv := by
              exact mul_le_mul_of_nonneg_right
                (infNorm_matMul_le hn A (inverseLeftResidual n A X))
                (infNorm_nonneg A_inv)
  have hdiv := div_le_div_of_nonneg_right hnorm (le_of_lt hLeftResPos)
  calc
    infNorm (inverseRightResidual n A X) /
        infNorm (inverseLeftResidual n A X)
        ≤ ((infNorm A * infNorm (inverseLeftResidual n A X)) * infNorm A_inv) /
            infNorm (inverseLeftResidual n A X) := hdiv
    _ = infNorm A * infNorm A_inv := by
        field_simp [ne_of_gt hLeftResPos]
    _ = kappaInf n hn A A_inv := by
        rw [kappaInf_eq_infNorm_mul_infNorm n hn A A_inv]

/-- Higham, 2nd ed., Chapter 14, Problem 14.3, infinity-norm half:
    `‖XA - I‖∞ / ‖AX - I‖∞ ≤ κ∞(A)`. -/
theorem higham14_problem14_3_left_over_right_residual_infNorm_le_kappa
    (n : ℕ) (hn : 0 < n)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv)
    (hRightResPos : 0 < infNorm (inverseRightResidual n A X)) :
    infNorm (inverseLeftResidual n A X) /
        infNorm (inverseRightResidual n A X) ≤
      kappaInf n hn A A_inv := by
  have hres_eq :=
    higham14_problem14_3_left_residual_eq_mul_right_residual
      n A A_inv X hLeft
  have hnorm :
      infNorm (inverseLeftResidual n A X) ≤
        (infNorm A_inv * infNorm (inverseRightResidual n A X)) * infNorm A := by
    calc
      infNorm (inverseLeftResidual n A X)
          = infNorm (matMul n (matMul n A_inv (inverseRightResidual n A X)) A) := by
              rw [hres_eq]
      _ ≤ infNorm (matMul n A_inv (inverseRightResidual n A X)) * infNorm A :=
              infNorm_matMul_le hn
                (matMul n A_inv (inverseRightResidual n A X)) A
      _ ≤ (infNorm A_inv * infNorm (inverseRightResidual n A X)) * infNorm A := by
              exact mul_le_mul_of_nonneg_right
                (infNorm_matMul_le hn A_inv (inverseRightResidual n A X))
                (infNorm_nonneg A)
  have hdiv := div_le_div_of_nonneg_right hnorm (le_of_lt hRightResPos)
  calc
    infNorm (inverseLeftResidual n A X) /
        infNorm (inverseRightResidual n A X)
        ≤ ((infNorm A_inv * infNorm (inverseRightResidual n A X)) * infNorm A) /
            infNorm (inverseRightResidual n A X) := hdiv
    _ = infNorm A_inv * infNorm A := by
        field_simp [ne_of_gt hRightResPos]
    _ = kappaInf n hn A A_inv := by
        rw [kappaInf_eq_infNorm_mul_infNorm n hn A A_inv]
        ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.3:
    for nonzero left and right residuals,
    `max (‖AX-I‖∞/‖XA-I‖∞) (‖XA-I‖∞/‖AX-I‖∞) ≤ κ∞(A)`. -/
theorem higham14_problem14_3_max_residual_ratio_infNorm_le_kappa
    (n : ℕ) (hn : 0 < n)
    (A A_inv X : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A A_inv)
    (hLeftResPos : 0 < infNorm (inverseLeftResidual n A X))
    (hRightResPos : 0 < infNorm (inverseRightResidual n A X)) :
    max
        (infNorm (inverseRightResidual n A X) /
          infNorm (inverseLeftResidual n A X))
        (infNorm (inverseLeftResidual n A X) /
          infNorm (inverseRightResidual n A X))
      ≤ kappaInf n hn A A_inv := by
  exact max_le
    (higham14_problem14_3_right_over_left_residual_infNorm_le_kappa
      n hn A A_inv X hInv.2 hLeftResPos)
    (higham14_problem14_3_left_over_right_residual_infNorm_le_kappa
      n hn A A_inv X hInv.1 hRightResPos)

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 matrix `A(eps)`.

The source uses this two-by-two family, with `0 < eps << 1`, to show that
the right residual `AX-I` can be arbitrarily larger than the left residual
`XA-I`. -/
noncomputable def higham14_problem14_4_A (eps : ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  ![![1 / eps, 1], ![1 / eps ^ 2 - 1, 1 / eps]]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 approximate inverse family. -/
noncomputable def higham14_problem14_4_X (eps : ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  ![![1 - eps + 2 / eps, -2 - eps],
    ![2 - eps + 1 / eps - 1 / eps ^ 2, -1 - eps + 1 / eps]]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 exact left product:
    `X(eps) A(eps) = [[1+eps,-eps],[eps,1-eps]]`. -/
theorem higham14_problem14_4_XA_eq (eps : ℝ) (heps : eps ≠ 0) :
    matMul 2 (higham14_problem14_4_X eps) (higham14_problem14_4_A eps) =
      ![![1 + eps, -eps], ![eps, 1 - eps]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higham14_problem14_4_X, higham14_problem14_4_A, matMul]
  all_goals
    field_simp [heps]
    ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 exact right product. -/
theorem higham14_problem14_4_AX_eq (eps : ℝ) (heps : eps ≠ 0) :
    matMul 2 (higham14_problem14_4_A eps) (higham14_problem14_4_X eps) =
      ![![1 / eps ^ 2 + 2 / eps + 1 - eps, -2 - eps - 1 / eps],
        ![1 / eps ^ 3 + 2 / eps ^ 2 - 1 / eps - 2 + eps,
          -1 / eps ^ 2 - 2 / eps + 1 + eps]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higham14_problem14_4_X, higham14_problem14_4_A, matMul]
  all_goals
    field_simp [heps]
    ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    the left residual is the small matrix with entries `±eps`. -/
theorem higham14_problem14_4_left_residual_eq
    (eps : ℝ) (heps : eps ≠ 0) :
    inverseLeftResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps) =
      ![![eps, -eps], ![eps, -eps]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseLeftResidual, idMatrix,
      higham14_problem14_4_XA_eq eps heps]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    for `0 <= eps`, `||X(eps)A(eps)-I||_∞ = 2 eps`. -/
theorem higham14_problem14_4_left_residual_infNorm_eq
    (eps : ℝ) (hpos : 0 ≤ eps) (heps : eps ≠ 0) :
    infNorm (inverseLeftResidual 2
      (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) =
      2 * eps := by
  rw [higham14_problem14_4_left_residual_eq eps heps]
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      fin_cases i <;> simp [hpos, abs_of_nonneg, abs_of_nonpos] <;> linarith
    · nlinarith [hpos]
  · have hrow :=
      row_sum_le_infNorm (![![eps, -eps], ![eps, -eps]] :
        Fin 2 → Fin 2 → ℝ) (0 : Fin 2)
    have hsum :
        (∑ j : Fin 2,
          |(![![eps, -eps], ![eps, -eps]] :
            Fin 2 → Fin 2 → ℝ) (0 : Fin 2) j|) = 2 * eps := by
      simp [hpos, abs_of_nonneg, abs_of_nonpos]
      ring
    linarith

/-- Higham, 2nd ed., Chapter 14, Problem 14.4 support:
    the displayed lower-left entry of `AX-I` dominates `eps^{-3}` for
    `0 < eps <= 1`. -/
lemma higham14_problem14_4_right_residual_entry_ge_inv_cube
    (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    1 / eps ^ 3 ≤
      1 / eps ^ 3 + 2 / eps ^ 2 - 1 / eps - 2 + eps := by
  field_simp [ne_of_gt hpos]
  nlinarith [hpos, hle, sq_nonneg eps, sq_nonneg (eps - 1)]

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    for `0 < eps <= 1`, the right residual has infinity norm at least
    `eps^{-3}`. -/
theorem higham14_problem14_4_right_residual_infNorm_ge_inv_cube
    (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    1 / eps ^ 3 ≤
      infNorm (inverseRightResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
  have heps : eps ≠ 0 := ne_of_gt hpos
  let M := inverseRightResidual 2
    (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)
  have hentry : M (1 : Fin 2) (0 : Fin 2) =
      1 / eps ^ 3 + 2 / eps ^ 2 - 1 / eps - 2 + eps := by
    simp [M, inverseRightResidual, idMatrix,
      higham14_problem14_4_AX_eq eps heps]
  have hentry_ge : 1 / eps ^ 3 ≤ M (1 : Fin 2) (0 : Fin 2) := by
    rw [hentry]
    exact higham14_problem14_4_right_residual_entry_ge_inv_cube eps hpos hle
  have habs : M (1 : Fin 2) (0 : Fin 2) ≤ |M (1 : Fin 2) (0 : Fin 2)| :=
    le_abs_self _
  have hsingle :
      |M (1 : Fin 2) (0 : Fin 2)| ≤ ∑ j : Fin 2, |M (1 : Fin 2) j| := by
    simp
  exact le_trans hentry_ge
    (le_trans habs (le_trans hsingle (row_sum_le_infNorm M (1 : Fin 2))))

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    the right-over-left residual ratio is bounded below by `1/(2 eps^4)`. -/
theorem higham14_problem14_4_right_over_left_ratio_ge
    (eps : ℝ) (hpos : 0 < eps) (hle : eps ≤ 1) :
    1 / (2 * eps ^ 4) ≤
      infNorm (inverseRightResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) /
        infNorm (inverseLeftResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
  have heps : eps ≠ 0 := ne_of_gt hpos
  have hleft :=
    higham14_problem14_4_left_residual_infNorm_eq eps (le_of_lt hpos) heps
  have hleft_pos :
      0 < infNorm (inverseLeftResidual 2
        (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
    rw [hleft]
    nlinarith
  have hright :=
    higham14_problem14_4_right_residual_infNorm_ge_inv_cube eps hpos hle
  calc
    1 / (2 * eps ^ 4) = (1 / eps ^ 3) / (2 * eps) := by
      field_simp [heps]
    _ = (1 / eps ^ 3) /
        infNorm (inverseLeftResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
      rw [hleft]
    _ ≤ infNorm (inverseRightResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) /
        infNorm (inverseLeftResidual 2
          (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) :=
      div_le_div_of_nonneg_right hright (le_of_lt hleft_pos)

/-- Higham, 2nd ed., Chapter 14, Problem 14.4:
    the ratio `||AX-I||_∞ / ||XA-I||_∞` is arbitrarily large for the displayed
    two-by-two family. -/
theorem higham14_problem14_4_right_over_left_ratio_arbitrarily_large
    (K : ℝ) :
    ∃ eps : ℝ,
      0 < eps ∧ eps ≤ 1 ∧
        K <
          infNorm (inverseRightResidual 2
            (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) /
            infNorm (inverseLeftResidual 2
              (higham14_problem14_4_A eps) (higham14_problem14_4_X eps)) := by
  let eps : ℝ := (2 * (|K| + 1))⁻¹
  have hden : 0 < 2 * (|K| + 1) := by positivity
  have hpos : 0 < eps := by
    dsimp [eps]
    exact inv_pos.mpr hden
  have hle : eps ≤ 1 := by
    dsimp [eps]
    have hden_ge_one : 1 ≤ 2 * (|K| + 1) := by
      have habs : 0 ≤ |K| := abs_nonneg K
      nlinarith
    exact inv_le_one_of_one_le₀ hden_ge_one
  refine ⟨eps, hpos, hle, ?_⟩
  have hlower :=
    higham14_problem14_4_right_over_left_ratio_ge eps hpos hle
  have htarget : K < 1 / (2 * eps ^ 4) := by
    dsimp [eps]
    have hK_lt : K < |K| + 1 := by
      have hKle : K ≤ |K| := le_abs_self K
      linarith
    have hnon : 0 ≤ |K| := abs_nonneg K
    have ht_ge_one : 1 ≤ |K| + 1 := by linarith
    have ht_nonneg : 0 ≤ |K| + 1 := by linarith
    have ht_le_pow4 : |K| + 1 ≤ (|K| + 1) ^ 4 := by
      nlinarith [ht_ge_one, ht_nonneg,
        sq_nonneg ((|K| + 1) ^ 2 - (|K| + 1))]
    have ht_le_8pow4 : |K| + 1 ≤ 2 ^ 3 * (|K| + 1) ^ 4 := by
      nlinarith
    field_simp [ne_of_gt hden]
    nlinarith [hK_lt, ht_le_8pow4]
  exact lt_of_lt_of_le htarget hlower

/-- Scalar gamma collapse used in Higham Chapter 14, Problem 14.5:
    `u + gamma_n <= gamma_{n+1}`. -/
lemma higham14_unit_roundoff_add_gamma_le_gamma_succ
    (fp : FPModel) (n : ℕ) (hn1 : gammaValid fp (n + 1)) :
    fp.u + gamma fp n ≤ gamma fp (n + 1) := by
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp (by omega : 1 ≤ n + 1) hn1
  have hvalidn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  have hγ_sum : gamma fp 1 + gamma fp n + gamma fp 1 * gamma fp n ≤
      gamma fp (n + 1) := by
    have h := gamma_sum_le fp 1 n (by simpa [Nat.add_comm] using hn1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hu_le_γ1 : fp.u ≤ gamma fp 1 :=
    u_le_gamma fp one_pos hvalid1
  have hγprod_nonneg : 0 ≤ gamma fp 1 * gamma fp n :=
    mul_nonneg (gamma_nonneg fp hvalid1) (gamma_nonneg fp hvalidn)
  linarith

/-- Scalar gamma collapse used by the Method 2 strict-tail dot-product adapter:
    `u + (1 + u) * gamma_n <= gamma_{n+1}`. -/
lemma higham14_unit_roundoff_add_one_plus_u_mul_gamma_le_gamma_succ
    (fp : FPModel) (n : ℕ) (hn1 : gammaValid fp (n + 1)) :
    fp.u + (1 + fp.u) * gamma fp n ≤ gamma fp (n + 1) := by
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp (by omega : 1 ≤ n + 1) hn1
  have hvalidn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_succ n) hn1
  have hγ_sum : gamma fp 1 + gamma fp n + gamma fp 1 * gamma fp n ≤
      gamma fp (n + 1) := by
    have h := gamma_sum_le fp 1 n (by simpa [Nat.add_comm] using hn1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have hu_le_γ1 : fp.u ≤ gamma fp 1 :=
    u_le_gamma fp one_pos hvalid1
  have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hvalidn
  have hu_gamma_le : fp.u * gamma fp n ≤ gamma fp 1 * gamma fp n :=
    mul_le_mul_of_nonneg_right hu_le_γ1 hγn_nonneg
  nlinarith

/-- Scalar gamma collapse for a rounded strict-tail dot product followed by one
    rounded scalar multiplication and then the Method 2 diagonal factor:
    `u + (1 + u) * (gamma_n + u * (1 + gamma_n)) <= gamma_{n+2}`. -/
lemma higham14_unit_roundoff_add_one_plus_u_mul_rounded_gamma_le_gamma_succ_succ
    (fp : FPModel) (n : ℕ) (hn2 : gammaValid fp (n + 2)) :
    fp.u + (1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n)) ≤
      gamma fp (n + 2) := by
  let C : ℝ := gamma fp n + fp.u * (1 + gamma fp n)
  let D : ℝ := fp.u + (1 + fp.u) * C
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp (by omega : 1 ≤ n + 2) hn2
  have hvalidn : gammaValid fp n :=
    gammaValid_mono fp (by omega : n ≤ n + 2) hn2
  have hvalidn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega : n + 1 ≤ n + 2) hn2
  have hvalidn1p1 : gammaValid fp ((n + 1) + 1) := by
    simpa [Nat.add_assoc] using hn2
  have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hvalidn
  have hu_abs_gamma1 : |fp.u| ≤ gamma fp 1 := by
    simpa [abs_of_nonneg fp.u_nonneg] using u_le_gamma fp one_pos hvalid1
  have hγn_abs : |gamma fp n| ≤ gamma fp n := by
    simp [abs_of_nonneg hγn_nonneg]
  obtain ⟨θ1, hθ1, hprod1⟩ :=
    gamma_mul fp n 1 (gamma fp n) fp.u hγn_abs hu_abs_gamma1 hvalidn1
  have hC_eq : C = θ1 := by
    have hC_prod : C = (1 + gamma fp n) * (1 + fp.u) - 1 := by
      simp [C]
      ring
    have hprod1' : (1 + gamma fp n) * (1 + fp.u) - 1 = θ1 := by
      linarith
    exact hC_prod.trans hprod1'
  have hC_nonneg : 0 ≤ C := by
    have honeγ_nonneg : 0 ≤ 1 + gamma fp n := by linarith
    dsimp [C]
    exact add_nonneg hγn_nonneg (mul_nonneg fp.u_nonneg honeγ_nonneg)
  have hC_abs : |C| ≤ gamma fp (n + 1) := by
    rw [hC_eq]
    exact hθ1
  obtain ⟨θ2, hθ2, hprod2⟩ :=
    gamma_mul fp (n + 1) 1 C fp.u hC_abs hu_abs_gamma1 hvalidn1p1
  have hD_eq : D = θ2 := by
    have hD_prod : D = (1 + C) * (1 + fp.u) - 1 := by
      simp [D]
      ring
    have hprod2' : (1 + C) * (1 + fp.u) - 1 = θ2 := by
      linarith
    exact hD_prod.trans hprod2'
  have hD_nonneg : 0 ≤ D := by
    have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    dsimp [D]
    exact add_nonneg fp.u_nonneg (mul_nonneg honeu_nonneg hC_nonneg)
  have hD_le : D ≤ gamma fp ((n + 1) + 1) := by
    rw [hD_eq]
    have hθ2_nonneg : 0 ≤ θ2 := by
      rwa [← hD_eq]
    simpa [abs_of_nonneg hθ2_nonneg] using hθ2
  simpa [D, C, Nat.add_assoc] using hD_le

/-- Lemma 14.1 support: a strict-tail Method 2 update with a `gamma_n`
    scaled product certificate gives the source-shaped below-diagonal
    `gamma_{n+1}` full-column residual budget. -/
theorem triInv_method2_offdiag_trailing_update_gamma_full_bound
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLT : ∀ a b : Fin n, b.val > a.val → L a b = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ gamma fp n *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ) :
    ∀ j row : Fin n, row.val > j.val →
      |(∑ k : Fin n, X_hat row k * L k j) -
          (if row = j then 1 else 0)| ≤
        gamma fp (n + 1) * (∑ k : Fin n, |X_hat row k| * |L k j|) := by
  intro j row hij
  have hn : gammaValid fp n := gammaValid_mono fp (Nat.le_succ n) hn1
  have hbase :=
    triInv_method2_offdiag_trailing_update_full_bound n fp L X_hat
      (gamma_nonneg fp hn) hLT hDiag hTrail j row hij
  let S : ℝ := ∑ k : Fin n, |X_hat row k| * |L k j|
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg (fun k _ =>
      mul_nonneg (abs_nonneg (X_hat row k)) (abs_nonneg (L k j)))
  have hcoeff : fp.u + gamma fp n ≤ gamma fp (n + 1) :=
    higham14_unit_roundoff_add_gamma_le_gamma_succ fp n hn1
  exact le_trans hbase (mul_le_mul_of_nonneg_right hcoeff hS_nonneg)

/-- Lemma 14.1 support: once the rounded strict-tail Method 2 update supplies
    a `gamma_n` certificate, the already-proved upper, diagonal, and
    below-diagonal regional estimates assemble into the source-shaped
    `gamma_{n+1}` componentwise left-residual bound.

This is still conditional infrastructure: the rounded strict-tail certificate
is the remaining source-facing induction obligation. -/
theorem triInv_method2_left_residual_of_strict_tail_gamma
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat)
    (hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ gamma fp n *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 1) * ∑ k : Fin n, |X_hat i k| * |L k j| := by
  have hUpper :=
    triInv_method2_left_residual_upper_zero n fp L X_hat hLT hSpec
  have hDiag :=
    triInv_method2_left_residual_diag_product_bound n fp L X_hat hn1 hLT hSpec
  have hLower :=
    triInv_method2_offdiag_trailing_update_gamma_full_bound n fp L X_hat
      hn1 hLT hSpec.diag_err hTrail
  exact triInv_method2_left_residual_from_region_bounds n L X_hat
    (gamma_nonneg fp hn1) hUpper hDiag hLower

/-- Lemma 14.1 support: if the below-diagonal Method 2 entry is obtained by a
    rounded strict-tail dot product and then scaled exactly by `-X_hat j j`,
    the full componentwise left-residual bound follows with coefficient
    `gamma_{n+1}`.

This is a concrete dot-product adapter, not the final fully rounded Method 2
loop theorem: the subsequent scalar scaling is still exact on this surface. -/
theorem triInv_method2_left_residual_of_strict_tail_fl_dot
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat)
    (hUpdate : ∀ j row : Fin n, row.val > j.val →
      X_hat row j =
        -X_hat j j *
          fl_dotProduct fp n
            (fun k : Fin n => if j.val < k.val then X_hat row k else 0)
            (fun k : Fin n => L k j)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 1) * ∑ k : Fin n, |X_hat i k| * |L k j| := by
  have hn : gammaValid fp n := gammaValid_mono fp (Nat.le_succ n) hn1
  have hη_nonneg : 0 ≤ (1 + fp.u) * gamma fp n := by
    exact mul_nonneg (by linarith [fp.u_nonneg]) (gamma_nonneg fp hn)
  have hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ ((1 + fp.u) * gamma fp n) *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ := by
    intro j row hij
    let x : Fin n → ℝ := fun k => if j.val < k.val then X_hat row k else 0
    let y : Fin n → ℝ := fun k => L k j
    let exactTail : ℝ :=
      ∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0
    let tailAbs : ℝ :=
      ∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0
    let flTail : ℝ := fl_dotProduct fp n x y
    let Δ : ℝ := -X_hat j j * (flTail - exactTail)
    refine Exists.intro Δ (And.intro ?_ ?_)
    case refine_1 =>
      have hdot := dotProduct_error_bound fp n x y hn
      have hsum_exact :
          (∑ k : Fin n, x k * y k) = exactTail := by
        dsimp [x, y, exactTail]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hsum_abs :
          (∑ k : Fin n, |x k| * |y k|) = tailAbs := by
        dsimp [x, y, tailAbs]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hdot_tail : |flTail - exactTail| ≤ gamma fp n * tailAbs := by
        simpa [flTail, hsum_exact, hsum_abs] using hdot
      let δ : ℝ := Classical.choose (hSpec.diag_err j)
      have hδ_diag := Classical.choose_spec (hSpec.diag_err j)
      have hδ : |δ| ≤ fp.u := hδ_diag.1
      have hdiag : X_hat j j * L j j = 1 + δ := hδ_diag.2
      have hdiag_abs : |X_hat j j * L j j| ≤ 1 + fp.u := by
        calc
          |X_hat j j * L j j| = |1 + δ| := by rw [hdiag]
          _ ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by
            norm_num
            exact hδ
      have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      calc
        |Δ * L j j| = |X_hat j j * L j j| * |flTail - exactTail| := by
          dsimp [Δ]
          rw [abs_mul, abs_mul, abs_neg, abs_mul]
          ring
        _ ≤ (1 + fp.u) * (gamma fp n * tailAbs) := by
          exact mul_le_mul hdiag_abs hdot_tail (abs_nonneg _) honeu_nonneg
        _ = ((1 + fp.u) * gamma fp n) * tailAbs := by ring
    case refine_2 =>
      have hupdate := hUpdate j row hij
      calc
        X_hat row j = -X_hat j j * flTail := by
          simpa [flTail, x, y] using hupdate
        _ = -X_hat j j * exactTail + Δ := by
          dsimp [Δ]
          ring
  have hUpper :=
    triInv_method2_left_residual_upper_zero n fp L X_hat hLT hSpec
  have hDiag :=
    triInv_method2_left_residual_diag_product_bound n fp L X_hat hn1 hLT hSpec
  have hLowerEta :=
    triInv_method2_offdiag_trailing_update_full_bound n fp L X_hat
      hη_nonneg hLT hSpec.diag_err hTrail
  have hcoeff : fp.u + (1 + fp.u) * gamma fp n ≤ gamma fp (n + 1) :=
    higham14_unit_roundoff_add_one_plus_u_mul_gamma_le_gamma_succ fp n hn1
  have hLower : ∀ j row : Fin n, row.val > j.val →
      |∑ k : Fin n, X_hat row k * L k j -
          (if row = j then 1 else 0)| ≤
        gamma fp (n + 1) * ∑ k : Fin n, |X_hat row k| * |L k j| := by
    intro j row hij
    have hbase := hLowerEta j row hij
    have hS_nonneg : 0 ≤ ∑ k : Fin n, |X_hat row k| * |L k j| := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_trans hbase (mul_le_mul_of_nonneg_right hcoeff hS_nonneg)
  exact triInv_method2_left_residual_from_region_bounds n L X_hat
    (gamma_nonneg fp hn1) hUpper hDiag hLower

/-- Lemma 14.1 support: if the below-diagonal Method 2 entry is obtained by a
    rounded strict-tail dot product and then by one rounded scalar
    multiplication with `-X_hat j j`, the full componentwise left-residual bound
    follows with the conservative coefficient `gamma_{n+2}`.

This closes the local dot/scalar rounding wrapper for the strict-tail update.
It is still not the full source loop theorem, since it assumes the stored
below-diagonal entries are exactly produced by this one dot/scalar kernel. -/
theorem triInv_method2_left_residual_of_strict_tail_fl_dot_fl_mul
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat)
    (hUpdate : ∀ j row : Fin n, row.val > j.val →
      X_hat row j =
        fp.fl_mul (-X_hat j j)
          (fl_dotProduct fp n
            (fun k : Fin n => if j.val < k.val then X_hat row k else 0)
            (fun k : Fin n => L k j))) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat i k| * |L k j| := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega : n ≤ n + 2) hn2
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega : n + 1 ≤ n + 2) hn2
  have hη_nonneg :
      0 ≤ (1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n)) := by
    have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hn
    have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have honeγ_nonneg : 0 ≤ 1 + gamma fp n := by linarith
    exact mul_nonneg honeu_nonneg
      (add_nonneg hγn_nonneg (mul_nonneg fp.u_nonneg honeγ_nonneg))
  have hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ ((1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n))) *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ := by
    intro j row hij
    let x : Fin n → ℝ := fun k => if j.val < k.val then X_hat row k else 0
    let y : Fin n → ℝ := fun k => L k j
    let exactTail : ℝ :=
      ∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0
    let tailAbs : ℝ :=
      ∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0
    let flTail : ℝ := fl_dotProduct fp n x y
    let Δ : ℝ := fp.fl_mul (-X_hat j j) flTail - (-X_hat j j * exactTail)
    refine Exists.intro Δ (And.intro ?_ ?_)
    · obtain ⟨δmul, hδmul, hmul⟩ := fp.model_mul (-X_hat j j) flTail
      have hdot := dotProduct_error_bound fp n x y hn
      have hsum_exact :
          (∑ k : Fin n, x k * y k) = exactTail := by
        dsimp [x, y, exactTail]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hsum_abs :
          (∑ k : Fin n, |x k| * |y k|) = tailAbs := by
        dsimp [x, y, tailAbs]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hdot_tail : |flTail - exactTail| ≤ gamma fp n * tailAbs := by
        simpa [flTail, hsum_exact, hsum_abs] using hdot
      have htail_abs : |exactTail| ≤ tailAbs := by
        calc
          |exactTail| =
              |∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0| := by
                rfl
          _ ≤ ∑ k : Fin n,
                |if j.val < k.val then X_hat row k * L k j else 0| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = tailAbs := by
              apply Finset.sum_congr rfl
              intro k _
              by_cases hjk : j.val < k.val <;> simp [hjk, abs_mul]
      have htail_nonneg : 0 ≤ tailAbs := by
        dsimp [tailAbs]
        exact Finset.sum_nonneg (fun k _ => by
          by_cases hjk : j.val < k.val
          · simpa [hjk] using
              mul_nonneg (abs_nonneg (X_hat row k)) (abs_nonneg (L k j))
          · simp [hjk])
      have hfl_abs : |flTail| ≤ (1 + gamma fp n) * tailAbs := by
        calc
          |flTail| = |exactTail + (flTail - exactTail)| := by
            congr 1
            ring
          _ ≤ |exactTail| + |flTail - exactTail| :=
              abs_add_le exactTail (flTail - exactTail)
          _ ≤ tailAbs + gamma fp n * tailAbs :=
              add_le_add htail_abs hdot_tail
          _ = (1 + gamma fp n) * tailAbs := by ring
      let δ : ℝ := Classical.choose (hSpec.diag_err j)
      have hδ_diag := Classical.choose_spec (hSpec.diag_err j)
      have hδ : |δ| ≤ fp.u := hδ_diag.1
      have hdiag : X_hat j j * L j j = 1 + δ := hδ_diag.2
      have hdiag_abs : |X_hat j j * L j j| ≤ 1 + fp.u := by
        calc
          |X_hat j j * L j j| = |1 + δ| := by rw [hdiag]
          _ ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by
            norm_num
            exact hδ
      have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have honeγ_nonneg : 0 ≤ 1 + gamma fp n := by
        linarith [gamma_nonneg fp hn]
      have hcoef_nonneg :
          0 ≤ (1 + fp.u) * ((1 + gamma fp n) * tailAbs) := by
        exact mul_nonneg honeu_nonneg
          (mul_nonneg honeγ_nonneg htail_nonneg)
      have hΔ_decomp :
          Δ * L j j =
            (-X_hat j j * L j j) * (flTail - exactTail) +
              ((-X_hat j j * L j j) * flTail) * δmul := by
        dsimp [Δ]
        rw [hmul]
        ring
      have hfirst :
          |(-X_hat j j * L j j) * (flTail - exactTail)| ≤
            (1 + fp.u) * (gamma fp n * tailAbs) := by
        have hneg_abs : |(-X_hat j j * L j j)| = |X_hat j j * L j j| := by
          have hneg : (-X_hat j j * L j j) = -(X_hat j j * L j j) := by ring
          rw [hneg, abs_neg]
        calc
          |(-X_hat j j * L j j) * (flTail - exactTail)|
              = |X_hat j j * L j j| * |flTail - exactTail| := by
                rw [abs_mul, hneg_abs]
          _ ≤ (1 + fp.u) * (gamma fp n * tailAbs) :=
              mul_le_mul hdiag_abs hdot_tail (abs_nonneg _) honeu_nonneg
      have hsecond :
          |((-X_hat j j * L j j) * flTail) * δmul| ≤
            ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u := by
        have hneg_abs : |(-X_hat j j * L j j)| = |X_hat j j * L j j| := by
          have hneg : (-X_hat j j * L j j) = -(X_hat j j * L j j) := by ring
          rw [hneg, abs_neg]
        have hleft :
            |X_hat j j * L j j| * |flTail| ≤
              (1 + fp.u) * ((1 + gamma fp n) * tailAbs) :=
          mul_le_mul hdiag_abs hfl_abs (abs_nonneg _) honeu_nonneg
        calc
          |((-X_hat j j * L j j) * flTail) * δmul|
              = |X_hat j j * L j j| * |flTail| * |δmul| := by
                rw [abs_mul, abs_mul, hneg_abs]
          _ ≤ ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u :=
              mul_le_mul hleft hδmul (abs_nonneg _) hcoef_nonneg
      calc
        |Δ * L j j|
            = |(-X_hat j j * L j j) * (flTail - exactTail) +
                ((-X_hat j j * L j j) * flTail) * δmul| := by
              rw [hΔ_decomp]
        _ ≤ |(-X_hat j j * L j j) * (flTail - exactTail)| +
              |((-X_hat j j * L j j) * flTail) * δmul| :=
            abs_add_le _ _
        _ ≤ (1 + fp.u) * (gamma fp n * tailAbs) +
              ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u :=
            add_le_add hfirst hsecond
        _ = ((1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n))) *
              tailAbs := by ring
    · have hupdate := hUpdate j row hij
      calc
        X_hat row j = fp.fl_mul (-X_hat j j) flTail := by
          simpa [flTail, x, y] using hupdate
        _ = -X_hat j j * exactTail + Δ := by
          dsimp [Δ]
          ring
  have hUpper :=
    triInv_method2_left_residual_upper_zero n fp L X_hat hLT hSpec
  have hDiagBase :=
    triInv_method2_left_residual_diag_product_bound n fp L X_hat hn1 hLT hSpec
  have hDiag : ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat j k| * |L k j| := by
    intro j
    have hS_nonneg : 0 ≤ ∑ k : Fin n, |X_hat j k| * |L k j| := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hmono : gamma fp (n + 1) ≤ gamma fp (n + 2) :=
      gamma_mono fp (by omega : n + 1 ≤ n + 2) hn2
    exact le_trans (hDiagBase j) (mul_le_mul_of_nonneg_right hmono hS_nonneg)
  have hLowerEta :=
    triInv_method2_offdiag_trailing_update_full_bound n fp L X_hat
      hη_nonneg hLT hSpec.diag_err hTrail
  have hcoeff :
      fp.u + (1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n)) ≤
        gamma fp (n + 2) :=
    higham14_unit_roundoff_add_one_plus_u_mul_rounded_gamma_le_gamma_succ_succ
      fp n hn2
  have hLower : ∀ j row : Fin n, row.val > j.val →
      |∑ k : Fin n, X_hat row k * L k j -
          (if row = j then 1 else 0)| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat row k| * |L k j| := by
    intro j row hij
    have hbase := hLowerEta j row hij
    have hS_nonneg : 0 ≤ ∑ k : Fin n, |X_hat row k| * |L k j| := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_trans hbase (mul_le_mul_of_nonneg_right hcoeff hS_nonneg)
  exact triInv_method2_left_residual_from_region_bounds n L X_hat
    (gamma_nonneg fp hn2) hUpper hDiag hLower

/-- Lemma 14.1 support: a strict-tail Method 2 storage recurrence implies
    the full componentwise left-residual bound using only the diagonal
    rounded-reciprocal certificate, triangular shape, and stored rounded
    dot/scalar update.

Compared with `triInv_method2_left_residual_of_strict_tail_fl_dot_fl_mul`,
this theorem removes the dependency on the older `Method2Spec.offdiag_err`
field.  It still assumes the storage recurrence itself; the remaining
source-facing loop obligation is to prove `hStore` from the concrete
reverse-column implementation. -/
theorem triInv_method2_left_residual_of_strict_tail_storage
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hUpper : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hStore : ∀ j row : Fin n, row.val > j.val →
      X_hat row j =
        fp.fl_mul (-X_hat j j)
          (fl_dotProduct fp n
            (fun k : Fin n => if j.val < k.val then X_hat row k else 0)
            (fun k : Fin n => L k j))) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat i k| * |L k j| := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega : n ≤ n + 2) hn2
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega : n + 1 ≤ n + 2) hn2
  have hη_nonneg :
      0 ≤ (1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n)) := by
    have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hn
    have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have honeγ_nonneg : 0 ≤ 1 + gamma fp n := by linarith
    exact mul_nonneg honeu_nonneg
      (add_nonneg hγn_nonneg (mul_nonneg fp.u_nonneg honeγ_nonneg))
  have hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ ((1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n))) *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ := by
    intro j row hij
    let x : Fin n → ℝ := fun k => if j.val < k.val then X_hat row k else 0
    let y : Fin n → ℝ := fun k => L k j
    let exactTail : ℝ :=
      ∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0
    let tailAbs : ℝ :=
      ∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0
    let flTail : ℝ := fl_dotProduct fp n x y
    let Δ : ℝ := fp.fl_mul (-X_hat j j) flTail - (-X_hat j j * exactTail)
    refine Exists.intro Δ (And.intro ?_ ?_)
    · obtain ⟨δmul, hδmul, hmul⟩ := fp.model_mul (-X_hat j j) flTail
      have hdot := dotProduct_error_bound fp n x y hn
      have hsum_exact :
          (∑ k : Fin n, x k * y k) = exactTail := by
        dsimp [x, y, exactTail]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hsum_abs :
          (∑ k : Fin n, |x k| * |y k|) = tailAbs := by
        dsimp [x, y, tailAbs]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hdot_tail : |flTail - exactTail| ≤ gamma fp n * tailAbs := by
        simpa [flTail, hsum_exact, hsum_abs] using hdot
      have htail_abs : |exactTail| ≤ tailAbs := by
        calc
          |exactTail| =
              |∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0| := by
                rfl
          _ ≤ ∑ k : Fin n,
                |if j.val < k.val then X_hat row k * L k j else 0| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = tailAbs := by
              apply Finset.sum_congr rfl
              intro k _
              by_cases hjk : j.val < k.val <;> simp [hjk, abs_mul]
      have htail_nonneg : 0 ≤ tailAbs := by
        dsimp [tailAbs]
        exact Finset.sum_nonneg (fun k _ => by
          by_cases hjk : j.val < k.val
          · simpa [hjk] using
              mul_nonneg (abs_nonneg (X_hat row k)) (abs_nonneg (L k j))
          · simp [hjk])
      have hfl_abs : |flTail| ≤ (1 + gamma fp n) * tailAbs := by
        calc
          |flTail| = |exactTail + (flTail - exactTail)| := by
            congr 1
            ring
          _ ≤ |exactTail| + |flTail - exactTail| :=
              abs_add_le exactTail (flTail - exactTail)
          _ ≤ tailAbs + gamma fp n * tailAbs :=
              add_le_add htail_abs hdot_tail
          _ = (1 + gamma fp n) * tailAbs := by ring
      obtain ⟨δ, hδ, hdiag⟩ := hDiag j
      have hdiag_abs : |X_hat j j * L j j| ≤ 1 + fp.u := by
        calc
          |X_hat j j * L j j| = |1 + δ| := by rw [hdiag]
          _ ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by
            norm_num
            exact hδ
      have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have honeγ_nonneg : 0 ≤ 1 + gamma fp n := by
        linarith [gamma_nonneg fp hn]
      have hcoef_nonneg :
          0 ≤ (1 + fp.u) * ((1 + gamma fp n) * tailAbs) := by
        exact mul_nonneg honeu_nonneg
          (mul_nonneg honeγ_nonneg htail_nonneg)
      have hΔ_decomp :
          Δ * L j j =
            (-X_hat j j * L j j) * (flTail - exactTail) +
              ((-X_hat j j * L j j) * flTail) * δmul := by
        dsimp [Δ]
        rw [hmul]
        ring
      have hfirst :
          |(-X_hat j j * L j j) * (flTail - exactTail)| ≤
            (1 + fp.u) * (gamma fp n * tailAbs) := by
        have hneg_abs : |(-X_hat j j * L j j)| = |X_hat j j * L j j| := by
          have hneg : (-X_hat j j * L j j) = -(X_hat j j * L j j) := by ring
          rw [hneg, abs_neg]
        calc
          |(-X_hat j j * L j j) * (flTail - exactTail)|
              = |X_hat j j * L j j| * |flTail - exactTail| := by
                rw [abs_mul, hneg_abs]
          _ ≤ (1 + fp.u) * (gamma fp n * tailAbs) :=
              mul_le_mul hdiag_abs hdot_tail (abs_nonneg _) honeu_nonneg
      have hsecond :
          |((-X_hat j j * L j j) * flTail) * δmul| ≤
            ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u := by
        have hneg_abs : |(-X_hat j j * L j j)| = |X_hat j j * L j j| := by
          have hneg : (-X_hat j j * L j j) = -(X_hat j j * L j j) := by ring
          rw [hneg, abs_neg]
        have hleft :
            |X_hat j j * L j j| * |flTail| ≤
              (1 + fp.u) * ((1 + gamma fp n) * tailAbs) :=
          mul_le_mul hdiag_abs hfl_abs (abs_nonneg _) honeu_nonneg
        calc
          |((-X_hat j j * L j j) * flTail) * δmul|
              = |X_hat j j * L j j| * |flTail| * |δmul| := by
                rw [abs_mul, abs_mul, hneg_abs]
          _ ≤ ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u :=
              mul_le_mul hleft hδmul (abs_nonneg _) hcoef_nonneg
      calc
        |Δ * L j j|
            = |(-X_hat j j * L j j) * (flTail - exactTail) +
                ((-X_hat j j * L j j) * flTail) * δmul| := by
              rw [hΔ_decomp]
        _ ≤ |(-X_hat j j * L j j) * (flTail - exactTail)| +
              |((-X_hat j j * L j j) * flTail) * δmul| :=
            abs_add_le _ _
        _ ≤ (1 + fp.u) * (gamma fp n * tailAbs) +
              ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u :=
            add_le_add hfirst hsecond
        _ = ((1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n))) *
              tailAbs := by ring
    · have hstore := hStore j row hij
      calc
        X_hat row j = fp.fl_mul (-X_hat j j) flTail := by
          simpa [flTail, x, y] using hstore
        _ = -X_hat j j * exactTail + Δ := by
          dsimp [Δ]
          ring
  have hUpperRes :=
    triInv_lower_left_residual_upper_zero n L X_hat hUpper hLT
  have hDiagBase :=
    triInv_method2_left_residual_diag_product_bound_of_diag_upper
      n fp L X_hat hn1 hLT hDiag hUpper
  have hDiagBudget : ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat j k| * |L k j| := by
    intro j
    have hS_nonneg : 0 ≤ ∑ k : Fin n, |X_hat j k| * |L k j| := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hmono : gamma fp (n + 1) ≤ gamma fp (n + 2) :=
      gamma_mono fp (by omega : n + 1 ≤ n + 2) hn2
    exact le_trans (hDiagBase j) (mul_le_mul_of_nonneg_right hmono hS_nonneg)
  have hLowerEta :=
    triInv_method2_offdiag_trailing_update_full_bound n fp L X_hat
      hη_nonneg hLT hDiag hTrail
  have hcoeff :
      fp.u + (1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n)) ≤
        gamma fp (n + 2) :=
    higham14_unit_roundoff_add_one_plus_u_mul_rounded_gamma_le_gamma_succ_succ
      fp n hn2
  have hLower : ∀ j row : Fin n, row.val > j.val →
      |∑ k : Fin n, X_hat row k * L k j -
          (if row = j then 1 else 0)| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat row k| * |L k j| := by
    intro j row hij
    have hbase := hLowerEta j row hij
    have hS_nonneg : 0 ≤ ∑ k : Fin n, |X_hat row k| * |L k j| := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_trans hbase (mul_le_mul_of_nonneg_right hcoeff hS_nonneg)
  exact triInv_method2_left_residual_from_region_bounds n L X_hat
    (gamma_nonneg fp hn2) hUpperRes hDiagBudget hLower

/-- Problem 14.2 / Lemma 14.1 normwise bridge:
    the strict-tail Method 2 storage recurrence implies the corresponding
    infinity-norm left-residual bound.

This is the normwise companion to
`triInv_method2_left_residual_of_strict_tail_storage`.  It remains conditional
on the source-facing storage recurrence `hStore`, so the concrete reverse-column
loop proof producing that recurrence is still explicit. -/
theorem triInv_method2_left_residual_normwise_of_strict_tail_storage
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hUpper : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hStore : ∀ j row : Fin n, row.val > j.val →
      X_hat row j =
        fp.fl_mul (-X_hat j j)
          (fl_dotProduct fp n
            (fun k : Fin n => if j.val < k.val then X_hat row k else 0)
            (fun k : Fin n => L k j))) :
    infNorm (fun i j =>
      ∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0) ≤
      gamma fp (n + 2) * infNorm X_hat * infNorm L := by
  have hComp :=
    triInv_method2_left_residual_of_strict_tail_storage
      n fp L X_hat hn2 hLT hDiag hUpper hStore
  exact higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (R := fun i j => ∑ k : Fin n, X_hat i k * L k j -
      if i = j then 1 else 0)
    (A := X_hat) (B := L) (gamma_nonneg fp hn2) hComp

/-- Higham, 2nd ed., Chapter 14, Lemma 14.1 / equation (14.8), Method 2
    strict-tail kernel surface:
    a source-facing strict-tail dot/scalar kernel certificate implies the
    componentwise left-residual bound with coefficient `gamma_(n+2)`.

    This closes the residual consequence of the packaged kernel certificate.
    The concrete reverse-column loop proof that produces
    `Method2StrictTailKernelSpec` remains a separate selected dependency. -/
theorem triInv_method2_left_residual_of_strict_tail_kernel_spec
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hKernel : Method2StrictTailKernelSpec fp n L X_hat) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat i k| * |L k j| :=
  triInv_method2_left_residual_of_strict_tail_fl_dot_fl_mul
    n fp L X_hat hn2 hLT hKernel.method2 hKernel.strict_tail_dot_scalar

/-- Problem 14.2 / Lemma 14.1 normwise bridge:
    a Method 2 strict-tail kernel certificate implies the corresponding
    infinity-norm left-residual bound, with the same conservative
    `gamma_(n+2)` coefficient as the rounded dot/scalar componentwise theorem.

    This is still conditional on the concrete reverse-column loop producing
    `Method2StrictTailKernelSpec`, but it removes the remaining normwise
    handoff once that kernel package is available. -/
theorem triInv_method2_left_residual_normwise_of_strict_tail_kernel_spec
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hKernel : Method2StrictTailKernelSpec fp n L X_hat) :
    infNorm (fun i j =>
      ∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0) ≤
      gamma fp (n + 2) * infNorm X_hat * infNorm L := by
  have hComp :=
    triInv_method2_left_residual_of_strict_tail_kernel_spec
      n fp L X_hat hn2 hLT hKernel
  exact higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (R := fun i j => ∑ k : Fin n, X_hat i k * L k j -
      if i = j then 1 else 0)
    (A := X_hat) (B := L) (gamma_nonneg fp hn2) hComp

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

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    Euclidean norm of row `i`, the quantity `||A(i,:)||₂` used in the
    determinant normalization defining the Hadamard condition number. -/
noncomputable def higham14_rowNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  vecNorm2 (fun j : Fin n => A i j)

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    diagonal matrix whose diagonal entries are the row 2-norms of `A`. -/
noncomputable def higham14_rowNormDiagonal {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i : Fin n => higham14_rowNorm2 A i)

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    Hadamard determinant condition number `ψ(A)`, modeled in the positive
    form used by the subsequent Hadamard-inequality statement.  The printed
    display omits absolute-value bars on `det(A)`, while the condition-number
    interpretation requires `|det(A)|` in the denominator. -/
noncomputable def higham14_hadamardConditionNumber {n : ℕ}
    (A : Fin n → Fin n → ℝ) : ℝ :=
  (∏ i : Fin n, higham14_rowNorm2 A i) /
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|

/-- Higham, 2nd ed., Chapter 14, Section 14.6, printed p.279:
    signed raw version of the displayed ratio `det(D)/det(A)`.  Use
    `higham14_hadamardConditionNumber` for the nonnegative condition-number
    surface that matches the following Hadamard inequality discussion. -/
noncomputable def higham14_hadamardConditionNumberRaw {n : ℕ}
    (A : Fin n → Fin n → ℝ) : ℝ :=
  (∏ i : Fin n, higham14_rowNorm2 A i) /
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)

lemma higham14_rowNorm2_nonneg {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) :
    0 ≤ higham14_rowNorm2 A i :=
  vecNorm2_nonneg _

/-- The row-norm diagonal has determinant equal to the product of the row
    2-norms, the numerator in Higham's `ψ(A)`. -/
theorem higham14_det_rowNormDiagonal_eq_prod_rowNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    Matrix.det (higham14_rowNormDiagonal A) =
      ∏ i : Fin n, higham14_rowNorm2 A i := by
  simp [higham14_rowNormDiagonal]

/-- Source-facing bridge from the diagonal determinant notation to the
    product-of-row-norms definition of `ψ(A)`. -/
theorem higham14_hadamardConditionNumber_eq_det_rowNormDiagonal_div_abs_det
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    higham14_hadamardConditionNumber A =
      Matrix.det (higham14_rowNormDiagonal A) /
        |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| := by
  rw [higham14_det_rowNormDiagonal_eq_prod_rowNorm2]
  rfl

/-- When `det(A)` is positive, the raw displayed ratio agrees with the
    nonnegative Hadamard condition-number form. -/
theorem higham14_hadamardConditionNumberRaw_eq_conditionNumber_of_det_pos
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : 0 < Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) :
    higham14_hadamardConditionNumberRaw A =
      higham14_hadamardConditionNumber A := by
  simp [higham14_hadamardConditionNumberRaw,
    higham14_hadamardConditionNumber, abs_of_pos hdet]

theorem higham14_hadamardConditionNumber_nonneg {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    0 ≤ higham14_hadamardConditionNumber A := by
  unfold higham14_hadamardConditionNumber
  exact div_nonneg
    (Finset.prod_nonneg fun i _ => higham14_rowNorm2_nonneg A i)
    (abs_nonneg _)

lemma higham14_rowNorm2_pos_of_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (i : Fin n) :
    0 < higham14_rowNorm2 A i := by
  have hne : higham14_rowNorm2 A i ≠ 0 := by
    intro hzero
    have hrow : ∀ j : Fin n, A i j = 0 :=
      (vecNorm2_eq_zero_iff (fun j : Fin n => A i j)).mp hzero
    exact hdet (Matrix.det_eq_zero_of_row_eq_zero i hrow)
  exact lt_of_le_of_ne (higham14_rowNorm2_nonneg A i) (Ne.symm hne)

theorem higham14_hadamardConditionNumber_pos_of_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    0 < higham14_hadamardConditionNumber A := by
  unfold higham14_hadamardConditionNumber
  exact div_pos
    (Finset.prod_pos fun i _ => higham14_rowNorm2_pos_of_det_ne_zero A hdet i)
    (abs_pos.mpr hdet)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    Hadamard's determinant inequality in squared row-norm form.  This is a
    Chapter 14 source-facing wrapper around the Chapter 9 Gram determinant
    proof. -/
theorem higham14_problem14_11_hadamard_det_sq_le_prod_rowNorm2_sq {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 ≤
      ∏ i : Fin n, higham14_rowNorm2 A i ^ 2 := by
  simpa [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq] using
    (higham9_hadamard_det_sq_le_prod_row_sq
      (A := (A : Matrix (Fin n) (Fin n) ℝ)))

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    Hadamard's determinant inequality in the form
    `|det(A)| <= prod_i ||A(i,:)||_2`. -/
theorem higham14_problem14_11_abs_det_le_prod_rowNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| ≤
      ∏ i : Fin n, higham14_rowNorm2 A i := by
  have hsquare :
      (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 ≤
        (∏ i : Fin n, higham14_rowNorm2 A i) ^ 2 := by
    rw [← Finset.prod_pow]
    exact higham14_problem14_11_hadamard_det_sq_le_prod_rowNorm2_sq A
  exact abs_le_of_sq_le_sq hsquare
    (Finset.prod_nonneg fun i _ => higham14_rowNorm2_nonneg A i)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    nonsingular matrices have Hadamard determinant condition number at least
    one, in the nonnegative `|det(A)|` denominator convention. -/
theorem higham14_problem14_11_hadamardConditionNumber_ge_one_of_det_ne_zero
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    1 ≤ higham14_hadamardConditionNumber A := by
  have hden_pos : 0 < |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| :=
    abs_pos.mpr hdet
  unfold higham14_hadamardConditionNumber
  exact (one_le_div hden_pos).mpr
    (higham14_problem14_11_abs_det_le_prod_rowNorm2 A)

/-- Source-facing predicate for Higham, Chapter 14, Problem 14.11:
    the rows of `A` are pairwise orthogonal in the Euclidean inner product. -/
def higham14_rowsOrthogonal {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ≠ j → ∑ k : Fin n, A i k * A j k = 0

/-- The source-facing row-orthogonality predicate is exactly Mathlib's
    matrix row-orthogonality predicate. -/
theorem higham14_rowsOrthogonal_iff_hasOrthogonalRows {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    higham14_rowsOrthogonal A ↔
      Matrix.HasOrthogonalRows (A : Matrix (Fin n) (Fin n) ℝ) := by
  rfl

/-- Row orthogonality is equivalently zero off-diagonal entries in the
    row Gram matrix `A Aᵀ`.  This is the landing point for the missing
    equality case of Hadamard's determinant inequality. -/
theorem higham14_rowsOrthogonal_iff_gram_offdiag_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ) :
    higham14_rowsOrthogonal A ↔
      let AM : Matrix (Fin n) (Fin n) ℝ := A
      ∀ ⦃i j : Fin n⦄, i ≠ j →
        (AM * Matrix.transpose AM) i j = 0 := by
  constructor
  · intro h
    dsimp only
    intro i j hij
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using
      h (i := i) (j := j) hij
  · intro h
    dsimp only at h
    intro i j hij
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using
      h (i := i) (j := j) hij

/-- Higham, 2nd ed., Chapter 14, Problem 14.11 support:
    equality in the row-norm Hadamard bound transfers to equality in the
    row-Gram positive-definite Hadamard bound.  The remaining converse reduces
    to proving the equality case of that positive-definite bound. -/
theorem higham14_problem14_11_gram_det_eq_prod_diag_of_abs_det_eq_prod_rowNorm2
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (heq :
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, higham14_rowNorm2 A i) :
    let AM : Matrix (Fin n) (Fin n) ℝ := A
    Matrix.det (AM * Matrix.transpose AM) =
      ∏ i : Fin n, (AM * Matrix.transpose AM) i i := by
  dsimp only
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  change Matrix.det (AM * Matrix.transpose AM) =
    ∏ i : Fin n, (AM * Matrix.transpose AM) i i
  have hdetGram :
      Matrix.det (AM * Matrix.transpose AM) = Matrix.det AM ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    ring
  have hdiag :
      ∀ i : Fin n,
        (AM * Matrix.transpose AM) i i = higham14_rowNorm2 A i ^ 2 := by
    intro i
    have hnorm :
        higham14_rowNorm2 A i ^ 2 = ∑ j : Fin n, A i j ^ 2 := by
      simp [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq]
    calc
      (AM * Matrix.transpose AM) i i
          = ∑ j : Fin n, A i j * A i j := by
            simp [AM, Matrix.mul_apply, Matrix.transpose_apply]
      _ = ∑ j : Fin n, A i j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = higham14_rowNorm2 A i ^ 2 := hnorm.symm
  calc
    Matrix.det (AM * Matrix.transpose AM)
        = Matrix.det AM ^ 2 := hdetGram
    _ = |Matrix.det AM| ^ 2 := by rw [sq_abs]
    _ = |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| ^ 2 := by simp [AM]
    _ = (∏ i : Fin n, higham14_rowNorm2 A i) ^ 2 := by rw [heq]
    _ = ∏ i : Fin n, higham14_rowNorm2 A i ^ 2 := by
          rw [Finset.prod_pow]
    _ = ∏ i : Fin n, (AM * Matrix.transpose AM) i i := by
          exact Finset.prod_congr rfl (fun i _ => (hdiag i).symm)

/-- AM-GM equality helper for the Chapter 14 Hadamard equality case:
    nonnegative `z_i` with arithmetic mean and geometric mean both one must
    have every `z_i = 1`. -/
theorem higham14_amgm_all_eq_one_of_sum_eq_card_prod_eq_one {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hsum : ∑ i : Fin n, z i = n) (hprod : ∏ i : Fin n, z i = 1) :
    ∀ i : Fin n, z i = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 < (1 / (n : ℝ)) := by
    intro _ _
    positivity
  have hw' : ∑ _i : Fin n, (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hz' : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ z i := by
    intro i _
    exact hz i
  have hrhs : ∑ i : Fin n, (1 / (n : ℝ)) * z i = 1 := by
    rw [← Finset.mul_sum, hsum]
    field_simp
  have hgm_nonneg : 0 ≤ ∏ i : Fin n, z i ^ (1 / (n : ℝ)) := by
    exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hz i) _
  have hpow :
      (∏ i : Fin n, z i ^ (1 / (n : ℝ))) ^ n = ∏ i : Fin n, z i := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_natCast (z i ^ (1 / (n : ℝ))) n,
      ← Real.rpow_mul (hz i)]
    rw [one_div, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), Real.rpow_one]
  have hgm_pow_one :
      (∏ i : Fin n, z i ^ (1 / (n : ℝ))) ^ n = 1 := by
    rw [hpow, hprod]
  have hgm_one : (∏ i : Fin n, z i ^ (1 / (n : ℝ))) = 1 :=
    (pow_eq_one_iff_of_nonneg hgm_nonneg hn.ne').mp hgm_pow_one
  have heq_gm_am :
      (∏ i ∈ (Finset.univ : Finset (Fin n)), z i ^ (1 / (n : ℝ))) =
        ∑ i ∈ (Finset.univ : Finset (Fin n)), (1 / (n : ℝ)) * z i := by
    have hgm_one_univ :
        (∏ i ∈ (Finset.univ : Finset (Fin n)), z i ^ (1 / (n : ℝ))) = 1 := by
      simpa using hgm_one
    have hrhs_univ :
        (∑ i ∈ (Finset.univ : Finset (Fin n)), (1 / (n : ℝ)) * z i) = 1 := by
      simpa using hrhs
    exact hgm_one_univ.trans hrhs_univ.symm
  have hall :=
    (Real.geom_mean_eq_arith_mean_weighted_iff'
      (s := (Finset.univ : Finset (Fin n)))
      (w := fun _ : Fin n => (1 / (n : ℝ))) (z := z)
      hw hw' hz').mp heq_gm_am
  intro i
  have hi := hall i (Finset.mem_univ i)
  exact hi.trans hrhs

/-- Higham, 2nd ed., Chapter 14, Problem 14.11 support:
    equality in the positive-definite Hadamard determinant inequality forces
    every off-diagonal entry to vanish. -/
theorem higham14_problem14_11_posDef_offdiag_eq_zero_of_det_eq_prod_diag
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef)
    (heq : Matrix.det M = ∏ i : Fin n, M i i) :
    ∀ ⦃i j : Fin n⦄, i ≠ j → M i j = 0 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    intro i
    exact Fin.elim0 i
  have hpos : ∀ i : Fin n, 0 < M i i := fun i => hM.diag_pos
  set d : Fin n → ℝ := fun i => (Real.sqrt (M i i))⁻¹ with hd
  set D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal d with hD
  have hdsq : ∀ i : Fin n, d i * d i = (M i i)⁻¹ := by
    intro i
    have hs : Real.sqrt (M i i) * Real.sqrt (M i i) = M i i :=
      Real.mul_self_sqrt (hpos i).le
    simp only [hd]
    rw [← mul_inv, hs]
  set C : Matrix (Fin n) (Fin n) ℝ := D * M * D with hC
  have hCij : ∀ i j : Fin n, C i j = d i * M i j * d j := by
    intro i j
    simp [hC, hD, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq]
  have hCii : ∀ i : Fin n, C i i = 1 := by
    intro i
    rw [hCij i i]
    calc d i * M i i * d i = d i * d i * M i i := by ring
      _ = (M i i)⁻¹ * M i i := by rw [hdsq i]
      _ = 1 := inv_mul_cancel₀ (hpos i).ne'
  have hstar : star d = d := by ext i; simp
  have hCpsd : C.PosSemidef := by
    have h1 := hM.posSemidef.conjTranspose_mul_mul_same D
    rw [hD, Matrix.diagonal_conjTranspose, hstar] at h1
    rw [hC, hD]
    exact h1
  have hCherm : C.IsHermitian := hCpsd.1
  have hprodd : (∏ i : Fin n, d i) * (∏ i : Fin n, d i) =
      (∏ i : Fin n, M i i)⁻¹ := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun i _ => hdsq i)
  have hdetC : C.det = M.det * (∏ i : Fin n, M i i)⁻¹ := by
    rw [hC, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    calc (∏ i : Fin n, d i) * M.det * (∏ i : Fin n, d i)
        = M.det * ((∏ i : Fin n, d i) * (∏ i : Fin n, d i)) := by ring
      _ = M.det * (∏ i : Fin n, M i i)⁻¹ := by rw [hprodd]
  have hdetC_eig : C.det = ∏ i : Fin n, hCherm.eigenvalues i := by
    rw [hCherm.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
  have htraceC_eig : C.trace = ∑ i : Fin n, hCherm.eigenvalues i := by
    rw [hCherm.trace_eq_sum_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id]
  have htraceC : C.trace = (n : ℝ) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [Finset.sum_congr rfl (fun i _ => hCii i)]
    simp
  have hsum_eig : ∑ i : Fin n, hCherm.eigenvalues i = (n : ℝ) := by
    rw [← htraceC_eig, htraceC]
  have hprodpos : 0 < ∏ i : Fin n, M i i :=
    Finset.prod_pos fun i _ => hpos i
  have hdetC_one : C.det = 1 := by
    rw [hdetC, heq, mul_inv_cancel₀ hprodpos.ne']
  have hprod_eig_one : ∏ i : Fin n, hCherm.eigenvalues i = 1 := by
    rw [← hdetC_eig, hdetC_one]
  have heig_one : ∀ i : Fin n, hCherm.eigenvalues i = 1 :=
    higham14_amgm_all_eq_one_of_sum_eq_card_prod_eq_one hn
      hCherm.eigenvalues (fun i => hCpsd.eigenvalues_nonneg i)
      hsum_eig hprod_eig_one
  have hCeq_one : C = 1 := by
    rw [hCherm.spectral_theorem]
    have hdiag :
        Matrix.diagonal (RCLike.ofReal ∘ hCherm.eigenvalues) =
          (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.diagonal, heig_one i]
      · simp [Matrix.diagonal, hij]
    rw [hdiag]
    simp
  intro i j hij
  have hCij_zero : C i j = 0 := by
    have hentry := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N i j) hCeq_one
    simpa [Matrix.one_apply, hij] using hentry
  have hdi_ne : d i ≠ 0 := by
    simp [hd, (Real.sqrt_pos.mpr (hpos i)).ne']
  have hdj_ne : d j ≠ 0 := by
    simp [hd, (Real.sqrt_pos.mpr (hpos j)).ne']
  rw [hCij i j] at hCij_zero
  have hleft : d i * M i j = 0 := by
    exact (mul_eq_zero.mp hCij_zero).resolve_right hdj_ne
  exact (mul_eq_zero.mp hleft).resolve_left hdi_ne

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    pairwise orthogonal rows attain equality in Hadamard's determinant
    inequality.  This is the source equality direction that does not require
    excluding zero rows. -/
theorem higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_rowsOrthogonal
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (horth : higham14_rowsOrthogonal A) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      ∏ i : Fin n, higham14_rowNorm2 A i := by
  have hgram :
      let AM : Matrix (Fin n) (Fin n) ℝ := A
      AM * Matrix.transpose AM =
        Matrix.diagonal (fun i : Fin n => ∑ k : Fin n, A i k ^ 2) := by
    dsimp only
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
    · simp [Matrix.mul_apply, Matrix.transpose_apply, hij, horth hij]
  have hsquare :
      (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 =
        (∏ i : Fin n, higham14_rowNorm2 A i) ^ 2 := by
    have hdetGram :
        let AM : Matrix (Fin n) (Fin n) ℝ := A
        Matrix.det (AM * Matrix.transpose AM) =
          (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 := by
      dsimp only
      rw [Matrix.det_mul, Matrix.det_transpose]
      ring
    rw [← hdetGram, hgram, Matrix.det_diagonal]
    rw [← Finset.prod_pow]
    simp [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq]
  exact (sq_eq_sq₀ (abs_nonneg _) (Finset.prod_nonneg fun i _ =>
    higham14_rowNorm2_nonneg A i)).mp (by
      rw [sq_abs]
      exact hsquare)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    equality in Hadamard's determinant inequality implies `ψ(A) = 1` for
    nonsingular `A`.  This isolates the algebraic condition-number bridge from
    the harder equality-characterization step. -/
theorem higham14_problem14_11_hadamardConditionNumber_eq_one_of_abs_det_eq_prod_rowNorm2
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (heq :
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, higham14_rowNorm2 A i) :
    higham14_hadamardConditionNumber A = 1 := by
  have hden_ne : |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| ≠ 0 :=
    abs_ne_zero.mpr hdet
  unfold higham14_hadamardConditionNumber
  rw [← heq]
  exact div_self hden_ne

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    if `ψ(A) = 1` for nonsingular `A`, then Hadamard's determinant inequality
    is attained with equality. -/
theorem higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_hadamardConditionNumber_eq_one
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hpsi : higham14_hadamardConditionNumber A = 1) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      ∏ i : Fin n, higham14_rowNorm2 A i := by
  have hden_ne : |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| ≠ 0 :=
    abs_ne_zero.mpr hdet
  unfold higham14_hadamardConditionNumber at hpsi
  have hmul :=
    congrArg
      (fun x : ℝ =>
        x * |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) hpsi
  dsimp only at hmul
  rw [div_mul_cancel₀ _ hden_ne] at hmul
  simpa [one_mul] using hmul.symm

/-- Higham, 2nd ed., Chapter 14, Problem 14.11 support:
    if `psi(A)=1` for nonsingular `A`, then the associated row Gram matrix
    attains equality in the positive-definite Hadamard determinant bound. -/
theorem higham14_problem14_11_gram_det_eq_prod_diag_of_hadamardConditionNumber_eq_one
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hpsi : higham14_hadamardConditionNumber A = 1) :
    let AM : Matrix (Fin n) (Fin n) ℝ := A
    Matrix.det (AM * Matrix.transpose AM) =
      ∏ i : Fin n, (AM * Matrix.transpose AM) i i :=
  higham14_problem14_11_gram_det_eq_prod_diag_of_abs_det_eq_prod_rowNorm2 A
    (higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_hadamardConditionNumber_eq_one
      A hdet hpsi)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    for nonsingular `A`, the normalized condition-number statement `ψ(A) = 1`
    is equivalent to equality in Hadamard's determinant inequality. -/
theorem higham14_problem14_11_hadamardConditionNumber_eq_one_iff_abs_det_eq_prod_rowNorm2
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    higham14_hadamardConditionNumber A = 1 ↔
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, higham14_rowNorm2 A i := by
  constructor
  · exact
      higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_hadamardConditionNumber_eq_one
        A hdet
  · exact
      higham14_problem14_11_hadamardConditionNumber_eq_one_of_abs_det_eq_prod_rowNorm2
        A hdet

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    nonsingular matrices with pairwise orthogonal rows have `ψ(A) = 1`. -/
theorem higham14_problem14_11_hadamardConditionNumber_eq_one_of_rowsOrthogonal
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (horth : higham14_rowsOrthogonal A) :
    higham14_hadamardConditionNumber A = 1 :=
  higham14_problem14_11_hadamardConditionNumber_eq_one_of_abs_det_eq_prod_rowNorm2
    A hdet
    (higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_rowsOrthogonal A horth)

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    equality in Hadamard's determinant inequality for a nonsingular matrix
    forces pairwise orthogonal rows. -/
theorem higham14_problem14_11_rowsOrthogonal_of_abs_det_eq_prod_rowNorm2
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (heq :
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, higham14_rowNorm2 A i) :
    higham14_rowsOrthogonal A := by
  rw [higham14_rowsOrthogonal_iff_gram_offdiag_zero A]
  dsimp only
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  have hgram_eq :
      Matrix.det (AM * Matrix.transpose AM) =
        ∏ i : Fin n, (AM * Matrix.transpose AM) i i := by
    simpa [AM] using
      higham14_problem14_11_gram_det_eq_prod_diag_of_abs_det_eq_prod_rowNorm2
        A heq
  have hAT :
      Matrix.conjTranspose AM = Matrix.transpose AM :=
    Matrix.conjTranspose_eq_transpose_of_trivial AM
  have hGpsd : (AM * Matrix.transpose AM).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose AM
    rwa [hAT] at h
  have hAunit : IsUnit AM :=
    (Matrix.isUnit_iff_isUnit_det AM).mpr (isUnit_iff_ne_zero.mpr (by simpa [AM] using hdet))
  have hATunit : IsUnit (Matrix.transpose AM) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (by simpa [AM] using hdet)
  have hGpd : (AM * Matrix.transpose AM).PosDef :=
    (hGpsd.posDef_iff_isUnit).mpr (hAunit.mul hATunit)
  exact
    higham14_problem14_11_posDef_offdiag_eq_zero_of_det_eq_prod_diag
      (AM * Matrix.transpose AM) hGpd hgram_eq

/-- Higham, 2nd ed., Chapter 14, Problem 14.11:
    for nonsingular `A`, `ψ(A) = 1` forces pairwise orthogonal rows. -/
theorem higham14_problem14_11_rowsOrthogonal_of_hadamardConditionNumber_eq_one
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hpsi : higham14_hadamardConditionNumber A = 1) :
    higham14_rowsOrthogonal A :=
  higham14_problem14_11_rowsOrthogonal_of_abs_det_eq_prod_rowNorm2 A hdet
    (higham14_problem14_11_abs_det_eq_prod_rowNorm2_of_hadamardConditionNumber_eq_one
      A hdet hpsi)

/-- Higham, 2nd ed., Chapter 14, Problem 14.12:
    Euclidean norm of column `j`, the quantity `rho_j = ||R(:,j)||_2` in the
    QR formula for the Hadamard condition number. -/
noncomputable def higham14_colNorm2 {n : ℕ}
    (A : Fin n → Fin n → ℝ) (j : Fin n) : ℝ :=
  vecNorm2 (fun i : Fin n => A i j)

/-- Orthogonal real matrices have determinant of absolute value one. -/
lemma higham14_abs_det_eq_one_of_isOrthogonal {n : ℕ}
    {Q : Fin n → Fin n → ℝ} (hQ : IsOrthogonal n Q) :
    |Matrix.det (Q : Matrix (Fin n) (Fin n) ℝ)| = 1 := by
  let QM : Matrix (Fin n) (Fin n) ℝ := Q
  have hmat :
      Matrix.transpose QM * QM = 1 := by
    ext i j
    simpa [QM, Matrix.mul_apply, Matrix.transpose_apply, matTranspose, idMatrix]
      using hQ.left_inv i j
  have hsquare : Matrix.det QM ^ 2 = 1 := by
    have hdet := congrArg Matrix.det hmat
    simpa [Matrix.det_mul, Matrix.det_transpose, pow_two] using hdet
  have habs_square : |Matrix.det QM| ^ 2 = 1 := by
    rw [sq_abs, hsquare]
  rcases (sq_eq_one_iff.mp habs_square) with h | h
  · simpa [QM] using h
  · have hnonneg : 0 ≤ |Matrix.det QM| := abs_nonneg _
    linarith

/-- Left multiplication by an orthogonal matrix preserves each column
    Euclidean norm. -/
lemma higham14_colNorm2_matMul_orthogonal_left {n : ℕ}
    (Q R : Fin n → Fin n → ℝ) (hQ : IsOrthogonal n Q) (j : Fin n) :
    higham14_colNorm2 (matMul n Q R) j = higham14_colNorm2 R j := by
  unfold higham14_colNorm2 matMul
  exact vecNorm2_orthogonal Q (fun k : Fin n => R k j) hQ

/-- In a QR factorization of `A^T`, row norms of `A` are column norms of `R`. -/
lemma higham14_rowNorm2_eq_colNorm2_of_transpose_qr {n : ℕ}
    (A Q R : Fin n → Fin n → ℝ)
    (hQR : ∀ i j : Fin n, A j i = matMul n Q R i j)
    (hQ : IsOrthogonal n Q) (i : Fin n) :
    higham14_rowNorm2 A i = higham14_colNorm2 R i := by
  calc
    higham14_rowNorm2 A i = higham14_colNorm2 (matMul n Q R) i := by
      unfold higham14_rowNorm2 higham14_colNorm2
      congr 1
      ext j
      exact hQR j i
    _ = higham14_colNorm2 R i :=
        higham14_colNorm2_matMul_orthogonal_left Q R hQ i

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(a):
    if `A^T = Q R` with `Q` orthogonal and `det(R) = prod_i r_ii`, then the
    Hadamard condition number satisfies
    `psi(A) = prod_i rho_i / |r_ii|`, where `rho_i = ||R(:,i)||_2`.

    The determinant-product hypothesis is separated out so callers can use any
    triangular or otherwise suitable QR certificate. -/
theorem higham14_problem14_12_hadamardConditionNumber_eq_prod_colNorm2_div_abs_diag_of_transpose_qr_det_product
    {n : ℕ} (A Q R : Fin n → Fin n → ℝ)
    (hQR : ∀ i j : Fin n, A j i = matMul n Q R i j)
    (hQ : IsOrthogonal n Q)
    (hdetR : Matrix.det (R : Matrix (Fin n) (Fin n) ℝ) = ∏ i : Fin n, R i i) :
    higham14_hadamardConditionNumber A =
      ∏ i : Fin n, higham14_colNorm2 R i / |R i i| := by
  have hrow : ∀ i : Fin n, higham14_rowNorm2 A i = higham14_colNorm2 R i :=
    higham14_rowNorm2_eq_colNorm2_of_transpose_qr A Q R hQR hQ
  have hQRmat :
      let AM : Matrix (Fin n) (Fin n) ℝ := A
      let QM : Matrix (Fin n) (Fin n) ℝ := Q
      let RM : Matrix (Fin n) (Fin n) ℝ := R
      Matrix.transpose AM = QM * RM := by
    dsimp only
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, matMul] using hQR i j
  have hdetA :
      Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.det (Q : Matrix (Fin n) (Fin n) ℝ) * (∏ i : Fin n, R i i) := by
    let AM : Matrix (Fin n) (Fin n) ℝ := A
    let QM : Matrix (Fin n) (Fin n) ℝ := Q
    let RM : Matrix (Fin n) (Fin n) ℝ := R
    have hdet_trans :
        Matrix.det (Matrix.transpose AM) = Matrix.det (QM * RM) := by
      simpa [AM, QM, RM] using congrArg Matrix.det hQRmat
    rw [Matrix.det_transpose, Matrix.det_mul] at hdet_trans
    simpa [AM, QM, RM, hdetR] using hdet_trans
  have hden :
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, |R i i| := by
    rw [hdetA, abs_mul, higham14_abs_det_eq_one_of_isOrthogonal hQ, one_mul,
      Finset.abs_prod]
  unfold higham14_hadamardConditionNumber
  rw [Finset.prod_congr rfl (fun i _ => hrow i), hden]
  rw [← Finset.prod_div_distrib]

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(a):
    source-shaped QR formula for `psi(A)` when `A^T = Q R`, `Q` is orthogonal,
    and `R` is upper triangular. -/
theorem higham14_problem14_12_hadamardConditionNumber_eq_prod_colNorm2_div_abs_diag_of_transpose_qr
    {n : ℕ} (A Q R : Fin n → Fin n → ℝ)
    (hQR : ∀ i j : Fin n, A j i = matMul n Q R i j)
    (hQ : IsOrthogonal n Q)
    (hRupper : (show Matrix (Fin n) (Fin n) ℝ from R).BlockTriangular id) :
    higham14_hadamardConditionNumber A =
      ∏ i : Fin n, higham14_colNorm2 R i / |R i i| :=
  higham14_problem14_12_hadamardConditionNumber_eq_prod_colNorm2_div_abs_diag_of_transpose_qr_det_product
    A Q R hQR hQ (Matrix.det_of_upperTriangular hRupper)

private lemma higham14_problem14_12_prod_nat_sub_eq_factorial (n : ℕ) :
    (∏ i ∈ Finset.range n, (n - i)) = Nat.factorial n := by
  calc
    (∏ i ∈ Finset.range n, (n - i))
        = ∏ i ∈ Finset.range n, ((n - 1 - i) + 1) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hi_lt : i < n := Finset.mem_range.mp hi
            omega
    _ = ∏ i ∈ Finset.range n, (i + 1) := by
            rw [Finset.prod_range_reflect (fun i : ℕ => i + 1) n]
    _ = Nat.factorial n := by
            rw [Finset.prod_range_add_one_eq_factorial]

private lemma higham14_problem14_12_prod_fin_nat_sub_eq_factorial (n : ℕ) :
    (∏ i : Fin n, (n - i.val)) = Nat.factorial n := by
  rw [Fin.prod_univ_eq_prod_range]
  exact higham14_problem14_12_prod_nat_sub_eq_factorial n

private lemma higham14_problem14_12_stressUpper_one_upper (n : ℕ) :
    (show Matrix (Fin n) (Fin n) ℝ from higham8_3_stressUpper n 1).BlockTriangular id := by
  intro i j hji
  have hv : j.val < i.val := by simpa using hji
  have hij : i ≠ j := by
    intro h
    subst j
    exact (lt_irrefl i.val) hv
  have hnot : ¬ i.val < j.val := by omega
  simp [higham8_3_stressUpper, hij, hnot]

private lemma higham14_problem14_12_det_stressUpper_one (n : ℕ) :
    Matrix.det (higham8_3_stressUpper n 1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  rw [Matrix.det_of_upperTriangular (higham14_problem14_12_stressUpper_one_upper n)]
  simp [higham8_3_stressUpper]

private lemma higham14_problem14_12_sum_tail_one (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, if i.val ≤ j.val then (1 : ℝ) else 0) =
      (n - i.val : ℝ) := by
  have hlt :
      (Finset.univ.filter (fun j : Fin n => j.val < i.val)).card = i.val := by
    simpa [Nat.min_eq_right (Nat.le_of_lt i.isLt)] using
      (Fin.card_filter_val_lt (n := n) (m := i.val))
  have hpart :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun j : Fin n => j.val < i.val)
  have htail :
      (Finset.univ.filter (fun j : Fin n => ¬ j.val < i.val)).card = n - i.val := by
    rw [Finset.card_univ, Fintype.card_fin] at hpart
    omega
  have htail' :
      (Finset.univ.filter (fun j : Fin n => i.val ≤ j.val)).card = n - i.val := by
    simpa only [not_lt] using htail
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [htail']
  exact Nat.cast_sub (Nat.le_of_lt i.isLt)

private lemma higham14_problem14_12_rowNorm2_sq_stressUpper_one
    (n : ℕ) (i : Fin n) :
    higham14_rowNorm2 (higham8_3_stressUpper n 1) i ^ 2 =
      (n - i.val : ℝ) := by
  rw [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq]
  have hsquare : ∀ j : Fin n,
      higham8_3_stressUpper n 1 i j ^ 2 =
        if i.val ≤ j.val then (1 : ℝ) else 0 := by
    intro j
    by_cases hle : i.val ≤ j.val
    · by_cases hij : i = j
      · subst j
        simp [higham8_3_stressUpper]
      · have hlt : i.val < j.val := by
          exact lt_of_le_of_ne hle (by
            intro hval
            exact hij (Fin.ext hval))
        simp [higham8_3_stressUpper, hij, hlt, hle]
    · have hij : i ≠ j := by
        intro h
        subst j
        exact hle (le_refl i.val)
      have hnotlt : ¬ i.val < j.val := by omega
      simp [higham8_3_stressUpper, hij, hnotlt, hle]
  simp_rw [hsquare]
  rw [higham14_problem14_12_sum_tail_one n i]

private lemma higham14_problem14_12_rowNorm2_stressUpper_one
    (n : ℕ) (i : Fin n) :
    higham14_rowNorm2 (higham8_3_stressUpper n 1) i =
      Real.sqrt ((n - i.val : ℕ) : ℝ) := by
  exact
    (sq_eq_sq₀
      (higham14_rowNorm2_nonneg (higham8_3_stressUpper n 1) i)
      (Real.sqrt_nonneg _)).mp (by
        rw [higham14_problem14_12_rowNorm2_sq_stressUpper_one n i,
          Real.sq_sqrt (Nat.cast_nonneg _)]
        exact (Nat.cast_sub (Nat.le_of_lt i.isLt)).symm)

private lemma higham14_problem14_12_prod_rowNorm2_stressUpper_one (n : ℕ) :
    (∏ i : Fin n, higham14_rowNorm2 (higham8_3_stressUpper n 1) i) =
      Real.sqrt (Nat.factorial n : ℝ) := by
  calc
    (∏ i : Fin n, higham14_rowNorm2 (higham8_3_stressUpper n 1) i)
        = ∏ i : Fin n, Real.sqrt ((n - i.val : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro i _
            exact higham14_problem14_12_rowNorm2_stressUpper_one n i
    _ = Real.sqrt (∏ i : Fin n, ((n - i.val : ℕ) : ℝ)) := by
            exact (Real.sqrt_prod Finset.univ
              (fun i _ => Nat.cast_nonneg (n - i.val))).symm
    _ = Real.sqrt (Nat.factorial n : ℝ) := by
            have hprod :
                (∏ i : Fin n, ((n - i.val : ℕ) : ℝ)) =
                  (Nat.factorial n : ℝ) := by
              exact_mod_cast higham14_problem14_12_prod_fin_nat_sub_eq_factorial n
            rw [hprod]

/-- Higham, 2nd ed., Appendix A, Problem 14.12(b), printed p.560:
    for the Chapter 8 stress matrix `U(1)`, the Hadamard determinant condition
    number is `sqrt(n!)`.  Lean indexes rows as `0, ..., n-1`, so row `i` has
    `n - i` unit entries. -/
theorem higham14_problem14_12_hadamardConditionNumber_stressUpper_one_eq_sqrt_factorial
    (n : ℕ) :
    higham14_hadamardConditionNumber (higham8_3_stressUpper n 1) =
      Real.sqrt (Nat.factorial n : ℝ) := by
  unfold higham14_hadamardConditionNumber
  rw [higham14_problem14_12_prod_rowNorm2_stressUpper_one n,
    higham14_problem14_12_det_stressUpper_one n]
  norm_num

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b):
    the Pei matrix `A = (alpha - 1) I + e e^T`, equivalently diagonal entries
    `alpha` and off-diagonal entries `1`. -/
noncomputable def higham14_peiMatrix (n : ℕ) (α : ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then α else 1

private lemma higham14_problem14_12_peiMatrix_eq_smul_one_add_rankOne
    (n : ℕ) (α : ℝ) (hα : α - 1 ≠ 0) :
    (higham14_peiMatrix n α : Matrix (Fin n) (Fin n) ℝ) =
      (α - 1) •
        (1 + Matrix.replicateCol Unit (fun _ : Fin n => (α - 1)⁻¹) *
          Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℝ))) := by
  funext i j
  change (if i = j then α else 1) =
    (α - 1) *
      (((1 : Matrix (Fin n) (Fin n) ℝ) +
        Matrix.replicateCol Unit (fun _ : Fin n => (α - 1)⁻¹) *
          Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℝ))) i j)
  by_cases hij : i = j
  · subst j
    simp [Matrix.add_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    field_simp [hα]
    ring
  · simp [hij, Matrix.add_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    field_simp [hα]

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b), dependency:
    determinant of the Pei matrix `(alpha - 1) I + e e^T`. -/
lemma higham14_problem14_12_peiMatrix_det
    (n : ℕ) (α : ℝ) (hn : 0 < n) (hα : α - 1 ≠ 0) :
    Matrix.det (higham14_peiMatrix n α : Matrix (Fin n) (Fin n) ℝ) =
      ((n : ℝ) + α - 1) * (α - 1) ^ (n - 1) := by
  let β : ℝ := α - 1
  have hβ : β ≠ 0 := by simpa [β] using hα
  let M : Matrix (Fin n) (Fin n) ℝ :=
    1 + Matrix.replicateCol Unit (fun _ : Fin n => β⁻¹) *
      Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℝ))
  have hmatrix :
      (higham14_peiMatrix n α : Matrix (Fin n) (Fin n) ℝ) = β • M := by
    dsimp [M, β]
    exact higham14_problem14_12_peiMatrix_eq_smul_one_add_rankOne n α hα
  rw [hmatrix]
  change Matrix.det (β • M) = ((n : ℝ) + α - 1) * (α - 1) ^ (n - 1)
  rw [Matrix.det_smul]
  rw [Fintype.card_fin]
  have hdetM : Matrix.det M = 1 + (n : ℝ) * β⁻¹ := by
    dsimp [M]
    rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct, Finset.sum_const, Fintype.card_fin]
  rw [hdetM]
  have hn_eq : n = (n - 1) + 1 := by omega
  rw [hn_eq, pow_succ]
  dsimp [β]
  field_simp [hα]
  ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b), dependency:
    every row of the Pei matrix has squared Euclidean norm
    `alpha^2 + n - 1`. -/
lemma higham14_problem14_12_peiMatrix_row_sq_sum
    (n : ℕ) (α : ℝ) (i : Fin n) :
    (∑ j : Fin n, (higham14_peiMatrix n α i j) ^ 2) =
      α ^ 2 + ((n - 1 : ℕ) : ℝ) := by
  calc
    (∑ j : Fin n, (higham14_peiMatrix n α i j) ^ 2)
        = ∑ j : Fin n, ((1 : ℝ) + if j = i then α ^ 2 - 1 else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hji : j = i
            · subst j
              simp [higham14_peiMatrix]
            · have hij : i ≠ j := by exact Ne.symm hji
              simp [higham14_peiMatrix, hij, hji]
    _ = α ^ 2 + ((n - 1 : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, Fintype.card_fin]
        have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
        rw [Nat.cast_sub (Nat.succ_le_of_lt hnpos)]
        ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b), dependency:
    row norm of the Pei matrix. -/
lemma higham14_problem14_12_peiMatrix_rowNorm2
    (n : ℕ) (α : ℝ) (i : Fin n) :
    higham14_rowNorm2 (higham14_peiMatrix n α) i =
      Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ)) := by
  have harg_nonneg : 0 ≤ α ^ 2 + ((n - 1 : ℕ) : ℝ) :=
    add_nonneg (sq_nonneg α) (Nat.cast_nonneg _)
  exact (sq_eq_sq₀ (higham14_rowNorm2_nonneg _ _) (Real.sqrt_nonneg _)).mp (by
    rw [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq]
    rw [Real.sq_sqrt harg_nonneg]
    exact higham14_problem14_12_peiMatrix_row_sq_sum n α i)

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b), dependency:
    numerator product of the Pei matrix Hadamard condition number. -/
lemma higham14_problem14_12_peiMatrix_prod_rowNorm2
    (n : ℕ) (α : ℝ) :
    (∏ i : Fin n, higham14_rowNorm2 (higham14_peiMatrix n α) i) =
      (Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ))) ^ n := by
  calc
    (∏ i : Fin n, higham14_rowNorm2 (higham14_peiMatrix n α) i)
        = ∏ _i : Fin n, Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ)) := by
            apply Finset.prod_congr rfl
            intro i _
            exact higham14_problem14_12_peiMatrix_rowNorm2 n α i
    _ = (Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ))) ^ n := by
            simp [Fintype.card_fin]

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b):
    Pei-matrix Hadamard condition-number formula in the nonnegative
    `|det(A)|` denominator convention used by `higham14_hadamardConditionNumber`. -/
theorem higham14_problem14_12_hadamardConditionNumber_peiMatrix_abs
    (n : ℕ) (α : ℝ) (hn : 0 < n) (hα : α - 1 ≠ 0) :
    higham14_hadamardConditionNumber (higham14_peiMatrix n α) =
      (Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ))) ^ n /
        |((n : ℝ) + α - 1) * (α - 1) ^ (n - 1)| := by
  unfold higham14_hadamardConditionNumber
  rw [higham14_problem14_12_peiMatrix_prod_rowNorm2,
    higham14_problem14_12_peiMatrix_det n α hn hα]

/-- Higham, 2nd ed., Chapter 14, Problem 14.12(b), Appendix A:
    for the Pei matrix `A = (alpha - 1) I + e e^T` with `alpha > 1`,
    `psi(A) = (sqrt(alpha^2 + n - 1))^n /
      ((n + alpha - 1) * (alpha - 1)^(n - 1))`. -/
theorem higham14_problem14_12_hadamardConditionNumber_peiMatrix
    (n : ℕ) (α : ℝ) (hn : 0 < n) (hα : 1 < α) :
    higham14_hadamardConditionNumber (higham14_peiMatrix n α) =
      (Real.sqrt (α ^ 2 + ((n - 1 : ℕ) : ℝ))) ^ n /
        (((n : ℝ) + α - 1) * (α - 1) ^ (n - 1)) := by
  have hαsub_pos : 0 < α - 1 := by linarith
  have hαne : α - 1 ≠ 0 := ne_of_gt hαsub_pos
  have hden_pos : 0 < ((n : ℝ) + α - 1) * (α - 1) ^ (n - 1) := by
    have hfirst : 0 < (n : ℝ) + α - 1 := by
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact mul_pos hfirst (pow_pos hαsub_pos _)
  rw [higham14_problem14_12_hadamardConditionNumber_peiMatrix_abs n α hn hαne,
    abs_of_pos hden_pos]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    finite AM-GM in the product form used by Appendix A.  For nonnegative
    `z_i`, `prod_i z_i <= ((sum_i z_i)/n)^n`. -/
theorem higham14_problem14_13_amgm_prod_le_pow_sum_div_card {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) :
    (∏ i : Fin n, z i) ≤ ((∑ i : Fin n, z i) / (n : ℝ)) ^ n := by
  let S : ℝ := ∑ i : Fin n, z i
  by_cases hS : S = 0
  · have hz_zero : ∀ i, z i = 0 := by
      have hsum_zero : ∑ i : Fin n, z i = 0 := by simpa [S] using hS
      have hterms := (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin n))) (f := z)
        (by intro i _; exact hz i)).mp hsum_zero
      intro i
      exact hterms i (Finset.mem_univ i)
    have hprod_zero : ∏ i : Fin n, z i = 0 := by
      let i : Fin n := ⟨0, hn⟩
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (hz_zero i)]
    have hsum_zero : ∑ i : Fin n, z i = 0 := by simpa [S] using hS
    rw [hprod_zero, hsum_zero]
    exact pow_nonneg (div_nonneg le_rfl (Nat.cast_nonneg n)) n
  · have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg (fun i _ => hz i)
    have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS)
    let y : Fin n → ℝ := fun i => (n : ℝ) / S * z i
    have hy_nonneg : ∀ i, 0 ≤ y i := by
      intro i
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg n) hS_nonneg) (hz i)
    have hy_sum : ∑ i : Fin n, y i = n := by
      dsimp [y]
      rw [← Finset.mul_sum]
      change ((n : ℝ) / S) * S = (n : ℝ)
      field_simp [hS]
    have hy_prod_le_one : ∏ i : Fin n, y i ≤ 1 :=
      higham9_amgm_prod_le_one_of_sum_eq_card hn y hy_nonneg hy_sum
    have hy_prod :
        ∏ i : Fin n, y i = ((n : ℝ) / S) ^ n * ∏ i : Fin n, z i := by
      dsimp [y]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    have hscale_pos : 0 < (S / (n : ℝ)) ^ n :=
      pow_pos (div_pos hS_pos (Nat.cast_pos.mpr hn)) n
    have hmain :
        ((n : ℝ) / S) ^ n * ∏ i : Fin n, z i ≤ 1 := by
      rwa [← hy_prod]
    have hmul := mul_le_mul_of_nonneg_left hmain hscale_pos.le
    have hcancel :
        (S / (n : ℝ)) ^ n * (((n : ℝ) / S) ^ n * ∏ i : Fin n, z i) =
          ∏ i : Fin n, z i := by
      have hfac : (S / (n : ℝ)) * ((n : ℝ) / S) = 1 := by
        field_simp [hS, Nat.cast_ne_zero.mpr hn.ne']
      calc
        (S / (n : ℝ)) ^ n * (((n : ℝ) / S) ^ n * ∏ i : Fin n, z i)
            = ((S / (n : ℝ)) ^ n * ((n : ℝ) / S) ^ n) *
                ∏ i : Fin n, z i := by ring
        _ = (((S / (n : ℝ)) * ((n : ℝ) / S)) ^ n) *
                ∏ i : Fin n, z i := by rw [mul_pow]
        _ = ∏ i : Fin n, z i := by rw [hfac]; simp
    have hrhs :
        (S / (n : ℝ)) ^ n * 1 = (S / (n : ℝ)) ^ n := by ring
    simpa [S] using (by rwa [hcancel, hrhs] at hmul)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the Appendix A AM-GM algebra in squared form.  The family `z` represents
    the `n` numbers whose geometric mean is
    `(kappa * |det(A)| / 2)^(2/n)` in the source proof. -/
theorem higham14_problem14_13_gej_squared_bound_from_amgm {n : ℕ} (hn : 0 < n)
    (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i)
    {p frob : ℝ}
    (hprod : (∏ i : Fin n, z i) = p ^ 2)
    (hsum_lt : (∑ i : Fin n, z i) < frob ^ 2) :
    p ^ 2 < (frob ^ 2 / (n : ℝ)) ^ n := by
  have hprod_le :=
    higham14_problem14_13_amgm_prod_le_pow_sum_div_card hn z hz
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, z i :=
    Finset.sum_nonneg (fun i _ => hz i)
  have hdiv_lt :
      (∑ i : Fin n, z i) / (n : ℝ) < frob ^ 2 / (n : ℝ) :=
    div_lt_div_of_pos_right hsum_lt (Nat.cast_pos.mpr hn)
  have hdiv_nonneg : 0 ≤ (∑ i : Fin n, z i) / (n : ℝ) :=
    div_nonneg hsum_nonneg (Nat.cast_nonneg n)
  have hpow_lt :
      ((∑ i : Fin n, z i) / (n : ℝ)) ^ n <
        (frob ^ 2 / (n : ℝ)) ^ n :=
    pow_lt_pow_left₀ hdiv_lt hdiv_nonneg hn.ne'
  calc
    p ^ 2 = ∏ i : Fin n, z i := hprod.symm
    _ ≤ ((∑ i : Fin n, z i) / (n : ℝ)) ^ n := hprod_le
    _ < (frob ^ 2 / (n : ℝ)) ^ n := hpow_lt

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    convert the squared GEJ AM-GM conclusion to the printed inequality shape
    `kappa < 2/|det(A)| * (||A||_F/sqrt(n))^n`. -/
theorem higham14_problem14_13_gej_bound_from_squared
    {n : ℕ} (hn : 0 < n) {kappa detAbs frob : ℝ}
    (hdet_pos : 0 < detAbs)
    (hkappa_nonneg : 0 ≤ kappa)
    (hfrob_nonneg : 0 ≤ frob)
    (hsq :
      (kappa * detAbs / 2) ^ 2 < (frob ^ 2 / (n : ℝ)) ^ n) :
    kappa < (2 / detAbs) * (frob / Real.sqrt (n : ℝ)) ^ n := by
  have hnR_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr hnR_pos
  have hbase_nonneg : 0 ≤ frob / Real.sqrt (n : ℝ) :=
    div_nonneg hfrob_nonneg hsqrtn_pos.le
  have hrhs_nonneg : 0 ≤ (frob / Real.sqrt (n : ℝ)) ^ n :=
    pow_nonneg hbase_nonneg n
  have hp_nonneg : 0 ≤ kappa * detAbs / 2 := by
    positivity
  have hrhs_sq :
      ((frob / Real.sqrt (n : ℝ)) ^ n) ^ 2 =
        (frob ^ 2 / (n : ℝ)) ^ n := by
    calc
      ((frob / Real.sqrt (n : ℝ)) ^ n) ^ 2
          = ((frob / Real.sqrt (n : ℝ)) ^ 2) ^ n := by
              rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = (frob ^ 2 / (n : ℝ)) ^ n := by
              rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hp_lt :
      kappa * detAbs / 2 < (frob / Real.sqrt (n : ℝ)) ^ n :=
    (sq_lt_sq₀ hp_nonneg hrhs_nonneg).mp (by
      simpa [hrhs_sq] using hsq)
  have hscale_pos : 0 < 2 / detAbs := div_pos (by norm_num) hdet_pos
  have hmul := mul_lt_mul_of_pos_left hp_lt hscale_pos
  have hleft : (2 / detAbs) * (kappa * detAbs / 2) = kappa := by
    field_simp [hdet_pos.ne']
  rwa [hleft] at hmul

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    source-shaped AM-GM certificate theorem.  Supplying the singular-value
    product certificate and the strict Frobenius-sum comparison yields the GEJ
    determinant/condition inequality. -/
theorem higham14_problem14_13_gej_bound_from_amgm_certificate
    {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ)
    {kappa detAbs frob : ℝ}
    (hdet_pos : 0 < detAbs)
    (hkappa_nonneg : 0 ≤ kappa)
    (hfrob_nonneg : 0 ≤ frob)
    (hz : ∀ i, 0 ≤ z i)
    (hprod : (∏ i : Fin n, z i) = (kappa * detAbs / 2) ^ 2)
    (hsum_lt : (∑ i : Fin n, z i) < frob ^ 2) :
    kappa < (2 / detAbs) * (frob / Real.sqrt (n : ℝ)) ^ n :=
  higham14_problem14_13_gej_bound_from_squared hn hdet_pos hkappa_nonneg
    hfrob_nonneg
    (higham14_problem14_13_gej_squared_bound_from_amgm hn z hz hprod hsum_lt)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the repository's exact real operator `2`-norm agrees with the operator
    norm of the complexified real matrix. -/
theorem higham14_problem14_13_opNorm2_eq_complexMatrixOp2_realRectToCMatrix
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    opNorm2 A = complexMatrixOp2 (realRectToCMatrix A) := by
  apply le_antisymm
  · exact opNorm2_le_of_opNorm2Le A
      (complexMatrixOp2_nonneg (realRectToCMatrix A))
      (opNorm2Le_complexMatrixOp2_realRectToCMatrix A)
  · exact complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le A
      (opNorm2_nonneg A) (opNorm2Le_opNorm2 A)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the real operator `2`-norm is the largest ordered singular value of the
    complexified real matrix. -/
theorem higham14_problem14_13_opNorm2_eq_complex_top_singularValue
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) :
    opNorm2 A =
      complexMatrixSingularValue (realRectToCMatrix A) ⟨0, hn⟩ := by
  rw [higham14_problem14_13_opNorm2_eq_complexMatrixOp2_realRectToCMatrix A]
  exact complexMatrixOp2_eq_top_singularValue hn (realRectToCMatrix A)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the real Frobenius square agrees with the Frobenius square of the
    complexified real matrix. -/
theorem higham14_problem14_13_frobNorm_sq_eq_complexMatrixFrobeniusSq
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    frobNorm A ^ 2 = complexMatrixFrobeniusSq (realRectToCMatrix A) := by
  rw [frobNorm_sq]
  unfold frobNormSq complexMatrixFrobeniusSq realRectToCMatrix
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [complexNorm_ofReal_eq_abs, sq_abs]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the Frobenius square of a real matrix is the sum of the squared ordered
    singular values of its complexification. -/
theorem higham14_problem14_13_frobNorm_sq_eq_sum_complex_singularValue_sq
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    frobNorm A ^ 2 =
      ∑ i : Fin n, complexMatrixSingularValue (realRectToCMatrix A) i ^ 2 := by
  rw [higham14_problem14_13_frobNorm_sq_eq_complexMatrixFrobeniusSq A]
  exact complexMatrixFrobeniusSq_eq_sum_singularValue_sq (realRectToCMatrix A)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the Euclidean lower norm of a real `(k+1) x (k+1)` matrix equals its last
    ordered singular value after complexification. -/
theorem higham14_problem14_13_lowerNorm_eq_complex_last_singularValue
    {k : ℕ} (A : Fin (k + 1) → Fin (k + 1) → ℝ) :
    matMulVecLowerNorm2 (Nat.succ_pos k) A =
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) := by
  let sigma : ℝ := complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)
  have hsigma_nonneg : 0 ≤ sigma := by
    simpa [sigma] using
      complexMatrixSingularValue_nonneg (realRectToCMatrix A) (Fin.last k)
  apply le_antisymm
  · obtain ⟨x, hx_ne, hx_eq⟩ :=
      realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq A
    have hx_norm_ne : vecNorm2 x ≠ 0 := by
      intro hx_zero
      apply hx_ne
      funext i
      exact (vecNorm2_eq_zero_iff x).mp hx_zero i
    have hx_norm_pos : 0 < vecNorm2 x :=
      lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hx_norm_ne)
    let y : Fin (k + 1) → ℝ := fun i => (vecNorm2 x)⁻¹ * x i
    have hy_unit : vecNorm2 y = 1 :=
      vecNorm2_inv_smul_self_of_pos x hx_norm_pos
    have hAy_sq : vecNorm2 (matMulVec (k + 1) A y) ^ 2 = sigma ^ 2 := by
      have hAx_sq : vecNorm2 (matMulVec (k + 1) A x) ^ 2 =
          sigma ^ 2 * vecNorm2 x ^ 2 := by
        rw [vecNorm2_sq, vecNorm2_sq]
        simpa [sigma, matMulVec, rectMatMulVec] using hx_eq
      have hAy_eq : matMulVec (k + 1) A y =
          fun i => (vecNorm2 x)⁻¹ * matMulVec (k + 1) A x i := by
        simpa [y] using matMulVec_const_mul_right (k + 1) A (vecNorm2 x)⁻¹ x
      calc
        vecNorm2 (matMulVec (k + 1) A y) ^ 2
            = ((vecNorm2 x)⁻¹ * vecNorm2 (matMulVec (k + 1) A x)) ^ 2 := by
                rw [hAy_eq, vecNorm2_smul, abs_of_pos (inv_pos.mpr hx_norm_pos)]
        _ = (vecNorm2 x)⁻¹ ^ 2 * vecNorm2 (matMulVec (k + 1) A x) ^ 2 := by
                ring
        _ = (vecNorm2 x)⁻¹ ^ 2 * (sigma ^ 2 * vecNorm2 x ^ 2) := by
                rw [hAx_sq]
        _ = sigma ^ 2 := by
                field_simp [hx_norm_ne]
    have hAy_norm : vecNorm2 (matMulVec (k + 1) A y) = sigma := by
      exact (sq_eq_sq₀ (vecNorm2_nonneg _) hsigma_nonneg).mp hAy_sq
    calc
      matMulVecLowerNorm2 (Nat.succ_pos k) A
          ≤ vecNorm2 (matMulVec (k + 1) A y) :=
            matMulVecLowerNorm2_le (Nat.succ_pos k) A y hy_unit
      _ = sigma := hAy_norm
  · obtain ⟨y, hy_unit, hy_eq⟩ :=
      matMulVecLowerNorm2_attained (Nat.succ_pos k) A
    have hlower :=
      complexMatrixSingularValue_last_mul_norm_le_norm_euclideanLin
        (realRectToCMatrix A) (realVecToEuclidean y)
    have hsigma_le : sigma ≤ vecNorm2 (matMulVec (k + 1) A y) := by
      simpa [sigma, realVecToEuclidean_norm,
        realRectToCMatrix_euclideanLin_realVecToEuclidean_norm, hy_unit,
        matMulVec, rectMatMulVec] using hlower
    rwa [← hy_eq] at hsigma_le

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    a certified right inverse has operator norm equal to the reciprocal of the
    last ordered singular value of the original matrix. -/
theorem higham14_problem14_13_opNorm2_rightInverse_eq_inv_complex_last_singularValue
    {k : ℕ} (A Ainv : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv) :
    opNorm2 Ainv =
      (complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k))⁻¹ := by
  have hlower :=
    matMulVecLowerNorm2_eq_inv_opNorm2_of_isRightInverse
      (Nat.succ_pos k) A Ainv hRight
  have hlast :=
    higham14_problem14_13_lowerNorm_eq_complex_last_singularValue A
  have hinv :
      (opNorm2 Ainv)⁻¹ =
        complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) := by
    rw [← hlower]
    exact hlast
  calc
    opNorm2 Ainv = ((opNorm2 Ainv)⁻¹)⁻¹ := by rw [inv_inv]
    _ = (complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k))⁻¹ := by
          rw [hinv]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    for a supplied right inverse, `kappa2` is `sigma_1 / sigma_n` in the
    ordered singular values of the complexified real matrix. -/
theorem higham14_problem14_13_kappa2_eq_top_div_last_singularValue_of_rightInverse
    {k : ℕ} (A Ainv : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv) :
    kappa2 A Ainv =
      complexMatrixSingularValue (realRectToCMatrix A) ⟨0, Nat.succ_pos k⟩ /
        complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) := by
  rw [kappa2,
    higham14_problem14_13_opNorm2_eq_complex_top_singularValue (Nat.succ_pos k) A,
    higham14_problem14_13_opNorm2_rightInverse_eq_inv_complex_last_singularValue
      A Ainv hRight,
    div_eq_mul_inv]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    determinant of the complex Gram linear map as the product of its ordered
    Gram eigenvalues. -/
theorem higham14_problem14_13_complexGramLin_det_eq_prod_gramEigenvalues
    {n : ℕ} (A : CMatrix n n) :
    LinearMap.det (complexMatrixGramLin A) =
      ∏ i : Fin n, (complexMatrixGramEigenvalues A i : ℂ) := by
  let ob := complexMatrixGramEigenvectorBasis A
  let b := ob.toBasis
  have hmat : LinearMap.toMatrix b b (complexMatrixGramLin A) =
      Matrix.diagonal (fun i : Fin n => (complexMatrixGramEigenvalues A i : ℂ)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have happ := complexMatrixGramLin_apply_eigenvectorBasis A j
    change b.repr ((complexMatrixGramLin A) (b j)) i =
      Matrix.diagonal (fun i : Fin n => (complexMatrixGramEigenvalues A i : ℂ)) i j
    have hb_j : b j = complexMatrixGramEigenvectorBasis A j := by rfl
    rw [hb_j, happ]
    rw [OrthonormalBasis.coe_toBasis_repr_apply]
    rw [map_smul, OrthonormalBasis.repr_self]
    by_cases hji : j = i
    · subst i
      rw [WithLp.ofLp_smul, Pi.smul_apply, EuclideanSpace.single_apply]
      simp
    · have hij : i ≠ j := fun h => hji h.symm
      rw [WithLp.ofLp_smul, Pi.smul_apply, EuclideanSpace.single_apply]
      simp [Matrix.diagonal, hij]
  rw [← LinearMap.det_toMatrix b (complexMatrixGramLin A), hmat,
    Matrix.det_diagonal]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    determinant of `Aᴴ A` is the product of squared ordered singular values. -/
theorem higham14_problem14_13_complex_det_conjTranspose_mul_self_eq_prod_singularValue_sq
    {n : ℕ} (A : CMatrix n n) :
    Matrix.det ((complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A) =
      ∏ i : Fin n, ((complexMatrixSingularValue A i : ℂ) ^ 2) := by
  have hdet_toMatrix := LinearMap.det_toMatrix (complexEuclideanBasisFin n)
    (complexMatrixGramLin A)
  rw [complexMatrixGramLin_toMatrix] at hdet_toMatrix
  calc
    Matrix.det ((complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A)
        = LinearMap.det (complexMatrixGramLin A) := hdet_toMatrix
    _ = ∏ i : Fin n, (complexMatrixGramEigenvalues A i : ℂ) :=
        higham14_problem14_13_complexGramLin_det_eq_prod_gramEigenvalues A
    _ = ∏ i : Fin n, ((complexMatrixSingularValue A i : ℂ) ^ 2) := by
        apply Finset.prod_congr rfl
        intro i _
        rw [← Complex.ofReal_pow, complexMatrixSingularValue_sq]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    square of a real determinant as the product of squared ordered singular
    values of the complexified real matrix. -/
theorem higham14_problem14_13_real_det_sq_eq_prod_complex_singularValue_sq
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    (Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 =
      ∏ i : Fin n, complexMatrixSingularValue (realRectToCMatrix A) i ^ 2 := by
  let C : CMatrix n n := realRectToCMatrix A
  have hdetC : Matrix.det (complexCMatrixAsMatrix C) =
      ((Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) : ℝ) : ℂ) := by
    dsimp [C]
    symm
    exact RingHom.map_det (algebraMap ℝ ℂ)
      (A : Matrix (Fin n) (Fin n) ℝ)
  have hleft :
      Matrix.det ((complexCMatrixAsMatrix C).conjTranspose * complexCMatrixAsMatrix C) =
        (((Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, hdetC]
    simp [pow_two]
  have h :=
    higham14_problem14_13_complex_det_conjTranspose_mul_self_eq_prod_singularValue_sq C
  rw [hleft] at h
  apply Complex.ofReal_injective
  calc
    (((Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ^ 2 : ℝ) : ℂ)
        = ∏ i : Fin n,
            ((complexMatrixSingularValue (realRectToCMatrix A) i : ℂ) ^ 2) := by
            simpa [C] using h
    _ = ((∏ i : Fin n,
            complexMatrixSingularValue (realRectToCMatrix A) i ^ 2 : ℝ) : ℂ) := by
        calc
          (∏ i : Fin n,
              ((complexMatrixSingularValue (realRectToCMatrix A) i : ℂ) ^ 2))
              = ∏ i : Fin n,
                  ((complexMatrixSingularValue (realRectToCMatrix A) i ^ 2 : ℝ) : ℂ) := by
                apply Finset.prod_congr rfl
                intro i _
                rw [Complex.ofReal_pow]
          _ = ((∏ i : Fin n,
                  complexMatrixSingularValue (realRectToCMatrix A) i ^ 2 : ℝ) : ℂ) :=
                (Complex.ofReal_prod Finset.univ
                  (fun i : Fin n =>
                    complexMatrixSingularValue (realRectToCMatrix A) i ^ 2)).symm

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    absolute value of a real determinant as the product of ordered singular
    values of the complexified real matrix. -/
theorem higham14_problem14_13_abs_det_eq_prod_complex_singularValue
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      ∏ i : Fin n, complexMatrixSingularValue (realRectToCMatrix A) i := by
  apply (sq_eq_sq₀ (abs_nonneg _) (Finset.prod_nonneg
    (fun i _ => complexMatrixSingularValue_nonneg (realRectToCMatrix A) i))).mp
  rw [sq_abs]
  rw [← Finset.prod_pow Finset.univ 2
    (fun i : Fin n => complexMatrixSingularValue (realRectToCMatrix A) i)]
  exact higham14_problem14_13_real_det_sq_eq_prod_complex_singularValue_sq A

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    a supplied right inverse makes the determinant strictly nonzero in
    absolute value. -/
theorem higham14_problem14_13_abs_det_pos_of_isRightInverse
    {n : ℕ} (A Ainv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A Ainv) :
    0 < |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| := by
  let AM : Matrix (Fin n) (Fin n) ℝ := A
  let AinvM : Matrix (Fin n) (Fin n) ℝ := Ainv
  have hmat :
      AM * AinvM = 1 := by
    ext i j
    simpa [AM, AinvM, Matrix.mul_apply] using hRight i j
  have hdet_prod : Matrix.det AM * Matrix.det AinvM = 1 := by
    calc
      Matrix.det AM * Matrix.det AinvM = Matrix.det (AM * AinvM) := by
        rw [Matrix.det_mul]
      _ = Matrix.det (1 : Matrix (Fin n) (Fin n) ℝ) := by
        rw [hmat]
      _ = 1 := Matrix.det_one
  have hdet_ne : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    intro hzero
    have hzeroAM : Matrix.det AM = 0 := by
      simpa [AM] using hzero
    rw [hzeroAM, zero_mul] at hdet_prod
    norm_num at hdet_prod
  exact abs_pos.mpr hdet_ne

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    matrix-shaped AM-GM certificate wrapper for the GEJ bound.  This removes
    the scalar positivity hypotheses from
    `higham14_problem14_13_gej_bound_from_amgm_certificate` when a right
    inverse is supplied. -/
theorem higham14_problem14_13_gej_bound_from_matrix_amgm_certificate
    {n : ℕ} (hn : 0 < n) (A Ainv : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hRight : IsRightInverse n A Ainv)
    (hz : ∀ i, 0 ≤ z i)
    (hprod :
      (∏ i : Fin n, z i) =
        (kappa2 A Ainv *
          |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| / 2) ^ 2)
    (hsum_lt : (∑ i : Fin n, z i) < frobNorm A ^ 2) :
    kappa2 A Ainv <
      (2 / |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) *
        (frobNorm A / Real.sqrt (n : ℝ)) ^ n := by
  exact
    higham14_problem14_13_gej_bound_from_amgm_certificate hn z
      (higham14_problem14_13_abs_det_pos_of_isRightInverse A Ainv hRight)
      (mul_nonneg (opNorm2_nonneg A) (opNorm2_nonneg Ainv))
      (frobNorm_nonneg A)
      hz hprod hsum_lt

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 / equation (14.37):
    the source AM-GM family for dimensions `k + 2`.  Its entries are
    `sigma_1^2/2`, `sigma_1^2/2`, and then `sigma_2^2, ..., sigma_{n-1}^2`,
    using zero-based ordered singular-value indices. -/
noncomputable def higham14_problem14_13_gejAmgmFamily
    {k : ℕ} (A : Fin (k + 2) → Fin (k + 2) → ℝ) :
    Fin (k + 2) → ℝ :=
  let sigma := fun i : Fin (k + 2) =>
    complexMatrixSingularValue (realRectToCMatrix A) i
  Fin.cons (sigma 0 ^ 2 / 2)
    (Fin.cons (sigma 0 ^ 2 / 2)
      (fun i : Fin k => sigma i.castSucc.succ ^ 2))

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the source GEJ AM-GM family is nonnegative. -/
theorem higham14_problem14_13_gejAmgmFamily_nonneg
    {k : ℕ} (A : Fin (k + 2) → Fin (k + 2) → ℝ) :
    ∀ i, 0 ≤ higham14_problem14_13_gejAmgmFamily A i := by
  intro i
  refine Fin.cases ?h0 ?hs i
  · simp [higham14_problem14_13_gejAmgmFamily]
    positivity
  · intro j
    refine Fin.cases ?h1 ?ht j
    · simp [higham14_problem14_13_gejAmgmFamily]
      positivity
    · intro t
      simp [higham14_problem14_13_gejAmgmFamily]
      positivity

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    a supplied right inverse makes the last ordered singular value positive. -/
theorem higham14_problem14_13_last_singularValue_pos_of_isRightInverse
    {k : ℕ} (A Ainv : Fin (k + 2) → Fin (k + 2) → ℝ)
    (hRight : IsRightInverse (k + 2) A Ainv) :
    0 <
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last (k + 1)) := by
  let sigma := fun i : Fin (k + 2) =>
    complexMatrixSingularValue (realRectToCMatrix A) i
  have hdet_pos :=
    higham14_problem14_13_abs_det_pos_of_isRightInverse A Ainv hRight
  have hprod_pos : 0 < ∏ i : Fin (k + 2), sigma i := by
    rwa [higham14_problem14_13_abs_det_eq_prod_complex_singularValue A] at hdet_pos
  have hprod_ne : (∏ i : Fin (k + 2), sigma i) ≠ 0 := ne_of_gt hprod_pos
  have hlast_ne : sigma (Fin.last (k + 1)) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hprod_ne)
      (Fin.last (k + 1)) (Finset.mem_univ _)
  exact lt_of_le_of_ne
    (complexMatrixSingularValue_nonneg (realRectToCMatrix A) (Fin.last (k + 1)))
    (Ne.symm hlast_ne)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    product certificate for the source GEJ AM-GM family. -/
theorem higham14_problem14_13_gejAmgmFamily_prod
    {k : ℕ} (A Ainv : Fin (k + 2) → Fin (k + 2) → ℝ)
    (hRight : IsRightInverse (k + 2) A Ainv) :
    (∏ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) =
      (kappa2 A Ainv *
        |Matrix.det (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)| / 2) ^ 2 := by
  let sigma := fun i : Fin (k + 2) =>
    complexMatrixSingularValue (realRectToCMatrix A) i
  let midProd : ℝ := ∏ i : Fin k, sigma i.castSucc.succ
  have hlast_pos :=
    higham14_problem14_13_last_singularValue_pos_of_isRightInverse A Ainv hRight
  have hlast_ne : sigma (Fin.last (k + 1)) ≠ 0 := ne_of_gt hlast_pos
  have hmid_sq :
      (∏ i : Fin k, sigma i.castSucc.succ ^ 2) = midProd ^ 2 := by
    dsimp [midProd]
    rw [← Finset.prod_pow]
  have hprodz :
      (∏ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) =
        (sigma 0 ^ 2 * midProd / 2) ^ 2 := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [higham14_problem14_13_gejAmgmFamily, sigma, hmid_sq]
    ring
  have hprefixprod :
      (∏ i : Fin (k + 1), sigma (Fin.castSucc i)) = sigma 0 * midProd := by
    rw [Fin.prod_univ_succ]
    simp [midProd]
  have hprod_all :
      (∏ i : Fin (k + 2), sigma i) =
        (sigma 0 * midProd) * sigma (Fin.last (k + 1)) := by
    rw [Fin.prod_univ_castSucc]
    rw [hprefixprod]
  have hdet :
      |Matrix.det (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)| =
        (sigma 0 * midProd) * sigma (Fin.last (k + 1)) := by
    rw [higham14_problem14_13_abs_det_eq_prod_complex_singularValue A]
    exact hprod_all
  have hkappa :=
    higham14_problem14_13_kappa2_eq_top_div_last_singularValue_of_rightInverse
      A Ainv hRight
  calc
    (∏ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i)
        = (sigma 0 ^ 2 * midProd / 2) ^ 2 := hprodz
    _ = (kappa2 A Ainv *
          |Matrix.det (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)| / 2) ^ 2 := by
        rw [hkappa, hdet]
        dsimp [sigma]
        field_simp [hlast_ne]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    the source GEJ AM-GM sum misses exactly the positive last singular-value
    square from the Frobenius-square sum. -/
theorem higham14_problem14_13_gejAmgmFamily_sum_add_last_singularValue_sq
    {k : ℕ} (A : Fin (k + 2) → Fin (k + 2) → ℝ) :
    (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) +
        complexMatrixSingularValue (realRectToCMatrix A) (Fin.last (k + 1)) ^ 2 =
      frobNorm A ^ 2 := by
  let sigma := fun i : Fin (k + 2) =>
    complexMatrixSingularValue (realRectToCMatrix A) i
  have hsumz :
      (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) =
        sigma 0 ^ 2 + ∑ i : Fin k, sigma i.castSucc.succ ^ 2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp [higham14_problem14_13_gejAmgmFamily, sigma]
    ring
  have hprefix :
      (∑ i : Fin (k + 1), sigma (Fin.castSucc i) ^ 2) =
        sigma 0 ^ 2 + ∑ i : Fin k, sigma i.castSucc.succ ^ 2 := by
    rw [Fin.sum_univ_succ]
    simp [sigma]
  calc
    (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) +
        sigma (Fin.last (k + 1)) ^ 2
        = (∑ i : Fin (k + 1), sigma (Fin.castSucc i) ^ 2) +
            sigma (Fin.last (k + 1)) ^ 2 := by
            rw [hsumz, hprefix]
    _ = ∑ i : Fin (k + 2), sigma i ^ 2 := by
        rw [Fin.sum_univ_castSucc (fun i : Fin (k + 2) => sigma i ^ 2)]
    _ = frobNorm A ^ 2 := by
        rw [higham14_problem14_13_frobNorm_sq_eq_sum_complex_singularValue_sq A]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 support:
    strict Frobenius-sum certificate for the source GEJ AM-GM family. -/
theorem higham14_problem14_13_gejAmgmFamily_sum_lt_frobNorm_sq
    {k : ℕ} (A Ainv : Fin (k + 2) → Fin (k + 2) → ℝ)
    (hRight : IsRightInverse (k + 2) A Ainv) :
    (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) <
      frobNorm A ^ 2 := by
  let sigma := fun i : Fin (k + 2) =>
    complexMatrixSingularValue (realRectToCMatrix A) i
  have hlast_pos :=
    higham14_problem14_13_last_singularValue_pos_of_isRightInverse A Ainv hRight
  have hlast_sq_pos : 0 < sigma (Fin.last (k + 1)) ^ 2 :=
    pow_pos hlast_pos 2
  have hsum_add :=
    higham14_problem14_13_gejAmgmFamily_sum_add_last_singularValue_sq A
  calc
    (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i)
        < (∑ i : Fin (k + 2), higham14_problem14_13_gejAmgmFamily A i) +
            sigma (Fin.last (k + 1)) ^ 2 :=
            lt_add_of_pos_right _ hlast_sq_pos
    _ = frobNorm A ^ 2 := hsum_add

/-- Higham, 2nd ed., Chapter 14, Problem 14.13 / equation (14.37):
    Guggenheimer-Edelman-Johnson determinant/condition inequality for
    matrices of dimension at least two, represented as `k + 2`. -/
theorem higham14_problem14_13_gej_bound_of_isRightInverse
    {k : ℕ} (A Ainv : Fin (k + 2) → Fin (k + 2) → ℝ)
    (hRight : IsRightInverse (k + 2) A Ainv) :
    kappa2 A Ainv <
      (2 / |Matrix.det (A : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ)|) *
        (frobNorm A / Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ (k + 2) := by
  exact
    higham14_problem14_13_gej_bound_from_matrix_amgm_certificate
      (Nat.succ_pos (k + 1)) A Ainv
      (higham14_problem14_13_gejAmgmFamily A) hRight
      (higham14_problem14_13_gejAmgmFamily_nonneg A)
      (higham14_problem14_13_gejAmgmFamily_prod A Ainv hRight)
      (higham14_problem14_13_gejAmgmFamily_sum_lt_frobNorm_sq A Ainv hRight)

/-- Higham, 2nd ed., Chapter 14, Problem 14.13(b) support:
    if every row has Euclidean norm one, then the Frobenius norm is
    `sqrt(n)`. -/
theorem higham14_problem14_13_frobNorm_eq_sqrt_card_of_rowNorm2_eq_one
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hrow : ∀ i : Fin n, higham14_rowNorm2 A i = 1) :
    frobNorm A = Real.sqrt (n : ℝ) := by
  refine (sq_eq_sq₀ (frobNorm_nonneg A) (Real.sqrt_nonneg _)).mp ?_
  rw [frobNorm_sq, Real.sq_sqrt (Nat.cast_nonneg n)]
  unfold frobNormSq
  calc
    (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2)
        = ∑ i : Fin n, higham14_rowNorm2 A i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            simp [higham14_rowNorm2, vecNorm2_sq, vecNorm2Sq]
    _ = ∑ _i : Fin n, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hrow i, one_pow]
    _ = (n : ℝ) := by
            simp [Fintype.card_fin]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13(b) support:
    for unit row norms, the Hadamard condition number is `1 / |det(A)|`. -/
theorem higham14_problem14_13_hadamardConditionNumber_eq_inv_abs_det_of_rowNorm2_eq_one
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hrow : ∀ i : Fin n, higham14_rowNorm2 A i = 1) :
    higham14_hadamardConditionNumber A =
      1 / |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| := by
  unfold higham14_hadamardConditionNumber
  have hprod : (∏ i : Fin n, higham14_rowNorm2 A i) = 1 := by
    simpa using Finset.prod_eq_one (fun i _ => hrow i)
  rw [hprod]

/-- Higham, 2nd ed., Chapter 14, Problem 14.13(b) support:
    the `2/|det(A)|` endpoint is the same as `2 * psi(A)` when all row norms
    are one. -/
theorem higham14_problem14_13_two_over_abs_det_eq_two_mul_hadamardConditionNumber
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hrow : ∀ i : Fin n, higham14_rowNorm2 A i = 1) :
    2 / |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      2 * higham14_hadamardConditionNumber A := by
  rw [higham14_problem14_13_hadamardConditionNumber_eq_inv_abs_det_of_rowNorm2_eq_one
    A hrow]
  ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.13(b) support:
    combine a supplied `kappa < 2/|det(A)|` bound with the unit-row
    Hadamard-condition-number identity. -/
theorem higham14_problem14_13_kappa_lt_two_mul_hadamardConditionNumber_of_unit_rows
    {n : ℕ} (A : Fin n → Fin n → ℝ) {kappa : ℝ}
    (hrow : ∀ i : Fin n, higham14_rowNorm2 A i = 1)
    (hkappa : kappa < 2 / |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) :
    kappa < 2 * higham14_hadamardConditionNumber A := by
  rwa [higham14_problem14_13_two_over_abs_det_eq_two_mul_hadamardConditionNumber
    A hrow] at hkappa

/-- Higham, 2nd ed., Chapter 14, Problem 14.13(b):
    if the rows are normalized to unit Euclidean norm, the GEJ inequality gives
    `kappa_2(A) < 2 * psi(A)` for dimensions at least two. -/
theorem higham14_problem14_13_kappa2_lt_two_mul_hadamardConditionNumber_of_unit_rows
    {k : ℕ} (A Ainv : Fin (k + 2) → Fin (k + 2) → ℝ)
    (hRight : IsRightInverse (k + 2) A Ainv)
    (hrow : ∀ i : Fin (k + 2), higham14_rowNorm2 A i = 1) :
    kappa2 A Ainv < 2 * higham14_hadamardConditionNumber A := by
  refine
    higham14_problem14_13_kappa_lt_two_mul_hadamardConditionNumber_of_unit_rows
      A hrow ?_
  have hgej := higham14_problem14_13_gej_bound_of_isRightInverse A Ainv hRight
  have hfrob :=
    higham14_problem14_13_frobNorm_eq_sqrt_card_of_rowNorm2_eq_one A hrow
  have hsqrt_pos : 0 < Real.sqrt (((k + 2 : ℕ) : ℝ)) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos (k + 1)))
  rw [hfrob] at hgej
  rw [div_self hsqrt_pos.ne', one_pow, mul_one] at hgej
  exact hgej

/-- Higham, 2nd ed., Chapter 14, Problem 14.15, Appendix A support:
    after the singular-value argument has produced scalar factors
    `1 + theta_i` with `|theta_i| <= eps`, Lemma 3.1 gives the determinant
    perturbation product radius `n*eps/(1-n*eps)`.

The guard is stated as `n*eps < 1`; it is the positivity condition needed for
the displayed denominator in the printed bound. -/
theorem higham14_problem14_15_theta_product_bound {n : ℕ} (hnpos : 0 < n)
    {eps : ℝ} (heps0 : 0 ≤ eps)
    (hsmall : (n : ℝ) * eps < (1 : ℝ)) (theta : Fin n → ℝ)
    (htheta : ∀ i : Fin n, |theta i| ≤ eps) :
    |(∏ i : Fin n, (1 + theta i)) - 1| ≤
      ((n : ℝ) * eps) / (1 - (n : ℝ) * eps) :=
  prod_one_add_delta_abs_sub_one_le_gamma_radius n hnpos heps0 hsmall theta htheta

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    a supplied all-index singular-value perturbation certificate reduces the
    absolute determinant relative-change bound to the scalar theta-product
    bound.  The still-open source work is to derive `htheta_sv` from the
    matrix perturbation hypotheses. -/
theorem higham14_problem14_15_abs_det_add_rel_le_of_singularValue_theta
    {n : ℕ} (hnpos : 0 < n)
    (A Delta : Fin n → Fin n → ℝ) {eps : ℝ}
    (heps0 : 0 ≤ eps) (hsmall : (n : ℝ) * eps < (1 : ℝ))
    (theta : Fin n → ℝ)
    (hdetA_pos : 0 < |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|)
    (htheta_sv : ∀ i : Fin n,
      complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i =
        complexMatrixSingularValue (realRectToCMatrix A) i * (1 + theta i))
    (htheta : ∀ i : Fin n, |theta i| ≤ eps) :
    |(|Matrix.det
          ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ)| /
        |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) - 1| ≤
      ((n : ℝ) * eps) / (1 - (n : ℝ) * eps) := by
  let B : Fin n → Fin n → ℝ := fun r c => A r c + Delta r c
  let sigmaA : Fin n → ℝ :=
    fun i => complexMatrixSingularValue (realRectToCMatrix A) i
  have hdetB_prod :
      |Matrix.det (B : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, sigmaA i * (1 + theta i) := by
    rw [higham14_problem14_13_abs_det_eq_prod_complex_singularValue B]
    apply Finset.prod_congr rfl
    intro i _
    simpa [B, sigmaA] using htheta_sv i
  have hdetA_prod :
      |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
        ∏ i : Fin n, sigmaA i := by
    simpa [sigmaA] using
      higham14_problem14_13_abs_det_eq_prod_complex_singularValue A
  have hprod_ne : (∏ i : Fin n, sigmaA i) ≠ 0 := by
    rw [← hdetA_prod]
    exact ne_of_gt hdetA_pos
  have hrel_eq :
      |Matrix.det (B : Matrix (Fin n) (Fin n) ℝ)| /
          |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| - 1 =
        (∏ i : Fin n, (1 + theta i)) - 1 := by
    rw [hdetB_prod, hdetA_prod, Finset.prod_mul_distrib]
    field_simp [hprod_ne]
  rw [show (fun r c => A r c + Delta r c) = B by rfl]
  rw [hrel_eq]
  exact higham14_problem14_15_theta_product_bound hnpos heps0 hsmall theta htheta

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    signed relative determinant-change form, obtained from the absolute-value
    determinant bridge when both determinants are positive. -/
theorem higham14_problem14_15_det_add_rel_le_of_singularValue_theta_of_det_pos
    {n : ℕ} (hnpos : 0 < n)
    (A Delta : Fin n → Fin n → ℝ) {eps : ℝ}
    (heps0 : 0 ≤ eps) (hsmall : (n : ℝ) * eps < (1 : ℝ))
    (theta : Fin n → ℝ)
    (hdetA_pos : 0 < Matrix.det (A : Matrix (Fin n) (Fin n) ℝ))
    (hdetB_pos :
      0 < Matrix.det
        ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ))
    (htheta_sv : ∀ i : Fin n,
      complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i =
        complexMatrixSingularValue (realRectToCMatrix A) i * (1 + theta i))
    (htheta : ∀ i : Fin n, |theta i| ≤ eps) :
    |(Matrix.det
          ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ) /
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) - 1| ≤
      ((n : ℝ) * eps) / (1 - (n : ℝ) * eps) := by
  have hAbs :=
    higham14_problem14_15_abs_det_add_rel_le_of_singularValue_theta
      hnpos A Delta heps0 hsmall theta (abs_pos.mpr hdetA_pos.ne')
      htheta_sv htheta
  simpa [abs_of_pos hdetA_pos, abs_of_pos hdetB_pos] using hAbs

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    an all-index absolute singular-value perturbation bound, scaled by a
    positive lower bound for the singular values of `A`, supplies the
    determinant relative-change estimate.

This is a dependency bridge toward the source theorem.  It does not prove the
Weyl/Mirsky all-index singular-value perturbation inequality; that remains the
missing spectral input. -/
theorem higham14_problem14_15_abs_det_add_rel_le_of_singularValue_abs_sub_bound
    {n : ℕ} (hnpos : 0 < n)
    (A Delta : Fin n → Fin n → ℝ) {eps delta lower : ℝ}
    (heps0 : 0 ≤ eps) (hsmall : (n : ℝ) * eps < (1 : ℝ))
    (hlower_pos : 0 < lower)
    (hlower : ∀ i : Fin n,
      lower ≤ complexMatrixSingularValue (realRectToCMatrix A) i)
    (habs : ∀ i : Fin n,
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ delta)
    (hscale : delta ≤ eps * lower)
    (hdetA_pos : 0 < |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) :
    |(|Matrix.det
          ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ)| /
        |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)|) - 1| ≤
      ((n : ℝ) * eps) / (1 - (n : ℝ) * eps) := by
  have hbase_pos :
      ∀ i : Fin n,
        0 < complexMatrixSingularValue (realRectToCMatrix A) i := by
    intro i
    exact lt_of_lt_of_le hlower_pos (hlower i)
  have hrel :
      ∀ i : Fin n,
        |complexMatrixSingularValue
            (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
          complexMatrixSingularValue (realRectToCMatrix A) i| ≤
          eps * complexMatrixSingularValue (realRectToCMatrix A) i := by
    intro i
    calc
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ delta :=
          habs i
      _ ≤ eps * lower := hscale
      _ ≤ eps * complexMatrixSingularValue (realRectToCMatrix A) i :=
          mul_le_mul_of_nonneg_left (hlower i) heps0
  obtain ⟨theta, htheta_sv, htheta_bound⟩ :=
    exists_relative_theta_of_abs_sub_le_mul_pos
      (fun i : Fin n => complexMatrixSingularValue (realRectToCMatrix A) i)
      (fun i : Fin n =>
        complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i)
      hbase_pos hrel
  exact
    higham14_problem14_15_abs_det_add_rel_le_of_singularValue_theta
      hnpos A Delta heps0 hsmall theta hdetA_pos htheta_sv htheta_bound

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    signed determinant relative-change form of the all-index absolute
    singular-value perturbation bridge, under positive determinants. -/
theorem higham14_problem14_15_det_add_rel_le_of_singularValue_abs_sub_bound_of_det_pos
    {n : ℕ} (hnpos : 0 < n)
    (A Delta : Fin n → Fin n → ℝ) {eps delta lower : ℝ}
    (heps0 : 0 ≤ eps) (hsmall : (n : ℝ) * eps < (1 : ℝ))
    (hlower_pos : 0 < lower)
    (hlower : ∀ i : Fin n,
      lower ≤ complexMatrixSingularValue (realRectToCMatrix A) i)
    (habs : ∀ i : Fin n,
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ delta)
    (hscale : delta ≤ eps * lower)
    (hdetA_pos : 0 < Matrix.det (A : Matrix (Fin n) (Fin n) ℝ))
    (hdetB_pos :
      0 < Matrix.det
        ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ)) :
    |(Matrix.det
          ((fun r c => A r c + Delta r c) : Matrix (Fin n) (Fin n) ℝ) /
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) - 1| ≤
      ((n : ℝ) * eps) / (1 - (n : ℝ) * eps) := by
  have hAbs :=
    higham14_problem14_15_abs_det_add_rel_le_of_singularValue_abs_sub_bound
      hnpos A Delta heps0 hsmall hlower_pos hlower habs hscale
      (abs_pos.mpr hdetA_pos.ne')
  simpa [abs_of_pos hdetA_pos, abs_of_pos hdetB_pos] using hAbs

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    a certified right inverse makes the last ordered singular value positive
    in every nonzero dimension. -/
theorem higham14_problem14_15_last_singularValue_pos_of_isRightInverse
    {k : ℕ} (A Ainv : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv) :
    0 <
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) := by
  have hNormPos : 0 < opNorm2 Ainv :=
    opNorm2_pos_of_right_inverse_at (Fin.last k) A Ainv hRight
  have hInvEq :=
    higham14_problem14_13_opNorm2_rightInverse_eq_inv_complex_last_singularValue
      A Ainv hRight
  have hInvPos :
      0 <
        (complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k))⁻¹ := by
    simpa [hInvEq] using hNormPos
  exact inv_pos.mp hInvPos

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    the last ordered singular value is a lower bound for all ordered singular
    values. -/
theorem higham14_problem14_15_last_singularValue_le_singularValue
    {k : ℕ} (A : Fin (k + 1) → Fin (k + 1) → ℝ) :
    ∀ i : Fin (k + 1),
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) ≤
        complexMatrixSingularValue (realRectToCMatrix A) i := by
  intro i
  exact complexMatrixSingularValue_antitone (realRectToCMatrix A) (Fin.le_last i)

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    with a certified right inverse, the source scaling
    `κ₂(A) * ||ΔA||₂ / ||A||₂` is exactly `||ΔA||₂ / σ_n(A)`, hence
    supplies the lower-scale premise needed by the determinant bridge. -/
theorem higham14_problem14_15_opNorm2_le_kappa2_scaled_last_singularValue
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv) :
    opNorm2 Delta ≤
      (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) *
        complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) := by
  let top : Fin (k + 1) := ⟨0, Nat.succ_pos k⟩
  let last : Fin (k + 1) := Fin.last k
  let sigma : Fin (k + 1) → ℝ :=
    fun i => complexMatrixSingularValue (realRectToCMatrix A) i
  have hlast_pos : 0 < sigma last := by
    simpa [sigma, last] using
      higham14_problem14_15_last_singularValue_pos_of_isRightInverse
        A Ainv hRight
  have hlast_le_top : sigma last ≤ sigma top := by
    simpa [sigma, top, last] using
      higham14_problem14_15_last_singularValue_le_singularValue A top
  have htop_pos : 0 < sigma top := lt_of_lt_of_le hlast_pos hlast_le_top
  have hlast_ne : sigma last ≠ 0 := ne_of_gt hlast_pos
  have htop_ne : sigma top ≠ 0 := ne_of_gt htop_pos
  have hkappa :
      kappa2 A Ainv = sigma top / sigma last := by
    simpa [sigma, top, last] using
      higham14_problem14_13_kappa2_eq_top_div_last_singularValue_of_rightInverse
        A Ainv hRight
  have hop : opNorm2 A = sigma top := by
    simpa [sigma, top] using
      higham14_problem14_13_opNorm2_eq_complex_top_singularValue
        (Nat.succ_pos k) A
  have hscale_eq :
      (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) * sigma last =
        opNorm2 Delta := by
    calc
      (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) * sigma last
          = ((sigma top / sigma last) * opNorm2 Delta / sigma top) *
              sigma last := by
                rw [hkappa, hop]
      _ = opNorm2 Delta := by
            field_simp [hlast_ne, htop_ne]
  simp [sigma, last, hscale_eq]

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    source-scaled determinant perturbation bridge.  If the still-open
    all-index singular-value perturbation inequality supplies
    `|σ_i(A+ΔA)-σ_i(A)| <= ||ΔA||₂`, then the matrix-specific
    `κ₂(A)||ΔA||₂/||A||₂` scaling and determinant product argument give the
    printed relative-change radius, under the necessary `n*eps < 1` guard. -/
theorem higham14_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) < (1 : ℝ))
    (habs : ∀ i : Fin (k + 1),
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ opNorm2 Delta) :
    |(|Matrix.det
          ((fun r c => A r c + Delta r c) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)| /
        |Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)|) - 1| ≤
      (((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) /
        (1 - ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) := by
  let top : Fin (k + 1) := ⟨0, Nat.succ_pos k⟩
  let last : Fin (k + 1) := Fin.last k
  let sigma : Fin (k + 1) → ℝ :=
    fun i => complexMatrixSingularValue (realRectToCMatrix A) i
  have hlast_pos : 0 < sigma last := by
    simpa [sigma, last] using
      higham14_problem14_15_last_singularValue_pos_of_isRightInverse
        A Ainv hRight
  have hlast_le_top : sigma last ≤ sigma top := by
    simpa [sigma, top, last] using
      higham14_problem14_15_last_singularValue_le_singularValue A top
  have htop_pos : 0 < sigma top := lt_of_lt_of_le hlast_pos hlast_le_top
  have hop : opNorm2 A = sigma top := by
    simpa [sigma, top] using
      higham14_problem14_13_opNorm2_eq_complex_top_singularValue
        (Nat.succ_pos k) A
  have hOpA_pos : 0 < opNorm2 A := by
    rw [hop]
    exact htop_pos
  have hkappa_nonneg : 0 ≤ kappa2 A Ainv := by
    unfold kappa2
    exact mul_nonneg (opNorm2_nonneg A) (opNorm2_nonneg Ainv)
  have heps0 :
      0 ≤ kappa2 A Ainv * opNorm2 Delta / opNorm2 A := by
    exact div_nonneg
      (mul_nonneg hkappa_nonneg (opNorm2_nonneg Delta)) hOpA_pos.le
  exact
    higham14_problem14_15_abs_det_add_rel_le_of_singularValue_abs_sub_bound
      (Nat.succ_pos k) A Delta heps0 hsmall hlast_pos
      (by
        intro i
        simpa [sigma, last] using
          higham14_problem14_15_last_singularValue_le_singularValue A i)
      habs
      (higham14_problem14_15_opNorm2_le_kappa2_scaled_last_singularValue
        A Ainv Delta hRight)
      (higham14_problem14_13_abs_det_pos_of_isRightInverse A Ainv hRight)

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    signed determinant version of the source-scaled conditional bridge, when
    both determinants are positive. -/
theorem higham14_problem14_15_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound_of_det_pos
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) < (1 : ℝ))
    (habs : ∀ i : Fin (k + 1),
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ opNorm2 Delta)
    (hdetA_pos : 0 < Matrix.det
      (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ))
    (hdetB_pos :
      0 < Matrix.det
        ((fun r c => A r c + Delta r c) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) :
    |(Matrix.det
          ((fun r c => A r c + Delta r c) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) /
        Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) - 1| ≤
      (((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) /
        (1 - ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) := by
  have hAbs :=
    higham14_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound
      A Ainv Delta hRight hsmall habs
  simpa [abs_of_pos hdetA_pos, abs_of_pos hdetB_pos] using hAbs

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 side-condition audit:
    the product-radius denominator is positive under the corrected guard
    `eps < 1/n`, because then `n*eps < 1`.

The determinant perturbation wrappers use the stronger `n*eps < 1` guard
directly; this lemma records the equivalent small-parameter form for positive
dimension. -/
theorem higham14_problem14_15_product_guard_of_lt_inv_card {n : ℕ}
    (hnpos : 0 < n) {eps : ℝ}
    (hsmall : eps < ((n : ℝ)⁻¹)) :
    (n : ℝ) * eps < (1 : ℝ) := by
  have hnreal_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnpos
  calc
    (n : ℝ) * eps < (n : ℝ) * ((n : ℝ)⁻¹) := by
      exact mul_lt_mul_of_pos_left hsmall hnreal_pos
    _ = (1 : ℝ) := by
      field_simp [ne_of_gt hnreal_pos]

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 side-condition audit:
    the weaker-looking hypothesis `eps < 1` does not imply the denominator
    guard `n*eps < 1` once `n > 1`.  For `n = 2`, `eps = 3/4` is already a
    counterexample. -/
theorem higham14_problem14_15_eps_lt_one_not_sufficient_for_product_guard :
    ∃ eps : ℝ, 0 ≤ eps ∧ eps < 1 ∧ ¬ ((2 : ℝ) * eps < 1) := by
  refine ⟨(3 : ℝ) / 4, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    source-scaled determinant perturbation bridge with the corrected
    small-parameter guard `eps < 1/(k+1)`.  It is a source-side-condition
    wrapper around the existing `n*eps < 1` determinant bridge.

The remaining spectral input is still the all-index absolute singular-value
perturbation bound supplied by `habs`. -/
theorem higham14_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound_inv_card_guard
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      kappa2 A Ainv * opNorm2 Delta / opNorm2 A <
        (((k + 1 : ℕ) : ℝ)⁻¹))
    (habs : ∀ i : Fin (k + 1),
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ opNorm2 Delta) :
    |(|Matrix.det
          ((fun r c => A r c + Delta r c) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)| /
        |Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)|) - 1| ≤
      (((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) /
        (1 - ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) := by
  have hguard :
      ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) < (1 : ℝ) :=
    higham14_problem14_15_product_guard_of_lt_inv_card (Nat.succ_pos k) hsmall
  exact
    higham14_problem14_15_abs_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound
      A Ainv Delta hRight hguard habs

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    signed determinant companion of the corrected `eps < 1/(k+1)` guard
    wrapper, under positive determinant signs. -/
theorem higham14_problem14_15_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound_inv_card_guard_of_det_pos
    {k : ℕ} (A Ainv Delta : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hRight : IsRightInverse (k + 1) A Ainv)
    (hsmall :
      kappa2 A Ainv * opNorm2 Delta / opNorm2 A <
        (((k + 1 : ℕ) : ℝ)⁻¹))
    (habs : ∀ i : Fin (k + 1),
      |complexMatrixSingularValue
          (realRectToCMatrix (fun r c => A r c + Delta r c)) i -
        complexMatrixSingularValue (realRectToCMatrix A) i| ≤ opNorm2 Delta)
    (hdetA_pos : 0 < Matrix.det
      (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ))
    (hdetB_pos :
      0 < Matrix.det
        ((fun r c => A r c + Delta r c) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) :
    |(Matrix.det
          ((fun r c => A r c + Delta r c) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) /
        Matrix.det (A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)) - 1| ≤
      (((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) /
        (1 - ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A)) := by
  have hguard :
      ((k + 1 : ℕ) : ℝ) *
          (kappa2 A Ainv * opNorm2 Delta / opNorm2 A) < (1 : ℝ) :=
    higham14_problem14_15_product_guard_of_lt_inv_card (Nat.succ_pos k) hsmall
  exact
    higham14_problem14_15_det_add_rel_le_of_kappa2_opNorm2_singularValue_abs_sub_bound_of_det_pos
      A Ainv Delta hRight hguard habs hdetA_pos hdetB_pos

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    the smallest ordered singular value of a perturbed square matrix is bounded
    below by `sigma_min(A) - delta` whenever `delta` bounds `B - A` in
    operator 2-norm.  This is the extremal singular-value perturbation line
    reused from the Chapter 20 Wedin infrastructure. -/
theorem higham14_problem14_15_sigmaMin_sub_le_sigmaMin_of_sub_rectOpNorm2Le
    {k : ℕ} (A B : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta) :
    complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) - delta ≤
      complexMatrixSingularValue (realRectToCMatrix B) (Fin.last k) := by
  simpa [wedinLemma20_11_sigmaMinCol] using
    wedinLemma20_11_sigmaMinCol_sub_le_sigmaMinCol_of_sub_rectOpNorm2Le
      A B hDelta

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    additive perturbation form of the smallest-singular-value lower bound. -/
theorem higham14_problem14_15_sigmaMin_sub_le_sigmaMin_add_of_rectOpNorm2Le
    {k : ℕ} (A Delta : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le Delta delta) :
    complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k) - delta ≤
      complexMatrixSingularValue
        (realRectToCMatrix (fun i j => A i j + Delta i j)) (Fin.last k) := by
  have hSub :
      rectOpNorm2Le
        (fun i j => (A i j + Delta i j) - A i j) delta := by
    convert hDelta using 1
    ext i j
    ring
  exact
    higham14_problem14_15_sigmaMin_sub_le_sigmaMin_of_sub_rectOpNorm2Le
      A (fun i j => A i j + Delta i j) hSub

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    a perturbation smaller than `sigma_min(A)` keeps the perturbed smallest
    singular value positive. -/
theorem higham14_problem14_15_sigmaMin_add_pos_of_rectOpNorm2Le_lt
    {k : ℕ} (A Delta : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : rectOpNorm2Le Delta delta)
    (hsmall :
      delta <
        complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)) :
    0 <
      complexMatrixSingularValue
        (realRectToCMatrix (fun i j => A i j + Delta i j)) (Fin.last k) := by
  have hSub :
      rectOpNorm2Le
        (fun i j => (A i j + Delta i j) - A i j) delta := by
    convert hDelta using 1
    ext i j
    ring
  simpa [wedinLemma20_11_sigmaMinCol] using
    wedinLemma20_11_sigmaMinCol_pos_of_sub_rectOpNorm2Le_lt
      A (fun i j => A i j + Delta i j) hSub
      (by simpa [wedinLemma20_11_sigmaMinCol] using hsmall)

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    rectangular operator-2 certificates are stable under negating the matrix.
    This lets extremal singular-value perturbation estimates be applied in
    both additive directions. -/
theorem higham14_problem14_15_rectOpNorm2Le_neg
    {m n : Nat} {M : Fin m -> Fin n -> Real} {c : Real}
    (hM : rectOpNorm2Le M c) :
    rectOpNorm2Le (fun i j => -M i j) c := by
  intro x
  have hmul :
      rectMatMulVec (fun i j => -M i j) x =
        fun i => -rectMatMulVec M x i := by
    ext i
    unfold rectMatMulVec
    calc
      (Finset.univ.sum fun j : Fin n => (-M i j) * x j)
          = Finset.univ.sum fun j : Fin n => -(M i j * x j) := by
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = -(Finset.univ.sum fun j : Fin n => M i j * x j) := by
            rw [Finset.sum_neg_distrib]
  rw [hmul]
  simpa [vecNorm2_neg] using hM x

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    absolute perturbation bound for the smallest ordered singular value.
    This closes the last-index extremal case of the all-index Weyl/Mirsky
    inequality still needed for the full determinant perturbation theorem. -/
theorem higham14_problem14_15_sigmaMin_abs_sub_le_of_rectOpNorm2Le
    {k : Nat} (A Delta : Fin (k + 1) -> Fin (k + 1) -> Real) {delta : Real}
    (hDelta : rectOpNorm2Le Delta delta) :
    |complexMatrixSingularValue
        (realRectToCMatrix (fun i j => A i j + Delta i j)) (Fin.last k) -
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)| <= delta := by
  let sigmaA : Real := complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)
  let sigmaB : Real :=
    complexMatrixSingularValue
      (realRectToCMatrix (fun i j => A i j + Delta i j)) (Fin.last k)
  have hLower : sigmaA - delta <= sigmaB := by
    simpa [sigmaA, sigmaB] using
      higham14_problem14_15_sigmaMin_sub_le_sigmaMin_add_of_rectOpNorm2Le
        A Delta hDelta
  have hNeg : rectOpNorm2Le (fun i j => -Delta i j) delta :=
    higham14_problem14_15_rectOpNorm2Le_neg hDelta
  have hReverseRaw :
      sigmaB - delta <=
        complexMatrixSingularValue
          (realRectToCMatrix
            (fun i j => (A i j + Delta i j) + -Delta i j)) (Fin.last k) := by
    simpa [sigmaB] using
      higham14_problem14_15_sigmaMin_sub_le_sigmaMin_add_of_rectOpNorm2Le
        (fun i j => A i j + Delta i j) (fun i j => -Delta i j) hNeg
  have hReverse : sigmaB - delta <= sigmaA := by
    simpa [sigmaA] using hReverseRaw
  have hRight : sigmaB - sigmaA <= delta := by linarith
  have hLeft : -delta <= sigmaB - sigmaA := by linarith
  have hAbs : |sigmaB - sigmaA| <= delta :=
    abs_le.mpr (And.intro hLeft hRight)
  simpa [sigmaA, sigmaB] using hAbs

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    operator 2-norm triangle inequality for an additive perturbation. -/
theorem higham14_problem14_15_opNorm2_add_le_of_opNorm2Le
    {k : ℕ} (A Delta : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : opNorm2Le Delta delta) :
    opNorm2 (fun i j => A i j + Delta i j) ≤ opNorm2 A + delta := by
  have hdelta_nonneg : 0 ≤ delta :=
    opNorm2Le_radius_nonneg Delta hDelta
  refine opNorm2_le_of_opNorm2Le
    (fun i j => A i j + Delta i j)
    (add_nonneg (opNorm2_nonneg A) hdelta_nonneg) ?_
  intro x
  rw [matMulVec_add_left]
  calc
    vecNorm2 (fun i => matMulVec (k + 1) A x i + matMulVec (k + 1) Delta x i)
        ≤ vecNorm2 (matMulVec (k + 1) A x) +
            vecNorm2 (matMulVec (k + 1) Delta x) :=
          vecNorm2_add_le _ _
    _ ≤ opNorm2 A * vecNorm2 x + delta * vecNorm2 x :=
          add_le_add (opNorm2Le_opNorm2 A x) (hDelta x)
    _ = (opNorm2 A + delta) * vecNorm2 x := by
          ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    largest-singular-value additive perturbation bound, expressed through the
    Chapter 14 ordered-singular-value bridge. -/
theorem higham14_problem14_15_top_singularValue_add_le_of_opNorm2Le
    {k : ℕ} (A Delta : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : opNorm2Le Delta delta) :
    complexMatrixSingularValue
        (realRectToCMatrix (fun i j => A i j + Delta i j))
        ⟨0, Nat.succ_pos k⟩ ≤
      complexMatrixSingularValue (realRectToCMatrix A)
          ⟨0, Nat.succ_pos k⟩ + delta := by
  rw [← higham14_problem14_13_opNorm2_eq_complex_top_singularValue
      (Nat.succ_pos k) (fun i j => A i j + Delta i j),
    ← higham14_problem14_13_opNorm2_eq_complex_top_singularValue
      (Nat.succ_pos k) A]
  exact higham14_problem14_15_opNorm2_add_le_of_opNorm2Le A Delta hDelta

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    square operator 2-norm certificates are stable under negating the matrix.
    This local helper lets the largest-singular-value perturbation bound be
    applied in both directions without importing the QR-specific wrapper. -/
theorem higham14_problem14_15_opNorm2Le_neg
    {n : ℕ} {M : Fin n → Fin n → ℝ} {c : ℝ}
    (hM : opNorm2Le M c) :
    opNorm2Le (fun i j => -M i j) c := by
  intro x
  have hmul :
      matMulVec n (fun i j => -M i j) x =
        fun i => -matMulVec n M x i := by
    ext i
    unfold matMulVec
    calc
      (Finset.univ.sum fun j : Fin n => (-M i j) * x j)
          = Finset.univ.sum fun j : Fin n => -(M i j * x j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = -(Finset.univ.sum fun j : Fin n => M i j * x j) := by
            rw [Finset.sum_neg_distrib]
  rw [hmul]
  simpa [vecNorm2_neg] using hM x

/-- Higham, 2nd ed., Chapter 14, Problem 14.15 support:
    absolute perturbation bound for the largest ordered singular value.  This
    is only the top-index case of the all-index Weyl/Mirsky inequality still
    needed to close the full determinant perturbation theorem. -/
theorem higham14_problem14_15_top_singularValue_abs_sub_le_of_opNorm2Le
    {k : ℕ} (A Delta : Fin (k + 1) → Fin (k + 1) → ℝ) {delta : ℝ}
    (hDelta : opNorm2Le Delta delta) :
    |complexMatrixSingularValue
        (realRectToCMatrix (fun i j => A i j + Delta i j))
        ⟨0, Nat.succ_pos k⟩ -
      complexMatrixSingularValue (realRectToCMatrix A)
        ⟨0, Nat.succ_pos k⟩| ≤ delta := by
  let top : Fin (k + 1) := ⟨0, Nat.succ_pos k⟩
  have hUpper :
      complexMatrixSingularValue
          (realRectToCMatrix (fun i j => A i j + Delta i j)) top ≤
        complexMatrixSingularValue (realRectToCMatrix A) top + delta := by
    simpa [top] using
      higham14_problem14_15_top_singularValue_add_le_of_opNorm2Le
        A Delta hDelta
  have hNeg : opNorm2Le (fun i j => -Delta i j) delta :=
    higham14_problem14_15_opNorm2Le_neg hDelta
  have hLowerRaw :
      complexMatrixSingularValue
          (realRectToCMatrix
            (fun i j => (A i j + Delta i j) + -Delta i j)) top ≤
        complexMatrixSingularValue
          (realRectToCMatrix (fun i j => A i j + Delta i j)) top + delta := by
    simpa [top] using
      higham14_problem14_15_top_singularValue_add_le_of_opNorm2Le
        (fun i j => A i j + Delta i j) (fun i j => -Delta i j) hNeg
  have hLower :
      complexMatrixSingularValue (realRectToCMatrix A) top ≤
        complexMatrixSingularValue
          (realRectToCMatrix (fun i j => A i j + Delta i j)) top + delta := by
    simpa [top] using hLowerRaw
  have hRight :
      complexMatrixSingularValue
          (realRectToCMatrix (fun i j => A i j + Delta i j)) top -
        complexMatrixSingularValue (realRectToCMatrix A) top ≤ delta := by
    linarith
  have hLeft :
      -delta ≤
        complexMatrixSingularValue
            (realRectToCMatrix (fun i j => A i j + Delta i j)) top -
          complexMatrixSingularValue (realRectToCMatrix A) top := by
    linarith
  simpa [top] using abs_le.mpr ⟨hLeft, hRight⟩

/-- Higham, 2nd ed., Chapter 14, equation (14.34), exact no-pivot/unit-lower
    LU core: the determinant is the product of the diagonal entries of `U`. -/
theorem higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i := by
  simpa using hLU.det_eq_prod_U_diag

/-- Higham, 2nd ed., Chapter 14, equation (14.34), absolute-value no-pivot
    determinant product form.  The row-interchange parity factor in GEPP is
    absent here because the certificate is an exact `A = L * U` factorization. -/
theorem higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_LUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ}
    (hLU : LUFactSpec n A L U) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      |∏ i : Fin n, U i i| := by
  rw [higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec hLU]

/-- Higham, 2nd ed., Chapter 14, equation (14.34), direct signed pivoted
    determinant relation.  If the row permutation `σ` gives `PA = L * U`,
    then `sign(σ) * det(A)` is the product of the computed pivots. -/
theorem higham14_eq14_34_perm_sign_mul_det_eq_prod_U_diag_of_PermutedLUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ} {σ : Fin n → Fin n}
    (hLU : PermutedLUFactSpec n A L U σ) :
    (Equiv.Perm.sign (Equiv.ofBijective σ hLU.perm) : ℝ) *
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i := by
  let Aσ : Fin n → Fin n → ℝ := fun i j => A (σ i) j
  have hLUσ : LUFactSpec n Aσ L U :=
    { L_diag := hLU.L_diag
      L_upper_zero := hLU.L_upper_zero
      U_lower_zero := hLU.U_lower_zero
      product_eq := by
        intro i j
        exact hLU.product_eq i j }
  have hdetσ :
      Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        ∏ i : Fin n, U i i :=
    higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec hLUσ
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective σ hLU.perm
  have hAσ :
      (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.submatrix (A : Matrix (Fin n) (Fin n) ℝ)
          eSigma (Equiv.refl (Fin n)) := by
    ext i j
    change A (σ i) j = A ((Equiv.ofBijective σ hLU.perm) i) j
    rfl
  have hperm :
      Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        (Equiv.Perm.sign eSigma : ℝ) *
          Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hAσ]
    simpa using
      (Matrix.det_permute (R := ℝ) eSigma
        (A : Matrix (Fin n) (Fin n) ℝ))
  change
    (Equiv.Perm.sign eSigma : ℝ) *
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i
  rw [← hdetσ]
  exact hperm.symm

/-- Higham, 2nd ed., Chapter 14, equation (14.34), source-oriented signed
    pivoted determinant product.  Since a permutation sign is its own inverse,
    the direct `sign(σ) * det(A)` relation is equivalent to the displayed
    `det(A) = sign(σ) * ∏ᵢ uᵢᵢ` form. -/
theorem higham14_eq14_34_det_eq_perm_sign_mul_prod_U_diag_of_PermutedLUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ} {σ : Fin n → Fin n}
    (hLU : PermutedLUFactSpec n A L U σ) :
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      (Equiv.Perm.sign (Equiv.ofBijective σ hLU.perm) : ℝ) *
        ∏ i : Fin n, U i i := by
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective σ hLU.perm
  have hdirect :=
    higham14_eq14_34_perm_sign_mul_det_eq_prod_U_diag_of_PermutedLUFactSpec
      (A := A) (L := L) (U := U) (σ := σ) hLU
  change
    (Equiv.Perm.sign eSigma : ℝ) *
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) =
      ∏ i : Fin n, U i i at hdirect
  have hsq : (Equiv.Perm.sign eSigma : ℝ) *
      (Equiv.Perm.sign eSigma : ℝ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign eSigma) with hsign | hsign <;>
      simp [hsign]
  calc
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)
        = 1 * Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by ring
    _ = ((Equiv.Perm.sign eSigma : ℝ) * (Equiv.Perm.sign eSigma : ℝ)) *
          Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by
          rw [hsq]
    _ = (Equiv.Perm.sign eSigma : ℝ) *
          ((Equiv.Perm.sign eSigma : ℝ) *
            Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) := by
          ring
    _ = (Equiv.Perm.sign eSigma : ℝ) * ∏ i : Fin n, U i i := by
          rw [hdirect]

/-- Higham, 2nd ed., Chapter 14, equation (14.34), pivoted absolute-value
    determinant product form.  A row permutation can change only the sign of
    the determinant, so a `PA = L * U` certificate gives the same absolute
    determinant product as the no-pivot core. -/
theorem higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_PermutedLUFactSpec
    {n : ℕ} {A L U : Fin n → Fin n → ℝ} {σ : Fin n → Fin n}
    (hLU : PermutedLUFactSpec n A L U σ) :
    |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| =
      |∏ i : Fin n, U i i| := by
  let Aσ : Fin n → Fin n → ℝ := fun i j => A (σ i) j
  have hLUσ : LUFactSpec n Aσ L U :=
    { L_diag := hLU.L_diag
      L_upper_zero := hLU.L_upper_zero
      U_lower_zero := hLU.U_lower_zero
      product_eq := by
        intro i j
        exact hLU.product_eq i j }
  have hdetσ :
      Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        ∏ i : Fin n, U i i :=
    higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec hLUσ
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective σ hLU.perm
  have hAσ :
      (Aσ : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.submatrix (A : Matrix (Fin n) (Fin n) ℝ)
          eSigma (Equiv.refl (Fin n)) := by
    ext i j
    change A (σ i) j = A ((Equiv.ofBijective σ hLU.perm) i) j
    rfl
  have hAbs :
      |Matrix.det (Aσ : Matrix (Fin n) (Fin n) ℝ)| =
        |Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)| := by
    rw [hAσ]
    simpa using
      (Matrix.abs_det_submatrix_equiv_equiv (R := ℝ)
        eSigma (Equiv.refl (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ))
  rw [hdetσ] at hAbs
  exact hAbs.symm

/-- Higham, 2nd ed., Chapter 14, Section 14.6.1, printed p.280:
    the row vector `hᵀ T⁻¹` in Hyman's method.  We model the
    source `(n-1)`-by-`(n-1)` block as an arbitrary `Fin n` block. -/
noncomputable def higham14_hymanRowTimesInv {n : ℕ}
    (h : Fin n → ℝ) (Tinv : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun j => ∑ k : Fin n, h k * Tinv k j

/-- Higham, 2nd ed., Chapter 14, Section 14.6.1, printed p.280:
    the Schur scalar `η - hᵀ T⁻¹ y` appearing in (14.35)--(14.36). -/
noncomputable def higham14_hymanSchur {n : ℕ}
    (h y : Fin n → ℝ) (Tinv : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) : ℝ :=
  η - ∑ j : Fin n, higham14_hymanRowTimesInv h Tinv j * y j

/-- Higham, 2nd ed., Chapter 14, Section 14.6.1, printed p.280:
    the cyclically permuted Hessenberg block matrix
    `H₁ = [[T, y], [hᵀ, η]]` used by Hyman's method. -/
noncomputable def higham14_hymanBlockMatrix {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks T (fun i (_ : Unit) => y i) (fun (_ : Unit) j => h j)
    (fun _ _ => η)

/-- Higham, 2nd ed., Chapter 14, equation (14.35), printed p.280:
    the lower block factor `[[I,0],[hᵀT⁻¹,1]]` in Hyman's LU factorization. -/
noncomputable def higham14_hymanLowerFactor {n : ℕ}
    (h : Fin n → ℝ) (Tinv : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks 1 0 (fun (_ : Unit) j => higham14_hymanRowTimesInv h Tinv j)
    (1 : Matrix Unit Unit ℝ)

/-- Higham, 2nd ed., Chapter 14, equation (14.35), printed p.280:
    the upper block factor `[[T,y],[0,η-hᵀT⁻¹y]]` in Hyman's LU factorization. -/
noncomputable def higham14_hymanUpperFactor {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ)
    (Tinv : Matrix (Fin n) (Fin n) ℝ) (η : ℝ) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ :=
  Matrix.fromBlocks T (fun i (_ : Unit) => y i) 0
    (fun _ _ => higham14_hymanSchur h y Tinv η)

lemma higham14_hymanRowTimesInv_mul_T {n : ℕ}
    (T Tinv : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (hTinv : IsLeftInverse n T Tinv) (j : Fin n) :
    ∑ x : Fin n, higham14_hymanRowTimesInv h Tinv x * T x j = h j := by
  calc
    ∑ x : Fin n, higham14_hymanRowTimesInv h Tinv x * T x j
        = ∑ x : Fin n, (∑ k : Fin n, h k * Tinv k x) * T x j := rfl
    _ = ∑ k : Fin n, h k * (∑ x : Fin n, Tinv k x * T x j) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro x _
        ring
    _ = ∑ k : Fin n, h k * (if k = j then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hTinv k j]
    _ = h j := by
        simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Higham, 2nd ed., Chapter 14, equation (14.35), printed p.280:
    exact Hyman block LU factorization of the cyclically permuted Hessenberg
    block matrix, assuming the displayed inverse certificate `T⁻¹T = I`. -/
theorem higham14_eq14_35_hyman_block_lu_factorization {n : ℕ}
    (T Tinv : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ)
    (hTinv : IsLeftInverse n T Tinv) :
    higham14_hymanBlockMatrix T y h η =
      higham14_hymanLowerFactor h Tinv *
        higham14_hymanUpperFactor T y h Tinv η := by
  ext a b
  cases a <;> cases b
  · rename_i i j
    simp [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, Matrix.mul_apply, Matrix.one_apply]
  · rename_i i u
    simp [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, Matrix.mul_apply, Matrix.one_apply]
  · rename_i u j
    simpa [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, Matrix.mul_apply]
      using (higham14_hymanRowTimesInv_mul_T T Tinv h hTinv j).symm
  · rename_i u v
    simp [higham14_hymanBlockMatrix, higham14_hymanLowerFactor,
      higham14_hymanUpperFactor, higham14_hymanSchur, Matrix.mul_apply]

/-- Higham, 2nd ed., Chapter 14, equation (14.36), printed p.280:
    determinant of the cyclically permuted Hyman block matrix is
    `det(T) * (η - hᵀT⁻¹y)`.  The separate cyclic-permutation sign converts
    this to the determinant of the original Hessenberg matrix. -/
theorem higham14_eq14_36_hyman_det_cyclic_block {n : ℕ}
    (T Tinv : Matrix (Fin n) (Fin n) ℝ) (y h : Fin n → ℝ) (η : ℝ)
    (hTinv : IsLeftInverse n T Tinv) :
    Matrix.det (higham14_hymanBlockMatrix T y h η) =
      Matrix.det T * higham14_hymanSchur h y Tinv η := by
  rw [higham14_eq14_35_hyman_block_lu_factorization T Tinv y h η hTinv]
  rw [Matrix.det_mul]
  have hdetL : Matrix.det (higham14_hymanLowerFactor h Tinv) = 1 := by
    rw [higham14_hymanLowerFactor, Matrix.det_fromBlocks_zero₁₂]
    simp
  have hdetU : Matrix.det (higham14_hymanUpperFactor T y h Tinv η) =
      Matrix.det T * higham14_hymanSchur h y Tinv η := by
    rw [higham14_hymanUpperFactor, Matrix.det_fromBlocks_zero₂₁]
    simp
  rw [hdetL, hdetU]
  ring

/-- Higham, 2nd ed., Chapter 14, equation (14.36), printed p.280:
    signed determinant formula for an original Hessenberg matrix whose row
    permutation is the cyclic Hyman block matrix.  For the source's cyclic
    permutation, the sign is the printed `(-1)^(n-1)` factor. -/
theorem higham14_eq14_36_hyman_det_original_of_row_permutation {n : ℕ}
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T Tinv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η : ℝ) (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hH :
      higham14_hymanBlockMatrix T y h η =
        Matrix.submatrix H σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTinv : IsLeftInverse n T Tinv) :
    Matrix.det H =
      (Equiv.Perm.sign σ : ℝ) *
        Matrix.det T * higham14_hymanSchur h y Tinv η := by
  have hperm_det :
      Matrix.det (higham14_hymanBlockMatrix T y h η) =
        (Equiv.Perm.sign σ : ℝ) * Matrix.det H := by
    rw [hH]
    simpa using
      (Matrix.det_permute (R := ℝ) σ H)
  have hcyclic :=
    higham14_eq14_36_hyman_det_cyclic_block
      T Tinv y h η hTinv
  have hdirect :
      (Equiv.Perm.sign σ : ℝ) * Matrix.det H =
        Matrix.det T * higham14_hymanSchur h y Tinv η := by
    rw [← hperm_det, hcyclic]
  have hsq : (Equiv.Perm.sign σ : ℝ) *
      (Equiv.Perm.sign σ : ℝ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign <;>
      simp [hsign]
  calc
    Matrix.det H = 1 * Matrix.det H := by ring
    _ = ((Equiv.Perm.sign σ : ℝ) * (Equiv.Perm.sign σ : ℝ)) *
          Matrix.det H := by
          rw [hsq]
    _ = (Equiv.Perm.sign σ : ℝ) *
          ((Equiv.Perm.sign σ : ℝ) * Matrix.det H) := by
          ring
    _ = (Equiv.Perm.sign σ : ℝ) *
          (Matrix.det T * higham14_hymanSchur h y Tinv η) := by
          rw [hdirect]
    _ = (Equiv.Perm.sign σ : ℝ) *
          Matrix.det T * higham14_hymanSchur h y Tinv η := by
          ring

/-- Higham, 2nd ed., Chapter 14, Problem 14.14, Appendix A:
    exact determinant hinge used in the Hyman backward-error proof.  If `T`
    is upper triangular, `DeltaT` has zero diagonal, and the componentwise
    bound `|DeltaT| <= gamma |T|` holds, then the bound forces `DeltaT` to
    have zero entries below the diagonal, so `T + DeltaT` has the same
    triangular determinant product as `T`. -/
theorem higham14_problem14_14_det_upper_add_zero_diag_of_abs_bound {n : ℕ}
    (T DeltaT : Matrix (Fin n) (Fin n) ℝ) (gamma : ℝ)
    (hTupper : T.BlockTriangular id)
    (hDeltaDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaBound : ∀ i j : Fin n, |DeltaT i j| ≤ gamma * |T i j|) :
    Matrix.det (T + DeltaT) = Matrix.det T := by
  have hDeltaLower : ∀ i j : Fin n, j < i → DeltaT i j = 0 := by
    intro i j hji
    have hTij : T i j = 0 := hTupper hji
    have hbound := hDeltaBound i j
    rw [hTij, abs_zero, mul_zero] at hbound
    exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  have hUpperSum : (T + DeltaT).BlockTriangular id := by
    intro i j hji
    simp [Matrix.add_apply, hTupper hji, hDeltaLower i j hji]
  rw [Matrix.det_of_upperTriangular hUpperSum, Matrix.det_of_upperTriangular hTupper]
  apply Finset.prod_congr rfl
  intro i _
  simp [Matrix.add_apply, hDeltaDiag i]

/-- Higham, 2nd ed., Chapter 14, Problem 14.14, Appendix A:
    exact Hyman determinant wrapper after perturbing the triangular solve
    block.  The determinant-invariance hinge above keeps the factor `det T`
    even though the Hyman block uses `T + DeltaT` and its inverse certificate. -/
theorem higham14_problem14_14_hyman_det_cyclic_block_of_upper_add_zero_diag
    {n : ℕ}
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gamma : ℝ)
    (hTupper : T.BlockTriangular id)
    (hDeltaDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaBound : ∀ i j : Fin n, |DeltaT i j| ≤ gamma * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    Matrix.det (higham14_hymanBlockMatrix (T + DeltaT) y h η) =
      Matrix.det T * higham14_hymanSchur h y TpertInv η := by
  rw [higham14_eq14_36_hyman_det_cyclic_block
    (T + DeltaT) TpertInv y h η hTpertInv]
  rw [higham14_problem14_14_det_upper_add_zero_diag_of_abs_bound
    T DeltaT gamma hTupper hDeltaDiag hDeltaBound]

/-- Higham, 2nd ed., Chapter 14, Problem 14.14, Appendix A:
    original-matrix Hyman determinant wrapper after perturbing the triangular
    solve block.  This combines the perturbed cyclic-block determinant formula
    with the signed row-permutation wrapper for the original Hessenberg matrix. -/
theorem higham14_problem14_14_hyman_det_original_of_upper_add_zero_diag
    {n : ℕ}
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gamma : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hH :
      higham14_hymanBlockMatrix (T + DeltaT) y h η =
        Matrix.submatrix H σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaBound : ∀ i j : Fin n, |DeltaT i j| ≤ gamma * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    Matrix.det H =
      (Equiv.Perm.sign σ : ℝ) *
        Matrix.det T * higham14_hymanSchur h y TpertInv η := by
  have horig :=
    higham14_eq14_36_hyman_det_original_of_row_permutation
      H (T + DeltaT) TpertInv y h η σ hH hTpertInv
  have hdet :
      Matrix.det (T + DeltaT) = Matrix.det T :=
    higham14_problem14_14_det_upper_add_zero_diag_of_abs_bound
      T DeltaT gamma hTupper hDeltaDiag hDeltaBound
  simpa [hdet] using horig

/-- Higham, 2nd ed., Chapter 14, Problem 14.14, Appendix A:
    absolute-value form of the perturbed original-matrix Hyman determinant
    wrapper.  The row-permutation sign disappears from the magnitude bound. -/
theorem higham14_problem14_14_abs_det_original_of_upper_add_zero_diag
    {n : ℕ}
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gamma : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hH :
      higham14_hymanBlockMatrix (T + DeltaT) y h η =
        Matrix.submatrix H σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaBound : ∀ i j : Fin n, |DeltaT i j| ≤ gamma * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    |Matrix.det H| =
      |Matrix.det T| * |higham14_hymanSchur h y TpertInv η| := by
  have hdet :=
    higham14_problem14_14_hyman_det_original_of_upper_add_zero_diag
      H T DeltaT TpertInv y h η gamma σ hH hTupper hDeltaDiag hDeltaBound
      hTpertInv
  have hsign_abs : |(Equiv.Perm.sign σ : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign <;>
      simp [hsign]
  rw [hdet, abs_mul, abs_mul, hsign_abs, one_mul]

/-- Higham, 2nd ed., Chapter 14, Problem 14.14, Appendix A:
    packaged original-matrix backward-error target for Hyman's method.  Once a
    later floating-point analysis supplies a componentwise-bounded `DeltaH`
    whose permuted block is the perturbed Hyman block, the exact determinant
    statement follows from the determinant wrappers above. -/
theorem higham14_problem14_14_exists_deltaH_det_original_of_upper_add_zero_diag
    {n : ℕ}
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gammaT gammaH : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hDeltaHCert :
      ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
        (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
        higham14_hymanBlockMatrix (T + DeltaT) y h η =
          Matrix.submatrix (H + DeltaH) σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaTDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaTBound : ∀ i j : Fin n, |DeltaT i j| ≤ gammaT * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
      Matrix.det (H + DeltaH) =
        (Equiv.Perm.sign σ : ℝ) *
          Matrix.det T * higham14_hymanSchur h y TpertInv η := by
  rcases hDeltaHCert with ⟨DeltaH, hDeltaHBound, hBlock⟩
  refine ⟨DeltaH, hDeltaHBound, ?_⟩
  exact
    higham14_problem14_14_hyman_det_original_of_upper_add_zero_diag
      (H + DeltaH) T DeltaT TpertInv y h η gammaT σ
      hBlock hTupper hDeltaTDiag hDeltaTBound hTpertInv

/-- Problem 14.14 absolute-value backward-error target for Hyman's method.
    This is the existential `DeltaH` companion to the signed determinant
    package above. -/
theorem higham14_problem14_14_exists_deltaH_abs_det_original_of_upper_add_zero_diag
    {n : ℕ}
    (H : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gammaT gammaH : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hDeltaHCert :
      ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
        (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
        higham14_hymanBlockMatrix (T + DeltaT) y h η =
          Matrix.submatrix (H + DeltaH) σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaTDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaTBound : ∀ i j : Fin n, |DeltaT i j| ≤ gammaT * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
      |Matrix.det (H + DeltaH)| =
        |Matrix.det T| * |higham14_hymanSchur h y TpertInv η| := by
  rcases
    higham14_problem14_14_exists_deltaH_det_original_of_upper_add_zero_diag
      H T DeltaT TpertInv y h η gammaT gammaH σ hDeltaHCert
      hTupper hDeltaTDiag hDeltaTBound hTpertInv
    with ⟨DeltaH, hDeltaHBound, hdet⟩
  refine ⟨DeltaH, hDeltaHBound, ?_⟩
  have hsign_abs : |(Equiv.Perm.sign σ : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign <;>
      simp [hsign]
  rw [hdet, abs_mul, abs_mul, hsign_abs, one_mul]

/-- Problem 14.14 support: diagonal similarity used to model the optional
    scaling of Hyman's Hessenberg matrix. -/
noncomputable def higham14_problem14_14_diagonalSimilarity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal d * A * Matrix.diagonal (fun i => (d i)⁻¹)

/-- Problem 14.14 support: transport a perturbation on the diagonally scaled
    matrix back to the original matrix. -/
noncomputable def higham14_problem14_14_diagonalUnscalePerturbation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (DeltaScaled : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => (d i)⁻¹) * DeltaScaled * Matrix.diagonal d

theorem higham14_problem14_14_diagonalSimilarity_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (A : Matrix ι ι ℝ) (i j : ι) :
    higham14_problem14_14_diagonalSimilarity d A i j =
      d i * A i j * (d j)⁻¹ := by
  simp [higham14_problem14_14_diagonalSimilarity, Matrix.mul_apply,
    Matrix.diagonal_apply, Finset.sum_ite_eq]

theorem higham14_problem14_14_diagonalUnscalePerturbation_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (DeltaScaled : Matrix ι ι ℝ) (i j : ι) :
    higham14_problem14_14_diagonalUnscalePerturbation d DeltaScaled i j =
      (d i)⁻¹ * DeltaScaled i j * d j := by
  simp [higham14_problem14_14_diagonalUnscalePerturbation, Matrix.mul_apply,
    Matrix.diagonal_apply, Finset.sum_ite_eq]

/-- Diagonal similarity preserves determinants.  This is the exact algebraic
    core behind the diagonal-scaling clause in Problem 14.14. -/
theorem higham14_problem14_14_det_diagonalSimilarity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (A : Matrix ι ι ℝ)
    (hd : ∀ i : ι, d i ≠ 0) :
    Matrix.det (higham14_problem14_14_diagonalSimilarity d A) =
      Matrix.det A := by
  have hprod :
      (∏ i : ι, d i) * (∏ i : ι, (d i)⁻¹) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun i _ => mul_inv_cancel₀ (hd i))
  rw [higham14_problem14_14_diagonalSimilarity, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  calc
    (∏ i : ι, d i) * Matrix.det A * (∏ i : ι, (d i)⁻¹)
        = ((∏ i : ι, d i) * (∏ i : ι, (d i)⁻¹)) * Matrix.det A := by
            ring
    _ = Matrix.det A := by
            rw [hprod]
            ring

/-- A componentwise perturbation bound on the diagonally scaled matrix
    transports back to the same relative componentwise bound on the original
    matrix. -/
theorem higham14_problem14_14_unscaled_delta_bound_of_scaled
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (H DeltaScaled : Matrix ι ι ℝ) (gamma : ℝ)
    (hd : ∀ i : ι, d i ≠ 0)
    (hDeltaScaled : ∀ i j : ι,
      |DeltaScaled i j| ≤
        gamma * |higham14_problem14_14_diagonalSimilarity d H i j|) :
    ∀ i j : ι,
      |higham14_problem14_14_diagonalUnscalePerturbation d DeltaScaled i j| ≤
        gamma * |H i j| := by
  intro i j
  have hleft_nonneg : 0 ≤ |(d i)⁻¹| := abs_nonneg _
  have hright_nonneg : 0 ≤ |d j| := abs_nonneg _
  have hmul_left :=
    mul_le_mul_of_nonneg_left (hDeltaScaled i j) hleft_nonneg
  have hmul := mul_le_mul_of_nonneg_right hmul_left hright_nonneg
  have hdi : |(d i)⁻¹| * |d i| = 1 := by
    rw [abs_inv]
    exact inv_mul_cancel₀ (abs_ne_zero.mpr (hd i))
  have hdj : |(d j)⁻¹| * |d j| = 1 := by
    rw [abs_inv]
    exact inv_mul_cancel₀ (abs_ne_zero.mpr (hd j))
  calc
    |higham14_problem14_14_diagonalUnscalePerturbation d DeltaScaled i j|
        = |(d i)⁻¹| * |DeltaScaled i j| * |d j| := by
            rw [higham14_problem14_14_diagonalUnscalePerturbation_apply,
              abs_mul, abs_mul]
    _ ≤ |(d i)⁻¹| *
          (gamma * |higham14_problem14_14_diagonalSimilarity d H i j|) *
          |d j| := hmul
    _ = gamma * |H i j| := by
            rw [higham14_problem14_14_diagonalSimilarity_apply, abs_mul,
              abs_mul]
            calc
              |(d i)⁻¹| * (gamma * (|d i| * |H i j| * |(d j)⁻¹|)) *
                  |d j|
                  = gamma * |H i j| *
                      ((|(d i)⁻¹| * |d i|) * (|(d j)⁻¹| * |d j|)) := by
                      ring
              _ = gamma * |H i j| := by
                      rw [hdi, hdj]
                      ring

/-- Problem 14.14 diagonal-scaling transport: a determinant certificate and
    componentwise perturbation bound for the scaled Hessenberg matrix give the
    same determinant certificate and relative bound after unscaling. -/
theorem higham14_problem14_14_unscale_deltaH_det_of_diagonal_scaled_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H Hscaled DeltaHscaled : Matrix ι ι ℝ) (d : ι → ℝ)
    (gamma theta : ℝ)
    (hd : ∀ i : ι, d i ≠ 0)
    (hHscaled : Hscaled = higham14_problem14_14_diagonalSimilarity d H)
    (hDeltaScaled : ∀ i j : ι, |DeltaHscaled i j| ≤ gamma * |Hscaled i j|)
    (hdetScaled : Matrix.det (Hscaled + DeltaHscaled) = theta) :
    ∃ DeltaH : Matrix ι ι ℝ,
      (∀ i j : ι, |DeltaH i j| ≤ gamma * |H i j|) ∧
      Matrix.det (H + DeltaH) = theta := by
  let DeltaH :=
    higham14_problem14_14_diagonalUnscalePerturbation d DeltaHscaled
  refine ⟨DeltaH, ?_, ?_⟩
  · apply higham14_problem14_14_unscaled_delta_bound_of_scaled d H DeltaHscaled gamma hd
    intro i j
    simpa [hHscaled] using hDeltaScaled i j
  · have hsim :
        higham14_problem14_14_diagonalSimilarity d (H + DeltaH) =
          Hscaled + DeltaHscaled := by
      ext i j
      simp [DeltaH, hHscaled, Matrix.add_apply,
        higham14_problem14_14_diagonalSimilarity_apply,
        higham14_problem14_14_diagonalUnscalePerturbation_apply]
      field_simp [hd i, hd j]
    have hdet :=
      higham14_problem14_14_det_diagonalSimilarity d (H + DeltaH) hd
    rw [← hdet, hsim, hdetScaled]

/-- Problem 14.14 diagonal-scaling wrapper for Hyman's method.  Applying the
    existing perturbed Hyman determinant package to a diagonally scaled
    Hessenberg matrix and then unscaling gives the same relative
    componentwise `DeltaH` certificate for the original matrix. -/
theorem higham14_problem14_14_exists_deltaH_det_original_of_diagonal_scaled_upper_add_zero_diag
    {n : ℕ}
    (H Hscaled : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (d : Fin n ⊕ Unit → ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gammaT gammaH : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hd : ∀ i : Fin n ⊕ Unit, d i ≠ 0)
    (hHscaled : Hscaled = higham14_problem14_14_diagonalSimilarity d H)
    (hDeltaHScaledCert :
      ∃ DeltaHscaled : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
        (∀ i j, |DeltaHscaled i j| ≤ gammaH * |Hscaled i j|) ∧
        higham14_hymanBlockMatrix (T + DeltaT) y h η =
          Matrix.submatrix (Hscaled + DeltaHscaled) σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaTDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaTBound : ∀ i j : Fin n, |DeltaT i j| ≤ gammaT * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
      Matrix.det (H + DeltaH) =
        (Equiv.Perm.sign σ : ℝ) *
          Matrix.det T * higham14_hymanSchur h y TpertInv η := by
  rcases
    higham14_problem14_14_exists_deltaH_det_original_of_upper_add_zero_diag
      Hscaled T DeltaT TpertInv y h η gammaT gammaH σ
      hDeltaHScaledCert hTupper hDeltaTDiag hDeltaTBound hTpertInv
    with ⟨DeltaHscaled, hDeltaHscaled, hdetScaled⟩
  exact
    higham14_problem14_14_unscale_deltaH_det_of_diagonal_scaled_det
      H Hscaled DeltaHscaled d gammaH
      ((Equiv.Perm.sign σ : ℝ) *
        Matrix.det T * higham14_hymanSchur h y TpertInv η)
      hd hHscaled hDeltaHscaled hdetScaled

/-- Absolute-value form of the diagonally scaled Problem 14.14 Hyman
    backward-error target. -/
theorem higham14_problem14_14_exists_deltaH_abs_det_original_of_diagonal_scaled_upper_add_zero_diag
    {n : ℕ}
    (H Hscaled : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (d : Fin n ⊕ Unit → ℝ)
    (T DeltaT TpertInv : Matrix (Fin n) (Fin n) ℝ)
    (y h : Fin n → ℝ) (η gammaT gammaH : ℝ)
    (σ : Equiv.Perm (Fin n ⊕ Unit))
    (hd : ∀ i : Fin n ⊕ Unit, d i ≠ 0)
    (hHscaled : Hscaled = higham14_problem14_14_diagonalSimilarity d H)
    (hDeltaHScaledCert :
      ∃ DeltaHscaled : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
        (∀ i j, |DeltaHscaled i j| ≤ gammaH * |Hscaled i j|) ∧
        higham14_hymanBlockMatrix (T + DeltaT) y h η =
          Matrix.submatrix (Hscaled + DeltaHscaled) σ (Equiv.refl (Fin n ⊕ Unit)))
    (hTupper : T.BlockTriangular id)
    (hDeltaTDiag : ∀ i : Fin n, DeltaT i i = 0)
    (hDeltaTBound : ∀ i j : Fin n, |DeltaT i j| ≤ gammaT * |T i j|)
    (hTpertInv : IsLeftInverse n (T + DeltaT) TpertInv) :
    ∃ DeltaH : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ,
      (∀ i j, |DeltaH i j| ≤ gammaH * |H i j|) ∧
      |Matrix.det (H + DeltaH)| =
        |Matrix.det T| * |higham14_hymanSchur h y TpertInv η| := by
  rcases
    higham14_problem14_14_exists_deltaH_det_original_of_diagonal_scaled_upper_add_zero_diag
      H Hscaled d T DeltaT TpertInv y h η gammaT gammaH σ
      hd hHscaled hDeltaHScaledCert hTupper hDeltaTDiag hDeltaTBound
      hTpertInv
    with ⟨DeltaH, hDeltaHBound, hdet⟩
  refine ⟨DeltaH, hDeltaHBound, ?_⟩
  have hsign_abs : |(Equiv.Perm.sign σ : ℝ)| = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign <;>
      simp [hsign]
  rw [hdet, abs_mul, abs_mul, hsign_abs, one_mul]

/-! ### Problem 14.8: complex inverse via a real block matrix -/

/-- Higham, 2nd ed., Chapter 14, Problem 14.8:
    real block representation of a complex matrix `A = B + i C`, using the
    product index `Fin 2 x Fin n` for the source `2n x 2n` matrix
    `[[B, -C], [C, B]]`. -/
noncomputable def higham14_problem14_8_realBlockMatrix {n : ℕ}
    (A : CMatrix n n) :
    (Fin 2 × Fin n) → (Fin 2 × Fin n) → ℝ :=
  fun p q =>
    if p.1 = (0 : Fin 2) then
      if q.1 = (0 : Fin 2) then (A p.2 q.2).re else -(A p.2 q.2).im
    else
      if q.1 = (0 : Fin 2) then (A p.2 q.2).im else (A p.2 q.2).re

/-- Pack a real `2n` vector, indexed as real and imaginary blocks, into a
    complex vector. -/
noncomputable def higham14_problem14_8_realToComplexVec {n : ℕ}
    (x : Fin 2 × Fin n → ℝ) : CVec n :=
  fun i => ((x ((0 : Fin 2), i) : ℝ) : ℂ) +
    Complex.I * ((x ((1 : Fin 2), i) : ℝ) : ℂ)

/-- Unpack a complex vector into its real and imaginary blocks. -/
noncomputable def higham14_problem14_8_complexToRealVec {n : ℕ}
    (z : CVec n) : Fin 2 × Fin n → ℝ :=
  fun p => if p.1 = (0 : Fin 2) then (z p.2).re else (z p.2).im

/-- The real part of the Hermitian quadratic form `z^* A z`, written with the
    repository's concrete complex matrix-vector action. -/
noncomputable def higham14_problem14_8_complexQuadraticForm {n : ℕ}
    (A : CMatrix n n) (z : CVec n) : ℝ :=
  (∑ i : Fin n, star (z i) * complexMatrixVecMul A z i).re

/-- Product-indexed symmetric positive definite predicate for the real block
    matrix in Problem 14.8.  This is the `Fin 2 x Fin n` version of the
    source's `2n x 2n` SPD statement. -/
def higham14_problem14_8_realBlockSymPosDef {n : ℕ}
    (M : (Fin 2 × Fin n) → (Fin 2 × Fin n) → ℝ) : Prop :=
  IsSymmetricFiniteMatrix M ∧
    ∀ x : Fin 2 × Fin n → ℝ, (∃ p : Fin 2 × Fin n, x p ≠ 0) →
      0 < finiteQuadraticForm M x

/-- Source-facing Hermitian positive definite predicate for the complex input
    matrix in Problem 14.8.  Positivity is stated as positivity of the real
    part of `z^* A z`. -/
def higham14_problem14_8_complexHermitianPosDef {n : ℕ}
    (A : CMatrix n n) : Prop :=
  (∀ i j : Fin n, A i j = star (A j i)) ∧
    ∀ z : CVec n, (∃ i : Fin n, z i ≠ 0) →
      0 < higham14_problem14_8_complexQuadraticForm A z

lemma higham14_problem14_8_complexToRealVec_realToComplexVec {n : ℕ}
    (x : Fin 2 × Fin n → ℝ) :
    higham14_problem14_8_complexToRealVec
      (higham14_problem14_8_realToComplexVec x) = x := by
  funext p
  rcases p with ⟨b, i⟩
  cases b using Fin.cases with
  | zero =>
      simp [higham14_problem14_8_complexToRealVec,
        higham14_problem14_8_realToComplexVec]
  | succ b =>
      cases b using Fin.cases with
      | zero =>
          simp [higham14_problem14_8_complexToRealVec,
            higham14_problem14_8_realToComplexVec]
      | succ b => exact Fin.elim0 b

lemma higham14_problem14_8_realToComplexVec_complexToRealVec {n : ℕ}
    (z : CVec n) :
    higham14_problem14_8_realToComplexVec
      (higham14_problem14_8_complexToRealVec z) = z := by
  funext i
  apply Complex.ext <;>
    simp [higham14_problem14_8_complexToRealVec,
      higham14_problem14_8_realToComplexVec]

/-- Matrix-vector action of the real block matrix is exactly the real/imaginary
    unpacking of the complex matrix-vector action. -/
theorem higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec
    {n : ℕ} (A : CMatrix n n) (x : Fin 2 × Fin n → ℝ) :
    finiteMatVec (higham14_problem14_8_realBlockMatrix A) x =
      higham14_problem14_8_complexToRealVec
        (complexMatrixVecMul A (higham14_problem14_8_realToComplexVec x)) := by
  funext p
  rcases p with ⟨b, i⟩
  cases b using Fin.cases with
  | zero =>
      simp [finiteMatVec, higham14_problem14_8_realBlockMatrix,
        higham14_problem14_8_complexToRealVec,
        higham14_problem14_8_realToComplexVec, complexMatrixVecMul,
        Fintype.sum_prod_type, Finset.sum_add_distrib, mul_add, sub_eq_add_neg]
  | succ b =>
      cases b using Fin.cases with
      | zero =>
          simp [finiteMatVec, higham14_problem14_8_realBlockMatrix,
            higham14_problem14_8_complexToRealVec,
            higham14_problem14_8_realToComplexVec, complexMatrixVecMul,
            Fintype.sum_prod_type, Finset.sum_add_distrib, mul_add]
      | succ b => exact Fin.elim0 b

/-- Problem 14.8, inverse transfer, right-inverse direction:
    if `Ainv` is a right inverse of the complex matrix `A`, then the real block
    matrix of `Ainv` is a right inverse of the real block matrix of `A`. -/
theorem higham14_problem14_8_realBlockMatrix_rightInverse_of_complex
    {n : ℕ} {A Ainv : CMatrix n n}
    (h : IsComplexMatrixRightInverse A Ainv) :
    ∀ x : Fin 2 × Fin n → ℝ,
      finiteMatVec (higham14_problem14_8_realBlockMatrix A)
        (finiteMatVec (higham14_problem14_8_realBlockMatrix Ainv) x) = x := by
  intro x
  rw [higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec,
    higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec,
    higham14_problem14_8_realToComplexVec_complexToRealVec, h,
    higham14_problem14_8_complexToRealVec_realToComplexVec]

/-- Problem 14.8, inverse transfer, left-inverse direction:
    if `Ainv` is a left inverse of the complex matrix `A`, then the real block
    matrix of `Ainv` is a left inverse of the real block matrix of `A`. -/
theorem higham14_problem14_8_realBlockMatrix_leftInverse_of_complex
    {n : ℕ} {A Ainv : CMatrix n n}
    (h : IsComplexMatrixLeftInverse A Ainv) :
    ∀ x : Fin 2 × Fin n → ℝ,
      finiteMatVec (higham14_problem14_8_realBlockMatrix Ainv)
        (finiteMatVec (higham14_problem14_8_realBlockMatrix A) x) = x := by
  intro x
  rw [higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec,
    higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec,
    higham14_problem14_8_realToComplexVec_complexToRealVec, h,
    higham14_problem14_8_complexToRealVec_realToComplexVec]

/-- Problem 14.8, two-sided inverse transfer for the real block matrix
    `[[Re A, -Im A], [Im A, Re A]]`. -/
theorem higham14_problem14_8_realBlockMatrix_inverse_of_complex
    {n : ℕ} {A Ainv : CMatrix n n}
    (h : IsComplexMatrixInverse A Ainv) :
    (∀ x : Fin 2 × Fin n → ℝ,
      finiteMatVec (higham14_problem14_8_realBlockMatrix Ainv)
        (finiteMatVec (higham14_problem14_8_realBlockMatrix A) x) = x) ∧
    (∀ x : Fin 2 × Fin n → ℝ,
      finiteMatVec (higham14_problem14_8_realBlockMatrix A)
        (finiteMatVec (higham14_problem14_8_realBlockMatrix Ainv) x) = x) := by
  exact ⟨higham14_problem14_8_realBlockMatrix_leftInverse_of_complex h.1,
    higham14_problem14_8_realBlockMatrix_rightInverse_of_complex h.2⟩

/-- The real block quadratic form is the real part of `z^* A z`, where
    `z` is the complex vector packed from the real and imaginary blocks. -/
theorem higham14_problem14_8_realBlockMatrix_quadratic_eq_complexQuadratic
    {n : ℕ} (A : CMatrix n n) (x : Fin 2 × Fin n → ℝ) :
    finiteQuadraticForm (higham14_problem14_8_realBlockMatrix A) x =
      higham14_problem14_8_complexQuadraticForm A
        (higham14_problem14_8_realToComplexVec x) := by
  unfold finiteQuadraticForm higham14_problem14_8_complexQuadraticForm
  rw [higham14_problem14_8_realBlockMatrix_finiteMatVec_eq_complexToRealVec]
  simp [higham14_problem14_8_complexToRealVec,
    higham14_problem14_8_realToComplexVec, complexMatrixVecMul,
    Fintype.sum_prod_type, Finset.sum_add_distrib, mul_add, sub_eq_add_neg]
  ring

lemma higham14_problem14_8_realBlockMatrix_symmetric_of_hermitian
    {n : ℕ} {A : CMatrix n n}
    (hHerm : ∀ i j : Fin n, A i j = star (A j i)) :
    IsSymmetricFiniteMatrix (higham14_problem14_8_realBlockMatrix A) := by
  intro p q
  rcases p with ⟨bp, i⟩
  rcases q with ⟨bq, j⟩
  cases bp using Fin.cases with
  | zero =>
      cases bq using Fin.cases with
      | zero =>
          change (A i j).re = (A j i).re
          simpa using congrArg Complex.re (hHerm i j)
      | succ bq =>
          cases bq using Fin.cases with
          | zero =>
              change -(A i j).im = (A j i).im
              have him : (A i j).im = -(A j i).im := by
                simpa using congrArg Complex.im (hHerm i j)
              linarith
          | succ bq => exact Fin.elim0 bq
  | succ bp =>
      cases bp using Fin.cases with
      | zero =>
          cases bq using Fin.cases with
          | zero =>
              change (A i j).im = -(A j i).im
              simpa using congrArg Complex.im (hHerm i j)
          | succ bq =>
              cases bq using Fin.cases with
              | zero =>
                  change (A i j).re = (A j i).re
                  simpa using congrArg Complex.re (hHerm i j)
              | succ bq => exact Fin.elim0 bq
      | succ bp => exact Fin.elim0 bp

lemma higham14_problem14_8_realToComplexVec_ne_zero_of_real_ne_zero
    {n : ℕ} {x : Fin 2 × Fin n → ℝ} {p : Fin 2 × Fin n}
    (hp : x p ≠ 0) :
    ∃ i : Fin n, higham14_problem14_8_realToComplexVec x i ≠ 0 := by
  rcases p with ⟨b, i⟩
  refine ⟨i, ?_⟩
  intro hz
  apply hp
  cases b using Fin.cases with
  | zero =>
      have hre := congrArg Complex.re hz
      simpa [higham14_problem14_8_realToComplexVec] using hre
  | succ b =>
      cases b using Fin.cases with
      | zero =>
          have him := congrArg Complex.im hz
          simpa [higham14_problem14_8_realToComplexVec] using him
      | succ b => exact Fin.elim0 b

/-- Problem 14.8, Hermitian positive definite transfer:
    if the complex matrix is Hermitian positive definite, then its real block
    representation `[[Re A, -Im A], [Im A, Re A]]` is SPD, in product-indexed
    `2n` form. -/
theorem higham14_problem14_8_realBlockMatrix_symPosDef_of_complexHermitianPosDef
    {n : ℕ} {A : CMatrix n n}
    (hA : higham14_problem14_8_complexHermitianPosDef A) :
    higham14_problem14_8_realBlockSymPosDef
      (higham14_problem14_8_realBlockMatrix A) := by
  constructor
  · exact higham14_problem14_8_realBlockMatrix_symmetric_of_hermitian hA.1
  · intro x hx
    rw [higham14_problem14_8_realBlockMatrix_quadratic_eq_complexQuadratic]
    rcases hx with ⟨p, hp⟩
    exact hA.2 (higham14_problem14_8_realToComplexVec x)
      (higham14_problem14_8_realToComplexVec_ne_zero_of_real_ne_zero hp)

/-- Entry perturbation used in Higham Chapter 14, Problem 14.10:
    replace `aᵢⱼ` by `aᵢⱼ + t`, leaving every other entry unchanged. -/
noncomputable def matrixEntryPerturb (n : ℕ)
    (A : Fin n → Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.updateRow (A : Matrix (Fin n) (Fin n) ℝ) i
    ((A : Matrix (Fin n) (Fin n) ℝ) i +
      t • (Pi.single j (1 : ℝ) : Fin n → ℝ))

/-- Higham, 2nd ed., Chapter 14, Problem 14.10, cofactor form:
    changing entry `aᵢⱼ` by `t` changes the determinant by
    `t * adj(A)ⱼᵢ`. -/
theorem higham14_problem14_10_det_entry_perturb_eq
    (n : ℕ) (A : Fin n → Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    Matrix.det (matrixEntryPerturb n A i j t) =
      Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) +
        t * Matrix.adjugate (A : Matrix (Fin n) (Fin n) ℝ) j i := by
  unfold matrixEntryPerturb
  rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
    Matrix.updateRow_eq_self, Matrix.adjugate_apply]

/-- Higham, 2nd ed., Chapter 14, Problem 14.10:
    if the `(j,i)` cofactor/adjugate entry vanishes, then `det(A)` is
    independent of the entry `aᵢⱼ`. -/
theorem higham14_problem14_10_det_entry_independent_of_adjugate_eq_zero
    (n : ℕ) (A : Fin n → Fin n → ℝ) (i j : Fin n)
    (hAdj : Matrix.adjugate (A : Matrix (Fin n) (Fin n) ℝ) j i = 0) :
    ∀ t : ℝ,
      Matrix.det (matrixEntryPerturb n A i j t) =
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) := by
  intro t
  rw [higham14_problem14_10_det_entry_perturb_eq n A i j t, hAdj, mul_zero, add_zero]

/-- Higham, 2nd ed., Chapter 14, Problem 14.10:
    the determinant is independent of `aᵢⱼ` for all additive perturbations iff
    the `(j,i)` adjugate entry is zero. -/
theorem higham14_problem14_10_det_entry_independent_iff_adjugate_eq_zero
    (n : ℕ) (A : Fin n → Fin n → ℝ) (i j : Fin n) :
    (∀ t : ℝ,
      Matrix.det (matrixEntryPerturb n A i j t) =
        Matrix.det (A : Matrix (Fin n) (Fin n) ℝ)) ↔
      Matrix.adjugate (A : Matrix (Fin n) (Fin n) ℝ) j i = 0 := by
  constructor
  · intro h
    have h1 := h 1
    rw [higham14_problem14_10_det_entry_perturb_eq n A i j 1] at h1
    linarith
  · exact higham14_problem14_10_det_entry_independent_of_adjugate_eq_zero n A i j

/-- Higham, 2nd ed., Chapter 14, Problem 14.7:
    if one row of a nonsingular matrix consists entirely of ones, then the
    entries of its inverse sum to one. -/
theorem higham14_problem14_7_inverse_entries_sum_eq_one_of_row_ones (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (hRight : IsRightInverse n A A_inv)
    (i : Fin n)
    (hrow : ∀ k : Fin n, A i k = 1) :
    (∑ j : Fin n, ∑ k : Fin n, A_inv k j) = 1 := by
  have hColSum : ∀ j : Fin n,
      (∑ k : Fin n, A_inv k j) = if i = j then (1 : ℝ) else 0 := by
    intro j
    have h := hRight i j
    simpa [hrow] using h
  calc
    (∑ j : Fin n, ∑ k : Fin n, A_inv k j)
        = ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hColSum j
    _ = 1 := by
          simp [Finset.mem_univ]

/-- Higham, 2nd ed., Chapter 14, Problem 14.7:
    if one column of a nonsingular matrix consists entirely of ones, then the
    entries of its inverse sum to one. -/
theorem higham14_problem14_7_inverse_entries_sum_eq_one_of_col_ones (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ)
    (hLeft : IsLeftInverse n A A_inv)
    (j : Fin n)
    (hcol : ∀ k : Fin n, A k j = 1) :
    (∑ i : Fin n, ∑ k : Fin n, A_inv i k) = 1 := by
  have hRowSum : ∀ i : Fin n,
      (∑ k : Fin n, A_inv i k) = if i = j then (1 : ℝ) else 0 := by
    intro i
    have h := hLeft i j
    simpa [hcol] using h
  calc
    (∑ i : Fin n, ∑ k : Fin n, A_inv i k)
        = ∑ i : Fin n, (if i = j then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hRowSum i
    _ = 1 := by
          simp [Finset.mem_univ]

end NumStability
