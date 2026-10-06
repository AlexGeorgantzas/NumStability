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
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms MatrixInversion Residuals MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

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

end NumStability
