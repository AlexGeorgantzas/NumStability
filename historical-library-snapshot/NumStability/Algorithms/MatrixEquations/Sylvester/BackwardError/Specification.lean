import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Lyapunov
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.MatrixEquations.Sylvester.BackwardError.Specification

W05 semantic leaf. Declaration commands are copied byte-identically from the frozen C0004 owners.
-/

-- Algorithms/Sylvester/SylvesterSpec.lean
--
-- Definitions and basic properties for the Sylvester equation AX - XB = C
-- (Higham §15). Core definitions: sylvesterResidual, SepLowerBound,
-- IsSymmetric, lyapunovOp, and the residual bound (eq 15.12).











namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- The Sylvester equation: AX - XB = C (§15, eq 15.1)
-- ============================================================



















-- ============================================================
-- Separation function (§15.3, eq 15.26)
-- ============================================================

























































-- ============================================================
-- Symmetric matrices and Lyapunov equation (§15.2.1)
-- ============================================================








































-- ============================================================
-- Normwise backward error definition (§15.2, eq 15.10)
-- ============================================================

/-- **Normwise backward error** (eq 15.10) as a lower bound predicate.
    η(Y) is the smallest ε such that (A+ΔA)Y - Y(B+ΔB) = C+ΔC
    with ‖ΔA‖_F ≤ εα, ‖ΔB‖_F ≤ εβ, ‖ΔC‖_F ≤ εγ.

    We represent this as: η is a backward error for Y if there exist
    perturbations ΔA, ΔB, ΔC satisfying the backward error equation
    and bounds. -/
def IsBackwardError (n : ℕ) (A B C Y : Fin n → Fin n → ℝ)
    (α β γ η : ℝ) : Prop :=
  ∃ (ΔA ΔB ΔC : Fin n → Fin n → ℝ),
    (∀ i j, sylvesterOp n (fun i' j' => A i' j' + ΔA i' j')
      (fun i' j' => B i' j' + ΔB i' j') Y i j = C i j + ΔC i j) ∧
    frobNormSq ΔA ≤ (η * α) ^ 2 ∧
    frobNormSq ΔB ≤ (η * β) ^ 2 ∧
    frobNormSq ΔC ≤ (η * γ) ^ 2





/-- Higham, 2nd ed., Chapter 16.2.1:
    structured Lyapunov normwise backward-error certificate.  The perturbation
    of `A` is tied on both sides as `DeltaA` and `DeltaA^T`, and the right-hand
    perturbation `DeltaC` is symmetric, matching the source definition of the
    Lyapunov eta model. -/
def IsLyapunovBackwardError (n : Nat) (A C Y : Fin n -> Fin n -> Real)
    (alpha gamma eta : Real) : Prop :=
  ∃ (DeltaA DeltaC : Fin n -> Fin n -> Real),
    IsSymmetricFiniteMatrix DeltaC ∧
    (∀ i j, lyapunovOp n (fun i' j' => A i' j' + DeltaA i' j') Y i j =
      C i j + DeltaC i j) ∧
    frobNormSq DeltaA ≤ (eta * alpha) ^ 2 ∧
    frobNormSq DeltaC ≤ (eta * gamma) ^ 2






-- ============================================================
-- Residual bound (§15.2, eq 15.12)
-- ============================================================

/-- **Residual decomposition** (Higham §15.2, eq 15.11).

    From (A+ΔA)Y - Y(B+ΔB) = C + ΔC, the residual R = C - (AY - YB)
    decomposes as R = ΔAY - YΔB - ΔC. -/
theorem residual_decomposition (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ)
    (ΔA ΔB ΔC : Fin n → Fin n → ℝ)
    (hEq : ∀ i j, sylvesterOp n (fun i' j' => A i' j' + ΔA i' j')
      (fun i' j' => B i' j' + ΔB i' j') Y i j = C i j + ΔC i j) :
    ∀ i j, sylvesterResidual n A B C Y i j =
      matMul n ΔA Y i j - matMul n Y ΔB i j - ΔC i j := by
  intro i j
  have h := hEq i j
  unfold sylvesterOp at h; unfold sylvesterResidual sylvesterOp
  unfold matMul at h ⊢
  simp only [add_mul, mul_add, Finset.sum_add_distrib] at h
  linarith





/-- **Residual bound** (Higham §15.2, eq 15.12).

    If ‖ΔA‖_F ≤ ηα, ‖ΔB‖_F ≤ ηβ, ‖ΔC‖_F ≤ ηγ, and
    R = ΔAY - YΔB - ΔC, then:
      ‖R‖_F ≤ ((α+β)‖Y‖_F + γ) · η.

    Proved via triangle inequality and submultiplicativity. -/
theorem residual_bound (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ)
    (ΔA ΔB ΔC : Fin n → Fin n → ℝ)
    (α β γ η : ℝ) (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (_hγ : 0 ≤ γ) (_hη : 0 ≤ η)
    (hEq : ∀ i j, sylvesterOp n (fun i' j' => A i' j' + ΔA i' j')
      (fun i' j' => B i' j' + ΔB i' j') Y i j = C i j + ΔC i j)
    (hΔA : frobNorm ΔA ≤ η * α)
    (hΔB : frobNorm ΔB ≤ η * β)
    (hΔC : frobNorm ΔC ≤ η * γ) :
    frobNorm (sylvesterResidual n A B C Y) ≤
    ((α + β) * frobNorm Y + γ) * η := by
  -- R_ij = (ΔA·Y)_ij - (Y·ΔB)_ij - ΔC_ij
  have hR := residual_decomposition n A B C Y ΔA ΔB ΔC hEq
  -- ‖R‖_F = ‖ΔAY - YΔB - ΔC‖_F
  -- We bound this using the triangle inequality step by step.
  -- First, ‖R‖_F ≤ ‖ΔAY - YΔB‖_F + ‖ΔC‖_F  (since R = (ΔAY - YΔB) + (-ΔC))
  -- Then, ‖ΔAY - YΔB‖_F ≤ ‖ΔAY‖_F + ‖YΔB‖_F
  -- And ‖ΔAY‖_F ≤ ‖ΔA‖_F ‖Y‖_F, ‖YΔB‖_F ≤ ‖Y‖_F ‖ΔB‖_F
  -- Step 1: ‖ΔAY‖_F ≤ ‖ΔA‖_F ‖Y‖_F ≤ ηα ‖Y‖_F
  have h1 : frobNorm (matMul n ΔA Y) ≤
      η * α * frobNorm Y :=
    le_trans (frobNorm_matMul_le ΔA Y)
      (mul_le_mul_of_nonneg_right hΔA (frobNorm_nonneg Y))
  -- Step 2: ‖YΔB‖_F ≤ ‖Y‖_F ‖ΔB‖_F ≤ ‖Y‖_F ηβ
  have h2 : frobNorm (matMul n Y ΔB) ≤
      frobNorm Y * (η * β) :=
    le_trans (frobNorm_matMul_le Y ΔB)
      (mul_le_mul_of_nonneg_left hΔB (frobNorm_nonneg Y))
  -- Step 3: ‖R‖_F ≤ ‖ΔAY‖_F + ‖YΔB‖_F + ‖ΔC‖_F via triangle inequality
  -- First rewrite R pointwise using residual_decomposition
  have hReq :
      frobNorm (sylvesterResidual n A B C Y) =
      frobNorm (fun i j => matMul n ΔA Y i j - matMul n Y ΔB i j - ΔC i j) := by
    congr 1; ext i j; exact hR i j
  rw [hReq]
  -- ‖ΔAY - YΔB - ΔC‖_F = ‖(ΔAY - YΔB) - ΔC‖_F ≤ ‖ΔAY - YΔB‖_F + ‖ΔC‖_F
  have h3 :
      frobNorm (fun i j => matMul n ΔA Y i j - matMul n Y ΔB i j - ΔC i j) ≤
      frobNorm (fun i j => matMul n ΔA Y i j - matMul n Y ΔB i j) +
        frobNorm ΔC := by
    have := frobNorm_sub_le (fun i j => matMul n ΔA Y i j - matMul n Y ΔB i j) ΔC
    convert this using 2
  -- ‖ΔAY - YΔB‖_F ≤ ‖ΔAY‖_F + ‖YΔB‖_F
  have h4 :
      frobNorm (fun i j => matMul n ΔA Y i j - matMul n Y ΔB i j) ≤
      frobNorm (matMul n ΔA Y) +
        frobNorm (matMul n Y ΔB) :=
    frobNorm_sub_le (matMul n ΔA Y) (matMul n Y ΔB)
  -- Combine: ‖R‖_F ≤ ηα‖Y‖_F + ‖Y‖_F ηβ + ηγ = ((α+β)‖Y‖_F + γ)η
  have h5 :
      frobNorm (matMul n ΔA Y) +
          frobNorm (matMul n Y ΔB) +
          frobNorm ΔC ≤
      (η * α * frobNorm Y +
        frobNorm Y * (η * β)) + η * γ :=
    add_le_add (add_le_add h1 h2) hΔC
  have h6 : (η * α * frobNorm Y +
        frobNorm Y * (η * β)) + η * γ =
      ((α + β) * frobNorm Y + γ) * η := by ring
  linarith





end NumStability
