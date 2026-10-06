import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra

/-!
# Algorithms.MatrixEquations.Sylvester.Equation.Basic

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

/-- **Sylvester operator**: T(X) = AX - XB.
    The Sylvester equation AX - XB = C is T(X) = C. -/
noncomputable def sylvesterOp (n : ℕ) (A B : Fin n → Fin n → ℝ)
    (X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => matMul n A X i j - matMul n X B i j

/-- **Sylvester residual**: R = C - (AŶ - ŶB) for approximate solution Ŷ.
    A small residual is necessary for a small backward error (§15.2). -/
noncomputable def sylvesterResidual (n : ℕ) (A B C Y_hat : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => C i j - sylvesterOp n A B Y_hat i j

/-- Residual expanded: R_ij = C_ij - (AŶ)_ij + (ŶB)_ij. -/
theorem sylvesterResidual_eq (n : ℕ) (A B C Y_hat : Fin n → Fin n → ℝ) :
    sylvesterResidual n A B C Y_hat =
    fun i j => C i j - matMul n A Y_hat i j + matMul n Y_hat B i j := by
  ext i j; unfold sylvesterResidual sylvesterOp; ring

-- ============================================================
-- Separation function (§15.3, eq 15.26)
-- ============================================================

/-- **sep(A,B)** as a lower bound hypothesis: sep(A,B) ≥ σ > 0.
    sep(A,B) = min_{X≠0} ‖AX-XB‖_F/‖X‖_F is the separation of A and B.
    We work with a lower bound σ rather than computing the exact value,
    following the library convention for operator norms. -/
def SepLowerBound (n : ℕ) (A B : Fin n → Fin n → ℝ) (σ : ℝ) : Prop :=
  0 < σ ∧ ∀ X : Fin n → Fin n → ℝ, frobNormSq X ≠ 0 →
    σ ^ 2 * frobNormSq X ≤ frobNormSq (sylvesterOp n A B X)

/-- If sep(A,B) ≥ σ > 0, then AX - XB = C has a unique solution for any C. -/
theorem sep_implies_unique_solution (n : ℕ) (A B : Fin n → Fin n → ℝ)
    (σ : ℝ) (hsep : SepLowerBound n A B σ)
    (C : Fin n → Fin n → ℝ)
    (X₁ X₂ : Fin n → Fin n → ℝ)
    (hX₁ : ∀ i j, sylvesterOp n A B X₁ i j = C i j)
    (hX₂ : ∀ i j, sylvesterOp n A B X₂ i j = C i j) :
    ∀ i j, X₁ i j = X₂ i j := by
  -- If X₁ ≠ X₂, then D = X₁ - X₂ ≠ 0 and sylvesterOp(D) = 0,
  -- contradicting sep > 0.
  by_contra h
  push_neg at h
  obtain ⟨i₀, j₀, hne⟩ := h
  -- D = X₁ - X₂
  let D : Fin n → Fin n → ℝ := fun i j => X₁ i j - X₂ i j
  -- D ≠ 0
  have hD_ne : frobNormSq D ≠ 0 := by
    intro h_eq
    have hzero := (frobNorm_eq_zero_iff D).mp (by
      rw [frobNorm_eq_sqrt_frobNormSq, Real.sqrt_eq_zero (frobNormSq_nonneg D)]
      exact h_eq)
    exact hne (sub_eq_zero.mp (hzero i₀ j₀))
  -- sylvesterOp(D) = 0
  have hD_zero : ∀ i j, sylvesterOp n A B D i j = 0 := by
    intro i j
    have h1 := hX₁ i j; have h2 := hX₂ i j
    unfold sylvesterOp at h1 h2 ⊢; unfold matMul at h1 h2 ⊢
    simp only [D]
    have : ∀ k : Fin n, A i k * (X₁ k j - X₂ k j) =
        A i k * X₁ k j - A i k * X₂ k j := fun k => mul_sub _ _ _
    have : ∀ k : Fin n, (X₁ i k - X₂ i k) * B k j =
        X₁ i k * B k j - X₂ i k * B k j := fun k => sub_mul _ _ _
    simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]; linarith
  -- frobNormSq(sylvesterOp(D)) = 0
  have hFrob_zero : frobNormSq (sylvesterOp n A B D) = 0 := by
    unfold frobNormSq
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    rw [hD_zero i j]; ring
  -- sep > 0 gives σ² ‖D‖² ≤ ‖T(D)‖² = 0, contradicting ‖D‖² > 0
  have hpos : 0 < frobNormSq D :=
    lt_of_le_of_ne (frobNormSq_nonneg D) (Ne.symm hD_ne)
  have hle := hsep.2 D hD_ne
  rw [hFrob_zero] at hle
  -- hle : σ ^ 2 * frobNormSq D ≤ 0, but σ² > 0 and ‖D‖² > 0
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hsep.1
  nlinarith

-- ============================================================
-- Symmetric matrices and Lyapunov equation (§15.2.1)
-- ============================================================








































-- ============================================================
-- Normwise backward error definition (§15.2, eq 15.10)
-- ============================================================








































-- ============================================================
-- Residual bound (§15.2, eq 15.12)
-- ============================================================































































































end NumStability
