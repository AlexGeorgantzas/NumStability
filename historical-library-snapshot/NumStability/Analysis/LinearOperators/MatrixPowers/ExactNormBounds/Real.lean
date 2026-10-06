import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding

/-!
# Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Real

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/MatrixPowers.lean
--
-- Higham Chapter 18: Error analysis of matrix powers.
--
-- Covers §18.2 (finite precision bounds for computed A^m via repeated
-- matrix-vector products) and the similarity-based convergence engine
-- underlying Theorem 18.1 (Higham–Knight).













namespace NumStability

open scoped BigOperators

-- ============================================================
-- §18.2  Backward error model for computed matrix powers
-- ============================================================


























-- ============================================================
-- §18.2  Concrete floating-point realization of (18.10)–(18.11)
-- ============================================================






































-- ============================================================
-- One-step componentwise bound
-- ============================================================
























-- ============================================================
-- §18.2  Componentwise forward bound (consequence of 18.10–18.11)
-- ============================================================















































-- ============================================================
-- §18.2  Normwise forward bound
-- ============================================================






































-- ============================================================
-- §18.2  Sufficient convergence condition (normwise, eq 18.12)
-- ============================================================





















-- ============================================================
-- §18.2  Matrix-level componentwise bound (column by column)
-- ============================================================


























-- ============================================================
-- §18.2  Nonneg matrix specialization
-- ============================================================















-- ============================================================
-- §18.2  Similarity-based convergence engine (eq 18.14)
-- ============================================================











































































-- ============================================================
-- §18.2  Corollary: normwise bound via similarity
-- ============================================================


























































-- ============================================================
-- Theorem 18.1: JordanFormSpec and convergence condition
-- ============================================================






















































































-- ============================================================
-- §18.2  Limit form of the convergence conclusion
-- ============================================================
























-- ============================================================
-- §18.2  End-to-end conditional forms with the limit conclusion
-- ============================================================






























































-- ============================================================
-- §18.2  Discharging `similarity_absorbs`: real-diagonalizable case (t = 1)
-- ============================================================















/-- Componentwise domination `|ΔA| ≤ η|A|` transfers to the matrix ∞-norm:
    `‖ΔA‖∞ ≤ η‖A‖∞`. -/
theorem infNorm_le_mul_of_abs_le_mul_abs {n : ℕ}
    (ΔA A : Fin n → Fin n → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hΔ : ∀ i j, |ΔA i j| ≤ η * |A i j|) :
    infNorm ΔA ≤ η * infNorm A := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |ΔA i j|
        ≤ ∑ j : Fin n, η * |A i j| :=
          Finset.sum_le_sum (fun j _ => hΔ i j)
      _ = η * ∑ j : Fin n, |A i j| := (Finset.mul_sum ..).symm
      _ ≤ η * infNorm A :=
          mul_le_mul_of_nonneg_left (row_sum_le_infNorm A i) hη
  · exact mul_nonneg hη (infNorm_nonneg A)




































































































































-- ============================================================
-- §18.1  Exact arithmetic: eq (18.4), real-diagonalizable case
-- ============================================================












































































































































































-- ============================================================
-- §18.2  Eq (18.12): weighted (Collatz–Wielandt) certificate form
-- ============================================================

/-- Weighted power bound: if `w > 0` satisfies `|A|·w ≤ θ·w` componentwise
    (a Collatz–Wielandt certificate, so `ρ(|A|) ≤ θ`), then
    `(|A|ᵐ·u)ᵢ ≤ M·θᵐ·wᵢ` for any `|u| ≤ M·w`. -/
theorem matPow_abs_weighted_bound (n : ℕ) (A : Fin n → Fin n → ℝ)
    (w : Fin n → ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hAw : ∀ i, ∑ j : Fin n, |A i j| * w j ≤ θ * w i)
    (u : Fin n → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hu : ∀ j, u j ≤ M * w j) (hu0 : ∀ j, 0 ≤ u j) (m : ℕ) :
    ∀ i, matMulVec n (matPow n (absMatrix n A) m) u i ≤ M * θ ^ m * w i := by
  induction m with
  | zero =>
    intro i
    have hid : matMulVec n (matPow n (absMatrix n A) 0) u i = u i := by
      show matMulVec n (idMatrix n) u i = u i
      unfold matMulVec idMatrix
      simp [Finset.sum_ite_eq]
    rw [hid, pow_zero, mul_one]
    exact hu i
  | succ m ih =>
    intro i
    have hsplit : matMulVec n (matPow n (absMatrix n A) (m + 1)) u i =
        ∑ j : Fin n, |A i j| *
          matMulVec n (matPow n (absMatrix n A) m) u j := by
      rw [matPow_succ n (absMatrix n A) m]
      rw [matMulVec_matMul n (absMatrix n A) (matPow n (absMatrix n A) m) u i]
      unfold matMulVec absMatrix
      rfl
    have hnn : ∀ j, 0 ≤ matMulVec n (matPow n (absMatrix n A) m) u j := by
      intro j
      unfold matMulVec
      apply Finset.sum_nonneg
      intro l _
      exact mul_nonneg (matPow_nonneg n (absMatrix n A)
        (fun a b => abs_nonneg (A a b)) m j l) (hu0 l)
    rw [hsplit]
    calc ∑ j : Fin n, |A i j| *
          matMulVec n (matPow n (absMatrix n A) m) u j
        ≤ ∑ j : Fin n, |A i j| * (M * θ ^ m * w j) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (ih j) (abs_nonneg _)
      _ = M * θ ^ m * ∑ j : Fin n, |A i j| * w j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ M * θ ^ m * (θ * w i) :=
          mul_le_mul_of_nonneg_left (hAw i)
            (mul_nonneg hM0 (pow_nonneg hθ0 m))
      _ = M * θ ^ (m + 1) * w i := by rw [pow_succ]; ring




















































































end NumStability
