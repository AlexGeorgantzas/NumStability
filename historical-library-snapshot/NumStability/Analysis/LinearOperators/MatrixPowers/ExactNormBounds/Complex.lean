import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Real
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.VectorNorms.Basic

/-!
# Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Complex

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/MatrixPowersComplex.lean
--
-- Higham Chapter 18: Error analysis of matrix powers — the GENERAL
-- (complex-spectrum, possibly defective) case of Theorem 18.1
-- (Higham–Knight) for a REAL input matrix `A` with COMPLEX Jordan-form
-- similarity data (Higham, Accuracy and Stability of Numerical Algorithms,
-- 2nd ed., §18.2, Theorem 18.1, pp. 347–348).
--
-- The computed iteration `v_{k+1} = fl(A v_k)` is real (a floating-point
-- object), matching the book's computational setting; the Jordan data
-- `X⁻¹ A X = J` lives over ℂ, which is the full generality of the printed
-- statement for real `A`.  The δ-scaling construction of the book's proof
-- is transported verbatim from the real-spectrum case
-- (`MatrixPowersJordan.lean`): the moduli arguments are identical because
-- `‖·‖` on ℂ is multiplicative and satisfies the triangle inequality.
--
-- Complex matrix infrastructure is REUSED from the canonical semantic API
-- (source traceability):
--   `CVec`                              — Analysis/VectorNorms/Basic.lean
--   `CMatrix`                           — Analysis/MatrixNorms/Basic.lean
--   `complexVecInfNorm` (+ nonneg / coord_le / le_of_coord_le)
--                                      — Analysis/VectorNorms/Basic.lean
--   `complexMatrixInfNorm` (+ nonneg / row_sum_le / le_of_row_sum_le)
--                                      — Analysis/MatrixNorms/Basic.lean («cInfNorm»:
--                                        max row sum of entry norms)
--   `complexMatrixMul`, `complexMatrixMul_assoc`
--                                      — Analysis/MatrixNorms/Basic.lean
--   `complexMatrixVecMul`, `complexMatrixVecMul_mul`
--                                      — Analysis/MatrixNorms/Basic.lean
--   `IsComplexMatrixRightInverse`      — Analysis/MatrixNorms/Basic.lean
-- Scalar margin lemmas are REUSED from `MatrixPowersJordan.lean`
-- (`jordanBeta`, `jordanBeta_pos`, `jordanBeta_lt_one`, `jordanBeta_add_eq`,
-- `higham_scaling_margin`) and the run-length machinery from the same file
-- (`jordanRunLength`, `exists_jordan_scaling_vector`) via a norm-matrix
-- wrapper.  Only what is missing over ℂ is defined here.












namespace NumStability

open scoped BigOperators

-- ============================================================
-- Missing pieces of the complex ∞-norm lemma suite
-- (complexMatrixInfNorm = the max-row-sum «cInfNorm»; the definition and
--  the nonneg / row_sum_le / le_of_row_sum_le lemmas are reused from
--  Analysis/MatrixNorms/Basic.lean)
-- ============================================================

/-- Matrix–vector ∞-norm bound over ℂ:
    `‖A x‖∞ ≤ ‖A‖∞ · ‖x‖∞` for the concrete complex row-sum norm. -/
theorem complexVecInfNorm_vecMul_le {m n : ℕ} (A : CMatrix m n) (x : CVec n) :
    complexVecInfNorm (complexMatrixVecMul A x) ≤
      complexMatrixInfNorm A * complexVecInfNorm x := by
  apply complexVecInfNorm_le_of_coord_le
  · exact mul_nonneg (complexMatrixInfNorm_nonneg A) (complexVecInfNorm_nonneg x)
  · intro i
    calc ‖complexMatrixVecMul A x i‖
        = ‖∑ j : Fin n, A i j * x j‖ := rfl
      _ ≤ ∑ j : Fin n, ‖A i j * x j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖A i j‖ * ‖x j‖ :=
          Finset.sum_congr rfl (fun j _ => norm_mul _ _)
      _ ≤ ∑ j : Fin n, ‖A i j‖ * complexVecInfNorm x := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (complexVecInfNorm_coord_le x j)
            (norm_nonneg _)
      _ = (∑ j : Fin n, ‖A i j‖) * complexVecInfNorm x :=
          (Finset.sum_mul ..).symm
      _ ≤ complexMatrixInfNorm A * complexVecInfNorm x :=
          mul_le_mul_of_nonneg_right (complexMatrixInfNorm_row_sum_le A i)
            (complexVecInfNorm_nonneg x)

/-- Submultiplicativity of the complex matrix ∞-norm over `complexMatrixMul`:
    `‖A·B‖∞ ≤ ‖A‖∞ · ‖B‖∞`.  The proof only uses `‖ab‖ = ‖a‖‖b‖` and the
    triangle inequality, exactly as in the real case. -/
theorem complexMatrixInfNorm_mul_le {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) :
    complexMatrixInfNorm (complexMatrixMul A B) ≤
      complexMatrixInfNorm A * complexMatrixInfNorm B := by
  apply complexMatrixInfNorm_le_of_row_sum_le
  · exact mul_nonneg (complexMatrixInfNorm_nonneg A)
      (complexMatrixInfNorm_nonneg B)
  · intro i
    calc ∑ j : Fin p, ‖complexMatrixMul A B i j‖
        = ∑ j : Fin p, ‖∑ k : Fin n, A i k * B k j‖ := rfl
      _ ≤ ∑ j : Fin p, ∑ k : Fin n, ‖A i k * B k j‖ :=
          Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
      _ = ∑ k : Fin n, ∑ j : Fin p, ‖A i k * B k j‖ := by
          rw [Finset.sum_comm]
      _ = ∑ k : Fin n, ‖A i k‖ * ∑ j : Fin p, ‖B k j‖ := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => norm_mul _ _)
      _ ≤ ∑ k : Fin n, ‖A i k‖ * complexMatrixInfNorm B := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left
            (complexMatrixInfNorm_row_sum_le B k) (norm_nonneg _)
      _ = (∑ k : Fin n, ‖A i k‖) * complexMatrixInfNorm B :=
          (Finset.sum_mul ..).symm
      _ ≤ complexMatrixInfNorm A * complexMatrixInfNorm B :=
          mul_le_mul_of_nonneg_right (complexMatrixInfNorm_row_sum_le A i)
            (complexMatrixInfNorm_nonneg B)

/-- Triangle inequality for the complex matrix ∞-norm (entrywise sum). -/
theorem complexMatrixInfNorm_add_le {m n : ℕ} (M N : CMatrix m n) :
    complexMatrixInfNorm (fun i j => M i j + N i j) ≤
      complexMatrixInfNorm M + complexMatrixInfNorm N := by
  apply complexMatrixInfNorm_le_of_row_sum_le
  · exact add_nonneg (complexMatrixInfNorm_nonneg M)
      (complexMatrixInfNorm_nonneg N)
  · intro i
    calc ∑ j : Fin n, ‖M i j + N i j‖
        ≤ ∑ j : Fin n, (‖M i j‖ + ‖N i j‖) :=
          Finset.sum_le_sum (fun j _ => norm_add_le _ _)
      _ = (∑ j : Fin n, ‖M i j‖) + ∑ j : Fin n, ‖N i j‖ :=
          Finset.sum_add_distrib
      _ ≤ complexMatrixInfNorm M + complexMatrixInfNorm N :=
          add_le_add (complexMatrixInfNorm_row_sum_le M i)
            (complexMatrixInfNorm_row_sum_le N i)

/-- A diagonal complex matrix with entries of modulus at most `ρ ≥ 0` has
    ∞-norm at most `ρ`. -/
theorem complexMatrixInfNorm_diagonal_le {n : ℕ} (M : CMatrix n n) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hdiag : ∀ i j, i ≠ j → M i j = 0)
    (hlam : ∀ i, ‖M i i‖ ≤ ρ) : complexMatrixInfNorm M ≤ ρ := by
  apply complexMatrixInfNorm_le_of_row_sum_le hρ0
  intro i
  have hsingle : ∑ j : Fin n, ‖M i j‖ = ‖M i i‖ := by
    refine Finset.sum_eq_single i (fun b _ hb => ?_) (fun h => ?_)
    · rw [hdiag i b (Ne.symm hb), norm_zero]
    · exact absurd (Finset.mem_univ i) h
  rw [hsingle]
  exact hlam i

-- ============================================================
-- Real-cast bridges: embedding ℝ-vectors and ℝ-matrices into ℂ
-- preserves the ∞-norms (via ‖(x : ℂ)‖ = ‖x‖ = |x|)
-- ============================================================

/-- The complex ∞-norm of a real-cast vector equals the real ∞-norm. -/
theorem complexVecInfNorm_ofReal {n : ℕ} (x : Fin n → ℝ) :
    complexVecInfNorm (fun i => ((x i : ℝ) : ℂ)) = infNormVec x := by
  apply le_antisymm
  · apply complexVecInfNorm_le_of_coord_le _ (infNormVec_nonneg x)
    intro i
    show ‖((x i : ℝ) : ℂ)‖ ≤ infNormVec x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le_infNormVec x i
  · apply infNormVec_le_of_abs_le
    · intro i
      have h := complexVecInfNorm_coord_le (fun k => ((x k : ℝ) : ℂ)) i
      simp only [Complex.norm_real, Real.norm_eq_abs] at h
      exact h
    · exact complexVecInfNorm_nonneg _

/-- The complex matrix ∞-norm of a real-cast matrix equals the real matrix
    ∞-norm: `‖Â‖∞ = ‖A‖∞` for `Â i j := ((A i j : ℝ) : ℂ)`. -/
theorem complexMatrixInfNorm_ofReal {n : ℕ} (M : Fin n → Fin n → ℝ) :
    complexMatrixInfNorm (fun i j => ((M i j : ℝ) : ℂ)) = infNorm M := by
  apply le_antisymm
  · apply complexMatrixInfNorm_le_of_row_sum_le (infNorm_nonneg M)
    intro i
    calc ∑ j : Fin n, ‖((M i j : ℝ) : ℂ)‖
        = ∑ j : Fin n, |M i j| :=
          Finset.sum_congr rfl (fun j _ => by
            rw [Complex.norm_real, Real.norm_eq_abs])
      _ ≤ infNorm M := row_sum_le_infNorm M i
  · apply infNorm_le_of_row_sum_le
    · intro i
      calc ∑ j : Fin n, |M i j|
          = ∑ j : Fin n, ‖((M i j : ℝ) : ℂ)‖ :=
            Finset.sum_congr rfl (fun j _ => by
              rw [Complex.norm_real, Real.norm_eq_abs])
        _ ≤ complexMatrixInfNorm (fun i j => ((M i j : ℝ) : ℂ)) :=
            complexMatrixInfNorm_row_sum_le
              (fun i j => ((M i j : ℝ) : ℂ)) i
    · exact complexMatrixInfNorm_nonneg _

/-- Perturbation-to-complex norm transfer: a real componentwise bound
    `|ΔA| ≤ η|A|` gives `‖ΔÂ‖∞ ≤ η·‖A‖∞` for the real-cast matrix `ΔÂ`.
    (Combined with `complexMatrixInfNorm_ofReal`, this is
    `‖ΔÂ‖∞ ≤ η·‖Â‖∞`.) -/
theorem complexMatrixInfNorm_ofReal_le_mul {n : ℕ}
    (ΔA A : Fin n → Fin n → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hΔ : ∀ i j, |ΔA i j| ≤ η * |A i j|) :
    complexMatrixInfNorm (fun i j => ((ΔA i j : ℝ) : ℂ)) ≤ η * infNorm A := by
  rw [complexMatrixInfNorm_ofReal]
  exact infNorm_le_mul_of_abs_le_mul_abs ΔA A hη hΔ

-- ============================================================
-- Entrywise addition distributes over complexMatrixMul
-- ============================================================

/-- Left distributivity of `complexMatrixMul` over entrywise addition. -/
theorem complexMatrixMul_add_left {m n p : ℕ}
    (A B : CMatrix m n) (C : CMatrix n p) :
    complexMatrixMul (fun i j => A i j + B i j) C
      = fun i j => complexMatrixMul A C i j + complexMatrixMul B C i j := by
  funext i j
  unfold complexMatrixMul
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => add_mul _ _ _)

/-- Right distributivity of `complexMatrixMul` over entrywise addition. -/
theorem complexMatrixMul_add_right {m n p : ℕ}
    (A : CMatrix m n) (B C : CMatrix n p) :
    complexMatrixMul A (fun i j => B i j + C i j)
      = fun i j => complexMatrixMul A B i j + complexMatrixMul A C i j := by
  funext i j
  unfold complexMatrixMul
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => mul_add _ _ _)

-- ============================================================
-- §18.2  Complex similarity-based convergence engine (eq 18.14)
-- for a REAL computed-power sequence, embedded into ℂ
-- ============================================================





































































































































-- ============================================================
-- Complex diagonal scaling matrices
-- ============================================================












































-- ============================================================
-- The scaled bidiagonal row-sum bound ‖D⁻¹ J D‖∞ ≤ ρ + β over ℂ
-- ============================================================























































































































-- ============================================================
-- Run lengths of superdiagonal chains for a ℂ-entry Jordan matrix
-- ============================================================






































-- ============================================================
-- Theorem 18.1: the absorbing similarity over ℂ (all t ≥ 1)
-- ============================================================







































































































































































































































































































































































-- ============================================================
-- Theorem 18.1: axiom-free end-to-end forms (complex Jordan data)
-- ============================================================


































































































end NumStability
