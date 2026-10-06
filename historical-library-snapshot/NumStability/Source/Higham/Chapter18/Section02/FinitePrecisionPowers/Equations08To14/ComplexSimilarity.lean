import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatrixPowers.ComputedIteration.Model
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Complex
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.VectorNorms.Basic

/-!
# Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.ComplexSimilarity

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
























































































-- ============================================================
-- Real-cast bridges: embedding ℝ-vectors and ℝ-matrices into ℂ
-- preserves the ∞-norms (via ‖(x : ℂ)‖ = ‖x‖ = |x|)
-- ============================================================



















































-- ============================================================
-- Entrywise addition distributes over complexMatrixMul
-- ============================================================





















-- ============================================================
-- §18.2  Complex similarity-based convergence engine (eq 18.14)
-- for a REAL computed-power sequence, embedded into ℂ
-- ============================================================

/-- **Complex similarity product bound** (eq 18.14 of Theorem 18.1's proof,
    transported to a complex similarity `S`): if the real computed-power
    sequence `v` satisfies the perturbed recurrence (18.10)–(18.11) with
    budget `c`, and the complex similarity `S` absorbs every admissible
    perturbation, `‖S⁻¹(Â+ΔÂ)S‖∞ ≤ q`, then the transformed embedded
    vectors decay geometrically:
    `‖S⁻¹ v̂_m‖∞ ≤ q^m · ‖S⁻¹ v̂_0‖∞`, where `v̂_m i := ((v m i : ℝ) : ℂ)`.

    Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
    Theorem 18.1 (pp. 347–348) — the telescoping step of the proof. -/
theorem complex_similarity_product_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (S S_inv : CMatrix n n)
    (hSr : IsComplexMatrixRightInverse S S_inv)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ)
    (hComp : ComputedMatPowVec n A v c)
    (q : ℝ) (hq : 0 ≤ q)
    (hBound : ∀ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ c * |A i j|) →
      complexMatrixInfNorm (complexMatrixMul S_inv (complexMatrixMul
        (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S)) ≤ q) :
    ∀ m, complexVecInfNorm
        (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) ≤
      q ^ m * complexVecInfNorm
        (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ))) := by
  intro m
  induction m with
  | zero => simp [pow_zero, one_mul]
  | succ m ih =>
    obtain ⟨ΔA, hΔ, hstep⟩ := hComp.step m
    have hBk := hBound ΔA hΔ
    -- Embed the real perturbed step into ℂ: v̂_{m+1} = (Â+ΔÂ)·v̂_m.
    have hstepC : (fun i => ((v (m + 1) i : ℝ) : ℂ)) =
        complexMatrixVecMul (fun i j => ((A i j + ΔA i j : ℝ) : ℂ))
          (fun i => ((v m i : ℝ) : ℂ)) := by
      funext i
      show ((v (m + 1) i : ℝ) : ℂ) =
        ∑ j : Fin n, ((A i j + ΔA i j : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)
      rw [hstep i, Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun j _ => Complex.ofReal_mul _ _)
    -- Key: S⁻¹ v̂_{m+1} = (S⁻¹(Â+ΔÂ)S)(S⁻¹ v̂_m).
    have key : complexMatrixVecMul S_inv (fun i => ((v (m + 1) i : ℝ) : ℂ)) =
        complexMatrixVecMul
          (complexMatrixMul S_inv (complexMatrixMul
            (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S))
          (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) := by
      rw [complexMatrixVecMul_mul, complexMatrixVecMul_mul, hSr, ← hstepC]
    calc complexVecInfNorm
          (complexMatrixVecMul S_inv (fun i => ((v (m + 1) i : ℝ) : ℂ)))
        = complexVecInfNorm (complexMatrixVecMul
            (complexMatrixMul S_inv (complexMatrixMul
              (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S))
            (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ)))) := by
          rw [key]
      _ ≤ complexMatrixInfNorm (complexMatrixMul S_inv (complexMatrixMul
            (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S)) *
          complexVecInfNorm
            (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) :=
          complexVecInfNorm_vecMul_le _ _
      _ ≤ q * complexVecInfNorm
            (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) :=
          mul_le_mul_of_nonneg_right hBk (complexVecInfNorm_nonneg _)
      _ ≤ q * (q ^ m * complexVecInfNorm
            (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ)))) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (m + 1) * complexVecInfNorm
            (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ))) := by
          ring

/-- **Complex normwise bound via similarity**:
    `‖v_m‖∞ ≤ κ∞(S) · q^m · ‖v_0‖∞` with `κ∞(S) = ‖S‖∞·‖S⁻¹‖∞` over ℂ,
    for a real computed-power sequence `v` and complex absorbing
    similarity `S`.  Uses `v̂ = S(S⁻¹ v̂)` and the real-cast norm equality
    `‖v̂_m‖∞ = ‖v_m‖∞`. -/
theorem complex_similarity_normwise_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (S S_inv : CMatrix n n)
    (hSr : IsComplexMatrixRightInverse S S_inv)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ)
    (hComp : ComputedMatPowVec n A v c)
    (q : ℝ) (hq : 0 ≤ q)
    (hBound : ∀ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ c * |A i j|) →
      complexMatrixInfNorm (complexMatrixMul S_inv (complexMatrixMul
        (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S)) ≤ q)
    (m : ℕ) :
    infNormVec (v m) ≤
      complexMatrixInfNorm S * complexMatrixInfNorm S_inv * q ^ m *
        infNormVec (v 0) := by
  have hprod := complex_similarity_product_bound n A S S_inv hSr v c hComp
    q hq hBound m
  have hrecover : (fun i => ((v m i : ℝ) : ℂ)) =
      complexMatrixVecMul S
        (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) :=
    (hSr _).symm
  have h1 : infNormVec (v m) ≤
      complexMatrixInfNorm S * complexVecInfNorm
        (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) := by
    calc infNormVec (v m)
        = complexVecInfNorm (fun i => ((v m i : ℝ) : ℂ)) :=
          (complexVecInfNorm_ofReal (v m)).symm
      _ = complexVecInfNorm (complexMatrixVecMul S
            (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ)))) :=
          congrArg complexVecInfNorm hrecover
      _ ≤ complexMatrixInfNorm S * complexVecInfNorm
            (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) :=
          complexVecInfNorm_vecMul_le _ _
  have h3 : complexVecInfNorm
      (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ))) ≤
      complexMatrixInfNorm S_inv * infNormVec (v 0) := by
    calc complexVecInfNorm
          (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ)))
        ≤ complexMatrixInfNorm S_inv *
            complexVecInfNorm (fun i => ((v 0 i : ℝ) : ℂ)) :=
          complexVecInfNorm_vecMul_le _ _
      _ = complexMatrixInfNorm S_inv * infNormVec (v 0) := by
          rw [complexVecInfNorm_ofReal]
  calc infNormVec (v m)
      ≤ complexMatrixInfNorm S * complexVecInfNorm
          (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) := h1
    _ ≤ complexMatrixInfNorm S * (q ^ m * complexVecInfNorm
          (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ)))) :=
        mul_le_mul_of_nonneg_left hprod (complexMatrixInfNorm_nonneg S)
    _ ≤ complexMatrixInfNorm S *
          (q ^ m * (complexMatrixInfNorm S_inv * infNormVec (v 0))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h3 (pow_nonneg hq m))
          (complexMatrixInfNorm_nonneg S)
    _ = complexMatrixInfNorm S * complexMatrixInfNorm S_inv * q ^ m *
          infNormVec (v 0) := by
        ring

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
