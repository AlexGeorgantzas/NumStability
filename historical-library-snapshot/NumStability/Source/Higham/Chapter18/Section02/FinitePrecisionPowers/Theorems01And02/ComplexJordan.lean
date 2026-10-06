import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatrixPowers.ComputedIteration.Model
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.Complex
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.ComplexSimilarity

/-!
# Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.ComplexJordan

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

/-- **Theorem 18.1 (Higham–Knight), complex Jordan data, limit form,
    abstract error model** — Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §18.2, Theorem 18.1 (pp. 347–348).

    Let `A` be a REAL `n×n` matrix (the computed iteration is a
    floating-point object, hence real, matching the book's setting) with
    COMPLEX Jordan-form similarity data: `X·X⁻¹ = I` over ℂ (as the vector
    action `IsComplexMatrixRightInverse`), `X⁻¹ Â X = J` for the real-cast
    `Â i j = ((A i j : ℝ) : ℂ)`, `J` upper bidiagonal with `‖J_{ii}‖ ≤ ρ < 1`,
    superdiagonal moduli ≤ 1, all other entries zero, and every run of
    consecutive nonzero superdiagonal entries of length ≤ `t − 1`
    (max Jordan block size ≤ `t`, via `cJordanRunLength`); all `1 ≤ t`.
    Under the Higham–Knight condition (18.13)

      `4t·c·κ∞(X)·‖A‖∞ < (1−ρ)^t`,
      `κ∞(X) := complexMatrixInfNorm X * complexMatrixInfNorm X_inv`,

    every real computed-power sequence `v` with per-step componentwise
    budget `c` (`ComputedMatPowVec`, eqs (18.10)–(18.11)) satisfies
    `‖v_m‖∞ → 0`.

    Scope: complex Jordan data as hypothesis (every complex matrix has one;
    JNF existence itself is not formalized — Mathlib lacks it); this is the
    full generality of the printed statement for a real input matrix `A`.
    No assumed contraction/absorption hypothesis: the absorbing similarity
    is PROVED from the Jordan data (`complex_jordan_similarity_absorbs`,
    δ-scaling construction with the `(1+1/m)^m < e < 4` optimisation). -/
theorem higham_18_1_complex_jordan_tendsto (n : ℕ)
    (A : Fin n → Fin n → ℝ) (X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hsim : complexMatrixMul X_inv (complexMatrixMul
      (fun i j => ((A i j : ℝ) : ℂ)) X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (t : ℕ) (ht1 : 1 ≤ t)
    (hrun : ∀ k, cJordanRunLength n J k ≤ t - 1)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * (t : ℝ) * c *
      (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
      < (1 - ρ) ^ t) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  obtain ⟨S, S_inv, q, hSr, hq0, hq1, hAbsorb⟩ :=
    complex_jordan_similarity_absorbs n A X X_inv J hXr hsim hshape
      ρ hρ0 hρ1 hdiagbd hsup t ht1 hrun c hc hCond
  have hbound : ∀ m, infNormVec (v m) ≤
      complexMatrixInfNorm S * complexMatrixInfNorm S_inv * q ^ m *
        infNormVec (v 0) :=
    fun m => complex_similarity_normwise_bound n A S S_inv hSr v c hComp
      q hq0 hAbsorb m
  exact computedMatPow_tendsto_zero_of_geometric n v
    (complexMatrixInfNorm S * complexMatrixInfNorm S_inv) q hq0 hq1 hbound

/-- **Theorem 18.1 (Higham–Knight), complex Jordan data, for the actual
    floating-point iteration** — Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §18.2, Theorem 18.1 (pp. 347–348).

    With complex Jordan data for the real matrix `A` as in
    `higham_18_1_complex_jordan_tendsto` and the printed condition (18.13)
    with the book's constant `γ_{n+2}`,

      `4t·γ_{n+2}·κ∞(X)·‖A‖∞ < (1−ρ)^t`,

    the computed vectors `fl(Aᵐ v₀)` (repeated `fl_matVec`) satisfy
    `‖fl(Aᵐ v₀)‖∞ → 0`.  Fully end-to-end: concrete algorithm, concrete
    rounding model, no assumed construction.

    Scope: complex Jordan data as hypothesis (every complex matrix has one;
    JNF existence itself is not formalized — Mathlib lacks it); this is the
    full generality of the printed statement for a real input matrix `A`. -/
theorem higham_18_1_complex_jordan_fl_tendsto (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hsim : complexMatrixMul X_inv (complexMatrixMul
      (fun i j => ((A i j : ℝ) : ℂ)) X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (t : ℕ) (ht1 : 1 ≤ t)
    (hrun : ∀ k, cJordanRunLength n J k ≤ t - 1)
    (v0 : Fin n → ℝ) (hval : gammaValid fp (n + 2))
    (hCond : 4 * (t : ℝ) * gamma fp (n + 2) *
      (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
      < (1 - ρ) ^ t) :
    Filter.Tendsto
      (fun m => infNormVec (fl_matPowVecSeq fp n A v0 m))
      Filter.atTop (nhds 0) :=
  higham_18_1_complex_jordan_tendsto n A X X_inv J hXr hsim hshape
    ρ hρ0 hρ1 hdiagbd hsup t ht1 hrun (fl_matPowVecSeq fp n A v0)
    (gamma fp (n + 2)) (gamma_nonneg fp hval)
    (computedMatPowVec_fl_matVec_gamma_add_two fp n A v0 hval) hCond

end NumStability
