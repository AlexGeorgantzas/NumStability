import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatrixPowers.ComputedIteration.Model
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.ComputedIteration

/-!
# Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.RealCases

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
















































/-- **Conditional reduction of Theorem 18.1** (Higham–Knight).

    This is **not** a full proof of Theorem 18.1.  It *assumes* the
    perturbation-absorbing similarity construction via
    `JordanFormSpec.similarity_absorbs` (an undischarged axiom — see there) and
    then performs only the book's elementary telescoping step.  The source row
    for Theorem 18.1 remains OPEN until that axiom is discharged.

    Given Jordan form data (X, X⁻¹, ρ, t) with ρ(A) < 1 and the Higham–Knight
    condition (18.13)

      4t · c · κ∞(X) · ‖A‖∞ < (1 − ρ(A))^t

    where t = max_i n_i (largest Jordan block), c is the per-step backward
    error bound, and κ∞(X) = ‖X‖∞ · ‖X⁻¹‖∞, it concludes geometric decay:
    ∃ C q, q < 1 ∧ ‖v_m‖∞ ≤ C · q^m · ‖v_0‖∞, with C = κ∞(S) for the scaled
    similarity S = X P(ε) (eq 18.15); in general κ∞(S) ≥ κ∞(X) when t > 1.

    Compose with `computedMatPow_tendsto_zero_of_geometric` to obtain the
    book's stated limit conclusion fl(A^m) → 0. -/
theorem higham_knight_18_1 (n : ℕ) (hn : 0 < n)
    (A X X_inv : Fin n → Fin n → ℝ)
    (hJ : JordanFormSpec n hn A X X_inv)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * hJ.max_block_size * c *
      (infNorm X * infNorm X_inv) * infNorm A <
      (1 - hJ.spectral_radius) ^ hJ.max_block_size) :
    ∃ (C q : ℝ), 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ m, infNormVec (v m) ≤
        C * q ^ m * infNormVec (v 0) := by
  obtain ⟨S, S_inv, q, hSr, hq0, hq1, hAbsorb⟩ :=
    hJ.similarity_absorbs c hc hCond
  exact ⟨infNorm S * infNorm S_inv, q,
    mul_nonneg (infNorm_nonneg S) (infNorm_nonneg S_inv),
    hq0, hq1, fun m =>
    similarity_normwise_bound n hn A S S_inv hSr v c hComp q hq0 hAbsorb m⟩

-- ============================================================
-- §18.2  Limit form of the convergence conclusion
-- ============================================================
























-- ============================================================
-- §18.2  End-to-end conditional forms with the limit conclusion
-- ============================================================

/-- **End-to-end conditional form of Theorem 18.1 for the actual
    floating-point iteration.**  Composes the concrete (18.10)–(18.11)
    realization (`fl_matPowVecSeq`, per-step constant `γ_{n+2}`), the
    conditional reduction `higham_knight_18_1`, and the limit wrapper: under
    the Jordan-data hypothesis (including the ASSUMED `similarity_absorbs`
    construction — see `JordanFormSpec`) and the Higham–Knight condition
    (18.13) with the printed constant `γ_{n+2}`, the computed vectors
    satisfy `‖fl(Aᵐ v₀)‖∞ → 0`.

    Still conditional on the `similarity_absorbs` axiom; the Theorem 18.1
    source row remains OPEN until that construction is discharged. -/
theorem higham_knight_18_1_fl_tendsto (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (A X X_inv : Fin n → Fin n → ℝ)
    (hJ : JordanFormSpec n hn A X X_inv)
    (v0 : Fin n → ℝ) (hval : gammaValid fp (n + 2))
    (hCond : 4 * hJ.max_block_size * gamma fp (n + 2) *
      (infNorm X * infNorm X_inv) * infNorm A <
      (1 - hJ.spectral_radius) ^ hJ.max_block_size) :
    Filter.Tendsto
      (fun m => infNormVec (fl_matPowVecSeq fp n A v0 m))
      Filter.atTop (nhds 0) := by
  obtain ⟨C, q, hC, hq0, hq1, hbound⟩ :=
    higham_knight_18_1 n hn A X X_inv hJ
      (fl_matPowVecSeq fp n A v0) (gamma fp (n + 2))
      (gamma_nonneg fp hval)
      (computedMatPowVec_fl_matVec_gamma_add_two fp n A v0 hval)
      hCond
  exact computedMatPow_tendsto_zero_of_geometric n
    (fl_matPowVecSeq fp n A v0) C q hq0 hq1 hbound

/-- **Conditional reduction of Theorem 18.2** (Higham–Knight), algebraic
    `t = 1` form.  The book's proof of Theorem 18.2 reduces the
    pseudospectral hypothesis to Theorem 18.1 with `t = 1` (diagonalizable
    `A`), where condition (18.13) becomes
    `4 · c · κ∞(X) · ‖A‖∞ < 1 − ρ(A)`.  This theorem formalizes exactly
    that reduction target with the limit conclusion `‖v_m‖∞ → 0`.

    NOT the full printed Theorem 18.2: the pseudospectral packaging
    (`ρ_ε(A) < 1` with `ε = cₙu‖A‖₂`, eqs (18.8)–(18.9), the unique dominant
    eigenvalue and norm normalizations, and the O(ε²) proviso) is deferred —
    pseudospectra are absent from Mathlib and this repository.  Also
    conditional on the `similarity_absorbs` axiom via `higham_knight_18_1`;
    the Theorem 18.2 source row remains OPEN. -/
theorem higham_knight_18_2_diagonalizable (n : ℕ) (hn : 0 < n)
    (A X X_inv : Fin n → Fin n → ℝ)
    (hJ : JordanFormSpec n hn A X X_inv)
    (ht : hJ.max_block_size = 1)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * c * (infNorm X * infNorm X_inv) * infNorm A <
      1 - hJ.spectral_radius) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  have hCond1 : 4 * hJ.max_block_size * c *
      (infNorm X * infNorm X_inv) * infNorm A <
      (1 - hJ.spectral_radius) ^ hJ.max_block_size := by
    rw [ht]
    simpa using hCond
  obtain ⟨C, q, hC, hq0, hq1, hbound⟩ :=
    higham_knight_18_1 n hn A X X_inv hJ v c hc hComp hCond1
  exact computedMatPow_tendsto_zero_of_geometric n v C q hq0 hq1 hbound

-- ============================================================
-- §18.2  Discharging `similarity_absorbs`: real-diagonalizable case (t = 1)
-- ============================================================






















































































































/-- **Axiom-free real-diagonalizable case of Theorem 18.1** (limit form,
    abstract error model): if `X⁻¹AX = J` is diagonal with `|J i i| ≤ ρ < 1`
    and the `t = 1` Higham–Knight condition `4·c·κ∞(X)·‖A‖∞ < 1 − ρ` holds,
    then any computed-power sequence with per-step budget `c` satisfies
    `‖v_m‖∞ → 0`.  No `similarity_absorbs` assumption: the construction is
    discharged by `JordanFormSpec.ofRealDiagonal`. -/
theorem higham_18_1_real_diagonalizable_tendsto (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hlam : ∀ i, |J i i| ≤ ρ)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * c * (infNorm X * infNorm X_inv) * infNorm A < 1 - ρ) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) :=
  higham_knight_18_2_diagonalizable n hn A X X_inv
    (JordanFormSpec.ofRealDiagonal n hn A X X_inv J hXr hsim hdiag ρ hρ0 hρ1 hlam)
    rfl v c hc hComp hCond

/-- **Axiom-free real-diagonalizable case of Theorem 18.1 for the actual
    floating-point iteration**: with `X⁻¹AX = J` diagonal, `|J i i| ≤ ρ < 1`,
    and `4·γ_{n+2}·κ∞(X)·‖A‖∞ < 1 − ρ`, the computed vectors
    `fl(Aᵐ v₀)` (repeated `fl_matVec`) satisfy `‖fl(Aᵐ v₀)‖∞ → 0`.
    Fully end-to-end: concrete algorithm, concrete rounding model,
    no assumed construction. -/
theorem higham_18_1_real_diagonalizable_fl_tendsto (fp : FPModel)
    (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hlam : ∀ i, |J i i| ≤ ρ)
    (v0 : Fin n → ℝ) (hval : gammaValid fp (n + 2))
    (hCond : 4 * gamma fp (n + 2) * (infNorm X * infNorm X_inv) *
      infNorm A < 1 - ρ) :
    Filter.Tendsto
      (fun m => infNormVec (fl_matPowVecSeq fp n A v0 m))
      Filter.atTop (nhds 0) :=
  higham_18_1_real_diagonalizable_tendsto n hn A X X_inv J hXr hsim hdiag
    ρ hρ0 hρ1 hlam (fl_matPowVecSeq fp n A v0) (gamma fp (n + 2))
    (gamma_nonneg fp hval)
    (computedMatPowVec_fl_matVec_gamma_add_two fp n A v0 hval) hCond

-- ============================================================
-- §18.1  Exact arithmetic: eq (18.4), real-diagonalizable case
-- ============================================================












































































































































































-- ============================================================
-- §18.2  Eq (18.12): weighted (Collatz–Wielandt) certificate form
-- ============================================================





































































































































end NumStability
