import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatVec
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Algorithms.MatrixPowers.ComputedIteration.Model

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

/-- Model for computing A^m v by repeated matrix-vector multiplication.

    At each step the computed vector satisfies
      v_{k+1} = (A + ΔA_k) · v_k,   |ΔA_k| ≤ c · |A|  componentwise
    corresponding to Higham eq (18.10)–(18.11).

    The constant c is `gamma fp n` when each step is a standard matVec
    of an n-column matrix (from `matVec_backward_error`). -/
structure ComputedMatPowVec (n : ℕ) (A : Fin n → Fin n → ℝ)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) : Prop where
  step : ∀ k, ∃ ΔA : Fin n → Fin n → ℝ,
    (∀ i j, |ΔA i j| ≤ c * |A i j|) ∧
    (∀ i, v (k + 1) i = ∑ j : Fin n, (A i j + ΔA i j) * v k j)

/-- Weakening the per-step perturbation constant: a computed-power sequence
    with componentwise budget `c` also satisfies any larger budget `c'`. -/
theorem ComputedMatPowVec.mono {n : ℕ} {A : Fin n → Fin n → ℝ}
    {v : ℕ → (Fin n → ℝ)} {c c' : ℝ} (hcc : c ≤ c')
    (h : ComputedMatPowVec n A v c) : ComputedMatPowVec n A v c' := by
  constructor
  intro k
  obtain ⟨ΔA, hΔ, heq⟩ := h.step k
  exact ⟨ΔA, fun i j =>
    (hΔ i j).trans (mul_le_mul_of_nonneg_right hcc (abs_nonneg _)), heq⟩

-- ============================================================
-- §18.2  Concrete floating-point realization of (18.10)–(18.11)
-- ============================================================

/-- The computed iteration `v_{k+1} = fl(A · v_k)` by repeated floating-point
    matrix–vector products, starting from `v0`.  This is the concrete
    algorithm whose error recurrence is eq (18.10). -/
noncomputable def fl_matPowVecSeq (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (v0 : Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => v0
  | k + 1 => fl_matVec fp n n A (fl_matPowVecSeq fp n A v0 k)

/-- **Concrete realization of the error model (18.10)–(18.11)**: the
    floating-point iteration `v_{k+1} = fl(A v_k)` satisfies the perturbed
    recurrence `v_{k+1} = (A + ΔA_k) v_k` with `|ΔA_k| ≤ γ_n |A|`
    componentwise.  Each step is one `fl_matVec` with inner dimension `n`
    (from `matVec_backward_error`), so the per-step constant is `γ_n`;
    the book's (18.11) uses the weaker constant `γ_{n+2}`, recovered in
    `computedMatPowVec_fl_matVec_gamma_add_two` by monotonicity. -/
theorem computedMatPowVec_fl_matVec (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (v0 : Fin n → ℝ) (hn : gammaValid fp n) :
    ComputedMatPowVec n A (fl_matPowVecSeq fp n A v0) (gamma fp n) := by
  constructor
  intro k
  obtain ⟨ΔA, hΔ, heq⟩ :=
    matVec_backward_error fp n n A (fl_matPowVecSeq fp n A v0 k) hn
  refine ⟨ΔA, hΔ, fun i => ?_⟩
  show fl_matPowVecSeq fp n A v0 (k + 1) i = _
  simp only [fl_matPowVecSeq]
  exact heq i

/-- The concrete realization stated with the book's (18.11) constant
    `γ_{n+2}` (valid since `γ_n ≤ γ_{n+2}`). -/
theorem computedMatPowVec_fl_matVec_gamma_add_two (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (v0 : Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2)) :
    ComputedMatPowVec n A (fl_matPowVecSeq fp n A v0) (gamma fp (n + 2)) :=
  (computedMatPowVec_fl_matVec fp n A v0
      (gammaValid_mono fp (Nat.le_add_right n 2) hn2)).mono
    (gamma_mono fp (Nat.le_add_right n 2) hn2)

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

/-- **Computed powers tend to zero from a geometric decay bound**.

    Higham states the conclusion of Theorems 18.1 and 18.2 as the *limit*
    `fl(A^m) → 0` as `m → ∞`, whereas the results above establish only the
    geometric *bound* `‖v_m‖∞ ≤ C · q^m · ‖v_0‖∞` with `q < 1`.  This lemma
    supplies the missing step: any such geometric bound forces
    `‖v_m‖∞ → 0`.

    Reusable for both the Higham–Knight matrix-power theorem (18.1) and its
    diagonalizable/pseudospectral corollary (18.2): apply it to the existential
    output `⟨C, q, _, _, hq1, hbound⟩` of the convergence theorem. Purely a
    real-analysis squeeze; introduces no assumption about `A`. -/
theorem computedMatPow_tendsto_zero_of_geometric (n : ℕ)
    (v : ℕ → (Fin n → ℝ)) (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ m, infNormVec (v m) ≤ C * q ^ m * infNormVec (v 0)) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun m : ℕ => q ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have htop : Filter.Tendsto (fun m => C * q ^ m * infNormVec (v 0))
      Filter.atTop (nhds 0) := by
    simpa using (hpow.const_mul C).mul_const (infNormVec (v 0))
  exact squeeze_zero (fun m => infNormVec_nonneg _) hbound htop

-- ============================================================
-- §18.2  End-to-end conditional forms with the limit conclusion
-- ============================================================






























































-- ============================================================
-- §18.2  Discharging `similarity_absorbs`: real-diagonalizable case (t = 1)
-- ============================================================


































































































































































-- ============================================================
-- §18.1  Exact arithmetic: eq (18.4), real-diagonalizable case
-- ============================================================












































































































































































-- ============================================================
-- §18.2  Eq (18.12): weighted (Collatz–Wielandt) certificate form
-- ============================================================





































































































































end NumStability
