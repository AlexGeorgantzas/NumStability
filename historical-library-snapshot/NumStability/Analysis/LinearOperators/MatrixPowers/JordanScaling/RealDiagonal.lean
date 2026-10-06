import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.PolynomialEvaluation.MatrixNorms
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Real
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding

/-!
# Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal

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

/-- Jordan form data for a matrix `A`, **plus one assumed axiom** carrying the
    crux of Theorem 18.1.

    The plain data fields are innocuous: `X`, `X_inv` (similarity `A = X J X⁻¹`),
    `spectral_radius` `ρ(A) < 1` (convergent matrix), and `max_block_size`
    `t = maxᵢ nᵢ` (largest Jordan block).

    ⚠ AXIOM / OPEN OBLIGATION.  The field `similarity_absorbs` is **not proved
    here** — it is an assumed hypothesis that packages the entire non-trivial
    content of Theorem 18.1's proof (Higham pp. 347–348): the `S = X P(ε)`
    Jordan-block δ-scaling construction with `D(δ) = diag(1,δ,…,δ^{nᵢ-1})`, and
    the `(1+1/t)^t < e < 4` optimisation, which turn the Higham–Knight condition
    `4t·η·κ∞(X)·‖A‖∞ < (1-ρ)^t` into a per-step contraction
    `‖S⁻¹(A+ΔA)S‖∞ ≤ q < 1` for all `|ΔA| ≤ η|A|`.  Discharging it needs
    classical Jordan Normal Form over ℂ, which Mathlib does not currently
    provide (only Jordan–Chevalley).  Until it is discharged, every result
    consuming this field is *conditional on this axiom*, not a closure of
    Theorem 18.1.

    Note: κ∞(S) ≤ (1−ρ−ε)^{1−t} · κ∞(X) from eq (18.15), which is
    generally ≥ κ∞(X) when t > 1.  We do not constrain κ∞(S) here;
    the convergence constant C in Theorem 18.1 is κ∞(S), not κ∞(X). -/
structure JordanFormSpec (n : ℕ) (hn : 0 < n)
    (A X X_inv : Fin n → Fin n → ℝ) where
  inv_right : IsRightInverse n X X_inv
  spectral_radius : ℝ
  hr_nonneg : 0 ≤ spectral_radius
  hr_lt_one : spectral_radius < 1
  max_block_size : ℕ
  ht_pos : 0 < max_block_size
  /-- ASSUMED AXIOM (see the structure docstring): under the Higham–Knight
      condition there exists a perturbation-absorbing similarity `S`.  This is
      the undischarged crux of Theorem 18.1 (the `S = X P(ε)` δ-scaling
      construction), not a proved fact. -/
  similarity_absorbs :
    ∀ (η : ℝ), 0 ≤ η →
    4 * max_block_size * η * (infNorm X * infNorm X_inv) *
      infNorm A < (1 - spectral_radius) ^ max_block_size →
    ∃ S S_inv : Fin n → Fin n → ℝ,
    ∃ q : ℝ,
      IsRightInverse n S S_inv ∧
      0 ≤ q ∧ q < 1 ∧
      (∀ ΔA : Fin n → Fin n → ℝ,
        (∀ i j, |ΔA i j| ≤ η * |A i j|) →
        infNorm (matMul n S_inv
          (matMul n (fun i j => A i j + ΔA i j) S)) ≤ q)







































-- ============================================================
-- §18.2  Limit form of the convergence conclusion
-- ============================================================
























-- ============================================================
-- §18.2  End-to-end conditional forms with the limit conclusion
-- ============================================================






























































-- ============================================================
-- §18.2  Discharging `similarity_absorbs`: real-diagonalizable case (t = 1)
-- ============================================================































/-- A diagonal matrix with entries of modulus at most `ρ ≥ 0` has
    ∞-norm at most `ρ`. -/
theorem infNorm_diagonal_le {n : ℕ} (J : Fin n → Fin n → ℝ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hlam : ∀ i, |J i i| ≤ ρ) : infNorm J ≤ ρ := by
  apply infNorm_le_of_row_sum_le
  · intro i
    have hsingle : ∑ j : Fin n, |J i j| = |J i i| := by
      refine Finset.sum_eq_single i (fun b _ hb => ?_) (fun h => ?_)
      · rw [hdiag i b (Ne.symm hb)]; exact abs_zero
      · exact absurd (Finset.mem_univ i) h
    rw [hsingle]; exact hlam i
  · exact hρ0

/-- **Discharged `t = 1` construction (real-diagonalizable case).**

    If `A` is explicitly diagonalized over ℝ — `X⁻¹AX = J` with `J` diagonal
    and `|J i i| ≤ ρ < 1` — then the perturbation-absorbing similarity of
    Theorem 18.1's proof exists with `S = X` and NO scaling construction:
    for `|ΔA| ≤ η|A|`,
      `‖X⁻¹(A+ΔA)X‖∞ ≤ ‖J‖∞ + κ∞(X)·η·‖A‖∞ ≤ ρ + η·κ∞(X)·‖A‖∞ < 1`
    under the `t = 1` Higham–Knight condition `4·η·κ∞(X)·‖A‖∞ < 1 − ρ`.

    This PROVES `similarity_absorbs` (no assumption) for this class, covering
    e.g. symmetric matrices and any real matrix with real eigenvalues and a
    full real eigenbasis.  Here `ρ` is any bound on the eigenvalue moduli
    (the printed theorem uses `ρ(A)` itself, which is the sharpest choice).
    The general case (complex spectrum / defective `A`, `t > 1`) still
    requires the Jordan δ-scaling over ℂ and remains an open obligation. -/
def JordanFormSpec.ofRealDiagonal (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hlam : ∀ i, |J i i| ≤ ρ) :
    JordanFormSpec n hn A X X_inv where
  inv_right := hXr
  spectral_radius := ρ
  hr_nonneg := hρ0
  hr_lt_one := hρ1
  max_block_size := 1
  ht_pos := one_pos
  similarity_absorbs := by
    intro η hη hcond
    -- The t = 1 condition: 4·η·κ∞(X)·‖A‖∞ < 1 − ρ.
    have hcond' : 4 * (η * (infNorm X * infNorm X_inv) * infNorm A) < 1 - ρ := by
      have := hcond
      simpa [mul_assoc, Nat.cast_one] using this
    set K : ℝ := η * (infNorm X * infNorm X_inv) * infNorm A with hK
    have hK0 : 0 ≤ K := by
      apply mul_nonneg (mul_nonneg hη _) (infNorm_nonneg A)
      exact mul_nonneg (infNorm_nonneg X) (infNorm_nonneg X_inv)
    have hKlt : K < 1 - ρ := by linarith
    refine ⟨X, X_inv, ρ + K, hXr, by linarith, by linarith, ?_⟩
    intro ΔA hΔ
    -- X⁻¹(A+ΔA)X = J + X⁻¹ΔA X, entrywise.
    have hsplit : matMul n X_inv (matMul n (fun i j => A i j + ΔA i j) X) =
        fun i j => J i j + matMul n X_inv (matMul n ΔA X) i j := by
      rw [matMul_add_left n A ΔA X, matMul_add_right n X_inv
        (matMul n A X) (matMul n ΔA X), hsim]
    rw [hsplit]
    -- ‖X⁻¹ΔA X‖∞ ≤ κ∞(X)·η·‖A‖∞
    have hΔnorm : infNorm ΔA ≤ η * infNorm A :=
      infNorm_le_mul_of_abs_le_mul_abs ΔA A hη hΔ
    have h1 : infNorm (matMul n ΔA X) ≤ infNorm ΔA * infNorm X :=
      infNorm_matMul_le hn ΔA X
    have h2 : infNorm (matMul n X_inv (matMul n ΔA X)) ≤
        infNorm X_inv * (infNorm ΔA * infNorm X) :=
      (infNorm_matMul_le hn X_inv (matMul n ΔA X)).trans
        (mul_le_mul_of_nonneg_left h1 (infNorm_nonneg X_inv))
    have h3 : infNorm X_inv * (infNorm ΔA * infNorm X) ≤
        infNorm X_inv * ((η * infNorm A) * infNorm X) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hΔnorm (infNorm_nonneg X))
        (infNorm_nonneg X_inv)
    have hEq : infNorm X_inv * ((η * infNorm A) * infNorm X) = K := by
      rw [hK]; ring
    calc infNorm (fun i j => J i j + matMul n X_inv (matMul n ΔA X) i j)
        ≤ infNorm J + infNorm (matMul n X_inv (matMul n ΔA X)) :=
          infNorm_add_le J _
      _ ≤ ρ + K := by
          have hJn : infNorm J ≤ ρ := infNorm_diagonal_le J hρ0 hdiag hlam
          have := h2.trans h3
          rw [hEq] at this
          linarith













































-- ============================================================
-- §18.1  Exact arithmetic: eq (18.4), real-diagonalizable case
-- ============================================================

/-- Powers of a diagonal matrix are diagonal with powered entries. -/
theorem matPow_diagonal (n : ℕ) (J : Fin n → Fin n → ℝ)
    (hdiag : ∀ i j, i ≠ j → J i j = 0) (k : ℕ) :
    ∀ i j, matPow n J k i j = if i = j then (J i i) ^ k else 0 := by
  induction k with
  | zero =>
    intro i j
    show idMatrix n i j = _
    unfold idMatrix
    simp [pow_zero]
  | succ k ih =>
    intro i j
    show matMul n J (matPow n J k) i j = _
    unfold matMul
    rw [Finset.sum_eq_single i
      (fun l _ hl => by rw [hdiag i l (Ne.symm hl), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [ih i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, pow_succ]; ring
    · rw [if_neg hij, if_neg hij, mul_zero]

/-- Similarity transport of matrix powers: if `X⁻¹AX = J` with two-sided
    inverse data, then `Aᵏ = X Jᵏ X⁻¹`. -/
theorem matPow_similarity (n : ℕ)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n A X) = J) (k : ℕ) :
    matPow n A k = matMul n X (matMul n (matPow n J k) X_inv) := by
  have hXXinv : matMul n X X_inv = idMatrix n := by ext a b; exact hXr a b
  have hXinvX : matMul n X_inv X = idMatrix n := by ext a b; exact hXl a b
  have hA : A = matMul n X (matMul n J X_inv) := by
    calc A = matMul n (matMul n X X_inv)
              (matMul n A (matMul n X X_inv)) := by
            rw [hXXinv, matMul_id_left, matMul_id_right]
      _ = matMul n X (matMul n (matMul n X_inv (matMul n A X)) X_inv) := by
            simp only [matMul_assoc]
      _ = matMul n X (matMul n J X_inv) := by rw [hsim]
  induction k with
  | zero =>
    show idMatrix n = _
    have : matMul n (matPow n J 0) X_inv = X_inv := by
      show matMul n (idMatrix n) X_inv = X_inv
      exact matMul_id_left n X_inv
    rw [this, hXXinv]
  | succ k ih =>
    rw [matPow_succ n A k, ih, matPow_succ n J k]
    nth_rewrite 1 [hA]
    simp only [matMul_assoc]
    congr 1
    congr 1
    rw [← matMul_assoc, hXinvX, matMul_id_left]























































































































-- ============================================================
-- §18.2  Eq (18.12): weighted (Collatz–Wielandt) certificate form
-- ============================================================





































































































































end NumStability
