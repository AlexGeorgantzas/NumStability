import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding

/-!
# Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.RealDiagonal

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


































































































































































-- ============================================================
-- §18.1  Exact arithmetic: eq (18.4), real-diagonalizable case
-- ============================================================






















































/-- **Eq (18.4), upper bound, real-diagonalizable ∞-norm case**
    (Higham 2nd ed., §18.1, p. 343): if `X⁻¹AX = J` is diagonal with
    `|J i i| ≤ ρ`, then `‖Aᵏ‖∞ ≤ κ∞(X) · ρᵏ`.

    Honest scope: the printed (18.4) is stated for every p-norm and complex
    diagonalizable `A`; this closes the `p = ∞`, real-spectrum subcase. -/
theorem higham_eq_18_4_upper_real_diagonalizable (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hlam : ∀ i, |J i i| ≤ ρ) (k : ℕ) :
    infNorm (matPow n A k) ≤ (infNorm X * infNorm X_inv) * ρ ^ k := by
  rw [matPow_similarity n A X X_inv J hXr hXl hsim k]
  have hJk : infNorm (matPow n J k) ≤ ρ ^ k := by
    refine infNorm_diagonal_le _ (pow_nonneg hρ0 k)
      (fun i j hij => by rw [matPow_diagonal n J hdiag k i j, if_neg hij])
      (fun i => ?_)
    rw [matPow_diagonal n J hdiag k i i, if_pos rfl]
    calc |J i i ^ k| = |J i i| ^ k := abs_pow _ _
      _ ≤ ρ ^ k := pow_le_pow_left₀ (abs_nonneg _) (hlam i) k
  calc infNorm (matMul n X (matMul n (matPow n J k) X_inv))
      ≤ infNorm X * infNorm (matMul n (matPow n J k) X_inv) :=
        infNorm_matMul_le hn _ _
    _ ≤ infNorm X * (infNorm (matPow n J k) * infNorm X_inv) :=
        mul_le_mul_of_nonneg_left (infNorm_matMul_le hn _ _)
          (infNorm_nonneg X)
    _ ≤ infNorm X * (ρ ^ k * infNorm X_inv) := by
        apply mul_le_mul_of_nonneg_left _ (infNorm_nonneg X)
        exact mul_le_mul_of_nonneg_right hJk (infNorm_nonneg X_inv)
    _ = (infNorm X * infNorm X_inv) * ρ ^ k := by ring

/-- **Eq (18.4), lower bound, real-diagonalizable ∞-norm case**
    (Higham 2nd ed., §18.1, p. 343): every eigenvalue modulus power is a
    lower bound, `|J j j|ᵏ ≤ ‖Aᵏ‖∞`; taking the dominant `j` gives the
    printed `ρ(A)ᵏ ≤ ‖Aᵏ‖_p` for `p = ∞` and real spectrum. -/
theorem higham_eq_18_4_lower_real_diagonalizable (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (j : Fin n) (k : ℕ) :
    |J j j| ^ k ≤ infNorm (matPow n A k) := by
  have hXXinv : matMul n X X_inv = idMatrix n := by ext a b; exact hXr a b
  -- Eigencolumn: x := column j of X, so A·X = X·J gives (Aᵏx)ᵢ = (J j j)ᵏ xᵢ.
  set x : Fin n → ℝ := fun i => X i j with hxdef
  have hAX : matMul n A X = matMul n X J := by
    have h := congrArg (matMul n X) hsim
    rwa [← matMul_assoc, hXXinv, matMul_id_left] at h
  -- one-step eigen action
  have hstep : ∀ i, matMulVec n A x i = J j j * x i := by
    intro i
    have h1 : matMulVec n A x i = matMul n A X i j := by
      unfold matMulVec matMul; rfl
    have h2 : matMul n X J i j = J j j * x i := by
      unfold matMul
      rw [Finset.sum_eq_single j
        (fun l _ hl => by rw [hdiag l j hl, mul_zero])
        (fun h => absurd (Finset.mem_univ j) h)]
      rw [hxdef]; ring
    rw [h1, hAX, h2]
  -- k-step eigen action
  have hact : ∀ k, ∀ i, matMulVec n (matPow n A k) x i = (J j j) ^ k * x i := by
    intro k
    induction k with
    | zero =>
      intro i
      show matMulVec n (idMatrix n) x i = _
      unfold matMulVec idMatrix
      simp [Finset.sum_ite_eq, pow_zero]
    | succ k ih =>
      intro i
      have h1 : matMulVec n (matPow n A (k + 1)) x i =
          matMulVec n A (matMulVec n (matPow n A k) x) i := by
        rw [matPow_succ n A k]
        exact matMulVec_matMul n A (matPow n A k) x i
      have h2 : matMulVec n A (matMulVec n (matPow n A k) x) i =
          matMulVec n A (fun l => (J j j) ^ k * x l) i := by
        have hfun : matMulVec n (matPow n A k) x =
            (fun l => (J j j) ^ k * x l) := funext ih
        rw [hfun]
      have h3 : matMulVec n A (fun l => (J j j) ^ k * x l) i =
          (J j j) ^ k * matMulVec n A x i := by
        unfold matMulVec
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by ring)
      rw [h1, h2, h3, hstep i, pow_succ]; ring
  -- x has a nonzero entry (X is invertible)
  have hone : ∑ l : Fin n, X_inv j l * X l j = 1 := by
    have := hXl j j
    simpa using this
  have hxne : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    have : ∑ l : Fin n, X_inv j l * X l j = 0 :=
      Finset.sum_eq_zero (fun l _ => by
        have hxl : X l j = 0 := h l
        rw [hxl, mul_zero])
    rw [this] at hone
    exact one_ne_zero hone.symm
  have hxpos : 0 < infNormVec x := by
    obtain ⟨i₁, hi₁⟩ := hxne
    calc (0:ℝ) < |x i₁| := abs_pos.mpr hi₁
      _ ≤ infNormVec x := abs_le_infNormVec x i₁
  -- sup-attaining index and the norm chain
  obtain ⟨i₀, hi₀⟩ := infNormVec_exists_abs_eq hn x
  have hchain : |J j j| ^ k * infNormVec x ≤
      infNorm (matPow n A k) * infNormVec x := by
    calc |J j j| ^ k * infNormVec x
        = |J j j| ^ k * |x i₀| := by rw [hi₀]
      _ = |(J j j) ^ k * x i₀| := by rw [abs_mul, abs_pow]
      _ = |matMulVec n (matPow n A k) x i₀| := by rw [hact k i₀]
      _ ≤ infNormVec (matMulVec n (matPow n A k) x) :=
          abs_le_infNormVec _ i₀
      _ ≤ infNorm (matPow n A k) * infNormVec x :=
          infNormVec_matMulVec_le hn _ _
  exact le_of_mul_le_mul_right hchain hxpos

-- ============================================================
-- §18.2  Eq (18.12): weighted (Collatz–Wielandt) certificate form
-- ============================================================





































































































































end NumStability
