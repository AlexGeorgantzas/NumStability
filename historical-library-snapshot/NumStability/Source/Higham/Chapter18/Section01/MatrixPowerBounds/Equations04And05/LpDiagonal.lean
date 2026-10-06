import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.Complex
import NumStability.Analysis.LinearOperators.MatrixPowers.LpBounds.ComplexDiagonal
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.VectorNorms.Basic

/-!
# Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.LpDiagonal

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/MatrixPowersLp.lean
--
-- Higham Chapter 18: exact-arithmetic power bounds of §18.1, eq (18.4),
-- p. 343, at every finite real p-norm exponent over ℂ:
--
--   ρ(A)^k  ≤  ‖A^k‖_p  ≤  κ_p(X) · ρ(A)^k     (A = X J X⁻¹ diagonalizable)
--
-- for `A : CMatrix n n` complex diagonalizable, where `‖·‖_p` is the repo's
-- subordinate complex matrix `L^p` norm `complexMatrixLpNormOfReal` at a real
-- exponent `1 ≤ p < ∞` (i.e. `ENNReal.ofReal p`), and `κ_p(X) = ‖X‖_p·‖X⁻¹‖_p`.
--
-- Honest scope: the printed (18.4) reads "for any p-norm"; this file closes
-- every finite real exponent `1 ≤ p < ∞` for complex diagonalizable data.
-- The `p = ∞` real-spectrum subcase is closed separately in
-- `MatrixPowers.lean` (`higham_eq_18_4_upper_real_diagonalizable`,
-- `higham_eq_18_4_lower_real_diagonalizable`).
--
-- Infrastructure REUSED (source traceability):
--   `CVec`, `complexVecLpNorm`, its norm proof and monotonicity
--                                              — Analysis/VectorNorms/Basic.lean
--   `CMatrix`, matrix multiplication/action, and right inverses
--                                              — Analysis/MatrixNorms/Basic.lean
--   `complexMatrixMul`, `complexMatrixVecMul`, `complexMatrixMul_assoc`,
--   `complexMatrixVecMul_mul`, `IsComplexMatrixRightInverse`
--                                              — Analysis/MatrixNorms/Basic.lean
--   `IsComplexMatrixLpNormValue`, `HasComplexMatrixLpBound`,
--   `hasComplexMatrixLpBound_apply`            — Analysis/MatrixNorms/Lp.lean
--   `isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound`
--                                              — Analysis/MatrixNorms/Lp.lean
--   `complexMatrixLpNormOfReal` (+ value/eq/mul_le lemmas)
--                                              — Analysis/MatrixNorms/Lp.lean
--   `cDiagMatrix`, `cDiagMatrix_vecMul`        — Algorithms/MatrixPowersComplex.lean ~366
-- The real-case proof skeletons mirrored here are `matPow_diagonal`,
-- `matPow_similarity`, `higham_eq_18_4_upper_real_diagonalizable`,
-- `higham_eq_18_4_lower_real_diagonalizable` in Algorithms/MatrixPowers.lean.







namespace NumStability

open scoped BigOperators

-- ============================================================
-- Complex identity matrix and complex matrix powers
-- ============================================================
































































-- ============================================================
-- Entrywise domination for the finite complex L^p vector norm
-- ============================================================



































-- ============================================================
-- Diagonal complex matrices in the subordinate L^p norm
-- ============================================================




























-- ============================================================
-- Powers of diagonal matrices and similarity transport over ℂ
-- ============================================================











































































-- ============================================================
-- Eq (18.4): upper and lower bounds at every real exponent 1 ≤ p < ∞
-- ============================================================

/-- **Higham 2nd ed., §18.1, eq (18.4), p. 343 — upper bound at every real
    exponent `1 ≤ p < ∞` for complex diagonalizable data**:
    if `X⁻¹ A X = J` is diagonal with `‖J i i‖ ≤ ρ`, then
    `‖A^k‖_p ≤ κ_p(X) · ρ^k` where `κ_p(X) = ‖X‖_p · ‖X⁻¹‖_p`.

    Honest scope: the exponent is a real `p` with `1 ≤ p`, embedded as
    `ENNReal.ofReal p`, so this covers the printed "any p-norm" for
    `1 ≤ p < ∞`; the `p = ∞` case is closed separately
    (`higham_eq_18_4_upper_real_diagonalizable`, Algorithms/MatrixPowers.lean).
    Taking the dominant eigenvalue `ρ = ρ(A)` recovers the printed statement. -/
theorem higham_eq_18_4_upper_lp_diagonalizable (n : ℕ) (hn : 0 < n)
    (A X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hXl : IsComplexMatrixRightInverse X_inv X)
    (hsim : complexMatrixMul X_inv (complexMatrixMul A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (ρ : ℝ) (hlam : ∀ i, ‖J i i‖ ≤ ρ) (hρ0 : 0 ≤ ρ)
    (p : ℝ) (hp : 1 ≤ p) (k : ℕ) :
    complexMatrixLpNormOfReal hn p hp (cMatPow n A k) ≤
      (complexMatrixLpNormOfReal hn p hp X *
        complexMatrixLpNormOfReal hn p hp X_inv) * ρ ^ k := by
  have hnonneg : ∀ M : CMatrix n n, 0 ≤ complexMatrixLpNormOfReal hn p hp M :=
    fun M => (hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal hn hp
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue hn p hp M)).1
  rw [cMatPow_similarity n A X X_inv J hXr hXl hsim k]
  have hJk : complexMatrixLpNormOfReal hn p hp (cMatPow n J k) ≤ ρ ^ k := by
    rw [cMatPow_diagonal_eq_cDiagMatrix n J hdiag k]
    refine complexMatrixLpNormOfReal_diagonal_le hn p hp _
      (pow_nonneg hρ0 k) (fun i => ?_)
    show ‖(J i i) ^ k‖ ≤ ρ ^ k
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hlam i) k
  calc complexMatrixLpNormOfReal hn p hp
        (complexMatrixMul X (complexMatrixMul (cMatPow n J k) X_inv))
      ≤ complexMatrixLpNormOfReal hn p hp X *
          complexMatrixLpNormOfReal hn p hp
            (complexMatrixMul (cMatPow n J k) X_inv) :=
        complexMatrixLpNormOfReal_mul_le hn hn hp X _
    _ ≤ complexMatrixLpNormOfReal hn p hp X *
          (complexMatrixLpNormOfReal hn p hp (cMatPow n J k) *
            complexMatrixLpNormOfReal hn p hp X_inv) :=
        mul_le_mul_of_nonneg_left
          (complexMatrixLpNormOfReal_mul_le hn hn hp _ X_inv)
          (hnonneg X)
    _ ≤ complexMatrixLpNormOfReal hn p hp X *
          (ρ ^ k * complexMatrixLpNormOfReal hn p hp X_inv) := by
        refine mul_le_mul_of_nonneg_left ?_ (hnonneg X)
        exact mul_le_mul_of_nonneg_right hJk (hnonneg X_inv)
    _ = (complexMatrixLpNormOfReal hn p hp X *
          complexMatrixLpNormOfReal hn p hp X_inv) * ρ ^ k := by ring

/-- **Higham 2nd ed., §18.1, eq (18.4), p. 343 — lower bound at every real
    exponent `1 ≤ p < ∞` for complex diagonalizable data**: every eigenvalue
    modulus power is a lower bound, `‖J j j‖^k ≤ ‖A^k‖_p`; taking the dominant
    `j` gives the printed `ρ(A)^k ≤ ‖A^k‖_p` for `1 ≤ p < ∞`.

    Proof by the eigencolumn argument: column `j` of `X` is an eigenvector of
    `A` for `J j j` (from `hsim` and the inverse action data), it is nonzero
    because `X⁻¹ X = I`, and the subordinate norm-value predicate bounds
    `‖A^k x‖_p ≤ ‖A^k‖_p · ‖x‖_p`.  The `p = ∞` real-spectrum subcase is
    closed separately (`higham_eq_18_4_lower_real_diagonalizable`,
    Algorithms/MatrixPowers.lean). -/
theorem higham_eq_18_4_lower_lp_diagonalizable (n : ℕ) (hn : 0 < n)
    (A X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hXl : IsComplexMatrixRightInverse X_inv X)
    (hsim : complexMatrixMul X_inv (complexMatrixMul A X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (p : ℝ) (hp : 1 ≤ p) (j : Fin n) (k : ℕ) :
    ‖J j j‖ ^ k ≤ complexMatrixLpNormOfReal hn p hp (cMatPow n A k) := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have hν : IsComplexVectorNorm (complexVecLpNorm (n := n) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hXXinv : complexMatrixMul X X_inv = cIdMatrix n :=
    complexMatrixMul_eq_cIdMatrix_of_rightInverse hXr
  have hXinvX : complexMatrixMul X_inv X = cIdMatrix n :=
    complexMatrixMul_eq_cIdMatrix_of_rightInverse hXl
  -- Eigencolumn: x := column j of X, so A·X = X·J gives (A^k x)_i = (J j j)^k x_i.
  set x : CVec n := fun i => X i j with hxdef
  have hAX : complexMatrixMul A X = complexMatrixMul X J := by
    have h := congrArg (complexMatrixMul X) hsim
    rwa [← complexMatrixMul_assoc, hXXinv,
      complexMatrixMul_cIdMatrix_left] at h
  -- one-step eigen action
  have hstep : ∀ i, complexMatrixVecMul A x i = J j j * x i := by
    intro i
    have h1 : complexMatrixVecMul A x i = complexMatrixMul A X i j := by
      unfold complexMatrixVecMul complexMatrixMul
      rfl
    have h2 : complexMatrixMul X J i j = J j j * x i := by
      unfold complexMatrixMul
      rw [Finset.sum_eq_single j
        (fun l _ hl => by rw [hdiag l j hl, mul_zero])
        (fun h => absurd (Finset.mem_univ j) h)]
      rw [hxdef]
      ring
    rw [h1, hAX, h2]
  -- k-step eigen action
  have hact : ∀ m, ∀ i,
      complexMatrixVecMul (cMatPow n A m) x i = (J j j) ^ m * x i := by
    intro m
    induction m with
    | zero =>
      intro i
      show complexMatrixVecMul (cIdMatrix n) x i = _
      rw [cIdMatrix_vecMul, pow_zero, one_mul]
    | succ m ih =>
      intro i
      have h1 : complexMatrixVecMul (cMatPow n A (m + 1)) x i =
          complexMatrixVecMul A (complexMatrixVecMul (cMatPow n A m) x) i := by
        rw [cMatPow_succ n A m, complexMatrixVecMul_mul]
      have h2 : complexMatrixVecMul (cMatPow n A m) x =
          (fun l => (J j j) ^ m * x l) := funext ih
      have h3 : complexMatrixVecMul A (fun l => (J j j) ^ m * x l) i =
          (J j j) ^ m * complexMatrixVecMul A x i := by
        unfold complexMatrixVecMul
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by ring)
      rw [h1, h2, h3, hstep i, pow_succ]
      ring
  -- x has a nonzero entry (X_inv·X = I)
  have hone : (∑ l : Fin n, X_inv j l * X l j) = (1 : ℂ) := by
    have h : complexMatrixMul X_inv X j j = cIdMatrix n j j := by rw [hXinvX]
    have h1 : complexMatrixMul X_inv X j j =
        ∑ l : Fin n, X_inv j l * X l j := rfl
    have h2 : cIdMatrix n j j = 1 := by
      unfold cIdMatrix
      rw [if_pos rfl]
    rw [h1, h2] at h
    exact h
  have hxne : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    have hzero : (∑ l : Fin n, X_inv j l * X l j) = 0 :=
      Finset.sum_eq_zero (fun l _ => by
        have hxl : X l j = 0 := h l
        rw [hxl, mul_zero])
    rw [hzero] at hone
    exact one_ne_zero hone.symm
  have hx0 : x ≠ 0 := by
    obtain ⟨i₁, hi₁⟩ := hxne
    intro h0
    apply hi₁
    rw [h0]
    rfl
  have hxpos : 0 < complexVecLpNorm (ENNReal.ofReal p) x := by
    rcases lt_or_eq_of_le (hν.nonneg x) with hlt | heq
    · exact hlt
    · exact absurd ((hν.eq_zero_iff x).mp heq.symm) hx0
  -- subordinate-value bound ‖A^k x‖_p ≤ ‖A^k‖_p · ‖x‖_p and the norm chain
  have hbound : HasComplexMatrixLpBound (ENNReal.ofReal p) (cMatPow n A k)
      (complexMatrixLpNormOfReal hn p hp (cMatPow n A k)) :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal hn hp
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue hn p hp
        (cMatPow n A k))
  have hfun : complexVecSMul ((J j j) ^ k) x =
      complexMatrixVecMul (cMatPow n A k) x := by
    funext i
    show (J j j) ^ k * x i = _
    exact (hact k i).symm
  have hchain : ‖J j j‖ ^ k * complexVecLpNorm (ENNReal.ofReal p) x ≤
      complexMatrixLpNormOfReal hn p hp (cMatPow n A k) *
        complexVecLpNorm (ENNReal.ofReal p) x := by
    calc ‖J j j‖ ^ k * complexVecLpNorm (ENNReal.ofReal p) x
        = ‖(J j j) ^ k‖ * complexVecLpNorm (ENNReal.ofReal p) x := by
          rw [norm_pow]
      _ = complexVecLpNorm (ENNReal.ofReal p)
            (complexVecSMul ((J j j) ^ k) x) := (hν.smul _ x).symm
      _ = complexVecLpNorm (ENNReal.ofReal p)
            (complexMatrixVecMul (cMatPow n A k) x) := by rw [hfun]
      _ ≤ complexMatrixLpNormOfReal hn p hp (cMatPow n A k) *
            complexVecLpNorm (ENNReal.ofReal p) x :=
          hasComplexMatrixLpBound_apply hbound x
  exact le_of_mul_le_mul_right hchain hxpos

end NumStability
