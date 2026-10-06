import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.Complex
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.VectorNorms.Basic

/-!
# Analysis.LinearOperators.MatrixPowers.LpBounds.ComplexDiagonal

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

/-- Complex identity matrix on `Fin n`.  Neither `Analysis/MatrixNorms/Basic.lean` nor
    `Algorithms/MatrixPowersComplex.lean` defines one (checked by search), so
    it is introduced here as the complex counterpart of `idMatrix`
    (Analysis/MatrixAlgebra.lean ~70). -/
noncomputable def cIdMatrix (n : ℕ) : CMatrix n n :=
  fun i j => if i = j then 1 else 0

/-- The complex identity matrix acts as the identity on vectors. -/
theorem cIdMatrix_vecMul {n : ℕ} (x : CVec n) :
    complexMatrixVecMul (cIdMatrix n) x = x := by
  funext i
  unfold complexMatrixVecMul cIdMatrix
  simp [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]

/-- Left multiplication by the complex identity: `I · A = A`. -/
theorem complexMatrixMul_cIdMatrix_left {n : ℕ} (A : CMatrix n n) :
    complexMatrixMul (cIdMatrix n) A = A := by
  funext i j
  unfold complexMatrixMul cIdMatrix
  simp [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]

/-- Right multiplication by the complex identity: `A · I = A`. -/
theorem complexMatrixMul_cIdMatrix_right {n : ℕ} (A : CMatrix n n) :
    complexMatrixMul A (cIdMatrix n) = A := by
  funext i j
  unfold complexMatrixMul cIdMatrix
  simp [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]

/-- Bridge from the repo's vector-action right-inverse predicate
    (`IsComplexMatrixRightInverse`, `Analysis/MatrixNorms/Basic.lean`) to the matrix-level
    identity `A · A⁻¹ = I`, obtained by applying the action to the coordinate
    basis vectors. -/
theorem complexMatrixMul_eq_cIdMatrix_of_rightInverse {n : ℕ}
    {A Ainv : CMatrix n n} (h : IsComplexMatrixRightInverse A Ainv) :
    complexMatrixMul A Ainv = cIdMatrix n := by
  funext i j
  have hcol : complexMatrixVecMul Ainv (fun l => if l = j then (1 : ℂ) else 0) =
      fun k => Ainv k j := by
    funext k
    unfold complexMatrixVecMul
    simp [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  have happ := congrFun (h (fun l => if l = j then (1 : ℂ) else 0)) i
  rw [hcol] at happ
  calc complexMatrixMul A Ainv i j
      = complexMatrixVecMul A (fun k => Ainv k j) i := rfl
    _ = (if i = j then (1 : ℂ) else 0) := happ
    _ = cIdMatrix n i j := rfl

/-- **Complex matrix power** `M^k` by recursion via `complexMatrixMul`, the
    complex counterpart of `matPow` (Analysis/MatrixAlgebra.lean ~398).  This
    is the `A^k` of Higham 2nd ed., §18.1, p. 343. -/
noncomputable def cMatPow (n : ℕ) (M : CMatrix n n) : ℕ → CMatrix n n
  | 0 => cIdMatrix n
  | k + 1 => complexMatrixMul M (cMatPow n M k)

/-- `M^0 = I` over ℂ. -/
theorem cMatPow_zero (n : ℕ) (M : CMatrix n n) :
    cMatPow n M 0 = cIdMatrix n := rfl

/-- `M^(k+1) = M · M^k` over ℂ. -/
theorem cMatPow_succ (n : ℕ) (M : CMatrix n n) (k : ℕ) :
    cMatPow n M (k + 1) = complexMatrixMul M (cMatPow n M k) := rfl

-- ============================================================
-- Entrywise domination for the finite complex L^p vector norm
-- ============================================================

/-- **Entrywise domination for the finite complex `L^p` norm** (workhorse for
    the diagonal-factor estimate in eq (18.4), Higham 2nd ed., §18.1, p. 343):
    if `‖y i‖ ≤ c · ‖x i‖` in every coordinate with `0 ≤ c`, then
    `‖y‖_p ≤ c · ‖x‖_p` for every real exponent `1 ≤ p < ∞`.

    Built on the repo's monotonicity theorem
    `complexVecLpNorm_ofReal_monotone` (`Analysis/VectorNorms/Basic.lean`, itself Higham
    Theorem 6.2) and the norm axioms `complexVecLpNorm_isComplexVectorNorm`
    (also in `Analysis/VectorNorms/Basic.lean`); no equivalent single-lemma form was found by search. -/
theorem complexVecLpNorm_le_mul_of_forall_norm_le {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    {y x : CVec n} {c : ℝ}
    (h : ∀ i, ‖y i‖ ≤ c * ‖x i‖) (hc : 0 ≤ c) :
    complexVecLpNorm (ENNReal.ofReal p) y ≤
      c * complexVecLpNorm (ENNReal.ofReal p) x := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have hν : IsComplexVectorNorm (complexVecLpNorm (n := n) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hmono := complexVecLpNorm_ofReal_monotone (n := n) hp
  have hle : componentwiseAbsLe y (complexVecSMul (c : ℂ) x) := by
    intro i
    have hnorm : ‖complexVecSMul (c : ℂ) x i‖ = c * ‖x i‖ := by
      show ‖(c : ℂ) * x i‖ = c * ‖x i‖
      rw [norm_mul, Complex.norm_of_nonneg hc]
    rw [hnorm]
    exact h i
  calc complexVecLpNorm (ENNReal.ofReal p) y
      ≤ complexVecLpNorm (ENNReal.ofReal p) (complexVecSMul (c : ℂ) x) :=
        hmono _ _ hle
    _ = ‖(c : ℂ)‖ * complexVecLpNorm (ENNReal.ofReal p) x := hν.smul _ _
    _ = c * complexVecLpNorm (ENNReal.ofReal p) x := by
        rw [Complex.norm_of_nonneg hc]

-- ============================================================
-- Diagonal complex matrices in the subordinate L^p norm
-- ============================================================

/-- **Diagonal matrix `p`-norm bound predicate form** (Higham 2nd ed., §18.1,
    p. 343, the `‖D‖_p ≤ max |d_i|` step of eq (18.4)): an entrywise bound
    `‖d i‖ ≤ c` on the diagonal gives the subordinate upper-bound predicate
    `HasComplexMatrixLpBound` at every real exponent `1 ≤ p < ∞`. -/
theorem hasComplexMatrixLpBound_diagonal {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (d : Fin n → ℂ) {c : ℝ} (hc : 0 ≤ c) (hd : ∀ i, ‖d i‖ ≤ c) :
    HasComplexMatrixLpBound (ENNReal.ofReal p) (cDiagMatrix d) c := by
  refine ⟨hc, ?_⟩
  intro x
  rw [cDiagMatrix_vecMul]
  refine complexVecLpNorm_le_mul_of_forall_norm_le hp (fun i => ?_) hc
  show ‖d i * x i‖ ≤ c * ‖x i‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hd i) (norm_nonneg _)

/-- **Diagonal matrix `p`-norm bound, norm-function form** (Higham 2nd ed.,
    §18.1, p. 343): `‖diag d‖_p ≤ c` whenever `‖d i‖ ≤ c` with `0 ≤ c`, for
    every real exponent `1 ≤ p < ∞`.  Only the upper direction is needed for
    eq (18.4). -/
theorem complexMatrixLpNormOfReal_diagonal_le {n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp : 1 ≤ p) (d : Fin n → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (hd : ∀ i, ‖d i‖ ≤ c) :
    complexMatrixLpNormOfReal hn p hp (cDiagMatrix d) ≤ c :=
  isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue hn p hp (cDiagMatrix d))
    (hasComplexMatrixLpBound_diagonal hp d hc hd)

-- ============================================================
-- Powers of diagonal matrices and similarity transport over ℂ
-- ============================================================

/-- **Powers of a diagonal complex matrix are diagonal with powered entries**
    (Higham 2nd ed., §18.1, p. 343, the `J^k = diag(λ_i^k)` step of eq (18.4)).
    Complex transport of `matPow_diagonal` (Algorithms/MatrixPowers.lean ~774). -/
theorem cMatPow_diagonal (n : ℕ) (J : CMatrix n n)
    (hdiag : ∀ i j, i ≠ j → J i j = 0) (k : ℕ) :
    ∀ i j, cMatPow n J k i j = if i = j then (J i i) ^ k else 0 := by
  induction k with
  | zero =>
    intro i j
    show cIdMatrix n i j = _
    unfold cIdMatrix
    simp [pow_zero]
  | succ k ih =>
    intro i j
    show complexMatrixMul J (cMatPow n J k) i j = _
    unfold complexMatrixMul
    rw [Finset.sum_eq_single i
      (fun l _ hl => by rw [hdiag i l (Ne.symm hl), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [ih i j]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij, pow_succ]
      ring
    · rw [if_neg hij, if_neg hij, mul_zero]

/-- Function-level repackaging of `cMatPow_diagonal` through the reused
    `cDiagMatrix` wrapper (Algorithms/MatrixPowersComplex.lean ~366), so the
    diagonal `p`-norm bound applies directly. -/
theorem cMatPow_diagonal_eq_cDiagMatrix (n : ℕ) (J : CMatrix n n)
    (hdiag : ∀ i j, i ≠ j → J i j = 0) (k : ℕ) :
    cMatPow n J k = cDiagMatrix (fun i => (J i i) ^ k) := by
  funext i j
  rw [cMatPow_diagonal n J hdiag k i j]
  rfl

/-- **Similarity transport of complex matrix powers** (Higham 2nd ed., §18.1,
    p. 343, the `A^k = X J^k X⁻¹` step of eq (18.4)): if `X⁻¹ A X = J` with
    two-sided inverse action data, then `A^k = X · J^k · X⁻¹`.  Complex
    transport of `matPow_similarity` (Algorithms/MatrixPowers.lean ~797). -/
theorem cMatPow_similarity (n : ℕ)
    (A X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hXl : IsComplexMatrixRightInverse X_inv X)
    (hsim : complexMatrixMul X_inv (complexMatrixMul A X) = J) (k : ℕ) :
    cMatPow n A k =
      complexMatrixMul X (complexMatrixMul (cMatPow n J k) X_inv) := by
  have hXXinv : complexMatrixMul X X_inv = cIdMatrix n :=
    complexMatrixMul_eq_cIdMatrix_of_rightInverse hXr
  have hXinvX : complexMatrixMul X_inv X = cIdMatrix n :=
    complexMatrixMul_eq_cIdMatrix_of_rightInverse hXl
  have hA : A = complexMatrixMul X (complexMatrixMul J X_inv) := by
    calc A = complexMatrixMul (complexMatrixMul X X_inv)
              (complexMatrixMul A (complexMatrixMul X X_inv)) := by
            rw [hXXinv, complexMatrixMul_cIdMatrix_left,
              complexMatrixMul_cIdMatrix_right]
      _ = complexMatrixMul X (complexMatrixMul
            (complexMatrixMul X_inv (complexMatrixMul A X)) X_inv) := by
            simp only [complexMatrixMul_assoc]
      _ = complexMatrixMul X (complexMatrixMul J X_inv) := by rw [hsim]
  induction k with
  | zero =>
    show cIdMatrix n = _
    have h0 : complexMatrixMul (cMatPow n J 0) X_inv = X_inv := by
      show complexMatrixMul (cIdMatrix n) X_inv = X_inv
      exact complexMatrixMul_cIdMatrix_left X_inv
    rw [h0, hXXinv]
  | succ k ih =>
    rw [cMatPow_succ n A k, ih, cMatPow_succ n J k]
    nth_rewrite 1 [hA]
    simp only [complexMatrixMul_assoc]
    congr 1
    congr 1
    rw [← complexMatrixMul_assoc, hXinvX, complexMatrixMul_cIdMatrix_left]

-- ============================================================
-- Eq (18.4): upper and lower bounds at every real exponent 1 ≤ p < ∞
-- ============================================================


















































































































































































end NumStability
