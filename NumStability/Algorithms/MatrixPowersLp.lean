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
--   `CVec`, `CMatrix`, `complexVecLpNorm`      — Analysis/Norms.lean (~47, ~98)
--   `complexVecLpNorm_isComplexVectorNorm`     — Norms.lean ~486
--   `complexVecLpNorm_ofReal_monotone`         — Norms.lean ~821
--   `complexMatrixMul`, `complexMatrixVecMul`, `complexMatrixMul_assoc`,
--   `complexMatrixVecMul_mul`, `IsComplexMatrixRightInverse`
--                                              — Norms.lean ~3022–3177
--   `IsComplexMatrixLpNormValue`, `HasComplexMatrixLpBound`,
--   `hasComplexMatrixLpBound_apply`            — Norms.lean ~4201, ~5131
--   `isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound`
--                                              — Norms.lean ~7162
--   `complexMatrixLpNormOfReal` (+ value/eq/mul_le lemmas)
--                                              — Norms.lean ~8444–8560
--   `cDiagMatrix`, `cDiagMatrix_vecMul`        — Algorithms/MatrixPowersComplex.lean ~366
-- The real-case proof skeletons mirrored here are `matPow_diagonal`,
-- `matPow_similarity`, `higham_eq_18_4_upper_real_diagonalizable`,
-- `higham_eq_18_4_lower_real_diagonalizable` in Algorithms/MatrixPowers.lean.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import NumStability.Analysis.Norms
import NumStability.Algorithms.MatrixPowersComplex

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Complex identity matrix and complex matrix powers
-- ============================================================

/-- Complex identity matrix on `Fin n`.  Neither `Analysis/Norms.lean` nor
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
    (`IsComplexMatrixRightInverse`, Norms.lean ~3033) to the matrix-level
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
    `complexVecLpNorm_ofReal_monotone` (Norms.lean ~821, itself Higham
    Theorem 6.2) and the norm axioms `complexVecLpNorm_isComplexVectorNorm`
    (Norms.lean ~486); no equivalent single-lemma form was found by search. -/
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
