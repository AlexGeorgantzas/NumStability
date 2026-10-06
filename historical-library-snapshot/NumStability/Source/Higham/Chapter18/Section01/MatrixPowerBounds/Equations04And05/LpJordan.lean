import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.Complex
import NumStability.Analysis.LinearOperators.MatrixPowers.LpBounds.ComplexDiagonal
import NumStability.Analysis.LinearOperators.MatrixPowers.LpBounds.ComplexJordan
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.VectorNorms.Basic

/-!
# Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.LpJordan

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/MatrixPowersLpJordan.lean
--
-- Higham Chapter 18: exact-arithmetic power bound of §18.1, eq (18.5)
-- alternative form (p. 344, unnumbered display), at every finite real
-- p-norm exponent over ℂ for Jordan (possibly defective) data:
--
--   ‖A^k‖_p ≤ κ_p(X) · κ_p(D) · (ρ + β)^k     (A = X J X⁻¹, J bidiagonal)
--
-- for `A : CMatrix n n` with complex bidiagonal Jordan-form-like similarity
-- data, where `‖·‖_p` is the repo's subordinate complex matrix `L^p` norm
-- `complexMatrixLpNormOfReal` at a real exponent `1 ≤ p < ∞`,
-- `κ_p(X) = ‖X‖_p·‖X⁻¹‖_p`, and `κ_p(D) ≤ (β^s)⁻¹` for the diagonal
-- δ-scaling `D = diag(q)` with `β^s ≤ q ≤ 1`.
--
-- Honest scope: the printed display reads "for any p-norm"; this file closes
-- every finite real exponent `1 ≤ p < ∞` for complex Jordan data.  The
-- `p = ∞` real-spectrum subcase is closed separately in
-- `MatrixPowersJordan.lean` (`higham_eq_18_5_alt_real_jordan`), and the
-- diagonalizable all-p case (eq 18.4) in `MatrixPowersLp.lean`.
--
-- Infrastructure REUSED (source traceability):
--   `CVec`, `CMatrix`, `complexVecLpNorm`,
--   `complexVecLpNorm_isComplexVectorNorm`,
--   `complexVecLpNorm_ofReal_eq_sum_rpow`     — Analysis/VectorNorms/Basic.lean
--   `complexMatrixVecMul`, `complexMatrixMul`, `complexMatrixMul_assoc`,
--   `complexMatrixVecMul_mul`, `IsComplexMatrixRightInverse`
--                                             — Analysis/MatrixNorms/Basic.lean
--   `HasComplexMatrixLpBound`, `hasComplexMatrixLpBound_apply`,
--   `isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound`,
--   `complexMatrixLpNormOfReal` (+ value/bound/mul_le lemmas)
--                                             — Analysis/MatrixNorms/Lp.lean
--   `cDiagMatrix`, `cDiagMatrix_vecMul`, `cDiagMatrix_conj_entry`
--                                             — Algorithms/MatrixPowersComplex.lean ~366
--   `cIdMatrix`, `cMatPow` (+_zero/_succ), `cMatPow_similarity`,
--   `complexVecLpNorm_le_mul_of_forall_norm_le`,
--   `complexMatrixLpNormOfReal_diagonal_le`   — Algorithms/MatrixPowersLp.lean
-- The proof skeletons mirrored here are `higham_eq_18_5_alt_real_jordan`
-- (Algorithms/MatrixPowersJordan.lean, the p = ∞ real case), the entry
-- computation of `cJordan_conj_row_sum_le`
-- (Algorithms/MatrixPowersComplex.lean ~418), and
-- `higham_eq_18_4_upper_lp_diagonalizable` (Algorithms/MatrixPowersLp.lean).








namespace NumStability

open scoped BigOperators

-- ============================================================
-- The shift bound: ‖shift(x)‖_p ≤ ‖x‖_p
-- ============================================================










































































-- ============================================================
-- The bidiagonal L^p bound ‖J'‖_p ≤ ρ + β
-- ============================================================






































































































































-- ============================================================
-- Identity and power norm bounds at every real exponent 1 ≤ p < ∞
-- ============================================================





































-- ============================================================
-- §18.1  Eq (18.5) alternative form, complex Jordan case, all 1 ≤ p < ∞
-- ============================================================

/-- **Higham 2nd ed., §18.1, eq (18.5) alternative form (p. 344, unnumbered
    display) at every real exponent `1 ≤ p < ∞` for complex Jordan data**:
    for complex bidiagonal Jordan-form-like data `X⁻¹AX = J` with
    `‖J_{ii}‖ ≤ ρ`, superdiagonal moduli ≤ 1, and a `β`-scaling vector `q`
    with `β^s ≤ q ≤ 1` obeying the run-step law across nonzero superdiagonal
    entries, the exact powers satisfy

      `‖A^k‖_p ≤ κ_p(X) · (β^s)⁻¹ · (ρ + β)^k`

    where `(β^s)⁻¹` bounds `κ_p(D)` for `D = diag(q)` (in the Jordan
    application `s = t − 1` with `t` the maximal block size, and `β` plays
    the role of the printed δ-margin, cf. `jordanBeta`).

    Honest scope: the printed display covers all p-norms; this closes every
    finite real exponent `1 ≤ p < ∞` for complex Jordan (defective) data;
    the `p = ∞` real-spectrum case is closed separately
    (`higham_eq_18_5_alt_real_jordan`, Algorithms/MatrixPowersJordan.lean).

    Structure: transport powers along `S = X·D`, `S⁻¹ = D⁻¹·X⁻¹`
    (`cMatPow_similarity`), bound the scaled bidiagonal `J' = D⁻¹JD` by
    `‖J'‖_p ≤ ρ + β` (`complexMatrixLpNormOfReal_bidiagonal_le` with the
    shift estimate `complexVecLpNorm_shift_le`), then chain
    submultiplicativity. -/
theorem higham_eq_18_5_alt_lp_jordan (n : ℕ) (hn : 0 < n)
    (A X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hXl : IsComplexMatrixRightInverse X_inv X)
    (hsim : complexMatrixMul X_inv (complexMatrixMul A X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (β : ℝ) (hβ0 : 0 < β) (s : ℕ)
    (q : Fin n → ℝ)
    (hq1 : ∀ i, β ^ s ≤ q i) (hq2 : ∀ i, q i ≤ 1)
    (hqstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 →
      q j = β * q i)
    (p : ℝ) (hp : 1 ≤ p) (k : ℕ) :
    complexMatrixLpNormOfReal hn p hp (cMatPow n A k) ≤
      (complexMatrixLpNormOfReal hn p hp X *
        complexMatrixLpNormOfReal hn p hp X_inv) * (β ^ s)⁻¹ * (ρ + β) ^ k := by
  have hβs : (0 : ℝ) < β ^ s := pow_pos hβ0 s
  have hq0 : ∀ i, 0 < q i := fun i => lt_of_lt_of_le hβs (hq1 i)
  have hnonneg : ∀ M : CMatrix n n, 0 ≤ complexMatrixLpNormOfReal hn p hp M :=
    fun M => (hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal hn hp
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue hn p hp M)).1
  set D := cDiagMatrix (fun a => ((q a : ℝ) : ℂ)) with hD
  set Dinv := cDiagMatrix (fun a => (((q a)⁻¹ : ℝ) : ℂ)) with hDinv
  set S := complexMatrixMul X D with hS
  set Sinv := complexMatrixMul Dinv X_inv with hSinv
  set J' := complexMatrixMul Dinv (complexMatrixMul J D) with hJ'
  -- D and D⁻¹ are a two-sided inverse pair through the vector action.
  have hDr : IsComplexMatrixRightInverse D Dinv := by
    intro x
    rw [hD, hDinv, cDiagMatrix_vecMul, cDiagMatrix_vecMul]
    funext i
    show ((q i : ℝ) : ℂ) * ((((q i)⁻¹ : ℝ) : ℂ) * x i) = x i
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hq0 i).ne',
      Complex.ofReal_one, one_mul]
  have hDl : IsComplexMatrixRightInverse Dinv D := by
    intro x
    rw [hD, hDinv, cDiagMatrix_vecMul, cDiagMatrix_vecMul]
    funext i
    show (((q i)⁻¹ : ℝ) : ℂ) * (((q i : ℝ) : ℂ) * x i) = x i
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (hq0 i).ne',
      Complex.ofReal_one, one_mul]
  -- S = X·D and S⁻¹ = D⁻¹·X⁻¹ are a two-sided inverse pair.
  have hSr : IsComplexMatrixRightInverse S Sinv := by
    intro x
    rw [hS, hSinv, complexMatrixVecMul_mul, complexMatrixVecMul_mul]
    rw [hDr (complexMatrixVecMul X_inv x)]
    exact hXr x
  have hSl : IsComplexMatrixRightInverse Sinv S := by
    intro x
    rw [hS, hSinv, complexMatrixVecMul_mul, complexMatrixVecMul_mul]
    rw [hXl (complexMatrixVecMul D x)]
    exact hDl x
  -- The scaled similarity: S⁻¹·A·S = D⁻¹·J·D = J'.
  have hsim' : complexMatrixMul Sinv (complexMatrixMul A S) = J' := by
    rw [hS, hSinv, hJ']
    have h1 : complexMatrixMul X_inv
        (complexMatrixMul A (complexMatrixMul X D))
        = complexMatrixMul (complexMatrixMul X_inv (complexMatrixMul A X)) D := by
      simp only [complexMatrixMul_assoc]
    rw [complexMatrixMul_assoc Dinv X_inv
      (complexMatrixMul A (complexMatrixMul X D)), h1, hsim]
  have htrans := cMatPow_similarity n A S Sinv J' hSr hSl hsim' k
  -- The scaled bidiagonal bound ‖J'‖_p ≤ ρ + β.
  have hJ'norm : complexMatrixLpNormOfReal hn p hp J' ≤ ρ + β := by
    refine complexMatrixLpNormOfReal_bidiagonal_le hn p hp J' ρ β hρ0 hβ0.le
      ?_ ?_ ?_
    · -- shape: J' inherits the bidiagonal zero pattern from J
      intro i j hji1 hji2
      rw [hJ', hDinv, hD]
      have he : complexMatrixMul (cDiagMatrix fun a => (((q a)⁻¹ : ℝ) : ℂ))
          (complexMatrixMul J (cDiagMatrix fun a => ((q a : ℝ) : ℂ))) i j
          = (((q i)⁻¹ : ℝ) : ℂ) * J i j * ((q j : ℝ) : ℂ) :=
        cDiagMatrix_conj_entry J _ _ i j
      rw [he, hshape i j hji1 hji2, mul_zero, zero_mul]
    · -- diagonal: the conjugation fixes diagonal entries
      intro i
      rw [hJ', hDinv, hD]
      have he : complexMatrixMul (cDiagMatrix fun a => (((q a)⁻¹ : ℝ) : ℂ))
          (complexMatrixMul J (cDiagMatrix fun a => ((q a : ℝ) : ℂ))) i i
          = (((q i)⁻¹ : ℝ) : ℂ) * J i i * ((q i : ℝ) : ℂ) :=
        cDiagMatrix_conj_entry J _ _ i i
      have hpc : (((q i)⁻¹ : ℝ) : ℂ) * ((q i : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hq0 i).ne',
          Complex.ofReal_one]
      have hdiagentry : (((q i)⁻¹ : ℝ) : ℂ) * J i i * ((q i : ℝ) : ℂ)
          = J i i := by
        calc (((q i)⁻¹ : ℝ) : ℂ) * J i i * ((q i : ℝ) : ℂ)
            = J i i * ((((q i)⁻¹ : ℝ) : ℂ) * ((q i : ℝ) : ℂ)) := by ring
          _ = J i i := by rw [hpc, mul_one]
      rw [he, hdiagentry]
      exact hdiagbd i
    · -- superdiagonal: the run-step law compresses each entry to modulus ≤ β
      intro i j hji
      rw [hJ', hDinv, hD]
      have he : complexMatrixMul (cDiagMatrix fun a => (((q a)⁻¹ : ℝ) : ℂ))
          (complexMatrixMul J (cDiagMatrix fun a => ((q a : ℝ) : ℂ))) i j
          = (((q i)⁻¹ : ℝ) : ℂ) * J i j * ((q j : ℝ) : ℂ) :=
        cDiagMatrix_conj_entry J _ _ i j
      rw [he]
      by_cases hJz : J i j = 0
      · rw [hJz, mul_zero, zero_mul, norm_zero]
        exact hβ0.le
      · have hstep := hqstep i j hji hJz
        have hpc : (((q i)⁻¹ : ℝ) : ℂ) * ((q i : ℝ) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hq0 i).ne',
            Complex.ofReal_one]
        have hentry : (((q i)⁻¹ : ℝ) : ℂ) * J i j * ((q j : ℝ) : ℂ)
            = ((β : ℝ) : ℂ) * J i j := by
          rw [hstep, Complex.ofReal_mul]
          calc (((q i)⁻¹ : ℝ) : ℂ) * J i j * (((β : ℝ) : ℂ) * ((q i : ℝ) : ℂ))
              = ((β : ℝ) : ℂ) * J i j *
                ((((q i)⁻¹ : ℝ) : ℂ) * ((q i : ℝ) : ℂ)) := by ring
            _ = ((β : ℝ) : ℂ) * J i j := by rw [hpc, mul_one]
        rw [hentry, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hβ0.le]
        calc β * ‖J i j‖ ≤ β * 1 :=
              mul_le_mul_of_nonneg_left (hsup i j hji) hβ0.le
          _ = β := mul_one β
  have hJ'k : complexMatrixLpNormOfReal hn p hp (cMatPow n J' k) ≤
      (ρ + β) ^ k :=
    complexMatrixLpNormOfReal_cMatPow_le hn p hp J'
      (add_nonneg hρ0 hβ0.le) hJ'norm k
  -- Diagonal factor norms: ‖D‖_p ≤ 1 and ‖D⁻¹‖_p ≤ (β^s)⁻¹.
  have hDnorm : complexMatrixLpNormOfReal hn p hp D ≤ 1 := by
    rw [hD]
    refine complexMatrixLpNormOfReal_diagonal_le hn p hp _ zero_le_one
      (fun i => ?_)
    show ‖((q i : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq0 i)]
    exact hq2 i
  have hDinvnorm : complexMatrixLpNormOfReal hn p hp Dinv ≤ (β ^ s)⁻¹ := by
    rw [hDinv]
    refine complexMatrixLpNormOfReal_diagonal_le hn p hp _
      (inv_nonneg.mpr hβs.le) (fun i => ?_)
    show ‖(((q i)⁻¹ : ℝ) : ℂ)‖ ≤ (β ^ s)⁻¹
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hq0 i))]
    exact inv_anti₀ hβs (hq1 i)
  have hSnorm : complexMatrixLpNormOfReal hn p hp S ≤
      complexMatrixLpNormOfReal hn p hp X := by
    calc complexMatrixLpNormOfReal hn p hp S
        ≤ complexMatrixLpNormOfReal hn p hp X *
            complexMatrixLpNormOfReal hn p hp D := by
          rw [hS]
          exact complexMatrixLpNormOfReal_mul_le hn hn hp X D
      _ ≤ complexMatrixLpNormOfReal hn p hp X * 1 :=
          mul_le_mul_of_nonneg_left hDnorm (hnonneg X)
      _ = complexMatrixLpNormOfReal hn p hp X := mul_one _
  have hSinvnorm : complexMatrixLpNormOfReal hn p hp Sinv ≤
      (β ^ s)⁻¹ * complexMatrixLpNormOfReal hn p hp X_inv := by
    calc complexMatrixLpNormOfReal hn p hp Sinv
        ≤ complexMatrixLpNormOfReal hn p hp Dinv *
            complexMatrixLpNormOfReal hn p hp X_inv := by
          rw [hSinv]
          exact complexMatrixLpNormOfReal_mul_le hn hn hp Dinv X_inv
      _ ≤ (β ^ s)⁻¹ * complexMatrixLpNormOfReal hn p hp X_inv :=
          mul_le_mul_of_nonneg_right hDinvnorm (hnonneg X_inv)
  rw [htrans]
  calc complexMatrixLpNormOfReal hn p hp
        (complexMatrixMul S (complexMatrixMul (cMatPow n J' k) Sinv))
      ≤ complexMatrixLpNormOfReal hn p hp S *
          complexMatrixLpNormOfReal hn p hp
            (complexMatrixMul (cMatPow n J' k) Sinv) :=
        complexMatrixLpNormOfReal_mul_le hn hn hp S _
    _ ≤ complexMatrixLpNormOfReal hn p hp S *
          (complexMatrixLpNormOfReal hn p hp (cMatPow n J' k) *
            complexMatrixLpNormOfReal hn p hp Sinv) :=
        mul_le_mul_of_nonneg_left
          (complexMatrixLpNormOfReal_mul_le hn hn hp _ Sinv) (hnonneg S)
    _ ≤ complexMatrixLpNormOfReal hn p hp X *
          ((ρ + β) ^ k *
            ((β ^ s)⁻¹ * complexMatrixLpNormOfReal hn p hp X_inv)) := by
        apply mul_le_mul hSnorm _
          (mul_nonneg (hnonneg _) (hnonneg _)) (hnonneg X)
        exact mul_le_mul hJ'k hSinvnorm (hnonneg Sinv)
          (pow_nonneg (add_nonneg hρ0 hβ0.le) k)
    _ = (complexMatrixLpNormOfReal hn p hp X *
          complexMatrixLpNormOfReal hn p hp X_inv) * (β ^ s)⁻¹ *
          (ρ + β) ^ k := by ring

end NumStability
