-- Analysis/MatrixPowersLp185Primary.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- §18.2, eq (18.5) PRIMARY printed form (p. 344):
--
--   ‖A^k‖_p ≤ κ_p(X_δ) · (ρ(A) + δ)^k
--
-- where X_δ is the Jordan transform of the *rescaled* Jordan matrix
-- (equivalently the transform that conjugates A to the δ-scaled Jordan
-- matrix J' = D⁻¹ J D), as opposed to the ALTERNATIVE form
--
--   ‖A^k‖_p ≤ κ_p(X) · κ_p(D) · (ρ(A) + δ)^k
--
-- which keeps the X and D factors separate.  The two forms are related by
-- X_δ = X·D and X_δ⁻¹ = D⁻¹·X⁻¹, so
-- κ_p(X_δ) = ‖X·D‖_p·‖D⁻¹·X⁻¹‖_p ≤ κ_p(X)·κ_p(D); the primary bound is
-- therefore at least as strong as the alternative one it is derived from.
--
-- This file is IMPORT-ONLY.  It reuses the alternative-form machinery of
-- `Algorithms/MatrixPowersLpJordan.lean` (the shift bound
-- `complexVecLpNorm_shift_le`, the bidiagonal L^p bound
-- `complexMatrixLpNormOfReal_bidiagonal_le`, and the submultiplicative
-- power bound `complexMatrixLpNormOfReal_cMatPow_le`) and the similarity
-- transport / inverse-pair lemmas of `Norms.lean` /
-- `Algorithms/MatrixPowersLp.lean`.  Nothing is re-proved; the primary
-- grouping `κ_p(X_δ)·(ρ+β)^k` is assembled fresh.
--
-- Honest scope: the printed display reads "for any p-norm"; this closes
-- every finite real exponent `1 ≤ p < ∞` for complex Jordan (possibly
-- defective) data.  The `p = ∞` real-spectrum subcase is closed here too
-- (`higham_eq_18_5_primary_real_jordan`), matching the alternative form's
-- `higham_eq_18_5_alt_real_jordan`.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import NumStability.Analysis.Norms
import NumStability.Algorithms.MatrixPowersLp
import NumStability.Algorithms.MatrixPowersLpJordan
import NumStability.Algorithms.MatrixPowersJordan

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §18.2  Eq (18.5) primary form, complex Jordan case, all 1 ≤ p < ∞
-- ============================================================

/-- **Higham 2nd ed., §18.2, eq (18.5) PRIMARY printed form (p. 344) at
    every real exponent `1 ≤ p < ∞` for complex Jordan data.**

    For complex bidiagonal Jordan-form-like data `X⁻¹AX = J` with
    `‖J_{ii}‖ ≤ ρ`, superdiagonal moduli ≤ 1, and a `β`-scaling vector `q`
    with `β^s ≤ q ≤ 1` obeying the run-step law across nonzero superdiagonal
    entries, form the *combined* Jordan transform of the δ-scaled matrix

      `X_δ = X · D`,   `X_δ⁻¹ = D⁻¹ · X⁻¹`   (`D = diag(q)`),

    which conjugates `A` to the δ-scaled Jordan matrix `J' = D⁻¹ J D`
    (superdiagonal moduli ≤ `β`).  Then the exact powers satisfy the printed
    primary bound

      `‖A^k‖_p ≤ κ_p(X_δ) · (ρ + β)^k`,

    with `κ_p(X_δ) = ‖X_δ‖_p · ‖X_δ⁻¹‖_p` and `β` playing the role of the
    printed δ-margin (`ρ + β = ρ(A) + δ` on Jordan data).

    This is the genuine primary shape: the condition number is that of the
    single transform `X_δ` of the rescaled Jordan matrix, NOT the product
    `κ_p(X)·κ_p(D)` of the alternative form.  It is derived from the
    alternative-form machinery (same `J' = D⁻¹JD`, same `‖J'‖_p ≤ ρ + β`
    step) by grouping the similarity factors as `X_δ`/`X_δ⁻¹` instead of
    splitting `D` off; by submultiplicativity it is at least as tight as the
    alternative bound (`κ_p(X_δ) ≤ κ_p(X)·κ_p(D)`).

    Honest scope: the printed display covers all p-norms; this closes every
    finite real exponent `1 ≤ p < ∞` for complex Jordan (defective) data;
    the `p = ∞` real-spectrum case is `higham_eq_18_5_primary_real_jordan`
    below. -/
theorem higham_eq_18_5_primary_lp_jordan (n : ℕ) (hn : 0 < n)
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
      (complexMatrixLpNormOfReal hn p hp
          (complexMatrixMul X (cDiagMatrix (fun a => ((q a : ℝ) : ℂ)))) *
        complexMatrixLpNormOfReal hn p hp
          (complexMatrixMul
            (cDiagMatrix (fun a => (((q a)⁻¹ : ℝ) : ℂ))) X_inv)) *
        (ρ + β) ^ k := by
  have hβs : (0 : ℝ) < β ^ s := pow_pos hβ0 s
  have hq0 : ∀ i, 0 < q i := fun i => lt_of_lt_of_le hβs (hq1 i)
  have hnonneg : ∀ M : CMatrix n n, 0 ≤ complexMatrixLpNormOfReal hn p hp M :=
    fun M => (hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal hn hp
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue hn p hp M)).1
  set D := cDiagMatrix (fun a => ((q a : ℝ) : ℂ)) with hD
  set Dinv := cDiagMatrix (fun a => (((q a)⁻¹ : ℝ) : ℂ)) with hDinv
  -- The combined Jordan transform of the rescaled matrix and its inverse.
  set Xδ := complexMatrixMul X D with hXδ
  set Xδinv := complexMatrixMul Dinv X_inv with hXδinv
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
  -- X_δ = X·D and X_δ⁻¹ = D⁻¹·X⁻¹ are a two-sided inverse pair.
  have hXδr : IsComplexMatrixRightInverse Xδ Xδinv := by
    intro x
    rw [hXδ, hXδinv, complexMatrixVecMul_mul, complexMatrixVecMul_mul]
    rw [hDr (complexMatrixVecMul X_inv x)]
    exact hXr x
  have hXδl : IsComplexMatrixRightInverse Xδinv Xδ := by
    intro x
    rw [hXδ, hXδinv, complexMatrixVecMul_mul, complexMatrixVecMul_mul]
    rw [hXl (complexMatrixVecMul D x)]
    exact hDl x
  -- The scaled similarity: X_δ⁻¹·A·X_δ = D⁻¹·J·D = J'.
  have hsim' : complexMatrixMul Xδinv (complexMatrixMul A Xδ) = J' := by
    rw [hXδ, hXδinv, hJ']
    have h1 : complexMatrixMul X_inv
        (complexMatrixMul A (complexMatrixMul X D))
        = complexMatrixMul (complexMatrixMul X_inv (complexMatrixMul A X)) D := by
      simp only [complexMatrixMul_assoc]
    rw [complexMatrixMul_assoc Dinv X_inv
      (complexMatrixMul A (complexMatrixMul X D)), h1, hsim]
  have htrans := cMatPow_similarity n A Xδ Xδinv J' hXδr hXδl hsim' k
  -- The scaled bidiagonal bound ‖J'‖_p ≤ ρ + β (reused from the alt form).
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
  -- Primary grouping: κ_p(X_δ)·‖J'^k‖_p, with X_δ = X·D kept intact.
  rw [htrans]
  calc complexMatrixLpNormOfReal hn p hp
        (complexMatrixMul Xδ (complexMatrixMul (cMatPow n J' k) Xδinv))
      ≤ complexMatrixLpNormOfReal hn p hp Xδ *
          complexMatrixLpNormOfReal hn p hp
            (complexMatrixMul (cMatPow n J' k) Xδinv) :=
        complexMatrixLpNormOfReal_mul_le hn hn hp Xδ _
    _ ≤ complexMatrixLpNormOfReal hn p hp Xδ *
          (complexMatrixLpNormOfReal hn p hp (cMatPow n J' k) *
            complexMatrixLpNormOfReal hn p hp Xδinv) :=
        mul_le_mul_of_nonneg_left
          (complexMatrixLpNormOfReal_mul_le hn hn hp _ Xδinv) (hnonneg Xδ)
    _ ≤ complexMatrixLpNormOfReal hn p hp Xδ *
          ((ρ + β) ^ k * complexMatrixLpNormOfReal hn p hp Xδinv) := by
        apply mul_le_mul_of_nonneg_left _ (hnonneg Xδ)
        exact mul_le_mul_of_nonneg_right hJ'k (hnonneg Xδinv)
    _ = (complexMatrixLpNormOfReal hn p hp Xδ *
          complexMatrixLpNormOfReal hn p hp Xδinv) * (ρ + β) ^ k := by ring

-- ============================================================
-- §18.2  Eq (18.5) primary form, real Jordan case, p = ∞
-- ============================================================

/-- **Higham 2nd ed., §18.2, eq (18.5) PRIMARY printed form (p. 344),
    real-spectrum ∞-norm case.**

    For real bidiagonal Jordan data `X⁻¹AX = J` with `|J_{ii}| ≤ ρ`,
    superdiagonal moduli ≤ 1, and a `β`-scaling vector `p` with
    `β^s ≤ p ≤ 1` obeying the run-step law, form the combined Jordan
    transform of the δ-scaled matrix `X_δ = X · D`, `X_δ⁻¹ = D⁻¹ · X⁻¹`
    (`D = diag(p)`).  Then the exact powers satisfy the printed primary
    bound

      `‖A^k‖∞ ≤ κ∞(X_δ) · (ρ + β)^k`,

    with `κ∞(X_δ) = ‖X_δ‖∞ · ‖X_δ⁻¹‖∞`.  This is the genuine primary shape:
    the condition number is that of the single transform `X_δ` of the
    rescaled Jordan matrix, not the product `κ∞(X)·κ∞(D)` of the alternative
    form `higham_eq_18_5_alt_real_jordan`; by submultiplicativity it is at
    least as tight (`κ∞(X_δ) ≤ κ∞(X)·κ∞(D)`).

    Honest scope: the printed display covers all p-norms and complex data;
    this closes the `p = ∞`, real-spectrum form, matching the alternative
    real form. -/
theorem higham_eq_18_5_primary_real_jordan (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hdiagbd : ∀ i, |J i i| ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → |J i j| ≤ 1)
    (β : ℝ) (hβ0 : 0 < β) (s : ℕ)
    (p : Fin n → ℝ)
    (hp1 : ∀ i, β ^ s ≤ p i) (hp2 : ∀ i, p i ≤ 1)
    (hpstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 → p j = β * p i)
    (k : ℕ) :
    infNorm (matPow n A k) ≤
      (infNorm (matMul n X (diagMatrix p)) *
        infNorm (matMul n (diagMatrix (fun a => (p a)⁻¹)) X_inv)) *
        (ρ + β) ^ k := by
  have hβs : (0:ℝ) < β ^ s := pow_pos hβ0 s
  have hp0 : ∀ i, 0 < p i := fun i => lt_of_lt_of_le hβs (hp1 i)
  set D := diagMatrix p with hD
  set Dinv := diagMatrix (fun a => (p a)⁻¹) with hDinv
  -- The combined Jordan transform of the rescaled matrix and its inverse.
  set Xδ := matMul n X D with hXδ
  set Xδinv := matMul n Dinv X_inv with hXδinv
  have hDr : IsRightInverse n D Dinv :=
    diagMatrix_isRightInverse n p _ (fun a => mul_inv_cancel₀ (hp0 a).ne')
  have hDl : IsRightInverse n Dinv D :=
    diagMatrix_isRightInverse n _ p (fun a => inv_mul_cancel₀ (hp0 a).ne')
  have hXX : matMul n X X_inv = idMatrix n := by ext a b; exact hXr a b
  have hXX' : matMul n X_inv X = idMatrix n := by ext a b; exact hXl a b
  have hDD : matMul n D Dinv = idMatrix n := by ext a b; exact hDr a b
  have hDD' : matMul n Dinv D = idMatrix n := by ext a b; exact hDl a b
  have hXδr : IsRightInverse n Xδ Xδinv := by
    intro a b
    have h : matMul n Xδ Xδinv = idMatrix n := by
      rw [hXδ, hXδinv, matMul_assoc n X D (matMul n Dinv X_inv),
        ← matMul_assoc n D Dinv X_inv, hDD, matMul_id_left, hXX]
    exact congrFun (congrFun h a) b
  have hXδl : IsRightInverse n Xδinv Xδ := by
    intro a b
    have h : matMul n Xδinv Xδ = idMatrix n := by
      rw [hXδinv, hXδ, matMul_assoc n Dinv X_inv (matMul n X D),
        ← matMul_assoc n X_inv X D, hXX', matMul_id_left, hDD']
    exact congrFun (congrFun h a) b
  set J' := matMul n Dinv (matMul n J D) with hJ'
  have hsim' : matMul n Xδinv (matMul n A Xδ) = J' := by
    rw [hXδinv, hXδ, hJ']
    have h1 : matMul n X_inv (matMul n A (matMul n X D))
        = matMul n (matMul n X_inv (matMul n A X)) D := by
      simp only [← matMul_assoc]
    rw [matMul_assoc n Dinv X_inv (matMul n A (matMul n X D)), h1, hsim]
  have htrans := matPow_similarity n A Xδ Xδinv J' hXδr hXδl hsim' k
  have hJ'norm : infNorm J' ≤ ρ + β := by
    rw [hJ', hDinv, hD]
    exact infNorm_jordan_conj_le n J p ρ β hρ0 hβ0.le hshape hdiagbd hsup
      hp0 hpstep
  have hJ'k : infNorm (matPow n J' k) ≤ (ρ + β) ^ k :=
    calc infNorm (matPow n J' k) ≤ infNorm J' ^ k := infNorm_matPow_le hn J' k
      _ ≤ (ρ + β) ^ k := pow_le_pow_left₀ (infNorm_nonneg J') hJ'norm k
  -- Primary grouping: κ∞(X_δ)·‖J'^k‖∞, with X_δ = X·D kept intact.
  rw [htrans]
  calc infNorm (matMul n Xδ (matMul n (matPow n J' k) Xδinv))
      ≤ infNorm Xδ * infNorm (matMul n (matPow n J' k) Xδinv) :=
        infNorm_matMul_le hn _ _
    _ ≤ infNorm Xδ * (infNorm (matPow n J' k) * infNorm Xδinv) :=
        mul_le_mul_of_nonneg_left (infNorm_matMul_le hn _ _)
          (infNorm_nonneg Xδ)
    _ ≤ infNorm Xδ * ((ρ + β) ^ k * infNorm Xδinv) := by
        apply mul_le_mul_of_nonneg_left _ (infNorm_nonneg Xδ)
        exact mul_le_mul_of_nonneg_right hJ'k (infNorm_nonneg Xδinv)
    _ = (infNorm Xδ * infNorm Xδinv) * (ρ + β) ^ k := by ring

end NumStability
