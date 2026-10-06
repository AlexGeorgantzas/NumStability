import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealJordan
import NumStability.Analysis.MatrixAlgebra

/-!
# Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.RealJordan

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/MatrixPowersJordan.lean
--
-- Higham Chapter 18: Error analysis of matrix powers — the defective
-- real-spectrum case of Theorem 18.1 (Higham–Knight).
--
-- Discharges `JordanFormSpec.similarity_absorbs` for real Jordan-form data
-- with block size t ≥ 2 via the δ-scaling construction of the book's proof
-- (Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
-- pp. 347–348): S = X·D with D = diag(p_i), p_i = β^(run length at i),
-- β = (1−ρ)(t−1)/t, together with the (1+1/m)^m < e < 4 optimisation that
-- turns the printed condition 4t·η·κ∞(X)·‖A‖∞ < (1−ρ)^t into a per-step
-- contraction ‖S⁻¹(A+ΔA)S‖∞ ≤ q < 1.












namespace NumStability

open scoped BigOperators

-- ============================================================
-- Scalar preliminaries: the (1 + 1/m)^m < e < 4 optimisation
-- ============================================================






















































-- ============================================================
-- The scaling margin β = (1−ρ)(t−1)/t of the δ-scaling construction
-- ============================================================








































































-- ============================================================
-- Diagonal scaling matrices: inverse, entries, norms
-- ============================================================



































-- ============================================================
-- The scaled bidiagonal row-sum bound ‖D⁻¹ J D‖∞ ≤ ρ + β
-- ============================================================






































































































-- ============================================================
-- Run lengths of superdiagonal 1-chains and the scaling vector
-- ============================================================
























































-- ============================================================
-- Theorem 18.1: discharged t ≥ 2 construction (real Jordan data)
-- ============================================================









































































































































































































-- ============================================================
-- Theorem 18.1: axiom-free end-to-end forms (real Jordan data)
-- ============================================================













































































































-- ============================================================
-- §18.1  Exact arithmetic: eq (18.5) alternative form, real Jordan case
-- ============================================================

/-- **Eq (18.5), alternative form (p. 344, unnumbered display), real-Jordan
    ∞-norm case** (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §18.1): for real bidiagonal Jordan data `X⁻¹AX = J` with
    `|J_{ii}| ≤ ρ`, superdiagonal moduli ≤ 1, and a `β`-scaling vector `p`
    with `βˢ ≤ p ≤ 1` obeying the run-step law, the exact powers satisfy

      `‖Aᵏ‖∞ ≤ κ∞(X) · (βˢ)⁻¹ · (ρ + β)ᵏ`

    where `(βˢ)⁻¹` bounds `κ∞(D)` for `D = diag(p)` (in the Jordan
    application `s = t − 1` and `β` plays the role of the printed
    δ-margin, cf. `jordanBeta`).  Honest scope: the printed display covers
    all p-norms and complex data; this closes the `p = ∞`, real-spectrum
    form. -/
theorem higham_eq_18_5_alt_real_jordan (n : ℕ) (hn : 0 < n)
    (A X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n A X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 → J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hdiagbd : ∀ i, |J i i| ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → |J i j| ≤ 1)
    (β : ℝ) (hβ0 : 0 < β) (s : ℕ)
    (p : Fin n → ℝ)
    (hp1 : ∀ i, β ^ s ≤ p i) (hp2 : ∀ i, p i ≤ 1)
    (hpstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 → p j = β * p i)
    (k : ℕ) :
    infNorm (matPow n A k) ≤
      (infNorm X * infNorm X_inv) * (β ^ s)⁻¹ * (ρ + β) ^ k := by
  have hβs : (0:ℝ) < β ^ s := pow_pos hβ0 s
  have hp0 : ∀ i, 0 < p i := fun i => lt_of_lt_of_le hβs (hp1 i)
  set D := diagMatrix p with hD
  set Dinv := diagMatrix (fun a => (p a)⁻¹) with hDinv
  set S := matMul n X D with hS
  set Sinv := matMul n Dinv X_inv with hSinv
  have hDr : IsRightInverse n D Dinv :=
    diagMatrix_isRightInverse n p _ (fun a => mul_inv_cancel₀ (hp0 a).ne')
  have hDl : IsRightInverse n Dinv D :=
    diagMatrix_isRightInverse n _ p (fun a => inv_mul_cancel₀ (hp0 a).ne')
  have hXX : matMul n X X_inv = idMatrix n := by ext a b; exact hXr a b
  have hXX' : matMul n X_inv X = idMatrix n := by ext a b; exact hXl a b
  have hDD : matMul n D Dinv = idMatrix n := by ext a b; exact hDr a b
  have hDD' : matMul n Dinv D = idMatrix n := by ext a b; exact hDl a b
  have hSr : IsRightInverse n S Sinv := by
    intro a b
    have h : matMul n S Sinv = idMatrix n := by
      rw [hS, hSinv, matMul_assoc n X D (matMul n Dinv X_inv),
        ← matMul_assoc n D Dinv X_inv, hDD, matMul_id_left, hXX]
    exact congrFun (congrFun h a) b
  have hSl : IsRightInverse n Sinv S := by
    intro a b
    have h : matMul n Sinv S = idMatrix n := by
      rw [hSinv, hS, matMul_assoc n Dinv X_inv (matMul n X D),
        ← matMul_assoc n X_inv X D, hXX', matMul_id_left, hDD']
    exact congrFun (congrFun h a) b
  set J' := matMul n Dinv (matMul n J D) with hJ'
  have hsim' : matMul n Sinv (matMul n A S) = J' := by
    rw [hSinv, hS, hJ']
    have h1 : matMul n X_inv (matMul n A (matMul n X D))
        = matMul n (matMul n X_inv (matMul n A X)) D := by
      simp only [← matMul_assoc]
    rw [matMul_assoc n Dinv X_inv (matMul n A (matMul n X D)), h1, hsim]
  have htrans := matPow_similarity n A S Sinv J' hSr hSl hsim' k
  have hJ'norm : infNorm J' ≤ ρ + β := by
    rw [hJ', hDinv, hD]
    exact infNorm_jordan_conj_le n J p ρ β hρ0 hβ0.le hshape hdiagbd hsup
      hp0 hpstep
  have hJ'k : infNorm (matPow n J' k) ≤ (ρ + β) ^ k :=
    calc infNorm (matPow n J' k) ≤ infNorm J' ^ k := infNorm_matPow_le hn J' k
      _ ≤ (ρ + β) ^ k := pow_le_pow_left₀ (infNorm_nonneg J') hJ'norm k
  have hDnorm : infNorm D ≤ 1 := by
    rw [hD]
    exact infNorm_diagMatrix_le p zero_le_one
      (fun i => by rw [abs_of_pos (hp0 i)]; exact hp2 i)
  have hDinvnorm : infNorm Dinv ≤ (β ^ s)⁻¹ := by
    rw [hDinv]
    apply infNorm_diagMatrix_le _ (inv_nonneg.mpr hβs.le)
    intro i
    rw [abs_of_pos (inv_pos.mpr (hp0 i))]
    exact inv_anti₀ hβs (hp1 i)
  have hSnorm : infNorm S ≤ infNorm X := by
    calc infNorm S ≤ infNorm X * infNorm D := by
          rw [hS]; exact infNorm_matMul_le hn X D
      _ ≤ infNorm X * 1 := mul_le_mul_of_nonneg_left hDnorm (infNorm_nonneg X)
      _ = infNorm X := mul_one _
  have hSinvnorm : infNorm Sinv ≤ (β ^ s)⁻¹ * infNorm X_inv := by
    calc infNorm Sinv ≤ infNorm Dinv * infNorm X_inv := by
          rw [hSinv]; exact infNorm_matMul_le hn _ _
      _ ≤ (β ^ s)⁻¹ * infNorm X_inv :=
          mul_le_mul_of_nonneg_right hDinvnorm (infNorm_nonneg X_inv)
  rw [htrans]
  calc infNorm (matMul n S (matMul n (matPow n J' k) Sinv))
      ≤ infNorm S * infNorm (matMul n (matPow n J' k) Sinv) :=
        infNorm_matMul_le hn _ _
    _ ≤ infNorm S * (infNorm (matPow n J' k) * infNorm Sinv) :=
        mul_le_mul_of_nonneg_left (infNorm_matMul_le hn _ _)
          (infNorm_nonneg S)
    _ ≤ infNorm X * ((ρ + β) ^ k * ((β ^ s)⁻¹ * infNorm X_inv)) := by
        apply mul_le_mul hSnorm _
          (mul_nonneg (infNorm_nonneg _) (infNorm_nonneg _))
          (infNorm_nonneg X)
        exact mul_le_mul hJ'k hSinvnorm (infNorm_nonneg Sinv)
          (pow_nonneg (add_nonneg hρ0 hβ0.le) k)
    _ = (infNorm X * infNorm X_inv) * (β ^ s)⁻¹ * (ρ + β) ^ k := by ring

end NumStability
