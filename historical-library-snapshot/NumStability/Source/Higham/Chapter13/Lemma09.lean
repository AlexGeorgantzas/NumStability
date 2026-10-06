import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral

/-!
# Source.Higham.Chapter13.Lemma09

This module formalizes the source-facing Chapter 13 statements for
`Lemma09`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


-- ============================================================
-- §13.3.2  SPD conditional adapters (Lemmas 13.9 and 13.10)
-- ============================================================

/-- Conditional adapter for **Lemma 13.9** (Higham): if the Cholesky/operator-norm
    route supplies `‖A₂₁ A₁₁⁻¹‖₂ ≤ κ₂(A)^{1/2}`, expose that bound under the
    chapter's name.
    From the Cholesky factorization A = RᵀR: A₂₁A₁₁⁻¹ = R₁₂ᵀR₁₁⁻ᵀ,
    so ‖A₂₁A₁₁⁻¹‖₂ ≤ ‖R₁₂‖₂ · ‖R₁₁⁻¹‖₂ ≤ κ₂(R) = κ₂(A)^{1/2}. -/
theorem higham13_lemma13_9_conditional_bound
    (norm2_A21_A11inv kappa2_A : ℝ)
    (_hkappa : 0 ≤ kappa2_A)
    (hBound : norm2_A21_A11inv ≤ Real.sqrt kappa2_A) :
    norm2_A21_A11inv ≤ Real.sqrt kappa2_A := hBound

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    scalar bridge from squared Cholesky norm bounds to the product bound.

    The Cholesky proof uses estimates of the form
    `‖R₁₂‖₂² ≤ ‖A‖₂`, `‖R₁₁⁻¹‖₂² ≤ ‖A⁻¹‖₂`, and
    `‖A‖₂ ‖A⁻¹‖₂ ≤ κ₂(A)`.  This lemma packages just the real-arithmetic
    consequence `‖R₁₂‖₂ ‖R₁₁⁻¹‖₂ ≤ κ₂(A)^{1/2}`. -/
theorem higham13_lemma13_9_product_majorant_from_square_bounds
    {normR12 normR11inv normA normAinv kappa2A : ℝ}
    (hNormA_nonneg : 0 ≤ normA)
    (hR12sq : normR12 ^ 2 ≤ normA)
    (hR11invsq : normR11inv ^ 2 ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappa2A) :
    normR12 * normR11inv ≤ Real.sqrt kappa2A := by
  apply Real.le_sqrt_of_sq_le
  calc
    (normR12 * normR11inv) ^ 2 = normR12 ^ 2 * normR11inv ^ 2 := by ring
    _ ≤ normA * normAinv := by
        exact mul_le_mul hR12sq hR11invsq
          (sq_nonneg normR11inv) hNormA_nonneg
    _ ≤ kappa2A := hkappa

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    the Cholesky diagonal block equation gives the `R₁₂` square-bound
    operator certificate.

    If `A₂₂ = R₁₂ᵀR₁₂ + R₂₂ᵀR₂₂` and `A₂₂` has operator-2 bound `normA`,
    then `‖R₁₂‖₂ ≤ sqrt(normA)`.  The remaining source-level step is relating
    the principal block bound `‖A₂₂‖₂ ≤ ‖A‖₂` to the full SPD matrix. -/
theorem higham13_lemma13_9_R12_rectOpNorm2Le_of_A22_cholesky_block
    {r s : ℕ}
    (A22 : Fin s → Fin s → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA : ℝ}
    (hNormA_nonneg : 0 ≤ normA)
    (hA22 : A22 =
      fun j k =>
        (∑ i : Fin r, R12 i j * R12 i k) +
          (∑ l : Fin s, R22 l j * R22 l k))
    (hA22_op : opNorm2Le A22 normA) :
    rectOpNorm2Le R12 (Real.sqrt normA) := by
  apply rectOpNorm2Le_sqrt_of_vecNorm2Sq_le R12 hNormA_nonneg
  intro x
  let y12 : Fin r → ℝ := rectMatMulVec R12 x
  let y22 : Fin s → ℝ := rectMatMulVec R22 x
  have hquad :
      (∑ j : Fin s, x j * matMulVec s A22 x j) =
        vecNorm2Sq y12 + vecNorm2Sq y22 := by
    rw [hA22]
    dsimp [matMulVec, vecNorm2Sq, rectMatMulVec, y12, y22]
    have h12 :
        (∑ j : Fin s,
            x j *
              (∑ k : Fin s, (∑ i : Fin r, R12 i j * R12 i k) * x k))
          =
        ∑ i : Fin r, (∑ j : Fin s, R12 i j * x j) ^ 2 := by
      calc
        (∑ j : Fin s,
            x j *
              (∑ k : Fin s, (∑ i : Fin r, R12 i j * R12 i k) * x k))
            =
          ∑ j : Fin s,
            x j *
              (∑ i : Fin r, R12 i j * ∑ k : Fin s, R12 i k * x k) := by
              apply Finset.sum_congr rfl
              intro j _hj
              congr 1
              calc
                (∑ k : Fin s, (∑ i : Fin r, R12 i j * R12 i k) * x k)
                    =
                  ∑ k : Fin s, ∑ i : Fin r, (R12 i j * R12 i k) * x k := by
                    apply Finset.sum_congr rfl
                    intro k _hk
                    rw [Finset.sum_mul]
                _ = ∑ i : Fin r, ∑ k : Fin s, (R12 i j * R12 i k) * x k := by
                    rw [Finset.sum_comm]
                _ = ∑ i : Fin r, R12 i j * ∑ k : Fin s, R12 i k * x k := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro k _hk
                    ring
        _ = ∑ i : Fin r, (∑ j : Fin s, R12 i j * x j) ^ 2 := by
              calc
                (∑ j : Fin s,
                    x j *
                      (∑ i : Fin r, R12 i j *
                        ∑ k : Fin s, R12 i k * x k))
                    =
                  ∑ j : Fin s, ∑ i : Fin r,
                    x j * (R12 i j * ∑ k : Fin s, R12 i k * x k) := by
                    apply Finset.sum_congr rfl
                    intro j _hj
                    rw [Finset.mul_sum]
                _ = ∑ i : Fin r, ∑ j : Fin s,
                    x j * (R12 i j * ∑ k : Fin s, R12 i k * x k) := by
                    rw [Finset.sum_comm]
                _ = ∑ i : Fin r, (∑ j : Fin s, R12 i j * x j) ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    rw [sq, Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro j _hj
                    ring
    have h22 :
        (∑ j : Fin s,
            x j *
              (∑ k : Fin s, (∑ l : Fin s, R22 l j * R22 l k) * x k))
          =
        ∑ l : Fin s, (∑ j : Fin s, R22 l j * x j) ^ 2 := by
      calc
        (∑ j : Fin s,
            x j *
              (∑ k : Fin s, (∑ l : Fin s, R22 l j * R22 l k) * x k))
            =
          ∑ j : Fin s,
            x j *
              (∑ l : Fin s, R22 l j * ∑ k : Fin s, R22 l k * x k) := by
              apply Finset.sum_congr rfl
              intro j _hj
              congr 1
              calc
                (∑ k : Fin s, (∑ l : Fin s, R22 l j * R22 l k) * x k)
                    =
                  ∑ k : Fin s, ∑ l : Fin s, (R22 l j * R22 l k) * x k := by
                    apply Finset.sum_congr rfl
                    intro k _hk
                    rw [Finset.sum_mul]
                _ = ∑ l : Fin s, ∑ k : Fin s, (R22 l j * R22 l k) * x k := by
                    rw [Finset.sum_comm]
                _ = ∑ l : Fin s, R22 l j * ∑ k : Fin s, R22 l k * x k := by
                    apply Finset.sum_congr rfl
                    intro l _hl
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro k _hk
                    ring
        _ = ∑ l : Fin s, (∑ j : Fin s, R22 l j * x j) ^ 2 := by
              calc
                (∑ j : Fin s,
                    x j *
                      (∑ l : Fin s, R22 l j *
                        ∑ k : Fin s, R22 l k * x k))
                    =
                  ∑ j : Fin s, ∑ l : Fin s,
                    x j * (R22 l j * ∑ k : Fin s, R22 l k * x k) := by
                    apply Finset.sum_congr rfl
                    intro j _hj
                    rw [Finset.mul_sum]
                _ = ∑ l : Fin s, ∑ j : Fin s,
                    x j * (R22 l j * ∑ k : Fin s, R22 l k * x k) := by
                    rw [Finset.sum_comm]
                _ = ∑ l : Fin s, (∑ j : Fin s, R22 l j * x j) ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro l _hl
                    rw [sq, Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro j _hj
                    ring
    calc
      (∑ j : Fin s,
          x j *
            (∑ k : Fin s,
              ((∑ i : Fin r, R12 i j * R12 i k) +
                (∑ l : Fin s, R22 l j * R22 l k)) * x k))
          =
        (∑ j : Fin s,
            x j *
              (∑ k : Fin s, (∑ i : Fin r, R12 i j * R12 i k) * x k)) +
          (∑ j : Fin s,
            x j *
              (∑ k : Fin s, (∑ l : Fin s, R22 l j * R22 l k) * x k)) := by
          calc
            (∑ j : Fin s,
                x j *
                  (∑ k : Fin s,
                    ((∑ i : Fin r, R12 i j * R12 i k) +
                      (∑ l : Fin s, R22 l j * R22 l k)) * x k))
                =
              ∑ j : Fin s,
                (x j *
                    (∑ k : Fin s, (∑ i : Fin r, R12 i j * R12 i k) * x k) +
                  x j *
                    (∑ k : Fin s, (∑ l : Fin s, R22 l j * R22 l k) * x k)) := by
                apply Finset.sum_congr rfl
                intro j _hj
                calc
                  x j *
                      (∑ k : Fin s,
                        ((∑ i : Fin r, R12 i j * R12 i k) +
                          (∑ l : Fin s, R22 l j * R22 l k)) * x k)
                      =
                    x j *
                      ((∑ k : Fin s, (∑ i : Fin r, R12 i j * R12 i k) * x k) +
                        (∑ k : Fin s, (∑ l : Fin s, R22 l j * R22 l k) * x k)) := by
                      congr 1
                      rw [← Finset.sum_add_distrib]
                      apply Finset.sum_congr rfl
                      intro k _hk
                      ring
                  _ =
                    x j * (∑ k : Fin s, (∑ i : Fin r, R12 i j * R12 i k) * x k) +
                      x j * (∑ k : Fin s, (∑ l : Fin s, R22 l j * R22 l k) * x k) := by
                      ring
            _ =
              (∑ j : Fin s,
                  x j *
                    (∑ k : Fin s, (∑ i : Fin r, R12 i j * R12 i k) * x k)) +
                (∑ j : Fin s,
                  x j *
                    (∑ k : Fin s, (∑ l : Fin s, R22 l j * R22 l k) * x k)) := by
                rw [Finset.sum_add_distrib]
      _ = (∑ i : Fin r, (∑ j : Fin s, R12 i j * x j) ^ 2) +
          (∑ l : Fin s, (∑ j : Fin s, R22 l j * x j) ^ 2) := by
          rw [h12, h22]
  have hR12_le_quad :
      vecNorm2Sq y12 ≤ ∑ j : Fin s, x j * matMulVec s A22 x j := by
    rw [hquad]
    exact le_add_of_nonneg_right (vecNorm2Sq_nonneg y22)
  have hquad_bound :
      ∑ j : Fin s, x j * matMulVec s A22 x j ≤ normA * vecNorm2Sq x := by
    exact le_trans (le_abs_self _)
      (abs_vecInnerProduct_matMulVec_le_of_opNorm2Le A22 hA22_op x)
  exact le_trans hR12_le_quad hquad_bound

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    the lower-right principal block inherits an operator-2 bound from the full
    two-by-two block matrix.

    This is the source step `‖A₂₂‖₂ ≤ ‖A‖₂`, stated with the repository's
    finite vector-action operator certificate for the full block matrix. -/
theorem higham13_lemma13_9_A22_opNorm2Le_of_full_block
    {r s : ℕ}
    (A : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    {normA : ℝ}
    (hA : finiteOpNorm2Le A normA) :
    opNorm2Le (fun i j : Fin s => A (Sum.inr i) (Sum.inr j)) normA :=
  opNorm2Le_of_finiteOpNorm2Le _
    (finiteOpNorm2Le_sumInr_principal A hA)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-facing equality wrapper for the lower-right principal block
    operator-2 bound. -/
theorem higham13_lemma13_9_A22_opNorm2Le_of_full_block_eq
    {r s : ℕ}
    (A : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    {normA : ℝ}
    (hA22 : A22 = fun i j : Fin s => A (Sum.inr i) (Sum.inr j))
    (hA : finiteOpNorm2Le A normA) :
    opNorm2Le A22 normA := by
  rw [hA22]
  exact higham13_lemma13_9_A22_opNorm2Le_of_full_block A hA

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    combine the lower-right principal-block operator bound with the Cholesky
    diagonal block equation to bound `R₁₂`.

    This closes the `R₁₂` square-bound branch once the full block matrix has
    the advertised operator-2 certificate. -/
theorem higham13_lemma13_9_R12_rectOpNorm2Le_of_full_cholesky_block
    {r s : ℕ}
    (A : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA : ℝ}
    (hNormA_nonneg : 0 ≤ normA)
    (hA22_block : A22 = fun i j : Fin s => A (Sum.inr i) (Sum.inr j))
    (hA22_chol : A22 =
      fun j k =>
        (∑ i : Fin r, R12 i j * R12 i k) +
          (∑ l : Fin s, R22 l j * R22 l k))
    (hA : finiteOpNorm2Le A normA) :
    rectOpNorm2Le R12 (Real.sqrt normA) :=
  higham13_lemma13_9_R12_rectOpNorm2Le_of_A22_cholesky_block
    A22 R12 R22 hNormA_nonneg hA22_chol
    (higham13_lemma13_9_A22_opNorm2Le_of_full_block_eq A A22 hA22_block hA)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    the upper-left principal block of the inverse matrix inherits an
    operator-2 bound from the full inverse.

    This is the source step `‖A₁₁⁻¹‖₂ ≤ ‖A⁻¹‖₂` in certificate form. -/
theorem higham13_lemma13_9_A11inv_opNorm2Le_of_full_inverse_block
    {r s : ℕ}
    (Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    {normAinv : ℝ}
    (hAinv : finiteOpNorm2Le Ainv normAinv) :
    opNorm2Le (fun i j : Fin r => Ainv (Sum.inl i) (Sum.inl j)) normAinv :=
  opNorm2Le_of_finiteOpNorm2Le _
    (finiteOpNorm2Le_sumInl_principal Ainv hAinv)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-facing equality wrapper for the upper-left inverse principal-block
    operator-2 bound. -/
theorem higham13_lemma13_9_A11inv_opNorm2Le_of_full_inverse_block_eq
    {r s : ℕ}
    (Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A11inv : Fin r → Fin r → ℝ)
    {normAinv : ℝ}
    (hA11inv : A11inv = fun i j : Fin r => Ainv (Sum.inl i) (Sum.inl j))
    (hAinv : finiteOpNorm2Le Ainv normAinv) :
    opNorm2Le A11inv normAinv := by
  rw [hA11inv]
  exact higham13_lemma13_9_A11inv_opNorm2Le_of_full_inverse_block Ainv hAinv

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    the inverse Cholesky block equation gives the `R₁₁⁻¹` square-bound
    operator certificate.

    The equation `A₁₁⁻¹ = R₁₁⁻¹ R₁₁⁻ᵀ` first bounds `R₁₁⁻ᵀ`; the repository
    transpose norm bridge then gives the same bound for `R₁₁⁻¹`. -/
theorem higham13_lemma13_9_R11inv_rectOpNorm2Le_of_A11inv_cholesky_block
    {r : ℕ}
    (A11inv R11inv : Fin r → Fin r → ℝ)
    {normAinv : ℝ}
    (hNormAinv_nonneg : 0 ≤ normAinv)
    (hA11inv : A11inv =
      fun j k => ∑ i : Fin r, R11inv j i * R11inv k i)
    (hA11inv_op : opNorm2Le A11inv normAinv) :
    rectOpNorm2Le R11inv (Real.sqrt normAinv) := by
  have hT :
      rectOpNorm2Le (finiteTranspose R11inv) (Real.sqrt normAinv) := by
    refine higham13_lemma13_9_R12_rectOpNorm2Le_of_A22_cholesky_block
      A11inv (finiteTranspose R11inv) (fun _ _ : Fin r => 0)
      hNormAinv_nonneg ?_ hA11inv_op
    rw [hA11inv]
    ext j k
    simp [finiteTranspose]
  have hTT :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      (finiteTranspose R11inv) (Real.sqrt_nonneg normAinv) hT
  simpa [finiteTranspose] using hTT

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    combine the full inverse principal-block bound with the inverse Cholesky
    block equation to bound `R₁₁⁻¹`. -/
theorem higham13_lemma13_9_R11inv_rectOpNorm2Le_of_full_inverse_cholesky_block
    {r s : ℕ}
    (Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A11inv R11inv : Fin r → Fin r → ℝ)
    {normAinv : ℝ}
    (hNormAinv_nonneg : 0 ≤ normAinv)
    (hA11inv_block :
      A11inv = fun i j : Fin r => Ainv (Sum.inl i) (Sum.inl j))
    (hA11inv_chol : A11inv =
      fun j k => ∑ i : Fin r, R11inv j i * R11inv k i)
    (hAinv : finiteOpNorm2Le Ainv normAinv) :
    rectOpNorm2Le R11inv (Real.sqrt normAinv) :=
  higham13_lemma13_9_R11inv_rectOpNorm2Le_of_A11inv_cholesky_block
    A11inv R11inv hNormAinv_nonneg hA11inv_chol
    (higham13_lemma13_9_A11inv_opNorm2Le_of_full_inverse_block_eq
      Ainv A11inv hA11inv_block hAinv)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    Cholesky block product route for the bound
    `‖A₂₁ A₁₁⁻¹‖₂ ≤ κ₂(A)^{1/2}`.

    If `R₁₂` and `R₁₁⁻¹` have operator-2 certificates and the Cholesky
    condition-number comparison supplies
    `‖R₁₂‖₂ ‖R₁₁⁻¹‖₂ ≤ κ₂(A)^{1/2}`, then the product
    `R₁₂ᵀ R₁₁⁻ᵀ` has the desired operator-2 certificate.  The remaining
    Lemma 13.9 source obligations are the Cholesky block identity
    `A₂₁ A₁₁⁻¹ = R₁₂ᵀ R₁₁⁻ᵀ` and the two condition-number comparisons. -/
theorem higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le
    {r s : ℕ}
    (R12 : Fin r → Fin s → ℝ)
    (R11inv : Fin r → Fin r → ℝ)
    {normR12 normR11inv kappa2A : ℝ}
    (hR12_nonneg : 0 ≤ normR12)
    (hR11inv_nonneg : 0 ≤ normR11inv)
    (hR12 : rectOpNorm2Le R12 normR12)
    (hR11inv : rectOpNorm2Le R11inv normR11inv)
    (hProd : normR12 * normR11inv ≤ Real.sqrt kappa2A) :
    rectOpNorm2Le
      (rectMatMul (finiteTranspose R12) (finiteTranspose R11inv))
      (Real.sqrt kappa2A) := by
  have hR12T : rectOpNorm2Le (finiteTranspose R12) normR12 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le R12 hR12_nonneg hR12
  have hR11invT : rectOpNorm2Le (finiteTranspose R11inv) normR11inv :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      R11inv hR11inv_nonneg hR11inv
  exact rectOpNorm2Le_mono hProd
    (rectOpNorm2Le_rectMatMul
      (finiteTranspose R12) (finiteTranspose R11inv)
      hR12_nonneg hR12T hR11invT)

/-- Nonempty-domain wrapper for the Lemma 13.9 Cholesky product route.

    The nonnegativity assumptions on the rectangular operator radii are derived
    from the two vector-action operator certificates themselves. -/
theorem higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_of_rect_operator_bounds
    {r s : ℕ} [Nonempty (Fin s)] [Nonempty (Fin r)]
    (R12 : Fin r → Fin s → ℝ)
    (R11inv : Fin r → Fin r → ℝ)
    {normR12 normR11inv kappa2A : ℝ}
    (hR12 : rectOpNorm2Le R12 normR12)
    (hR11inv : rectOpNorm2Le R11inv normR11inv)
    (hProd : normR12 * normR11inv ≤ Real.sqrt kappa2A) :
    rectOpNorm2Le
      (rectMatMul (finiteTranspose R12) (finiteTranspose R11inv))
      (Real.sqrt kappa2A) :=
  higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le
    R12 R11inv
    (rectOpNorm2Le_radius_nonneg R12 hR12)
    (rectOpNorm2Le_radius_nonneg R11inv hR11inv)
    hR12 hR11inv hProd

/-- Squared-bound form of
    `higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le`.

    This removes the single product-majorant hypothesis from the Cholesky route
    and replaces it by the squared norm and condition-number inequalities used
    in the source proof of Lemma 13.9. -/
theorem higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_from_square_bounds
    {r s : ℕ}
    (R12 : Fin r → Fin s → ℝ)
    (R11inv : Fin r → Fin r → ℝ)
    {normR12 normR11inv normA normAinv kappa2A : ℝ}
    (hR12_nonneg : 0 ≤ normR12)
    (hR11inv_nonneg : 0 ≤ normR11inv)
    (hR12 : rectOpNorm2Le R12 normR12)
    (hR11inv : rectOpNorm2Le R11inv normR11inv)
    (hNormA_nonneg : 0 ≤ normA)
    (hR12sq : normR12 ^ 2 ≤ normA)
    (hR11invsq : normR11inv ^ 2 ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappa2A) :
    rectOpNorm2Le
      (rectMatMul (finiteTranspose R12) (finiteTranspose R11inv))
      (Real.sqrt kappa2A) :=
  higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le
    R12 R11inv hR12_nonneg hR11inv_nonneg hR12 hR11inv
    (higham13_lemma13_9_product_majorant_from_square_bounds
      hNormA_nonneg hR12sq hR11invsq hkappa)

/-- Nonempty-domain wrapper for the squared-bound Lemma 13.9 Cholesky product
    route.

    The rectangular operator-radius nonnegativity assumptions are derived from
    the supplied `rectOpNorm2Le` certificates.  The source mathematical
    hypotheses are therefore just the squared Cholesky norm bounds and the
    condition-number majorant. -/
theorem higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_from_square_bounds_of_rect_operator_bounds
    {r s : ℕ} [Nonempty (Fin s)] [Nonempty (Fin r)]
    (R12 : Fin r → Fin s → ℝ)
    (R11inv : Fin r → Fin r → ℝ)
    {normR12 normR11inv normA normAinv kappa2A : ℝ}
    (hR12 : rectOpNorm2Le R12 normR12)
    (hR11inv : rectOpNorm2Le R11inv normR11inv)
    (hNormA_nonneg : 0 ≤ normA)
    (hR12sq : normR12 ^ 2 ≤ normA)
    (hR11invsq : normR11inv ^ 2 ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappa2A) :
    rectOpNorm2Le
      (rectMatMul (finiteTranspose R12) (finiteTranspose R11inv))
      (Real.sqrt kappa2A) :=
  higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_from_square_bounds
    R12 R11inv
    (rectOpNorm2Le_radius_nonneg R12 hR12)
    (rectOpNorm2Le_radius_nonneg R11inv hR11inv)
    hR12 hR11inv hNormA_nonneg hR12sq hR11invsq hkappa

/-- Equality-instantiated form of
    `higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le`, for the
    source identity `A₂₁ A₁₁⁻¹ = R₁₂ᵀ R₁₁⁻ᵀ`. -/
theorem higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_of_eq
    {r s : ℕ}
    (A21A11inv : Fin s → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R11inv : Fin r → Fin r → ℝ)
    {normR12 normR11inv kappa2A : ℝ}
    (hA21 :
      A21A11inv = rectMatMul (finiteTranspose R12) (finiteTranspose R11inv))
    (hR12_nonneg : 0 ≤ normR12)
    (hR11inv_nonneg : 0 ≤ normR11inv)
    (hR12 : rectOpNorm2Le R12 normR12)
    (hR11inv : rectOpNorm2Le R11inv normR11inv)
    (hProd : normR12 * normR11inv ≤ Real.sqrt kappa2A) :
    rectOpNorm2Le A21A11inv (Real.sqrt kappa2A) := by
  rw [hA21]
  exact higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le
    R12 R11inv hR12_nonneg hR11inv_nonneg hR12 hR11inv hProd

/-- Squared-bound equality-instantiated form of the Lemma 13.9 Cholesky route. -/
theorem higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_of_eq_from_square_bounds
    {r s : ℕ}
    (A21A11inv : Fin s → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R11inv : Fin r → Fin r → ℝ)
    {normR12 normR11inv normA normAinv kappa2A : ℝ}
    (hA21 :
      A21A11inv = rectMatMul (finiteTranspose R12) (finiteTranspose R11inv))
    (hR12_nonneg : 0 ≤ normR12)
    (hR11inv_nonneg : 0 ≤ normR11inv)
    (hR12 : rectOpNorm2Le R12 normR12)
    (hR11inv : rectOpNorm2Le R11inv normR11inv)
    (hNormA_nonneg : 0 ≤ normA)
    (hR12sq : normR12 ^ 2 ≤ normA)
    (hR11invsq : normR11inv ^ 2 ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappa2A) :
    rectOpNorm2Le A21A11inv (Real.sqrt kappa2A) := by
  rw [hA21]
  exact higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_from_square_bounds
    R12 R11inv hR12_nonneg hR11inv_nonneg hR12 hR11inv
    hNormA_nonneg hR12sq hR11invsq hkappa

/-- Nonempty-domain equality-instantiated squared-bound form of the Lemma 13.9
    Cholesky route. -/
theorem higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_of_eq_from_square_bounds_of_rect_operator_bounds
    {r s : ℕ} [Nonempty (Fin s)] [Nonempty (Fin r)]
    (A21A11inv : Fin s → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R11inv : Fin r → Fin r → ℝ)
    {normR12 normR11inv normA normAinv kappa2A : ℝ}
    (hA21 :
      A21A11inv = rectMatMul (finiteTranspose R12) (finiteTranspose R11inv))
    (hR12 : rectOpNorm2Le R12 normR12)
    (hR11inv : rectOpNorm2Le R11inv normR11inv)
    (hNormA_nonneg : 0 ≤ normA)
    (hR12sq : normR12 ^ 2 ≤ normA)
    (hR11invsq : normR11inv ^ 2 ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappa2A) :
    rectOpNorm2Le A21A11inv (Real.sqrt kappa2A) := by
  rw [hA21]
  exact
    higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_from_square_bounds_of_rect_operator_bounds
      R12 R11inv hR12 hR11inv hNormA_nonneg hR12sq hR11invsq hkappa

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    extract the source block equations from a full sum-indexed Cholesky product
    certificate.

    If `A = RᵀR` on the partition `Fin r ⊕ Fin s` and `R` has the compatible
    upper block form `[[R₁₁,R₁₂],[0,R₂₂]]`, then the lower-right block satisfies
    `A₂₂ = R₁₂ᵀR₁₂ + R₂₂ᵀR₂₂` and the lower-left block satisfies
    `A₂₁ = R₁₂ᵀR₁₁`.  This removes two proof-artifact hypotheses from the
    Lemma 13.9 Cholesky route; it still assumes the block decomposition of the
    Cholesky factor. -/
theorem higham13_lemma13_9_cholesky_block_equations_of_sum_product
    {r s : ℕ}
    (A R : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    (hA22_block : A22 = fun i j : Fin s => A (Sum.inr i) (Sum.inr j))
    (hA21_block : A21 = fun (i : Fin s) (j : Fin r) =>
      A (Sum.inr i) (Sum.inl j))
    (hR11 : ∀ i j, R (Sum.inl i) (Sum.inl j) = R11 i j)
    (hR12 : ∀ i j, R (Sum.inl i) (Sum.inr j) = R12 i j)
    (hR21_zero : ∀ i j, R (Sum.inr i) (Sum.inl j) = 0)
    (hR22 : ∀ i j, R (Sum.inr i) (Sum.inr j) = R22 i j)
    (hProd : ∀ i j,
      ∑ k : Fin r ⊕ Fin s, R k i * R k j = A i j) :
    (A22 =
      fun j k =>
        (∑ i : Fin r, R12 i j * R12 i k) +
          (∑ l : Fin s, R22 l j * R22 l k))
    ∧ A21 = rectMatMul (finiteTranspose R12) R11 := by
  constructor
  · ext j k
    calc
      A22 j k = A (Sum.inr j) (Sum.inr k) := by rw [hA22_block]
      _ = (∑ i : Fin r, R12 i j * R12 i k) +
          (∑ l : Fin s, R22 l j * R22 l k) := by
            rw [← hProd (Sum.inr j) (Sum.inr k)]
            rw [Fintype.sum_sum_type]
            simp [hR12, hR22]
  · ext i j
    calc
      A21 i j = A (Sum.inr i) (Sum.inl j) := by rw [hA21_block]
      _ = rectMatMul (finiteTranspose R12) R11 i j := by
            rw [← hProd (Sum.inr i) (Sum.inl j)]
            rw [Fintype.sum_sum_type]
            simp [rectMatMul, finiteTranspose, hR11, hR12, hR21_zero]

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    extract the leading Cholesky block equation from a full sum-indexed product
    certificate.

    If `A = RᵀR` on the partition `Fin r ⊕ Fin s` and the lower-left Cholesky
    block is zero, then the leading block satisfies `A₁₁ = R₁₁ᵀR₁₁`. -/
theorem higham13_lemma13_9_cholesky_leading_block_eq_of_sum_product
    {r s : ℕ}
    (A R : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (R11 : Fin r → Fin r → ℝ)
    (hR11 : ∀ i j, R (Sum.inl i) (Sum.inl j) = R11 i j)
    (hR21_zero : ∀ i j, R (Sum.inr i) (Sum.inl j) = 0)
    (hProd : ∀ i j,
      ∑ k : Fin r ⊕ Fin s, R k i * R k j = A i j) :
    (fun i j : Fin r => A (Sum.inl i) (Sum.inl j)) =
      rectMatMul (finiteTranspose R11) R11 := by
  ext i j
  calc
    A (Sum.inl i) (Sum.inl j)
        = ∑ k : Fin r ⊕ Fin s,
            R k (Sum.inl i) * R k (Sum.inl j) := by
            rw [hProd]
    _ = rectMatMul (finiteTranspose R11) R11 i j := by
            rw [Fintype.sum_sum_type]
            simp [rectMatMul, finiteTranspose, hR11, hR21_zero]

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    reindex a Cholesky product certificate through a finite equivalence.

    This is the bridge needed when a Cholesky existence theorem supplies
    `A = RᵀR` on a finite index type such as `Fin n`, while the block proof
    route uses the partition index `Fin r ⊕ Fin s`. -/
theorem higham13_lemma13_9_sum_product_of_equiv_product
    {σ ι : Type*} [Fintype σ] [Fintype ι]
    (e : σ ≃ ι)
    (A R : ι → ι → ℝ)
    (hProd : ∀ i j, ∑ k : ι, R k i * R k j = A i j) :
    ∀ i j : σ,
      ∑ k : σ, R (e k) (e i) * R (e k) (e j) = A (e i) (e j) := by
  intro i j
  calc
    (∑ k : σ, R (e k) (e i) * R (e k) (e j))
        = ∑ k : ι, R k (e i) * R k (e j) := by
          rw [← Fintype.sum_equiv e]
          intro x
          rfl
    _ = A (e i) (e j) := hProd (e i) (e j)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    extract the source Cholesky block equations from a product certificate
    after reindexing through a finite equivalence.

    This specializes
    `higham13_lemma13_9_cholesky_block_equations_of_sum_product` to the common
    case where the Cholesky factor is indexed on another finite type and then
    pulled back to the block partition. -/
theorem higham13_lemma13_9_cholesky_block_equations_of_equiv_product
    {r s : ℕ} {ι : Type*} [Fintype ι]
    (e : (Fin r ⊕ Fin s) ≃ ι)
    (A R : ι → ι → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    (hA22_block : A22 =
      fun i j : Fin s => A (e (Sum.inr i)) (e (Sum.inr j)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) => A (e (Sum.inr i)) (e (Sum.inl j)))
    (hR11 : ∀ i j, R (e (Sum.inl i)) (e (Sum.inl j)) = R11 i j)
    (hR12 : ∀ i j, R (e (Sum.inl i)) (e (Sum.inr j)) = R12 i j)
    (hR21_zero : ∀ i j, R (e (Sum.inr i)) (e (Sum.inl j)) = 0)
    (hR22 : ∀ i j, R (e (Sum.inr i)) (e (Sum.inr j)) = R22 i j)
    (hProd : ∀ i j, ∑ k : ι, R k i * R k j = A i j) :
    (A22 =
      fun j k =>
        (∑ i : Fin r, R12 i j * R12 i k) +
          (∑ l : Fin s, R22 l j * R22 l k))
    ∧ A21 = rectMatMul (finiteTranspose R12) R11 := by
  exact
    higham13_lemma13_9_cholesky_block_equations_of_sum_product
      (fun i j : Fin r ⊕ Fin s => A (e i) (e j))
      (fun i j : Fin r ⊕ Fin s => R (e i) (e j))
      A22 A21 R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR21_zero hR22
      (higham13_lemma13_9_sum_product_of_equiv_product e A R hProd)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    reindexed leading-block Cholesky identity `A₁₁ = R₁₁ᵀR₁₁`. -/
theorem higham13_lemma13_9_cholesky_leading_block_eq_of_equiv_product
    {r s : ℕ} {ι : Type*} [Fintype ι]
    (e : (Fin r ⊕ Fin s) ≃ ι)
    (A R : ι → ι → ℝ)
    (R11 : Fin r → Fin r → ℝ)
    (hR11 : ∀ i j, R (e (Sum.inl i)) (e (Sum.inl j)) = R11 i j)
    (hR21_zero : ∀ i j, R (e (Sum.inr i)) (e (Sum.inl j)) = 0)
    (hProd : ∀ i j, ∑ k : ι, R k i * R k j = A i j) :
    (fun i j : Fin r => A (e (Sum.inl i)) (e (Sum.inl j))) =
      rectMatMul (finiteTranspose R11) R11 := by
  exact
    higham13_lemma13_9_cholesky_leading_block_eq_of_sum_product
      (fun i j : Fin r ⊕ Fin s => A (e i) (e j))
      (fun i j : Fin r ⊕ Fin s => R (e i) (e j))
      R11 hR11 hR21_zero
      (higham13_lemma13_9_sum_product_of_equiv_product e A R hProd)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    exact Cholesky block identity
    `A₂₁ A₁₁⁻¹ = R₁₂ᵀ R₁₁⁻ᵀ`.

    This theorem proves the algebraic identity from the source block equations
    `A₂₁ = R₁₂ᵀ R₁₁`, `A₁₁⁻¹ = R₁₁⁻¹ R₁₁⁻ᵀ`, and the right-inverse relation
    `R₁₁ R₁₁⁻¹ = I`.  It is the exact-identity part of the book's Lemma 13.9
    Cholesky proof; the remaining open work is deriving the operator-2
    condition-number majorants from SPD Cholesky data. -/
theorem higham13_lemma13_9_cholesky_block_identity
    {r s : ℕ}
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (hA21 : A21 = rectMatMul (finiteTranspose R12) R11)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv) :
    rectMatMul A21 A11inv =
      rectMatMul (finiteTranspose R12) (finiteTranspose R11inv) := by
  rw [hA21, hA11inv]
  calc
    rectMatMul (rectMatMul (finiteTranspose R12) R11)
        (rectMatMul R11inv (finiteTranspose R11inv))
        = rectMatMul (finiteTranspose R12)
            (rectMatMul R11 (rectMatMul R11inv (finiteTranspose R11inv))) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul (finiteTranspose R12)
          (rectMatMul (rectMatMul R11 R11inv) (finiteTranspose R11inv)) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul (finiteTranspose R12)
          (rectMatMul (idMatrix r) (finiteTranspose R11inv)) := by
            have hRR : rectMatMul R11 R11inv = idMatrix r := by
              ext i j
              exact hRight i j
            rw [hRR]
    _ = rectMatMul (finiteTranspose R12) (finiteTranspose R11inv) := by
            rw [rectMatMul_id_left]

/-- Lemma 13.9 Cholesky route from the source block equations plus squared
    norm/condition-number majorants.

    This combines the exact block identity
    `A₂₁A₁₁⁻¹ = R₁₂ᵀR₁₁⁻ᵀ` with the squared-bound scalar bridge above.  The
    remaining source-level SPD work is to prove the operator certificates and
    the two squared norm/condition-number majorants from the SPD Cholesky
    factorization itself. -/
theorem higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_block_eqs
    {r s : ℕ}
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    {normR12 normR11inv normA normAinv kappa2A : ℝ}
    (hA21 : A21 = rectMatMul (finiteTranspose R12) R11)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hR12_nonneg : 0 ≤ normR12)
    (hR11inv_nonneg : 0 ≤ normR11inv)
    (hR12 : rectOpNorm2Le R12 normR12)
    (hR11inv : rectOpNorm2Le R11inv normR11inv)
    (hNormA_nonneg : 0 ≤ normA)
    (hR12sq : normR12 ^ 2 ≤ normA)
    (hR11invsq : normR11inv ^ 2 ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappa2A) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt kappa2A) :=
  higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_of_eq_from_square_bounds
    (rectMatMul A21 A11inv) R12 R11inv
    (higham13_lemma13_9_cholesky_block_identity
      A21 A11inv R11 R11inv R12 hA21 hA11inv hRight)
    hR12_nonneg hR11inv_nonneg hR12 hR11inv
    hNormA_nonneg hR12sq hR11invsq hkappa

/-- Nonempty-domain wrapper for the Lemma 13.9 Cholesky route from source
    block equations.

    This is the same block-equation route as
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_block_eqs`, but the
    rectangular operator-radius nonnegativity assumptions are derived from the
    supplied `R12` and `R11inv` operator certificates. -/
theorem higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_block_eqs_of_rect_operator_bounds
    {r s : ℕ} [Nonempty (Fin s)] [Nonempty (Fin r)]
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    {normR12 normR11inv normA normAinv kappa2A : ℝ}
    (hA21 : A21 = rectMatMul (finiteTranspose R12) R11)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hR12 : rectOpNorm2Le R12 normR12)
    (hR11inv : rectOpNorm2Le R11inv normR11inv)
    (hNormA_nonneg : 0 ≤ normA)
    (hR12sq : normR12 ^ 2 ≤ normA)
    (hR11invsq : normR11inv ^ 2 ≤ normAinv)
    (hkappa : normA * normAinv ≤ kappa2A) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt kappa2A) :=
  higham13_lemma13_9_cholesky_route_transpose_rectOpNorm2Le_of_eq_from_square_bounds_of_rect_operator_bounds
    (rectMatMul A21 A11inv) R12 R11inv
    (higham13_lemma13_9_cholesky_block_identity
      A21 A11inv R11 R11inv R12 hA21 hA11inv hRight)
    hR12 hR11inv hNormA_nonneg hR12sq hR11invsq hkappa

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    Cholesky route from full `A` and `A⁻¹` operator certificates.

    This combines the exact Cholesky block identity, the `R₁₂` square-bound
    branch from the lower-right block of `A`, the `R₁₁⁻¹` square-bound branch
    from the upper-left block of `A⁻¹`, and the condition-number majorant
    `‖A‖₂ ‖A⁻¹‖₂ ≤ κ₂(A)`. -/
theorem higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_full_operator_bounds
    {r s : ℕ}
    (A Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv kappa2A : ℝ}
    (hNormA_nonneg : 0 ≤ normA)
    (hNormAinv_nonneg : 0 ≤ normAinv)
    (hA22_block : A22 = fun i j : Fin s => A (Sum.inr i) (Sum.inr j))
    (hA22_chol : A22 =
      fun j k =>
        (∑ i : Fin r, R12 i j * R12 i k) +
          (∑ l : Fin s, R22 l j * R22 l k))
    (hA11inv_block :
      A11inv = fun i j : Fin r => Ainv (Sum.inl i) (Sum.inl j))
    (hA21 : A21 = rectMatMul (finiteTranspose R12) R11)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hA : finiteOpNorm2Le A normA)
    (hAinv : finiteOpNorm2Le Ainv normAinv)
    (hkappa : normA * normAinv ≤ kappa2A) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt kappa2A) := by
  have hR12 :
      rectOpNorm2Le R12 (Real.sqrt normA) :=
    higham13_lemma13_9_R12_rectOpNorm2Le_of_full_cholesky_block
      A A22 R12 R22 hNormA_nonneg hA22_block hA22_chol hA
  have hA11inv_chol :
      A11inv = fun j k => ∑ i : Fin r, R11inv j i * R11inv k i := by
    rw [hA11inv]
    ext j k
    simp [rectMatMul, finiteTranspose]
  have hR11inv :
      rectOpNorm2Le R11inv (Real.sqrt normAinv) :=
    higham13_lemma13_9_R11inv_rectOpNorm2Le_of_full_inverse_cholesky_block
      Ainv A11inv R11inv hNormAinv_nonneg hA11inv_block hA11inv_chol hAinv
  have hR12sq : (Real.sqrt normA) ^ 2 ≤ normA := by
    rw [Real.sq_sqrt hNormA_nonneg]
  have hR11invsq : (Real.sqrt normAinv) ^ 2 ≤ normAinv := by
    rw [Real.sq_sqrt hNormAinv_nonneg]
  exact higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_block_eqs
    A21 A11inv R11 R11inv R12
    hA21 hA11inv hRight
    (Real.sqrt_nonneg normA) (Real.sqrt_nonneg normAinv)
    hR12 hR11inv hNormA_nonneg hR12sq hR11invsq hkappa

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    nonempty-dimension wrapper for the full-operator Cholesky certificate.

    The explicit nonnegativity assumptions on `‖A‖₂` and `‖A⁻¹‖₂` are derived
    from the vector-action operator-2 certificates themselves.  The remaining
    hypotheses are the source Cholesky block equations and the condition-number
    majorant `‖A‖₂ ‖A⁻¹‖₂ ≤ κ₂(A)`. -/
theorem higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_nonempty_full_operator_bounds
    {r s : ℕ} [Nonempty (Fin r ⊕ Fin s)]
    (A Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv kappa2A : ℝ}
    (hA22_block : A22 = fun i j : Fin s => A (Sum.inr i) (Sum.inr j))
    (hA22_chol : A22 =
      fun j k =>
        (∑ i : Fin r, R12 i j * R12 i k) +
          (∑ l : Fin s, R22 l j * R22 l k))
    (hA11inv_block :
      A11inv = fun i j : Fin r => Ainv (Sum.inl i) (Sum.inl j))
    (hA21 : A21 = rectMatMul (finiteTranspose R12) R11)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hA : finiteOpNorm2Le A normA)
    (hAinv : finiteOpNorm2Le Ainv normAinv)
    (hkappa : normA * normAinv ≤ kappa2A) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt kappa2A) :=
  higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_full_operator_bounds
    A Ainv A22 A21 A11inv R11 R11inv R12 R22
    (finiteOpNorm2Le_radius_nonneg A hA)
    (finiteOpNorm2Le_radius_nonneg Ainv hAinv)
    hA22_block hA22_chol hA11inv_block hA21 hA11inv hRight hA hAinv hkappa

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    nonempty full-operator Cholesky certificate with the source
    condition-number product expanded directly.

    This removes the separate majorant hypothesis
    `‖A‖₂ * ‖A⁻¹‖₂ ≤ κ₂(A)` when the displayed condition number is represented
    by its defining product.  The remaining hypotheses are still the source
    Cholesky block equations, a right-inverse equation for `R₁₁`, and
    full-operator certificates for `A` and `A⁻¹`; bare-SPD Cholesky existence is
    not assumed here. -/
theorem higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_nonempty_full_operator_bounds_kappa_product
    {r s : ℕ} [Nonempty (Fin r ⊕ Fin s)]
    (A Ainv : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 = fun i j : Fin s => A (Sum.inr i) (Sum.inr j))
    (hA22_chol : A22 =
      fun j k =>
        (∑ i : Fin r, R12 i j * R12 i k) +
          (∑ l : Fin s, R22 l j * R22 l k))
    (hA11inv_block :
      A11inv = fun i j : Fin r => Ainv (Sum.inl i) (Sum.inl j))
    (hA21 : A21 = rectMatMul (finiteTranspose R12) R11)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hA : finiteOpNorm2Le A normA)
    (hAinv : finiteOpNorm2Le Ainv normAinv) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) :=
  higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_nonempty_full_operator_bounds
    A Ainv A22 A21 A11inv R11 R11inv R12 R22
    hA22_block hA22_chol hA11inv_block hA21 hA11inv hRight hA hAinv
    (le_refl (normA * normAinv))

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    full-operator Cholesky route with the `A₂₂` and `A₂₁` block equations
    extracted from a single sum-indexed product certificate.

    This theorem advances the SPD route by replacing the separate hypotheses
    `A₂₂ = R₁₂ᵀR₁₂ + R₂₂ᵀR₂₂` and `A₂₁ = R₁₂ᵀR₁₁` with the full product
    certificate `A = RᵀR` plus the displayed block form of `R`.  It is still a
    certificate theorem: deriving these data from the bare SPD hypothesis and
    Cholesky existence remains the open Lemma 13.9 row. -/
theorem higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_sum_cholesky_product
    {r s : ℕ} [Nonempty (Fin r ⊕ Fin s)]
    (A Ainv R : (Fin r ⊕ Fin s) → (Fin r ⊕ Fin s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 = fun i j : Fin s => A (Sum.inr i) (Sum.inr j))
    (hA21_block : A21 = fun (i : Fin s) (j : Fin r) =>
      A (Sum.inr i) (Sum.inl j))
    (hA11inv_block :
      A11inv = fun i j : Fin r => Ainv (Sum.inl i) (Sum.inl j))
    (hR11 : ∀ i j, R (Sum.inl i) (Sum.inl j) = R11 i j)
    (hR12 : ∀ i j, R (Sum.inl i) (Sum.inr j) = R12 i j)
    (hR21_zero : ∀ i j, R (Sum.inr i) (Sum.inl j) = 0)
    (hR22 : ∀ i j, R (Sum.inr i) (Sum.inr j) = R22 i j)
    (hProd : ∀ i j,
      ∑ k : Fin r ⊕ Fin s, R k i * R k j = A i j)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hA : finiteOpNorm2Le A normA)
    (hAinv : finiteOpNorm2Le Ainv normAinv) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  obtain ⟨hA22_chol, hA21⟩ :=
    higham13_lemma13_9_cholesky_block_equations_of_sum_product
      A R A22 A21 R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR21_zero hR22 hProd
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_nonempty_full_operator_bounds_kappa_product
      A Ainv A22 A21 A11inv R11 R11inv R12 R22
      hA22_block hA22_chol hA11inv_block hA21 hA11inv hRight hA hAinv

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    full-operator Cholesky route after reindexing an arbitrary finite Cholesky
    product certificate to the block partition.

    This is the equivalence-indexed version of
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_sum_cholesky_product`.
    It still assumes the pulled-back full `A` and `A⁻¹` operator certificates
    and the block form of `R`; proving those from bare SPD remains open. -/
theorem higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_equiv_cholesky_product
    {r s : ℕ} {ι : Type*} [Fintype ι] [Nonempty (Fin r ⊕ Fin s)]
    (e : (Fin r ⊕ Fin s) ≃ ι)
    (A Ainv R : ι → ι → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s => A (e (Sum.inr i)) (e (Sum.inr j)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) => A (e (Sum.inr i)) (e (Sum.inl j)))
    (hA11inv_block :
      A11inv = fun i j : Fin r => Ainv (e (Sum.inl i)) (e (Sum.inl j)))
    (hR11 : ∀ i j, R (e (Sum.inl i)) (e (Sum.inl j)) = R11 i j)
    (hR12 : ∀ i j, R (e (Sum.inl i)) (e (Sum.inr j)) = R12 i j)
    (hR21_zero : ∀ i j, R (e (Sum.inr i)) (e (Sum.inl j)) = 0)
    (hR22 : ∀ i j, R (e (Sum.inr i)) (e (Sum.inr j)) = R22 i j)
    (hProd : ∀ i j, ∑ k : ι, R k i * R k j = A i j)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hA : finiteOpNorm2Le
      (fun i j : Fin r ⊕ Fin s => A (e i) (e j)) normA)
    (hAinv : finiteOpNorm2Le
      (fun i j : Fin r ⊕ Fin s => Ainv (e i) (e j)) normAinv) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_sum_cholesky_product
      (fun i j : Fin r ⊕ Fin s => A (e i) (e j))
      (fun i j : Fin r ⊕ Fin s => Ainv (e i) (e j))
      (fun i j : Fin r ⊕ Fin s => R (e i) (e j))
      A22 A21 A11inv R11 R11inv R12 R22
      hA22_block hA21_block hA11inv_block
      hR11 hR12 hR21_zero hR22
      (higham13_lemma13_9_sum_product_of_equiv_product e A R hProd)
      hA11inv hRight hA hAinv

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    lower-left zero block of a Cholesky factor after an order-compatible
    reindexing.

    A repository `CholeskyFactSpec` supplies upper triangularity in the form
    `R i j = 0` when `j < i`.  If all leading-block indices precede all trailing
    block indices through the equivalence `e`, then the pulled-back Cholesky
    factor has zero lower-left block. -/
theorem higham13_lemma13_9_cholesky_lower_left_zero_of_order_equiv
    {r s n : ℕ}
    (e : (Fin r ⊕ Fin s) ≃ Fin n)
    {A R : Fin n → Fin n → ℝ}
    (hChol : CholeskyFactSpec n A R)
    (hOrder : ∀ (i : Fin s) (j : Fin r),
      (e (Sum.inl j)).val < (e (Sum.inr i)).val) :
    ∀ i j, R (e (Sum.inr i)) (e (Sum.inl j)) = 0 := by
  intro i j
  exact hChol.R_upper (e (Sum.inr i)) (e (Sum.inl j)) (hOrder i j)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    extract the source Cholesky block equations from a `CholeskyFactSpec`.

    Compared with
    `higham13_lemma13_9_cholesky_block_equations_of_equiv_product`, this theorem
    replaces the separate lower-left-zero and product-certificate hypotheses by
    the repository Cholesky specification plus the order condition that the
    leading block precedes the trailing block. -/
theorem higham13_lemma13_9_cholesky_block_equations_of_cholesky_fact_equiv
    {r s n : ℕ}
    (e : (Fin r ⊕ Fin s) ≃ Fin n)
    (A R : Fin n → Fin n → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    (hA22_block : A22 =
      fun i j : Fin s => A (e (Sum.inr i)) (e (Sum.inr j)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) => A (e (Sum.inr i)) (e (Sum.inl j)))
    (hR11 : ∀ i j, R (e (Sum.inl i)) (e (Sum.inl j)) = R11 i j)
    (hR12 : ∀ i j, R (e (Sum.inl i)) (e (Sum.inr j)) = R12 i j)
    (hR22 : ∀ i j, R (e (Sum.inr i)) (e (Sum.inr j)) = R22 i j)
    (hChol : CholeskyFactSpec n A R)
    (hOrder : ∀ (i : Fin s) (j : Fin r),
      (e (Sum.inl j)).val < (e (Sum.inr i)).val) :
    (A22 =
      fun j k =>
        (∑ i : Fin r, R12 i j * R12 i k) +
          (∑ l : Fin s, R22 l j * R22 l k))
    ∧ A21 = rectMatMul (finiteTranspose R12) R11 := by
  exact
    higham13_lemma13_9_cholesky_block_equations_of_equiv_product
      e A R A22 A21 R11 R12 R22
      hA22_block hA21_block hR11 hR12
      (higham13_lemma13_9_cholesky_lower_left_zero_of_order_equiv
        e hChol hOrder)
      hR22 hChol.product_eq

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    extract the leading-block Cholesky identity from a `CholeskyFactSpec`. -/
theorem higham13_lemma13_9_cholesky_leading_block_eq_of_cholesky_fact_equiv
    {r s n : ℕ}
    (e : (Fin r ⊕ Fin s) ≃ Fin n)
    (A R : Fin n → Fin n → ℝ)
    (R11 : Fin r → Fin r → ℝ)
    (hR11 : ∀ i j, R (e (Sum.inl i)) (e (Sum.inl j)) = R11 i j)
    (hChol : CholeskyFactSpec n A R)
    (hOrder : ∀ (i : Fin s) (j : Fin r),
      (e (Sum.inl j)).val < (e (Sum.inr i)).val) :
    (fun i j : Fin r => A (e (Sum.inl i)) (e (Sum.inl j))) =
      rectMatMul (finiteTranspose R11) R11 := by
  exact
    higham13_lemma13_9_cholesky_leading_block_eq_of_equiv_product
      e A R R11 hR11
      (higham13_lemma13_9_cholesky_lower_left_zero_of_order_equiv
        e hChol hOrder)
      hChol.product_eq

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    SPD supplies a Cholesky factor whose pulled-back blocks satisfy the source
    block equations.

    This is still not the final Lemma 13.9 theorem, because the source-level
    operator certificates for `A`, `A⁻¹`, and `A₁₁⁻¹` remain separate.  It does,
    however, connect bare SPD and repository Cholesky existence to the two
    Cholesky block equations used in the existing route. -/
theorem higham13_lemma13_9_cholesky_block_equations_exists_of_spd_equiv
    {r s n : ℕ}
    (e : (Fin r ⊕ Fin s) ≃ Fin n)
    (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A)
    (hOrder : ∀ (i : Fin s) (j : Fin r),
      (e (Sum.inl j)).val < (e (Sum.inr i)).val) :
    ∃ (R : Fin n → Fin n → ℝ)
      (R11 : Fin r → Fin r → ℝ)
      (R12 : Fin r → Fin s → ℝ)
      (R22 : Fin s → Fin s → ℝ),
      CholeskyFactSpec n A R ∧
      ((fun j k : Fin s => A (e (Sum.inr j)) (e (Sum.inr k))) =
        fun j k =>
          (∑ i : Fin r, R12 i j * R12 i k) +
            (∑ l : Fin s, R22 l j * R22 l k)) ∧
      ((fun (i : Fin s) (j : Fin r) =>
          A (e (Sum.inr i)) (e (Sum.inl j))) =
        rectMatMul (finiteTranspose R12) R11) := by
  obtain ⟨R, hChol⟩ := cholesky_existence n A hSPD
  refine
    ⟨R,
      (fun i j => R (e (Sum.inl i)) (e (Sum.inl j))),
      (fun i j => R (e (Sum.inl i)) (e (Sum.inr j))),
      (fun i j => R (e (Sum.inr i)) (e (Sum.inr j))),
      hChol, ?_⟩
  exact
    higham13_lemma13_9_cholesky_block_equations_of_cholesky_fact_equiv
      e A R
      (fun j k : Fin s => A (e (Sum.inr j)) (e (Sum.inr k)))
      (fun (i : Fin s) (j : Fin r) =>
        A (e (Sum.inr i)) (e (Sum.inl j)))
      (fun i j => R (e (Sum.inl i)) (e (Sum.inl j)))
      (fun i j => R (e (Sum.inl i)) (e (Sum.inr j)))
      (fun i j => R (e (Sum.inr i)) (e (Sum.inr j)))
      rfl rfl
      (by intro i j; rfl)
      (by intro i j; rfl)
      (by intro i j; rfl)
      hChol hOrder

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    full-operator route from a repository `CholeskyFactSpec`.

    This replaces the explicit product and lower-left-zero hypotheses of the
    equivalence-indexed route by the Cholesky specification and the order
    condition on the block partition.  The theorem remains a certificate result:
    the full `A`/`A⁻¹` operator bounds and the `A₁₁⁻¹ = R₁₁⁻¹R₁₁⁻ᵀ` certificate
    are still explicit hypotheses. -/
theorem higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_equiv
    {r s n : ℕ} [Nonempty (Fin r ⊕ Fin s)]
    (e : (Fin r ⊕ Fin s) ≃ Fin n)
    (A Ainv R : Fin n → Fin n → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s => A (e (Sum.inr i)) (e (Sum.inr j)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) => A (e (Sum.inr i)) (e (Sum.inl j)))
    (hA11inv_block :
      A11inv = fun i j : Fin r => Ainv (e (Sum.inl i)) (e (Sum.inl j)))
    (hR11 : ∀ i j, R (e (Sum.inl i)) (e (Sum.inl j)) = R11 i j)
    (hR12 : ∀ i j, R (e (Sum.inl i)) (e (Sum.inr j)) = R12 i j)
    (hR22 : ∀ i j, R (e (Sum.inr i)) (e (Sum.inr j)) = R22 i j)
    (hChol : CholeskyFactSpec n A R)
    (hOrder : ∀ (i : Fin s) (j : Fin r),
      (e (Sum.inl j)).val < (e (Sum.inr i)).val)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hA : finiteOpNorm2Le
      (fun i j : Fin r ⊕ Fin s => A (e i) (e j)) normA)
    (hAinv : finiteOpNorm2Le
      (fun i j : Fin r ⊕ Fin s => Ainv (e i) (e j)) normAinv) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_equiv_cholesky_product
      e A Ainv R A22 A21 A11inv R11 R11inv R12 R22
      hA22_block hA21_block hA11inv_block hR11 hR12
      (higham13_lemma13_9_cholesky_lower_left_zero_of_order_equiv
        e hChol hOrder)
      hR22 hChol.product_eq hA11inv hRight hA hAinv

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    in the standard block ordering `Fin r ⊕ Fin s ≃ Fin (r+s)`, every leading
    block index precedes every trailing block index. -/
theorem higham13_lemma13_9_finSumFinEquiv_leading_lt_trailing
    {r s : ℕ} (i : Fin s) (j : Fin r) :
    (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)).val <
      (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s)).val := by
  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  simp [Fin.castAdd, Fin.natAdd]
  omega

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-standard `Fin (r+s)` form of the `CholeskyFactSpec` block-equation
    extraction.

    This is the specialization of
    `higham13_lemma13_9_cholesky_block_equations_of_cholesky_fact_equiv` to
    Mathlib's canonical block ordering `finSumFinEquiv`; the order side
    condition is discharged by
    `higham13_lemma13_9_finSumFinEquiv_leading_lt_trailing`. -/
theorem higham13_lemma13_9_cholesky_block_equations_of_cholesky_fact_fin_sum
    {r s : ℕ}
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R) :
    (A22 =
      fun j k =>
        (∑ i : Fin r, R12 i j * R12 i k) +
          (∑ l : Fin s, R22 l j * R22 l k))
    ∧ A21 = rectMatMul (finiteTranspose R12) R11 := by
  exact
    higham13_lemma13_9_cholesky_block_equations_of_cholesky_fact_equiv
      finSumFinEquiv A R A22 A21 R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol
      higham13_lemma13_9_finSumFinEquiv_leading_lt_trailing

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-standard `Fin (r+s)` leading-block Cholesky identity
    `A₁₁ = R₁₁ᵀR₁₁`. -/
theorem higham13_lemma13_9_cholesky_leading_block_eq_of_cholesky_fact_fin_sum
    {r s : ℕ}
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (R11 : Fin r → Fin r → ℝ)
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hChol : CholeskyFactSpec (r + s) A R) :
    (fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))) =
      rectMatMul (finiteTranspose R11) R11 := by
  exact
    higham13_lemma13_9_cholesky_leading_block_eq_of_cholesky_fact_equiv
      finSumFinEquiv A R R11 hR11 hChol
      higham13_lemma13_9_finSumFinEquiv_leading_lt_trailing

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    SPD supplies a standard-ordered Cholesky factor whose pulled-back blocks
    satisfy the source equations. -/
theorem higham13_lemma13_9_cholesky_block_equations_exists_of_spd_fin_sum
    {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hSPD : IsSymPosDef (r + s) A) :
    ∃ (R : Fin (r + s) → Fin (r + s) → ℝ)
      (R11 : Fin r → Fin r → ℝ)
      (R12 : Fin r → Fin s → ℝ)
      (R22 : Fin s → Fin s → ℝ),
      CholeskyFactSpec (r + s) A R ∧
      ((fun j k : Fin s =>
          A (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))
            (finSumFinEquiv (Sum.inr k : Fin r ⊕ Fin s))) =
        fun j k =>
          (∑ i : Fin r, R12 i j * R12 i k) +
            (∑ l : Fin s, R22 l j * R22 l k)) ∧
      ((fun (i : Fin s) (j : Fin r) =>
          A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
            (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))) =
        rectMatMul (finiteTranspose R12) R11) := by
  exact
    higham13_lemma13_9_cholesky_block_equations_exists_of_spd_equiv
      finSumFinEquiv A hSPD
      higham13_lemma13_9_finSumFinEquiv_leading_lt_trailing

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-standard `Fin (r+s)` full-operator route from a repository
    `CholeskyFactSpec`.

    This removes both the arbitrary-equivalence parameter and the order
    hypothesis from
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_equiv`
    when the source partition is represented by Mathlib's standard
    `finSumFinEquiv`. -/
theorem higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum
    {r s : ℕ} [Nonempty (Fin r ⊕ Fin s)]
    (A Ainv R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA11inv_block : A11inv =
      fun i j : Fin r =>
        Ainv (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hA : finiteOpNorm2Le
      (fun i j : Fin r ⊕ Fin s => A (finSumFinEquiv i) (finSumFinEquiv j))
      normA)
    (hAinv : finiteOpNorm2Le
      (fun i j : Fin r ⊕ Fin s => Ainv (finSumFinEquiv i) (finSumFinEquiv j))
      normAinv) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_equiv
      finSumFinEquiv A Ainv R A22 A21 A11inv R11 R11inv R12 R22
      hA22_block hA21_block hA11inv_block hR11 hR12 hR22 hChol
      higham13_lemma13_9_finSumFinEquiv_leading_lt_trailing
      hA11inv hRight hA hAinv

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    standard `Fin (r+s)` Cholesky route from full operator certificates.

    This is the same source-standard route as
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum`,
    but it accepts ordinary full `Fin (r+s)` operator-2 certificates for `A`
    and `A⁻¹`.  The conversion to the pulled-back `Fin r ⊕ Fin s` surface is
    handled by `finiteOpNorm2Le_reindex_equiv`.  The remaining non-source-free
    certificate is still the Cholesky principal inverse identity
    `A₁₁⁻¹ = R₁₁⁻¹ R₁₁⁻ᵀ`. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_full_operator
    {r s : ℕ} [Nonempty (Fin r ⊕ Fin s)]
    (A Ainv R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA11inv_block : A11inv =
      fun i j : Fin r =>
        Ainv (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hA : finiteOpNorm2Le A normA)
    (hAinv : finiteOpNorm2Le Ainv normAinv) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum
      A Ainv R A22 A21 A11inv R11 R11inv R12 R22
      hA22_block hA21_block hA11inv_block hR11 hR12 hR22 hChol
      hA11inv hRight
      (finiteOpNorm2Le_reindex_equiv finSumFinEquiv A hA)
      (finiteOpNorm2Le_reindex_equiv finSumFinEquiv Ainv hAinv)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    standard Cholesky route from the repository `opNorm2Le` certificates.

    This is a source-facing convenience wrapper around
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_full_operator`.
    It accepts the repository's usual `Fin (r+s)` operator-2 predicate for the
    full matrix and inverse, then converts it to the generic finite predicate
    with `finiteOpNorm2Le_of_opNorm2Le`. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_opNorm2
    {r s : ℕ} [Nonempty (Fin r ⊕ Fin s)]
    (A Ainv R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hA11inv_block : A11inv =
      fun i j : Fin r =>
        Ainv (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hA : opNorm2Le A normA)
    (hAinv : opNorm2Le Ainv normAinv) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_full_operator
      A Ainv R A22 A21 A11inv R11 R11inv R12 R22
      hA22_block hA21_block hA11inv_block hR11 hR12 hR22 hChol
      hA11inv hRight
      (finiteOpNorm2Le_of_opNorm2Le A hA)
      (finiteOpNorm2Le_of_opNorm2Le Ainv hAinv)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-standard Cholesky route from a principal-inverse operator
    certificate.

    This is the source-aligned variant of the full-operator wrappers above:
    it uses an operator-2 certificate for the actual leading-principal inverse
    `A₁₁⁻¹`, together with the Cholesky identity
    `A₁₁⁻¹ = R₁₁⁻¹ R₁₁⁻ᵀ`.  It intentionally does not identify `A₁₁⁻¹` with
    the upper-left block of the full inverse matrix, which is not the general
    SPD source statement. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_principal_inverse
    {r s : ℕ} [Nonempty (Fin r)]
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 R11inv : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv : A11inv = rectMatMul R11inv (finiteTranspose R11inv))
    (hRight : IsRightInverse r R11 R11inv)
    (hA : opNorm2Le A normA)
    (hA11inv_op : opNorm2Le A11inv normAinv) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  classical
  let i0 : Fin r := Classical.choice (inferInstance : Nonempty (Fin r))
  haveI : Nonempty (Fin (r + s)) :=
    ⟨finSumFinEquiv (Sum.inl i0 : Fin r ⊕ Fin s)⟩
  have hNormA_nonneg : 0 ≤ normA :=
    opNorm2Le_radius_nonneg A hA
  have hNormAinv_nonneg : 0 ≤ normAinv :=
    opNorm2Le_radius_nonneg A11inv hA11inv_op
  have hA_sum :
      finiteOpNorm2Le
        (fun i j : Fin r ⊕ Fin s => A (finSumFinEquiv i) (finSumFinEquiv j))
        normA :=
    finiteOpNorm2Le_reindex_equiv finSumFinEquiv A
      (finiteOpNorm2Le_of_opNorm2Le A hA)
  obtain ⟨hA22_chol, hA21_chol⟩ :=
    higham13_lemma13_9_cholesky_block_equations_of_cholesky_fact_fin_sum
      A R A22 A21 R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol
  have hR12_op :
      rectOpNorm2Le R12 (Real.sqrt normA) :=
    higham13_lemma13_9_R12_rectOpNorm2Le_of_full_cholesky_block
      (fun i j : Fin r ⊕ Fin s => A (finSumFinEquiv i) (finSumFinEquiv j))
      A22 R12 R22 hNormA_nonneg hA22_block hA22_chol hA_sum
  have hA11inv_chol :
      A11inv = fun j k => ∑ i : Fin r, R11inv j i * R11inv k i := by
    rw [hA11inv]
    ext j k
    simp [rectMatMul, finiteTranspose]
  have hR11inv_op :
      rectOpNorm2Le R11inv (Real.sqrt normAinv) :=
    higham13_lemma13_9_R11inv_rectOpNorm2Le_of_A11inv_cholesky_block
      A11inv R11inv hNormAinv_nonneg hA11inv_chol hA11inv_op
  have hR12sq : (Real.sqrt normA) ^ 2 ≤ normA := by
    rw [Real.sq_sqrt hNormA_nonneg]
  have hR11invsq : (Real.sqrt normAinv) ^ 2 ≤ normAinv := by
    rw [Real.sq_sqrt hNormAinv_nonneg]
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_block_eqs
      A21 A11inv R11 R11inv R12 hA21_chol hA11inv hRight
      (Real.sqrt_nonneg normA) (Real.sqrt_nonneg normAinv)
      hR12_op hR11inv_op hNormA_nonneg hR12sq hR11invsq
      (le_refl (normA * normAinv))

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    the leading Cholesky block has a repository two-sided inverse.

    In the standard `Fin (r+s)` block ordering, the leading block `R₁₁` of a
    Cholesky factor is upper triangular with positive diagonal.  Therefore its
    repository nonsingular inverse satisfies both inverse identities. -/
theorem higham13_lemma13_9_R11_nonsingInv_inverse_of_cholesky_fact_fin_sum
    {r s : ℕ}
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (R11 : Fin r → Fin r → ℝ)
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hChol : CholeskyFactSpec (r + s) A R) :
    IsInverse r R11 (nonsingInv r R11) := by
  have hupper : ∀ i j : Fin r, j.val < i.val → R11 i j = 0 := by
    intro i j hij
    rw [← hR11 i j]
    apply hChol.R_upper
    rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left]
    simpa [Fin.castAdd] using hij
  have hdiag : ∀ i : Fin r, R11 i i ≠ 0 := by
    intro i
    have hpos :
        0 < R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s)) :=
      hChol.R_diag_pos (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
    have hpos11 : 0 < R11 i i := by
      rw [hR11 i i] at hpos
      exact hpos
    exact ne_of_gt hpos11
  exact
    isInverse_nonsingInv_of_det_ne_zero r R11
      (det_ne_zero_of_upper_triangular_diag_ne_zero r R11 hupper hdiag)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    the leading Cholesky block has a repository right inverse.

    This is the right-inverse projection of
    `higham13_lemma13_9_R11_nonsingInv_inverse_of_cholesky_fact_fin_sum`,
    retained for the existing Cholesky block-identity route. -/
theorem higham13_lemma13_9_R11_nonsingInv_right_inverse_of_cholesky_fact_fin_sum
    {r s : ℕ}
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (R11 : Fin r → Fin r → ℝ)
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hChol : CholeskyFactSpec (r + s) A R) :
    IsRightInverse r R11 (nonsingInv r R11) :=
  (higham13_lemma13_9_R11_nonsingInv_inverse_of_cholesky_fact_fin_sum
    A R R11 hR11 hChol).2

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    lower spectral/Loewner bound for the full SPD matrix gives the scalar
    upper Loewner bound for the actual leading-principal inverse.

    This proves the mathematical step `alpha I <= A` implies
    `A₁₁⁻¹ <= alpha⁻¹ I`, using the Cholesky identity
    `A₁₁ = R₁₁ᵀR₁₁` and the repository nonsingular inverse of `R₁₁`. -/
theorem higham13_lemma13_9_principal_inverse_loewner_upper_of_full_lower
    {r s : ℕ}
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    {alpha : ℝ}
    (halpha : 0 < alpha)
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hLower : finiteLoewnerLe
      (fun i j : Fin (r + s) => alpha * finiteIdMatrix i j) A) :
    finiteLoewnerLe A11inv
      (fun i j : Fin r => alpha⁻¹ * finiteIdMatrix i j) := by
  let Aμ : Fin r ⊕ Fin s → Fin r ⊕ Fin s → ℝ :=
    fun i j => A (finSumFinEquiv i) (finSumFinEquiv j)
  have hLowerSum :
      finiteLoewnerLe
        (fun i j : Fin r ⊕ Fin s => alpha * finiteIdMatrix i j) Aμ := by
    have hReindex :=
      finiteLoewnerLe_reindex_equiv finSumFinEquiv hLower
    simpa [Aμ, finiteIdMatrix] using hReindex
  have hLeadingLower :
      finiteLoewnerLe
        (fun i j : Fin r => alpha * finiteIdMatrix i j)
        (fun i j : Fin r =>
          A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
            (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))) :=
    finiteLoewnerLe_smul_id_sumInl_principal Aμ hLowerSum
  have hLeadingEq :
      (fun i j : Fin r =>
          A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
            (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))) =
        rectMatMul (finiteTranspose R11) R11 :=
    higham13_lemma13_9_cholesky_leading_block_eq_of_cholesky_fact_fin_sum
      A R R11 hR11 hChol
  have hGramLower :
      finiteLoewnerLe
        (fun i j : Fin r => alpha * finiteIdMatrix i j)
        (rectMatMul (finiteTranspose R11) R11) := by
    rw [← hLeadingEq]
    exact hLeadingLower
  have hR11Inv :
      IsInverse r R11 (nonsingInv r R11) :=
    higham13_lemma13_9_R11_nonsingInv_inverse_of_cholesky_fact_fin_sum
      A R R11 hR11 hChol
  have hGramRight :
      IsRightInverse r
        (rectMatMul (finiteTranspose R11) R11)
        (rectMatMul (nonsingInv r R11)
          (finiteTranspose (nonsingInv r R11))) :=
    IsRightInverse_rectMatMul_transpose_self_of_IsInverse hR11Inv
  have hUpper :
      finiteLoewnerLe
        (rectMatMul (nonsingInv r R11)
          (finiteTranspose (nonsingInv r R11)))
        (fun i j : Fin r => alpha⁻¹ * finiteIdMatrix i j) :=
    finiteLoewnerLe_right_inverse_upper_of_smul_id_le
      (rectMatMul (finiteTranspose R11) R11)
      (rectMatMul (nonsingInv r R11)
        (finiteTranspose (nonsingInv r R11)))
      halpha hGramLower hGramRight
  simpa [hA11inv] using hUpper

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    principal-inverse route with the leading Cholesky inverse chosen as the
    repository nonsingular inverse of `R₁₁`.

    This wrapper discharges the `R₁₁ R₁₁⁻¹ = I` side condition from the
    Cholesky factor itself.  The remaining source-level norm obligation is
    still the actual principal-inverse operator certificate. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_principal_inverse_nonsingInv
    {r s : ℕ} [Nonempty (Fin r)]
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hA : opNorm2Le A normA)
    (hA11inv_op : opNorm2Le A11inv normAinv) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_principal_inverse
      A R A22 A21 A11inv R11 (nonsingInv r R11) R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv
      (higham13_lemma13_9_R11_nonsingInv_right_inverse_of_cholesky_fact_fin_sum
        A R R11 hR11 hChol)
      hA hA11inv_op

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    a PSD/Loewner certificate for the actual leading-principal inverse gives
    the repository operator-2 certificate needed by the Cholesky route. -/
theorem higham13_lemma13_9_principal_inverse_operator_certificate_from_loewner
    {r : ℕ}
    (A11inv : Fin r → Fin r → ℝ) {normAinv : ℝ}
    (hNormAinv : 0 ≤ normAinv)
    (hSym : IsSymmetricFiniteMatrix A11inv)
    (hPSD : finitePSD A11inv)
    (hLe : finiteLoewnerLe A11inv
      (fun i j => normAinv * finiteIdMatrix i j)) :
    opNorm2Le A11inv normAinv := by
  exact
    opNorm2Le_of_finiteOpNorm2Le A11inv
      (finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_smul_id
        A11inv hNormAinv hSym hPSD hLe)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    a PSD/Loewner certificate for the full SPD matrix gives the repository
    operator-2 certificate needed by the Cholesky route. -/
theorem higham13_lemma13_9_full_operator_certificate_from_loewner
    {n : ℕ}
    (A : Fin n → Fin n → ℝ) {normA : ℝ}
    (hNormA : 0 ≤ normA)
    (hSym : IsSymmetricFiniteMatrix A)
    (hPSD : finitePSD A)
    (hLe : finiteLoewnerLe A
      (fun i j => normA * finiteIdMatrix i j)) :
    opNorm2Le A normA := by
  exact
    opNorm2Le_of_finiteOpNorm2Le A
      (finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_smul_id
        A hNormA hSym hPSD hLe)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    the full SPD matrix side of the Loewner certificate route.

    This removes the separate full-matrix symmetry and PSD hypotheses when the
    source supplies the standard SPD predicate and the remaining upper Loewner
    certificate `A <= ‖A‖₂ I`. -/
theorem higham13_lemma13_9_full_operator_certificate_from_spd_loewner
    {n : ℕ}
    (A : Fin n → Fin n → ℝ) {normA : ℝ}
    (hNormA : 0 ≤ normA)
    (hSPD : IsSymPosDef n A)
    (hLe : finiteLoewnerLe A
      (fun i j => normA * finiteIdMatrix i j)) :
    opNorm2Le A normA :=
  higham13_lemma13_9_full_operator_certificate_from_loewner
    A hNormA
    (isSymPosDef_to_IsSymmetricFiniteMatrix A hSPD)
    (finitePSD_of_isSymPosDef A hSPD)
    hLe

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    principal-inverse Cholesky route from a Loewner upper certificate for the
    actual leading-principal inverse.

    This wrapper keeps the remaining source obligation at the natural SPD
    level: prove the actual `A₁₁⁻¹` is symmetric PSD and bounded by
    `‖A⁻¹‖₂ I` in Loewner order. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_principal_inverse_loewner
    {r s : ℕ} [Nonempty (Fin r)]
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hA : opNorm2Le A normA)
    (hNormAinv : 0 ≤ normAinv)
    (hA11inv_sym : IsSymmetricFiniteMatrix A11inv)
    (hA11inv_psd : finitePSD A11inv)
    (hA11inv_le : finiteLoewnerLe A11inv
      (fun i j => normAinv * finiteIdMatrix i j)) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_principal_inverse_nonsingInv
      A R A22 A21 A11inv R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv hA
      (higham13_lemma13_9_principal_inverse_operator_certificate_from_loewner
        A11inv hNormAinv hA11inv_sym hA11inv_psd hA11inv_le)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    standard source-order Cholesky route from Loewner certificates for both
    the full SPD matrix and the actual leading-principal inverse.

    This is the current narrowest source-facing certificate surface before the
    remaining SPD/spectral work: derive `0 <= A <= ‖A‖₂ I` and
    `0 <= A₁₁⁻¹ <= ‖A⁻¹‖₂ I`, then this wrapper feeds the established
    Cholesky algebra route. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_loewner_certificates
    {r s : ℕ} [Nonempty (Fin r)]
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hNormA : 0 ≤ normA)
    (hA_sym : IsSymmetricFiniteMatrix A)
    (hA_psd : finitePSD A)
    (hA_le : finiteLoewnerLe A
      (fun i j => normA * finiteIdMatrix i j))
    (hNormAinv : 0 ≤ normAinv)
    (hA11inv_sym : IsSymmetricFiniteMatrix A11inv)
    (hA11inv_psd : finitePSD A11inv)
    (hA11inv_le : finiteLoewnerLe A11inv
      (fun i j => normAinv * finiteIdMatrix i j)) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_principal_inverse_loewner
      A R A22 A21 A11inv R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv
      (higham13_lemma13_9_full_operator_certificate_from_loewner
        A hNormA hA_sym hA_psd hA_le)
      hNormAinv hA11inv_sym hA11inv_psd hA11inv_le

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    standard source-order Cholesky route from the source SPD hypothesis on the
    full matrix and a Loewner certificate for the actual leading-principal
    inverse.

    Compared with
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_loewner_certificates`,
    this theorem discharges the full-matrix symmetry and PSD obligations from
    `IsSymPosDef (r+s) A`.  The remaining open source work is the spectral or
    norm route proving the two scalar-identity Loewner upper certificates. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_and_principal_inverse_loewner
    {r s : ℕ} [Nonempty (Fin r)]
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hNormA : 0 ≤ normA)
    (hSPD : IsSymPosDef (r + s) A)
    (hA_le : finiteLoewnerLe A
      (fun i j => normA * finiteIdMatrix i j))
    (hNormAinv : 0 ≤ normAinv)
    (hA11inv_sym : IsSymmetricFiniteMatrix A11inv)
    (hA11inv_psd : finitePSD A11inv)
    (hA11inv_le : finiteLoewnerLe A11inv
      (fun i j => normAinv * finiteIdMatrix i j)) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_principal_inverse_loewner
      A R A22 A21 A11inv R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv
      (higham13_lemma13_9_full_operator_certificate_from_spd_loewner
        A hNormA hSPD hA_le)
      hNormAinv hA11inv_sym hA11inv_psd hA11inv_le

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-order Cholesky route with the actual leading-principal inverse
    symmetry and PSD obligations discharged from its Gram identity.

    The remaining principal-inverse norm obligation is now the scalar-identity
    Loewner upper bound
    `A₁₁⁻¹ <= ‖A⁻¹‖₂ I`; the facts `A₁₁⁻¹` is symmetric PSD follow from the
    already supplied identity `A₁₁⁻¹ = R₁₁⁻¹ R₁₁⁻ᵀ`. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_and_principal_inverse_loewner_upper
    {r s : ℕ} [Nonempty (Fin r)]
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hNormA : 0 ≤ normA)
    (hSPD : IsSymPosDef (r + s) A)
    (hA_le : finiteLoewnerLe A
      (fun i j => normA * finiteIdMatrix i j))
    (hNormAinv : 0 ≤ normAinv)
    (hA11inv_le : finiteLoewnerLe A11inv
      (fun i j => normAinv * finiteIdMatrix i j)) :
    rectOpNorm2Le (rectMatMul A21 A11inv) (Real.sqrt (normA * normAinv)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_and_principal_inverse_loewner
      A R A22 A21 A11inv R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv
      hNormA hSPD hA_le hNormAinv
      (IsSymmetricFiniteMatrix_of_eq_rectMatMul_self_transpose
        (nonsingInv r R11) hA11inv)
      (finitePSD_of_eq_rectMatMul_self_transpose
        (nonsingInv r R11) hA11inv)
      hA11inv_le

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-order Cholesky route from full-matrix upper and lower Loewner
    certificates.

    The lower bound `alpha I <= A` is used to prove the actual
    leading-principal inverse certificate `A₁₁⁻¹ <= alpha⁻¹ I`; the upper bound
    `A <= normA I` supplies the full-matrix operator certificate.  This is the
    source spectral-radius form immediately before identifying
    `normA * alpha⁻¹` with `κ₂(A)`. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_lower_upper
    {r s : ℕ} [Nonempty (Fin r)]
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA alpha : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hNormA : 0 ≤ normA)
    (hSPD : IsSymPosDef (r + s) A)
    (hA_upper : finiteLoewnerLe A
      (fun i j => normA * finiteIdMatrix i j))
    (halpha : 0 < alpha)
    (hA_lower : finiteLoewnerLe
      (fun i j : Fin (r + s) => alpha * finiteIdMatrix i j) A) :
    rectOpNorm2Le (rectMatMul A21 A11inv)
      (Real.sqrt (normA * alpha⁻¹)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_and_principal_inverse_loewner_upper
      A R A22 A21 A11inv R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv
      hNormA hSPD hA_upper
      (inv_nonneg.mpr (le_of_lt halpha))
      (higham13_lemma13_9_principal_inverse_loewner_upper_of_full_lower
        A R A11inv R11 halpha hR11 hChol hA11inv hA_lower)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-order Cholesky route from the repository full-matrix operator
    certificate and a full lower Loewner certificate.

    Compared with
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_lower_upper`,
    this wrapper derives the upper Loewner certificate `A <= normA I` from
    `opNorm2Le A normA`.  The remaining source-facing gap is the lower
    certificate `(1 / ||A^{-1}||₂) I <= A` and the final condition-number
    identification. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_lower_opNorm2_upper
    {r s : ℕ} [Nonempty (Fin r)]
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA alpha : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hNormA : 0 ≤ normA)
    (hSPD : IsSymPosDef (r + s) A)
    (hA_op : opNorm2Le A normA)
    (halpha : 0 < alpha)
    (hA_lower : finiteLoewnerLe
      (fun i j : Fin (r + s) => alpha * finiteIdMatrix i j) A) :
    rectOpNorm2Le (rectMatMul A21 A11inv)
      (Real.sqrt (normA * alpha⁻¹)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_lower_upper
      A R A22 A21 A11inv R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv
      hNormA hSPD
      (finiteLoewnerLe_smul_id_of_opNorm2Le A hA_op)
      halpha hA_lower

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-order Cholesky route from full `opNorm2Le` certificates for `A` and
    a right inverse of `A`.

    This wrapper derives both scalar-identity Loewner certificates from
    repository operator-2 predicates: `A <= normA I` from `opNorm2Le A normA`,
    and `(normAinv)⁻¹ I <= A` from `opNorm2Le Ainv normAinv` plus
    `A * Ainv = I`.  Thus the displayed radius is the usual
    `sqrt (normA * normAinv)` condition-number product surface. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_opNorm2_inverse
    {r s : ℕ} [Nonempty (Fin r)]
    (A Ainv R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hNormA : 0 ≤ normA)
    (hNormAinv : 0 < normAinv)
    (hSPD : IsSymPosDef (r + s) A)
    (hA_op : opNorm2Le A normA)
    (hAinv_op : opNorm2Le Ainv normAinv)
    (hA_right_inv : IsRightInverse (r + s) A Ainv) :
    rectOpNorm2Le (rectMatMul A21 A11inv)
      (Real.sqrt (normA * normAinv)) := by
  have hA_lower : finiteLoewnerLe
      (fun i j : Fin (r + s) => normAinv⁻¹ * finiteIdMatrix i j) A :=
    finiteLoewnerLe_smul_id_le_of_right_inverse_opNorm2Le
      A Ainv hNormAinv
      (finitePSD_of_isSymPosDef A hSPD)
      (isSymPosDef_to_IsSymmetricFiniteMatrix A hSPD)
      hA_right_inv hAinv_op
  simpa [inv_inv] using
    (higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_lower_opNorm2_upper
      A R A22 A21 A11inv R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv
      hNormA hSPD hA_op (inv_pos.mpr hNormAinv) hA_lower)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-order Cholesky route with the exact l2-operator condition-number
    product surface `kappa2 A Ainv`.

    This is the exact-norm wrapper around
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_opNorm2_inverse`.
    It still exposes the chosen inverse candidate and the positivity of its
    exact 2-norm, while replacing the abstract certificate radii by
    `opNorm2 A` and `opNorm2 Ainv`. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2
    {r s : ℕ} [Nonempty (Fin r)]
    (A Ainv R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hNormAinv : 0 < opNorm2 Ainv)
    (hSPD : IsSymPosDef (r + s) A)
    (hA_right_inv : IsRightInverse (r + s) A Ainv) :
    rectOpNorm2Le (rectMatMul A21 A11inv)
      (Real.sqrt (kappa2 A Ainv)) := by
  simpa [kappa2] using
    (higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_opNorm2_inverse
      A Ainv R A22 A21 A11inv R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv
      (opNorm2_nonneg A) hNormAinv hSPD
      (opNorm2Le_opNorm2 A) (opNorm2Le_opNorm2 Ainv) hA_right_inv)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-order Cholesky route with the exact l2-operator condition-number
    product surface `kappa2 A Ainv`, deriving positivity of `||Ainv||₂` from
    the right-inverse certificate.

    This removes the explicit positivity assumption in
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2`.
    The remaining source-facing data are the chosen right inverse and the
    Cholesky block certificate. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2_of_right_inverse
    {r s : ℕ} [Nonempty (Fin r)]
    (A Ainv R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hSPD : IsSymPosDef (r + s) A)
    (hA_right_inv : IsRightInverse (r + s) A Ainv) :
    rectOpNorm2Le (rectMatMul A21 A11inv)
      (Real.sqrt (kappa2 A Ainv)) := by
  classical
  let i0 : Fin r := Classical.choice (inferInstance : Nonempty (Fin r))
  have hNormAinv : 0 < opNorm2 Ainv :=
    opNorm2_pos_of_right_inverse_at
      (finSumFinEquiv (Sum.inl i0 : Fin r ⊕ Fin s)) A Ainv hA_right_inv
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2
      A Ainv R A22 A21 A11inv R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv
      hNormAinv hSPD hA_right_inv

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    exact `kappa2` Cholesky route with the canonical repository inverse
    `nonsingInv (r+s) A`.

    This wrapper removes the arbitrary inverse-candidate and right-inverse
    hypotheses from
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2_of_right_inverse`.
    The remaining source-facing data are the Cholesky block certificate and the
    identity identifying the displayed `A11inv` with the Cholesky expression. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2_nonsingInv
    {r s : ℕ} [Nonempty (Fin r)]
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hSPD : IsSymPosDef (r + s) A) :
    rectOpNorm2Le (rectMatMul A21 A11inv)
      (Real.sqrt (kappa2 A (nonsingInv (r + s) A))) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2_of_right_inverse
      A (nonsingInv (r + s) A) R A22 A21 A11inv R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv hSPD
      (isRightInverse_nonsingInv_of_isSymPosDef A hSPD)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    SPD supplies the Cholesky factor, source block data, displayed leading
    inverse `R₁₁⁻¹ R₁₁⁻ᵀ`, and the exact `kappa2` Cholesky-route bound.

    This is an existential packaging of
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2_nonsingInv`:
    the remaining non-existential source step is to identify the displayed
    `A₁₁⁻¹` used in the chapter with this Cholesky-derived inverse expression. -/
theorem
    higham13_lemma13_9_exists_cholesky_route_rectOpNorm2Le_from_spd_kappa2_nonsingInv
    {r s : ℕ} [Nonempty (Fin r)]
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hSPD : IsSymPosDef (r + s) A) :
    ∃ (R : Fin (r + s) → Fin (r + s) → ℝ)
      (R11 : Fin r → Fin r → ℝ)
      (R12 : Fin r → Fin s → ℝ)
      (R22 : Fin s → Fin s → ℝ)
      (A11inv : Fin r → Fin r → ℝ),
      CholeskyFactSpec (r + s) A R ∧
      (∀ i j,
        R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j) ∧
      (∀ i j,
        R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j) ∧
      (∀ i j,
        R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j) ∧
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)) ∧
      rectOpNorm2Le (rectMatMul A21 A11inv)
        (Real.sqrt (kappa2 A (nonsingInv (r + s) A))) := by
  obtain ⟨R, hChol⟩ := cholesky_existence (r + s) A hSPD
  let R11 : Fin r → Fin r → ℝ := fun i j =>
    R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
      (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))
  let R12 : Fin r → Fin s → ℝ := fun i j =>
    R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
      (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))
  let R22 : Fin s → Fin s → ℝ := fun i j =>
    R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
      (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))
  let A11inv : Fin r → Fin r → ℝ :=
    rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11))
  refine ⟨R, R11, R12, R22, A11inv, hChol, ?_, ?_, ?_, rfl, ?_⟩
  · intro i j
    rfl
  · intro i j
    rfl
  · intro i j
    rfl
  · exact
      higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2_nonsingInv
        A R A22 A21 A11inv R11 R12 R22
        hA22_block hA21_block
        (by intro i j; rfl)
        (by intro i j; rfl)
        (by intro i j; rfl)
        hChol rfl hSPD

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    identify the canonical inverse of the leading principal block with the
    displayed Cholesky expression `R₁₁⁻¹ R₁₁⁻ᵀ`.

    This is the source inverse-identification step after a Cholesky factor has
    been selected: `A₁₁ = R₁₁ᵀ R₁₁`, and the repository nonsingular inverse of
    `R₁₁ᵀ R₁₁` is `R₁₁⁻¹ R₁₁⁻ᵀ`. -/
theorem higham13_lemma13_9_leading_nonsingInv_eq_cholesky_fact_fin_sum
    {r s : ℕ}
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (R11 : Fin r → Fin r → ℝ)
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hChol : CholeskyFactSpec (r + s) A R) :
    nonsingInv r
      (fun i j : Fin r =>
        A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))) =
      rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)) := by
  have hLeadingEq :
      (fun i j : Fin r =>
          A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
            (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))) =
        rectMatMul (finiteTranspose R11) R11 :=
    higham13_lemma13_9_cholesky_leading_block_eq_of_cholesky_fact_fin_sum
      A R R11 hR11 hChol
  rw [hLeadingEq]
  exact
    nonsingInv_rectMatMul_transpose_self_of_IsInverse
      (higham13_lemma13_9_R11_nonsingInv_inverse_of_cholesky_fact_fin_sum
        A R R11 hR11 hChol)

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9:
    for a source-ordered SPD block matrix,
    `||A₂₁ A₁₁⁻¹||₂ <= sqrt(κ₂(A))`.

    The leading inverse is modeled by the repository canonical inverse of the
    leading principal block, and `κ₂(A)` is the exact product
    `kappa2 A (nonsingInv (r+s) A)`.  The proof chooses a Cholesky factor from
    SPD, identifies `A₁₁⁻¹` with `R₁₁⁻¹R₁₁⁻ᵀ`, and feeds the exact-`kappa2`
    Cholesky route. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_spd_leading_nonsingInv_kappa2
    {r s : ℕ} [Nonempty (Fin r)]
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hSPD : IsSymPosDef (r + s) A) :
    rectOpNorm2Le
      (rectMatMul A21
        (nonsingInv r
          (fun i j : Fin r =>
            A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
              (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))))
      (Real.sqrt (kappa2 A (nonsingInv (r + s) A))) := by
  obtain ⟨R, hChol⟩ := cholesky_existence (r + s) A hSPD
  let R11 : Fin r → Fin r → ℝ := fun i j =>
    R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
      (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))
  let R12 : Fin r → Fin s → ℝ := fun i j =>
    R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
      (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))
  let R22 : Fin s → Fin s → ℝ := fun i j =>
    R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
      (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s))
  let A11 : Fin r → Fin r → ℝ := fun i j =>
    A (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
      (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s))
  have hA11inv :
      nonsingInv r A11 =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)) := by
    exact
      higham13_lemma13_9_leading_nonsingInv_eq_cholesky_fact_fin_sum
        A R R11 (by intro i j; rfl) hChol
  have hbound :
      rectOpNorm2Le (rectMatMul A21 (nonsingInv r A11))
        (Real.sqrt (kappa2 A (nonsingInv (r + s) A))) :=
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2_nonsingInv
      A R A22 A21 (nonsingInv r A11) R11 R12 R22
      hA22_block hA21_block
      (by intro i j; rfl)
      (by intro i j; rfl)
      (by intro i j; rfl)
      hChol hA11inv hSPD
  simpa [A11] using hbound

/-- Higham, 2nd ed., Chapter 13, Lemma 13.9 proof route:
    source-order Cholesky route from spectral upper certificates.

    This theorem replaces the raw scalar-identity Loewner upper hypotheses in
    `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_and_principal_inverse_loewner_upper`
    by pointwise upper bounds on the locally named Hermitian eigenvalues of
    `A` and of the actual leading-principal inverse.  It is still a
    certificate theorem: the remaining source task is to identify the displayed
    radii with the corresponding operator-2 norm/eigenvalue upper bounds. -/
theorem
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_and_principal_inverse_eigenvalue_upper
    {r s : ℕ} [Nonempty (Fin r)]
    (A R : Fin (r + s) → Fin (r + s) → ℝ)
    (A22 : Fin s → Fin s → ℝ)
    (A21 : Fin s → Fin r → ℝ)
    (A11inv R11 : Fin r → Fin r → ℝ)
    (R12 : Fin r → Fin s → ℝ)
    (R22 : Fin s → Fin s → ℝ)
    {normA normAinv : ℝ}
    (hA22_block : A22 =
      fun i j : Fin s =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)))
    (hA21_block : A21 =
      fun (i : Fin s) (j : Fin r) =>
        A (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
          (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)))
    (hR11 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inl j : Fin r ⊕ Fin s)) = R11 i j)
    (hR12 : ∀ i j,
      R (finSumFinEquiv (Sum.inl i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R12 i j)
    (hR22 : ∀ i j,
      R (finSumFinEquiv (Sum.inr i : Fin r ⊕ Fin s))
        (finSumFinEquiv (Sum.inr j : Fin r ⊕ Fin s)) = R22 i j)
    (hChol : CholeskyFactSpec (r + s) A R)
    (hA11inv :
      A11inv =
        rectMatMul (nonsingInv r R11) (finiteTranspose (nonsingInv r R11)))
    (hNormA : 0 ≤ normA)
    (hSPD : IsSymPosDef (r + s) A)
    (hA_eig : ∀ a : Fin (r + s),
      finiteHermitianEigenvalues A
        (isSymPosDef_to_IsSymmetricFiniteMatrix A hSPD) a ≤ normA)
    (hNormAinv : 0 ≤ normAinv)
    (hA11inv_eig : ∀ a : Fin r,
      finiteHermitianEigenvalues A11inv
        (IsSymmetricFiniteMatrix_of_eq_rectMatMul_self_transpose
          (nonsingInv r R11) hA11inv) a ≤ normAinv) :
    rectOpNorm2Le (rectMatMul A21 A11inv)
      (Real.sqrt (normA * normAinv)) := by
  exact
    higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_and_principal_inverse_loewner_upper
      A R A22 A21 A11inv R11 R12 R22
      hA22_block hA21_block hR11 hR12 hR22 hChol hA11inv
      hNormA hSPD
      (finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le A
        (isSymPosDef_to_IsSymmetricFiniteMatrix A hSPD) hA_eig)
      hNormAinv
      (finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le A11inv
        (IsSymmetricFiniteMatrix_of_eq_rectMatMul_self_transpose
          (nonsingInv r R11) hA11inv)
        hA11inv_eig)

end NumStability
