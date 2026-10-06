/-
Copyright (c) 2026 NumStability contributors. All rights reserved.
Released under Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
-/
import NumStability.Algorithms.HighamChapter9

/-!
# Corollary 14.7 — Row Diagonally Dominant Gauss–Jordan Elimination Stability

Higham, *Accuracy and Stability of Numerical Algorithms* (2nd ed.),
Corollary 14.7 (p. 277).

> If GJE successfully computes an approximate solution `x̂` to `A x = b`, where
> `A ∈ ℝ^{n×n}` is row diagonally dominant, then
> ```
>   |b − A x̂|          ≤ 32 n² u |A| e eᵀ |x̂|      + O(u²)      (residual)
>   ‖x − x̂‖∞ / ‖x‖∞    ≤ 4 n³ u (κ∞(A) + 3)         + O(u²)      (forward error)
> ```

The book's proof is one sentence (p. 277):

> "The bounds follow from Theorem 14.5 on noting that `U` is row diagonally
> dominant and using Lemma 8.8 to bound cond(U) and (9.17) to bound `‖|L||U|‖∞`."

This file carries out that specialization.  The two structural facts that row
diagonal dominance supplies are proved / reused from Chapters 8 and 9:

* **Lemma 8.8** (`higham8_8_rowDiagDominantUpper_condSkeel_bound`): for a
  row-diagonally-dominant upper factor `U`, `cond(U) = ‖|U⁻¹||U|‖∞ ≤ 2n − 1`.
  Repackaged here in operator-`infNorm` form as
  `ch14ext_cor147_condU_infNorm_le`.
* **Equation (9.17)** (`higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec`): for
  `A = L̂ Û` with `Û` row diagonally dominant, `‖|L̂||Û|‖∞ ≤ (2n − 1)‖A‖∞`.
  Repackaged here as `ch14ext_cor147_absLU_infNorm_le`.

## What is DERIVED vs. INHERITED

The endpoint theorems `ch14ext_gje_overall_residual_of_accumulation` /
`ch14ext_gje_overall_forward_error_of_accumulation` (Theorem 14.5, eqs.
(14.31)/(14.32)) are the base results.  Corollary 14.7 is an *honest
specialization* of them: the row-dominant norm reduction below is fully derived
here from Lemma 8.8 + (9.17), while the componentwise Theorem-14.5 bound itself
enters as an explicit hypothesis (`hFwd` / `hRes`).  This is exactly the
inheritance the mandate flags as `SUBSTANTIVE_PARTIAL`: Theorem 14.5 carries its
own three documented residuals (Higham's WLOG `D = I`, the supplied cumulative
product inverse `Q`, and the `8nu`/`2nu` leading-order scalar audit — the latter
being precisely the `8 n u` / `2 n u` coefficients appearing in `hRes`/`hFwd`).

## Constant audit (honest)

* **Forward error.** The row-dominant reduction gives, from (14.32),
  `‖x − x̂‖∞ ≤ 2n(2n−1) u (κ∞(A) + 3) ‖x̂‖∞`.  The leading factor `2n(2n−1) =
  4n² − 2n` is *tighter* than the printed `4n³`; since `2n(2n−1) ≤ 4n³` for
  `n ≥ 1`, the printed constant `4 n³ u (κ∞(A) + 3)` is reached (as a weakening
  of the tighter derived bound).  The `‖x̂‖∞ / ‖x‖∞` factor — which equals
  `1 + O(u)` — is kept explicit rather than absorbed into `O(u²)`.
* **Residual.** The norm-only reduction of (14.31) gives
  `‖b − A x̂‖∞ ≤ 8n(2n−1)² u ‖A‖∞ ‖x̂‖∞`.  Higham's printed componentwise
  `32n²` bound uses the sharper entrywise comparison-matrix consequence
  `( |U⁻¹||U| )ᵢⱼ ≤ 2` of Lemma 8.8.  The exported Chapter 8 theorem currently
  supplies only the `2n−1` infinity-norm bound; the entrywise consequence is
  therefore derived locally below before it is composed into the exact printed
  endpoint.  The norm-only fallback remains available as a separate theorem.
-/

namespace NumStability.Ch14Ext

open NumStability

-- ═══════════════════════════════════════════════════════════════════════════
-- §1  Row-dominant control facts (Lemma 8.8 and eq. (9.17) in infNorm form)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Lemma 8.8, operator-`infNorm` form.**

For a row-diagonally-dominant upper factor `U` with exact inverse `U_inv`, the
Skeel condition number `cond(U) = ‖|U⁻¹||U|‖∞` is at most `2n − 1`.  This is
`higham8_8_rowDiagDominantUpper_condSkeel_bound` repackaged as an `infNorm`
bound on the componentwise product `|U⁻¹||U|`, which is the shape Theorem 14.5's
residual/forward-error bounds consume. -/
theorem ch14ext_cor147_condU_infNorm_le (n : ℕ) (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (hURow : higham8_8_rowDiagDominantUpper n U)
    (hUinv : IsInverse n U U_inv) :
    infNorm (matMul n (absMatrix n U_inv) (absMatrix n U)) ≤ 2 * (n : ℝ) - 1 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hcond : condSkeel n hn U U_inv ≤ 2 * (n : ℝ) - 1 :=
    higham8_8_rowDiagDominantUpper_condSkeel_bound n hn U U_inv hURow hUinv
  apply infNorm_le_of_row_sum_le
  · intro i
    have hentry : ∀ j : Fin n,
        |matMul n (absMatrix n U_inv) (absMatrix n U) i j|
          = ∑ k : Fin n, |U_inv i k| * |U k j| := by
      intro j
      have hnn : 0 ≤ matMul n (absMatrix n U_inv) (absMatrix n U) i j := by
        simp only [matMul, absMatrix]
        exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      rw [abs_of_nonneg hnn]
      simp only [matMul, absMatrix]
    calc
      ∑ j : Fin n, |matMul n (absMatrix n U_inv) (absMatrix n U) i j|
          = ∑ j : Fin n, ∑ k : Fin n, |U_inv i k| * |U k j| :=
            Finset.sum_congr rfl (fun j _ => hentry j)
      _ = ∑ k : Fin n, ∑ j : Fin n, |U_inv i k| * |U k j| := Finset.sum_comm
      _ = ∑ k : Fin n, |U_inv i k| * ∑ j : Fin n, |U k j| := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [Finset.mul_sum]
      _ ≤ condSkeel n hn U U_inv := by
            unfold condSkeel
            exact Finset.le_sup'
              (fun i => ∑ j : Fin n, |U_inv i j| * (∑ k : Fin n, |U j k|))
              (Finset.mem_univ i)
      _ ≤ 2 * (n : ℝ) - 1 := hcond
  · linarith

/-- **Lemma 8.8, entrywise comparison-matrix consequence.**

If `U` is row diagonally dominant and `U_inv` is its exact inverse, then every
entry of `|U_inv||U|` is at most `2`.  This is the sharper fact used by the
componentwise `32 n^2` residual estimate in Corollary 14.7; summing these
entrywise bounds alone would give the coarser `2n` norm estimate.

The proof constructs the inverse of the comparison matrix `M(U)`, normalizes
it to unit diagonal, and applies the Chapter 8 unit-upper inverse-entry bound. -/
theorem ch14ext_cor147_condU_entry_le_two (n : ℕ)
    (U U_inv : Fin n → Fin n → ℝ)
    (hURow : higham8_8_rowDiagDominantUpper n U)
    (hUinv : IsInverse n U U_inv) :
    ∀ i j : Fin n,
      matMul n (absMatrix n U_inv) (absMatrix n U) i j ≤ 2 := by
  rcases hURow with ⟨hUT, hDiag, hRow⟩
  let M : Fin n → Fin n → ℝ := comparisonMatrix n U
  have hM_ut : ∀ i j : Fin n, j.val < i.val → M i j = 0 := by
    intro i j hij
    simp [M, comparisonMatrix, show i ≠ j from Fin.ne_of_val_ne (by omega),
      hUT i j hij]
  have hM_diag : ∀ i : Fin n, M i i ≠ 0 := by
    intro i
    simp [M, comparisonMatrix, hDiag i]
  have hdetM : Matrix.det (M : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
    det_ne_zero_of_upper_triangular_diag_ne_zero n M hM_ut hM_diag
  let M_inv : Fin n → Fin n → ℝ := nonsingInv n M
  have hMInv : IsInverse n M M_inv :=
    isInverse_nonsingInv_of_det_ne_zero n M hdetM
  have hM_inv_ut : ∀ i j : Fin n, j.val < i.val → M_inv i j = 0 :=
    inv_upper_tri n M M_inv hM_ut hM_diag hMInv.1
  let C : Fin n → Fin n → ℝ := fun i j => M i j / |U i i|
  let C_inv : Fin n → Fin n → ℝ := fun i j => M_inv i j * |U j j|
  have hC_ut : ∀ i j : Fin n, j.val < i.val → C i j = 0 := by
    intro i j hij
    simp [C, hM_ut i j hij]
  have hC_unit : ∀ i : Fin n, C i i = 1 := by
    intro i
    simp [C, M, comparisonMatrix, hDiag i]
  have hC_row : ∀ i : Fin n,
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |C i j| ≤ 1 := by
    intro i
    calc
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |C i j| =
          (1 / |U i i|) *
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
              |U i j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hij : i ≠ j := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          exact Fin.ne_of_val_ne (by omega)
        simp [C, M, comparisonMatrix, hij, div_eq_mul_inv, mul_comm]
      _ ≤ (1 / |U i i|) * |U i i| :=
        mul_le_mul_of_nonneg_left (hRow i) (one_div_nonneg.mpr (abs_nonneg _))
      _ = 1 := by
        rw [one_div, inv_mul_cancel₀]
        exact abs_ne_zero.mpr (hDiag i)
  have hCinv_ut : ∀ i j : Fin n, j.val < i.val → C_inv i j = 0 := by
    intro i j hij
    simp [C_inv, hM_inv_ut i j hij]
  have hCinv_diag : ∀ i : Fin n, C_inv i i = 1 := by
    intro i
    simp [C_inv,
      inv_diag_entry n M M_inv hM_ut hM_diag hMInv.1 hM_inv_ut i,
      M, comparisonMatrix, hDiag i]
  have hCRInv : IsRightInverse n C C_inv := by
    intro i j
    unfold C C_inv
    have hsimp :
        ∑ k : Fin n, (M i k / |U i i|) * (M_inv k j * |U j j|) =
          (|U j j| / |U i i|) * ∑ k : Fin n, M i k * M_inv k j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      field_simp [abs_ne_zero.mpr (hDiag i)]
    rw [hsimp, hMInv.2 i j]
    by_cases hij : i = j
    · subst hij
      simp [hDiag i]
    · simp [hij]
  have hCinv_le_one :=
    unitUpperTri_inv_entry_le_one_of_row_sum_le_one
      n C C_inv hC_ut hC_unit hC_row hCRInv hCinv_ut hCinv_diag
  have habsInv : ∀ i j : Fin n, |U_inv i j| ≤ M_inv i j := by
    simpa [M] using
      higham8_12_abs_inv_le_comparison_inv
        n U U_inv M_inv hUT hDiag hUinv hMInv.2 hM_inv_ut
  have hAbsU : ∀ i j : Fin n,
      |U i j| =
        2 * diagMatrix (fun k : Fin n => |U k k|) i j - M i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp [M, comparisonMatrix, diagMatrix]
      ring
    · simp [M, comparisonMatrix, diagMatrix, hij]
  have hdiagMul : ∀ i j : Fin n,
      ∑ k : Fin n,
          M_inv i k * diagMatrix (fun q : Fin n => |U q q|) k j =
        M_inv i j * |U j j| := by
    intro i j
    simpa [matMul] using
      matMul_diagMatrix_right M_inv (fun q : Fin n => |U q q|) i j
  have hsum_eq : ∀ i j : Fin n,
      ∑ k : Fin n, M_inv i k * |U k j| =
        2 * (M_inv i j * |U j j|) - idMatrix n i j := by
    intro i j
    calc
      ∑ k : Fin n, M_inv i k * |U k j| =
          ∑ k : Fin n,
            (2 * (M_inv i k * diagMatrix (fun q : Fin n => |U q q|) k j) -
              M_inv i k * M k j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hAbsU k j]
        ring
      _ = 2 *
            (∑ k : Fin n,
              M_inv i k * diagMatrix (fun q : Fin n => |U q q|) k j) -
          ∑ k : Fin n, M_inv i k * M k j := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * (M_inv i j * |U j j|) - idMatrix n i j := by
        rw [hdiagMul i j, hMInv.1 i j]
        simp [idMatrix]
  intro i j
  have hMabsU_le : ∑ k : Fin n, M_inv i k * |U k j| ≤ 2 := by
    by_cases hij : i.val ≤ j.val
    · have hscaled_abs : |C_inv i j| ≤ 1 := hCinv_le_one i j hij
      have hscaled : M_inv i j * |U j j| ≤ 1 := by
        exact le_trans (le_abs_self (C_inv i j)) (by simpa [C_inv] using hscaled_abs)
      have hid_nonneg : 0 ≤ idMatrix n i j := by
        unfold idMatrix
        positivity
      rw [hsum_eq i j]
      linarith
    · have hji : j.val < i.val := by omega
      have hij_ne : i ≠ j := Fin.ne_of_val_ne (by omega)
      rw [hsum_eq i j, hM_inv_ut i j hji]
      simp [idMatrix, hij_ne]
  calc
    matMul n (absMatrix n U_inv) (absMatrix n U) i j =
        ∑ k : Fin n, |U_inv i k| * |U k j| := rfl
    _ ≤ ∑ k : Fin n, M_inv i k * |U k j| := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (habsInv i k) (abs_nonneg _)
    _ ≤ 2 := hMabsU_le

/-- **Equation (9.17), operator-`infNorm` form.**

For an exact factorization `A = L̂ Û` whose upper factor `Û` is row diagonally
dominant, `‖|L̂||Û|‖∞ ≤ (2n − 1)‖A‖∞`.  A thin wrapper over
`higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec` unfolding the predicate to a
bare inequality. -/
theorem ch14ext_cor147_absLU_infNorm_le (n : ℕ) (hn : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat) :
    infNorm (matMul n (absMatrix n L_hat) (absMatrix n U_hat)) ≤
      (2 * (n : ℝ) - 1) * infNorm A :=
  higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec hn A L_hat U_hat hLU hURow

/-- **Equation (9.17), row-wise form used by Corollary 14.7.**

For each source row `i`, exact LU algebra and Lemma 8.8 give
`sum_j (|L_hat||U_hat|)_ij <= (2n-1) sum_j |A_ij|`.
Unlike the infinity-norm wrapper above, this keeps the source row weight
`|A|e` visible. -/
theorem ch14ext_cor147_absLU_rowSum_le (n : ℕ) (hn : 0 < n)
    (A L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (i : Fin n) :
    ∑ j : Fin n,
        |matMul n (absMatrix n L_hat) (absMatrix n U_hat) i j| ≤
      (2 * (n : ℝ) - 1) * ∑ s : Fin n, |A i s| := by
  let W : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let kappaRow : Fin n → ℝ :=
    fun s => ∑ k : Fin n, |U_inv s k| * (∑ j : Fin n, |U_hat k j|)
  have hprod : matMul n L_hat U_hat = A := by
    funext a b
    exact hLU.product_eq a b
  have hUright : matMul n U_hat U_inv = idMatrix n := by
    funext a b
    exact hUinv.2 a b
  have hAUinv : matMul n A U_inv = L_hat := by
    calc
      matMul n A U_inv = matMul n (matMul n L_hat U_hat) U_inv := by rw [hprod]
      _ = matMul n L_hat (matMul n U_hat U_inv) :=
        matMul_assoc n L_hat U_hat U_inv
      _ = matMul n L_hat (idMatrix n) := by rw [hUright]
      _ = L_hat := matMul_id_right n L_hat
  have hLentry : ∀ a k : Fin n,
      L_hat a k = ∑ s : Fin n, A a s * U_inv s k := by
    intro a k
    simpa [matMul] using (congrFun (congrFun hAUinv a) k).symm
  have hkappa_le : ∀ s : Fin n,
      kappaRow s ≤ condSkeel n hn U_hat U_inv := by
    intro s
    unfold kappaRow condSkeel
    exact Finset.le_sup'
      (fun a => ∑ k : Fin n, |U_inv a k| * (∑ j : Fin n, |U_hat k j|))
      (Finset.mem_univ s)
  have hcond : condSkeel n hn U_hat U_inv ≤ 2 * (n : ℝ) - 1 :=
    higham8_8_rowDiagDominantUpper_condSkeel_bound
      n hn U_hat U_inv hURow hUinv
  have hWnonneg : ∀ a b : Fin n, 0 ≤ W a b := by
    intro a b
    unfold W matMul absMatrix
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc
    ∑ j : Fin n,
        |matMul n (absMatrix n L_hat) (absMatrix n U_hat) i j| =
        ∑ j : Fin n, W i j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_of_nonneg (hWnonneg i j)]
    _ = ∑ j : Fin n, ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
      simp [W, matMul, absMatrix]
    _ ≤ ∑ j : Fin n, ∑ k : Fin n,
          (∑ s : Fin n, |A i s| * |U_inv s k|) * |U_hat k j| := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      have hLik : |L_hat i k| ≤ ∑ s : Fin n, |A i s| * |U_inv s k| := by
        rw [hLentry i k]
        calc
          |∑ s : Fin n, A i s * U_inv s k| ≤
              ∑ s : Fin n, |A i s * U_inv s k| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ s : Fin n, |A i s| * |U_inv s k| := by
            apply Finset.sum_congr rfl
            intro s _
            rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hLik (abs_nonneg _)
    _ = ∑ k : Fin n,
          (∑ s : Fin n, |A i s| * |U_inv s k|) *
            (∑ j : Fin n, |U_hat k j|) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.mul_sum]
    _ = ∑ s : Fin n, |A i s| * kappaRow s := by
      simp only [kappaRow]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ ∑ s : Fin n, |A i s| * condSkeel n hn U_hat U_inv := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (hkappa_le s) (abs_nonneg _)
    _ ≤ ∑ s : Fin n, |A i s| * (2 * (n : ℝ) - 1) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left hcond (abs_nonneg _)
    _ = (2 * (n : ℝ) - 1) * ∑ s : Fin n, |A i s| := by
      rw [← Finset.sum_mul]
      ring

/-- **Corollary 14.7, honest componentwise row-wise residual specialization.**

Specializing the leading-order Theorem 14.5 residual through the row-wise
equation (9.17) bound and the exported norm form of Lemma 8.8 gives
`8 n (2n-1)^2 u (|A|e)_i (e^T|x_hat|)` for every row.  This is a genuine
row-wise backward-stability statement.  The exact printed constant is proved
separately below from Lemma 8.8's sharper entrywise consequence. -/
theorem ch14ext_cor147_rowwise_residual_of_theorem14_5
    (n : ℕ) (fp : FPModel) (hn : 0 < n)
    (A L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (b x_hat : Fin n → ℝ)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (hRes : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat)))
            (absVec n x_hat) i) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u *
          (∑ j : Fin n, |A i j|) * (∑ j : Fin n, |x_hat j|) := by
  let MLU : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let M2 : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n U_inv) (absMatrix n U_hat)
  let sx : ℝ := ∑ j : Fin n, |x_hat j|
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hcoeff : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
  have hsx : 0 ≤ sx := Finset.sum_nonneg (fun j _ => abs_nonneg (x_hat j))
  have hMLUnonneg : ∀ a k : Fin n, 0 ≤ MLU a k := by
    intro a k
    unfold MLU matMul absMatrix
    exact Finset.sum_nonneg (fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hM2nonneg : ∀ k j : Fin n, 0 ≤ M2 k j := by
    intro k j
    unfold M2 matMul absMatrix
    exact Finset.sum_nonneg (fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hM2norm : infNorm M2 ≤ 2 * (n : ℝ) - 1 := by
    simpa [M2] using ch14ext_cor147_condU_infNorm_le n hn U_hat U_inv hURow hUinv
  have hM2row : ∀ k : Fin n, ∑ j : Fin n, |M2 k j| ≤ 2 * (n : ℝ) - 1 := by
    intro k
    exact le_trans (row_sum_le_infNorm M2 k) hM2norm
  have hM2action : ∀ k : Fin n,
      matMulVec n M2 (absVec n x_hat) k ≤ (2 * (n : ℝ) - 1) * sx := by
    intro k
    calc
      matMulVec n M2 (absVec n x_hat) k =
          ∑ j : Fin n, M2 k j * |x_hat j| := by
        simp [matMulVec, absVec]
      _ ≤ ∑ j : Fin n, M2 k j * sx := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (abs_coord_le_sum_abs x_hat j)
          (hM2nonneg k j)
      _ = (∑ j : Fin n, M2 k j) * sx := by rw [Finset.sum_mul]
      _ = (∑ j : Fin n, |M2 k j|) * sx := by
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_of_nonneg (hM2nonneg k j)]
      _ ≤ (2 * (n : ℝ) - 1) * sx :=
        mul_le_mul_of_nonneg_right (hM2row k) hsx
  intro i
  have hMLUrow : ∑ k : Fin n, |MLU i k| ≤
      (2 * (n : ℝ) - 1) * ∑ j : Fin n, |A i j| := by
    simpa [MLU] using
      ch14ext_cor147_absLU_rowSum_le n hn A L_hat U_hat U_inv hLU hURow hUinv i
  have hproduct :
      matMulVec n (matMul n MLU M2) (absVec n x_hat) i ≤
        (2 * (n : ℝ) - 1) ^ 2 *
          (∑ j : Fin n, |A i j|) * sx := by
    calc
      matMulVec n (matMul n MLU M2) (absVec n x_hat) i =
          matMulVec n MLU (matMulVec n M2 (absVec n x_hat)) i :=
        matMulVec_matMul n MLU M2 (absVec n x_hat) i
      _ ≤ ∑ k : Fin n, MLU i k * ((2 * (n : ℝ) - 1) * sx) := by
        unfold matMulVec
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hM2action k) (hMLUnonneg i k)
      _ = (∑ k : Fin n, MLU i k) * ((2 * (n : ℝ) - 1) * sx) := by
        rw [Finset.sum_mul]
      _ = (∑ k : Fin n, |MLU i k|) * ((2 * (n : ℝ) - 1) * sx) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_of_nonneg (hMLUnonneg i k)]
      _ ≤ ((2 * (n : ℝ) - 1) * ∑ j : Fin n, |A i j|) *
            ((2 * (n : ℝ) - 1) * sx) :=
        mul_le_mul_of_nonneg_right hMLUrow (mul_nonneg hcoeff hsx)
      _ = (2 * (n : ℝ) - 1) ^ 2 *
            (∑ j : Fin n, |A i j|) * sx := by ring
  have h8nu : 0 ≤ 8 * (n : ℝ) * fp.u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  calc
    |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * fp.u *
          matMulVec n (matMul n MLU M2) (absVec n x_hat) i := by
      simpa [MLU, M2] using hRes i
    _ ≤ 8 * (n : ℝ) * fp.u *
          ((2 * (n : ℝ) - 1) ^ 2 * (∑ j : Fin n, |A i j|) * sx) :=
      mul_le_mul_of_nonneg_left hproduct h8nu
    _ = 8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u *
          (∑ j : Fin n, |A i j|) * (∑ j : Fin n, |x_hat j|) := by
      simp [sx]
      ring

/-- **Corollary 14.7, printed componentwise residual coefficient.**

The sharper entrywise consequence of Lemma 8.8 is
`(|U_hat⁻¹||U_hat|)_ij <= 2`.  Together with exact LU algebra, it turns the
leading-order Theorem 14.5 residual into Higham's printed row-wise bound
`32 n^2 u (|A|e)_i (e^T|x_hat|)`.

This helper isolates the comparison-matrix input from the residual algebra.
The source-facing wrapper below discharges `hCondEntry` from ordinary row
diagonal dominance, so neither theorem assumes the residual conclusion. -/
theorem ch14ext_cor147_rowwise_residual_printed_of_condEntry_le_two
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (b x_hat : Fin n → ℝ)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (hCondEntry : ∀ i j : Fin n,
      matMul n (absMatrix n U_inv) (absMatrix n U_hat) i j ≤ 2)
    (hRes : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat)))
            (absVec n x_hat) i) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        32 * (n : ℝ) ^ 2 * fp.u *
          (∑ j : Fin n, |A i j|) * (∑ j : Fin n, |x_hat j|) := by
  let MLU : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let B : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n U_inv) (absMatrix n U_hat)
  let sx : ℝ := ∑ j : Fin n, |x_hat j|
  have hprod : matMul n L_hat U_hat = A := by
    funext i j
    exact hLU.product_eq i j
  have hUright : matMul n U_hat U_inv = idMatrix n := by
    funext i j
    exact hUinv.2 i j
  have hAUinv : matMul n A U_inv = L_hat := by
    calc
      matMul n A U_inv = matMul n (matMul n L_hat U_hat) U_inv := by rw [hprod]
      _ = matMul n L_hat (matMul n U_hat U_inv) :=
        matMul_assoc n L_hat U_hat U_inv
      _ = matMul n L_hat (idMatrix n) := by rw [hUright]
      _ = L_hat := matMul_id_right n L_hat
  have hLentry : ∀ i k : Fin n,
      L_hat i k = ∑ s : Fin n, A i s * U_inv s k := by
    intro i k
    simpa [matMul] using (congrFun (congrFun hAUinv i) k).symm
  have hBnonneg : ∀ i j : Fin n, 0 ≤ B i j := by
    intro i j
    unfold B matMul absMatrix
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hMLUentry : ∀ i j : Fin n,
      MLU i j ≤ matMul n (absMatrix n A) B i j := by
    intro i j
    calc
      MLU i j = ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
        simp [MLU, matMul, absMatrix]
      _ ≤ ∑ k : Fin n,
          (∑ s : Fin n, |A i s| * |U_inv s k|) * |U_hat k j| := by
        apply Finset.sum_le_sum
        intro k _
        have hLik : |L_hat i k| ≤ ∑ s : Fin n, |A i s| * |U_inv s k| := by
          rw [hLentry i k]
          calc
            |∑ s : Fin n, A i s * U_inv s k| ≤
                ∑ s : Fin n, |A i s * U_inv s k| :=
              Finset.abs_sum_le_sum_abs _ _
            _ = ∑ s : Fin n, |A i s| * |U_inv s k| := by
              apply Finset.sum_congr rfl
              intro s _
              rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hLik (abs_nonneg _)
      _ = ∑ s : Fin n,
          |A i s| * (∑ k : Fin n, |U_inv s k| * |U_hat k j|) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = matMul n (absMatrix n A) B i j := by
        simp [B, matMul, absMatrix]
  have hB2entry : ∀ i j : Fin n,
      matMul n B B i j ≤ 4 * (n : ℝ) := by
    intro i j
    calc
      matMul n B B i j = ∑ k : Fin n, B i k * B k j := rfl
      _ ≤ ∑ _k : Fin n, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        calc
          B i k * B k j ≤ B i k * 2 :=
            mul_le_mul_of_nonneg_left (hCondEntry k j) (hBnonneg i k)
          _ ≤ 2 * 2 :=
            mul_le_mul_of_nonneg_right (hCondEntry i k) (by norm_num)
          _ = 4 := by norm_num
      _ = 4 * (n : ℝ) := by simp [mul_comm]
  have hB2action : ∀ i : Fin n,
      matMulVec n (matMul n B B) (absVec n x_hat) i ≤
        4 * (n : ℝ) * sx := by
    intro i
    calc
      matMulVec n (matMul n B B) (absVec n x_hat) i =
          ∑ j : Fin n, matMul n B B i j * |x_hat j| := by
        simp [matMulVec, absVec]
      _ ≤ ∑ j : Fin n, (4 * (n : ℝ)) * |x_hat j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hB2entry i j) (abs_nonneg _)
      _ = 4 * (n : ℝ) * sx := by simp [sx, Finset.mul_sum]
  have hBxnonneg : ∀ i : Fin n,
      0 ≤ matMulVec n B (absVec n x_hat) i := by
    intro i
    unfold matMulVec absVec
    exact Finset.sum_nonneg
      (fun j _ => mul_nonneg (hBnonneg i j) (abs_nonneg (x_hat j)))
  intro i
  have hproduct :
      matMulVec n (matMul n MLU B) (absVec n x_hat) i ≤
        4 * (n : ℝ) * (∑ s : Fin n, |A i s|) * sx := by
    calc
      matMulVec n (matMul n MLU B) (absVec n x_hat) i =
          matMulVec n MLU (matMulVec n B (absVec n x_hat)) i :=
        matMulVec_matMul n MLU B (absVec n x_hat) i
      _ ≤ matMulVec n (matMul n (absMatrix n A) B)
          (matMulVec n B (absVec n x_hat)) i := by
        unfold matMulVec
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hMLUentry i j) (hBxnonneg j)
      _ = matMulVec n (absMatrix n A)
          (matMulVec n B (matMulVec n B (absVec n x_hat))) i :=
        matMulVec_matMul n (absMatrix n A) B
          (matMulVec n B (absVec n x_hat)) i
      _ ≤ ∑ s : Fin n, |A i s| * (4 * (n : ℝ) * sx) := by
        change (∑ s : Fin n, |A i s| *
          matMulVec n B (matMulVec n B (absVec n x_hat)) s) ≤ _
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hs := hB2action s
        rw [matMulVec_matMul n B B (absVec n x_hat) s] at hs
        exact hs
      _ = 4 * (n : ℝ) * (∑ s : Fin n, |A i s|) * sx := by
        rw [← Finset.sum_mul]
        ring
  have h8nu : 0 ≤ 8 * (n : ℝ) * fp.u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  calc
    |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * fp.u *
          matMulVec n (matMul n MLU B) (absVec n x_hat) i := by
      simpa [MLU, B] using hRes i
    _ ≤ 8 * (n : ℝ) * fp.u *
          (4 * (n : ℝ) * (∑ s : Fin n, |A i s|) * sx) :=
      mul_le_mul_of_nonneg_left hproduct h8nu
    _ = 32 * (n : ℝ) ^ 2 * fp.u *
          (∑ j : Fin n, |A i j|) * (∑ j : Fin n, |x_hat j|) := by
      simp [sx]
      ring

/-- **Corollary 14.7, printed row-wise backward-stability bound (p. 277).**

For a row-diagonally-dominant final upper factor, the leading-order Theorem
14.5 residual implies Higham's componentwise bound
`|b-A*x_hat| <= 32 n^2 u |A| e e^T |x_hat|`.

The entrywise condition-number estimate is derived from `hURow` and `hUinv`;
the only inherited numerical-analysis premise is the parent Theorem 14.5
residual `hRes`. -/
theorem ch14ext_cor147_rowwise_residual_printed_of_rowDiagDominantUpper
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (b x_hat : Fin n → ℝ)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (hRes : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat)))
            (absVec n x_hat) i) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        32 * (n : ℝ) ^ 2 * fp.u *
          (∑ j : Fin n, |A i j|) * (∑ j : Fin n, |x_hat j|) :=
  ch14ext_cor147_rowwise_residual_printed_of_condEntry_le_two
    n fp A L_hat U_hat U_inv b x_hat hLU hUinv
      (ch14ext_cor147_condU_entry_le_two n U_hat U_inv hURow hUinv) hRes

-- ═══════════════════════════════════════════════════════════════════════════
-- §2  Corollary 14.7 forward-error bound (printed constant `4 n³ (κ∞ + 3)`)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Corollary 14.7 — forward error (p. 277).**

`‖x − x̂‖∞ / ‖x‖∞ ≤ 4 n³ u (κ∞(A) + 3) · (‖x̂‖∞ / ‖x‖∞)`.

DERIVED from the inherited Theorem-14.5 forward-error bound (14.32) in the
printed leading-order form
```
  |x − x̂| ≤ 2 n u ( |A⁻¹||L̂||Û| + 3 |Û⁻¹||Û| ) |x̂|                         (hFwd)
```
via row diagonal dominance: `‖|Û⁻¹||Û|‖∞ ≤ 2n − 1` (Lemma 8.8) and
`‖|L̂||Û|‖∞ ≤ (2n − 1)‖A‖∞` (eq. 9.17), together with submultiplicativity of the
operator `infNorm` and `κ∞(A) = ‖A‖∞ ‖A⁻¹‖∞`.

The intermediate derived constant is the *tighter* `2n(2n − 1) (κ∞(A) + 3)`;
the headline states the printed `4 n³` (a valid weakening since
`2n(2n − 1) ≤ 4n³` for `n ≥ 1`).  The `‖x̂‖∞/‖x‖∞ = 1 + O(u)` factor is kept
explicit. -/
theorem ch14ext_cor147_forward_error_relative_infNorm
    (n : ℕ) (fp : FPModel) (hn : 0 < n)
    (A A_inv L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (x x_hat : Fin n → ℝ)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (_hAinv : IsLeftInverse n A A_inv)
    (hxpos : 0 < infNormVec x)
    (hFwd : ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u *
          (matMulVec n
              (matMul n (absMatrix n A_inv)
                (matMul n (absMatrix n L_hat) (absMatrix n U_hat)))
              (absVec n x_hat) i +
            3 * matMulVec n (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
                (absVec n x_hat) i)) :
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x ≤
      4 * (n : ℝ) ^ 3 * fp.u * (kappaInf n hn A A_inv + 3) *
        (infNormVec x_hat / infNormVec x) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hu : 0 ≤ fp.u := fp.u_nonneg
  -- Abbreviations for the two componentwise matrix factors of (14.32).
  set MLU : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat) with hMLU_def
  set M1 : Fin n → Fin n → ℝ := matMul n (absMatrix n A_inv) MLU with hM1_def
  set M2 : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n U_inv) (absMatrix n U_hat) with hM2_def
  set s : ℝ := infNormVec x_hat with hs_def
  set kap : ℝ := kappaInf n hn A A_inv with hkap_def
  have hs_nonneg : 0 ≤ s := infNormVec_nonneg x_hat
  have hkap_eq : kap = infNorm A * infNorm A_inv :=
    kappaInf_eq_infNorm_mul_infNorm n hn A A_inv
  have hkap_nonneg : 0 ≤ kap := kappaInf_nonneg n hn A A_inv
  -- Row-dominant control of the two factors.
  have hM2_norm : infNorm M2 ≤ 2 * (n : ℝ) - 1 :=
    ch14ext_cor147_condU_infNorm_le n hn U_hat U_inv hURow hUinv
  have hMLU_norm : infNorm MLU ≤ (2 * (n : ℝ) - 1) * infNorm A :=
    ch14ext_cor147_absLU_infNorm_le n hn A L_hat U_hat hLU hURow
  -- `‖|A⁻¹||L̂||Û|‖∞ ≤ (2n−1) κ∞(A)`.
  have hM1_norm : infNorm M1 ≤ (2 * (n : ℝ) - 1) * kap := by
    calc
      infNorm M1 ≤ infNorm (absMatrix n A_inv) * infNorm MLU :=
        infNorm_matMul_le hn _ _
      _ = infNorm A_inv * infNorm MLU := by rw [infNorm_absMatrix hn A_inv]
      _ ≤ infNorm A_inv * ((2 * (n : ℝ) - 1) * infNorm A) :=
        mul_le_mul_of_nonneg_left hMLU_norm (infNorm_nonneg A_inv)
      _ = (2 * (n : ℝ) - 1) * kap := by rw [hkap_eq]; ring
  -- Each componentwise matrix–vector term is bounded by `‖M‖∞ · ‖x̂‖∞`.
  have hMV : ∀ (M : Fin n → Fin n → ℝ) (i : Fin n),
      matMulVec n M (absVec n x_hat) i ≤ infNorm M * s := by
    intro M i
    calc
      matMulVec n M (absVec n x_hat) i
          ≤ |matMulVec n M (absVec n x_hat) i| := le_abs_self _
      _ ≤ infNormVec (matMulVec n M (absVec n x_hat)) :=
            abs_le_infNormVec _ i
      _ ≤ infNorm M * infNormVec (absVec n x_hat) :=
            infNormVec_matMulVec_le hn M _
      _ = infNorm M * s := by rw [infNormVec_absVec hn x_hat]
  -- Per-component forward-error bound at the tight constant `2n(2n−1)(κ+3)`.
  have h2nu : 0 ≤ 2 * (n : ℝ) * fp.u := by positivity
  have hrow_coeff : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
  have hstep : ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s := by
    intro i
    have hmv1 : matMulVec n M1 (absVec n x_hat) i ≤ (2 * (n : ℝ) - 1) * kap * s := by
      calc
        matMulVec n M1 (absVec n x_hat) i ≤ infNorm M1 * s := hMV M1 i
        _ ≤ ((2 * (n : ℝ) - 1) * kap) * s :=
              mul_le_mul_of_nonneg_right hM1_norm hs_nonneg
        _ = (2 * (n : ℝ) - 1) * kap * s := by ring
    have hmv2 : matMulVec n M2 (absVec n x_hat) i ≤ (2 * (n : ℝ) - 1) * s := by
      calc
        matMulVec n M2 (absVec n x_hat) i ≤ infNorm M2 * s := hMV M2 i
        _ ≤ (2 * (n : ℝ) - 1) * s :=
              mul_le_mul_of_nonneg_right hM2_norm hs_nonneg
    calc
      |x i - x_hat i|
          ≤ 2 * (n : ℝ) * fp.u *
              (matMulVec n M1 (absVec n x_hat) i +
                3 * matMulVec n M2 (absVec n x_hat) i) := hFwd i
      _ ≤ 2 * (n : ℝ) * fp.u *
              ((2 * (n : ℝ) - 1) * kap * s + 3 * ((2 * (n : ℝ) - 1) * s)) := by
            apply mul_le_mul_of_nonneg_left _ h2nu
            linarith [hmv1, hmv2]
      _ = 2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s := by ring
  -- Normwise, then weaken `2n(2n−1) ≤ 4n³`.
  have hRHS_nonneg :
      0 ≤ 2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s := by
    have : 0 ≤ kap + 3 := by linarith
    positivity
  have hnorm_tight :
      infNormVec (fun i : Fin n => x i - x_hat i) ≤
        2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s :=
    infNormVec_le_of_abs_le _ hstep hRHS_nonneg
  have hpoly : 2 * (n : ℝ) * (2 * (n : ℝ) - 1) ≤ 4 * (n : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) by linarith) (sq_nonneg ((n : ℝ) - 1)),
      mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) by linarith)
        (show (0 : ℝ) ≤ 2 * (n : ℝ) - 1 by linarith)]
  have hP : 0 ≤ fp.u * (kap + 3) * s :=
    mul_nonneg (mul_nonneg hu (by linarith)) hs_nonneg
  have hweak :
      2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s ≤
        4 * (n : ℝ) ^ 3 * fp.u * (kap + 3) * s := by
    have hL :
        2 * (n : ℝ) * fp.u * (2 * (n : ℝ) - 1) * (kap + 3) * s =
          (2 * (n : ℝ) * (2 * (n : ℝ) - 1)) * (fp.u * (kap + 3) * s) := by ring
    have hR :
        4 * (n : ℝ) ^ 3 * fp.u * (kap + 3) * s =
          (4 * (n : ℝ) ^ 3) * (fp.u * (kap + 3) * s) := by ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right hpoly hP
  have hnorm :
      infNormVec (fun i : Fin n => x i - x_hat i) ≤
        4 * (n : ℝ) ^ 3 * fp.u * (kap + 3) * s :=
    le_trans hnorm_tight hweak
  -- Divide by `‖x‖∞ > 0`.
  have hdiv := div_le_div_of_nonneg_right hnorm hxpos.le
  calc
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x
        ≤ (4 * (n : ℝ) ^ 3 * fp.u * (kap + 3) * s) / infNormVec x := hdiv
    _ = 4 * (n : ℝ) ^ 3 * fp.u * (kap + 3) * (s / infNormVec x) := by
          rw [mul_div_assoc]

-- ═══════════════════════════════════════════════════════════════════════════
-- §3  Corollary 14.7 residual bound (norm-only fallback)
-- ═══════════════════════════════════════════════════════════════════════════

/-- **Corollary 14.7 — residual (p. 277), norm-only fallback.**

`‖b − A x̂‖∞ / (‖A‖∞ ‖x̂‖∞) ≤ 8 n (2n − 1)² u`.

DERIVED from the inherited Theorem-14.5 residual bound (14.31) in the printed
leading-order form
```
  |b − A x̂| ≤ 8 n u · |L̂||Û| · |Û⁻¹||Û| · |x̂|                              (hRes)
```
via `‖|L̂||Û|‖∞ ≤ (2n − 1)‖A‖∞` (eq. 9.17) and `‖|Û⁻¹||Û|‖∞ ≤ 2n − 1`
(the exported norm form of Lemma 8.8) with submultiplicativity of `infNorm`.
The componentwise theorem above recovers the printed `32 n²` constant from
the sharper entrywise comparison-matrix premise. -/
theorem ch14ext_cor147_residual_relative_infNorm
    (n : ℕ) (fp : FPModel) (hn : 0 < n)
    (A L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (b x_hat : Fin n → ℝ)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (hApos : 0 < infNorm A)
    (hxpos : 0 < infNormVec x_hat)
    (hRes : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat)))
            (absVec n x_hat) i) :
    infNormVec (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (infNorm A * infNormVec x_hat) ≤
      8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hu : 0 ≤ fp.u := fp.u_nonneg
  have hrow_coeff : 0 ≤ 2 * (n : ℝ) - 1 := by linarith
  set MLU : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat) with hMLU_def
  set M2 : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n U_inv) (absMatrix n U_hat) with hM2_def
  set Mres : Fin n → Fin n → ℝ := matMul n MLU M2 with hMres_def
  set s : ℝ := infNormVec x_hat with hs_def
  have hs_nonneg : 0 ≤ s := infNormVec_nonneg x_hat
  have hApos' : 0 < infNorm A := hApos
  have hdenom_pos : 0 < infNorm A * s := mul_pos hApos hxpos
  have hM2_norm : infNorm M2 ≤ 2 * (n : ℝ) - 1 :=
    ch14ext_cor147_condU_infNorm_le n hn U_hat U_inv hURow hUinv
  have hMLU_norm : infNorm MLU ≤ (2 * (n : ℝ) - 1) * infNorm A :=
    ch14ext_cor147_absLU_infNorm_le n hn A L_hat U_hat hLU hURow
  -- `‖(|L̂||Û|)(|Û⁻¹||Û|)‖∞ ≤ (2n−1)² ‖A‖∞`.
  have hMres_norm : infNorm Mres ≤ (2 * (n : ℝ) - 1) ^ 2 * infNorm A := by
    calc
      infNorm Mres ≤ infNorm MLU * infNorm M2 := infNorm_matMul_le hn _ _
      _ ≤ ((2 * (n : ℝ) - 1) * infNorm A) * (2 * (n : ℝ) - 1) :=
            mul_le_mul hMLU_norm hM2_norm (infNorm_nonneg M2)
              (mul_nonneg hrow_coeff (infNorm_nonneg A))
      _ = (2 * (n : ℝ) - 1) ^ 2 * infNorm A := by ring
  -- Per-component: `matMulVec Mres |x̂| i ≤ ‖Mres‖∞ ‖x̂‖∞`.
  have hMV : ∀ i : Fin n,
      matMulVec n Mres (absVec n x_hat) i ≤ infNorm Mres * s := by
    intro i
    calc
      matMulVec n Mres (absVec n x_hat) i
          ≤ |matMulVec n Mres (absVec n x_hat) i| := le_abs_self _
      _ ≤ infNormVec (matMulVec n Mres (absVec n x_hat)) := abs_le_infNormVec _ i
      _ ≤ infNorm Mres * infNormVec (absVec n x_hat) := infNormVec_matMulVec_le hn Mres _
      _ = infNorm Mres * s := by rw [infNormVec_absVec hn x_hat]
  have h8nu : 0 ≤ 8 * (n : ℝ) * fp.u := by positivity
  -- Per-component residual bound at the honest constant.
  have hstep : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u * (infNorm A * s) := by
    intro i
    have hmv : matMulVec n Mres (absVec n x_hat) i ≤
        (2 * (n : ℝ) - 1) ^ 2 * infNorm A * s := by
      calc
        matMulVec n Mres (absVec n x_hat) i ≤ infNorm Mres * s := hMV i
        _ ≤ ((2 * (n : ℝ) - 1) ^ 2 * infNorm A) * s :=
              mul_le_mul_of_nonneg_right hMres_norm hs_nonneg
        _ = (2 * (n : ℝ) - 1) ^ 2 * infNorm A * s := by ring
    calc
      |b i - ∑ j : Fin n, A i j * x_hat j|
          ≤ 8 * (n : ℝ) * fp.u * matMulVec n Mres (absVec n x_hat) i := hRes i
      _ ≤ 8 * (n : ℝ) * fp.u * ((2 * (n : ℝ) - 1) ^ 2 * infNorm A * s) :=
            mul_le_mul_of_nonneg_left hmv h8nu
      _ = 8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u * (infNorm A * s) := by ring
  have hRHS_nonneg :
      0 ≤ 8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u * (infNorm A * s) := by
    have h1 : 0 ≤ infNorm A * s := hdenom_pos.le
    positivity
  have hnorm :
      infNormVec (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) ≤
        8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u * (infNorm A * s) :=
    infNormVec_le_of_abs_le _ hstep hRHS_nonneg
  -- Divide by `‖A‖∞ ‖x̂‖∞ > 0`.
  have hdiv := div_le_div_of_nonneg_right hnorm hdenom_pos.le
  calc
    infNormVec (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (infNorm A * s)
        ≤ (8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u * (infNorm A * s)) /
            (infNorm A * s) := hdiv
    _ = 8 * (n : ℝ) * (2 * (n : ℝ) - 1) ^ 2 * fp.u := by
          field_simp

end NumStability.Ch14Ext
