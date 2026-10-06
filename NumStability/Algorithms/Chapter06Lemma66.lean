import NumStability.Analysis.Norms

/-!
# Higham, "Accuracy and Stability of Numerical Algorithms" (2nd ed.)
## Chapter 6 (Norms), §6.2, Lemma 6.6 parts (a) and (c)

Higham 2nd ed., §6.2, Lemma 6.6 (p. 111).  For `A, B ∈ R^{m×n}`:

* (a) If `‖a_j‖₂ ≤ ‖b_j‖₂` for every column `j = 1:n`, then
    - (i)   `‖A‖_F ≤ ‖B‖_F`,
    - (ii)  `‖A‖₂ ≤ sqrt(rank B) · ‖B‖₂`,
    - (iii) `|A| ≤ e eᵀ |B|` (entrywise, `e` the all-ones vector).
  The second inequality is sharp (equality when `A = B` has rank one; also for
  `A = e eᵀ`, `B = sqrt(n) I`).

* (c) If `|A| ≤ |B|` (entrywise) then `‖A‖₂ ≤ sqrt(rank B) · ‖B‖₂`.

Higham's own proof of (a)(ii) is the chain `‖A‖₂ ≤ ‖A‖_F ≤ ‖B‖_F ≤ sqrt(rank B) ‖B‖₂`
(Table 6.2); (a)(iii) is `|a_ij| ≤ ‖a_j‖₂ ≤ ‖b_j‖₂ ≤ ‖b_j‖₁ = (e eᵀ |B|)_{ij}`; and
(c) is a special case of (a) because entrywise domination `|A| ≤ |B|` forces the
columnwise 2-norm domination hypothesis of (a).

We work in the complex layer (`CMatrix`, which contains the real case), matching
the pre-existing building blocks in `Norms.lean`:
`complexMatrixOp2_le_complexMatrixFrobenius`,
`complexMatrixFrobenius_le_sqrt_rank_mul_complexMatrixOp2`,
`complexMatrixFrobeniusSq_eq_entrywise_sum`, plus the Mathlib inequality
`Finset.sum_sq_le_sq_sum_of_nonneg` for the 2-norm ≤ 1-norm column step.
-/

namespace NumStability

namespace Lemma66

open scoped BigOperators

/-- Squared Euclidean 2-norm of column `j` of a complex rectangular matrix:
    `‖a_j‖₂² = Σ_i |a_ij|²`. -/
noncomputable def lemma66_colNormSq {m n : ℕ} (A : CMatrix m n) (j : Fin n) : ℝ :=
  ∑ i : Fin m, ‖A i j‖ ^ 2

/-- Euclidean 2-norm of column `j`: `‖a_j‖₂`. -/
noncomputable def lemma66_colNorm2 {m n : ℕ} (A : CMatrix m n) (j : Fin n) : ℝ :=
  Real.sqrt (lemma66_colNormSq A j)

/-- Manhattan 1-norm of column `j`: `‖a_j‖₁ = eᵀ|a_j| = Σ_i |a_ij|`.
    This is the `j`-th entry of `eᵀ|B|` in Higham's `|A| ≤ e eᵀ |B|`. -/
noncomputable def lemma66_colNorm1 {m n : ℕ} (A : CMatrix m n) (j : Fin n) : ℝ :=
  ∑ i : Fin m, ‖A i j‖

lemma lemma66_colNormSq_nonneg {m n : ℕ} (A : CMatrix m n) (j : Fin n) :
    0 ≤ lemma66_colNormSq A j :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma lemma66_colNorm2_nonneg {m n : ℕ} (A : CMatrix m n) (j : Fin n) :
    0 ≤ lemma66_colNorm2 A j :=
  Real.sqrt_nonneg _

lemma lemma66_colNorm1_nonneg {m n : ℕ} (A : CMatrix m n) (j : Fin n) :
    0 ≤ lemma66_colNorm1 A j :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- `(‖a_j‖₂)² = ‖a_j‖₂²`. -/
lemma lemma66_colNorm2_sq {m n : ℕ} (A : CMatrix m n) (j : Fin n) :
    lemma66_colNorm2 A j ^ 2 = lemma66_colNormSq A j := by
  rw [lemma66_colNorm2, Real.sq_sqrt (lemma66_colNormSq_nonneg A j)]

/-- Frobenius square as the sum over columns of squared column 2-norms:
    `‖A‖_F² = Σ_j ‖a_j‖₂²`. -/
lemma lemma66_frobeniusSq_eq_sum_colNormSq {m n : ℕ} (A : CMatrix m n) :
    complexMatrixFrobeniusSq A = ∑ j : Fin n, lemma66_colNormSq A j := by
  unfold complexMatrixFrobeniusSq lemma66_colNormSq
  rw [Finset.sum_comm]

/-- Each entry is dominated by its column 2-norm: `|a_ij| ≤ ‖a_j‖₂`. -/
lemma lemma66_entry_le_colNorm2 {m n : ℕ} (A : CMatrix m n) (i : Fin m) (j : Fin n) :
    ‖A i j‖ ≤ lemma66_colNorm2 A j := by
  rw [lemma66_colNorm2, show ‖A i j‖ = Real.sqrt (‖A i j‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun i => ‖A i j‖ ^ 2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ i)

/-- Euclidean 2-norm of a column is dominated by its Manhattan 1-norm:
    `‖a_j‖₂ ≤ ‖a_j‖₁`. -/
lemma lemma66_colNorm2_le_colNorm1 {m n : ℕ} (A : CMatrix m n) (j : Fin n) :
    lemma66_colNorm2 A j ≤ lemma66_colNorm1 A j := by
  rw [lemma66_colNorm2, lemma66_colNorm1,
    show (∑ i : Fin m, ‖A i j‖)
        = Real.sqrt ((∑ i : Fin m, ‖A i j‖) ^ 2) from
      (Real.sqrt_sq (lemma66_colNorm1_nonneg A j)).symm]
  apply Real.sqrt_le_sqrt
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)

/-- Columnwise squared-2-norm domination follows from the (2-norm) hypothesis. -/
lemma lemma66_colNormSq_le_of_colNorm2_le {m n : ℕ} (A B : CMatrix m n)
    (h : ∀ j, lemma66_colNorm2 A j ≤ lemma66_colNorm2 B j) (j : Fin n) :
    lemma66_colNormSq A j ≤ lemma66_colNormSq B j := by
  rw [← lemma66_colNorm2_sq, ← lemma66_colNorm2_sq]
  exact pow_le_pow_left₀ (lemma66_colNorm2_nonneg A j) (h j) 2

/-!
### Lemma 6.6 (a): columnwise 2-norm domination
-/

/-- **Higham Lemma 6.6 (a)(i).**  If `‖a_j‖₂ ≤ ‖b_j‖₂` for every column `j`, then
    `‖A‖_F ≤ ‖B‖_F`. -/
theorem lemma66_a_frobenius_le {m n : ℕ} (A B : CMatrix m n)
    (h : ∀ j, lemma66_colNorm2 A j ≤ lemma66_colNorm2 B j) :
    complexMatrixFrobenius A ≤ complexMatrixFrobenius B := by
  rw [complexMatrixFrobenius, complexMatrixFrobenius]
  apply Real.sqrt_le_sqrt
  rw [lemma66_frobeniusSq_eq_sum_colNormSq, lemma66_frobeniusSq_eq_sum_colNormSq]
  exact Finset.sum_le_sum fun j _ => lemma66_colNormSq_le_of_colNorm2_le A B h j

/-- **Higham Lemma 6.6 (a)(iii).**  If `‖a_j‖₂ ≤ ‖b_j‖₂` for every column `j`,
    then `|A| ≤ e eᵀ |B|` entrywise, i.e. for all `i, j`,
    `|a_ij| ≤ Σ_k |b_kj| = (e eᵀ |B|)_{ij}`. -/
theorem lemma66_a_abs_entry_le {m n : ℕ} (A B : CMatrix m n)
    (h : ∀ j, lemma66_colNorm2 A j ≤ lemma66_colNorm2 B j) (i : Fin m) (j : Fin n) :
    ‖A i j‖ ≤ lemma66_colNorm1 B j :=
  calc ‖A i j‖ ≤ lemma66_colNorm2 A j := lemma66_entry_le_colNorm2 A i j
    _ ≤ lemma66_colNorm2 B j := h j
    _ ≤ lemma66_colNorm1 B j := lemma66_colNorm2_le_colNorm1 B j

/-- **Higham Lemma 6.6 (a)(ii).**  If `‖a_j‖₂ ≤ ‖b_j‖₂` for every column `j`,
    then `‖A‖₂ ≤ sqrt(rank B) · ‖B‖₂`.

    Proof by Higham's chain `‖A‖₂ ≤ ‖A‖_F ≤ ‖B‖_F ≤ sqrt(rank B) ‖B‖₂`.
    The `0 < n` hypothesis is the (non-degenerate column count) condition
    carried by the underlying `‖A‖₂ ≤ ‖A‖_F` step in `Norms.lean`. -/
theorem lemma66_a_op2_le {m n : ℕ} (hn : 0 < n) (A B : CMatrix m n)
    (h : ∀ j, lemma66_colNorm2 A j ≤ lemma66_colNorm2 B j) :
    complexMatrixOp2 A ≤ Real.sqrt (complexMatrixRank B : ℝ) * complexMatrixOp2 B :=
  calc complexMatrixOp2 A
      ≤ complexMatrixFrobenius A := complexMatrixOp2_le_complexMatrixFrobenius hn A
    _ ≤ complexMatrixFrobenius B := lemma66_a_frobenius_le A B h
    _ ≤ Real.sqrt (complexMatrixRank B : ℝ) * complexMatrixOp2 B :=
        complexMatrixFrobenius_le_sqrt_rank_mul_complexMatrixOp2 B

/-!
### Lemma 6.6 (c): entrywise domination
-/

/-- Entrywise absolute-value domination `|A| ≤ |B|` implies columnwise
    squared-2-norm domination. -/
lemma lemma66_colNormSq_le_of_abs_entry_le {m n : ℕ} (A B : CMatrix m n)
    (h : ∀ i j, ‖A i j‖ ≤ ‖B i j‖) (j : Fin n) :
    lemma66_colNormSq A j ≤ lemma66_colNormSq B j := by
  unfold lemma66_colNormSq
  exact Finset.sum_le_sum fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (h i j) 2

/-- Entrywise absolute-value domination `|A| ≤ |B|` implies columnwise
    2-norm domination `‖a_j‖₂ ≤ ‖b_j‖₂`. -/
lemma lemma66_colNorm2_le_of_abs_entry_le {m n : ℕ} (A B : CMatrix m n)
    (h : ∀ i j, ‖A i j‖ ≤ ‖B i j‖) (j : Fin n) :
    lemma66_colNorm2 A j ≤ lemma66_colNorm2 B j := by
  rw [lemma66_colNorm2, lemma66_colNorm2]
  exact Real.sqrt_le_sqrt (lemma66_colNormSq_le_of_abs_entry_le A B h j)

/-- **Higham Lemma 6.6 (c).**  If `|A| ≤ |B|` entrywise then
    `‖A‖₂ ≤ sqrt(rank B) · ‖B‖₂`.  Special case of (a). -/
theorem lemma66_c_op2_le {m n : ℕ} (hn : 0 < n) (A B : CMatrix m n)
    (h : ∀ i j, ‖A i j‖ ≤ ‖B i j‖) :
    complexMatrixOp2 A ≤ Real.sqrt (complexMatrixRank B : ℝ) * complexMatrixOp2 B :=
  lemma66_a_op2_le hn A B (lemma66_colNorm2_le_of_abs_entry_le A B h)

/-!
### Sharpness of the `sqrt(rank B)` factor in (a)(ii)/(c)

Higham's note: "the second inequality in (a) is sharp: there is equality if
`A = B` has rank 1".  Taking `A = B = e_{i0} e_{j0}ᵀ` (a standard rank-one
matrix) the hypothesis of (a) holds trivially, `rank B = 1`, `‖B‖₂ = 1`, and
`‖A‖₂ = 1 = sqrt(1) · 1 = sqrt(rank B) · ‖B‖₂`, so the bound is attained with a
positive operator norm (hence not vacuously). -/
theorem lemma66_a_op2_sharp {m n : ℕ} (i0 : Fin m) (j0 : Fin n) :
    ∃ A B : CMatrix m n,
      (∀ j, lemma66_colNorm2 A j ≤ lemma66_colNorm2 B j) ∧
        complexMatrixOp2 A
          = Real.sqrt (complexMatrixRank B : ℝ) * complexMatrixOp2 B ∧
        complexMatrixOp2 A = 1 := by
  refine ⟨complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0),
    complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0),
    fun j => le_refl _, ?_, ?_⟩
  · rw [complexMatrixRank_rankOne_standard_standard i0 j0,
      complexMatrixOp2_rankOne_standard_standard i0 j0]
    simp
  · exact complexMatrixOp2_rankOne_standard_standard i0 j0

end Lemma66

end NumStability
