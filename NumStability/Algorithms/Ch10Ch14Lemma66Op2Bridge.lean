import NumStability.Algorithms.Chapter06Lemma66
import NumStability.Algorithms.HighamChapter10

/-!
# Bridge B5(b): ch6 Lemma 6.6 (op2) → ch10 Cholesky / ch14 inversion 2-norm step

Higham, "Accuracy and Stability of Numerical Algorithms" (2nd ed.).

Both the Cholesky normwise-backward-stability argument (Ch.10, eq. (10.7),
ch10.txt: "The key inequality is (using Lemma 6.6) `‖ |R| ‖₂² ≤ n‖R‖₂²`") and
the matrix-inversion residual argument (Ch.14, §14.3.4, ch14.txt: "From the
inequality `‖ |B| ‖₂ ≤ √n‖B‖₂` for `B ∈ Rⁿˣⁿ` (see Lemma 6.6)") turn a
componentwise/absolute-value bound into an operator (2-)norm bound through **one
and the same** consequence of Higham Lemma 6.6 (c):

    ‖ |B| ‖₂ ≤ √n · ‖B‖₂        (B square, `rank B ≤ n`).

`Chapter06Lemma66.lean` proves the general
`lemma66_c_op2_le : |A| ≤ |B| entrywise → ‖A‖₂ ≤ √(rank B)·‖B‖₂`, but that
theorem was orphaned: the Lean Ch.10 (Cholesky) and Ch.14 (inversion) modules
carried the printed analyses in the *real, componentwise / ∞-norm* layer and
never crossed into the complex `CMatrix` operator-2-norm layer where Lemma 6.6
lives, so the printed 2-norm step above was missing.

This module supplies exactly that missing printed step, as a genuine consumer:
every theorem below applies `lemma66_c_op2_le` in its proof term (instantiated at
`A := complexAbsMatrix B`, whose entries satisfy `‖ |B|ᵢⱼ ‖ = ‖Bᵢⱼ‖`), and then
collapses the `√(rank B)` factor to `√n` via `Matrix.rank_le_width`.

* `lemma66c_absMatrix_op2_le_sqrt_card` — the printed key inequality
  `‖ |B| ‖₂ ≤ √n · ‖B‖₂` cited from Lemma 6.6 in BOTH Ch.10 and Ch.14.
* `lemma66c_ch10_absFactor_op2Sq_le` — the exact squared form
  `‖ |R| ‖₂² ≤ n · ‖R‖₂²` written in ch10.txt (the Ch.10 (10.7) key inequality).
* `lemma66c_ch14_residual_op2_le_sqrt_card` — the Ch.14 residual-lift step:
  a residual matrix `E` componentwise dominated by `|B|` obeys
  `‖E‖₂ ≤ √n · ‖B‖₂` (the `‖G‖₂ ≤ …√n…` move behind `‖X̂A − I‖₂ ≤ dₙu‖A‖₂‖X̂‖₂`).
-/

namespace NumStability

namespace Lemma66Op2Bridge

open scoped BigOperators

/-- Square matrices have `rank ≤ n` (Mathlib `Matrix.rank_le_width`), recast for
the local `complexMatrixRank`. -/
theorem lemma66c_rank_le_card {n : ℕ} (B : CMatrix n n) :
    complexMatrixRank B ≤ n := by
  rw [complexMatrixRank]
  exact Matrix.rank_le_width _

/-- **Bridge / printed key inequality (Higham Lemma 6.6, used in Ch.10 (10.7) and
Ch.14 §14.3.4).**  For a square matrix `B`,

    ‖ |B| ‖₂ ≤ √n · ‖B‖₂,

where `|B| = complexAbsMatrix B` is the entrywise absolute value.  The proof
*applies* `Lemma66.lemma66_c_op2_le` to `A := |B|` (using `‖ |B|ᵢⱼ ‖ = ‖Bᵢⱼ‖`)
and then bounds `√(rank B) ≤ √n` via `lemma66c_rank_le_card`. -/
theorem lemma66c_absMatrix_op2_le_sqrt_card {n : ℕ} (hn : 0 < n) (B : CMatrix n n) :
    complexMatrixOp2 (complexAbsMatrix B) ≤ Real.sqrt (n : ℝ) * complexMatrixOp2 B := by
  have hentry : ∀ i j, ‖complexAbsMatrix B i j‖ ≤ ‖B i j‖ := fun i j =>
    le_of_eq (complexAbsMatrix_norm_apply B i j)
  refine (Lemma66.lemma66_c_op2_le hn (complexAbsMatrix B) B hentry).trans ?_
  have hrank : (complexMatrixRank B : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast lemma66c_rank_le_card B
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hrank) (complexMatrixOp2_nonneg B)

/-- **Higham Ch.10, eq. (10.7) key inequality.**  ch10.txt: "The key inequality
is (using Lemma 6.6) `‖ |R| ‖₂² ≤ n‖R‖₂²`".  Squaring the bridge inequality for
the (square) computed Cholesky factor `R`. -/
theorem lemma66c_ch10_absFactor_op2Sq_le {n : ℕ} (hn : 0 < n) (R : CMatrix n n) :
    complexMatrixOp2 (complexAbsMatrix R) ^ 2 ≤ (n : ℝ) * complexMatrixOp2 R ^ 2 := by
  have hbase := lemma66c_absMatrix_op2_le_sqrt_card hn R
  have h0 : 0 ≤ complexMatrixOp2 (complexAbsMatrix R) := complexMatrixOp2_nonneg _
  calc complexMatrixOp2 (complexAbsMatrix R) ^ 2
      ≤ (Real.sqrt (n : ℝ) * complexMatrixOp2 R) ^ 2 := pow_le_pow_left₀ h0 hbase 2
    _ = Real.sqrt (n : ℝ) ^ 2 * complexMatrixOp2 R ^ 2 := by ring
    _ = (n : ℝ) * complexMatrixOp2 R ^ 2 := by
        rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ))]

/-- **Higham Ch.14, §14.3.4 residual-lift step.**  A residual matrix `E`
componentwise dominated by a square matrix `B` (`|E| ≤ |B|` entrywise) obeys the
2-norm bound `‖E‖₂ ≤ √n · ‖B‖₂` — the `‖G‖₂ ≤ …√n…` move that yields
`‖X̂A − I‖₂ ≤ dₙ u ‖A‖₂ ‖X̂‖₂`.  This applies `Lemma66.lemma66_c_op2_le` directly
to `E` and `B`. -/
theorem lemma66c_ch14_residual_op2_le_sqrt_card {n : ℕ} (hn : 0 < n)
    (E B : CMatrix n n) (h : ∀ i j, ‖E i j‖ ≤ ‖B i j‖) :
    complexMatrixOp2 E ≤ Real.sqrt (n : ℝ) * complexMatrixOp2 B := by
  refine (Lemma66.lemma66_c_op2_le hn E B h).trans ?_
  have hrank : (complexMatrixRank B : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast lemma66c_rank_le_card B
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hrank) (complexMatrixOp2_nonneg B)

end Lemma66Op2Bridge

end NumStability
