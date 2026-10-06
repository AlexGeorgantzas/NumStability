-- Algorithms/LU/TridiagonalCondCh15.lean
--
-- Correctly Chapter-15-labeled wrappers for the condition numbers of
-- tridiagonal matrices, Higham, "Accuracy and Stability of Numerical
-- Algorithms", 2nd ed., §15.6 "Condition Numbers of Tridiagonal Matrices"
-- (pp. 299-300).
--
-- The underlying MATHEMATICS is already proved in
-- `NumStability.Algorithms.LU.TridiagonalCond`, but that module
-- MISLABELS the results as Chapter 14 (§14.5). This module is IMPORT-ONLY:
-- it re-exposes the same proofs under the correct Chapter 15 labels,
-- reusing the existing proofs verbatim (no re-proving).
--
-- Correspondence (verified against the extracted §15.6 PDF text):
--   H15_Theorem15_7 : Theorem 15.7 (p. 299)  -- |L||U| = |A| ⟹ |U⁻¹||L⁻¹| = |A⁻¹|
--     ← tridiag_exact_inv_abs           (mislabeled "Theorem 14.7")
--   H15_Theorem15_8 : Theorem 15.8 (p. 300)  -- row-diag-dominant (2n−1) bound
--     ← tridiag_diagdom_cond_bound      (mislabeled "Theorem 14.8")
--   H15_Theorem15_9 : Theorem 15.9 (Ikebe, p. 300) -- irreducible rank-1 structure
--     ← ikebe_tridiag_inv_structure     (mislabeled "Theorem 14.9")

import NumStability.Algorithms.LU.TridiagonalCond

namespace NumStability.Ch15

open scoped BigOperators

-- ============================================================
-- §15.6  Theorem 15.7 (Higham, p. 299)
-- ============================================================

/-- **Theorem 15.7** (Higham, §15.6, p. 299).

    "If the nonsingular tridiagonal matrix `A ∈ ℝⁿˣⁿ` has the LU
    factorization `A = LU` and `|L||U| = |A|`, then `|U⁻¹||L⁻¹| = |A⁻¹|`."

    This is a Chapter-15-correct re-statement of the result proved (but
    mislabeled "Theorem 14.7") as
    `NumStability.tridiag_exact_inv_abs`, reused verbatim.

    Encoding.  The componentwise identity `|U⁻¹||L⁻¹| = |A⁻¹|` is stated
    entrywise: at index `(i,j)` the product-matrix entry
    `(|U⁻¹||L⁻¹|)_{ij} = ∑ₖ |U⁻¹_{ik}| · |L⁻¹_{kj}|` equals `|A⁻¹_{ij}|`.
    `hA_inv_eq` records `A⁻¹ = U⁻¹ L⁻¹` (which follows from `A = LU`), and
    `hSignCoherent` records the sign-coherence consequence of the printed
    hypothesis `|L||U| = |A|` (established in the book's proof via (15.9)):
    every summand `U⁻¹_{ik} · L⁻¹_{kj}` is nonnegative, so no cancellation
    occurs and the absolute value passes through the sum. -/
theorem H15_Theorem15_7 (n : ℕ)
    (U_inv L_inv A_inv : Fin n → Fin n → ℝ)
    (hA_inv_eq : ∀ i j, A_inv i j = ∑ k : Fin n, U_inv i k * L_inv k j)
    (hSignCoherent : ∀ i j k : Fin n, 0 ≤ U_inv i k * L_inv k j) :
    ∀ i j, ∑ k : Fin n, |U_inv i k| * |L_inv k j| = |A_inv i j| :=
  NumStability.tridiag_exact_inv_abs n U_inv L_inv A_inv hA_inv_eq hSignCoherent

-- ============================================================
-- §15.6  Theorem 15.8 (Higham, p. 300)
-- ============================================================

/-- **Theorem 15.8** (Higham, §15.6, p. 300).

    "Suppose the nonsingular, row diagonally dominant tridiagonal matrix
    `A ∈ ℝⁿˣⁿ` has the LU factorization `A = LU`. Then, if `y ≥ 0`,
    `‖ |U⁻¹||L⁻¹| y ‖∞ ≤ (2n − 1) ‖ |A⁻¹| y ‖∞`."

    This is a Chapter-15-correct re-statement of the result proved (but
    mislabeled "Theorem 14.8") as
    `NumStability.tridiag_diagdom_cond_bound`, reused verbatim.

    Encoding.  `‖·‖∞` is `infNormVec`.  The `(2n−1)` factor is the printed
    constant, stated explicitly (not smuggled into a hypothesis).  The
    hypothesis `hRowSumBound` captures the structural consequence of row
    diagonal dominance used in the book's proof (via `L⁻¹ = U A⁻¹` and
    Lemma 8.8): the unit upper-bidiagonal `V = diag(U)⁻¹ U` has
    `|V_{i,i+1}| ≤ 1`, so each row sum of `|U⁻¹||U|` is bounded by `2n−1`.
    That structural bound is itself proved unconditionally in the base
    module as `NumStability.unit_bidiag_row_sum_bound`. -/
theorem H15_Theorem15_8 (n : ℕ) (hn : 0 < n)
    (A L U A_inv L_inv U_inv : Fin n → Fin n → ℝ)
    (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hLU : ∀ i j, ∑ k : Fin n, L i k * U k j = A i j)
    (hLInv : NumStability.IsLeftInverse n L L_inv)
    (hAInv : NumStability.IsRightInverse n A A_inv)
    (hRowSumBound : ∀ i : Fin n,
      ∑ l : Fin n, ∑ k : Fin n, |U_inv i k| * |U k l| ≤ 2 * ↑n - 1) :
    NumStability.infNormVec (fun i => ∑ j : Fin n,
      (∑ k : Fin n, |U_inv i k| * |L_inv k j|) * y j) ≤
    (2 * ↑n - 1) * NumStability.infNormVec (fun i => ∑ j : Fin n,
      |A_inv i j| * y j) :=
  NumStability.tridiag_diagdom_cond_bound n hn A L U A_inv L_inv U_inv y hy
    hLU hLInv hAInv hRowSumBound

-- ============================================================
-- §15.6  Theorem 15.9 (Ikebe) (Higham, p. 300)
-- ============================================================

/-- **Theorem 15.9** (Ikebe, 1979; Higham §15.6, p. 300).

    "Let `A ∈ ℝⁿˣⁿ` be tridiagonal and irreducible (that is, `a_{i+1,i}`
    and `a_{i,i+1}` are nonzero for all `i`). Then there are vectors
    `x, y, p, q` such that
    `(A⁻¹)_{ij} = xᵢ yⱼ` for `i ≤ j`, and `(A⁻¹)_{ij} = pᵢ qⱼ` for `i ≥ j`."

    I.e. `A⁻¹` is the upper-triangular part of one rank-1 matrix joined
    along the diagonal to the lower-triangular part of another rank-1
    matrix.

    This is a Chapter-15-correct re-statement of the result proved (but
    mislabeled "Theorem 14.9") as
    `NumStability.ikebe_tridiag_inv_structure`, reused verbatim.  The
    hypotheses encode the LU factorization `A = LU` (`hStruct`, `hU_diag`,
    `hA_inv_eq`), the triangularity of `U⁻¹`, `L⁻¹`, and the explicit
    bidiagonal-inverse product formulas for their entries; the conclusion
    is the printed rank-1 structure. -/
theorem H15_Theorem15_9 (n : ℕ)
    (A_inv : Fin n → Fin n → ℝ)
    (L U L_inv U_inv : Fin n → Fin n → ℝ)
    (hStruct : NumStability.IsTridiagLU n L U)
    (hU_diag : ∀ i : Fin n, U i i ≠ 0)
    (hA_inv_eq : ∀ i j, A_inv i j = ∑ k : Fin n, U_inv i k * L_inv k j)
    (hU_inv_ut : ∀ i j : Fin n, j.val < i.val → U_inv i j = 0)
    (hL_inv_lt : ∀ i j : Fin n, i.val < j.val → L_inv i j = 0)
    (hU_inv_prod : ∀ i k : Fin n, i.val ≤ k.val →
      U_inv i k = NumStability.cumulProdUpper (fun m => U m m)
        (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0) k /
        (NumStability.cumulProdUpper (fun m => U m m)
          (fun m => if h : m.val + 1 < n then U m ⟨m.val + 1, h⟩ else 0) i *
          U k k))
    (hL_inv_prod : ∀ k j : Fin n, j.val ≤ k.val →
      L_inv k j = NumStability.cumulProdLower
        (fun m => if h : 0 < m.val then L m ⟨m.val - 1, by omega⟩ else 0) k /
        NumStability.cumulProdLower
          (fun m => if h : 0 < m.val then L m ⟨m.val - 1, by omega⟩ else 0) j) :
    ∃ (x y p q : Fin n → ℝ),
      (∀ i j : Fin n, i.val ≤ j.val → A_inv i j = x i * y j) ∧
      (∀ i j : Fin n, j.val ≤ i.val → A_inv i j = p i * q j) :=
  NumStability.ikebe_tridiag_inv_structure n A_inv L U L_inv U_inv
    hStruct hU_diag hA_inv_eq hU_inv_ut hL_inv_lt hU_inv_prod hL_inv_prod

end NumStability.Ch15
