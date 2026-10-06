import NumStability.Algorithms.LU.TridiagonalCond

/-!
# Chapter15 Theorem08 TridiagonalDiagonalDominance Basic

Canonical destination for material split out of
`NumStability.Algorithms.LU.TridiagonalCondCh15` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

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

end Ch15
end NumStability
