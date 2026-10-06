import NumStability.Algorithms.LU.TridiagonalCond

/-!
# Chapter15 Theorem07 TridiagonalLU Basic

Canonical destination for material split out of
`NumStability.Algorithms.LU.TridiagonalCondCh15` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

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

end Ch15
end NumStability
