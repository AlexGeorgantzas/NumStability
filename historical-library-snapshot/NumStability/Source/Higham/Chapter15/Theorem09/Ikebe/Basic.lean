import NumStability.Algorithms.LU.TridiagonalCond

/-!
# Chapter15 Theorem09 Ikebe Basic

Canonical destination for material split out of
`NumStability.Algorithms.LU.TridiagonalCondCh15` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

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

end Ch15
end NumStability
