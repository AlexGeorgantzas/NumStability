import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Analysis.LinearOperators.MatrixPowers.Henrici.BinomialPowerBound

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

/-
Analysis/MatrixPowersBinomialBound.lean

**§18.1 / eq. (18.7): the 2-norm power bounds via the Schur form** (Higham,
*Accuracy and Stability of Numerical Algorithms*, 2nd ed., Section 18.1, pp.
344-345).

Higham (p. 344, attributing the bounds to Henrici's *departure from normality*)
states, for `A ∈ ℂⁿˣⁿ` with Schur decomposition `Qᴴ A Q = D + N` (`D` diagonal
holding the eigenvalues, `N` strictly upper triangular) and
`Δ₂(A) = ‖N‖₂ = min_{N ∈ S} ‖N‖₂`, the departure from normality:

    ‖Aᵏ‖₂ ≤ ⎧ Σ_{i=0}^{n-1} C(k,i) ρ(A)^{k-i} Δ₂(A)ⁱ,   ρ(A) > 0,          (18.7)
            ⎨
            ⎩ Δ₂(A)ᵏ,                                     ρ(A) = 0 and k < n.

This file re-uses the Schur machinery of `MatrixPowersSchur.lean`
(`pow_eq_unitary_conj`, `strictUpper_pow_eq_zero`,
`schur_triangulation_diag_add_strictUpper`, and the `l2`-op-norm facts) and
proves, in increasing difficulty:

  * `norm_pow_eq_norm_schur_pow` — (a) the unitary-conjugation isometry
    `‖Aᵏ‖₂ = ‖(D + N)ᵏ‖₂`.
  * `norm_diag_schur_eq_rho` — the reading `‖D‖₂ = ρ(A) = maxᵢ |λᵢ|`
    (`l2_opNorm_diagonal`).
  * `opNorm_pow_le_geometric` — (c) the crude geometric bound
    `‖(D + N)ᵏ‖₂ ≤ (‖D‖₂ + ‖N‖₂)ᵏ`, i.e. `‖Aᵏ‖₂ ≤ (ρ(A) + Δ₂(A))ᵏ`.
  * `sum_binomial_eq_geometric` — the untruncated binomial identity
    `Σ_{i=0}^{k} C(k,i) ‖D‖^{k-i} ‖N‖ⁱ = (‖D‖ + ‖N‖)ᵏ`, i.e. (c) as a sum.
  * `norm_pow_nilpotent` — (b) the `ρ(A) = 0` (nilpotent, `D = 0`, `T = N`)
    sub-case of (18.7): `‖Aᵏ‖₂ ≤ Δ₂(A)ᵏ` for all `k` and `‖Aᵏ‖₂ = 0` for `k ≥ n`.
  * `exists_schur_powerBounds` — the packaged statement over an arbitrary `A`,
    combining (a), (c), and **(d) THE TARGET**, the truncated bound
    `‖Aᵏ‖₂ ≤ Σ_{i=0}^{n-1} C(k,i) ‖D‖₂^{k-i} ‖N‖₂ⁱ` (first line of (18.7)),
    valid for all `A` (the `ρ(A) > 0` hypothesis in (18.7) is not needed for the
    *upper* bound: with `ρ = 0` the truncated sum still dominates `‖Aᵏ‖₂`).  The
    matrix-level target is `opNorm_schurpow_le_binomial`.

HONEST STATEMENT STRENGTH.  Everything below is unconditional.  The `Δ₂(A)` that
appears is `‖N‖₂` for the specific Schur factor `N` produced by
`schur_triangulation_diag_add_strictUpper` — this is a *valid* Schur `N` so
`Δ₂(A) = min_{N ∈ S} ‖N‖₂ ≤ ‖N‖₂`; hence our bounds with `‖N‖₂` in place of the
minimising `Δ₂(A)` are the honest, possibly-weaker, *always-true* form.  We do
NOT claim the minimum is attained by this `N`.  `ρ(A)` is read as `‖fun i ↦ T i i‖`
(the Pi sup-norm of the diagonal = `maxᵢ |λᵢ|`), exactly as in
`MatrixPowersSchur.lean`.

The truncation at `i ≤ n - 1` (the content that makes (18.7) sharper than the
crude `(ρ + Δ₂)ᵏ`) is obtained *without* the Jordan form and *without* a
noncommutative binomial theorem: we decompose `(D + N)ᵏ` into the `k + 1`
"N-degree pieces" `P k i` = sum of all length-`k` words in `{D, N}` containing
exactly `i` factors `N`, via the Pascal recursion `P(k+1,i) = P(k,i)·D +
P(k,i-1)·N`.  A band-shifting argument (each `N` pushes the nonzero band one
super-diagonal out, `D` diagonal preserves it) shows `P k i = 0` for `i ≥ n`, so
the sum `(D+N)ᵏ = Σ_{i=0}^k P k i` truncates at `n - 1`; submultiplicativity
bounds `‖P k i‖ ≤ C(k,i) ‖D‖^{k-i} ‖N‖ⁱ`.
-/




open scoped Matrix.Norms.L2Operator BigOperators Matrix

namespace NumStability

noncomputable section

variable {n : ℕ}

/-!
### `l2`-operator-norm helpers

`MatrixPowersSchur.lean` proves the unitary-conjugation isometry but keeps it
`private`, so we re-prove the tiny facts we need here, exactly as that file does:
`‖1‖₂ = 1`, `‖U‖₂ = 1` for unitary `U`, and `‖U M Uᴴ‖₂ = ‖M‖₂`.
-/












































/-!
### (a) Unitary-conjugation isometry for powers  `‖Aᵏ‖₂ = ‖(D + N)ᵏ‖₂`
-/











/-!
### `‖D‖₂ = ρ(A)` and the geometric bound
-/

/-- `‖diagonal d‖₂ = ‖d‖∞ = maxᵢ |dᵢ| = ρ(A)`, the spectral radius read off the
diagonal Schur factor.  Higham §18.1 (`ρ(A) = maxᵢ |λᵢ|`); `l2_opNorm_diagonal`. -/
theorem norm_diag_schur_eq_rho (d : Fin n → ℂ) :
    ‖(Matrix.diagonal d : Matrix (Fin n) (Fin n) ℂ)‖ = ‖d‖ :=
  Matrix.l2_opNorm_diagonal d

/-- **(c) Crude geometric bound.**  For any square matrices `D`, `N`,
`‖(D + N)ᵏ‖₂ ≤ (‖D‖₂ + ‖N‖₂)ᵏ`, by induction using submultiplicativity
(`l2_opNorm_mul`) and the triangle inequality.  With the Schur split this is
`‖Aᵏ‖₂ ≤ (ρ(A) + Δ₂(A))ᵏ`, Higham's coarse bound preceding (18.7). -/
theorem opNorm_pow_le_geometric (D N : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ‖(D + N) ^ k‖ ≤ (‖D‖ + ‖N‖) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero,
      show (1 : Matrix (Fin n) (Fin n) ℂ)
        = Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
      Matrix.l2_opNorm_diagonal]
    rcases isEmpty_or_nonempty (Fin n) with h | h
    · simp [Pi.norm_def]
    · rw [Pi.norm_def, Finset.sup_const Finset.univ_nonempty]; simp
  | succ m ih =>
    have hDN : ‖D + N‖ ≤ ‖D‖ + ‖N‖ := norm_add_le D N
    rw [pow_succ, pow_succ]
    calc ‖(D + N) ^ m * (D + N)‖
        ≤ ‖(D + N) ^ m‖ * ‖D + N‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖D‖ + ‖N‖) ^ m * (‖D‖ + ‖N‖) := by gcongr

/-!
### N-degree decomposition of `(D + N)ᵏ`  (the honest route to the truncation)

We split `(D + N)ᵏ` into its `k + 1` "N-degree pieces": `Ppiece D N k i` is the
sum of all length-`k` words in `{D, N}` containing exactly `i` factors `N`.  The
Pascal recursion is `Ppiece (k+1) i = Ppiece k i · D + Ppiece k (i-1) · N`
(append a `D`, keeping the N-count, or append an `N`, raising it by one).
-/






































































/-!
### Band-shifting: the piece with `i` factors `N` lives above the `i`-th diagonal

For `D` diagonal (`D a b = 0`, `a ≠ b`) and `N` strictly upper (`N a b = 0`,
`b ≤ a`), every length-`k` word with exactly `i` factors `N` has its nonzero
entries strictly above the `i`-th super-diagonal.  Each `N` pushes the band out
by one; each `D`, being diagonal, keeps it in place.  Hence `Ppiece D N k i = 0`
once `i ≥ n`: there is no room above the `n`-th super-diagonal in an `n × n`
matrix.  This is what truncates the binomial sum at `i ≤ n - 1`.
-/

































































/-!
### Norm bound on each N-degree piece  `‖Ppiece k i‖ ≤ C(k,i) ‖D‖^{k-i} ‖N‖ⁱ`

There are `C(k,i)` length-`k` words with exactly `i` factors `N`, and each such
word has norm `≤ ‖D‖^{k-i} ‖N‖ⁱ` by submultiplicativity.  We prove the bound on
the *sum* `Ppiece k i` by the same Pascal induction that defines it.
-/








































































/-!
### The untruncated binomial form  `Σ_{i=0}^{k} C(k,i) ρ^{k-i} Δ₂ⁱ = (ρ + Δ₂)ᵏ`

Before the truncation at `i ≤ n - 1`, the *full* sum over `i ≤ k` collapses to
the crude geometric bound `(‖D‖ + ‖N‖)ᵏ` by the ordinary (commutative, real)
binomial theorem.  This is the "untruncated" fallback form of (18.7): every term
of the truncated sum is `≥ 0`, so the truncated bound is no larger than this.
-/

/-- The untruncated binomial identity in `ℝ`:
`Σ_{i=0}^{k} C(k,i) ‖D‖^{k-i} ‖N‖ⁱ = (‖D‖ + ‖N‖)ᵏ`.  (`add_pow` / `Commute.add_pow`.) -/
theorem sum_binomial_eq_geometric (D N : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ) * ‖D‖ ^ (k - i) * ‖N‖ ^ i
      = (‖D‖ + ‖N‖) ^ k := by
  rw [add_pow, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hidx : k + 1 - 1 - i = k - i := by omega
  rw [hidx]
  have h1 : k - (k - i) = i := by omega
  rw [h1, Nat.choose_symm (by omega : i ≤ k)]
  ring


/-!
### (d) The truncated binomial bound at the matrix level
-/















































/-!
### Top-level statements over `A`, via the Schur decomposition

We package `schur_triangulation_diag_add_strictUpper A` to expose, for every
`A ∈ ℂⁿˣⁿ`, a unitary `U`, diagonal `D`, and strictly-upper `N` with
`A = U (D + N) Uᴴ`, `ρ(A) = ‖D‖₂` (the max modulus of the eigenvalues), and
`Δ₂(A) = ‖N‖₂`, then state the (18.7) bounds in these terms.
-/





















































































end

end NumStability
