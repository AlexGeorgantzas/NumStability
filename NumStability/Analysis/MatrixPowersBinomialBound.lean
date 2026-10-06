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

import Mathlib.Analysis.CStarAlgebra.Matrix
import NumStability.Analysis.MatrixPowersSchur

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

/-- `‖1‖₂ = 1` for the `l2` operator norm on `Fin n → Fin n` matrices (`n ≥ 1`).
`1 = diagonal 1` and the sup-norm of the all-ones vector is `1`. -/
private theorem opNorm_one [Nonempty (Fin n)] :
    ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = 1 := by
  rw [show (1 : Matrix (Fin n) (Fin n) ℂ)
        = Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
      Matrix.l2_opNorm_diagonal, Pi.norm_def, Finset.sup_const Finset.univ_nonempty]
  simp

/-- `‖U‖₂ = 1` for unitary `U` (`n ≥ 1`).  From `‖Uᴴ U‖ = ‖U‖²` and `Uᴴ U = 1`. -/
private theorem opNorm_unitary [Nonempty (Fin n)]
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ‖U‖ = 1 := by
  have h1 : Uᴴ * U = 1 := by
    have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hsq : ‖Uᴴ * U‖ = ‖U‖ * ‖U‖ := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [h1, opNorm_one] at hsq
  nlinarith [norm_nonneg U]

/-- **Unitary conjugation is an `l2`-op-norm isometry** (`n ≥ 1`):
`‖U M Uᴴ‖₂ = ‖M‖₂` for unitary `U`. -/
private theorem opNorm_unitary_conj [Nonempty (Fin n)]
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖U * M * Uᴴ‖ = ‖M‖ := by
  have hUnorm : ‖U‖ = 1 := opNorm_unitary hU
  have hUHnorm : ‖Uᴴ‖ = 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hUnorm
  have hUHU : Uᴴ * U = 1 := by
    have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hle : ‖U * M * Uᴴ‖ ≤ ‖M‖ := by
    calc ‖U * M * Uᴴ‖ ≤ ‖U * M‖ * ‖Uᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖U‖ * ‖M‖) * ‖Uᴴ‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖M‖ := by rw [hUnorm, hUHnorm]; ring
  have hge : ‖M‖ ≤ ‖U * M * Uᴴ‖ := by
    have hMrw : M = Uᴴ * (U * M * Uᴴ) * U := by
      calc M = (Uᴴ * U) * M * (Uᴴ * U) := by rw [hUHU, Matrix.one_mul, Matrix.mul_one]
        _ = Uᴴ * (U * M * Uᴴ) * U := by simp only [Matrix.mul_assoc]
    calc ‖M‖ = ‖Uᴴ * (U * M * Uᴴ) * U‖ := by rw [← hMrw]
      _ ≤ ‖Uᴴ * (U * M * Uᴴ)‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Uᴴ‖ * ‖U * M * Uᴴ‖) * ‖U‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖U * M * Uᴴ‖ := by rw [hUnorm, hUHnorm]; ring
  exact le_antisymm hle hge

/-!
### (a) Unitary-conjugation isometry for powers  `‖Aᵏ‖₂ = ‖(D + N)ᵏ‖₂`
-/

/-- **(a)** For the Schur split `Uᴴ A U = D + N`, the powers satisfy
`‖Aᵏ‖₂ = ‖(D + N)ᵏ‖₂` (`n ≥ 1`).  Immediate from `pow_eq_unitary_conj`
(`Aᵏ = U (D + N)ᵏ Uᴴ`) and the unitary-conjugation isometry.  Higham §18.1
Schur form `A = Q T Qᴴ`, `T = D + N`. -/
theorem norm_pow_eq_norm_schur_pow [Nonempty (Fin n)]
    {A U D N : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : Uᴴ * A * U = D + N) (k : ℕ) :
    ‖A ^ k‖ = ‖(D + N) ^ k‖ := by
  rw [pow_eq_unitary_conj hU hT k, opNorm_unitary_conj hU]

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

/-- `Ppiece D N k i` = sum of all length-`k` words in `{D, N}` with exactly `i`
factors `N`.  Defined by the Pascal recursion in `k`. -/
private def Ppiece (D N : Matrix (Fin n) (Fin n) ℂ) : ℕ → ℕ → Matrix (Fin n) (Fin n) ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => Ppiece D N k 0 * D
  | k + 1, i + 1 => Ppiece D N k (i + 1) * D + Ppiece D N k i * N

@[simp] private theorem Ppiece_zero_zero (D N : Matrix (Fin n) (Fin n) ℂ) :
    Ppiece D N 0 0 = 1 := rfl

@[simp] private theorem Ppiece_zero_succ (D N : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) :
    Ppiece D N 0 (i + 1) = 0 := rfl

private theorem Ppiece_succ_zero (D N : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    Ppiece D N (k + 1) 0 = Ppiece D N k 0 * D := rfl

private theorem Ppiece_succ_succ (D N : Matrix (Fin n) (Fin n) ℂ) (k i : ℕ) :
    Ppiece D N (k + 1) (i + 1) = Ppiece D N k (i + 1) * D + Ppiece D N k i * N := rfl

/-- Above the diagonal band: `Ppiece D N k i` vanishes when `i > k` (there are no
length-`k` words with more than `k` letters `N`). -/
private theorem Ppiece_eq_zero_of_lt (D N : Matrix (Fin n) (Fin n) ℂ) :
    ∀ k i : ℕ, k < i → Ppiece D N k i = 0 := by
  intro k
  induction k with
  | zero => intro i hi; cases i with
      | zero => exact absurd hi (lt_irrefl 0)
      | succ j => rfl
  | succ m ih =>
    intro i hi
    cases i with
    | zero => exact absurd hi (Nat.not_lt_zero _)
    | succ j =>
      rw [Ppiece_succ_succ, ih (j + 1) (by omega), ih j (by omega)]
      simp

/-- **`(D + N)ᵏ` is the sum of its N-degree pieces:**
`(D + N)ᵏ = Σ_{i=0}^{k} Ppiece D N k i`. -/
private theorem sum_Ppiece (D N : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (D + N) ^ k = ∑ i ∈ Finset.range (k + 1), Ppiece D N k i := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    -- ∑_{i=0}^{m} Ppiece m i * (D + N) = ∑_{i=0}^{m} Ppiece m i * D + ∑ Ppiece m i * N
    have hsplit : ∑ i ∈ Finset.range (m + 1), Ppiece D N m i * (D + N)
        = (∑ i ∈ Finset.range (m + 1), Ppiece D N m i * D)
          + ∑ i ∈ Finset.range (m + 1), Ppiece D N m i * N := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_add]
    rw [hsplit]
    -- Rewrite the RHS `∑_{i=0}^{m+1} Ppiece (m+1) i`, splitting off `i = 0`.
    rw [Finset.sum_range_succ' (fun i => Ppiece D N (m + 1) i) (m + 1)]
    simp only [Ppiece_succ_zero, Ppiece_succ_succ]
    -- RHS = ∑_{j=0}^{m} (Ppiece m (j+1)·D + Ppiece m j·N) + Ppiece m 0·D
    rw [Finset.sum_add_distrib]
    -- Match the N-sum and the D-sum.  The D-sum from LHS is
    -- ∑_{i=0}^{m} Ppiece m i·D = Ppiece m 0·D + ∑_{j=0}^{m-1} Ppiece m (j+1)·D,
    -- and the extra top term Ppiece m (m+1)·D = 0.
    have hDsum : ∑ i ∈ Finset.range (m + 1), Ppiece D N m i * D
        = (∑ j ∈ Finset.range (m + 1), Ppiece D N m (j + 1) * D) + Ppiece D N m 0 * D := by
      rw [Finset.sum_range_succ' (fun i => Ppiece D N m i * D) m,
          Finset.sum_range_succ (fun j => Ppiece D N m (j + 1) * D) m]
      rw [Ppiece_eq_zero_of_lt D N m (m + 1) (by omega)]
      simp [add_comm]
    rw [hDsum]
    abel

/-!
### Band-shifting: the piece with `i` factors `N` lives above the `i`-th diagonal

For `D` diagonal (`D a b = 0`, `a ≠ b`) and `N` strictly upper (`N a b = 0`,
`b ≤ a`), every length-`k` word with exactly `i` factors `N` has its nonzero
entries strictly above the `i`-th super-diagonal.  Each `N` pushes the band out
by one; each `D`, being diagonal, keeps it in place.  Hence `Ppiece D N k i = 0`
once `i ≥ n`: there is no room above the `n`-th super-diagonal in an `n × n`
matrix.  This is what truncates the binomial sum at `i ≤ n - 1`.
-/

/-- Band-shifting bound for the N-degree piece: if `D` is diagonal and `N`
strictly upper, then `(Ppiece D N k i) a b = 0` whenever `b < a + i`. -/
private theorem Ppiece_apply_eq_zero {D N : Matrix (Fin n) (Fin n) ℂ}
    (hD : ∀ a b : Fin n, a ≠ b → D a b = 0)
    (hN : ∀ a b : Fin n, (b : ℕ) ≤ (a : ℕ) → N a b = 0) (k : ℕ) :
    ∀ i : ℕ, ∀ a b : Fin n, (b : ℕ) < (a : ℕ) + i → (Ppiece D N k i) a b = 0 := by
  induction k with
  | zero =>
    intro i a b hab
    cases i with
    | zero =>
      -- Ppiece 0 0 = 1; b < a forces a ≠ b
      rw [Ppiece_zero_zero]
      have : a ≠ b := by
        intro h; rw [h] at hab; simp at hab
      exact Matrix.one_apply_ne this
    | succ j => rw [Ppiece_zero_succ]; rfl
  | succ m ih =>
    intro i a b hab
    cases i with
    | zero =>
      -- Ppiece (m+1) 0 = Ppiece m 0 * D
      rw [Ppiece_succ_zero, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : (c : ℕ) < (a : ℕ) + 0
      · rw [ih 0 a c hc, zero_mul]
      · -- c ≥ a; and b < a (since i = 0), so c ≠ b, D c b = 0
        have hca : (a : ℕ) ≤ (c : ℕ) := by omega
        have hcb : c ≠ b := by
          intro h; rw [h] at hca; omega
        rw [hD c b hcb, mul_zero]
    | succ j =>
      -- Ppiece (m+1) (j+1) = Ppiece m (j+1) * D + Ppiece m j * N
      rw [Ppiece_succ_succ, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
      have hterm1 : ∑ c, (Ppiece D N m (j + 1)) a c * D c b = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        by_cases hc : (c : ℕ) < (a : ℕ) + (j + 1)
        · rw [ih (j + 1) a c hc, zero_mul]
        · have hcb : c ≠ b := by
            intro h; rw [h] at hc; omega
          rw [hD c b hcb, mul_zero]
      have hterm2 : ∑ c, (Ppiece D N m j) a c * N c b = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        by_cases hc : (c : ℕ) < (a : ℕ) + j
        · rw [ih j a c hc, zero_mul]
        · have hbc : (b : ℕ) ≤ (c : ℕ) := by omega
          rw [hN c b hbc, mul_zero]
      rw [hterm1, hterm2, add_zero]

/-- **The N-degree piece vanishes once it needs more room than the matrix has.**
If `D` is diagonal and `N` strictly upper, then `Ppiece D N k i = 0` for `i ≥ n`:
a word with `≥ n` factors `N` would place all its mass strictly above the `n`-th
super-diagonal, of which there is none in an `n × n` matrix.  This is the
`Nⁿ = 0` phenomenon (cf. `strictUpper_pow_eq_zero`) at the level of mixed words. -/
private theorem Ppiece_eq_zero_of_ge {D N : Matrix (Fin n) (Fin n) ℂ}
    (hD : ∀ a b : Fin n, a ≠ b → D a b = 0)
    (hN : ∀ a b : Fin n, (b : ℕ) ≤ (a : ℕ) → N a b = 0) (k i : ℕ) (hi : n ≤ i) :
    Ppiece D N k i = 0 := by
  ext a b
  rw [Matrix.zero_apply]
  refine Ppiece_apply_eq_zero hD hN k i a b ?_
  have hbn : (b : ℕ) < n := b.2
  omega

/-!
### Norm bound on each N-degree piece  `‖Ppiece k i‖ ≤ C(k,i) ‖D‖^{k-i} ‖N‖ⁱ`

There are `C(k,i)` length-`k` words with exactly `i` factors `N`, and each such
word has norm `≤ ‖D‖^{k-i} ‖N‖ⁱ` by submultiplicativity.  We prove the bound on
the *sum* `Ppiece k i` by the same Pascal induction that defines it.
-/

/-- Submultiplicative bound on the N-degree piece:
`‖Ppiece D N k i‖ ≤ C(k,i) · ‖D‖^{k-i} · ‖N‖ⁱ`. -/
private theorem norm_Ppiece_le (D N : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ∀ i : ℕ, ‖Ppiece D N k i‖ ≤ (Nat.choose k i : ℝ) * ‖D‖ ^ (k - i) * ‖N‖ ^ i := by
  induction k with
  | zero =>
    intro i
    cases i with
    | zero =>
      simp only [Ppiece_zero_zero, Nat.choose_self, Nat.cast_one, Nat.zero_sub,
        pow_zero, mul_one]
      -- ‖1‖ ≤ 1
      rw [show (1 : Matrix (Fin n) (Fin n) ℂ)
            = Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
          Matrix.l2_opNorm_diagonal]
      rcases isEmpty_or_nonempty (Fin n) with h | h
      · simp [Pi.norm_def]
      · rw [Pi.norm_def, Finset.sup_const Finset.univ_nonempty]; simp
    | succ j =>
      rw [Ppiece_zero_succ, norm_zero, Nat.choose_zero_succ]
      simp
  | succ m ih =>
    intro i
    cases i with
    | zero =>
      rw [Ppiece_succ_zero]
      calc ‖Ppiece D N m 0 * D‖
          ≤ ‖Ppiece D N m 0‖ * ‖D‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ ((Nat.choose m 0 : ℝ) * ‖D‖ ^ (m - 0) * ‖N‖ ^ 0) * ‖D‖ := by
              gcongr; exact ih 0
        _ = (Nat.choose (m + 1) 0 : ℝ) * ‖D‖ ^ (m + 1 - 0) * ‖N‖ ^ 0 := by
              simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero, mul_one]
              rw [pow_succ]; ring
    | succ j =>
      rw [Ppiece_succ_succ]
      -- ‖A + B‖ ≤ ‖A‖ + ‖B‖, then bound each term.
      have hchoose : (Nat.choose (m + 1) (j + 1) : ℝ)
          = (Nat.choose m j : ℝ) + (Nat.choose m (j + 1) : ℝ) := by
        rw [Nat.choose_succ_succ m j]; push_cast; ring
      -- Term B:  ‖Ppiece m j · N‖ ≤ C(m,j) ‖D‖^{m-j} ‖N‖^{j+1}.
      have hB : ‖Ppiece D N m j * N‖
          ≤ (Nat.choose m j : ℝ) * ‖D‖ ^ (m - j) * ‖N‖ ^ (j + 1) := by
        calc ‖Ppiece D N m j * N‖
            ≤ ‖Ppiece D N m j‖ * ‖N‖ := Matrix.l2_opNorm_mul _ _
          _ ≤ ((Nat.choose m j : ℝ) * ‖D‖ ^ (m - j) * ‖N‖ ^ j) * ‖N‖ := by
                gcongr; exact ih j
          _ = (Nat.choose m j : ℝ) * ‖D‖ ^ (m - j) * ‖N‖ ^ (j + 1) := by
                rw [pow_succ]; ring
      -- Term A:  ‖Ppiece m (j+1) · D‖ ≤ C(m,j+1) ‖D‖^{m-j} ‖N‖^{j+1}.
      have hA : ‖Ppiece D N m (j + 1) * D‖
          ≤ (Nat.choose m (j + 1) : ℝ) * ‖D‖ ^ (m - j) * ‖N‖ ^ (j + 1) := by
        rcases le_or_gt (j + 1) m with hjm | hjm
        · calc ‖Ppiece D N m (j + 1) * D‖
              ≤ ‖Ppiece D N m (j + 1)‖ * ‖D‖ := Matrix.l2_opNorm_mul _ _
            _ ≤ ((Nat.choose m (j + 1) : ℝ) * ‖D‖ ^ (m - (j + 1)) * ‖N‖ ^ (j + 1)) * ‖D‖ := by
                  gcongr; exact ih (j + 1)
            _ = (Nat.choose m (j + 1) : ℝ) * ‖D‖ ^ (m - j) * ‖N‖ ^ (j + 1) := by
                  have hexp : m - (j + 1) + 1 = m - j := by omega
                  rw [← hexp, pow_succ]; ring
        · -- j + 1 > m: the piece is zero, and so is C(m, j+1).
          rw [Ppiece_eq_zero_of_lt D N m (j + 1) hjm, Matrix.zero_mul, norm_zero,
              Nat.choose_eq_zero_of_lt hjm]
          simp
      calc ‖Ppiece D N m (j + 1) * D + Ppiece D N m j * N‖
          ≤ ‖Ppiece D N m (j + 1) * D‖ + ‖Ppiece D N m j * N‖ := norm_add_le _ _
        _ ≤ (Nat.choose m (j + 1) : ℝ) * ‖D‖ ^ (m - j) * ‖N‖ ^ (j + 1)
            + (Nat.choose m j : ℝ) * ‖D‖ ^ (m - j) * ‖N‖ ^ (j + 1) := by
              gcongr
        _ = (Nat.choose (m + 1) (j + 1) : ℝ) * ‖D‖ ^ (m + 1 - (j + 1)) * ‖N‖ ^ (j + 1) := by
              rw [hchoose, show m + 1 - (j + 1) = m - j by omega]; ring

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

/-- **The truncated binomial bound for `(D + N)ᵏ`** (matrix level).  For `D`
diagonal and `N` strictly upper triangular in `ℂⁿˣⁿ`,

    `‖(D + N)ᵏ‖₂ ≤ Σ_{i=0}^{n-1} C(k,i) · ‖D‖₂^{k-i} · ‖N‖₂ⁱ`.

The full sum `(D + N)ᵏ = Σ_{i=0}^{k} Ppiece k i` (`sum_Ppiece`) has every piece with
`i ≥ n` equal to `0` (`Ppiece_eq_zero_of_ge`), so it truncates at `i ≤ n - 1`;
each surviving piece is bounded by `norm_Ppiece_le`.  This is the first line of
Higham's (18.7). -/
theorem opNorm_schurpow_le_binomial {D N : Matrix (Fin n) (Fin n) ℂ}
    (hD : ∀ a b : Fin n, a ≠ b → D a b = 0)
    (hN : ∀ a b : Fin n, (b : ℕ) ≤ (a : ℕ) → N a b = 0) (k : ℕ) :
    ‖(D + N) ^ k‖ ≤ ∑ i ∈ Finset.range n, (Nat.choose k i : ℝ) * ‖D‖ ^ (k - i) * ‖N‖ ^ i := by
  -- Step 1: ‖Σ Ppiece‖ ≤ Σ ‖Ppiece‖ over range (k+1).
  have h1 : ‖(D + N) ^ k‖ ≤ ∑ i ∈ Finset.range (k + 1), ‖Ppiece D N k i‖ := by
    rw [sum_Ppiece D N k]; exact norm_sum_le _ _
  -- Step 2: bound each ‖Ppiece k i‖ by the indicator term.
  set f : ℕ → ℝ := fun i => (Nat.choose k i : ℝ) * ‖D‖ ^ (k - i) * ‖N‖ ^ i with hf
  have h2 : ∑ i ∈ Finset.range (k + 1), ‖Ppiece D N k i‖
      ≤ ∑ i ∈ Finset.range (k + 1), (if i < n then f i else 0) := by
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i < n
    · rw [if_pos hi]; exact norm_Ppiece_le D N k i
    · rw [if_neg hi, Ppiece_eq_zero_of_ge hD hN k i (Nat.not_lt.mp hi), norm_zero]
  -- Step 3: the indicator sum over range (k+1) equals Σ_{i ∈ range n} f i.
  -- Both equal Σ over range (k+1) ∩ range n, since f i = 0 for i > k (C(k,i) = 0).
  have hfzero : ∀ i, k < i → f i = 0 := by
    intro i hi; simp only [hf, Nat.choose_eq_zero_of_lt hi, Nat.cast_zero, zero_mul]
  have h3 : ∑ i ∈ Finset.range (k + 1), (if i < n then f i else 0)
      = ∑ i ∈ Finset.range n, f i := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    -- (range (k+1)).filter (· < n) = (range n).filter (· < k+1)
    have hset : (Finset.range (k + 1)).filter (· < n)
        = (Finset.range n).filter (· < k + 1) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; tauto
    rw [hset]
    -- drop the terms i ∈ range n with i ≥ k+1 (there f i = 0)
    refine Finset.sum_subset (Finset.filter_subset _ _) fun i hi hni => ?_
    rw [Finset.mem_range] at hi
    rw [Finset.mem_filter, Finset.mem_range] at hni
    push_neg at hni
    exact hfzero i (by omega)
  calc ‖(D + N) ^ k‖ ≤ ∑ i ∈ Finset.range (k + 1), ‖Ppiece D N k i‖ := h1
    _ ≤ ∑ i ∈ Finset.range (k + 1), (if i < n then f i else 0) := h2
    _ = ∑ i ∈ Finset.range n, f i := h3

/-!
### Top-level statements over `A`, via the Schur decomposition

We package `schur_triangulation_diag_add_strictUpper A` to expose, for every
`A ∈ ℂⁿˣⁿ`, a unitary `U`, diagonal `D`, and strictly-upper `N` with
`A = U (D + N) Uᴴ`, `ρ(A) = ‖D‖₂` (the max modulus of the eigenvalues), and
`Δ₂(A) = ‖N‖₂`, then state the (18.7) bounds in these terms.
-/

/-- **(a) + (c) + (d) packaged over `A`.**  For every `A ∈ ℂⁿˣⁿ` (`n ≥ 1`) there
is a Schur data set: a unitary `U`, a diagonal `D = diag(λ)` (the eigenvalues),
and a strictly-upper `N`, with `A = U (D + N) Uᴴ`, such that for all `k`:

  * `‖Aᵏ‖₂ = ‖(D + N)ᵏ‖₂`  (the unitary-conjugation isometry, part (a));
  * `‖Aᵏ‖₂ ≤ (‖D‖₂ + ‖N‖₂)ᵏ`  (the crude geometric bound, part (c);
    `‖D‖₂ = ρ(A)`, `‖N‖₂ = Δ₂(A)`);
  * `‖Aᵏ‖₂ ≤ Σ_{i=0}^{n-1} C(k,i) ‖D‖₂^{k-i} ‖N‖₂ⁱ`  (**the target (18.7)**,
    part (d)).

Here `‖D‖₂ = ‖fun i ↦ (Uᴴ A U) i i‖ = maxᵢ |λᵢ| = ρ(A)` and `‖N‖₂ = Δ₂(A)` for
this Schur `N`.  Higham (18.7), p. 344.  The `ρ(A) > 0` hypothesis of (18.7) is
not needed for these *upper* bounds. -/
theorem exists_schur_powerBounds [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (U D N : Matrix (Fin n) (Fin n) ℂ),
      U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      (∃ d : Fin n → ℂ, D = Matrix.diagonal d) ∧
      (∀ a b : Fin n, (b : ℕ) ≤ (a : ℕ) → N a b = 0) ∧
      A = U * (D + N) * Uᴴ ∧
      (∀ k, ‖A ^ k‖ = ‖(D + N) ^ k‖) ∧
      (∀ k, ‖A ^ k‖ ≤ (‖D‖ + ‖N‖) ^ k) ∧
      (∀ k, ‖A ^ k‖
          ≤ ∑ i ∈ Finset.range n, (Nat.choose k i : ℝ) * ‖D‖ ^ (k - i) * ‖N‖ ^ i) := by
  obtain ⟨U, T, D, N, hUu, hUeq, hUtri, hDdef, hNdef, hTDN⟩ :=
    schur_triangulation_diag_add_strictUpper A
  have hTeq : Uᴴ * A * U = D + N := by rw [hUeq, hTDN]
  have hD : ∀ a b : Fin n, a ≠ b → D a b = 0 := by
    intro a b hab; rw [hDdef, Matrix.diagonal_apply, if_neg hab]
  have hN : ∀ a b : Fin n, (b : ℕ) ≤ (a : ℕ) → N a b = 0 := by
    intro a b hba; rw [hNdef a b]; exact if_neg (by omega)
  have hAeq : A = U * (D + N) * Uᴴ := by
    rw [← hTDN]; exact eq_unitary_conj_of_schur hUu hUeq
  refine ⟨U, D, N, hUu, ⟨fun i => T i i, hDdef⟩, hN, hAeq, ?_, ?_, ?_⟩
  · intro k; exact norm_pow_eq_norm_schur_pow hUu hTeq k
  · intro k
    rw [norm_pow_eq_norm_schur_pow hUu hTeq k]
    exact opNorm_pow_le_geometric D N k
  · intro k
    rw [norm_pow_eq_norm_schur_pow hUu hTeq k]
    exact opNorm_schurpow_le_binomial hD hN k

/-- **(b) The `ρ(A) = 0` (nilpotent) sub-case of (18.7).**  If the diagonal Schur
factor `D` vanishes (all eigenvalues `0`, i.e. `ρ(A) = 0`), then `T = N` is
strictly upper triangular, hence nilpotent (`Nⁿ = 0`), and

  * `‖Aᵏ‖₂ ≤ ‖N‖₂ᵏ = Δ₂(A)ᵏ`  for all `k`  (Higham's `Δ₂(A)ᵏ` bound), and
  * `‖Aᵏ‖₂ = 0`  for `k ≥ n`  (the powers vanish beyond `n`).

Higham (18.7), second line (`ρ(A) = 0`, `k < n`), plus the stronger `k ≥ n` fact.
`Δ₂(A) = ‖N‖₂` for this Schur `N`. -/
theorem norm_pow_nilpotent [Nonempty (Fin n)] {A U N : Matrix (Fin n) (Fin n) ℂ}
    (hUu : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hTeq : Uᴴ * A * U = N)
    (hN : ∀ a b : Fin n, (b : ℕ) ≤ (a : ℕ) → N a b = 0) :
    (∀ k, ‖A ^ k‖ ≤ ‖N‖ ^ k) ∧ (∀ k, n ≤ k → ‖A ^ k‖ = 0) := by
  -- `‖Aᵏ‖ = ‖Nᵏ‖` by the isometry (with `D = 0`).
  have hiso : ∀ k, ‖A ^ k‖ = ‖N ^ k‖ := by
    intro k
    have := norm_pow_eq_norm_schur_pow (D := (0 : Matrix (Fin n) (Fin n) ℂ)) (N := N)
      hUu (by rw [zero_add]; exact hTeq) k
    rwa [zero_add] at this
  have hpow : ∀ k, ‖N ^ k‖ ≤ ‖N‖ ^ k := by
    intro k
    induction k with
    | zero =>
        rw [pow_zero, pow_zero,
            show (1 : Matrix (Fin n) (Fin n) ℂ)
              = Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
            Matrix.l2_opNorm_diagonal, Pi.norm_def,
            Finset.sup_const Finset.univ_nonempty]
        simp
    | succ m ih =>
        rw [pow_succ, pow_succ]
        calc ‖N ^ m * N‖ ≤ ‖N ^ m‖ * ‖N‖ := Matrix.l2_opNorm_mul _ _
          _ ≤ ‖N‖ ^ m * ‖N‖ := by gcongr
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · rw [hiso k]; exact hpow k
  · rw [hiso k]
    -- N is nilpotent: Nⁿ = 0, so Nᵏ = 0 for k ≥ n.
    have hNn : N ^ n = 0 := strictUpper_pow_eq_zero hN
    have hNk : N ^ k = 0 := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [pow_add, hNn, Matrix.zero_mul]
    rw [hNk, norm_zero]

end

end NumStability
