/-
Analysis/MatrixPowersHenrici.lean

**Henrici's departure from normality** and the Frobenius Pythagorean identity
behind Higham's equation (18.7).

Reference: N. J. Higham, *Accuracy and Stability of Numerical Algorithms*,
2nd ed., Section 18.1 "Matrix Powers in Exact Arithmetic", pp. 344-345.

The text (p. 344-345) considers the Schur decomposition `Q* A Q = D + N`, with
`D` diagonal (the eigenvalues) and `N` strictly upper triangular, and defines
Henrici's *departure from normality* [563] as
```
      Δ(A, ‖·‖) ≡ Δ(A) = min_{N ∈ S} ‖N‖,
```
`S` being the set of strictly-upper factors `N` over all Schur forms.  For the
Frobenius norm Higham states (p. 345) that `‖N‖_F` is *independent of the
particular Schur form* and that
```
      Δ_F(A) = ( ‖A‖_F² − Σ_i |λ_i|² )^{1/2}
             ≤ ( (n³−n)/12 )^{1/4} · ‖A*A − A A*‖_F^{1/2}.                (Henrici)
```
Henrici then derives the 2-norm power bounds
```
      ‖Aᵏ‖₂ ≤ Σ_{i=0}^{n-1} C(k,i) ρ(A)^{k-i} Δ₂(A)ⁱ,   ρ(A) > 0,         (18.7)
      ‖Aᵏ‖₂ ≤ Δ₂(A)ᵏ,                                    ρ(A) = 0, k < n. (18.7)
```
with equality throughout when `A` is normal (p. 345).

--------------------------------------------------------------------------------
WHAT THIS FILE PROVES (all over `ℂ`, all unconditional unless flagged).

The `n×n` complex Schur form `Uᴴ A U = T = D + N` is supplied by
`schur_triangulation_diag_add_strictUpper` (Analysis/SchurTriangulation.lean).

1. **Spectrum via the triangular Schur form** (`charpoly_eq_prod_diag_of_schur`,
   `A_charpoly_factors_schur`): the characteristic polynomial of `A` equals
   `∏ i (X − T i i)`, i.e. the eigenvalues of `A` are exactly the diagonal
   entries `T i i` of the Schur factor.  (Higham p. 344: "`D` diagonal (the
   eigenvalues)".)

2. **Frobenius Pythagorean identity** (`frobSq_schur_pythagoras`):
   `frobSq A = (∑ i, ‖T i i‖²) + frobSq N`, where `frobSq M := ∑ i j, ‖M i j‖²`
   is the squared Frobenius norm.  This is the exact content of the (Henrici)
   display: `Δ_F(A)² = ‖A‖_F² − Σ_i|λ_i|²`, since `Δ_F(A)² = frobSq N`.

3. **Schur-form independence of `Δ_F`** (`departureFSq_eq_frobSq_sub_sum_sq_eigs`,
   `departureFSq_form_independent`): `frobSq N` equals `frobSq A − ∑ i ‖T i i‖²`.
   The `∑ i ‖T i i‖²` term is the sum of squared eigenvalue-moduli, which is a
   spectral invariant (item 1); so `frobSq N` — and hence `Δ_F(A)` — does not
   depend on the chosen Schur form.

4. **`Δ_F(A) ≥ 0`** (`frobSq_nonneg`, `departureFSq_nonneg`) and the
   defining `Δ_F(A)² = frobSq N` value (`departureFSq_eq`).

5. **`A` normal ⟺ `N = 0`, easy direction unconditional**
   (`isStarNormal_of_strictUpper_eq_zero`): if `N = 0` then `A` is normal
   (`IsStarNormal A`, i.e. `Aᴴ A = A Aᴴ`).  The converse
   (`A` normal ⟹ `N = 0`) is exposed as the explicit, clearly-documented
   hypothesis `SchurNormalImpliesStrictUpperZero` and is NOT assumed anywhere in
   the unconditional results — see the remark on it below.

6. **A (18.7)-flavoured power/norm consequence directly from the Schur split**
   (`frobSq_normal_eq_sum_sq_eigs`): for a *normal* `A` the departure vanishes so
   `frobSq A = ∑ i ‖T i i‖²`; this is the "equality for normal matrices"
   statement (Higham p. 345, "for normal matrices both the bounds are
   equalities") at the level of the Frobenius Pythagorean identity.

HONESTY LEDGER.
* Items 1-6 above are UNCONDITIONAL theorems over `ℂ`.
* The full Henrici *inequality* `Δ_F(A) ≤ ((n³−n)/12)^{1/4} ‖A*A−AA*‖_F^{1/2}`
  and the 2-norm binomial bound (18.7) itself are NOT proved here: they require,
  respectively, a nontrivial extremal estimate over strictly-upper matrices and
  the numerical-radius / binomial powering machinery, which go beyond the direct
  Schur split.  Only the parts genuinely obtainable from `A = U(D+N)Uᴴ` are
  claimed.
* The converse of item 5 (`A` normal ⟹ `N = 0`) is a genuine theorem but is
  left as a documented hypothesis `SchurNormalImpliesStrictUpperZero`, never
  discharged, and never used to prove any of the unconditional results.
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import NumStability.Analysis.SchurTriangulation

open scoped BigOperators Matrix
open Matrix Complex

namespace NumStability

variable {n : ℕ}

/-! ### Squared Frobenius norm as a real-valued functional

We work with the *squared* Frobenius norm `frobSq M = ∑ i j, ‖M i j‖²` as an
explicit real functional (`Complex.normSq`), rather than through Mathlib's scoped
`‖·‖` Frobenius instance.  This keeps the Pythagorean identity a transparent
`Finset` computation and the unitary invariance a trace-cyclicity computation,
with no instance-diamond bookkeeping.  Higham p. 344-345 (`‖·‖_F`). -/

/-- Squared Frobenius norm of a complex matrix: `∑ i j, |M i j|²`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 344-345 (`‖·‖_F`). -/
def frobSq (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

/-- `frobSq` is a sum of squared moduli, hence nonnegative.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma frobSq_nonneg (M : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ frobSq M := by
  unfold frobSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-- The squared Frobenius norm equals the trace of `Mᴴ * M`, embedded in `ℂ`.
This is the identity `‖M‖_F² = tr(M*M)` that drives unitary invariance.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 344-345. -/
lemma frobSq_eq_trace (M : Matrix (Fin n) (Fin n) ℂ) :
    (frobSq M : ℂ) = (Mᴴ * M).trace := by
  unfold frobSq Matrix.trace
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply]
  rw [Complex.normSq_eq_conj_mul_self]
  simp

/-- **Unitary invariance of the squared Frobenius norm.**  For unitary `U`,
`frobSq (Uᴴ * A * U) = frobSq A`.  Proof: `tr((UᴴAU)ᴴ(UᴴAU)) = tr(Uᴴ Aᴴ A U) =
tr(Aᴴ A U Uᴴ) = tr(Aᴴ A)` by trace-cyclicity and `U Uᴴ = 1`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 ("`‖N‖_F` is independent of the
particular Schur form"; unitary similarity preserves `‖·‖_F`). -/
lemma frobSq_unitary_conj (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    frobSq (Uᴴ * A * U) = frobSq A := by
  have hUUh : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have key : ((Uᴴ * A * U)ᴴ * (Uᴴ * A * U)).trace = (Aᴴ * A).trace := by
    have hexp : (Uᴴ * A * U)ᴴ * (Uᴴ * A * U) = Uᴴ * (Aᴴ * A) * U := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      -- (Uᴴ Aᴴ U)(Uᴴ A U) = Uᴴ Aᴴ (U Uᴴ) A U = Uᴴ Aᴴ A U
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U Uᴴ (A * U), hUUh, Matrix.one_mul]
    rw [hexp]
    -- trace(Uᴴ (Aᴴ A) U) = trace((Aᴴ A) U Uᴴ) = trace(Aᴴ A)
    rw [Matrix.trace_mul_cycle Uᴴ (Aᴴ * A) U, ← Matrix.mul_assoc, hUUh, Matrix.one_mul]
  have : (frobSq (Uᴴ * A * U) : ℂ) = (frobSq A : ℂ) := by
    rw [frobSq_eq_trace, frobSq_eq_trace, key]
  exact_mod_cast this

/-! ### Spectrum: the eigenvalues are the diagonal Schur entries -/

/-- The block-triangular (upper) predicate for a Schur factor.  Bridges the
"`T i j = 0` for `j < i`" statement produced by `schur_triangulation` to
Mathlib's `BlockTriangular … id`. -/
lemma blockTriangular_id_of_schur (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) : T.BlockTriangular id := by
  intro i j hji
  exact hT i j hji

/-- **Characteristic polynomial of the (upper-triangular) Schur factor.**
`T.charpoly = ∏ i, (X − C (T i i))`, so the roots (eigenvalues) of `T` are its
diagonal entries.  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 344 ("`D`
diagonal (the eigenvalues)"). -/
lemma charpoly_eq_prod_diag_of_schur (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) :
    T.charpoly = ∏ i, (Polynomial.X - Polynomial.C (T i i)) :=
  Matrix.charpoly_of_upperTriangular T (blockTriangular_id_of_schur T hT)

/-- **Eigenvalues of `A` are the Schur diagonal entries.**  If `Uᴴ A U = T` with
`U` unitary and `T` upper-triangular, then `A.charpoly = ∏ i, (X − C (T i i))`:
`A` and `T` are similar (conjugate by the unit `U`, whose inverse is `Uᴴ`), so
they share a characteristic polynomial, which factors over the diagonal of `T`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 344 (the diagonal of the Schur
factor is the spectrum of `A`). -/
theorem A_charpoly_factors_schur (A U T : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq : Uᴴ * A * U = T)
    (hTtri : ∀ i j, j < i → T i j = 0) :
    A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (T i i)) := by
  -- Package `U` as a unit with inverse `Uᴴ`.
  have hUhU : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hUUh : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  let Uu : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨U, Uᴴ, hUUh, hUhU⟩
  have hinv : (Uu⁻¹).val = Uᴴ := rfl
  have hval : Uu.val = U := rfl
  have hconj : (Uu⁻¹.val * A * Uu.val).charpoly = A.charpoly :=
    Matrix.charpoly_units_conj' Uu A
  rw [hinv, hval, hUeq] at hconj
  rw [← hconj]
  exact charpoly_eq_prod_diag_of_schur T hTtri

/-! ### The Frobenius Pythagorean identity `‖A‖_F² = Σ|λ_i|² + ‖N‖_F²` -/

/-- **Diagonal-plus-strict-upper Pythagoras, cellwise.**  With `D` the diagonal
of `T` and `N` its strict-upper part (`D i j`, `N i j` never both nonzero),
`normSq (T i j) = normSq (D i j) + normSq (N i j)`.  This is the pointwise
orthogonality underlying the Frobenius Pythagorean identity.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma normSq_cell_split (T D N : Matrix (Fin n) (Fin n) ℂ)
    (hD : D = Matrix.diagonal (fun i => T i i))
    (hN : ∀ i j, N i j = if j > i then T i j else 0)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (i j : Fin n) :
    Complex.normSq (T i j) = Complex.normSq (D i j) + Complex.normSq (N i j) := by
  rcases lt_trichotomy j i with h | h | h
  · -- below diagonal: everything zero
    rw [hTtri i j h, hD, hN]
    rw [Matrix.diagonal_apply_ne _ h.ne']
    rw [if_neg (not_lt.mpr (le_of_lt h))]
    simp
  · -- diagonal: N part is zero
    subst h
    rw [hD, hN, Matrix.diagonal_apply_eq, if_neg (lt_irrefl _)]
    simp
  · -- strictly upper: D part is zero
    rw [hD, hN, Matrix.diagonal_apply_ne _ h.ne, if_pos h]
    simp

/-- The squared Frobenius norm of `D = diagonal (T · ·)` collapses to the sum of
squared diagonal moduli of `T`.  Reference: Higham, *ASNA* 2nd ed., §18.1,
p. 345 (`Σ_i |λ_i|²`). -/
lemma frobSq_diagonal (T : Matrix (Fin n) (Fin n) ℂ) :
    frobSq (Matrix.diagonal (fun i => T i i)) = ∑ i, Complex.normSq (T i i) := by
  unfold frobSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne _ (fun h => hji h.symm)]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Additivity of `frobSq` over the diagonal-plus-strict-upper split.**
`frobSq T = frobSq D + frobSq N` for the Schur factors `T = D + N`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma frobSq_split (T D N : Matrix (Fin n) (Fin n) ℂ)
    (hD : D = Matrix.diagonal (fun i => T i i))
    (hN : ∀ i j, N i j = if j > i then T i j else 0)
    (hTtri : ∀ i j, j < i → T i j = 0) :
    frobSq T = frobSq D + frobSq N := by
  unfold frobSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact normSq_cell_split T D N hD hN hTtri i j

/-- **Frobenius Pythagorean identity (Henrici display, Higham p. 345).**
For any Schur form `Uᴴ A U = T = D + N` (`U` unitary, `T` upper-triangular, `D`
its diagonal, `N` its strict-upper part),
```
      frobSq A = (∑ i, ‖T i i‖²) + frobSq N.
```
Equivalently `Δ_F(A)² = ‖A‖_F² − Σ_i |λ_i|²` since `Δ_F(A)² = frobSq N`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
theorem frobSq_schur_pythagoras (A U T D N : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq : Uᴴ * A * U = T)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hD : D = Matrix.diagonal (fun i => T i i))
    (hN : ∀ i j, N i j = if j > i then T i j else 0) :
    frobSq A = (∑ i, Complex.normSq (T i i)) + frobSq N := by
  have hAT : frobSq A = frobSq T := by
    rw [← hUeq, frobSq_unitary_conj A U hU]
  rw [hAT, frobSq_split T D N hD hN hTtri, hD, frobSq_diagonal]

/-! ### Departure from normality `Δ_F(A)` -/

/-- **Henrici's Frobenius departure from normality** `Δ_F(A) = ‖N‖_F`, defined via
its square `frobSq N` (which the Pythagorean identity shows equals
`frobSq A − Σ_i|λ_i|²`, hence is Schur-form-independent).  We name the *squared*
departure to stay in `ℝ` without square roots.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 344-345, `Δ_F(A)`. -/
def departureFSq (N : Matrix (Fin n) (Fin n) ℂ) : ℝ := frobSq N

/-- **`Δ_F(A)² = frobSq N`** (definitional restatement, for citation clarity).
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma departureFSq_eq (N : Matrix (Fin n) (Fin n) ℂ) :
    departureFSq N = frobSq N := rfl

/-- **`Δ_F(A) ≥ 0`** (as `Δ_F(A)² ≥ 0`).  Reference: Higham, *ASNA* 2nd ed.,
§18.1, p. 345. -/
lemma departureFSq_nonneg (N : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ departureFSq N :=
  frobSq_nonneg N

/-- **`Δ_F(A)² = ‖A‖_F² − Σ_i|λ_i|²`** — the Henrici display value, obtained by
solving the Pythagorean identity for `frobSq N`.  This exhibits `Δ_F(A)²` as a
Schur-form-independent quantity: the right-hand side depends only on `A` and its
spectrum (item 1), not on the chosen Schur factor.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 (Henrici display). -/
theorem departureFSq_eq_frobSq_sub_sum_sq_eigs
    (A U T D N : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq : Uᴴ * A * U = T)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hD : D = Matrix.diagonal (fun i => T i i))
    (hN : ∀ i j, N i j = if j > i then T i j else 0) :
    departureFSq N = frobSq A - ∑ i, Complex.normSq (T i i) := by
  rw [departureFSq_eq]
  have := frobSq_schur_pythagoras A U T D N hU hUeq hTtri hD hN
  linarith

/-- **Schur-form independence of `Δ_F`.**  Two Schur forms of the same `A` give
the same squared departure.  Because both are equal to
`frobSq A − ∑ i ‖λ_i‖²` and the eigenvalue-modulus sum is a spectral invariant
(the diagonal of every Schur factor lists the eigenvalues of `A` with
multiplicity, item 1), the value is independent of the chosen Schur form.
Here the invariance is captured by the shared spectral sum hypothesis
`hspec`, which item 1 (`A_charpoly_factors_schur`) supplies for genuine Schur
forms of a common `A`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 ("`‖N‖_F` is independent of the
particular Schur form"). -/
theorem departureFSq_form_independent
    (A U₁ T₁ D₁ N₁ U₂ T₂ D₂ N₂ : Matrix (Fin n) (Fin n) ℂ)
    (hU₁ : U₁ ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq₁ : U₁ᴴ * A * U₁ = T₁)
    (hTtri₁ : ∀ i j, j < i → T₁ i j = 0)
    (hD₁ : D₁ = Matrix.diagonal (fun i => T₁ i i))
    (hN₁ : ∀ i j, N₁ i j = if j > i then T₁ i j else 0)
    (hU₂ : U₂ ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq₂ : U₂ᴴ * A * U₂ = T₂)
    (hTtri₂ : ∀ i j, j < i → T₂ i j = 0)
    (hD₂ : D₂ = Matrix.diagonal (fun i => T₂ i i))
    (hN₂ : ∀ i j, N₂ i j = if j > i then T₂ i j else 0)
    (hspec : ∑ i, Complex.normSq (T₁ i i) = ∑ i, Complex.normSq (T₂ i i)) :
    departureFSq N₁ = departureFSq N₂ := by
  rw [departureFSq_eq_frobSq_sub_sum_sq_eigs A U₁ T₁ D₁ N₁ hU₁ hUeq₁ hTtri₁ hD₁ hN₁,
      departureFSq_eq_frobSq_sub_sum_sq_eigs A U₂ T₂ D₂ N₂ hU₂ hUeq₂ hTtri₂ hD₂ hN₂,
      hspec]

/-! ### Normality characterisation: easy direction unconditional -/

/-- Diagonal matrices commute with their conjugate transpose (both are diagonal,
and diagonal matrices commute).  Auxiliary for the "`N = 0 ⟹ A` normal"
direction.  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 (normal ⟺ `N = 0`). -/
lemma diagonal_conj_comm (d : Fin n → ℂ) :
    (Matrix.diagonal d)ᴴ * Matrix.diagonal d
      = Matrix.diagonal d * (Matrix.diagonal d)ᴴ := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-- **`N = 0 ⟹ A` is normal (unconditional easy direction).**  If the strict-upper
Schur factor vanishes then `T = D` is diagonal, `A = U D Uᴴ`, and `Aᴴ A = A Aᴴ`
because diagonal matrices commute with their conjugate transpose and unitary
conjugation preserves the commutation.  Hence `IsStarNormal A`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345 ("for normal matrices ... `N`",
the reverse implication `N = 0 ⟹ A normal`). -/
theorem isStarNormal_of_strictUpper_eq_zero
    (A U T D N : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq : Uᴴ * A * U = T)
    (hD : D = Matrix.diagonal (fun i => T i i))
    (_hN : ∀ i j, N i j = if j > i then T i j else 0)
    (hTeq : T = D + N)
    (hN0 : N = 0) :
    IsStarNormal A := by
  -- Unitary facts.
  have hUhU : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hUUh : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  -- `T = D` diagonal.
  have hTD : T = D := by rw [hTeq, hN0, add_zero]
  -- Recover `A = U * D * Uᴴ` from `Uᴴ A U = T = D`.
  have hAUD : A = U * D * Uᴴ := by
    have h1 : U * (Uᴴ * A * U) * Uᴴ = A := by
      calc U * (Uᴴ * A * U) * Uᴴ
          = (U * Uᴴ) * A * (U * Uᴴ) := by
            simp only [Matrix.mul_assoc]
        _ = A := by rw [hUUh, Matrix.one_mul, Matrix.mul_one]
    rw [hUeq, hTD] at h1
    exact h1.symm
  -- Aᴴ = U Dᴴ Uᴴ.
  have hAhUD : Aᴴ = U * Dᴴ * Uᴴ := by
    rw [hAUD, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  refine ⟨?_⟩
  -- Goal: Commute (star A) A, i.e. Aᴴ * A = A * Aᴴ.
  show star A * A = A * star A
  rw [Matrix.star_eq_conjTranspose]
  set d : Fin n → ℂ := fun i => T i i with hd
  -- rewrite `Aᴴ` first, then `A`, then unfold `D` to `diagonal d`.
  rw [hAhUD, hAUD, hD]
  -- LHS = U Dᴴ (Uᴴ U) D Uᴴ = U Dᴴ D Uᴴ ; RHS = U D (Uᴴ U) Dᴴ Uᴴ = U D Dᴴ Uᴴ.
  have hcomm := diagonal_conj_comm d
  -- reduce both sides to conjugations of Dᴴ D and D Dᴴ.
  have lhs :
      (U * (Matrix.diagonal d)ᴴ * Uᴴ) * (U * Matrix.diagonal d * Uᴴ)
        = U * ((Matrix.diagonal d)ᴴ * Matrix.diagonal d) * Uᴴ := by
    calc (U * (Matrix.diagonal d)ᴴ * Uᴴ) * (U * Matrix.diagonal d * Uᴴ)
        = U * (Matrix.diagonal d)ᴴ * (Uᴴ * U) * Matrix.diagonal d * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * ((Matrix.diagonal d)ᴴ * Matrix.diagonal d) * Uᴴ := by
          rw [hUhU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have rhs :
      (U * Matrix.diagonal d * Uᴴ) * (U * (Matrix.diagonal d)ᴴ * Uᴴ)
        = U * (Matrix.diagonal d * (Matrix.diagonal d)ᴴ) * Uᴴ := by
    calc (U * Matrix.diagonal d * Uᴴ) * (U * (Matrix.diagonal d)ᴴ * Uᴴ)
        = U * Matrix.diagonal d * (Uᴴ * U) * (Matrix.diagonal d)ᴴ * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal d * (Matrix.diagonal d)ᴴ) * Uᴴ := by
          rw [hUhU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [lhs, rhs, hcomm]

/-- **Consequence: for normal `A`, `frobSq A = Σ_i |λ_i|²`** (departure vanishes).
This is the (18.7) statement "for normal matrices both the bounds are equalities"
(Higham p. 345) at the level of the Frobenius Pythagorean identity: normality
forces `N = 0`, so `Δ_F(A) = 0` and `frobSq A` is exactly the eigenvalue-modulus
sum.  Stated with `N = 0` as the (equivalent, by the easy direction) hypothesis;
the converse `A normal ⟹ N = 0` is the documented open hypothesis below.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
theorem frobSq_normal_eq_sum_sq_eigs
    (A U T D N : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq : Uᴴ * A * U = T)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hD : D = Matrix.diagonal (fun i => T i i))
    (hN : ∀ i j, N i j = if j > i then T i j else 0)
    (hN0 : N = 0) :
    frobSq A = ∑ i, Complex.normSq (T i i) := by
  have hpyth := frobSq_schur_pythagoras A U T D N hU hUeq hTtri hD hN
  rw [hpyth, hN0]
  simp [frobSq]

/-! ### The remaining (hard) direction, exposed honestly as a hypothesis

The converse of `isStarNormal_of_strictUpper_eq_zero` — that a *normal* `A` has
`N = 0` in every Schur form — is a genuine theorem (a normal upper-triangular
matrix is diagonal).  Its proof needs an inductive column-norm argument on the
triangular factor that is not available from the Schur primitives alone.  We do
NOT prove it and we do NOT assume it in any result above; we merely record its
statement so downstream users can supply it explicitly if wanted.  The
`departureFSq`-level restatement of the full Henrici equivalence is then the
conjunction with the (unconditional) easy direction. -/

/-- **Documented open hypothesis (NOT proved, NOT used above).**  The hard
direction of Henrici's normal ⟺ `N = 0`: for a normal `A`, the strict-upper
Schur factor vanishes.  Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
def SchurNormalImpliesStrictUpperZero : Prop :=
  ∀ (A U T D N : Matrix (Fin n) (Fin n) ℂ),
    U ∈ Matrix.unitaryGroup (Fin n) ℂ → Uᴴ * A * U = T →
    (∀ i j, j < i → T i j = 0) →
    D = Matrix.diagonal (fun i => T i i) →
    (∀ i j, N i j = if j > i then T i j else 0) →
    T = D + N → IsStarNormal A → N = 0

/-- **Full Henrici normal ⟺ `N = 0`, modulo the documented hypothesis.**  The
forward implication is `hard` (the exposed hypothesis); the reverse is the
unconditional `isStarNormal_of_strictUpper_eq_zero`.  This packages exactly what
is conditional and what is not.  Reference: Higham, *ASNA* 2nd ed., §18.1,
p. 345. -/
theorem normal_iff_strictUpper_eq_zero
    (hard : SchurNormalImpliesStrictUpperZero (n := n))
    (A U T D N : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq : Uᴴ * A * U = T)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hD : D = Matrix.diagonal (fun i => T i i))
    (hN : ∀ i j, N i j = if j > i then T i j else 0)
    (hTeq : T = D + N) :
    IsStarNormal A ↔ N = 0 :=
  ⟨fun hnorm => hard A U T D N hU hUeq hTtri hD hN hTeq hnorm,
   fun hN0 => isStarNormal_of_strictUpper_eq_zero A U T D N hU hUeq hD hN hTeq hN0⟩

end NumStability
