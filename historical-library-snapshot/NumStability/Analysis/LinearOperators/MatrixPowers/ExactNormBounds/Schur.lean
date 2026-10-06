import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Schur

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

/-
Analysis/MatrixPowersSchur.lean

**§18.1 power-bound consequences of the Schur decomposition** (the Jordan-free
route), formalizing Higham, *Accuracy and Stability of Numerical Algorithms*,
2nd ed., Section 18.1 (Matrix Powers, pp. 340-342).

Higham §18.1 studies the behaviour of the powers `Aᵏ` of `A ∈ ℂⁿˣⁿ`.  The
asymptotic rate of growth is governed by the spectral radius `ρ(A)`, while the
initial "hump" is governed by the norm.  Higham derives these facts through the
Jordan form (18.1a).  Here we take the **Schur route** instead, which needs only
unitary similarity and avoids the (non-unitary, ill-conditioned) Jordan
transformation.  This file delivers, over `ℂ`:

  * `pow_eq_unitary_conj` — from the Schur decomposition `Uᴴ A U = T`, the
    unitary conjugation of powers `Aᵏ = U Tᵏ Uᴴ`; with `T = D + N` this is
    `Aᵏ = U (D + N)ᵏ Uᴴ`.
  * `strictUpper_pow_eq_zero` — a strictly upper-triangular `n × n` matrix `N`
    (`N i j = 0` for `j ≤ i`) is **nilpotent**: `Nⁿ = 0`.  Hence `(D + N)ᵏ`, and
    therefore `Aᵏ`, is a *finite* sum (Higham's finite Jordan-block expansion,
    obtained here with no Jordan form).
  * `normal_upperTriangular_isDiag` — a **normal upper-triangular** matrix is
    diagonal (proved from primitives by the classical row induction comparing
    the diagonals of `T Tᴴ` and `Tᴴ T`).  This is the Schur-form input to the
    normal-matrix identity and is NOT available in Mathlib.
  * `normal_schur_strictUpper_eq_zero` — for normal `A`, the Schur factor `N` in
    `schur_triangulation_diag_add_strictUpper` vanishes, so `A = U D Uᴴ`.
  * `norm_pow_normal_eq` — the **normal-matrix identity** of Higham p. 342:
    for normal `A`, `‖Aᵏ‖₂ = ρ(A)ᵏ = (maxᵢ |λᵢ|)ᵏ`, where `‖·‖₂` is Mathlib's
    `l2` operator norm and the eigenvalues `λᵢ` are the diagonal of the Schur
    factor.  Higham (p. 342): "if `A` is normal … we have
    `‖Aᵏ‖₂ = ‖diag(λᵢᵏ)‖₂ = ‖A‖ᵏ₂ = ρ(A)ᵏ`."

The matrix 2-norm `‖A‖₂` is Mathlib's `l2` operator norm on finite complex
matrices (`Matrix.instL2OpNormedAddCommGroup`, scope `Matrix.Norms.L2Operator`),
the same op-norm `NumericalRadius.lean` transports through `toEuclideanCLM`.  Two
Mathlib facts about it are used: `Matrix.l2_opNorm_diagonal`
(`‖diagonal v‖₂ = ‖v‖∞`, the max modulus) and submultiplicativity
`Matrix.l2_opNorm_mul`; from the latter plus the C*-identity
`Matrix.l2_opNorm_conjTranspose_mul_self` we prove here that unitary conjugation
is an `l2`-op-norm isometry (`l2_opNorm_unitary_conj`).  We prove this norm
isometry directly rather than invoking the abstract C*-algebra unitary lemmas
(`CStarRing.norm_mem_unitary_mul` etc.): although `Matrix.unitaryGroup (Fin n) ℂ`
is definitionally `unitary (Matrix (Fin n) (Fin n) ℂ)`, the scoped `l2`-op-norm
`CStarRing` instance and the plain `StarRing` on `Matrix` form an instance diamond
that blocks those lemmas from firing on `Matrix … ℂ`.

HONEST STATEMENT STRENGTH.  Everything below is proved unconditionally from
primitives; nothing in the normal-matrix identity is assumed.  In particular
`normal_upperTriangular_isDiag` (the "normal Schur factor is diagonal" step,
which is exactly the content Higham invokes via the Jordan form) is proved here
rather than hypothesized.  The one modelling choice is that we read off the
spectral radius `ρ(A) = maxᵢ |λᵢ|` as the sup-norm `‖fun i => T i i‖` of the
diagonal of the Schur factor `T`; this equals `maxᵢ |λᵢ|` by definition of the
Pi sup-norm (`Matrix.l2_opNorm_diagonal` / `Pi.norm_def`).
-/




open scoped Matrix.Norms.L2Operator BigOperators Matrix

namespace NumStability

noncomputable section

variable {n : ℕ}

/-!
### Unitary conjugation of powers  (Higham §18.1)

From the Schur decomposition `Uᴴ A U = T` with `U` unitary we get `A = U T Uᴴ`,
hence `Aᵏ = U Tᵏ Uᴴ`.  With `T = D + N` (diagonal-plus-strictly-upper) this reads
`Aᵏ = U (D + N)ᵏ Uᴴ`.
-/

/-- If `U` is unitary and `Uᴴ A U = T`, then `A = U T Uᴴ`.  (Solve the Schur
relation for `A` using `U Uᴴ = 1`.)  Higham §18.1, Schur form `A = Q T Qᴴ`. -/
theorem eq_unitary_conj_of_schur {A U T : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : Uᴴ * A * U = T) :
    A = U * T * Uᴴ := by
  have hUUH : U * Uᴴ = 1 := by
    have := hU.2
    rwa [Matrix.star_eq_conjTranspose] at this
  have hUHU : Uᴴ * U = 1 := by
    have := hU.1
    rwa [Matrix.star_eq_conjTranspose] at this
  calc A = (U * Uᴴ) * A * (U * Uᴴ) := by rw [hUUH, Matrix.one_mul, Matrix.mul_one]
    _ = U * (Uᴴ * A * U) * Uᴴ := by
          simp only [Matrix.mul_assoc]
    _ = U * T * Uᴴ := by rw [hT]

/-- **Unitary conjugation of powers.**  If `U` is unitary and `Uᴴ A U = T`, then
`Aᵏ = U Tᵏ Uᴴ` for every `k`.  This is the Jordan-free (Schur) analogue of the
per-block power expansion Higham uses after (18.1); combined with
`schur_triangulation` it expresses every power of `A` through a *triangular*
factor.  Higham §18.1. -/
theorem pow_eq_unitary_conj {A U T : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hT : Uᴴ * A * U = T) (k : ℕ) :
    A ^ k = U * T ^ k * Uᴴ := by
  have hUHU : Uᴴ * U = 1 := by
    have := hU.1
    rwa [Matrix.star_eq_conjTranspose] at this
  have hUUH : U * Uᴴ = 1 := by
    have := hU.2
    rwa [Matrix.star_eq_conjTranspose] at this
  have hA : A = U * T * Uᴴ := eq_unitary_conj_of_schur hU hT
  induction k with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hUUH]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ, hA]
    -- (U Tᵐ Uᴴ) * (U T Uᴴ) = U Tᵐ⁺¹ Uᴴ
    calc U * T ^ m * Uᴴ * (U * T * Uᴴ)
        = U * T ^ m * (Uᴴ * U) * T * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * (T ^ m * T) * Uᴴ := by rw [hUHU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = U * T ^ (m + 1) * Uᴴ := by rw [← pow_succ]

/-!
### Nilpotency of the strictly-upper-triangular Schur factor  (Higham §18.1)

A strictly upper-triangular `n × n` matrix `N` (`N i j = 0` whenever `j ≤ i`) is
nilpotent with `Nⁿ = 0`.  This makes `(D + N)ᵏ`, and hence `Aᵏ`, a finite sum —
the finite Jordan-block expansion of Higham §18.1, obtained here without the
Jordan form.  The proof is the "band-shifting" estimate: each matrix product with
`N` shifts the first nonzero super-diagonal one step further out, so after `n`
products no entry survives inside an `n × n` matrix.
-/

/-- Band-shifting bound.  If `N i j = 0` for all `j ≤ i` (strictly upper
triangular), then `(Nᵐ) i j = 0` whenever `j < i + m`.  The nonzero band of the
`m`-th power starts at the `m`-th super-diagonal. -/
theorem strictUpper_pow_apply_eq_zero {N : Matrix (Fin n) (Fin n) ℂ}
    (hN : ∀ i j : Fin n, (j : ℕ) ≤ (i : ℕ) → N i j = 0) (m : ℕ) :
    ∀ i j : Fin n, (j : ℕ) < (i : ℕ) + m → (N ^ m) i j = 0 := by
  induction m with
  | zero =>
    intro i j hji
    simp only [Nat.add_zero] at hji
    -- `N^0 = 1`; `j < i` forces `i ≠ j`, so the identity entry is `0`.
    have hij : i ≠ j := fun h => by rw [h] at hji; exact absurd hji (lt_irrefl _)
    rw [pow_zero, Matrix.one_apply_ne hij]
  | succ p ih =>
    intro i j hji
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    -- either N^p i k = 0 (if k < i + p) or N k j = 0 (if j ≤ k)
    by_cases hk : (k : ℕ) < (i : ℕ) + p
    · rw [ih i k hk, zero_mul]
    · -- k ≥ i + p, and j < i + (p+1), so j ≤ i + p ≤ k
      have hle : (i : ℕ) + p ≤ (k : ℕ) := Nat.not_lt.mp hk
      have hjk : (j : ℕ) ≤ (k : ℕ) := by omega
      rw [hN k j hjk, mul_zero]

/-- **Nilpotency of a strictly upper-triangular matrix.**  If `N i j = 0` for all
`j ≤ i` then `Nⁿ = 0`.  Hence the Schur factor `N` of
`schur_triangulation_diag_add_strictUpper` is nilpotent, so `(D + N)ᵏ` is a
finite sum.  Higham §18.1 (the finite Jordan-block / nilpotent expansion). -/
theorem strictUpper_pow_eq_zero {N : Matrix (Fin n) (Fin n) ℂ}
    (hN : ∀ i j : Fin n, (j : ℕ) ≤ (i : ℕ) → N i j = 0) :
    N ^ n = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  refine strictUpper_pow_apply_eq_zero hN n i j ?_
  have hjn : (j : ℕ) < n := j.2
  omega

/-!
### A normal upper-triangular matrix is diagonal  (Schur input to the identity)

Higham p. 342 invokes "if `A` is normal … `J` is diagonal and `X` can be taken to
be unitary", i.e. the Schur form of a normal matrix is diagonal.  Mathlib has the
spectral theorem for Hermitian matrices but not this normal-Schur fact, so we
prove it directly: a normal (`Tᴴ T = T Tᴴ`) upper-triangular matrix is diagonal.
The proof is the classical row induction comparing the `(i,i)` diagonal entries
of `T Tᴴ` (sum of squared moduli along row `i`) and `Tᴴ T` (down column `i`).
-/






















































































/-!
### The normal-matrix identity  `‖Aᵏ‖₂ = ρ(A)ᵏ`  (Higham p. 342)

For normal `A`, the Schur factor is diagonal, so `A = U D Uᴴ` with `U` unitary and
`D = diag(λᵢ)`.  Unitary invariance of the `l2` operator norm and
`Matrix.l2_opNorm_diagonal` (`‖diag v‖₂ = ‖v‖∞ = maxᵢ |vᵢ|`) then give
`‖Aᵏ‖₂ = ‖Dᵏ‖₂ = ‖diag(λᵢᵏ)‖₂ = (maxᵢ |λᵢ|)ᵏ = ρ(A)ᵏ`.

Higham p. 342: "if `A` is normal … we have
`‖Aᵏ‖₂ = ‖diag(λᵢᵏ)‖₂ = ‖A‖ᵏ₂ = ρ(A)ᵏ`."
-/




















































































































































end

end NumStability
