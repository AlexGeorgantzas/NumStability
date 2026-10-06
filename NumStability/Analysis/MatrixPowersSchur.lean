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

import Mathlib.Analysis.CStarAlgebra.Matrix
import NumStability.Analysis.SchurTriangulation

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

/-- The `(i,i)` entry of `T Tᴴ` is the sum of squared moduli of row `i` of `T`. -/
private theorem mul_conjTranspose_diag (T : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (T * Tᴴ) i i = ∑ j, (‖T i j‖ : ℂ) ^ 2 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, RCLike.mul_conj]
  norm_cast

/-- The `(i,i)` entry of `Tᴴ T` is the sum of squared moduli of column `i` of `T`. -/
private theorem conjTranspose_mul_diag (T : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    (Tᴴ * T) i i = ∑ k, (‖T k i‖ : ℂ) ^ 2 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, RCLike.conj_mul]
  norm_cast

/-- **A normal upper-triangular matrix is diagonal.**  If `T` is upper triangular
(`T i j = 0` for `j < i`) and normal (`Tᴴ * T = T * Tᴴ`), then `T i j = 0` for
`i ≠ j`.  This is the Schur-form statement Higham uses on p. 342 for normal `A`
("`J` is diagonal"); it is proved here from primitives, not taken from Mathlib.

Proof by strong induction on the row index `i`: assuming every earlier row `i' <
i` is diagonal, column `i` of `T` has only the diagonal entry surviving, so
`(Tᴴ T)_{ii} = |T i i|²`; upper-triangularity gives `(T Tᴴ)_{ii} = ∑_{j≥i} |T i
j|²`; normality equates them, forcing every super-diagonal `T i j` (`j > i`) to
vanish. -/
theorem normal_upperTriangular_isDiag {T : Matrix (Fin n) (Fin n) ℂ}
    (hUpper : ∀ i j : Fin n, (j : ℕ) < (i : ℕ) → T i j = 0)
    (hNormal : Tᴴ * T = T * Tᴴ) :
    ∀ i j : Fin n, i ≠ j → T i j = 0 := by
  -- We prove, by strong induction on the natural number `N = (i : ℕ)`, that
  -- every row `i` is diagonal:  `T i j = 0` for `j ≠ i`.
  have key : ∀ N : ℕ, ∀ i : Fin n, (i : ℕ) = N → ∀ j : Fin n, i ≠ j → T i j = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro i hiN j hij
      -- Column `i` of `T` has only the diagonal entry:  `T k i = 0` for `k ≠ i`.
      have hcol : ∀ k : Fin n, k ≠ i → T k i = 0 := by
        intro k hk
        rcases lt_trichotomy (k : ℕ) (i : ℕ) with hki | hki | hki
        · -- k < i: earlier row, diagonal by IH; `k ≠ i`
          exact IH (k : ℕ) (hiN ▸ hki) k rfl i hk
        · exact absurd (Fin.ext hki) hk
        · -- k > i: below diagonal, upper-triangular
          exact hUpper k i hki
      -- `(Tᴴ T)_{ii} = ∑_k |T k i|² = |T i i|²`, since off-diagonal column entries vanish.
      have hTHT : (Tᴴ * T) i i = (‖T i i‖ : ℂ) ^ 2 := by
        rw [conjTranspose_mul_diag]
        rw [Finset.sum_eq_single i]
        · rintro k _ hk; rw [hcol k hk]; simp
        · intro h; exact absurd (Finset.mem_univ i) h
      -- `(T Tᴴ)_{ii} = ∑_j |T i j|²`.
      have hTTH : (T * Tᴴ) i i = ∑ j, (‖T i j‖ : ℂ) ^ 2 := mul_conjTranspose_diag T i
      -- Normality:  ∑_j |T i j|² = |T i i|².
      have hEq : ∑ j, (‖T i j‖ : ℂ) ^ 2 = (‖T i i‖ : ℂ) ^ 2 := by
        rw [← hTTH, ← hNormal, hTHT]
      -- Move to real sums:  ∑_j |T i j|² = |T i i|²  in ℝ.
      have hEqR : ∑ j, ‖T i j‖ ^ 2 = ‖T i i‖ ^ 2 := by
        have hcast : ((∑ j, ‖T i j‖ ^ 2 : ℝ) : ℂ) = ((‖T i i‖ ^ 2 : ℝ) : ℂ) := by
          push_cast
          exact hEq
        exact_mod_cast hcast
      -- Split off the diagonal term:  ∑_{j ≠ i} |T i j|² = 0.
      have hzero : ∑ j ∈ Finset.univ.erase i, ‖T i j‖ ^ 2 = 0 := by
        have hsplit : ∑ j, ‖T i j‖ ^ 2
            = ‖T i i‖ ^ 2 + ∑ j ∈ Finset.univ.erase i, ‖T i j‖ ^ 2 := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]; ring
        rw [hsplit] at hEqR
        linarith
      -- Every off-diagonal term is `≥ 0`, so all vanish; in particular `T i j`.
      have hji_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨(Ne.symm hij), Finset.mem_univ j⟩
      have hterm : ‖T i j‖ ^ 2 = 0 := by
        by_contra hne
        have hpos : 0 < ‖T i j‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hne)
        have hle : ‖T i j‖ ^ 2 ≤ ∑ j' ∈ Finset.univ.erase i, ‖T i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖T i j'‖ ^ 2)
            (fun _ _ => by positivity) hji_mem
        rw [hzero] at hle
        linarith
      have : ‖T i j‖ = 0 := by nlinarith [norm_nonneg (T i j)]
      exact norm_eq_zero.mp this
  intro i j hij
  exact key (i : ℕ) i rfl j hij

/-!
### The normal-matrix identity  `‖Aᵏ‖₂ = ρ(A)ᵏ`  (Higham p. 342)

For normal `A`, the Schur factor is diagonal, so `A = U D Uᴴ` with `U` unitary and
`D = diag(λᵢ)`.  Unitary invariance of the `l2` operator norm and
`Matrix.l2_opNorm_diagonal` (`‖diag v‖₂ = ‖v‖∞ = maxᵢ |vᵢ|`) then give
`‖Aᵏ‖₂ = ‖Dᵏ‖₂ = ‖diag(λᵢᵏ)‖₂ = (maxᵢ |λᵢ|)ᵏ = ρ(A)ᵏ`.

Higham p. 342: "if `A` is normal … we have
`‖Aᵏ‖₂ = ‖diag(λᵢᵏ)‖₂ = ‖A‖ᵏ₂ = ρ(A)ᵏ`."
-/

/-- The sup-norm of a vector commutes with pointwise powers on a nonempty index
type: `‖vᵏ‖ = ‖v‖ᵏ` for `v : Fin n → ℂ` with `n ≥ 1`.  This is the vector-level
statement `maxᵢ |vᵢ|ᵏ = (maxᵢ |vᵢ|)ᵏ` (the map `x ↦ xᵏ` is monotone on `ℝ≥0`, so
it commutes with the finite `⊔`), and it is what turns `‖diag(λᵢᵏ)‖` into
`ρ(A)ᵏ`. -/
private theorem pi_norm_pow [Nonempty (Fin n)] (v : Fin n → ℂ) (k : ℕ) :
    ‖(v ^ k : Fin n → ℂ)‖ = ‖v‖ ^ k := by
  rw [← coe_nnnorm, ← coe_nnnorm, ← NNReal.coe_pow]
  congr 1
  have hlhs : ‖(v ^ k : Fin n → ℂ)‖₊ = Finset.univ.sup (fun i => ‖v i‖₊ ^ k) := by
    rw [Pi.nnnorm_def]
    refine Finset.sup_congr rfl fun i _ => ?_
    simp only [Pi.pow_apply, nnnorm_pow]
  have hrhs : ‖v‖₊ ^ k = Finset.univ.sup (fun i => ‖v i‖₊ ^ k) := by
    rw [Pi.nnnorm_def]
    have hmono : Monotone (fun x : NNReal => x ^ k) := fun a b hab => pow_le_pow_left' hab k
    exact Finset.comp_sup_eq_sup_comp_of_nonempty hmono Finset.univ_nonempty
  rw [hlhs, hrhs]

/-- **The Schur factor `N` of a normal matrix vanishes.**  Applying
`normal_upperTriangular_isDiag` to the Schur factor produced by
`schur_triangulation_diag_add_strictUpper`: for normal `A` (`Aᴴ A = A Aᴴ`) the
strictly-upper part `N` is zero, so `T = D` is diagonal and `A = U D Uᴴ` with `U`
unitary.  Higham p. 342 ("if `A` is normal … `J` is diagonal and `X` can be taken
to be unitary"). -/
theorem normal_schur_strictUpper_eq_zero {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : Aᴴ * A = A * Aᴴ) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ),
      U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      D = Matrix.diagonal d ∧
      Uᴴ * A * U = D ∧
      A = U * D * Uᴴ := by
  obtain ⟨U, T, D, N, hUu, hUeq, hUtri, hDdef, hNdef, hTDN⟩ :=
    schur_triangulation_diag_add_strictUpper A
  -- `T = Uᴴ A U` is normal because unitary conjugation preserves normality.
  have hUHU : Uᴴ * U = 1 := by
    have := hUu.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hUUH : U * Uᴴ = 1 := by
    have := hUu.2; rwa [Matrix.star_eq_conjTranspose] at this
  have hTeq : T = Uᴴ * A * U := hUeq.symm
  have hTH : Tᴴ = Uᴴ * Aᴴ * U := by
    rw [hTeq]; simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc]
  -- Compute `Tᴴ T` and `T Tᴴ`, cancelling the inner `U Uᴴ`.
  have hnormalT : Tᴴ * T = T * Tᴴ := by
    rw [hTH, hTeq]
    calc Uᴴ * Aᴴ * U * (Uᴴ * A * U)
        = Uᴴ * Aᴴ * (U * Uᴴ) * A * U := by simp only [Matrix.mul_assoc]
      _ = Uᴴ * (Aᴴ * A) * U := by rw [hUUH]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = Uᴴ * (A * Aᴴ) * U := by rw [hA]
      _ = Uᴴ * A * (U * Uᴴ) * Aᴴ * U := by rw [hUUH]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = Uᴴ * A * U * (Uᴴ * Aᴴ * U) := by simp only [Matrix.mul_assoc]
  -- `T` upper-triangular + normal ⟹ diagonal, hence `N = 0`.
  have hTdiag : ∀ i j : Fin n, i ≠ j → T i j = 0 :=
    normal_upperTriangular_isDiag
      (fun i j hji => hUtri i j hji) hnormalT
  have hN0 : N = 0 := by
    ext i j
    rw [hNdef i j, Matrix.zero_apply]
    split_ifs with h
    · exact hTdiag i j (ne_of_lt h)
    · rfl
  have hTD : T = D := by rw [hTDN, hN0, add_zero]
  refine ⟨U, D, fun i => T i i, hUu, hDdef, ?_, ?_⟩
  · rw [hUeq, hTD]
  · rw [hTD] at hUeq; exact eq_unitary_conj_of_schur hUu hUeq

/-- The `l2` operator norm of the identity `n × n` matrix (`n ≥ 1`) is `1`.
(`1 = diag 1`, and the sup-norm of the all-ones vector is `1`.) -/
private theorem l2_opNorm_one [Nonempty (Fin n)] :
    ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = 1 := by
  rw [show (1 : Matrix (Fin n) (Fin n) ℂ)
        = Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
      Matrix.l2_opNorm_diagonal, Pi.norm_def, Finset.sup_const Finset.univ_nonempty]
  simp

/-- The `l2` operator norm of a unitary matrix (`n ≥ 1`) is `1`.  From the
C*-identity `‖Uᴴ U‖ = ‖U‖²` (`Matrix.l2_opNorm_conjTranspose_mul_self`) and
`Uᴴ U = 1`. -/
private theorem l2_opNorm_of_mem_unitaryGroup [Nonempty (Fin n)]
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ‖U‖ = 1 := by
  have h1 : Uᴴ * U = 1 := by
    have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hsq : ‖Uᴴ * U‖ = ‖U‖ * ‖U‖ := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [h1, l2_opNorm_one] at hsq
  nlinarith [norm_nonneg U]

/-- **Unitary conjugation is an `l2`-operator-norm isometry** (`n ≥ 1`):
`‖U M Uᴴ‖₂ = ‖M‖₂` for `U` unitary.  Proved from submultiplicativity
(`Matrix.l2_opNorm_mul`), `‖U‖ = ‖Uᴴ‖ = 1`, and the fact that inserting `Uᴴ U =
U Uᴴ = 1` cannot decrease the norm.  This is the norm invariance behind Higham's
`‖Aᵏ‖₂ = ‖diag(λᵢᵏ)‖₂` on p. 342. -/
private theorem l2_opNorm_unitary_conj [Nonempty (Fin n)]
    {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖U * M * Uᴴ‖ = ‖M‖ := by
  have hUnorm : ‖U‖ = 1 := l2_opNorm_of_mem_unitaryGroup hU
  have hUHnorm : ‖Uᴴ‖ = 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hUnorm
  have hUHU : Uᴴ * U = 1 := by
    have := hU.1; rwa [Matrix.star_eq_conjTranspose] at this
  have hUUH : U * Uᴴ = 1 := by
    have := hU.2; rwa [Matrix.star_eq_conjTranspose] at this
  -- upper bound: ‖U M Uᴴ‖ ≤ ‖M‖
  have hle : ‖U * M * Uᴴ‖ ≤ ‖M‖ := by
    calc ‖U * M * Uᴴ‖ ≤ ‖U * M‖ * ‖Uᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖U‖ * ‖M‖) * ‖Uᴴ‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖M‖ := by rw [hUnorm, hUHnorm]; ring
  -- lower bound: ‖M‖ = ‖Uᴴ (U M Uᴴ) U‖ ≤ ‖U M Uᴴ‖
  have hge : ‖M‖ ≤ ‖U * M * Uᴴ‖ := by
    have hMrw : M = Uᴴ * (U * M * Uᴴ) * U := by
      calc M = (Uᴴ * U) * M * (Uᴴ * U) := by rw [hUHU, Matrix.one_mul, Matrix.mul_one]
        _ = Uᴴ * (U * M * Uᴴ) * U := by simp only [Matrix.mul_assoc]
    calc ‖M‖ = ‖Uᴴ * (U * M * Uᴴ) * U‖ := by rw [← hMrw]
      _ ≤ ‖Uᴴ * (U * M * Uᴴ)‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Uᴴ‖ * ‖U * M * Uᴴ‖) * ‖U‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖U * M * Uᴴ‖ := by rw [hUnorm, hUHnorm]; ring
  exact le_antisymm hle hge

/-- **The normal-matrix identity** (Higham, *Accuracy and Stability*, 2nd ed.,
p. 342).  For a normal `A ∈ ℂⁿˣⁿ` (`n ≥ 1`) with eigenvalues `dᵢ` (the diagonal of
its diagonal Schur factor) and unitary Schur transform `U`,

  `‖Aᵏ‖₂ = (maxᵢ |dᵢ|)ᵏ = ρ(A)ᵏ`,

where `‖·‖₂` is the `l2` operator norm and `maxᵢ |dᵢ| = ‖d‖∞` is the spectral
radius `ρ(A)`.  Concretely this states `‖Aᵏ‖₂ = ‖d‖ᵏ` (sup-norm on `Fin n → ℂ`).

Proof (Jordan-free, via Schur): `A = U (diag d) Uᴴ`, so `Aᵏ = U (diag d)ᵏ Uᴴ =
U (diag (dᵏ)) Uᴴ`; unitary invariance of the `l2` operator norm
(`l2_opNorm_unitary_conj`) removes `U`, and `Matrix.l2_opNorm_diagonal` gives
`‖diag (dᵏ)‖₂ = ‖dᵏ‖∞ = ‖d‖ᵏ∞` (`pi_norm_pow`).  Higham p. 342:
`‖Aᵏ‖₂ = ‖diag(λᵢᵏ)‖₂ = ‖A‖ᵏ₂ = ρ(A)ᵏ`. -/
theorem norm_pow_normal_eq [Nonempty (Fin n)] {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : Aᴴ * A = A * Aᴴ) (k : ℕ) :
    ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ),
      U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      A = U * Matrix.diagonal d * Uᴴ ∧
      ‖A ^ k‖ = ‖d‖ ^ k := by
  obtain ⟨U, D, d, hUu, hDdef, hUeq, hAeq⟩ := normal_schur_strictUpper_eq_zero hA
  refine ⟨U, d, hUu, by rw [hAeq, hDdef], ?_⟩
  -- `Aᵏ = U Dᵏ Uᴴ = U (diag dᵏ) Uᴴ`
  have hpow : A ^ k = U * D ^ k * Uᴴ := pow_eq_unitary_conj hUu hUeq k
  rw [hpow, hDdef, Matrix.diagonal_pow, l2_opNorm_unitary_conj hUu,
      Matrix.l2_opNorm_diagonal]
  exact pi_norm_pow d k

end

end NumStability
