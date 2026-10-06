import Mathlib.Analysis.CStarAlgebra.Matrix
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Schur
import NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.NormalCharacterization.Schur
import NumStability.Analysis.LinearOperators.Schur.Complex.Triangulation

/-!
# Analysis.LinearOperators.MatrixPowers.ExactNormBounds.NormalMatrices.Powers

R07 canonical `reusable` leaf. Declaration-level review groups 5 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.norm_pow_normal_eq`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.MatrixPowersSchur`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


open scoped Matrix.Norms.L2Operator BigOperators Matrix

namespace NumStability

noncomputable section

variable {n : ℕ}

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
