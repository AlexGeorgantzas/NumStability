import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Schur
import NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.DepartureFromNormality
import NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.NormalMatrices
import NumStability.Analysis.LinearOperators.Schur.Complex.NormalTriangular.Diagonal
import NumStability.Analysis.LinearOperators.Schur.Complex.Triangulation

/-!
# Analysis.LinearOperators.MatrixPowers.Henrici.NormalCharacterization.Schur

R07 canonical `reusable` leaf. Declaration-level review groups 3 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.normal_iff_strictUpper_eq_zero_unconditional`, `NumStability.normal_schur_strictUpper_eq_zero`, `NumStability.schurNormalImpliesStrictUpperZero_holds`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.MatrixPowersSchur`, `NumStability.Analysis.MatrixPowersHenriciNormal`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


open scoped Matrix.Norms.L2Operator BigOperators Matrix

namespace NumStability

noncomputable section

variable {n : ℕ}

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

end

end NumStability


open scoped BigOperators Matrix
open Matrix

namespace NumStability

variable {n : ℕ}

/-- **The hard direction discharged.**  `SchurNormalImpliesStrictUpperZero`
holds unconditionally: for a normal `A`, the strict-upper factor `N` of any Schur
form vanishes.  Proof: the Schur factor `T = Uᴴ A U` is normal
(`schurFactor_normal_of_normal`) and upper-triangular, hence diagonal
(`normal_upperTriangular_isDiag`), so its strict-upper part `N` is `0`.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
theorem schurNormalImpliesStrictUpperZero_holds :
    SchurNormalImpliesStrictUpperZero (n := n) := by
  intro A U T D N hU hUeq hTtri _hD hN _hTeq hnorm
  -- Normality of `A` in matrix (conjTranspose) form.
  have hAnormal : Aᴴ * A = A * Aᴴ := by
    have h := hnorm.star_comm_self.eq
    rwa [Matrix.star_eq_conjTranspose] at h
  -- The Schur factor `T` is normal.
  have hTnormal : Tᴴ * T = T * Tᴴ :=
    schurFactor_normal_of_normal A U T hU hUeq hAnormal
  -- Upper-triangularity in ℕ-index form.
  have hUpper : ∀ i j : Fin n, (j : ℕ) < (i : ℕ) → T i j = 0 := by
    intro i j h; exact hTtri i j h
  -- Normal + upper-triangular ⟹ diagonal.
  have hdiag := normal_upperTriangular_isDiag hUpper hTnormal
  -- Hence `N = 0`.
  ext i j
  rw [Matrix.zero_apply, hN i j]
  split_ifs with h
  · exact hdiag i j (ne_of_lt h)
  · rfl

/-- **Full Henrici normal ⟺ `N = 0`, UNCONDITIONAL.**  Both directions proved:
the reverse is the unconditional easy direction, the forward is the now-discharged
hard direction.  No hypothesis beyond a genuine Schur form is required.
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
theorem normal_iff_strictUpper_eq_zero_unconditional
    (A U T D N : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq : Uᴴ * A * U = T)
    (hTtri : ∀ i j, j < i → T i j = 0)
    (hD : D = Matrix.diagonal (fun i => T i i))
    (hN : ∀ i j, N i j = if j > i then T i j else 0)
    (hTeq : T = D + N) :
    IsStarNormal A ↔ N = 0 :=
  normal_iff_strictUpper_eq_zero schurNormalImpliesStrictUpperZero_holds
    A U T D N hU hUeq hTtri hD hN hTeq

end NumStability
