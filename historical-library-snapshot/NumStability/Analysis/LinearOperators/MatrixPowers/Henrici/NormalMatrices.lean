import NumStability.Analysis.LinearOperators.Schur.Complex.Triangulation

/-!
# Analysis.LinearOperators.MatrixPowers.Henrici.NormalMatrices

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

/-
Analysis/MatrixPowersHenriciNormal.lean

**Full, unconditional Henrici normal ⟺ N = 0** (Higham, *Accuracy and Stability
of Numerical Algorithms*, 2nd ed., §18.1, p. 345).

`MatrixPowersHenrici.lean` proves the easy direction (`N = 0 ⟹ A` normal)
unconditionally and exposes the hard direction (`A` normal `⟹ N = 0` in every
Schur form) as the documented hypothesis `SchurNormalImpliesStrictUpperZero`.
`MatrixPowersSchur.lean` independently proves `normal_upperTriangular_isDiag`
(a normal upper-triangular matrix is diagonal) — exactly the content the hard
direction needs.  This file combines the two: it DISCHARGES
`SchurNormalImpliesStrictUpperZero` (no longer a hypothesis) and delivers the
fully unconditional equivalence `normal_iff_strictUpper_eq_zero_unconditional`.

Reference: N. J. Higham, *ASNA* 2nd ed., §18.1, p. 345.
-/



open scoped BigOperators Matrix
open Matrix

namespace NumStability

variable {n : ℕ}

/-- **Unitary conjugation preserves normality.**  If `Aᴴ A = A Aᴴ` and `U` is
unitary with `Uᴴ A U = T`, then `Tᴴ T = T Tᴴ`.  (`Tᴴ T = Uᴴ Aᴴ A U`,
`T Tᴴ = Uᴴ A Aᴴ U` via `U Uᴴ = 1`, then normality of `A`.)
Reference: Higham, *ASNA* 2nd ed., §18.1, p. 345. -/
lemma schurFactor_normal_of_normal
    (A U T : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUeq : Uᴴ * A * U = T)
    (hAnormal : Aᴴ * A = A * Aᴴ) :
    Tᴴ * T = T * Tᴴ := by
  have hUUh : U * Uᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hTT : Tᴴ * T = Uᴴ * (Aᴴ * A) * U := by
    rw [← hUeq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ (A * U), hUUh, Matrix.one_mul]
  have hTTh : T * Tᴴ = Uᴴ * (A * Aᴴ) * U := by
    rw [← hUeq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ (Aᴴ * U), hUUh, Matrix.one_mul]
  rw [hTT, hTTh, hAnormal]












































end NumStability
