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
import NumStability.Analysis.MatrixPowersHenrici
import NumStability.Analysis.MatrixPowersSchur

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
