/-
Analysis/BergerInequality.lean

Berger's power inequality for the numerical radius, `r(A^k) ≤ r(A)^k`, from
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., Section 18.1
(Matrix Powers), p. 345.

The file `Analysis/NumericalRadius.lean` develops the matrix numerical radius
`r(A) = ⨆ x, ‖⟪A x, x⟫‖ / ‖x‖²` and the norm sandwich `‖A‖₂/2 ≤ r(A) ≤ ‖A‖₂`,
and closes the §18.1 power bound `‖A^k‖₂ ≤ 2 · r(A)^k` *conditionally* on
Berger's inequality `r(A^k) ≤ r(A)^k`
(`norm_pow_le_two_mul_numericalRadius_pow_of_le`).

Berger's inequality in full generality (Higham §18.1, p. 345) rests on the
unitary-dilation / power-inequality machinery, which is genuinely absent from
Mathlib v4.29 (no numerical range, field of values, or unitary dilation
development: a grep for `numericalRange` / `fieldOfValues` / `unitaryDilation`
returns zero hits).  This file establishes the inequality **unconditionally on
the self-adjoint (Hermitian) subclass**, which is the case in which Berger's
inequality is elementary and where it in fact holds with equality-flavoured
strength; and it packages the resulting *unconditional* §18.1 power bound for
Hermitian matrices.

The mechanism is the identity

  `r(T) = ‖T‖`   for self-adjoint `T`                         (Hermitian case)

which for the numerical radius `r(T) = ⨆ ‖⟪T x, x⟫‖/‖x‖²` follows from Mathlib's
Rayleigh-quotient norm formula `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient`
together with the reality `⟪T x, x⟫ ∈ ℝ` of the quadratic form of a symmetric
operator (`LinearMap.IsSymmetric.coe_reApplyInnerSelf_apply`).  Berger for the
Hermitian class is then

  `r(A^k) = ‖A^k‖ ≤ ‖A‖^k = r(A)^k`,

the middle step being sub-multiplicativity of the operator norm
(`norm_pow_le`), valid in any normed ring, and `A^k` being Hermitian whenever
`A` is (`IsSelfAdjoint.pow`).

Main results (all over `ℂ`, no `sorry`/`axiom`, standard axioms only):

  * `numericalRadiusCLM_eq_opNorm_of_isSelfAdjoint`
        -- `r(T) = ‖T‖` for self-adjoint operators `T` on `ℂⁿ`.
  * `numericalRadius_eq_opNorm_of_isHermitian`
        -- `r(A) = ‖A‖₂` for Hermitian matrices `A`.
  * `numericalRadius_pow_le_of_isHermitian`
        -- Berger's inequality `r(A^k) ≤ r(A)^k`, UNCONDITIONALLY, for Hermitian
           `A` (Higham §18.1, p. 345).
  * `norm_pow_le_two_mul_numericalRadius_pow_of_isHermitian`
        -- the full §18.1 power bound `‖A^k‖₂ ≤ 2 · r(A)^k`, UNCONDITIONALLY,
           for Hermitian `A`.

HONEST SCOPE.  Berger's inequality for *general* complex `A` is NOT proved here;
that requires unitary-dilation machinery absent from Mathlib.  What is
unconditional here is the Hermitian case (a genuine, standard sub-result), which
discharges the `hBerger` hypothesis of
`NumericalRadius.norm_pow_le_two_mul_numericalRadius_pow_of_le` on that subclass.
Nothing is smuggled: the Hermitian hypothesis is a real restriction, stated
explicitly, and the conclusion is the printed §18.1 bound at full strength on it.
-/

import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Matrix.Hermitian
import NumStability.Analysis.NumericalRadius

open scoped Matrix.Norms.L2Operator InnerProductSpace
open RCLike ComplexConjugate

namespace NumStability

noncomputable section

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin n)

/-!
### The Hermitian identity `r(T) = ‖T‖`

For a self-adjoint operator the quadratic form `x ↦ ⟪T x, x⟫` is real, so the
numerical radius (which measures `‖⟪T x, x⟫‖`) coincides with the supremum of the
absolute Rayleigh quotient, which Mathlib identifies with the operator norm.
-/

/-- For a **self-adjoint** operator `T` on complex Euclidean space, the numerical
radius equals the operator norm: `r(T) = ‖T‖`.

Higham §18.1, p. 345: for Hermitian `A` the field of values `W(A)` is the real
interval `[λ_min, λ_max]`, so `r(A) = ρ(A) = ‖A‖₂`.  Here the two sandwich
inequalities `r(T) ≤ ‖T‖` and `‖T‖ ≤ 2 r(T)` are sharpened to an equality using
`ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` and the reality of the
quadratic form of a symmetric operator. -/
theorem numericalRadiusCLM_eq_opNorm_of_isSelfAdjoint {T : 𝔼 →L[ℂ] 𝔼}
    (hT : IsSelfAdjoint T) : numericalRadiusCLM T = ‖T‖ := by
  have hsym : (T : 𝔼 →ₗ[ℂ] 𝔼).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1 hT
  -- The two supremum families are pointwise equal.
  have hfun : (fun x : 𝔼 => ‖(inner ℂ (T x) x : ℂ)‖ / ‖x‖ ^ 2)
      = (fun x : 𝔼 => |T.rayleighQuotient x|) := by
    funext x
    -- `⟪T x, x⟫` is real: `(re ⟪T x, x⟫ : ℂ) = ⟪T x, x⟫`.
    have hreal : ((re (inner ℂ (T x) x : ℂ) : ℝ) : ℂ) = (inner ℂ (T x) x : ℂ) :=
      hsym.coe_reApplyInnerSelf_apply x
    have hnorm : ‖(inner ℂ (T x) x : ℂ)‖ = |re (inner ℂ (T x) x : ℂ)| := by
      conv_lhs => rw [← hreal]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    -- unfold the Rayleigh quotient and split the absolute value over the quotient
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      abs_div]
    have hsq : |‖x‖ ^ 2| = ‖x‖ ^ 2 := abs_of_nonneg (by positivity)
    rw [hsq]
  rw [numericalRadiusCLM, hfun]
  exact (T.norm_eq_iSup_rayleighQuotient hsym).symm

/-- **The Hermitian numerical-radius identity** `r(A) = ‖A‖₂`.

Higham §18.1, p. 345: for a Hermitian matrix `A`, `r(A) = ρ(A) = ‖A‖₂`.  Here
`‖A‖₂` is Mathlib's `l2` operator norm on finite complex matrices. -/
theorem numericalRadius_eq_opNorm_of_isHermitian {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : Matrix.IsHermitian A) : numericalRadius A = ‖A‖ := by
  have hSA : IsSelfAdjoint A := hA.isSelfAdjoint
  have hT : IsSelfAdjoint (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) := by
    rw [IsSelfAdjoint, ← map_star, hSA.star_eq]
  rw [numericalRadius, numericalRadiusCLM_eq_opNorm_of_isSelfAdjoint hT,
    Matrix.l2_opNorm_toEuclideanCLM]

/-!
### Berger's inequality for the Hermitian class (Higham §18.1, p. 345)
-/

/-- Sub-multiplicativity of the `l2` matrix operator norm on powers:
`‖A^k‖₂ ≤ ‖A‖₂^k`.  Transported from the operator-norm sub-multiplicativity on
`ℂⁿ →L[ℂ] ℂⁿ` through the isometric star-algebra map `Matrix.toEuclideanCLM`
(`norm_pow_le'` for `k > 0`, `norm_id_le` for `k = 0`).  Valid for every complex
matrix; used with the Hermitian identity `r = ‖·‖` to prove Berger's inequality. -/
theorem l2_norm_matrix_pow_le (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ‖A ^ k‖ ≤ ‖A‖ ^ k := by
  set S := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A with hS
  have hpow : ‖A ^ k‖ = ‖S ^ k‖ := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM (A ^ k), map_pow]
  have hbase : ‖A‖ = ‖S‖ := (Matrix.l2_opNorm_toEuclideanCLM A).symm
  rw [hpow, hbase]
  cases k with
  | zero =>
      simpa using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := 𝔼))
  | succ m => exact norm_pow_le' S (Nat.succ_pos m)

/-- **Berger's power inequality, Hermitian case (unconditional).**
`r(A^k) ≤ r(A)^k` for every Hermitian matrix `A` and every `k`.

Higham §18.1, p. 345: `r(A^k) ≤ r(A)^k`.  For Hermitian `A`, `A^k` is again
Hermitian, so `r(A^k) = ‖A^k‖` and `r(A) = ‖A‖` by
`numericalRadius_eq_opNorm_of_isHermitian`; the inequality is then
`‖A^k‖ ≤ ‖A‖^k`, sub-multiplicativity of the operator norm (`norm_pow_le`).
(In fact `r(A^k) = ‖A^k‖`; only the sub-multiplicative half is needed for §18.1.)

This discharges the `hBerger` hypothesis of
`norm_pow_le_two_mul_numericalRadius_pow_of_le` on the Hermitian subclass.  The
general (non-Hermitian) case needs unitary-dilation machinery absent from
Mathlib and is not claimed here. -/
theorem numericalRadius_pow_le_of_isHermitian {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : Matrix.IsHermitian A) (k : ℕ) :
    numericalRadius (A ^ k) ≤ numericalRadius A ^ k := by
  -- `A^k` is Hermitian.
  have hAk : Matrix.IsHermitian (A ^ k) := (hA.isSelfAdjoint.pow k).isHermitian
  rw [numericalRadius_eq_opNorm_of_isHermitian hAk,
    numericalRadius_eq_opNorm_of_isHermitian hA]
  exact l2_norm_matrix_pow_le A k

/-- **The §18.1 power bound for Hermitian matrices (unconditional).**
`‖A^k‖₂ ≤ 2 · r(A)^k` for every Hermitian `A`.

Higham §18.1, p. 345: `‖A^k‖₂ ≤ 2 · r(A)^k`.  Obtained by feeding the
unconditional Hermitian Berger inequality `numericalRadius_pow_le_of_isHermitian`
into the conditional closure
`norm_pow_le_two_mul_numericalRadius_pow_of_le`.  (For Hermitian `A` one even has
`‖A^k‖₂ = r(A)^k`, so the factor `2` is not tight here; the statement is kept in
the printed §18.1 form.) -/
theorem norm_pow_le_two_mul_numericalRadius_pow_of_isHermitian
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : Matrix.IsHermitian A) (k : ℕ) :
    ‖A ^ k‖ ≤ 2 * numericalRadius A ^ k :=
  norm_pow_le_two_mul_numericalRadius_pow_of_le A k
    (numericalRadius_pow_le_of_isHermitian hA k)

end

end NumStability
