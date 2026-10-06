/-
Analysis/NumericalRadius.lean

The matrix numerical radius `r(A)` and its norm sandwich, formalizing the
auxiliary bounds of Higham, *Accuracy and Stability of Numerical Algorithms*,
2nd ed., Section 18.1 (Matrix Powers).

Higham §18.1 records, for `A ∈ ℂ^{n×n}`, the field of values / numerical range
`W(A) = { z*Az / z*z : z ≠ 0 }` and the numerical radius `r(A) = max |W(A)|`,
together with:

  * the sandwich          `‖A‖₂ / 2 ≤ r(A) ≤ ‖A‖₂`                     (§18.1)
  * the power bound        `‖A^k‖₂ ≤ 2 · r(A)^k`                        (§18.1)

which in turn factors through Berger's power inequality `r(A^k) ≤ r(A)^k`.

This file delivers, over `ℂ` (the numerical radius is degenerate over `ℝ`: for a
real matrix `W(A)` collapses to a real interval and the factor of two is
vacuous):

  * `numericalRadius A`               -- `r(A)` as `⨆ x, ‖⟪Ax, x⟫‖ / ‖x‖²`
  * `numericalRadius_nonneg`
  * `numericalRadius_le_opNorm`       -- `r(A) ≤ ‖A‖₂`   (Cauchy–Schwarz, §18.1)
  * `opNorm_le_two_mul_numericalRadius`
                                      -- `‖A‖₂ ≤ 2 · r(A)`   (§18.1, polarization)
  * `norm_pow_le_two_mul_numericalRadius_pow_of_le`
                                      -- `‖A^k‖₂ ≤ 2 · r(A)^k` GIVEN Berger's
                                         inequality `r(A^k) ≤ r(A)^k` as a
                                         hypothesis (honest conditional closure).

The matrix 2-norm `‖A‖₂` used here is Mathlib's `l2` operator norm on finite
complex matrices (`Matrix.instL2OpNormedAddCommGroup`, scope
`Matrix.Norms.L2Operator`), transported to `EuclideanSpace ℂ (Fin n)` through the
star-algebra equivalence `Matrix.toEuclideanCLM`.

SCOPE / DEFERRAL.  Berger's power inequality `r(A^k) ≤ r(A)^k` is *genuinely
absent* from Mathlib and is NOT proved here.  Its standard proof relies on the
unitary-dilation / power-inequality machinery (equivalently the positivity
characterization `Re (I - zA)⁻¹ ≥ 0` for `‖A‖ ≤ 1`), none of which is available:
Mathlib has no numerical range, numerical radius, field of values, or unitary
dilation development (a grep for `numericalRange` / `numericalRadius` /
`fieldOfValues` returns zero hits).  Consequently the unconditional §18.1 target
`‖A^k‖₂ ≤ 2 · r(A)^k` cannot be assembled here; we expose the achievable half
`‖A^k‖₂ ≤ 2 · r(A^k)` and the conditional closure that consumes Berger's
inequality as an explicit hypothesis.
-/

import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix

open scoped Matrix.Norms.L2Operator InnerProductSpace
open RCLike ComplexConjugate

namespace NumStability

noncomputable section

variable {n : ℕ}

/-- The complex Euclidean space `ℂⁿ` used as the ambient inner-product space for
the numerical range.  A local abbreviation to keep signatures short. -/
local notation "𝔼" => EuclideanSpace ℂ (Fin n)

/-!
### The numerical radius of a continuous linear operator on `ℂⁿ`

We first develop everything for a continuous linear map `T : ℂⁿ →L[ℂ] ℂⁿ` and
then transport to matrices through `Matrix.toEuclideanCLM`.
-/

/-- The **numerical radius** `r(T)` of a continuous linear operator on complex
Euclidean space, `r(T) = ⨆ x, ‖⟪T x, x⟫‖ / ‖x‖²`, i.e. `max |W(T)|` for the
field of values `W(T) = { ⟪T x, x⟫ / ‖x‖² }`.

Higham §18.1: `r(A) = max |W(A)|`, `W(A) = { z*Az / z*z : z ≠ 0 }`. -/
def numericalRadiusCLM (T : 𝔼 →L[ℂ] 𝔼) : ℝ :=
  ⨆ x : 𝔼, ‖(inner ℂ (T x) x : ℂ)‖ / ‖x‖ ^ 2

/-- The Rayleigh-type summands `‖⟪T x, x⟫‖ / ‖x‖²` are bounded above by `‖T‖`, so
the supremum defining `numericalRadiusCLM` is well behaved. -/
theorem bddAbove_numericalRadiusCLM (T : 𝔼 →L[ℂ] 𝔼) :
    BddAbove (Set.range fun x : 𝔼 => ‖(inner ℂ (T x) x : ℂ)‖ / ‖x‖ ^ 2) := by
  refine ⟨‖T‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hx : x = 0
  · simp [hx]
  · rw [div_le_iff₀ (by positivity)]
    calc ‖(inner ℂ (T x) x : ℂ)‖
          ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := by gcongr; exact T.le_opNorm x
      _ = ‖T‖ * ‖x‖ ^ 2 := by ring

/-- The numerical radius of an operator is nonnegative. -/
theorem numericalRadiusCLM_nonneg (T : 𝔼 →L[ℂ] 𝔼) : 0 ≤ numericalRadiusCLM T := by
  refine le_ciSup_of_le (bddAbove_numericalRadiusCLM T) 0 ?_
  positivity

/-- The defining pointwise inequality of the numerical radius:
`‖⟪T z, z⟫‖ ≤ r(T) · ‖z‖²` for every `z`.  This is `le_ciSup` cleared of the
denominator, and is the workhorse for the sandwich bounds below. -/
theorem norm_inner_apply_self_le (T : 𝔼 →L[ℂ] 𝔼) (z : 𝔼) :
    ‖(inner ℂ (T z) z : ℂ)‖ ≤ numericalRadiusCLM T * ‖z‖ ^ 2 := by
  by_cases hz : z = 0
  · simp [hz]
  · have hpos : (0 : ℝ) < ‖z‖ ^ 2 := by positivity
    have hle : ‖(inner ℂ (T z) z : ℂ)‖ / ‖z‖ ^ 2 ≤ numericalRadiusCLM T :=
      le_ciSup (bddAbove_numericalRadiusCLM T) z
    rwa [div_le_iff₀ hpos] at hle

/-- **Upper sandwich bound (operator form).** `r(T) ≤ ‖T‖`.

Higham §18.1: `r(A) ≤ ‖A‖₂`.  Immediate from Cauchy–Schwarz
`‖⟪T x, x⟫‖ ≤ ‖T x‖‖x‖ ≤ ‖T‖‖x‖²`. -/
theorem numericalRadiusCLM_le_opNorm (T : 𝔼 →L[ℂ] 𝔼) :
    numericalRadiusCLM T ≤ ‖T‖ := by
  refine ciSup_le fun x => ?_
  by_cases hx : x = 0
  · simp [hx, T.opNorm_nonneg]
  · rw [div_le_iff₀ (by positivity)]
    calc ‖(inner ℂ (T x) x : ℂ)‖
          ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := by gcongr; exact T.le_opNorm x
      _ = ‖T‖ * ‖x‖ ^ 2 := by ring

/-- Key polarization estimate for the lower sandwich bound: for unit vectors
`x, y`, the real part of the sesquilinear form is bounded by twice the numerical
radius, `Re ⟪T x, y⟫ ≤ 2 · r(T)`.

Proof: the complex polarization identity `inner_map_polarization'` writes
`⟪T x, y⟫` as a combination of the four diagonal values
`⟪T (x ± y), x ± y⟫`, `⟪T (x ± i y), x ± i y⟫` over `4`; bounding each real part
by its modulus, then each modulus by `r(T)‖·‖²`, and summing the norms with the
parallelogram law (`‖x±y‖² + ... = 8` on unit vectors) yields `8 r(T) / 4`. -/
theorem re_inner_le_two_mul_numericalRadiusCLM (T : 𝔼 →L[ℂ] 𝔼) {x y : 𝔼}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    re (inner ℂ (T x) y : ℂ) ≤ 2 * numericalRadiusCLM T := by
  set r := numericalRadiusCLM T with hr
  have hpol := inner_map_polarization' (T : 𝔼 →ₗ[ℂ] 𝔼) x y
  set a := (inner ℂ (T (x + y)) (x + y) : ℂ) with ha
  set b := (inner ℂ (T (x - y)) (x - y) : ℂ) with hb
  set c := (inner ℂ (T (x + Complex.I • y)) (x + Complex.I • y) : ℂ) with hc
  set d := (inner ℂ (T (x - Complex.I • y)) (x - Complex.I • y) : ℂ) with hd
  have hpol' : (inner ℂ (T x) y : ℂ) = (a - b - Complex.I * c + Complex.I * d) / 4 := by
    convert hpol using 2
  have hre : (inner ℂ (T x) y : ℂ).re
      = ((a - b - Complex.I * c + Complex.I * d).re) / 4 := by
    rw [hpol']; simp only [Complex.div_ofNat_re]
  -- the real part of the numerator is bounded by the sum of the four moduli
  have hnum : (a - b - Complex.I * c + Complex.I * d).re ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    have e1 : a.re ≤ ‖a‖ := Complex.re_le_norm a
    have e2 : (-b).re ≤ ‖b‖ := by
      have : ‖(-b : ℂ)‖ = ‖b‖ := norm_neg b
      exact this ▸ Complex.re_le_norm (-b)
    have e3 : (-(Complex.I * c)).re ≤ ‖c‖ := by
      have h1 : ‖(-(Complex.I * c) : ℂ)‖ = ‖c‖ := by
        rw [norm_neg, Complex.norm_mul, Complex.norm_I, one_mul]
      exact h1 ▸ Complex.re_le_norm (-(Complex.I * c))
    have e4 : (Complex.I * d).re ≤ ‖d‖ := by
      have h1 : ‖(Complex.I * d : ℂ)‖ = ‖d‖ := by
        rw [Complex.norm_mul, Complex.norm_I, one_mul]
      exact h1 ▸ Complex.re_le_norm (Complex.I * d)
    have hsplit : (a - b - Complex.I * c + Complex.I * d).re
        = a.re + (-b).re + (-(Complex.I * c)).re + (Complex.I * d).re := by
      simp only [Complex.add_re, Complex.sub_re, Complex.neg_re]; ring
    rw [hsplit]; linarith
  -- each modulus is ≤ r · ‖·‖²
  have hIy : ‖Complex.I • y‖ = 1 := by rw [norm_smul, Complex.norm_I, one_mul, hy]
  have ba : ‖a‖ ≤ r * ‖x + y‖ ^ 2 := norm_inner_apply_self_le T _
  have bb : ‖b‖ ≤ r * ‖x - y‖ ^ 2 := norm_inner_apply_self_le T _
  have bc : ‖c‖ ≤ r * ‖x + Complex.I • y‖ ^ 2 := norm_inner_apply_self_le T _
  have bd : ‖d‖ ≤ r * ‖x - Complex.I • y‖ ^ 2 := norm_inner_apply_self_le T _
  -- parallelogram law: the four squared norms sum to 8 on unit vectors
  have pg1 : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 4 := by
    rw [parallelogram_law_with_norm ℂ x y, hx, hy]; norm_num
  have pg2 : ‖x + Complex.I • y‖ ^ 2 + ‖x - Complex.I • y‖ ^ 2 = 4 := by
    rw [parallelogram_law_with_norm ℂ x (Complex.I • y), hx, hIy]; norm_num
  have hsum : ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ ≤ 8 * r := by
    calc ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖
          ≤ r * ‖x + y‖ ^ 2 + r * ‖x - y‖ ^ 2
              + r * ‖x + Complex.I • y‖ ^ 2 + r * ‖x - Complex.I • y‖ ^ 2 := by
            linarith [ba, bb, bc, bd]
      _ = r * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2)
            + r * (‖x + Complex.I • y‖ ^ 2 + ‖x - Complex.I • y‖ ^ 2) := by ring
      _ = 8 * r := by rw [pg1, pg2]; ring
  have hnum8 : (a - b - Complex.I * c + Complex.I * d).re ≤ 8 * r := le_trans hnum hsum
  have hgoal : re (inner ℂ (T x) y : ℂ) = (inner ℂ (T x) y : ℂ).re := rfl
  rw [hgoal, hre]; linarith

/-- **Lower sandwich bound (operator form).** `‖T‖ ≤ 2 · r(T)`.

Higham §18.1: `‖A‖₂ / 2 ≤ r(A)`, i.e. `‖A‖₂ ≤ 2 r(A)`.  Follows from
`re_inner_le_two_mul_numericalRadiusCLM` via
`ContinuousLinearMap.opNorm_le_of_re_inner_le`. -/
theorem opNorm_le_two_mul_numericalRadiusCLM (T : 𝔼 →L[ℂ] 𝔼) :
    ‖T‖ ≤ 2 * numericalRadiusCLM T := by
  refine ContinuousLinearMap.opNorm_le_of_re_inner_le
    (by have := numericalRadiusCLM_nonneg T; positivity) ?_
  intro x y hx hy
  exact re_inner_le_two_mul_numericalRadiusCLM T hx hy

/-!
### The numerical radius of a complex matrix

We transport the operator definition through `Matrix.toEuclideanCLM`, the
star-algebra equivalence `Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] (ℂⁿ →L[ℂ] ℂⁿ)`, whose
image operator has the same `l2` operator norm (`Matrix.l2_opNorm_toEuclideanCLM`)
and respects powers (`map_pow`).
-/

/-- The **numerical radius** `r(A)` of a complex `n × n` matrix, defined as the
numerical radius of the induced continuous linear operator on `ℂⁿ`.
Unfolding, `r(A) = ⨆ x, ‖⟪A x, x⟫‖ / ‖x‖²` in the Euclidean inner product.

Higham §18.1: `r(A) = max |W(A)|`, `W(A) = { z*Az / z*z : z ≠ 0 }`. -/
def numericalRadius (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  numericalRadiusCLM (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A)

/-- The numerical radius of a matrix is nonnegative. -/
theorem numericalRadius_nonneg (A : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ numericalRadius A :=
  numericalRadiusCLM_nonneg _

/-- **Upper sandwich bound.** `r(A) ≤ ‖A‖₂`.

Higham §18.1 (right half of `‖A‖₂/2 ≤ r(A) ≤ ‖A‖₂`).  Here `‖A‖₂` is Mathlib's
`l2` operator norm on finite matrices. -/
theorem numericalRadius_le_opNorm (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRadius A ≤ ‖A‖ := by
  rw [numericalRadius, ← Matrix.l2_opNorm_toEuclideanCLM A]
  exact numericalRadiusCLM_le_opNorm _

/-- **Lower sandwich bound.** `‖A‖₂ ≤ 2 · r(A)`.

Higham §18.1 (left half of `‖A‖₂/2 ≤ r(A) ≤ ‖A‖₂`).  Here `‖A‖₂` is Mathlib's
`l2` operator norm on finite matrices. -/
theorem opNorm_le_two_mul_numericalRadius (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A‖ ≤ 2 * numericalRadius A := by
  rw [numericalRadius, ← Matrix.l2_opNorm_toEuclideanCLM A]
  exact opNorm_le_two_mul_numericalRadiusCLM _

/-- **The numerical-radius sandwich**, both halves together:
`‖A‖₂ / 2 ≤ r(A) ≤ ‖A‖₂` in the equivalent form
`r(A) ≤ ‖A‖₂ ∧ ‖A‖₂ ≤ 2 · r(A)`.

Higham §18.1. -/
theorem numericalRadius_sandwich (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRadius A ≤ ‖A‖ ∧ ‖A‖ ≤ 2 * numericalRadius A :=
  ⟨numericalRadius_le_opNorm A, opNorm_le_two_mul_numericalRadius A⟩

/-!
### Matrix powers (Higham §18.1)

The achievable half of the §18.1 power bound `‖A^k‖₂ ≤ 2 · r(A)^k`, plus its
honest conditional closure.
-/

/-- **Achievable half of the §18.1 power bound.** `‖A^k‖₂ ≤ 2 · r(A^k)`.

This is just the lower sandwich bound applied to the matrix `A^k`.  Combined with
Berger's power inequality `r(A^k) ≤ r(A)^k` it would give the full §18.1 result
`‖A^k‖₂ ≤ 2 · r(A)^k`; see
`norm_pow_le_two_mul_numericalRadius_pow_of_le`, which takes that inequality as an
explicit hypothesis.  Berger's inequality itself is genuinely absent from Mathlib
(no unitary-dilation machinery) and is not proved here. -/
theorem norm_pow_le_two_mul_numericalRadius_pow_aux
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ‖A ^ k‖ ≤ 2 * numericalRadius (A ^ k) :=
  opNorm_le_two_mul_numericalRadius (A ^ k)

/-- **Conditional §18.1 power bound.** Given Berger's power inequality
`r(A^k) ≤ r(A)^k` as a hypothesis, `‖A^k‖₂ ≤ 2 · r(A)^k`.

Higham §18.1: `‖A^k‖₂ ≤ 2 · r(A)^k`.  This is the honest conditional closure of
the target.  The unconditional statement requires Berger's inequality
`numericalRadius (A^k) ≤ numericalRadius A ^ k`, which needs
unitary-dilation / power-inequality machinery that is genuinely absent from
Mathlib; hence it is exposed here as the hypothesis `hBerger` rather than proved.
The remaining step is the achievable sandwich
`‖A^k‖₂ ≤ 2 · r(A^k) ≤ 2 · r(A)^k`. -/
theorem norm_pow_le_two_mul_numericalRadius_pow_of_le
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (hBerger : numericalRadius (A ^ k) ≤ numericalRadius A ^ k) :
    ‖A ^ k‖ ≤ 2 * numericalRadius A ^ k := by
  calc ‖A ^ k‖ ≤ 2 * numericalRadius (A ^ k) :=
        norm_pow_le_two_mul_numericalRadius_pow_aux A k
    _ ≤ 2 * numericalRadius A ^ k := by gcongr

end

end NumStability
