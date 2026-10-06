-- Algorithms/Higham5FastPolynomialEvaluation.lean
--
-- Source-facing closure of Higham, 2nd ed., Chapter 5's statement that
-- every polynomial of degree n > 4 has an evaluation scheme using strictly
-- fewer than 2n additions and multiplications in total.

import Mathlib.Analysis.Polynomial.Factorization
import Mathlib.Tactic
import NumStability.Algorithms.Horner

namespace NumStability

open Polynomial

/-! ## The explicit quartic scheme on page 103 -/

/-- Higham, 2nd ed., Chapter 5, Section 5.5, p. 103: the first
preprocessed coefficient in the displayed quartic evaluation scheme. -/
noncomputable def higham5QuarticAlphaZero (aFour aThree : ℝ) : ℝ :=
  (aThree / aFour - 1) / 2

/-- The auxiliary coefficient `β` in Higham's displayed quartic scheme. -/
noncomputable def higham5QuarticBeta (aFour aThree aTwo : ℝ) : ℝ :=
  aTwo / aFour -
    higham5QuarticAlphaZero aFour aThree *
      (higham5QuarticAlphaZero aFour aThree + 1)

/-- The coefficient `α₁` in Higham's displayed quartic scheme. -/
noncomputable def higham5QuarticAlphaOne
    (aFour aThree aTwo aOne : ℝ) : ℝ :=
  aOne / aFour -
    higham5QuarticAlphaZero aFour aThree *
      higham5QuarticBeta aFour aThree aTwo

/-- The coefficient `α₂` in Higham's displayed quartic scheme. -/
noncomputable def higham5QuarticAlphaTwo
    (aFour aThree aTwo aOne : ℝ) : ℝ :=
  higham5QuarticBeta aFour aThree aTwo -
    2 * higham5QuarticAlphaOne aFour aThree aTwo aOne

/-- The coefficient `α₃` in Higham's displayed quartic scheme. -/
noncomputable def higham5QuarticAlphaThree
    (aFour aThree aTwo aOne aZero : ℝ) : ℝ :=
  aZero / aFour -
    higham5QuarticAlphaOne aFour aThree aTwo aOne *
      (higham5QuarticAlphaOne aFour aThree aTwo aOne +
        higham5QuarticAlphaTwo aFour aThree aTwo aOne)

/-- The shared quadratic intermediate
`y = (x + α₀) * x + α₁` in Higham's quartic scheme. -/
noncomputable def higham5QuarticY
    (aFour aThree aTwo aOne x : ℝ) : ℝ :=
  (x + higham5QuarticAlphaZero aFour aThree) * x +
    higham5QuarticAlphaOne aFour aThree aTwo aOne

/-- The displayed fast quartic evaluator
`((y + x + α₂) * y + α₃) * α₄`, with `α₄ = a₄`. -/
noncomputable def higham5QuarticFastEval
    (aFour aThree aTwo aOne aZero x : ℝ) : ℝ :=
  let y := higham5QuarticY aFour aThree aTwo aOne x
  ((y + x + higham5QuarticAlphaTwo aFour aThree aTwo aOne) * y +
      higham5QuarticAlphaThree aFour aThree aTwo aOne aZero) * aFour

/-- Runtime additions/subtractions in the preprocessed quartic scheme. -/
def higham5QuarticAdditions : ℕ := 5

/-- Runtime multiplications in the preprocessed quartic scheme. -/
def higham5QuarticMultiplications : ℕ := 3

/-- Higham, 2nd ed., Chapter 5, Section 5.5, p. 103: the printed quartic
coefficient formulas give an evaluator identically equal to the original
quartic.  The only source side condition is the displayed `a₄ ≠ 0`. -/
theorem higham5_quartic_fast_eval_eq
    (aFour aThree aTwo aOne aZero x : ℝ) (haFour : aFour ≠ 0) :
    higham5QuarticFastEval aFour aThree aTwo aOne aZero x =
      aFour * x ^ 4 + aThree * x ^ 3 + aTwo * x ^ 2 +
        aOne * x + aZero := by
  simp only [higham5QuarticFastEval, higham5QuarticY,
    higham5QuarticAlphaThree, higham5QuarticAlphaTwo,
    higham5QuarticAlphaOne, higham5QuarticBeta,
    higham5QuarticAlphaZero]
  field_simp [haFour]
  ring

/-- The source's exact runtime comparison: after preprocessing, the quartic
scheme uses three multiplications and five additions, versus four of each for
ordinary Horner evaluation. -/
theorem higham5_quartic_runtime_counts :
    higham5QuarticMultiplications = 3 ∧
      higham5QuarticAdditions = 5 ∧
      higham5QuarticMultiplications < 4 ∧
      4 < higham5QuarticAdditions := by
  norm_num [higham5QuarticMultiplications, higham5QuarticAdditions]

/-!
The source's operation-count statement is an exact-arithmetic preprocessing
claim, not a rounding-error claim.  The preprocessing constants below may
depend on the coefficients.  At run time the evaluator shares `z = x - t`
and `s = z*z`; consequently it performs five additions/subtractions and four
multiplications.
-/

/-- Coefficient data for the nine-operation quintic kernel used in the
Knuth--Eve construction described in Higham Chapter 5. -/
structure Higham5QuinticData where
  t : ℝ
  alphaOne : ℝ
  qOne : ℝ
  qZero : ℝ
  alphaTwo : ℝ
  gammaTwo : ℝ

/-- The shared-intermediate quintic kernel.  Its straight-line evaluation is

* `z = x - t`, `s = z*z`;
* `q = qOne*z + qZero`;
* `(q*(s-alphaTwo)+gammaTwo)*(s-alphaOne)`.

Thus the kernel has exactly five additions/subtractions and four
multiplications. -/
def Higham5QuinticData.eval (d : Higham5QuinticData) (x : ℝ) : ℝ :=
  let z := x - d.t
  let s := z * z
  let q := d.qOne * z + d.qZero
  (q * (s - d.alphaTwo) + d.gammaTwo) * (s - d.alphaOne)

/-- Runtime additions/subtractions in the shared-intermediate quintic kernel. -/
def higham5QuinticAdditions : ℕ := 5

/-- Runtime multiplications in the shared-intermediate quintic kernel. -/
def higham5QuinticMultiplications : ℕ := 4

private lemma eval_monic_cubic
    {q : ℝ[X]} (hq : q.IsMonicOfDegree 3) (x : ℝ) :
    q.eval x =
      x ^ 3 + q.coeff 2 * x ^ 2 + q.coeff 1 * x + q.coeff 0 := by
  have hThree : q.coeff 3 = 1 := by
    simpa [hq.natDegree_eq] using hq.monic.coeff_natDegree
  rw [Polynomial.eval_eq_sum_range, hq.natDegree_eq]
  norm_num [Finset.sum_range_succ, hThree]
  ring

/-- Every real quintic has a preprocessed nine-operation kernel.  The leading
coefficient is absorbed into the inner linear factor, so no extra runtime
scaling multiplication is needed. -/
theorem higham5_exists_nine_operation_quintic_kernel
    (p : ℝ[X]) (hp : p.natDegree = 5) :
    ∃ d : Higham5QuinticData, ∀ x : ℝ, d.eval x = p.eval x := by
  have hp0 : p ≠ 0 := by
    intro hpz
    simp [hpz] at hp
  let a : ℝ := p.leadingCoeff
  have ha : a ≠ 0 := by
    exact leadingCoeff_ne_zero.mpr hp0
  let f : ℝ[X] := p * C a⁻¹
  have hfMonic : f.Monic := by
    simpa [f, a] using monic_mul_leadingCoeff_inv hp0
  have hfDegree : f.natDegree = 5 := by
    change (p * C a⁻¹).natDegree = 5
    rw [natDegree_mul_C]
    · exact hp
    · exact inv_ne_zero ha
  have hf : f.IsMonicOfDegree (3 + 2) := by
    exact ⟨by simpa using hfDegree, hfMonic⟩
  obtain ⟨r, q, hr, hq, hfactor⟩ :=
    hf.eq_isMonicOfDegree_two_mul_isMonicOfDegree
  obtain ⟨rOne, rZero, hrForm⟩ :=
    Polynomial.isMonicOfDegree_two_iff.mp hr
  let t : ℝ := -rOne / 2
  let alphaOne : ℝ := t ^ 2 - rZero
  let bTwo : ℝ := 3 * t + q.coeff 2
  let bOne : ℝ := 3 * t ^ 2 + 2 * q.coeff 2 * t + q.coeff 1
  let bZero : ℝ :=
    t ^ 3 + q.coeff 2 * t ^ 2 + q.coeff 1 * t + q.coeff 0
  let qOne : ℝ := a
  let qZero : ℝ := a * bTwo
  let alphaTwo : ℝ := -bOne
  let gammaTwo : ℝ := a * bZero + qZero * alphaTwo
  refine ⟨⟨t, alphaOne, qOne, qZero, alphaTwo, gammaTwo⟩, ?_⟩
  intro x
  have hpEval : p.eval x = a * f.eval x := by
    have hfEval : f.eval x = p.eval x * a⁻¹ := by
      simp [f]
    rw [hfEval]
    calc
      p.eval x = p.eval x * 1 := by ring
      _ = p.eval x * (a * a⁻¹) := by rw [mul_inv_cancel₀ ha]
      _ = a * (p.eval x * a⁻¹) := by ring
  have hrEval :
      r.eval x = (x - t) ^ 2 - alphaOne := by
    rw [hrForm]
    simp [t, alphaOne]
    ring
  have hqEval := eval_monic_cubic hq x
  rw [hfactor, eval_mul] at hpEval
  rw [hrEval, hqEval] at hpEval
  simp only [Higham5QuinticData.eval]
  rw [hpEval]
  simp [t, alphaOne, bTwo, bOne, bZero, qOne, qZero, alphaTwo,
    gammaTwo]
  ring

/-- Evaluate the remaining lower coefficients by ordinary Horner updates
after the fast quintic prefix has been evaluated. -/
def higham5FastDesc
    (d : Higham5QuinticData) (lowerCoeffsDesc : List ℝ) (x : ℝ) : ℝ :=
  lowerCoeffsDesc.foldl (hornerStep x) (d.eval x)

/-- Runtime additions/subtractions for the fast quintic prefix followed by
the ordinary Horner suffix. -/
def higham5FastDescAdditions (lowerCoeffsDesc : List ℝ) : ℕ :=
  higham5QuinticAdditions + lowerCoeffsDesc.length

/-- Runtime multiplications for the fast quintic prefix followed by the
ordinary Horner suffix. -/
def higham5FastDescMultiplications (lowerCoeffsDesc : List ℝ) : ℕ :=
  higham5QuinticMultiplications + lowerCoeffsDesc.length

/-- The total operation count is `2n - 1`, hence strictly below Horner's
`2n`, for degree `n = 5 + lowerCoeffsDesc.length`. -/
theorem higham5FastDesc_operation_count_lt_two_mul_degree
    (lowerCoeffsDesc : List ℝ) :
    higham5FastDescAdditions lowerCoeffsDesc +
        higham5FastDescMultiplications lowerCoeffsDesc <
      2 * (5 + lowerCoeffsDesc.length) := by
  simp [higham5FastDescAdditions, higham5FastDescMultiplications,
    higham5QuinticAdditions, higham5QuinticMultiplications]
  omega

private lemma foldl_horner_append
    (x y : ℝ) (left right : List ℝ) :
    (left ++ right).foldl (hornerStep x) y =
      right.foldl (hornerStep x) (left.foldl (hornerStep x) y) := by
  simp

/-- Higham Chapter 5's precise `n > 4` operation-count claim, in the source's
descending-coefficient convention.  A degree-`n` coefficient list consists
of six leading coefficients followed by `n-5` lower coefficients.  If the
leading coefficient is nonzero, preprocessing supplies a correct evaluator
using `n+5` additions/subtractions and `n+4` multiplications, for `2n-1 < 2n`
total operations. -/
theorem higham5_exists_fast_scheme_degree_gt_four
    (aFive aFour aThree aTwo aOne aZero : ℝ)
    (lowerCoeffsDesc : List ℝ) (haFive : aFive ≠ 0) :
    ∃ d : Higham5QuinticData,
      (∀ x : ℝ,
        higham5FastDesc d lowerCoeffsDesc x =
          polyDesc x
            ([aFive, aFour, aThree, aTwo, aOne, aZero] ++ lowerCoeffsDesc)) ∧
      higham5FastDescAdditions lowerCoeffsDesc +
          higham5FastDescMultiplications lowerCoeffsDesc <
        2 * (5 + lowerCoeffsDesc.length) := by
  let p : ℝ[X] :=
    C aFive * X ^ 5 + C aFour * X ^ 4 + C aThree * X ^ 3 +
      C aTwo * X ^ 2 + C aOne * X + C aZero
  have hpDegree : p.natDegree = 5 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · refine natDegree_le_iff_coeff_eq_zero.mpr ?_
      intro n hn
      simp [p, coeff_X_pow, show n ≠ 5 by omega, show n ≠ 4 by omega,
        show n ≠ 3 by omega, show n ≠ 2 by omega,
        coeff_X_of_ne_one (show n ≠ 1 by omega),
        coeff_C_ne_zero (show n ≠ 0 by omega)]
    · simp [p, haFive]
  obtain ⟨d, hd⟩ := higham5_exists_nine_operation_quintic_kernel p hpDegree
  refine ⟨d, ?_, higham5FastDesc_operation_count_lt_two_mul_degree _⟩
  intro x
  rw [higham5FastDesc, hd]
  have hpEval :
      p.eval x = polyDesc x [aFive, aFour, aThree, aTwo, aOne, aZero] := by
    simp [p, polyDesc]
    ring
  rw [hpEval]
  calc
    lowerCoeffsDesc.foldl (hornerStep x)
          (polyDesc x [aFive, aFour, aThree, aTwo, aOne, aZero]) =
        lowerCoeffsDesc.foldl (hornerStep x)
          (hornerDesc x [aFive, aFour, aThree, aTwo, aOne, aZero]) := by
          rw [hornerDesc_eq_polyDesc]
    _ = hornerDesc x
          ([aFive, aFour, aThree, aTwo, aOne, aZero] ++ lowerCoeffsDesc) := by
          simp [hornerDesc]
    _ = polyDesc x
          ([aFive, aFour, aThree, aTwo, aOne, aZero] ++ lowerCoeffsDesc) :=
      hornerDesc_eq_polyDesc _ _

end NumStability
