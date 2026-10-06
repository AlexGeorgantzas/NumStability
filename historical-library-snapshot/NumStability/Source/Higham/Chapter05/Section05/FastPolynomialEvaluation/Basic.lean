import Mathlib.Analysis.Polynomial.Factorization
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Section01.Horner.Basic

/-!
# Chapter05 Section05 FastPolynomialEvaluation Basic

Canonical destination for material split out of
`NumStability.Algorithms.Higham5FastPolynomialEvaluation` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Polynomial

namespace NumStability

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

end NumStability
