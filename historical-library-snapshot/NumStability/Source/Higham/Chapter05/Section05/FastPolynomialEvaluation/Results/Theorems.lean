-- NumStability/Source/Higham/Chapter05/Section05/FastPolynomialEvaluation/Results/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Algorithms.Higham5FastPolynomialEvaluation`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Analysis.Polynomial.Factorization
import Mathlib.Tactic
import NumStability.Algorithms.PolynomialEvaluation.DerivativeEvaluation.ErrorBounds
import NumStability.Source.Higham.Chapter05.Section05.FastPolynomialEvaluation.Basic

/-!
# Theorems

Relocated from `NumStability.Algorithms.Higham5FastPolynomialEvaluation` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Higham5FastPolynomialEvaluation (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Higham5FastPolynomialEvaluation`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open Polynomial

namespace NumStability

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
