-- NumStability/Algorithms/PolynomialEvaluation/DerivativeEvaluation/ErrorBounds.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Algorithms.Horner`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.PolynomialEvaluation.ElementaryErrorBounds
import NumStability.Algorithms.PolynomialEvaluation.MatrixNorms
import NumStability.Algorithms.PolynomialEvaluation.RootProduct
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter05.Problem01.DifferentiatedHorner.Basic
import NumStability.Source.Higham.Chapter05.Section01.Horner.Basic

/-!
# ErrorBounds

Relocated from `NumStability.Algorithms.Horner` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Horner (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Horner`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

namespace NumStability

private lemma fl_hornerDerivativeStep_backward_algebra_nil
    (x d y deltaDMul deltaDAdd thetaDTail thetaD thetaCarry : ℝ)
    (hD :
      (1 + deltaDMul) * (1 + deltaDAdd) * (1 + thetaDTail) =
        1 + thetaD)
    (hCarry :
      (1 + deltaDAdd) * (1 + thetaDTail) = 1 + thetaCarry) :
    ((x * d) * (1 + deltaDMul) + y) * (1 + deltaDAdd) *
        (1 + thetaDTail) =
      d * (1 + thetaD) * x + y * (1 + thetaCarry) := by
  rw [← hD, ← hCarry]
  ring

private lemma fl_hornerDerivativeStep_backward_algebra_cons
    (x z m d y a deltaDMul deltaDAdd deltaYMul deltaYAdd thetaDTail
      thetaYTail thetaD thetaCarry thetaValue thetaA thetaY : ℝ)
    (hD :
      (1 + deltaDMul) * (1 + deltaDAdd) * (1 + thetaDTail) =
        1 + thetaD)
    (hCarry :
      (1 + deltaDAdd) * (1 + thetaDTail) = 1 + thetaCarry)
    (hValue :
      (1 + deltaYMul) * (1 + deltaYAdd) * (1 + thetaYTail) =
        1 + thetaValue)
    (hA :
      (1 + deltaYAdd) * (1 + thetaYTail) = 1 + thetaA)
    (hY :
      (1 + thetaCarry) + m * (1 + thetaValue) =
        (m + 1) * (1 + thetaY)) :
    ((x * d) * (1 + deltaDMul) + y) * (1 + deltaDAdd) *
        (1 + thetaDTail) * (x * z) +
      m * (((x * y) * (1 + deltaYMul) + a) * (1 + deltaYAdd) *
        (1 + thetaYTail)) * z =
      d * (1 + thetaD) * (x * (x * z)) +
        (m + 1) * y * (1 + thetaY) * (x * z) +
        m * a * (1 + thetaA) * z := by
  have hycombine :
      y * (1 + thetaCarry) * (x * z) +
          m * y * (1 + thetaValue) * (x * z) =
        (m + 1) * y * (1 + thetaY) * (x * z) := by
    calc
      y * (1 + thetaCarry) * (x * z) +
          m * y * (1 + thetaValue) * (x * z) =
          ((1 + thetaCarry) + m * (1 + thetaValue)) *
            y * (x * z) := by
        ring
      _ = ((m + 1) * (1 + thetaY)) * y * (x * z) := by
        rw [hY]
      _ = (m + 1) * y * (1 + thetaY) * (x * z) := by
        ring
  rw [← hD, ← hA, ← hycombine, ← hCarry, ← hValue]
  ring

/-- Coupled coefficientwise backward-error expansion for the first-derivative
component of rounded Algorithm 5.2.

Unlike the quotient-splitting proof below, this theorem keeps the value and
derivative recurrences coupled.  The leading derivative coefficient receives a
weighted average of the two rounded paths, so every coefficient perturbation
stays within the same `gamma (2 * rest.length)` envelope. -/
theorem fl_hornerDerivativeFold_snd_backward_error_coefficients
    (fp : FPModel) (x : ℝ) :
    ∀ (rest : List ℝ) (y d : ℝ),
      gammaValid fp (2 * rest.length) →
      ∃ thetaD thetaY : ℝ, ∃ pairs : List (ℝ × ℝ),
        |thetaD| ≤ gamma fp (2 * rest.length) ∧
        |thetaY| ≤ gamma fp (2 * rest.length) ∧
        pairs.map Prod.fst = rest ∧
        (∀ p ∈ pairs, |p.2| ≤ gamma fp (2 * rest.length)) ∧
        (rest.foldl (fl_hornerDerivativeStep fp x) (y, d)).2 =
          d * (1 + thetaD) * x ^ rest.length +
            (rest.length : ℝ) * y * (1 + thetaY) *
              x ^ (rest.length - 1) +
            polyDescPairsDerivPerturbed x pairs := by
  intro rest
  induction rest with
  | nil =>
      intro y d hvalid
      refine ⟨0, 0, [], ?_, ?_, ?_, ?_, ?_⟩
      · simpa using gamma_nonneg fp hvalid
      · simpa using gamma_nonneg fp hvalid
      · simp
      · intro p hp
        simp at hp
      · simp [polyDescPairsDerivPerturbed]
  | cons a rest ih =>
      intro y d hvalid
      let yNext := fl_hornerStep fp x y a
      let dNext := fl_hornerStep fp x d y
      have htailValid : gammaValid fp (2 * rest.length) :=
        gammaValid_mono fp (by simp) hvalid
      obtain ⟨thetaDTail, thetaYTail, pairsTail,
        hthetaDTail, hthetaYTail, hpairsTail, hpairsTailBound,
        hfoldTail⟩ := ih yNext dNext htailValid
      obtain ⟨deltaDMul, hdeltaDMul, hdmul⟩ := fp.model_mul x d
      obtain ⟨deltaDAdd, hdeltaDAdd, hdadd⟩ :=
        fp.model_add (fp.fl_mul x d) y
      obtain ⟨deltaYMul, hdeltaYMul, hymul⟩ := fp.model_mul x y
      obtain ⟨deltaYAdd, hdeltaYAdd, hyadd⟩ :=
        fp.model_add (fp.fl_mul x y) a
      have hdstep :
          dNext = ((x * d) * (1 + deltaDMul) + y) *
            (1 + deltaDAdd) := by
        unfold dNext fl_hornerStep
        rw [hdadd, hdmul]
      have hystep :
          yNext = ((x * y) * (1 + deltaYMul) + a) *
            (1 + deltaYAdd) := by
        unfold yNext fl_hornerStep
        rw [hyadd, hymul]
      have hvalid1 : gammaValid fp 1 :=
        gammaValid_mono fp (by simp; omega) hvalid
      have hvalid2 : gammaValid fp 2 :=
        gammaValid_mono fp (by simp) hvalid
      have hvalid1Tail : gammaValid fp (1 + 2 * rest.length) :=
        gammaValid_mono fp (by simp; omega) hvalid
      have hvalid2Tail : gammaValid fp (2 + 2 * rest.length) := by
        have hle : 2 + 2 * rest.length ≤ 2 * (a :: rest).length := by
          simp
          omega
        exact gammaValid_mono fp hle hvalid
      have hdeltaDMul1 : |deltaDMul| ≤ gamma fp 1 :=
        le_trans hdeltaDMul (u_le_gamma fp one_pos hvalid1)
      have hdeltaDAdd1 : |deltaDAdd| ≤ gamma fp 1 :=
        le_trans hdeltaDAdd (u_le_gamma fp one_pos hvalid1)
      have hdeltaYMul1 : |deltaYMul| ≤ gamma fp 1 :=
        le_trans hdeltaYMul (u_le_gamma fp one_pos hvalid1)
      have hdeltaYAdd1 : |deltaYAdd| ≤ gamma fp 1 :=
        le_trans hdeltaYAdd (u_le_gamma fp one_pos hvalid1)
      obtain ⟨thetaDMulAdd, hthetaDMulAdd, hthetaDMulAddEq⟩ :=
        gamma_mul fp 1 1 deltaDMul deltaDAdd hdeltaDMul1
          hdeltaDAdd1 hvalid2
      obtain ⟨thetaD, hthetaD, hthetaDEq⟩ :=
        gamma_mul fp 2 (2 * rest.length) thetaDMulAdd thetaDTail
          hthetaDMulAdd hthetaDTail hvalid2Tail
      obtain ⟨thetaCarry, hthetaCarry, hthetaCarryEq⟩ :=
        gamma_mul fp 1 (2 * rest.length) deltaDAdd thetaDTail
          hdeltaDAdd1 hthetaDTail hvalid1Tail
      obtain ⟨thetaYMulAdd, hthetaYMulAdd, hthetaYMulAddEq⟩ :=
        gamma_mul fp 1 1 deltaYMul deltaYAdd hdeltaYMul1
          hdeltaYAdd1 hvalid2
      obtain ⟨thetaValue, hthetaValue, hthetaValueEq⟩ :=
        gamma_mul fp 2 (2 * rest.length) thetaYMulAdd thetaYTail
          hthetaYMulAdd hthetaYTail hvalid2Tail
      obtain ⟨thetaA, hthetaA, hthetaAEq⟩ :=
        gamma_mul fp 1 (2 * rest.length) deltaYAdd thetaYTail
          hdeltaYAdd1 hthetaYTail hvalid1Tail
      let thetaY : ℝ :=
        (thetaCarry + (rest.length : ℝ) * thetaValue) /
          ((rest.length : ℝ) + 1)
      have hthetaDFull :
          |thetaD| ≤ gamma fp (2 * (a :: rest).length) :=
        le_trans hthetaD (gamma_mono fp (by simp; omega) hvalid)
      have hthetaCarryFull :
          |thetaCarry| ≤ gamma fp (2 * (a :: rest).length) :=
        le_trans hthetaCarry (gamma_mono fp (by simp; omega) hvalid)
      have hthetaValueFull :
          |thetaValue| ≤ gamma fp (2 * (a :: rest).length) :=
        le_trans hthetaValue (gamma_mono fp (by simp; omega) hvalid)
      have hthetaAFull :
          |thetaA| ≤ gamma fp (2 * (a :: rest).length) :=
        le_trans hthetaA (gamma_mono fp (by simp; omega) hvalid)
      have hgammaFull_nonneg :
          0 ≤ gamma fp (2 * (a :: rest).length) :=
        gamma_nonneg fp hvalid
      have hm_nonneg : 0 ≤ (rest.length : ℝ) := by
        exact_mod_cast rest.length.zero_le
      have hm1_pos : 0 < (rest.length : ℝ) + 1 := by
        exact_mod_cast Nat.succ_pos rest.length
      have hm1_ne : (rest.length : ℝ) + 1 ≠ 0 := ne_of_gt hm1_pos
      have hthetaYFull :
          |thetaY| ≤ gamma fp (2 * (a :: rest).length) := by
        have hnum :
            |thetaCarry + (rest.length : ℝ) * thetaValue| ≤
              ((rest.length : ℝ) + 1) *
                gamma fp (2 * (a :: rest).length) := by
          have hmul_abs :
              |(rest.length : ℝ) * thetaValue| =
                (rest.length : ℝ) * |thetaValue| := by
            rw [abs_mul, abs_of_nonneg hm_nonneg]
          calc
            |thetaCarry + (rest.length : ℝ) * thetaValue| ≤
                |thetaCarry| + |(rest.length : ℝ) * thetaValue| :=
              abs_add_le _ _
            _ = |thetaCarry| + (rest.length : ℝ) * |thetaValue| := by
              rw [hmul_abs]
            _ ≤ gamma fp (2 * (a :: rest).length) +
                (rest.length : ℝ) *
                  gamma fp (2 * (a :: rest).length) := by
              exact add_le_add hthetaCarryFull
                (mul_le_mul_of_nonneg_left hthetaValueFull hm_nonneg)
            _ = ((rest.length : ℝ) + 1) *
                gamma fp (2 * (a :: rest).length) := by
              ring
        calc
          |thetaY| =
              |thetaCarry + (rest.length : ℝ) * thetaValue| /
                ((rest.length : ℝ) + 1) := by
            simp [thetaY, abs_div, abs_of_pos hm1_pos]
          _ ≤ (((rest.length : ℝ) + 1) *
                gamma fp (2 * (a :: rest).length)) /
                ((rest.length : ℝ) + 1) :=
            div_le_div_of_nonneg_right hnum (le_of_lt hm1_pos)
          _ = gamma fp (2 * (a :: rest).length) := by
            field_simp [hm1_ne]
      refine ⟨thetaD, thetaY, (a, thetaA) :: pairsTail,
        hthetaDFull, hthetaYFull, ?_, ?_, ?_⟩
      · simp [hpairsTail]
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases hp
          exact hthetaAFull
        · exact le_trans (hpairsTailBound p hp)
            (gamma_mono fp (by simp) hvalid)
      · have hpairsLen : pairsTail.length = rest.length := by
          have hlen := congrArg List.length hpairsTail
          simpa using hlen
        have hthetaDProd :
            (1 + deltaDMul) * (1 + deltaDAdd) *
                (1 + thetaDTail) =
              1 + thetaD := by
          rw [hthetaDMulAddEq, hthetaDEq]
        have hthetaCarryProd :
            (1 + deltaDAdd) * (1 + thetaDTail) =
              1 + thetaCarry :=
          hthetaCarryEq
        have hthetaValueProd :
            (1 + deltaYMul) * (1 + deltaYAdd) *
                (1 + thetaYTail) =
              1 + thetaValue := by
          rw [hthetaYMulAddEq, hthetaValueEq]
        have hthetaAProd :
            (1 + deltaYAdd) * (1 + thetaYTail) =
              1 + thetaA :=
          hthetaAEq
        have hthetaYAvg :
            (1 + thetaCarry) +
                (rest.length : ℝ) * (1 + thetaValue) =
              ((rest.length : ℝ) + 1) * (1 + thetaY) := by
          dsimp [thetaY]
          field_simp [hm1_ne]
          ring
        have hstepPair :
            fl_hornerDerivativeStep fp x (y, d) a = (yNext, dNext) := by
          simp [fl_hornerDerivativeStep, yNext, dNext]
        simp only [List.foldl]
        rw [hstepPair, hfoldTail, hdstep, hystep]
        cases rest with
        | nil =>
            simp [polyDescPairsDerivPerturbed, hpairsLen]
            have hthetaYEq : thetaY = thetaCarry := by
              dsimp [thetaY]
              norm_num
            rw [hthetaYEq]
            simpa [mul_comm, mul_left_comm, mul_assoc, add_comm,
              add_left_comm, add_assoc] using
              fl_hornerDerivativeStep_backward_algebra_nil
                x d y deltaDMul deltaDAdd thetaDTail thetaD thetaCarry
                hthetaDProd hthetaCarryProd
        | cons b tail =>
            have halg :=
              fl_hornerDerivativeStep_backward_algebra_cons
                x (x ^ tail.length) ((b :: tail).length : ℝ) d y a
                deltaDMul deltaDAdd deltaYMul deltaYAdd thetaDTail
                thetaYTail thetaD thetaCarry thetaValue thetaA thetaY
                hthetaDProd hthetaCarryProd hthetaValueProd hthetaAProd
                hthetaYAvg
            have halgTail :=
              congrArg
                (fun t => t + polyDescPairsDerivPerturbed x pairsTail)
                halg
            have hpowRest :
                x ^ tail.length * x = x * x ^ tail.length := by
              ring
            have hpowRestSucc :
                x ^ (tail.length + 1) = x * x ^ tail.length := by
              rw [pow_succ]
              ring
            have hpowFull :
                x ^ (tail.length + (1 + 1)) =
                  x * (x * x ^ tail.length) := by
              rw [show tail.length + (1 + 1) = tail.length + 2 by omega]
              rw [pow_add]
              ring
            have hpowFullPred :
                x ^ (tail.length + (1 + 1) - 1) =
                  x * x ^ tail.length := by
              rw [show tail.length + (1 + 1) - 1 =
                  tail.length + 1 by omega]
              rw [pow_succ]
              ring
            simpa only [polyDescPairsDerivPerturbed, hpairsLen,
              List.length_cons, Nat.succ_sub_one, Nat.cast_add,
              Nat.cast_one, hpowRest, hpowRestSucc, hpowFull,
              hpowFullPred, mul_assoc, add_assoc] using halgTail

/-- Direct coupled backward-error form of Higham (5.7) for the first
derivative: the rounded derivative output is the exact derivative of a
coefficientwise-perturbed polynomial, with every coefficient perturbation
bounded by `gamma (2 * (coeffsDesc.length - 1))`. -/
theorem fl_hornerDerivativeDesc_snd_backward_error_coefficients_coupled
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    ∃ pairs : List (ℝ × ℝ),
      pairs.map Prod.fst = coeffsDesc ∧
      (∀ p ∈ pairs,
        |p.2| ≤ gamma fp (2 * (coeffsDesc.length - 1))) ∧
      (fl_hornerDerivativeDesc fp x coeffsDesc).2 =
        polyDescPairsDerivPerturbed x pairs := by
  cases coeffsDesc with
  | nil =>
      refine ⟨[], ?_, ?_, ?_⟩
      · simp
      · intro p hp
        simp at hp
      · simp [fl_hornerDerivativeDesc, polyDescPairsDerivPerturbed]
  | cons a rest =>
      have hrestValid : gammaValid fp (2 * rest.length) := by
        simpa using hvalid
      obtain ⟨thetaD, thetaY, pairsRest, _hthetaD, hthetaY,
        hpairsRest, hpairsRestBound, hfold⟩ :=
          fl_hornerDerivativeFold_snd_backward_error_coefficients
            fp x rest a 0 hrestValid
      refine ⟨(a, thetaY) :: pairsRest, ?_, ?_, ?_⟩
      · simp [hpairsRest]
      · intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · rcases hp
          simpa using hthetaY
        · simpa using hpairsRestBound p hp
      · have hpairsLen : pairsRest.length = rest.length := by
          have hlen := congrArg List.length hpairsRest
          simpa using hlen
        simpa [fl_hornerDerivativeDesc, polyDescPairsDerivPerturbed,
          hpairsLen, mul_assoc] using hfold

/-- Direct coupled forward-error form for the first derivative.  This closes
the (5.7) finite precursor without routing through the computed synthetic
quotient budget. -/
theorem fl_hornerDerivativeDesc_snd_forward_error_bound_coupled
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) *
        polyDescDerivAbs x coeffsDesc := by
  obtain ⟨pairs, hpairs, hpairsBound, hfl⟩ :=
    fl_hornerDerivativeDesc_snd_backward_error_coefficients_coupled
      fp x coeffsDesc hvalid
  have hpert :=
    abs_polyDescPairsDerivPerturbed_sub_polyDescPairsDeriv_le x
      (gamma fp (2 * (coeffsDesc.length - 1)))
      (gamma_nonneg fp hvalid) pairs hpairsBound
  have hpoly :
      polyDescPairsDeriv x pairs = polyDescDeriv x coeffsDesc := by
    rw [polyDescPairsDeriv_eq_polyDescDeriv_map_fst, hpairs]
  have habs :
      polyDescPairsDerivAbs x pairs = polyDescDerivAbs x coeffsDesc := by
    rw [polyDescPairsDerivAbs_eq_polyDescDerivAbs_map_fst, hpairs]
  simpa [hfl, hpoly, habs] using hpert

/-- Higham (5.7), direct first-order derivative error display:
`2*n*u*ptilde'(x)` plus the explicit quadratic-and-higher gamma remainder. -/
theorem fl_hornerDerivativeDesc_first_derivative_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      (((2 * (coeffsDesc.length - 1) : ℕ) : ℝ) * fp.u) *
          polyDescDerivAbs x coeffsDesc +
        fl_hornerDerivativeDescFirstOrderRemainder fp x coeffsDesc := by
  let nops : ℕ := 2 * (coeffsDesc.length - 1)
  let D : ℝ := polyDescDerivAbs x coeffsDesc
  have hbase :=
    fl_hornerDerivativeDesc_snd_forward_error_bound_coupled
      fp x coeffsDesc hvalid
  have hgamma :
      gamma fp nops =
        (nops : ℝ) * fp.u +
          (((nops : ℝ) * fp.u) ^ 2) /
            (1 - (nops : ℝ) * fp.u) := by
    simpa [nops] using gamma_eq_linear_plus_quadratic_remainder
      fp nops hvalid
  have hrewrite :
      gamma fp nops * D =
        ((nops : ℝ) * fp.u) * D +
          fl_hornerDerivativeDescFirstOrderRemainder fp x coeffsDesc := by
    unfold fl_hornerDerivativeDescFirstOrderRemainder
    dsimp [nops, D]
    rw [hgamma]
    ring
  simpa [nops, D] using le_trans hbase (le_of_eq hrewrite)

end NumStability
