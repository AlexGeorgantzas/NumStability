-- Exact Horner-evaluation definitions from Higham Chapter 1, Section 1.17.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.FloatingPoint.Model

namespace NumStability

/-!
# Nonrandom rounding: analytic core

This file records the exact Horner-form rational function, sampling grid,
continued-fraction reference, abstract `FPModel` rounded Horner operation
trace, and concrete IEEE-double finite round-to-even Horner trace from Higham
Section 1.17. It does not prove the visual nonrandom-error pattern in
Figure 1.6.
-/

/-- Kahan's Section 1.17 numerator in the displayed Horner form. -/
noncomputable def kahanHornerNumerator (x : ℝ) : ℝ :=
  622 - x * (751 - x * (324 - x * (59 - 4 * x)))

/-- Kahan's Section 1.17 denominator in the displayed Horner form. -/
noncomputable def kahanHornerDenominator (x : ℝ) : ℝ :=
  112 - x * (151 - x * (72 - x * (14 - x)))

/-- Kahan's Section 1.17 rational function. -/
noncomputable def kahanRationalFunction (x : ℝ) : ℝ :=
  kahanHornerNumerator x / kahanHornerDenominator x

/-! ## Continued-fraction reference curve -/

/-- The innermost nonconstant denominator in the continued-fraction
representation of Kahan's rational function. -/
noncomputable def kahanContinuedFractionTail1 (x : ℝ) : ℝ :=
  (x - 2) - 2 / (x - 3)

/-- The next denominator in the continued-fraction representation of Kahan's
rational function. -/
noncomputable def kahanContinuedFractionTail2 (x : ℝ) : ℝ :=
  (x - 7) + 10 / kahanContinuedFractionTail1 x

/-- The outer denominator in the continued-fraction representation of Kahan's
rational function. -/
noncomputable def kahanContinuedFractionTail3 (x : ℝ) : ℝ :=
  (x - 2) - 1 / kahanContinuedFractionTail2 x

/-- Continued-fraction representation used as the exact reference curve for
the §1.17 Kahan example. -/
noncomputable def kahanContinuedFraction (x : ℝ) : ℝ :=
  4 - 3 / kahanContinuedFractionTail3 x

/-- Quadratic denominator produced by the Euclidean derivation of the
continued fraction. -/
noncomputable def kahanContinuedFractionP2 (x : ℝ) : ℝ :=
  x ^ 2 - 5 * x + 4

/-- Cubic denominator produced by the Euclidean derivation of the continued
fraction. -/
noncomputable def kahanContinuedFractionP1 (x : ℝ) : ℝ :=
  x ^ 3 - 12 * x ^ 2 + 49 * x - 58

/-! ## Rounded Horner operation traces -/

/-- Rounded Horner evaluation of Kahan's numerator using the displayed
operation order. -/
noncomputable def flKahanHornerNumerator (fp : FPModel) (x : ℝ) : ℝ :=
  let m0 := fp.fl_mul 4 x
  let s0 := fp.fl_sub 59 m0
  let m1 := fp.fl_mul x s0
  let s1 := fp.fl_sub 324 m1
  let m2 := fp.fl_mul x s1
  let s2 := fp.fl_sub 751 m2
  let m3 := fp.fl_mul x s2
  fp.fl_sub 622 m3

/-- Rounded Horner evaluation of Kahan's denominator using the displayed
operation order. -/
noncomputable def flKahanHornerDenominator (fp : FPModel) (x : ℝ) : ℝ :=
  let s0 := fp.fl_sub 14 x
  let m1 := fp.fl_mul x s0
  let s1 := fp.fl_sub 72 m1
  let m2 := fp.fl_mul x s1
  let s2 := fp.fl_sub 151 m2
  let m3 := fp.fl_mul x s2
  fp.fl_sub 112 m3

/-- Rounded Horner quotient path: evaluate numerator and denominator by the
displayed Horner schemes and then perform one rounded division. -/
noncomputable def flKahanRationalFunction (fp : FPModel) (x : ℝ) : ℝ :=
  fp.fl_div (flKahanHornerNumerator fp x) (flKahanHornerDenominator fp x)

/-- Symbolic local-error expansion for the rounded numerator Horner trace. -/
noncomputable def kahanHornerNumeratorErrorEval (x : ℝ) (δ : Fin 8 → ℝ) : ℝ :=
  let m0 := (4 * x) * (1 + δ 0)
  let s0 := (59 - m0) * (1 + δ 1)
  let m1 := (x * s0) * (1 + δ 2)
  let s1 := (324 - m1) * (1 + δ 3)
  let m2 := (x * s1) * (1 + δ 4)
  let s2 := (751 - m2) * (1 + δ 5)
  let m3 := (x * s2) * (1 + δ 6)
  (622 - m3) * (1 + δ 7)

/-- Symbolic local-error expansion for the rounded denominator Horner trace. -/
noncomputable def kahanHornerDenominatorErrorEval (x : ℝ) (δ : Fin 7 → ℝ) : ℝ :=
  let s0 := (14 - x) * (1 + δ 0)
  let m1 := (x * s0) * (1 + δ 1)
  let s1 := (72 - m1) * (1 + δ 2)
  let m2 := (x * s1) * (1 + δ 3)
  let s2 := (151 - m2) * (1 + δ 4)
  let m3 := (x * s2) * (1 + δ 5)
  (112 - m3) * (1 + δ 6)

/-- The rounded numerator Horner trace has one bounded local relative-error
factor for each of its eight primitive operations. -/
theorem flKahanHornerNumerator_eq_errorEval (fp : FPModel) (x : ℝ) :
    ∃ δ : Fin 8 → ℝ,
      (∀ i, |δ i| ≤ fp.u) ∧
        flKahanHornerNumerator fp x =
          kahanHornerNumeratorErrorEval x δ := by
  rcases fp.model_mul 4 x with ⟨δ0, hδ0, hm0⟩
  let m0 := fp.fl_mul 4 x
  rcases fp.model_sub 59 m0 with ⟨δ1, hδ1, hs0⟩
  let s0 := fp.fl_sub 59 m0
  rcases fp.model_mul x s0 with ⟨δ2, hδ2, hm1⟩
  let m1 := fp.fl_mul x s0
  rcases fp.model_sub 324 m1 with ⟨δ3, hδ3, hs1⟩
  let s1 := fp.fl_sub 324 m1
  rcases fp.model_mul x s1 with ⟨δ4, hδ4, hm2⟩
  let m2 := fp.fl_mul x s1
  rcases fp.model_sub 751 m2 with ⟨δ5, hδ5, hs2⟩
  let s2 := fp.fl_sub 751 m2
  rcases fp.model_mul x s2 with ⟨δ6, hδ6, hm3⟩
  let m3 := fp.fl_mul x s2
  rcases fp.model_sub 622 m3 with ⟨δ7, hδ7, hs3⟩
  refine ⟨![δ0, δ1, δ2, δ3, δ4, δ5, δ6, δ7], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3, hδ4, hδ5, hδ6, hδ7]
  · change fp.fl_sub 622 m3 =
        kahanHornerNumeratorErrorEval x ![δ0, δ1, δ2, δ3, δ4, δ5, δ6, δ7]
    rw [hs3]
    dsimp [kahanHornerNumeratorErrorEval]
    rw [show m3 = x * s2 * (1 + δ6) by simpa [m3] using hm3]
    rw [show s2 = (751 - m2) * (1 + δ5) by simpa [s2] using hs2]
    rw [show m2 = x * s1 * (1 + δ4) by simpa [m2] using hm2]
    rw [show s1 = (324 - m1) * (1 + δ3) by simpa [s1] using hs1]
    rw [show m1 = x * s0 * (1 + δ2) by simpa [m1] using hm1]
    rw [show s0 = (59 - m0) * (1 + δ1) by simpa [s0] using hs0]
    rw [show m0 = 4 * x * (1 + δ0) by simpa [m0] using hm0]

/-- The rounded denominator Horner trace has one bounded local relative-error
factor for each of its seven primitive operations. -/
theorem flKahanHornerDenominator_eq_errorEval (fp : FPModel) (x : ℝ) :
    ∃ δ : Fin 7 → ℝ,
      (∀ i, |δ i| ≤ fp.u) ∧
        flKahanHornerDenominator fp x =
          kahanHornerDenominatorErrorEval x δ := by
  rcases fp.model_sub 14 x with ⟨δ0, hδ0, hs0⟩
  let s0 := fp.fl_sub 14 x
  rcases fp.model_mul x s0 with ⟨δ1, hδ1, hm1⟩
  let m1 := fp.fl_mul x s0
  rcases fp.model_sub 72 m1 with ⟨δ2, hδ2, hs1⟩
  let s1 := fp.fl_sub 72 m1
  rcases fp.model_mul x s1 with ⟨δ3, hδ3, hm2⟩
  let m2 := fp.fl_mul x s1
  rcases fp.model_sub 151 m2 with ⟨δ4, hδ4, hs2⟩
  let s2 := fp.fl_sub 151 m2
  rcases fp.model_mul x s2 with ⟨δ5, hδ5, hm3⟩
  let m3 := fp.fl_mul x s2
  rcases fp.model_sub 112 m3 with ⟨δ6, hδ6, hs3⟩
  refine ⟨![δ0, δ1, δ2, δ3, δ4, δ5, δ6], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hδ0, hδ1, hδ2, hδ3, hδ4, hδ5, hδ6]
  · change fp.fl_sub 112 m3 =
        kahanHornerDenominatorErrorEval x ![δ0, δ1, δ2, δ3, δ4, δ5, δ6]
    rw [hs3]
    dsimp [kahanHornerDenominatorErrorEval]
    rw [show m3 = x * s2 * (1 + δ5) by simpa [m3] using hm3]
    rw [show s2 = (151 - m2) * (1 + δ4) by simpa [s2] using hs2]
    rw [show m2 = x * s1 * (1 + δ3) by simpa [m2] using hm2]
    rw [show s1 = (72 - m1) * (1 + δ2) by simpa [s1] using hs1]
    rw [show m1 = x * s0 * (1 + δ1) by simpa [m1] using hm1]
    rw [show s0 = (14 - x) * (1 + δ0) by simpa [s0] using hs0]

/-- The rounded Kahan quotient path is the numerator and denominator Horner
local-error expansions followed by one rounded division. -/
theorem flKahanRationalFunction_eq_errorEval (fp : FPModel) (x : ℝ)
    (hden : flKahanHornerDenominator fp x ≠ 0) :
    ∃ δN : Fin 8 → ℝ, ∃ δD : Fin 7 → ℝ, ∃ δq : ℝ,
      (∀ i, |δN i| ≤ fp.u) ∧
      (∀ i, |δD i| ≤ fp.u) ∧
      |δq| ≤ fp.u ∧
        flKahanRationalFunction fp x =
          (kahanHornerNumeratorErrorEval x δN /
            kahanHornerDenominatorErrorEval x δD) * (1 + δq) := by
  rcases flKahanHornerNumerator_eq_errorEval fp x with ⟨δN, hδN, hnum⟩
  rcases flKahanHornerDenominator_eq_errorEval fp x with ⟨δD, hδD, hdenEval⟩
  rcases fp.model_div (flKahanHornerNumerator fp x)
      (flKahanHornerDenominator fp x) hden with ⟨δq, hδq, hdiv⟩
  refine ⟨δN, δD, δq, hδN, hδD, hδq, ?_⟩
  simp [flKahanRationalFunction, hnum, hdenEval] at hdiv ⊢
  exact hdiv

/-! ## IEEE-double finite round-to-even Horner trace -/

noncomputable section IeeeDoubleHorner

/-- IEEE-double unit roundoff used by the concrete finite round-to-even
§1.17 Horner trace. -/
noncomputable def kahanIeeeDoubleUnitRoundoff : ℝ :=
  FloatingPointFormat.unitRoundoff FloatingPointFormat.ieeeDoubleFormat

/-- First rounded numerator Horner intermediate, `fl(4*x)`, in IEEE double. -/
noncomputable def ieeeDoubleKahanNumerator_m0 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul 4 x

/-- Second rounded numerator Horner intermediate, `fl(59 - m0)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanNumerator_s0 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 59
    (ieeeDoubleKahanNumerator_m0 x)

/-- Third rounded numerator Horner intermediate, `fl(x*s0)`, in IEEE double. -/
noncomputable def ieeeDoubleKahanNumerator_m1 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanNumerator_s0 x)

/-- Fourth rounded numerator Horner intermediate, `fl(324 - m1)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanNumerator_s1 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 324
    (ieeeDoubleKahanNumerator_m1 x)

/-- Fifth rounded numerator Horner intermediate, `fl(x*s1)`, in IEEE double. -/
noncomputable def ieeeDoubleKahanNumerator_m2 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanNumerator_s1 x)

/-- Sixth rounded numerator Horner intermediate, `fl(751 - m2)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanNumerator_s2 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 751
    (ieeeDoubleKahanNumerator_m2 x)

/-- Seventh rounded numerator Horner intermediate, `fl(x*s2)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanNumerator_m3 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanNumerator_s2 x)

/-- IEEE-double finite round-to-even numerator Horner evaluation in the
displayed operation order. -/
noncomputable def ieeeDoubleKahanHornerNumerator (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 622
    (ieeeDoubleKahanNumerator_m3 x)

/-- First rounded denominator Horner intermediate, `fl(14 - x)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_s0 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 14 x

/-- Second rounded denominator Horner intermediate, `fl(x*s0)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_m1 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanDenominator_s0 x)

/-- Third rounded denominator Horner intermediate, `fl(72 - m1)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_s1 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 72
    (ieeeDoubleKahanDenominator_m1 x)

/-- Fourth rounded denominator Horner intermediate, `fl(x*s1)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_m2 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanDenominator_s1 x)

/-- Fifth rounded denominator Horner intermediate, `fl(151 - m2)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_s2 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 151
    (ieeeDoubleKahanDenominator_m2 x)

/-- Sixth rounded denominator Horner intermediate, `fl(x*s2)`, in IEEE
double. -/
noncomputable def ieeeDoubleKahanDenominator_m3 (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.mul x
    (ieeeDoubleKahanDenominator_s2 x)

/-- IEEE-double finite round-to-even denominator Horner evaluation in the
displayed operation order. -/
noncomputable def ieeeDoubleKahanHornerDenominator (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub 112
    (ieeeDoubleKahanDenominator_m3 x)

/-- IEEE-double finite round-to-even Horner quotient path. -/
noncomputable def ieeeDoubleKahanRationalFunction (x : ℝ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.div
    (ieeeDoubleKahanHornerNumerator x) (ieeeDoubleKahanHornerDenominator x)

/-- Normal-range obligations for the IEEE-double numerator Horner trace.
The fields are deliberately the exact primitive results in the actual rounded
operation order. -/
structure IeeeDoubleKahanNumeratorNormalTrace (x : ℝ) : Prop where
  m0 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul 4 x)
  s0 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 59 (ieeeDoubleKahanNumerator_m0 x))
  m1 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s0 x))
  s1 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 324 (ieeeDoubleKahanNumerator_m1 x))
  m2 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s1 x))
  s2 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 751 (ieeeDoubleKahanNumerator_m2 x))
  m3 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanNumerator_s2 x))
  result : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 622 (ieeeDoubleKahanNumerator_m3 x))

/-- Normal-range obligations for the IEEE-double denominator Horner trace. -/
structure IeeeDoubleKahanDenominatorNormalTrace (x : ℝ) : Prop where
  s0 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 14 x)
  m1 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s0 x))
  s1 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 72 (ieeeDoubleKahanDenominator_m1 x))
  m2 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s1 x))
  s2 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 151 (ieeeDoubleKahanDenominator_m2 x))
  m3 : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.mul x (ieeeDoubleKahanDenominator_s2 x))
  result : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.sub 112 (ieeeDoubleKahanDenominator_m3 x))

/-- Normal-range obligations for the complete IEEE-double Horner quotient
trace. -/
structure IeeeDoubleKahanQuotientNormalTrace (x : ℝ) : Prop where
  numerator : IeeeDoubleKahanNumeratorNormalTrace x
  denominator : IeeeDoubleKahanDenominatorNormalTrace x
  quotient : FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
    (BasicOp.exact BasicOp.div (ieeeDoubleKahanHornerNumerator x)
      (ieeeDoubleKahanHornerDenominator x))

/-- IEEE-double numerator Horner evaluation reduces to the same local-error
expansion as the abstract `FPModel` trace, with strict IEEE-double unit-roundoff
bounds, provided the actual primitive exact results stay in the finite normal
range. -/
theorem ieeeDoubleKahanHornerNumerator_eq_errorEval_of_finiteNormal
    (x : ℝ) (h : IeeeDoubleKahanNumeratorNormalTrace x) :
    ∃ δ : Fin 8 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerNumerator x =
          kahanHornerNumeratorErrorEval x δ := by
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := 4) (y := x) h.m0 with ⟨δ0, hδ0, hm0⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 59) (y := ieeeDoubleKahanNumerator_m0 x) h.s0 with
    ⟨δ1, hδ1, hs0⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s0 x) h.m1 with
    ⟨δ2, hδ2, hm1⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 324) (y := ieeeDoubleKahanNumerator_m1 x) h.s1 with
    ⟨δ3, hδ3, hs1⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s1 x) h.m2 with
    ⟨δ4, hδ4, hm2⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 751) (y := ieeeDoubleKahanNumerator_m2 x) h.s2 with
    ⟨δ5, hδ5, hs2⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanNumerator_s2 x) h.m3 with
    ⟨δ6, hδ6, hm3⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 622) (y := ieeeDoubleKahanNumerator_m3 x) h.result with
    ⟨δ7, hδ7, hs3⟩
  refine ⟨![δ0, δ1, δ2, δ3, δ4, δ5, δ6, δ7], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [kahanIeeeDoubleUnitRoundoff, hδ0, hδ1, hδ2, hδ3,
      hδ4, hδ5, hδ6, hδ7]
  · change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
        622 (ieeeDoubleKahanNumerator_m3 x) =
        kahanHornerNumeratorErrorEval x ![δ0, δ1, δ2, δ3, δ4, δ5, δ6, δ7]
    rw [hs3]
    dsimp [kahanHornerNumeratorErrorEval]
    rw [show ieeeDoubleKahanNumerator_m3 x =
        x * ieeeDoubleKahanNumerator_s2 x * (1 + δ6) by
        simpa [ieeeDoubleKahanNumerator_m3, BasicOp.exact] using hm3]
    rw [show ieeeDoubleKahanNumerator_s2 x =
        (751 - ieeeDoubleKahanNumerator_m2 x) * (1 + δ5) by
        simpa [ieeeDoubleKahanNumerator_s2, BasicOp.exact] using hs2]
    rw [show ieeeDoubleKahanNumerator_m2 x =
        x * ieeeDoubleKahanNumerator_s1 x * (1 + δ4) by
        simpa [ieeeDoubleKahanNumerator_m2, BasicOp.exact] using hm2]
    rw [show ieeeDoubleKahanNumerator_s1 x =
        (324 - ieeeDoubleKahanNumerator_m1 x) * (1 + δ3) by
        simpa [ieeeDoubleKahanNumerator_s1, BasicOp.exact] using hs1]
    rw [show ieeeDoubleKahanNumerator_m1 x =
        x * ieeeDoubleKahanNumerator_s0 x * (1 + δ2) by
        simpa [ieeeDoubleKahanNumerator_m1, BasicOp.exact] using hm1]
    rw [show ieeeDoubleKahanNumerator_s0 x =
        (59 - ieeeDoubleKahanNumerator_m0 x) * (1 + δ1) by
        simpa [ieeeDoubleKahanNumerator_s0, BasicOp.exact] using hs0]
    rw [show ieeeDoubleKahanNumerator_m0 x =
        4 * x * (1 + δ0) by
        simpa [ieeeDoubleKahanNumerator_m0, BasicOp.exact] using hm0]
    simp [BasicOp.exact]

/-- IEEE-double denominator Horner evaluation reduces to the same local-error
expansion as the abstract trace under the corresponding finite-normal
obligations. -/
theorem ieeeDoubleKahanHornerDenominator_eq_errorEval_of_finiteNormal
    (x : ℝ) (h : IeeeDoubleKahanDenominatorNormalTrace x) :
    ∃ δ : Fin 7 → ℝ,
      (∀ i, |δ i| < kahanIeeeDoubleUnitRoundoff) ∧
        ieeeDoubleKahanHornerDenominator x =
          kahanHornerDenominatorErrorEval x δ := by
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 14) (y := x) h.s0 with ⟨δ0, hδ0, hs0⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s0 x) h.m1 with
    ⟨δ1, hδ1, hm1⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 72) (y := ieeeDoubleKahanDenominator_m1 x) h.s1 with
    ⟨δ2, hδ2, hs1⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s1 x) h.m2 with
    ⟨δ3, hδ3, hm2⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 151) (y := ieeeDoubleKahanDenominator_m2 x) h.s2 with
    ⟨δ4, hδ4, hs2⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.mul)
      (x := x) (y := ieeeDoubleKahanDenominator_s2 x) h.m3 with
    ⟨δ5, hδ5, hm3⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.sub)
      (x := 112) (y := ieeeDoubleKahanDenominator_m3 x) h.result with
    ⟨δ6, hδ6, hs3⟩
  refine ⟨![δ0, δ1, δ2, δ3, δ4, δ5, δ6], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [kahanIeeeDoubleUnitRoundoff, hδ0, hδ1, hδ2, hδ3,
      hδ4, hδ5, hδ6]
  · change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.sub
        112 (ieeeDoubleKahanDenominator_m3 x) =
        kahanHornerDenominatorErrorEval x ![δ0, δ1, δ2, δ3, δ4, δ5, δ6]
    rw [hs3]
    dsimp [kahanHornerDenominatorErrorEval]
    rw [show ieeeDoubleKahanDenominator_m3 x =
        x * ieeeDoubleKahanDenominator_s2 x * (1 + δ5) by
        simpa [ieeeDoubleKahanDenominator_m3, BasicOp.exact] using hm3]
    rw [show ieeeDoubleKahanDenominator_s2 x =
        (151 - ieeeDoubleKahanDenominator_m2 x) * (1 + δ4) by
        simpa [ieeeDoubleKahanDenominator_s2, BasicOp.exact] using hs2]
    rw [show ieeeDoubleKahanDenominator_m2 x =
        x * ieeeDoubleKahanDenominator_s1 x * (1 + δ3) by
        simpa [ieeeDoubleKahanDenominator_m2, BasicOp.exact] using hm2]
    rw [show ieeeDoubleKahanDenominator_s1 x =
        (72 - ieeeDoubleKahanDenominator_m1 x) * (1 + δ2) by
        simpa [ieeeDoubleKahanDenominator_s1, BasicOp.exact] using hs1]
    rw [show ieeeDoubleKahanDenominator_m1 x =
        x * ieeeDoubleKahanDenominator_s0 x * (1 + δ1) by
        simpa [ieeeDoubleKahanDenominator_m1, BasicOp.exact] using hm1]
    rw [show ieeeDoubleKahanDenominator_s0 x =
        (14 - x) * (1 + δ0) by
        simpa [ieeeDoubleKahanDenominator_s0, BasicOp.exact] using hs0]
    simp [BasicOp.exact]

/-- Complete IEEE-double finite round-to-even Horner quotient trace, reduced
to the numerator/denominator local-error expansions plus the final division
factor.  This is the concrete double-precision operation-order bridge; it does
not prove the Figure 1.6 rounded-value pattern. -/
theorem ieeeDoubleKahanRationalFunction_eq_errorEval_of_finiteNormal
    (x : ℝ) (h : IeeeDoubleKahanQuotientNormalTrace x) :
    ∃ δN : Fin 8 → ℝ, ∃ δD : Fin 7 → ℝ, ∃ δq : ℝ,
      (∀ i, |δN i| < kahanIeeeDoubleUnitRoundoff) ∧
      (∀ i, |δD i| < kahanIeeeDoubleUnitRoundoff) ∧
      |δq| < kahanIeeeDoubleUnitRoundoff ∧
        ieeeDoubleKahanRationalFunction x =
          (kahanHornerNumeratorErrorEval x δN /
            kahanHornerDenominatorErrorEval x δD) * (1 + δq) := by
  rcases ieeeDoubleKahanHornerNumerator_eq_errorEval_of_finiteNormal x
      h.numerator with ⟨δN, hδN, hnum⟩
  rcases ieeeDoubleKahanHornerDenominator_eq_errorEval_of_finiteNormal x
      h.denominator with ⟨δD, hδD, hden⟩
  rcases FloatingPointFormat.finiteRoundToEvenOp_standardModel_lt_of_finiteNormalRange
      (fmt := FloatingPointFormat.ieeeDoubleFormat) (op := BasicOp.div)
      (x := ieeeDoubleKahanHornerNumerator x)
      (y := ieeeDoubleKahanHornerDenominator x) h.quotient with
    ⟨δq, hδq, hquot⟩
  refine ⟨δN, δD, δq, hδN, hδD, ?_, ?_⟩
  · simpa [kahanIeeeDoubleUnitRoundoff] using hδq
  · simp [ieeeDoubleKahanRationalFunction, BasicOp.exact, hnum, hden] at hquot ⊢
    exact hquot

end IeeeDoubleHorner

end NumStability
