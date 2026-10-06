import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Algorithms.Summation.Compensated.Kahan.Coefficients.Coupled
import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Algorithms.Summation.Compensated.Kahan.ErrorBounds
import NumStability.Algorithms.Summation.Compensated.Kahan.Finite
import NumStability.Algorithms.Summation.Compensated.Kahan.LocalCoefficients

namespace NumStability

/-!
# Higham equation (4.8): ordinary returned-Kahan correction

This source module records the concrete finite returned-sum obstruction, the
suffix-coefficient audit, and the corrected leading-`3u` componentwise
backward bound for the ordinary returned coordinate of Algorithm 4.2.
-/

/-- First input in the four-term finite round-to-even returned-Kahan
counterexample obtained from the strict Chapter 4 follow-up. -/
noncomputable def highamCh4KahanReturnedCounterexampleX1 : Real := -22

/-- Second input in the four-term finite round-to-even returned-Kahan
counterexample.  The parameter `p` is `2^precision`; for the concrete p=5
format below this is `32`. -/
noncomputable def highamCh4KahanReturnedCounterexampleX2 (p : Real) : Real :=
  -(2 * p + 4)

/-- Third input in the four-term finite round-to-even returned-Kahan
counterexample. -/
noncomputable def highamCh4KahanReturnedCounterexampleX3 (p : Real) : Real :=
  -(8 * p - 8)

/-- Fourth input in the four-term finite round-to-even returned-Kahan
counterexample. -/
noncomputable def highamCh4KahanReturnedCounterexampleX4 : Real := 8

/-- Stored sum after the second finite Kahan step in the counterexample trace. -/
noncomputable def highamCh4KahanReturnedCounterexampleS2 (p : Real) : Real :=
  -(2 * p + 24)

/-- Rounded `y` value in the third finite Kahan step of the counterexample
trace. -/
noncomputable def highamCh4KahanReturnedCounterexampleY3 (p : Real) : Real :=
  -(8 * p)

/-- Final stored sum in the four-term finite round-to-even returned-Kahan
counterexample trace. -/
noncomputable def highamCh4KahanReturnedCounterexampleS3 (p : Real) : Real :=
  -(10 * p + 32)

/-- Coefficient functions used to test source-weight backward-error
representations for the four-term returned-Kahan counterexample. -/
abbrev HighamCh4KahanReturnedCounterexampleWeight := Fin 4 -> Real

/-- Uniform bound on a source-weight coefficient function. -/
def highamCh4KahanReturnedCounterexampleMuBound
    (b : Real) (mu : Fin 4 -> Real) : Prop :=
  forall i, |mu i| <= b

/-- Four-term input vector for the finite round-to-even returned-Kahan
counterexample. -/
noncomputable def highamCh4KahanReturnedCounterexampleInput
    (p : Real) : Fin 4 -> Real :=
  fun i =>
    if i.val = 0 then highamCh4KahanReturnedCounterexampleX1
    else if i.val = 1 then highamCh4KahanReturnedCounterexampleX2 p
    else if i.val = 2 then highamCh4KahanReturnedCounterexampleX3 p
    else highamCh4KahanReturnedCounterexampleX4

/-- Source-weight representation predicate for the four-term returned-Kahan
counterexample. -/
def highamCh4KahanReturnedCounterexampleSourceRepresentation
    (fmt : FloatingPointFormat) (p b : Real) (mu : Fin 4 -> Real) : Prop :=
  And (highamCh4KahanReturnedCounterexampleMuBound b mu)
    (finiteKahanSum fmt 4 (highamCh4KahanReturnedCounterexampleInput p) =
      Finset.univ.sum (fun i : Fin 4 =>
        highamCh4KahanReturnedCounterexampleInput p i * (1 + mu i)))

/-- Concrete p=5 binary format used by the four-term returned-Kahan
counterexample.  Its normalized values have mantissas `16 <= m < 32` and
exponents `3 <= e <= 9`, so the local spacing around the counterexample
values is exactly the one used in the GPT-5.5 Pro trace. -/
def highamCh4KahanReturnedCounterexampleP5Format : FloatingPointFormat where
  beta := 2
  t := 5
  emin := 3
  emax := 9
  beta_ge_two := by norm_num
  t_pos := by norm_num
  emin_le_emax := by norm_num

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
    (negative : Bool) (m : Nat) (e : Int)
    (hm :
      highamCh4KahanReturnedCounterexampleP5Format.normalizedMantissa m)
    (he :
      highamCh4KahanReturnedCounterexampleP5Format.exponentInRange e) :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
        negative m e) := by
  right
  left
  refine Exists.intro negative ?_
  refine Exists.intro m ?_
  refine Exists.intro e ?_
  exact And.intro hm (And.intro he rfl)

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg22 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (-22 : Real) := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
      true 22 (5 : Int)
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa])
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.exponentInRange])
  convert h using 1
  norm_num [highamCh4KahanReturnedCounterexampleP5Format,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR]

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_pos22 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (22 : Real) := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
      false 22 (5 : Int)
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa])
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.exponentInRange])
  convert h using 1
  norm_num [highamCh4KahanReturnedCounterexampleP5Format,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR]

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg68 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (-68 : Real) := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
      true 17 (7 : Int)
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa])
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.exponentInRange])
  convert h using 1
  norm_num [highamCh4KahanReturnedCounterexampleP5Format,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR]

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg4 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (-4 : Real) := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
      true 16 (3 : Int)
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa])
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.exponentInRange])
  convert h using 1
  norm_num [highamCh4KahanReturnedCounterexampleP5Format,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg]

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_zero :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (0 : Real) := by
  exact Or.inl rfl

theorem highamCh4KahanReturnedCounterexampleP5_finiteSystem_pos8 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
      (8 : Real) := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5_finiteSystem_of_normalizedValue
      false 16 (4 : Int)
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.normalizedMantissa,
          FloatingPointFormat.mantissaInRange,
          FloatingPointFormat.minNormalMantissa,
          FloatingPointFormat.maxNormalMantissa])
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.exponentInRange])
  convert h using 1
  norm_num [highamCh4KahanReturnedCounterexampleP5Format,
    FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
    FloatingPointFormat.betaR, zpow_neg]
  rfl

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
    {op : BasicOp} {x y z : Real}
    (hz : BasicOp.exact op x y = z)
    (hfin :
      highamCh4KahanReturnedCounterexampleP5Format.finiteSystem z) :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
      op x y = z := by
  have hfin' :
      highamCh4KahanReturnedCounterexampleP5Format.finiteSystem
        (BasicOp.exact op x y) := by
    simpa [hz] using hfin
  simpa [hz] using
    (highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := op) (x := x) (y := y) hfin'
      )

theorem highamCh4KahanReturnedCounterexampleP5_sameExponentTie_left_even
    {x left right : Real} {m : Nat} {e : Int}
    (hm :
      highamCh4KahanReturnedCounterexampleP5Format.normalizedMantissa m)
    (hm1 :
      highamCh4KahanReturnedCounterexampleP5Format.normalizedMantissa
        (m + 1))
    (hleft :
      left =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false m e)
    (hright :
      right =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false (m + 1) e)
    (hrange :
      highamCh4KahanReturnedCounterexampleP5Format.finiteNormalRange x)
    (hstrict : And (left < x) (x < right))
    (htie : |x - left| = |x - right|)
    (heven : FloatingPointFormat.evenMantissa m) :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven x =
      left := by
  let fmt := highamCh4KahanReturnedCounterexampleP5Format
  have hstruct : fmt.sameExponentAdjacentNormalized left right := by
    refine Exists.intro false ?_
    refine Exists.intro m ?_
    refine Exists.intro e ?_
    exact And.intro hm (And.intro hm1 (Or.inl (And.intro hleft hright)))
  have hadj : fmt.realOrderAdjacentNormalized left right :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hrange
  exact
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven

theorem highamCh4KahanReturnedCounterexampleP5_sameExponentTie_right_odd
    {x left right : Real} {m : Nat} {e : Int}
    (hm :
      highamCh4KahanReturnedCounterexampleP5Format.normalizedMantissa m)
    (hm1 :
      highamCh4KahanReturnedCounterexampleP5Format.normalizedMantissa
        (m + 1))
    (hleft :
      left =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false m e)
    (hright :
      right =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false (m + 1) e)
    (hrange :
      highamCh4KahanReturnedCounterexampleP5Format.finiteNormalRange x)
    (hstrict : And (left < x) (x < right))
    (htie : |x - left| = |x - right|)
    (hodd : ¬ FloatingPointFormat.evenMantissa m) :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven x =
      right := by
  let fmt := highamCh4KahanReturnedCounterexampleP5Format
  have hstruct : fmt.sameExponentAdjacentNormalized left right := by
    refine Exists.intro false ?_
    refine Exists.intro m ?_
    refine Exists.intro e ?_
    exact And.intro hm (And.intro hm1 (Or.inl (And.intro hleft hright)))
  have hadj : fmt.realOrderAdjacentNormalized left right :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hrange
  exact
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd

theorem highamCh4KahanReturnedCounterexampleP5_boundaryTie_right_odd
    {x left right : Real} {e : Int}
    (hleft :
      left =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false
          highamCh4KahanReturnedCounterexampleP5Format.maxNormalMantissa e)
    (hright :
      right =
        highamCh4KahanReturnedCounterexampleP5Format.normalizedValue
          false
          highamCh4KahanReturnedCounterexampleP5Format.minNormalMantissa
          (e + 1))
    (hrange :
      highamCh4KahanReturnedCounterexampleP5Format.finiteNormalRange x)
    (hstrict : And (left < x) (x < right))
    (htie : |x - left| = |x - right|)
    (hodd :
      ¬ FloatingPointFormat.evenMantissa
        highamCh4KahanReturnedCounterexampleP5Format.maxNormalMantissa) :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven x =
      right := by
  let fmt := highamCh4KahanReturnedCounterexampleP5Format
  have hm : fmt.normalizedMantissa fmt.maxNormalMantissa :=
    fmt.maxNormalMantissa_normalized
  have hboundary : fmt.boundaryAdjacentNormalized left right := by
    exact Exists.intro false
      (Exists.intro e (Or.inl (And.intro hleft hright)))
  have hadj : fmt.realOrderAdjacentNormalized left right :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hrange
  exact
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_90 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (90 : Real) = 88 := by
  apply highamCh4KahanReturnedCounterexampleP5_sameExponentTie_left_even
    (m := 22) (e := (7 : Int)) (left := 88) (right := 92)
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR]
    change (90 : Real) <= 496
    norm_num
  · norm_num
  · norm_num
  · norm_num [FloatingPointFormat.evenMantissa]

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_66 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (66 : Real) = 64 := by
  apply highamCh4KahanReturnedCounterexampleP5_sameExponentTie_left_even
    (m := 16) (e := (7 : Int)) (left := 64) (right := 68)
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR]
    change (66 : Real) <= 496
    norm_num
  · norm_num
  · norm_num
  · norm_num [FloatingPointFormat.evenMantissa]

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_252 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (252 : Real) = 256 := by
  apply highamCh4KahanReturnedCounterexampleP5_boundaryTie_right_odd
    (e := (8 : Int)) (left := 248) (right := 256)
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR, FloatingPointFormat.minNormalMantissa]
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR]
    change (252 : Real) <= 496
    norm_num
  · norm_num
  · norm_num
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.maxNormalMantissa,
      FloatingPointFormat.evenMantissa]

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_264 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (264 : Real) = 256 := by
  apply highamCh4KahanReturnedCounterexampleP5_sameExponentTie_left_even
    (m := 16) (e := (9 : Int)) (left := 256) (right := 272)
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR]
    change (264 : Real) <= 496
    norm_num
  · norm_num
  · norm_num
  · norm_num [FloatingPointFormat.evenMantissa]

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_344 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (344 : Real) = 352 := by
  apply highamCh4KahanReturnedCounterexampleP5_sameExponentTie_right_odd
    (m := 21) (e := (9 : Int)) (left := 336) (right := 352)
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.maxNormalMantissa]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.normalizedValue, FloatingPointFormat.signValue,
      FloatingPointFormat.betaR]
  · rw [FloatingPointFormat.finiteNormalRange]
    norm_num [highamCh4KahanReturnedCounterexampleP5Format,
      FloatingPointFormat.minNormalMagnitude,
      FloatingPointFormat.maxFiniteMagnitude, FloatingPointFormat.betaR]
    change (344 : Real) <= 496
    norm_num
  · norm_num
  · norm_num
  · norm_num [FloatingPointFormat.evenMantissa]

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg90 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (-90 : Real) = -88 := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven_neg
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.evenMantissa])
      (by norm_num [highamCh4KahanReturnedCounterexampleP5Format])
      (90 : Real)
  simpa [highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_90]
    using h

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg252 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (-252 : Real) = -256 := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven_neg
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.evenMantissa])
      (by norm_num [highamCh4KahanReturnedCounterexampleP5Format])
      (252 : Real)
  simpa [highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_252]
    using h

theorem highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg344 :
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
      (-344 : Real) = -352 := by
  have h :=
    highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven_neg
      (by
        norm_num [highamCh4KahanReturnedCounterexampleP5Format,
          FloatingPointFormat.evenMantissa])
      (by norm_num [highamCh4KahanReturnedCounterexampleP5Format])
      (344 : Real)
  simpa [highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_344]
    using h

/-- Exact finite round-to-even identities for the four-term returned-Kahan
counterexample trace.

This isolates the remaining concrete finite-format proof obligation from the
algorithmic obstruction: once these identities are supplied by a p=5 binary
format, the theorem below shows the returned sum cannot satisfy a first-order
`2u` source coefficient cap. -/
structure HighamCh4KahanReturnedCounterexampleRounding
    (fmt : FloatingPointFormat) (p : Real) : Prop where
  y1 :
    fmt.finiteRoundToEvenOp BasicOp.add
      highamCh4KahanReturnedCounterexampleX1 0 =
    highamCh4KahanReturnedCounterexampleX1
  s1 :
    fmt.finiteRoundToEvenOp BasicOp.add 0
      highamCh4KahanReturnedCounterexampleX1 =
    highamCh4KahanReturnedCounterexampleX1
  q1 :
    fmt.finiteRoundToEvenOp BasicOp.sub 0
      highamCh4KahanReturnedCounterexampleX1 = 22
  e1 :
    fmt.finiteRoundToEvenOp BasicOp.add 22
      highamCh4KahanReturnedCounterexampleX1 = 0
  y2 :
    fmt.finiteRoundToEvenOp BasicOp.add
      (highamCh4KahanReturnedCounterexampleX2 p) 0 =
    highamCh4KahanReturnedCounterexampleX2 p
  s2 :
    fmt.finiteRoundToEvenOp BasicOp.add
      highamCh4KahanReturnedCounterexampleX1
      (highamCh4KahanReturnedCounterexampleX2 p) =
    highamCh4KahanReturnedCounterexampleS2 p
  q2 :
    fmt.finiteRoundToEvenOp BasicOp.sub
      highamCh4KahanReturnedCounterexampleX1
      (highamCh4KahanReturnedCounterexampleS2 p) = 2 * p
  e2 :
    fmt.finiteRoundToEvenOp BasicOp.add (2 * p)
      (highamCh4KahanReturnedCounterexampleX2 p) = -4
  y3 :
    fmt.finiteRoundToEvenOp BasicOp.add
      (highamCh4KahanReturnedCounterexampleX3 p) (-4) =
    highamCh4KahanReturnedCounterexampleY3 p
  s3 :
    fmt.finiteRoundToEvenOp BasicOp.add
      (highamCh4KahanReturnedCounterexampleS2 p)
      (highamCh4KahanReturnedCounterexampleY3 p) =
    highamCh4KahanReturnedCounterexampleS3 p
  q3 :
    fmt.finiteRoundToEvenOp BasicOp.sub
      (highamCh4KahanReturnedCounterexampleS2 p)
      (highamCh4KahanReturnedCounterexampleS3 p) = 8 * p
  e3 :
    fmt.finiteRoundToEvenOp BasicOp.add (8 * p)
      (highamCh4KahanReturnedCounterexampleY3 p) = 0
  y4 :
    fmt.finiteRoundToEvenOp BasicOp.add
      highamCh4KahanReturnedCounterexampleX4 0 =
    highamCh4KahanReturnedCounterexampleX4
  s4 :
    fmt.finiteRoundToEvenOp BasicOp.add
      (highamCh4KahanReturnedCounterexampleS3 p)
      highamCh4KahanReturnedCounterexampleX4 =
    highamCh4KahanReturnedCounterexampleS3 p
  q4 :
    fmt.finiteRoundToEvenOp BasicOp.sub
      (highamCh4KahanReturnedCounterexampleS3 p)
      (highamCh4KahanReturnedCounterexampleS3 p) = 0
  e4 :
    fmt.finiteRoundToEvenOp BasicOp.add 0
      highamCh4KahanReturnedCounterexampleX4 =
    highamCh4KahanReturnedCounterexampleX4

/-- The concrete p=5 binary format satisfies all finite round-to-even trace
identities for the four-term returned-Kahan obstruction. -/
theorem highamCh4KahanReturnedCounterexampleP5_rounding :
    HighamCh4KahanReturnedCounterexampleRounding
      highamCh4KahanReturnedCounterexampleP5Format 32 := by
  refine
    { y1 := ?_, s1 := ?_, q1 := ?_, e1 := ?_,
      y2 := ?_, s2 := ?_, q2 := ?_, e2 := ?_,
      y3 := ?_, s3 := ?_, q3 := ?_, e3 := ?_,
      y4 := ?_, s4 := ?_, q4 := ?_, e4 := ?_ }
  all_goals
    norm_num [highamCh4KahanReturnedCounterexampleX1,
      highamCh4KahanReturnedCounterexampleX2,
      highamCh4KahanReturnedCounterexampleX3,
      highamCh4KahanReturnedCounterexampleX4,
      highamCh4KahanReturnedCounterexampleS2,
      highamCh4KahanReturnedCounterexampleY3,
      highamCh4KahanReturnedCounterexampleS3]
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-22 : Real) 0 = -22
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg22
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 0 (-22 : Real) = -22
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg22
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.sub 0 (-22 : Real) = 22
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact]; rfl)
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_pos22
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 22 (-22 : Real) = 0
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact]; rfl)
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_zero
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-68 : Real) 0 = -68
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg68
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-22 : Real) (-68) = -88
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.add (-22 : Real) (-68)) = -88
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg90
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.sub (-22 : Real) (-88) = 64
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.sub (-22 : Real) (-88)) = 64
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_66
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 64 (-68 : Real) = -4
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_neg4
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-248 : Real) (-4) = -256
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.add (-248 : Real) (-4)) = -256
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg252
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-88 : Real) (-256) = -352
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.add (-88 : Real) (-256)) = -352
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg344
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.sub (-88 : Real) (-352) = 256
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.sub (-88 : Real) (-352)) = 256
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_264
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 256 (-256 : Real) = 0
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact]; rfl)
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_zero
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 8 0 = (8 : Real)
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_pos8
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add (-352 : Real) 8 = -352
    change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEven
        (BasicOp.exact BasicOp.add (-352 : Real) 8) = -352
    norm_num [BasicOp.exact]
    exact
      highamCh4KahanReturnedCounterexampleP5_finiteRoundToEven_neg344
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.sub (-352 : Real) (-352) = 0
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact]; rfl)
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_zero
  · change
      highamCh4KahanReturnedCounterexampleP5Format.finiteRoundToEvenOp
        BasicOp.add 0 8 = (8 : Real)
    exact highamCh4KahanReturnedCounterexampleP5_finiteRoundToEvenOp_eq
      (by norm_num [BasicOp.exact])
      highamCh4KahanReturnedCounterexampleP5_finiteSystem_pos8

/-- The four-term returned-Kahan counterexample trace finishes with stored sum
`-(10p+32)` and retained correction `8`. -/
theorem highamCh4KahanReturnedCounterexampleState_eq_of_rounding
    (fmt : FloatingPointFormat) {p : Real}
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p) :
    finiteKahanState fmt 4
        (highamCh4KahanReturnedCounterexampleInput p) =
      { s := highamCh4KahanReturnedCounterexampleS3 p,
        e := highamCh4KahanReturnedCounterexampleX4 } := by
  norm_num [finiteKahanState, finiteKahanPrefixState, finiteKahanStep,
    finiteKahanStepTrace, KahanStepTrace.nextState, KahanState.zero,
    highamCh4KahanReturnedCounterexampleInput, Fin.foldl_succ,
    hround.y1, hround.s1, hround.q1, hround.e1, hround.y2,
    hround.s2, hround.q2, hround.e2, hround.y3, hround.s3,
    hround.q3, hround.e3, hround.y4, hround.s4, hround.q4,
    hround.e4]

/-- Returned stored sum for the four-term counterexample trace. -/
theorem highamCh4KahanReturnedCounterexampleSum_eq_of_rounding
    (fmt : FloatingPointFormat) {p : Real}
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p) :
    finiteKahanSum fmt 4
        (highamCh4KahanReturnedCounterexampleInput p) =
      highamCh4KahanReturnedCounterexampleS3 p := by
  have hstate :=
    highamCh4KahanReturnedCounterexampleState_eq_of_rounding fmt hround
  simpa [finiteKahanSum] using congrArg KahanState.s hstate

/-- Retained correction for the four-term counterexample trace. -/
theorem highamCh4KahanReturnedCounterexampleCorrection_eq_of_rounding
    (fmt : FloatingPointFormat) {p : Real}
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p) :
    finiteKahanCorrection fmt 4
        (highamCh4KahanReturnedCounterexampleInput p) =
      highamCh4KahanReturnedCounterexampleX4 := by
  have hstate :=
    highamCh4KahanReturnedCounterexampleState_eq_of_rounding fmt hround
  simpa [finiteKahanCorrection] using congrArg KahanState.e hstate

/-- Exact sum of the four-term returned-Kahan counterexample input. -/
theorem highamCh4KahanReturnedCounterexample_exactSum (p : Real) :
    Finset.univ.sum (fun i : Fin 4 =>
      highamCh4KahanReturnedCounterexampleInput p i) =
      -(10 * p + 10) := by
  rw [Fin.sum_univ_four]
  norm_num [highamCh4KahanReturnedCounterexampleInput,
    highamCh4KahanReturnedCounterexampleX1,
    highamCh4KahanReturnedCounterexampleX2,
    highamCh4KahanReturnedCounterexampleX3,
    highamCh4KahanReturnedCounterexampleX4]
  ring_nf

/-- Absolute input sum for the returned-Kahan counterexample when `p >= 1`. -/
theorem highamCh4KahanReturnedCounterexample_absSum
    (p : Real) (hp : 1 <= p) :
    Finset.univ.sum (fun i : Fin 4 =>
      |highamCh4KahanReturnedCounterexampleInput p i|) =
      10 * p + 26 := by
  rw [Fin.sum_univ_four]
  norm_num [highamCh4KahanReturnedCounterexampleInput,
    highamCh4KahanReturnedCounterexampleX1,
    highamCh4KahanReturnedCounterexampleX2,
    highamCh4KahanReturnedCounterexampleX3,
    highamCh4KahanReturnedCounterexampleX4]
  rw [abs_of_nonpos (by nlinarith : -4 + -(2 * p) <= 0)]
  rw [abs_of_nonpos (by nlinarith : 8 - 8 * p <= 0)]
  nlinarith

/-- Any source-weight representation of the returned value for the four-term
finite trace needs total coefficient budget at least the observed returned
error `22`. -/
theorem highamCh4KahanReturnedCounterexample_productLowerBound
    (fmt : FloatingPointFormat) {p b : Real}
    (hp : 1 <= p)
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p)
    (mu : Fin 4 -> Real)
    (hmu : highamCh4KahanReturnedCounterexampleMuBound b mu)
    (hrep :
      finiteKahanSum fmt 4
          (highamCh4KahanReturnedCounterexampleInput p) =
        Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * (1 + mu i))) :
    22 <= (10 * p + 26) * b := by
  have hreturned :=
    highamCh4KahanReturnedCounterexampleSum_eq_of_rounding fmt hround
  have hreturned' :
      finiteKahanSum fmt 4
          (highamCh4KahanReturnedCounterexampleInput p) =
        -(10 * p + 32) := by
    simpa [highamCh4KahanReturnedCounterexampleS3] using hreturned
  have hexact := highamCh4KahanReturnedCounterexample_exactSum p
  have hsplit :
      Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * (1 + mu i)) =
        Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i) +
        Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * mu i) := by
    calc
      Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * (1 + mu i)) =
          Finset.univ.sum (fun i : Fin 4 =>
            highamCh4KahanReturnedCounterexampleInput p i +
              highamCh4KahanReturnedCounterexampleInput p i * mu i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = Finset.univ.sum (fun i : Fin 4 =>
            highamCh4KahanReturnedCounterexampleInput p i) +
          Finset.univ.sum (fun i : Fin 4 =>
            highamCh4KahanReturnedCounterexampleInput p i * mu i) := by
            rw [Finset.sum_add_distrib]
  have hmu_sum :
      Finset.univ.sum (fun i : Fin 4 =>
        highamCh4KahanReturnedCounterexampleInput p i * mu i) = -22 := by
    nlinarith [hrep, hreturned', hexact, hsplit]
  have habs_sum :
      |Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * mu i)| <=
        Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i * mu i|) := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * mu i)
        Finset.univ)
  have hterm : forall i : Fin 4,
      |highamCh4KahanReturnedCounterexampleInput p i * mu i| <=
        |highamCh4KahanReturnedCounterexampleInput p i| * b := by
    intro i
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hmu i)
      (abs_nonneg (highamCh4KahanReturnedCounterexampleInput p i))
  have hsum_le :
      Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i * mu i|) <=
        Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i| * b) := by
    exact Finset.sum_le_sum (by intro i _hi; exact hterm i)
  have hsum_mul :
      Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i| * b) =
        (Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i|)) * b := by
    rw [Finset.sum_mul]
  have habs_eq :
      |Finset.univ.sum (fun i : Fin 4 =>
        highamCh4KahanReturnedCounterexampleInput p i * mu i)| = 22 := by
    rw [hmu_sum]
    norm_num
  have hchain :
      22 <=
        (Finset.univ.sum (fun i : Fin 4 =>
          |highamCh4KahanReturnedCounterexampleInput p i|)) * b := by
    rw [<- habs_eq]
    exact habs_sum.trans (hsum_le.trans (le_of_eq hsum_mul))
  rw [highamCh4KahanReturnedCounterexample_absSum p hp] at hchain
  exact hchain

/-- Quantitative lower bound on the maximum source coefficient for any
source-weight representation of the returned counterexample value. -/
theorem highamCh4KahanReturnedCounterexample_muLowerBound
    (fmt : FloatingPointFormat) {p b : Real}
    (hp : 1 <= p)
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p)
    (mu : Fin 4 -> Real)
    (hmu : highamCh4KahanReturnedCounterexampleMuBound b mu)
    (hrep :
      finiteKahanSum fmt 4
          (highamCh4KahanReturnedCounterexampleInput p) =
        Finset.univ.sum (fun i : Fin 4 =>
          highamCh4KahanReturnedCounterexampleInput p i * (1 + mu i))) :
    22 / (10 * p + 26) <= b := by
  have hprod :=
    highamCh4KahanReturnedCounterexample_productLowerBound
      fmt hp hround mu hmu hrep
  have hden : 0 < 10 * p + 26 := by nlinarith
  exact (div_le_iff₀ hden).mpr (by nlinarith [hprod])

/-- If a proposed uniform source-weight budget is below the forced lower bound
`22/(10p+26)`, then the returned trace cannot have such a representation. -/
theorem highamCh4KahanReturnedCounterexample_no_source_bound_of_lt
    (fmt : FloatingPointFormat) {p b : Real}
    (hp : 1 <= p)
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p)
    (hb : b < 22 / (10 * p + 26)) :
    Not (Exists fun
      (mu : HighamCh4KahanReturnedCounterexampleWeight) =>
        highamCh4KahanReturnedCounterexampleSourceRepresentation
          fmt p b mu) := by
  intro h
  cases h with
  | intro mu hrep =>
      cases hrep with
      | intro hmu hsum =>
          have hbound :=
            highamCh4KahanReturnedCounterexample_muLowerBound
              fmt hp hround mu hmu hsum
          nlinarith

/-- Conditional asymptotic obstruction: for any returned trace satisfying the
same identities at scale `p > 26`, the pure first-order budget `2/p` is too
small for a source-weight representation. -/
theorem highamCh4KahanReturnedCounterexample_no_source_bound_two_div_p
    (fmt : FloatingPointFormat) {p : Real}
    (hp : 26 < p)
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt p) :
    Not (Exists fun
      (mu : HighamCh4KahanReturnedCounterexampleWeight) =>
        highamCh4KahanReturnedCounterexampleSourceRepresentation
          fmt p (2 / p) mu) := by
  have hp_one : 1 <= p := by nlinarith
  apply highamCh4KahanReturnedCounterexample_no_source_bound_of_lt
    fmt hp_one hround
  have hp_pos : 0 < p := by nlinarith
  have hden : 0 < 10 * p + 26 := by nlinarith
  rw [div_lt_div_iff₀ hp_pos hden]
  nlinarith

/-- Local inequalities used in the suffix-recurrence audit for the remaining
returned-Kahan coefficient blocker.  This predicate deliberately mirrors the
available local facts, rather than claiming that the coefficients come from an
actual floating-point trace. -/
def highamCh4KahanSuffixCounterexampleLocalFacts
    (u : Real) (step : KahanCoupledCoeffStep)
    (deltaSub deltaY : Real) : Prop :=
  |step.totalStateCoeff - 1| <= 3 * u ^ 2 ∧
  |step.totalInputCoeff - 1| <= 2 * u + 9 * u ^ 2 ∧
  |step.C| <= u * (1 + u) ^ 2 ∧
  |step.correctionResidualCoeff| <= u * (1 + u) ^ 2 * (3 + u) ∧
  |step.correctionResidualCoeff + deltaSub| <= 7 * u ^ 2 ∧
  |step.residualCoeff - step.correctionResidualCoeff - deltaY| <= u ^ 2 ∧
  |step.residualCoeff + deltaSub - deltaY| <= 8 * u ^ 2 ∧
  |deltaSub| <= u ∧
  |deltaY| <= u

/-- First step of the two-step symbolic suffix-recurrence counterexample
suggested by the GPT-5.5 Pro proof-route audit. -/
def highamCh4KahanSuffixCounterexampleStep1
    (u : Real) : KahanCoupledCoeffStep :=
  { A := 1
    B := 1 + u
    C := 0
    D := u + u ^ 2
    x := 0 }

/-- Second step of the two-step symbolic suffix-recurrence counterexample. -/
def highamCh4KahanSuffixCounterexampleStep2
    (u : Real) : KahanCoupledCoeffStep :=
  { A := 1 + u
    B := 1 + u
    C := -u
    D := -u
    x := 0 }

/-- Returned coefficient after injecting a source at step 1 and propagating it
through the second symbolic suffix step. -/
def highamCh4KahanSuffixCounterexampleReturnedCoeff
    (u : Real) : Real :=
  KahanState.returnedFromTotalCorrection
    ((highamCh4KahanSuffixCounterexampleStep2 u).propagateTotalCorrection
      { s := (highamCh4KahanSuffixCounterexampleStep1 u).totalInputCoeff
        e := (highamCh4KahanSuffixCounterexampleStep1 u).D })

theorem highamCh4KahanSuffixCounterexampleReturnedCoeff_eq (u : Real) :
    highamCh4KahanSuffixCounterexampleReturnedCoeff u = (1 + u) ^ 3 := by
  dsimp [highamCh4KahanSuffixCounterexampleReturnedCoeff,
    highamCh4KahanSuffixCounterexampleStep1,
    highamCh4KahanSuffixCounterexampleStep2,
    KahanState.returnedFromTotalCorrection,
    KahanCoupledCoeffStep.propagateTotalCorrection,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.totalInputCoeff,
    KahanCoupledCoeffStep.residualCoeff,
    KahanCoupledCoeffStep.correctionResidualCoeff]
  ring

/-- One-step majorant update for the corrected leading-`3*u` suffix audit.
This is the Lean-facing arithmetic core of the GPT-5.5 Pro follow-up: if the
paired-total error `alpha` is already at most first-order small and the retained
correction majorant `beta` is at most `3*u`, then the local recurrence increases
`alpha` by only `13*u^2` and preserves `beta <= 3*u`. -/
theorem highamCh4KahanSuffixMajorant_step
    {u alpha beta alphaNext betaNext : Real}
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (halpha : alpha <= 1) (hbeta : beta <= 3 * u)
    (halphaNext :
      alphaNext <= alpha + 3 * u ^ 2 * (1 + alpha) +
        (2 * u + 8 * u ^ 2) * beta)
    (hbetaNext :
      betaNext <= u * (1 + u) ^ 2 * (1 + alpha) +
        (u + 7 * u ^ 2) * beta) :
    alphaNext <= alpha + 13 * u ^ 2 ∧ betaNext <= 3 * u := by
  constructor
  · nlinarith [hu0, hu64, halpha, hbeta, halphaNext]
  · have hfac_nonneg : 0 <= u * (1 + u) ^ 2 := by
      exact mul_nonneg hu0 (sq_nonneg (1 + u))
    have hterm1_le :
        u * (1 + u) ^ 2 * (1 + alpha) <=
          u * (1 + u) ^ 2 * 2 := by
      exact mul_le_mul_of_nonneg_left (by nlinarith [halpha]) hfac_nonneg
    have hterm1 :
        u * (1 + u) ^ 2 * (1 + alpha) <= (9 / 4) * u := by
      nlinarith [hterm1_le, hu0, hu64, sq_nonneg u,
        mul_nonneg (sq_nonneg u) hu0]
    have hcoef_nonneg : 0 <= u + 7 * u ^ 2 := by
      nlinarith [hu0, sq_nonneg u]
    have hterm2_le :
        (u + 7 * u ^ 2) * beta <= (u + 7 * u ^ 2) * (3 * u) := by
      exact mul_le_mul_of_nonneg_left hbeta hcoef_nonneg
    have hterm2 :
        (u + 7 * u ^ 2) * beta <= (3 / 4) * u := by
      nlinarith [hterm2_le, hu0, hu64, sq_nonneg u,
        mul_nonneg (sq_nonneg u) hu0]
    nlinarith

/-- Sequence-level corrected leading-`3*u` suffix majorant.  This theorem is
still an audit theorem: it proves the majorant recurrence once the `alpha` and
`beta` update inequalities have been supplied, but it does not itself derive
those updates from an arbitrary finite Kahan trace. -/
theorem highamCh4KahanSuffixMajorant_recurrence
    {u : Real} {m : Nat} {alpha beta : Nat -> Real}
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (hm : (m : Real) * u ^ 2 <= 1 / 16)
    (halpha0 : alpha 0 <= 2 * u + 9 * u ^ 2)
    (hbeta0 : beta 0 <= 3 * u)
    (halphaNext : ∀ j, j < m ->
      alpha (j + 1) <= alpha j + 3 * u ^ 2 * (1 + alpha j) +
        (2 * u + 8 * u ^ 2) * beta j)
    (hbetaNext : ∀ j, j < m ->
      beta (j + 1) <= u * (1 + u) ^ 2 * (1 + alpha j) +
        (u + 7 * u ^ 2) * beta j) :
    ∀ j, j <= m ->
      alpha j <= 2 * u + (9 + 13 * (j : Real)) * u ^ 2 ∧
        beta j <= 3 * u := by
  intro j hj
  induction j with
  | zero =>
      constructor
      · simpa using halpha0
      · simpa using hbeta0
  | succ j ih =>
      have hjm : j < m := Nat.lt_of_succ_le hj
      have hjle : j <= m := Nat.le_of_lt hjm
      have hih := ih hjle
      have hju2 : (j : Real) * u ^ 2 <= (m : Real) * u ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjle) (sq_nonneg u)
      have halpha_le_one : alpha j <= 1 := by
        have hju2_nonneg : 0 <= (j : Real) * u ^ 2 := by
          exact mul_nonneg (by exact_mod_cast Nat.zero_le j) (sq_nonneg u)
        nlinarith [hih.1, hju2, hju2_nonneg, hm, hu0, hu64, sq_nonneg u]
      have hstep :=
        highamCh4KahanSuffixMajorant_step
          hu0 hu64 halpha_le_one hih.2
          (halphaNext j hjm) (hbetaNext j hjm)
      constructor
      · norm_num [Nat.cast_succ]
        nlinarith [hih.1, hstep.1]
      · exact hstep.2

/-- The local suffix facts imply the corrected leading-`3*u` majorant update
for one abstract `(z,q)` propagation step. -/
theorem highamCh4KahanSuffixMajorant_update_of_localFacts
    {u z q deltaSub deltaY : Real} {step : KahanCoupledCoeffStep}
    (hu0 : 0 <= u)
    (hlocal :
      highamCh4KahanSuffixCounterexampleLocalFacts u step deltaSub deltaY) :
    |(step.totalStateCoeff * z + step.residualCoeff * q) - 1| <=
        |z - 1| + 3 * u ^ 2 * (1 + |z - 1|) +
          (2 * u + 8 * u ^ 2) * |q| ∧
      |step.C * z + step.correctionResidualCoeff * q| <=
        u * (1 + u) ^ 2 * (1 + |z - 1|) +
          (u + 7 * u ^ 2) * |q| := by
  rcases hlocal with
    ⟨hts, _htx, hC, _hc, hc_delta, _hr_c_delta, hr_combined, hdeltaSub, hdeltaY⟩
  have hz_abs : |z| <= 1 + |z - 1| := by
    calc
      |z| = |(z - 1) + 1| := by
        congr 1
        ring
      _ <= |z - 1| + |(1 : Real)| := abs_add_le _ _
      _ = 1 + |z - 1| := by ring
  have hr_abs : |step.residualCoeff| <= 2 * u + 8 * u ^ 2 := by
    have hr_decomp :
        step.residualCoeff =
          (step.residualCoeff + deltaSub - deltaY) - deltaSub + deltaY := by
      ring
    calc
      |step.residualCoeff| =
          |(step.residualCoeff + deltaSub - deltaY) - deltaSub + deltaY| := by
        exact congrArg abs hr_decomp
      _ <= |step.residualCoeff + deltaSub - deltaY| +
            |deltaSub| + |deltaY| := by
        calc
          |(step.residualCoeff + deltaSub - deltaY) - deltaSub + deltaY|
              <= |(step.residualCoeff + deltaSub - deltaY) - deltaSub| +
                  |deltaY| := abs_add_le _ _
          _ <= |step.residualCoeff + deltaSub - deltaY| +
                |deltaSub| + |deltaY| := by
            have hsub :
                |(step.residualCoeff + deltaSub - deltaY) - deltaSub| <=
                  |step.residualCoeff + deltaSub - deltaY| + |deltaSub| := by
              simpa [sub_eq_add_neg] using
                abs_add_le (step.residualCoeff + deltaSub - deltaY) (-deltaSub)
            nlinarith
      _ <= 2 * u + 8 * u ^ 2 := by nlinarith
  have hc_tight : |step.correctionResidualCoeff| <= u + 7 * u ^ 2 := by
    have hc_decomp :
        step.correctionResidualCoeff =
          (step.correctionResidualCoeff + deltaSub) - deltaSub := by
      ring
    calc
      |step.correctionResidualCoeff| =
          |(step.correctionResidualCoeff + deltaSub) - deltaSub| := by
        exact congrArg abs hc_decomp
      _ <= |step.correctionResidualCoeff + deltaSub| + |deltaSub| := by
        simpa [sub_eq_add_neg] using
          abs_add_le (step.correctionResidualCoeff + deltaSub) (-deltaSub)
      _ <= u + 7 * u ^ 2 := by nlinarith
  constructor
  · have hdecomp :
        (step.totalStateCoeff * z + step.residualCoeff * q) - 1 =
          (z - 1) + (step.totalStateCoeff - 1) * z +
            step.residualCoeff * q := by
      ring
    have htri :
        |(step.totalStateCoeff * z + step.residualCoeff * q) - 1| <=
          |z - 1| + |(step.totalStateCoeff - 1) * z| +
            |step.residualCoeff * q| := by
      rw [hdecomp]
      calc
        |(z - 1) + (step.totalStateCoeff - 1) * z +
            step.residualCoeff * q|
            <= |(z - 1) + (step.totalStateCoeff - 1) * z| +
                |step.residualCoeff * q| := abs_add_le _ _
        _ <= |z - 1| + |(step.totalStateCoeff - 1) * z| +
              |step.residualCoeff * q| := by
          have hfirst :
              |(z - 1) + (step.totalStateCoeff - 1) * z| <=
                |z - 1| + |(step.totalStateCoeff - 1) * z| := abs_add_le _ _
          nlinarith
    have hts_term :
        |(step.totalStateCoeff - 1) * z| <=
          3 * u ^ 2 * (1 + |z - 1|) := by
      rw [abs_mul]
      exact mul_le_mul hts hz_abs (abs_nonneg z)
        (by nlinarith [sq_nonneg u])
    have hr_term :
        |step.residualCoeff * q| <= (2 * u + 8 * u ^ 2) * |q| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hr_abs (abs_nonneg q)
    nlinarith
  · have htri :
        |step.C * z + step.correctionResidualCoeff * q| <=
          |step.C * z| + |step.correctionResidualCoeff * q| := abs_add_le _ _
    have hC_term :
        |step.C * z| <= u * (1 + u) ^ 2 * (1 + |z - 1|) := by
      rw [abs_mul]
      exact mul_le_mul hC hz_abs (abs_nonneg z)
        (mul_nonneg hu0 (sq_nonneg (1 + u)))
    have hc_term :
        |step.correctionResidualCoeff * q| <= (u + 7 * u ^ 2) * |q| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hc_tight (abs_nonneg q)
    nlinarith

/-- Auxiliary list propagation theorem for the corrected leading-`3*u`
suffix majorant.  Starting from an arbitrary paired-total radius `base`, each
local-fact step increases the paired-total radius by at most `13*u^2` and keeps
the retained correction within `3*u`. -/
theorem highamCh4KahanSuffixMajorant_propagate_of_localFacts_aux
    {u base : Real} {steps : List KahanCoupledCoeffStep} {init : KahanState}
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (hbudget : base + 13 * (steps.length : Real) * u ^ 2 <= 1)
    (hlocal : ∀ i : Fin steps.length, ∃ deltaSub deltaY : Real,
      highamCh4KahanSuffixCounterexampleLocalFacts u (steps.get i)
        deltaSub deltaY)
    (hinitS : |init.s - 1| <= base)
    (hinitE : |init.e| <= 3 * u) :
    let final := kahanCoupledTotalCorrectionPropagate steps init
    |final.s - 1| <= base + 13 * (steps.length : Real) * u ^ 2 ∧
      |final.e| <= 3 * u := by
  induction steps generalizing init base with
  | nil =>
      dsimp [kahanCoupledTotalCorrectionPropagate]
      constructor
      · simpa using hinitS
      · simpa using hinitE
  | cons step tail ih =>
      have hhead :
          ∃ deltaSub deltaY : Real,
            highamCh4KahanSuffixCounterexampleLocalFacts u step
              deltaSub deltaY := by
        simpa using hlocal ⟨0, by simp⟩
      rcases hhead with ⟨deltaSub, deltaY, hstepLocal⟩
      let next := step.propagateTotalCorrection init
      have hupdate :=
        highamCh4KahanSuffixMajorant_update_of_localFacts
          (u := u) (z := init.s) (q := init.e)
          (deltaSub := deltaSub) (deltaY := deltaY)
          (step := step) hu0 hstepLocal
      have hnextS_update :
          |next.s - 1| <= |init.s - 1| +
            3 * u ^ 2 * (1 + |init.s - 1|) +
              (2 * u + 8 * u ^ 2) * |init.e| := by
        simpa [next, KahanCoupledCoeffStep.propagateTotalCorrection,
          mul_comm, mul_left_comm, mul_assoc] using hupdate.1
      have hnextE_update :
          |next.e| <= u * (1 + u) ^ 2 * (1 + |init.s - 1|) +
            (u + 7 * u ^ 2) * |init.e| := by
        simpa [next, KahanCoupledCoeffStep.propagateTotalCorrection,
          mul_comm, mul_left_comm, mul_assoc] using hupdate.2
      have hlen_nonneg : 0 <= 13 * ((step :: tail).length : Real) * u ^ 2 := by
        exact mul_nonneg
          (mul_nonneg (by norm_num)
            (by exact_mod_cast Nat.zero_le (step :: tail).length))
          (sq_nonneg u)
      have hbase_le_one : base <= 1 := by nlinarith
      have halpha_le_one : |init.s - 1| <= 1 := by nlinarith [hinitS, hbase_le_one]
      have hmajorantStep :=
        highamCh4KahanSuffixMajorant_step
          hu0 hu64 halpha_le_one hinitE hnextS_update hnextE_update
      have hnextS :
          |next.s - 1| <= base + 13 * u ^ 2 := by
        nlinarith [hinitS, hmajorantStep.1]
      have htailBudget :
          (base + 13 * u ^ 2) + 13 * (tail.length : Real) * u ^ 2 <= 1 := by
        norm_num [Nat.cast_succ] at hbudget ⊢
        nlinarith
      have htailLocal :
          ∀ i : Fin tail.length, ∃ deltaSub deltaY : Real,
            highamCh4KahanSuffixCounterexampleLocalFacts u (tail.get i)
              deltaSub deltaY := by
        intro i
        have h := hlocal ⟨i.val + 1, by simp [i.isLt]⟩
        simpa using h
      have htail :=
        ih htailBudget htailLocal hnextS hmajorantStep.2
      dsimp [kahanCoupledTotalCorrectionPropagate]
      simpa [next, Nat.cast_succ, add_assoc, add_left_comm, add_comm,
        mul_add, add_mul] using htail

/-- Corrected leading-`3*u` list propagation theorem for the local suffix
facts.  This does not close Higham's printed leading-`2*u` Eq. (4.8); it is a
checked corrected route for the currently available local facts. -/
theorem highamCh4KahanSuffixMajorant_propagate_of_localFacts
    {u : Real} {steps : List KahanCoupledCoeffStep} {init : KahanState}
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (hm : (steps.length : Real) * u ^ 2 <= 1 / 16)
    (hlocal : ∀ i : Fin steps.length, ∃ deltaSub deltaY : Real,
      highamCh4KahanSuffixCounterexampleLocalFacts u (steps.get i)
        deltaSub deltaY)
    (hinitS : |init.s - 1| <= 2 * u + 9 * u ^ 2)
    (hinitE : |init.e| <= 3 * u) :
    let final := kahanCoupledTotalCorrectionPropagate steps init
    |final.s - 1| <= 2 * u + (9 + 13 * (steps.length : Real)) * u ^ 2 ∧
      |final.e| <= 3 * u := by
  have hbudget :
      (2 * u + 9 * u ^ 2) + 13 * (steps.length : Real) * u ^ 2 <= 1 := by
    nlinarith [hu0, hu64, hm, sq_nonneg u]
  have h :=
    highamCh4KahanSuffixMajorant_propagate_of_localFacts_aux
      (u := u) (base := 2 * u + 9 * u ^ 2)
      (steps := steps) (init := init)
      hu0 hu64 hbudget hlocal hinitS hinitE
  simpa [add_assoc, add_left_comm, add_comm, right_distrib, mul_add,
    mul_comm, mul_left_comm, mul_assoc] using h

/-- The actual indexed Kahan coefficient step satisfies the local-facts
interface used by the suffix recurrence audit. -/
theorem kahanCoupledCoeffStepOfIndex_localFacts
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (i : Fin n)
    (hu1 : fp.u <= 1) :
    highamCh4KahanSuffixCounterexampleLocalFacts fp.u
      (kahanCoupledCoeffStepOfIndex fp v i)
      (kahanTrace_deltaWitness fp v i).deltaSub
      (kahanTrace_deltaWitness fp v i).deltaY := by
  dsimp [highamCh4KahanSuffixCounterexampleLocalFacts]
  constructor
  · exact
      kahanCoupledCoeffStepOfIndex_totalStateCoeff_abs_sub_one_le_three_u_sq
        fp v i hu1
  constructor
  · exact
      kahanCoupledCoeffStepOfIndex_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
        fp v i hu1
  constructor
  · exact kahanCoupledCoeffStepOfIndex_C_abs_le fp v i
  constructor
  · exact kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_abs_le fp v i
  constructor
  · exact
      kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
        fp v i hu1
  constructor
  · exact
      kahanCoupledCoeffStepOfIndex_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
        fp v i
  constructor
  · exact
      kahanCoupledCoeffStepOfIndex_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
        fp v i hu1
  constructor
  · exact (kahanTrace_deltaWitness fp v i).h_deltaSub
  · exact (kahanTrace_deltaWitness fp v i).h_deltaY

/-- The actual coefficient-step list supplies local-facts witnesses for every
suffix index. -/
theorem kahanCoupledCoeffSteps_localFacts
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu1 : fp.u <= 1) :
    forall i : Fin (kahanCoupledCoeffSteps fp v k hk).length,
      exists deltaSub deltaY : Real,
        highamCh4KahanSuffixCounterexampleLocalFacts fp.u
          ((kahanCoupledCoeffSteps fp v k hk).get i)
          deltaSub deltaY := by
  intro i
  have hik : i.val < k := by
    simpa [kahanCoupledCoeffSteps] using i.isLt
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le hik hk⟩
  refine
    ⟨(kahanTrace_deltaWitness fp v idx).deltaSub,
      (kahanTrace_deltaWitness fp v idx).deltaY, ?_⟩
  simpa [kahanCoupledCoeffSteps, idx] using
    kahanCoupledCoeffStepOfIndex_localFacts fp v idx hu1

/-- Actual-step version of the corrected leading-`3*u` suffix majorant.  This
packages the individual Kahan coefficient-step inequalities into the abstract
local-facts recurrence. -/
theorem kahanCoupledCoeffSteps_totalCorrectionPropagate_abs_le_correctedSuffixMajorant
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu64 : fp.u <= 1 / 64)
    (hm : ((kahanCoupledCoeffSteps fp v k hk).length : Real) *
        fp.u ^ 2 <= 1 / 16)
    {init : KahanState}
    (hinitS : |init.s - 1| <= 2 * fp.u + 9 * fp.u ^ 2)
    (hinitE : |init.e| <= 3 * fp.u) :
    let final :=
      kahanCoupledTotalCorrectionPropagate
        (kahanCoupledCoeffSteps fp v k hk) init
    |final.s - 1| <=
        2 * fp.u +
          (9 + 13 * ((kahanCoupledCoeffSteps fp v k hk).length : Real)) *
            fp.u ^ 2 ∧
      |final.e| <= 3 * fp.u := by
  have hu1 : fp.u <= 1 := by nlinarith
  exact
    highamCh4KahanSuffixMajorant_propagate_of_localFacts
      (u := fp.u) (steps := kahanCoupledCoeffSteps fp v k hk)
      (init := init) fp.u_nonneg hu64 hm
      (kahanCoupledCoeffSteps_localFacts fp v k hk hu1)
      hinitS hinitE

/-- Any dropped suffix of the actual coefficient-step list still supplies
local-facts witnesses at every suffix index. -/
theorem kahanCoupledCoeffSteps_drop_localFacts
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu1 : fp.u <= 1) (r : Nat) :
    forall i : Fin ((kahanCoupledCoeffSteps fp v k hk).drop r).length,
      exists deltaSub deltaY : Real,
        highamCh4KahanSuffixCounterexampleLocalFacts fp.u
          (((kahanCoupledCoeffSteps fp v k hk).drop r).get i)
          deltaSub deltaY := by
  intro i
  let steps := kahanCoupledCoeffSteps fp v k hk
  have hi_len : i.val < steps.length - r := by
    simpa [steps, List.length_drop] using i.isLt
  have hir : r + i.val < steps.length := by
    simpa [Nat.add_comm] using Nat.add_lt_of_lt_sub hi_len
  let j : Fin steps.length := ⟨r + i.val, hir⟩
  rcases kahanCoupledCoeffSteps_localFacts fp v k hk hu1 j with
    ⟨deltaSub, deltaY, hlocal⟩
  refine ⟨deltaSub, deltaY, ?_⟩
  have hget : (steps.drop r).get i = steps.get j := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    change (steps.drop r)[i.val] = steps[r + i.val]
    exact List.getElem_drop (xs := steps) (i := r) (j := i.val)
      (h := i.isLt)
  change highamCh4KahanSuffixCounterexampleLocalFacts fp.u
    ((steps.drop r).get i) deltaSub deltaY
  rw [hget]
  simpa [steps] using hlocal

/-- Dropped-suffix version of the corrected leading-`3*u` actual-step
majorant.  This is the reusable suffix handoff for source-coefficient
propagation. -/
theorem kahanCoupledCoeffSteps_drop_totalCorrectionPropagate_abs_le_correctedSuffixMajorant
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (r : Nat)
    (hu64 : fp.u <= 1 / 64)
    (hm : (((kahanCoupledCoeffSteps fp v k hk).drop r).length : Real) *
        fp.u ^ 2 <= 1 / 16)
    {init : KahanState}
    (hinitS : |init.s - 1| <= 2 * fp.u + 9 * fp.u ^ 2)
    (hinitE : |init.e| <= 3 * fp.u) :
    let suffix := (kahanCoupledCoeffSteps fp v k hk).drop r
    let final := kahanCoupledTotalCorrectionPropagate suffix init
    |final.s - 1| <=
        2 * fp.u + (9 + 13 * (suffix.length : Real)) * fp.u ^ 2 ∧
      |final.e| <= 3 * fp.u := by
  have hu1 : fp.u <= 1 := by nlinarith
  exact
    highamCh4KahanSuffixMajorant_propagate_of_localFacts
      (u := fp.u) (steps := (kahanCoupledCoeffSteps fp v k hk).drop r)
      (init := init) fp.u_nonneg hu64 hm
      (kahanCoupledCoeffSteps_drop_localFacts fp v k hk hu1 r)
      hinitS hinitE

/-- Corrected leading-`3*u` paired-coordinate bound for every propagated
source coefficient of the actual Kahan coefficient-step list.  This theorem
specializes the dropped-suffix majorant to the source coefficient injected at
index `i`; it is source-shaped for the compensated-total coordinate, not yet
Higham's ordinary returned-`s` leading-`2*u` theorem. -/
theorem kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_correctedSuffixMajorant
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu64 : fp.u <= 1 / 64)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hm : (((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)).length : Real) *
        fp.u ^ 2 <= 1 / 16) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    |(kahanCoupledSourceTotalCorrectionCoeff steps i).s - 1| <=
        2 * fp.u +
          (9 + 13 * ((steps.drop (i.val + 1)).length : Real)) *
            fp.u ^ 2 ∧
      |(kahanCoupledSourceTotalCorrectionCoeff steps i).e| <= 3 * fp.u := by
  have hu1 : fp.u <= 1 := by nlinarith
  let steps := kahanCoupledCoeffSteps fp v k hk
  have hmem : steps.get i ∈ steps := List.get_mem steps i
  have hinitS :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| <=
        2 * fp.u + 9 * fp.u ^ 2 := by
    have h :=
      kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
        fp v k hk hu1 (steps.get i) hmem
    simpa [steps, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff,
      KahanCoupledCoeffStep.totalInputCoeff] using h
  have hinitE :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| <=
        3 * fp.u := by
    have hD :=
      kahanCoupledCoeffSteps_D_abs_le fp v k hk (steps.get i) hmem
    have hD3 : fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) <= 3 * fp.u := by
      nlinarith [fp.u_nonneg, hu64, sq_nonneg fp.u,
        mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))]
    have hD_bound : |(steps.get i).D| <= 3 * fp.u := by
      nlinarith
    simpa [steps, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff] using hD_bound
  have hprop :=
    kahanCoupledCoeffSteps_drop_totalCorrectionPropagate_abs_le_correctedSuffixMajorant
      fp v k hk (i.val + 1) hu64 hm hinitS hinitE
  simpa [steps, kahanCoupledSourceCoeff_totalCorrection_eq] using hprop

/-- Final-step returned-coordinate extraction for the corrected ordinary
returned-Kahan route.  If the paired source-total state has leading `2*u`, the
last ordinary returned step contributes the missing main-addition first-order
term, giving leading `3*u`. -/
theorem highamCh4KahanReturnedFinalStep_majorant
    {u a : Real} {step : KahanCoupledCoeffStep} {state : KahanState}
    (hu0 : 0 <= u)
    (hS : |state.s - 1| <= 2 * u + a * u ^ 2)
    (hE : |state.e| <= 3 * u)
    (hA : |step.returnedStateCoeff - 1| <= u)
    (hB : |step.returnedCorrectionCoeff| <= u * (1 + u)) :
    |KahanState.returnedFromTotalCorrection
        (step.propagateTotalCorrection state) - 1| <=
      3 * u + (a + 5) * u ^ 2 + (a + 3) * u ^ 3 := by
  have hbase :=
    KahanCoupledCoeffStep.propagateTotalCorrection_returnedDev_abs_le_of_bounds
      step state hA hB
  have hone : 0 <= 1 + u := by nlinarith
  have htheta : 0 <= u * (1 + u) := mul_nonneg hu0 hone
  have hSstep :
      |state.s - 1| * (1 + u) <=
        (2 * u + a * u ^ 2) * (1 + u) := by
    exact mul_le_mul_of_nonneg_right hS hone
  have hEstep :
      |state.e| * (u * (1 + u)) <=
        (3 * u) * (u * (1 + u)) := by
    exact mul_le_mul_of_nonneg_right hE htheta
  calc
    |KahanState.returnedFromTotalCorrection
        (step.propagateTotalCorrection state) - 1|
        <= |state.s - 1| * (1 + u) + u +
          |state.e| * (u * (1 + u)) := hbase
    _ <= (2 * u + a * u ^ 2) * (1 + u) + u +
          (3 * u) * (u * (1 + u)) := by nlinarith
    _ = 3 * u + (a + 5) * u ^ 2 + (a + 3) * u ^ 3 := by ring

/-- Append-final-step form of the corrected ordinary returned route.  A
paired-coordinate prefix recurrence with leading `2*u` becomes an ordinary
returned-coordinate bound with leading `3*u` after one final returned step. -/
theorem highamCh4KahanReturnedAppendFinal_majorant
    {u : Real} {pref : List KahanCoupledCoeffStep}
    {last : KahanCoupledCoeffStep} {init : KahanState}
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (hm : (pref.length : Real) * u ^ 2 <= 1 / 16)
    (hlocal : forall i : Fin pref.length, exists deltaSub deltaY : Real,
      highamCh4KahanSuffixCounterexampleLocalFacts u (pref.get i)
        deltaSub deltaY)
    (hinitS : |init.s - 1| <= 2 * u + 9 * u ^ 2)
    (hinitE : |init.e| <= 3 * u)
    (hA : |last.returnedStateCoeff - 1| <= u)
    (hB : |last.returnedCorrectionCoeff| <= u * (1 + u)) :
    |KahanState.returnedFromTotalCorrection
        (kahanCoupledTotalCorrectionPropagate (pref ++ [last]) init) - 1| <=
      3 * u +
        ((9 + 13 * (pref.length : Real)) + 5) * u ^ 2 +
          ((9 + 13 * (pref.length : Real)) + 3) * u ^ 3 := by
  let mid := kahanCoupledTotalCorrectionPropagate pref init
  have hprefix :=
    highamCh4KahanSuffixMajorant_propagate_of_localFacts
      (u := u) (steps := pref) (init := init)
      hu0 hu64 hm hlocal hinitS hinitE
  have hfold :
      kahanCoupledTotalCorrectionPropagate (pref ++ [last]) init =
        last.propagateTotalCorrection mid := by
    dsimp [kahanCoupledTotalCorrectionPropagate, mid]
    simp [List.foldl_append]
  rw [hfold]
  exact
    highamCh4KahanReturnedFinalStep_majorant
      (u := u) (a := 9 + 13 * (pref.length : Real))
      (step := last) (state := mid)
      hu0 hprefix.1 hprefix.2 hA hB

/-- Nonempty-list form of the corrected ordinary returned route, splitting the
list at its final step. -/
theorem highamCh4KahanReturnedNonempty_majorant
    {u : Real} {steps : List KahanCoupledCoeffStep} {init : KahanState}
    (hne : Not (steps = []))
    (hu0 : 0 <= u) (hu64 : u <= 1 / 64)
    (hm : (steps.dropLast.length : Real) * u ^ 2 <= 1 / 16)
    (hlocal : forall i : Fin steps.dropLast.length, exists deltaSub deltaY : Real,
      highamCh4KahanSuffixCounterexampleLocalFacts u (steps.dropLast.get i)
        deltaSub deltaY)
    (hinitS : |init.s - 1| <= 2 * u + 9 * u ^ 2)
    (hinitE : |init.e| <= 3 * u)
    (hA : |(steps.getLast hne).returnedStateCoeff - 1| <= u)
    (hB : |(steps.getLast hne).returnedCorrectionCoeff| <= u * (1 + u)) :
    |KahanState.returnedFromTotalCorrection
        (kahanCoupledTotalCorrectionPropagate steps init) - 1| <=
      3 * u +
        ((9 + 13 * (steps.dropLast.length : Real)) + 5) * u ^ 2 +
          ((9 + 13 * (steps.dropLast.length : Real)) + 3) * u ^ 3 := by
  have hdecomp :
      kahanCoupledTotalCorrectionPropagate steps init =
        kahanCoupledTotalCorrectionPropagate
          (steps.dropLast ++ [steps.getLast hne]) init := by
    rw [List.dropLast_append_getLast hne]
  rw [hdecomp]
  exact
    highamCh4KahanReturnedAppendFinal_majorant
      (u := u) (pref := steps.dropLast) (last := steps.getLast hne)
      (init := init) hu0 hu64 hm hlocal hinitS hinitE hA hB

/-- Membership version of the actual-step local-facts package. -/
theorem kahanCoupledCoeffSteps_localFacts_of_mem
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu1 : fp.u <= 1) {step : KahanCoupledCoeffStep}
    (hmem : step ∈ kahanCoupledCoeffSteps fp v k hk) :
    exists deltaSub deltaY : Real,
      highamCh4KahanSuffixCounterexampleLocalFacts fp.u step
        deltaSub deltaY := by
  let steps := kahanCoupledCoeffSteps fp v k hk
  have hmem' : step ∈ steps := by simpa [steps] using hmem
  rcases List.get_of_mem hmem' with ⟨idx, hidx⟩
  rcases kahanCoupledCoeffSteps_localFacts fp v k hk hu1 idx with
    ⟨deltaSub, deltaY, hlocal⟩
  refine ⟨deltaSub, deltaY, ?_⟩
  rw [← hidx]
  simpa [steps] using hlocal

/-- Local `B`-coefficient bound for an actual coupled Kahan step.  This handles
the empty-suffix source-coefficient case. -/
theorem kahanCoupledCoeffStepOfIndex_B_abs_sub_one_le_two_u_plus_u_sq
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).B - 1| <=
      2 * fp.u + fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanTrace_deltaWitness_storedSumInputCoeff_abs_sub_one_le_two_u_plus_u_sq
      fp v i

/-- Corrected ordinary returned source-coefficient bound for a nonempty suffix.
This is the main checked Lean translation of the whole-problem GPT-5.5 Pro
audit's leading-`3*u` route. -/
theorem kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant_nonempty
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu64 : fp.u <= 1 / 64)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hne :
      Not (((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)) = []))
    (hm :
      ((((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)).dropLast.length : Real) *
          fp.u ^ 2 <= 1 / 16)) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let suffix := steps.drop (i.val + 1)
    |(kahanCoupledSourceCoeff steps i).s - 1| <=
      3 * fp.u +
        ((9 + 13 * (suffix.dropLast.length : Real)) + 5) * fp.u ^ 2 +
          ((9 + 13 * (suffix.dropLast.length : Real)) + 3) * fp.u ^ 3 := by
  have hu1 : fp.u <= 1 := by nlinarith
  let steps := kahanCoupledCoeffSteps fp v k hk
  let suffix := steps.drop (i.val + 1)
  have hmem : steps.get i ∈ steps := List.get_mem steps i
  have hinitS :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| <=
        2 * fp.u + 9 * fp.u ^ 2 := by
    have h :=
      kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
        fp v k hk hu1 (steps.get i) hmem
    simpa [steps, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff,
      KahanCoupledCoeffStep.totalInputCoeff] using h
  have hinitE :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| <=
        3 * fp.u := by
    have hD :=
      kahanCoupledCoeffSteps_D_abs_le fp v k hk (steps.get i) hmem
    have hD3 : fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) <= 3 * fp.u := by
      nlinarith [fp.u_nonneg, hu64, sq_nonneg fp.u,
        mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))]
    have hD_bound : |(steps.get i).D| <= 3 * fp.u := by
      nlinarith
    simpa [steps, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff] using hD_bound
  have hprefixLocal :
      forall j : Fin suffix.dropLast.length, exists deltaSub deltaY : Real,
        highamCh4KahanSuffixCounterexampleLocalFacts fp.u
          (suffix.dropLast.get j) deltaSub deltaY := by
    intro j
    have hmemDropLast : suffix.dropLast.get j ∈ suffix.dropLast :=
      List.get_mem suffix.dropLast j
    have hmemSuffix : suffix.dropLast.get j ∈ suffix :=
      List.dropLast_subset suffix hmemDropLast
    have hmemSteps : suffix.dropLast.get j ∈ steps :=
      List.mem_of_mem_drop hmemSuffix
    exact
      kahanCoupledCoeffSteps_localFacts_of_mem
        fp v k hk hu1 hmemSteps
  have hlastMemSuffix : suffix.getLast hne ∈ suffix := List.getLast_mem hne
  have hlastMemSteps : suffix.getLast hne ∈ steps :=
    List.mem_of_mem_drop hlastMemSuffix
  have hA :
      |(suffix.getLast hne).returnedStateCoeff - 1| <= fp.u :=
    kahanCoupledCoeffSteps_returnedStateCoeff_abs_sub_one_le
      fp v k hk (suffix.getLast hne) hlastMemSteps
  have hB :
      |(suffix.getLast hne).returnedCorrectionCoeff| <= fp.u * (1 + fp.u) :=
    kahanCoupledCoeffSteps_returnedCorrectionCoeff_abs_le
      fp v k hk (suffix.getLast hne) hlastMemSteps
  have hret :=
    highamCh4KahanReturnedNonempty_majorant
      (u := fp.u) (steps := suffix)
      (init := KahanState.totalCorrection (steps.get i).sourceCoeff)
      hne fp.u_nonneg hu64 hm hprefixLocal hinitS hinitE hA hB
  have hsource :=
    kahanCoupledSourceCoeff_s_eq_returned_totalCorrectionPropagate steps i
  dsimp
  rw [hsource]
  simpa [steps, suffix] using hret

/-- Corrected ordinary returned source-coefficient bound for an empty suffix;
the source coefficient is just the local stored-sum input coefficient. -/
theorem kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant_empty
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hempty :
      ((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)) = []) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let suffix := steps.drop (i.val + 1)
    |(kahanCoupledSourceCoeff steps i).s - 1| <=
      3 * fp.u +
        ((9 + 13 * (suffix.dropLast.length : Real)) + 5) * fp.u ^ 2 +
          ((9 + 13 * (suffix.dropLast.length : Real)) + 3) * fp.u ^ 3 := by
  have hu0 := fp.u_nonneg
  have hB :
      |((kahanCoupledCoeffSteps fp v k hk).get i).B - 1| <=
        2 * fp.u + fp.u ^ 2 := by
    let steps := kahanCoupledCoeffSteps fp v k hk
    have hik : i.val < k := by
      simpa [steps, kahanCoupledCoeffSteps] using i.isLt
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le hik hk⟩
    have hget : steps.get i = kahanCoupledCoeffStepOfIndex fp v idx := by
      rw [List.get_eq_getElem]
      simp [steps, kahanCoupledCoeffSteps, idx]
    rw [hget]
    exact kahanCoupledCoeffStepOfIndex_B_abs_sub_one_le_two_u_plus_u_sq
      fp v idx
  have hsource :
      (kahanCoupledSourceCoeff (kahanCoupledCoeffSteps fp v k hk) i).s =
        ((kahanCoupledCoeffSteps fp v k hk).get i).B := by
    dsimp [kahanCoupledSourceCoeff, KahanCoupledCoeffStep.sourceCoeff,
      kahanCoupledCoeffPropagate]
    simp [hempty]
  dsimp
  rw [hsource]
  have hu3_nonneg : 0 <= fp.u ^ 3 := by positivity
  nlinarith [hB, hu0, sq_nonneg fp.u, hu3_nonneg]

/-- Corrected ordinary returned source-coefficient bound for actual Kahan
coefficient steps.  The leading constant is `3*u`, matching the whole-problem
source-statement audit for the ordinary returned coordinate rather than the
printed leading-`2*u` claim. -/
theorem kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant
    (fp : FPModel) {n : Nat} (v : Fin n -> Real) (k : Nat) (hk : k <= n)
    (hu64 : fp.u <= 1 / 64)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hm :
      ((((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)).dropLast.length : Real) *
          fp.u ^ 2 <= 1 / 16)) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let suffix := steps.drop (i.val + 1)
    |(kahanCoupledSourceCoeff steps i).s - 1| <=
      3 * fp.u +
        ((9 + 13 * (suffix.dropLast.length : Real)) + 5) * fp.u ^ 2 +
          ((9 + 13 * (suffix.dropLast.length : Real)) + 3) * fp.u ^ 3 := by
  let steps := kahanCoupledCoeffSteps fp v k hk
  let suffix := steps.drop (i.val + 1)
  by_cases hnil : suffix = []
  · have hempty :
        ((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)) = [] := by
      simpa [steps, suffix] using hnil
    simpa [steps, suffix] using
      kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant_empty
        fp v k hk i hempty
  · have hne :
        Not (((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)) = []) := by
      simpa [steps, suffix] using hnil
    simpa [steps, suffix] using
      kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant_nonempty
        fp v k hk hu64 i hne hm

/-- Corrected ordinary returned-Kahan backward-error representation with
leading constant `3*u`.  This is source-honest for the current model after the
whole-problem audit: it does not claim Higham's printed ordinary returned
leading `2*u` statement, which remains available only in the conditional
exact-subtraction/coherence routes above. -/
theorem fl_kahanSum_backward_error_source_bound_correctedReturnedMajorant
    (fp : FPModel) (n : Nat) (v : Fin n -> Real)
    (hu64 : fp.u <= 1 / 64)
    (hm : (n : Real) * fp.u ^ 2 <= 1 / 16) :
    exists mu : Fin n -> Real,
      (forall i,
        |mu i| <=
          3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
            (12 + 13 * (n : Real)) * fp.u ^ 3) /\
      fl_kahanSum fp n v = Finset.univ.sum (fun i : Fin n => v i * (1 + mu i)) := by
  let steps := kahanCoupledCoeffSteps fp v n (Nat.le_refl n)
  have hcoeff :
      forall i : Fin steps.length,
        |(kahanCoupledSourceCoeff steps i).s - 1| <=
          3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
            (12 + 13 * (n : Real)) * fp.u ^ 3 := by
    intro i
    let suffix := steps.drop (i.val + 1)
    let m := suffix.dropLast.length
    have hm_le_n_nat : m <= n := by
      have hm_le_suffix : m <= suffix.length := by
        simp [m, List.length_dropLast]
      have hsuffix_le_steps : suffix.length <= steps.length := by
        dsimp [suffix]
        rw [List.length_drop]
        exact Nat.sub_le steps.length (i.val + 1)
      have hsteps_len : steps.length = n := by
        simp [steps, kahanCoupledCoeffSteps]
      have hm_le_steps : m <= steps.length := Nat.le_trans hm_le_suffix hsuffix_le_steps
      simpa [hsteps_len] using hm_le_steps
    have hm_le_n : (m : Real) <= (n : Real) := by exact_mod_cast hm_le_n_nat
    have hm_budget : (m : Real) * fp.u ^ 2 <= 1 / 16 := by
      have hu2_nonneg : 0 <= fp.u ^ 2 := sq_nonneg fp.u
      nlinarith [hm, hm_le_n, hu2_nonneg]
    have hsrc :=
      kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_correctedReturnedMajorant
        fp v n (Nat.le_refl n) hu64 i hm_budget
    have hbound :
        3 * fp.u +
              ((9 + 13 * (suffix.dropLast.length : Real)) + 5) *
                fp.u ^ 2 +
            ((9 + 13 * (suffix.dropLast.length : Real)) + 3) *
                fp.u ^ 3 <=
          3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
            (12 + 13 * (n : Real)) * fp.u ^ 3 := by
      have hu2_nonneg : 0 <= fp.u ^ 2 := sq_nonneg fp.u
      have hu3_nonneg : 0 <= fp.u ^ 3 := by nlinarith [fp.u_nonneg, sq_nonneg fp.u]
      have hm_real : ((suffix.dropLast.length : Real)) <= (n : Real) := by
        simpa [m] using hm_le_n
      nlinarith
    dsimp [steps] at hsrc
    exact le_trans hsrc hbound
  exact
    fl_kahanSum_backward_error_source_bound_of_sourceCoeff_s_bound
      fp n v (by simpa [steps] using hcoeff)

theorem highamCh4KahanSuffixCounterexampleStep1_localFacts
    {u : Real} (hu0 : 0 <= u) (_hu1 : u <= 1) :
    highamCh4KahanSuffixCounterexampleLocalFacts u
      (highamCh4KahanSuffixCounterexampleStep1 u) (-u) u := by
  dsimp [highamCh4KahanSuffixCounterexampleLocalFacts,
    highamCh4KahanSuffixCounterexampleStep1,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.totalInputCoeff,
    KahanCoupledCoeffStep.residualCoeff,
    KahanCoupledCoeffStep.correctionResidualCoeff]
  constructor
  · norm_num
    exact mul_nonneg (by norm_num : (0 : Real) <= 3) (sq_nonneg u)
  constructor
  · rw [abs_of_nonneg (by nlinarith [hu0, sq_nonneg u])]
    nlinarith [sq_nonneg u]
  constructor
  · norm_num
    exact mul_nonneg hu0 (sq_nonneg (1 + u))
  constructor
  · have hnonneg : 0 <= u * (1 + u) ^ 2 * (3 + u) := by
      exact mul_nonneg (mul_nonneg hu0 (sq_nonneg (1 + u))) (by nlinarith)
    rw [abs_of_nonneg (by nlinarith [hu0, sq_nonneg u])]
    ring_nf
    nlinarith [hu0, sq_nonneg u, hnonneg]
  constructor
  · rw [abs_of_nonneg (by ring_nf; exact sq_nonneg u)]
    ring_nf
    nlinarith [sq_nonneg u]
  constructor
  · ring_nf
    norm_num
    exact sq_nonneg u
  constructor
  · rw [abs_of_nonneg (by ring_nf; exact sq_nonneg u)]
    ring_nf
    nlinarith [sq_nonneg u]
  constructor
  · rw [abs_of_nonpos (by nlinarith : -u <= 0)]
    simp
  · rw [abs_of_nonneg hu0]

theorem highamCh4KahanSuffixCounterexampleStep2_localFacts
    {u : Real} (hu0 : 0 <= u) (_hu1 : u <= 1) :
    highamCh4KahanSuffixCounterexampleLocalFacts u
      (highamCh4KahanSuffixCounterexampleStep2 u) 0 0 := by
  dsimp [highamCh4KahanSuffixCounterexampleLocalFacts,
    highamCh4KahanSuffixCounterexampleStep2,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.totalInputCoeff,
    KahanCoupledCoeffStep.residualCoeff,
    KahanCoupledCoeffStep.correctionResidualCoeff]
  constructor
  · norm_num
    nlinarith [sq_nonneg u]
  constructor
  · norm_num
    nlinarith [hu0, sq_nonneg u]
  constructor
  · rw [abs_of_nonpos (by nlinarith : -u <= 0)]
    have hone : 1 <= (1 + u) ^ 2 := by nlinarith [hu0, sq_nonneg u]
    calc
      -(-u) = u := by ring
      _ = u * 1 := by ring
      _ <= u * (1 + u) ^ 2 := mul_le_mul_of_nonneg_left hone hu0
  constructor
  · norm_num
    exact mul_nonneg (mul_nonneg hu0 (sq_nonneg (1 + u))) (by nlinarith)
  constructor
  · norm_num
    nlinarith [sq_nonneg u]
  constructor
  · ring_nf
    norm_num
    exact sq_nonneg u
  constructor
  · norm_num
    nlinarith [sq_nonneg u]
  constructor
  · norm_num
    exact hu0
  · norm_num
    exact hu0

/-- Exact returned-coefficient error in the two-step symbolic suffix
counterexample. -/
theorem highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_eq
    {u : Real} (hu0 : 0 <= u) :
    |highamCh4KahanSuffixCounterexampleReturnedCoeff u - 1| =
      3 * u + 3 * u ^ 2 + u ^ 3 := by
  rw [highamCh4KahanSuffixCounterexampleReturnedCoeff_eq]
  have hpoly_nonneg : 0 <= 3 * u + 3 * u ^ 2 + u ^ 3 := by
    nlinarith [hu0, sq_nonneg u, mul_nonneg (sq_nonneg u) hu0]
  rw [show (1 + u) ^ 3 - 1 = 3 * u + 3 * u ^ 2 + u ^ 3 by ring]
  exact abs_of_nonneg hpoly_nonneg

/-- On the usual small-unit interval, the symbolic suffix counterexample has a
leading-`3*u` returned-coefficient error.  This is a route audit for corrected
surfaces; it is not a positive theorem for arbitrary Kahan traces. -/
theorem highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_le_three_u_plus_four_u_sq
    {u : Real} (hu0 : 0 <= u) (hu1 : u <= 1) :
    |highamCh4KahanSuffixCounterexampleReturnedCoeff u - 1| <=
      3 * u + 4 * u ^ 2 := by
  rw [highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_eq hu0]
  nlinarith [hu0, hu1, sq_nonneg u, mul_nonneg (sq_nonneg u) hu0]

/-- The local suffix-recurrence facts alone cannot imply a
`2*u + K*u^2` returned-coefficient cap with any fixed nonnegative constant
`K`.  The counterexample is purely algebraic; it is a route audit, not a claim
that the two symbolic steps are realized by round-to-even arithmetic. -/
theorem highamCh4KahanSuffixCounterexample_not_two_u_plus_K_u_sq
    (K u : Real) (hK : 0 <= K) (hu : 0 < u)
    (huSmall : u < min (1 / 20) (1 / (K + 1))) :
    highamCh4KahanSuffixCounterexampleLocalFacts u
      (highamCh4KahanSuffixCounterexampleStep1 u) (-u) u ∧
    highamCh4KahanSuffixCounterexampleLocalFacts u
      (highamCh4KahanSuffixCounterexampleStep2 u) 0 0 ∧
    2 * u + K * u ^ 2 <
      |highamCh4KahanSuffixCounterexampleReturnedCoeff u - 1| := by
  have hu0 : 0 <= u := le_of_lt hu
  have hu_lt_one_twentieth : u < 1 / 20 := lt_of_lt_of_le huSmall (min_le_left _ _)
  have hu1 : u <= 1 := by nlinarith
  have hK1pos : 0 < K + 1 := by nlinarith
  have hu_lt_inv : u < 1 / (K + 1) := lt_of_lt_of_le huSmall (min_le_right _ _)
  have hmul : u * (K + 1) < 1 := by
    rw [lt_div_iff₀ hK1pos] at hu_lt_inv
    simpa [mul_comm] using hu_lt_inv
  have hKu : K * u < 1 := by nlinarith
  have hKu2 : K * u ^ 2 < u := by nlinarith [mul_pos hK1pos hu, hKu]
  have hret :
      |highamCh4KahanSuffixCounterexampleReturnedCoeff u - 1| =
        3 * u + 3 * u ^ 2 + u ^ 3 := by
    exact highamCh4KahanSuffixCounterexampleReturnedCoeff_abs_sub_one_eq hu0
  refine ⟨?_, ?_, ?_⟩
  · exact highamCh4KahanSuffixCounterexampleStep1_localFacts hu0 hu1
  · exact highamCh4KahanSuffixCounterexampleStep2_localFacts hu0 hu1
  · rw [hret]
    nlinarith [hKu2, sq_nonneg u, mul_nonneg (sq_nonneg u) hu0]

/-- For the concrete p=5 scale (`p = 32`, so `2u = 1/16`), the returned
four-term finite round-to-even trace cannot be represented with all source
weights bounded by `2u`. -/
theorem highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth
    (fmt : FloatingPointFormat)
    (hround : HighamCh4KahanReturnedCounterexampleRounding fmt 32) :
    Not (Exists fun
      (mu : HighamCh4KahanReturnedCounterexampleWeight) =>
        highamCh4KahanReturnedCounterexampleSourceRepresentation
          fmt 32 (1 / 16) mu) := by
  intro h
  cases h with
  | intro mu hrep =>
      cases hrep with
      | intro hmu hsum =>
          have hp32 : (1 : Real) <= 32 := by norm_num
          have hbound :=
            highamCh4KahanReturnedCounterexample_productLowerBound
              fmt hp32 hround mu hmu hsum
          norm_num at hbound

/-- The concrete p=5 binary finite round-to-even trace finishes at stored sum
`-352` with retained correction `8`. -/
theorem highamCh4KahanReturnedCounterexampleP5_state_eq :
    finiteKahanState highamCh4KahanReturnedCounterexampleP5Format 4
        (highamCh4KahanReturnedCounterexampleInput 32) =
      { s := highamCh4KahanReturnedCounterexampleS3 32,
        e := highamCh4KahanReturnedCounterexampleX4 } :=
  highamCh4KahanReturnedCounterexampleState_eq_of_rounding
    highamCh4KahanReturnedCounterexampleP5Format
    highamCh4KahanReturnedCounterexampleP5_rounding

/-- Concrete p=5 finite round-to-even Kahan counterexample: no source-weight
representation with all coefficients bounded by `1/16` can produce the returned
stored sum. -/
theorem highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth_actual :
    Not (Exists fun
      (mu : HighamCh4KahanReturnedCounterexampleWeight) =>
        highamCh4KahanReturnedCounterexampleSourceRepresentation
          highamCh4KahanReturnedCounterexampleP5Format 32 (1 / 16) mu) :=
  highamCh4KahanReturnedCounterexampleP5_no_source_bound_one_sixteenth
    highamCh4KahanReturnedCounterexampleP5Format
    highamCh4KahanReturnedCounterexampleP5_rounding

/-- Corrected terminal corresponding to Higham (4.8) after the bare-model
strength discrepancy above: actual returned Kahan admits a componentwise
backward representation with leading constant 3 and an explicit
n-dependent second- and third-order majorant. -/
theorem highamCh4_equation48_modelStrengthCorrection_bareFPModel
    (fp : FPModel) (n : Nat) (v : Fin n -> Real)
    (hu64 : fp.u <= 1 / 64)
    (hm : (n : Real) * fp.u ^ 2 <= 1 / 16) :
    exists mu : Fin n -> Real,
      (forall i,
        |mu i| <=
          3 * fp.u + (14 + 13 * (n : Real)) * fp.u ^ 2 +
            (12 + 13 * (n : Real)) * fp.u ^ 3) /\
      fl_kahanSum fp n v =
        Finset.univ.sum (fun i : Fin n => v i * (1 + mu i)) :=
  fl_kahanSum_backward_error_source_bound_correctedReturnedMajorant
    fp n v hu64 hm
