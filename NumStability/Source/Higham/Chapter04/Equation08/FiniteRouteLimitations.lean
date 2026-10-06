import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Algorithms.Summation.Compensated.Kahan.Finite

namespace NumStability

/-!
# Higham equation (4.8): finite-route limitations

These source audits show that tail-order, Sterbenz, Ferguson, direct finite
subtraction, and finite-normal-range shortcuts are genuine additional
hypotheses. They do not follow from an arbitrary finite Kahan trace.
-/

/-- The tail-order FastTwoSum hypothesis is a genuine extra hypothesis, not a
consequence of the finite Kahan trace for arbitrary input order.

For the two-term input `[1, 2]`, the second correction-formula call has
`temp = 1` and `y = 2`, so `|y| < |temp|` is false. -/
theorem not_forall_finiteKahanTrace_tail_abs_order
    (fmt : FloatingPointFormat)
    (hone : fmt.finiteSystem (1 : ℝ))
    (htwo : fmt.finiteSystem (2 : ℝ)) :
    let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 2
    ¬ (∀ i : Fin 2, i.val ≠ 0 →
        |(finiteKahanTrace fmt v i).y| <
          |(finiteKahanTrace fmt v i).temp|) := by
  intro v horder
  let i : Fin 2 := ⟨1, by norm_num⟩
  have hv0 : fmt.finiteSystem (v ⟨0, by norm_num⟩) := by
    simpa [v] using hone
  have hprefix :
      finiteKahanPrefixState fmt v 1 (by norm_num : 1 ≤ 2) =
        { s := 1, e := 0 } := by
    simpa [v] using
      finiteKahanPrefixState_one_of_finiteSystem
        fmt v (by norm_num : 1 ≤ 2) hv0
  have hyround :
      fmt.finiteRoundToEvenOp BasicOp.add (2 : ℝ) 0 = 2 :=
    fmt.finiteRoundToEvenOp_add_zero_right_of_finiteSystem htwo
  have hprefix_e :
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e = 0 := by
    simp [i, hprefix]
  have htemp : (finiteKahanTrace fmt v i).temp = 1 := by
    simp [finiteKahanTrace, finiteKahanStepTrace, i, hprefix]
  have hy : (finiteKahanTrace fmt v i).y = 2 := by
    have hinput : v i = 2 := by
      simp [i, v]
    calc
      (finiteKahanTrace fmt v i).y =
          fmt.finiteRoundToEvenOp BasicOp.add (v i)
            (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add 2 0 := by
            rw [hinput, hprefix_e]
      _ = 2 := hyround
  have hbad := horder i (by norm_num : i.val ≠ 0)
  rw [hy, htemp] at hbad
  norm_num at hbad

/-- The tail-only inclusive Sterbenz route is also not a consequence of the
finite Kahan trace for arbitrary input order.

For the two-term input `[1, 2]` with exact representability of `1`, `2`, and
`3`, the second correction-subtraction pair has `temp = 1` and rounded
`s = 3`, so the inclusive Sterbenz condition `s / 2 <= temp` is false. -/
theorem not_forall_finiteKahanTrace_tail_sterbenzLe
    (fmt : FloatingPointFormat)
    (hone : fmt.finiteSystem (1 : ℝ))
    (htwo : fmt.finiteSystem (2 : ℝ))
    (hthree : fmt.finiteSystem (3 : ℝ)) :
    let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 2
    ¬ (∀ i : Fin 2, i.val ≠ 0 →
        fmt.sterbenzRatioConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s) := by
  intro v hsterbenz
  let i : Fin 2 := ⟨1, by norm_num⟩
  have hv0 : fmt.finiteSystem (v ⟨0, by norm_num⟩) := by
    simpa [v] using hone
  have hprefix :
      finiteKahanPrefixState fmt v 1 (by norm_num : 1 ≤ 2) =
        { s := 1, e := 0 } := by
    simpa [v] using
      finiteKahanPrefixState_one_of_finiteSystem
        fmt v (by norm_num : 1 ≤ 2) hv0
  have hprefix_e :
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e = 0 := by
    simp [i, hprefix]
  have htemp : (finiteKahanTrace fmt v i).temp = 1 := by
    simp [finiteKahanTrace, finiteKahanStepTrace, i, hprefix]
  have hy : (finiteKahanTrace fmt v i).y = 2 := by
    have hinput : v i = 2 := by
      simp [i, v]
    have hyround :
        fmt.finiteRoundToEvenOp BasicOp.add (2 : ℝ) 0 = 2 :=
      fmt.finiteRoundToEvenOp_add_zero_right_of_finiteSystem htwo
    calc
      (finiteKahanTrace fmt v i).y =
          fmt.finiteRoundToEvenOp BasicOp.add (v i)
            (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add 2 0 := by
            rw [hinput, hprefix_e]
      _ = 2 := hyround
  have hs : (finiteKahanTrace fmt v i).s = 3 := by
    have hthreeExact :
        fmt.finiteSystem (BasicOp.exact BasicOp.add (1 : ℝ) 2) := by
      convert hthree using 1
      norm_num [BasicOp.exact]
    have hsround :
        fmt.finiteRoundToEvenOp BasicOp.add (1 : ℝ) 2 = 3 := by
      have hround :=
        (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
          (op := BasicOp.add) (x := (1 : ℝ)) (y := (2 : ℝ)) hthreeExact)
      norm_num [BasicOp.exact] at hround
      exact hround
    calc
      (finiteKahanTrace fmt v i).s =
          fmt.finiteRoundToEvenOp BasicOp.add
            (finiteKahanTrace fmt v i).temp
            (finiteKahanTrace fmt v i).y := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add (1 : ℝ) 2 := by
            rw [htemp, hy]
      _ = 3 := hsround
  have hbad := hsterbenz i (by norm_num : i.val ≠ 0)
  rw [htemp, hs] at hbad
  norm_num [FloatingPointFormat.sterbenzRatioConditionLe] at hbad

/-- The tail-only inclusive Ferguson route is not a consequence of the finite
Kahan trace for arbitrary input order.

For the all-zero two-term input, the nonzero tail index still has `temp = 0`
and `s = 0`; Ferguson's condition requires normalized operands, so it fails. -/
theorem not_forall_finiteKahanTrace_tail_fergusonLe
    (fmt : FloatingPointFormat) :
    let v : Fin 2 → ℝ := fun _ => 0
    ¬ (∀ i : Fin 2, i.val ≠ 0 →
        fmt.fergusonExponentConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s) := by
  intro v hferguson
  let i : Fin 2 := ⟨1, by norm_num⟩
  have hv0 : fmt.finiteSystem (v ⟨0, by norm_num⟩) := by
    simp [v, fmt.finiteSystem_zero]
  have hprefix :
      finiteKahanPrefixState fmt v 1 (by norm_num : 1 ≤ 2) =
        { s := 0, e := 0 } := by
    simpa [v] using
      finiteKahanPrefixState_one_of_finiteSystem
        fmt v (by norm_num : 1 ≤ 2) hv0
  have htemp : (finiteKahanTrace fmt v i).temp = 0 := by
    simp [finiteKahanTrace, finiteKahanStepTrace, i, hprefix]
  have hs : (finiteKahanTrace fmt v i).s = 0 := by
    have hprefix_e :
        (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e = 0 := by
      simp [i, hprefix]
    have hinput : v i = 0 := by
      simp [v]
    have hy : (finiteKahanTrace fmt v i).y = 0 := by
      calc
        (finiteKahanTrace fmt v i).y =
            fmt.finiteRoundToEvenOp BasicOp.add (v i)
              (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e := by
              rfl
        _ = fmt.finiteRoundToEvenOp BasicOp.add 0 0 := by
              rw [hinput, hprefix_e]
        _ = 0 := fmt.finiteRoundToEvenOp_add_zero_of_finiteSystem fmt.finiteSystem_zero
    calc
      (finiteKahanTrace fmt v i).s =
          fmt.finiteRoundToEvenOp BasicOp.add
            (finiteKahanTrace fmt v i).temp
            (finiteKahanTrace fmt v i).y := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add 0 0 := by
            rw [htemp, hy]
      _ = 0 := fmt.finiteRoundToEvenOp_add_zero_of_finiteSystem fmt.finiteSystem_zero
  have hbad := hferguson i (by norm_num : i.val ≠ 0)
  have hleft : fmt.normalizedSystem (finiteKahanTrace fmt v i).temp :=
    fmt.fergusonExponentConditionLe_left_normalized hbad
  rw [htemp] at hleft
  have hzeroLower : fmt.betaR ^ (fmt.emin - 1) ≤ (0 : ℝ) := by
    simpa using fmt.normalizedSystem_abs_lower_bound hleft
  exact (not_lt_of_ge hzeroLower) (fmt.betaR_zpow_pos (fmt.emin - 1))

/-- Direct tail finite representability of `temp - s` is not a consequence of
the finite Kahan trace for arbitrary input order.

In the two-exponent one-digit decimal audit format, the input `[1, 90]` has tail
`temp = 1` and saturated rounded sum `s = 90`, so `temp - s = -89`, which is not
finite representable. -/
theorem not_forall_finiteKahanTrace_tail_direct_sub_finite :
    let fmt := FloatingPointFormat.decimalSingleDigitTwoExponentFormat
    let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 90
    ¬ (∀ i : Fin 2, i.val ≠ 0 →
        fmt.finiteSystem
          ((finiteKahanTrace fmt v i).temp -
            (finiteKahanTrace fmt v i).s)) := by
  intro fmt v hfinite
  let i : Fin 2 := ⟨1, by norm_num⟩
  have hv0 : fmt.finiteSystem (v ⟨0, by norm_num⟩) := by
    simpa [v, fmt] using
      FloatingPointFormat.decimalSingleDigitTwoExponentFormat_finiteSystem_one
  have hprefix :
      finiteKahanPrefixState fmt v 1 (by norm_num : 1 ≤ 2) =
        { s := 1, e := 0 } := by
    simpa [v, fmt] using
      finiteKahanPrefixState_one_of_finiteSystem
        fmt v (by norm_num : 1 ≤ 2) hv0
  have hprefix_e :
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e = 0 := by
    simp [i, hprefix]
  have htemp : (finiteKahanTrace fmt v i).temp = 1 := by
    simp [finiteKahanTrace, finiteKahanStepTrace, i, hprefix]
  have hy : (finiteKahanTrace fmt v i).y = 90 := by
    have hinput : v i = 90 := by
      simp [i, v]
    have hround :
        fmt.finiteRoundToEvenOp BasicOp.add (90 : ℝ) 0 = 90 := by
      simpa [fmt] using
        fmt.finiteRoundToEvenOp_add_zero_right_of_finiteSystem
          FloatingPointFormat.decimalSingleDigitTwoExponentFormat_finiteSystem_ninety
    calc
      (finiteKahanTrace fmt v i).y =
          fmt.finiteRoundToEvenOp BasicOp.add (v i)
            (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add 90 0 := by
            rw [hinput, hprefix_e]
      _ = 90 := hround
  have hs : (finiteKahanTrace fmt v i).s = 90 := by
    calc
      (finiteKahanTrace fmt v i).s =
          fmt.finiteRoundToEvenOp BasicOp.add
            (finiteKahanTrace fmt v i).temp
            (finiteKahanTrace fmt v i).y := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add (1 : ℝ) 90 := by
            rw [htemp, hy]
      _ = 90 := by
            simpa [fmt] using
              FloatingPointFormat.decimalSingleDigitTwoExponentFormat_round_add_one_ninety
  have hbad := hfinite i (by norm_num : i.val ≠ 0)
  rw [htemp, hs] at hbad
  norm_num at hbad
  have hpos :
      FloatingPointFormat.decimalSingleDigitTwoExponentFormat.finiteSystem (89 : ℝ) := by
    simpa [fmt] using
      FloatingPointFormat.decimalSingleDigitTwoExponentFormat.finiteSystem_neg hbad
  exact FloatingPointFormat.decimalSingleDigitTwoExponentFormat_not_finiteSystem_eightynine hpos

/-- Concrete value of the tail correction subtraction in the direct finite
subtraction route counterexample. -/
theorem finiteKahanTrace_decimal_tail_direct_sub_eq_neg_eightynine :
    let fmt := FloatingPointFormat.decimalSingleDigitTwoExponentFormat
    let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 90
    let i : Fin 2 := ⟨1, by norm_num⟩
    (finiteKahanTrace fmt v i).temp -
        (finiteKahanTrace fmt v i).s = -89 := by
  dsimp
  let fmt := FloatingPointFormat.decimalSingleDigitTwoExponentFormat
  let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 90
  let i : Fin 2 := ⟨1, by norm_num⟩
  have hv0 : fmt.finiteSystem (v ⟨0, by norm_num⟩) := by
    simpa [v, fmt] using
      FloatingPointFormat.decimalSingleDigitTwoExponentFormat_finiteSystem_one
  have hprefix :
      finiteKahanPrefixState fmt v 1 (by norm_num : 1 ≤ 2) =
        { s := 1, e := 0 } := by
    simpa [v, fmt] using
      finiteKahanPrefixState_one_of_finiteSystem
        fmt v (by norm_num : 1 ≤ 2) hv0
  have hprefix_e :
      (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e = 0 := by
    simp [i, hprefix]
  have htemp : (finiteKahanTrace fmt v i).temp = 1 := by
    simp [finiteKahanTrace, finiteKahanStepTrace, i, hprefix]
  have hy : (finiteKahanTrace fmt v i).y = 90 := by
    have hinput : v i = 90 := by
      simp [i, v]
    have hround :
        fmt.finiteRoundToEvenOp BasicOp.add (90 : ℝ) 0 = 90 := by
      simpa [fmt] using
        fmt.finiteRoundToEvenOp_add_zero_right_of_finiteSystem
          FloatingPointFormat.decimalSingleDigitTwoExponentFormat_finiteSystem_ninety
    calc
      (finiteKahanTrace fmt v i).y =
          fmt.finiteRoundToEvenOp BasicOp.add (v i)
            (finiteKahanPrefixState fmt v i.val (Nat.le_of_lt i.isLt)).e := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add 90 0 := by
            rw [hinput, hprefix_e]
      _ = 90 := hround
  have hs : (finiteKahanTrace fmt v i).s = 90 := by
    calc
      (finiteKahanTrace fmt v i).s =
          fmt.finiteRoundToEvenOp BasicOp.add
            (finiteKahanTrace fmt v i).temp
            (finiteKahanTrace fmt v i).y := by
            rfl
      _ = fmt.finiteRoundToEvenOp BasicOp.add (1 : ℝ) 90 := by
            rw [htemp, hy]
      _ = 90 := by
            simpa [fmt] using
              FloatingPointFormat.decimalSingleDigitTwoExponentFormat_round_add_one_ninety
  have hsub :
      (finiteKahanTrace fmt v i).temp -
          (finiteKahanTrace fmt v i).s = -89 := by
    rw [htemp, hs]
    norm_num
  simpa [fmt, v, i] using hsub

/-- The source-facing finite-normal-range shortcut does not repair the failed
direct finite-subtraction route for arbitrary Kahan input order.

In the same two-exponent one-digit decimal audit trace used by
`not_forall_finiteKahanTrace_tail_direct_sub_finite`, the tail correction
subtraction is `-89`.  Its magnitude lies in the finite normal range, but the
value is not representable in the finite system.  Thus a no-overflow/range
hypothesis alone is weaker than the finite/coherence hypothesis needed by
`fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite`. -/
theorem finiteKahanTrace_tail_direct_sub_finiteNormalRange_not_finiteSystem_counterexample :
    let fmt := FloatingPointFormat.decimalSingleDigitTwoExponentFormat
    let v : Fin 2 → ℝ := fun i => if i.val = 0 then 1 else 90
    (∀ i : Fin 2, i.val ≠ 0 →
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v i).temp -
            (finiteKahanTrace fmt v i).s)) ∧
      ¬ (∀ i : Fin 2, i.val ≠ 0 →
        fmt.finiteSystem
          ((finiteKahanTrace fmt v i).temp -
            (finiteKahanTrace fmt v i).s)) := by
  dsimp
  constructor
  · intro i hi
    fin_cases i
    · exact False.elim (hi rfl)
    · have hsub := finiteKahanTrace_decimal_tail_direct_sub_eq_neg_eightynine
      dsimp at hsub
      have hnormal :
          FloatingPointFormat.decimalSingleDigitTwoExponentFormat.finiteNormalRange
            (-89 : ℝ) := by
        rw [FloatingPointFormat.finiteNormalRange]
        have hmin :
            FloatingPointFormat.decimalSingleDigitTwoExponentFormat.minNormalMagnitude =
              (1 : ℝ) := by
          norm_num [FloatingPointFormat.minNormalMagnitude,
            FloatingPointFormat.decimalSingleDigitTwoExponentFormat,
            FloatingPointFormat.betaR]
        have hmax :
            FloatingPointFormat.decimalSingleDigitTwoExponentFormat.maxFiniteMagnitude =
              (90 : ℝ) := by
          norm_num [FloatingPointFormat.maxFiniteMagnitude,
            FloatingPointFormat.decimalSingleDigitTwoExponentFormat,
            FloatingPointFormat.betaR, zpow_neg]
          rfl
        constructor
        · rw [hmin]
          norm_num
        · rw [hmax]
          norm_num
      have htarget :
          FloatingPointFormat.decimalSingleDigitTwoExponentFormat.finiteNormalRange
            ((finiteKahanTrace
                FloatingPointFormat.decimalSingleDigitTwoExponentFormat
                (fun i : Fin 2 => if i.val = 0 then 1 else 90)
                (⟨1, by norm_num⟩ : Fin 2)).temp -
              (finiteKahanTrace
                FloatingPointFormat.decimalSingleDigitTwoExponentFormat
                (fun i : Fin 2 => if i.val = 0 then 1 else 90)
                (⟨1, by norm_num⟩ : Fin 2)).s) := by
        have hsub' :
            (finiteKahanTrace
                  FloatingPointFormat.decimalSingleDigitTwoExponentFormat
                  (fun i : Fin 2 => if i.val = 0 then 1 else 90)
                  (⟨1, by norm_num⟩ : Fin 2)).temp -
                (finiteKahanTrace
                  FloatingPointFormat.decimalSingleDigitTwoExponentFormat
                  (fun i : Fin 2 => if i.val = 0 then 1 else 90)
                  (⟨1, by norm_num⟩ : Fin 2)).s =
              -89 := by
          simpa using hsub
        rw [hsub']
        exact hnormal
      simpa using htarget
  · simpa using not_forall_finiteKahanTrace_tail_direct_sub_finite
