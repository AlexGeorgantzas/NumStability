-- Algorithms/Summation/Compensated/Kahan/LocalCoefficients.lean

import NumStability.FloatingPoint.Model
import NumStability.Algorithms.Summation.Compensated.Kahan.Core

namespace NumStability

/-!
# Kahan compensated summation: local roundoff coefficients

This module packages the one-step standard-model witnesses and the local
coefficient identities and bounds used by higher Kahan analysis layers.  It
also supplies indexed projections and the explicit exact-subtraction witness
family, without importing finite-format or source-facing modules.
-/

/-- Standard-model roundoff witnesses for one Algorithm 4.2 Kahan step.

The four deltas expose the source proof's primitive operations:
`y = fl(x + e)`, `s = fl(temp + y)`, the subtraction `fl(temp - s)`,
and the final correction add `e = fl(fl(temp - s) + y)`. -/
structure KahanStepDeltaWitness (fp : FPModel) (x : ℝ) (state : KahanState) where
  deltaY : ℝ
  deltaS : ℝ
  deltaSub : ℝ
  deltaE : ℝ
  h_deltaY : |deltaY| ≤ fp.u
  h_deltaS : |deltaS| ≤ fp.u
  h_deltaSub : |deltaSub| ≤ fp.u
  h_deltaE : |deltaE| ≤ fp.u
  hy :
    (kahanStepTrace fp x state).y =
      (x + state.e) * (1 + deltaY)
  hs :
    (kahanStepTrace fp x state).s =
      ((kahanStepTrace fp x state).temp + (kahanStepTrace fp x state).y) *
        (1 + deltaS)
  hsub :
    fp.fl_sub (kahanStepTrace fp x state).temp
        (kahanStepTrace fp x state).s =
      ((kahanStepTrace fp x state).temp - (kahanStepTrace fp x state).s) *
        (1 + deltaSub)
  he :
    (kahanStepTrace fp x state).e =
      (fp.fl_sub (kahanStepTrace fp x state).temp
          (kahanStepTrace fp x state).s +
        (kahanStepTrace fp x state).y) *
        (1 + deltaE)

/-- Every abstract `FPModel` Kahan step admits the standard-model roundoff
delta witnesses used by the Knuth/Goldberg coefficient-recursion proof. -/
theorem exists_kahanStepTrace_deltaWitness
    (fp : FPModel) (x : ℝ) (state : KahanState) :
    Nonempty (KahanStepDeltaWitness fp x state) := by
  rcases fp.model_basicOp BasicOp.add x state.e (by intro h; cases h) with
    ⟨deltaY, h_deltaY, hy⟩
  rcases fp.model_basicOp BasicOp.add
      (kahanStepTrace fp x state).temp
      (kahanStepTrace fp x state).y
      (by intro h; cases h) with
    ⟨deltaS, h_deltaS, hs⟩
  rcases fp.model_basicOp BasicOp.sub
      (kahanStepTrace fp x state).temp
      (kahanStepTrace fp x state).s
      (by intro h; cases h) with
    ⟨deltaSub, h_deltaSub, hsub⟩
  rcases fp.model_basicOp BasicOp.add
      (fp.fl_sub (kahanStepTrace fp x state).temp
        (kahanStepTrace fp x state).s)
      (kahanStepTrace fp x state).y
      (by intro h; cases h) with
    ⟨deltaE, h_deltaE, he⟩
  refine
    ⟨{ deltaY := deltaY
       deltaS := deltaS
       deltaSub := deltaSub
       deltaE := deltaE
       h_deltaY := h_deltaY
       h_deltaS := h_deltaS
       h_deltaSub := h_deltaSub
       h_deltaE := h_deltaE
       hy := ?_
       hs := ?_
       hsub := ?_
       he := ?_ }⟩
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using hy
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using hs
  · simpa [FPModel.round, BasicOp.exact] using hsub
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using he

/-- A convenient chosen bundle of the per-operation Kahan roundoff witnesses. -/
noncomputable def kahanStepTrace_deltaWitness
    (fp : FPModel) (x : ℝ) (state : KahanState) :
    KahanStepDeltaWitness fp x state :=
  Classical.choice (exists_kahanStepTrace_deltaWitness fp x state)

/-- If the displayed correction subtraction in one Algorithm 4.2 step is
exact, choose the standard-model witness bundle with zero subtraction delta.

This is the one-step construction needed by the witness-family route for
Higham equation (4.8): exact subtraction is represented by the concrete
choice `deltaSub = 0`, while the other three operations still use the ordinary
standard-model witnesses. -/
theorem exists_kahanStepTrace_deltaWitness_of_exact_sub
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (hsubExact :
      fp.fl_sub (kahanStepTrace fp x state).temp
          (kahanStepTrace fp x state).s =
        (kahanStepTrace fp x state).temp -
          (kahanStepTrace fp x state).s) :
    ∃ w : KahanStepDeltaWitness fp x state, w.deltaSub = 0 := by
  rcases fp.model_basicOp BasicOp.add x state.e (by intro h; cases h) with
    ⟨deltaY, h_deltaY, hy⟩
  rcases fp.model_basicOp BasicOp.add
      (kahanStepTrace fp x state).temp
      (kahanStepTrace fp x state).y
      (by intro h; cases h) with
    ⟨deltaS, h_deltaS, hs⟩
  rcases fp.model_basicOp BasicOp.add
      (fp.fl_sub (kahanStepTrace fp x state).temp
        (kahanStepTrace fp x state).s)
      (kahanStepTrace fp x state).y
      (by intro h; cases h) with
    ⟨deltaE, h_deltaE, he⟩
  refine
    ⟨{ deltaY := deltaY
       deltaS := deltaS
       deltaSub := 0
       deltaE := deltaE
       h_deltaY := h_deltaY
       h_deltaS := h_deltaS
       h_deltaSub := by simpa using fp.u_nonneg
       h_deltaE := h_deltaE
       hy := ?_
       hs := ?_
       hsub := ?_
       he := ?_ }, rfl⟩
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using hy
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using hs
  · simp [hsubExact]
  · simpa [kahanStepTrace, FPModel.round, BasicOp.exact] using he

/-- A chosen one-step Kahan witness with zero subtraction delta, under an
explicit exact-subtraction hypothesis. -/
noncomputable def kahanStepTrace_deltaWitnessOfExactSub
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (hsubExact :
      fp.fl_sub (kahanStepTrace fp x state).temp
          (kahanStepTrace fp x state).s =
        (kahanStepTrace fp x state).temp -
          (kahanStepTrace fp x state).s) :
    KahanStepDeltaWitness fp x state :=
  Classical.choose
    (exists_kahanStepTrace_deltaWitness_of_exact_sub
      fp x state hsubExact)

/-- The exact-subtraction witness selected by
`kahanStepTrace_deltaWitnessOfExactSub` has zero subtraction delta. -/
theorem kahanStepTrace_deltaWitnessOfExactSub_deltaSub
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (hsubExact :
      fp.fl_sub (kahanStepTrace fp x state).temp
          (kahanStepTrace fp x state).s =
        (kahanStepTrace fp x state).temp -
          (kahanStepTrace fp x state).s) :
    (kahanStepTrace_deltaWitnessOfExactSub fp x state hsubExact).deltaSub =
      0 :=
  Classical.choose_spec
    (exists_kahanStepTrace_deltaWitness_of_exact_sub
      fp x state hsubExact)

/-- Expanded one-step recurrence for the updated Kahan sum after substituting
the standard-model delta for the `y = fl(x + e)` operation. -/
theorem kahanStepDeltaWitness_s_expanded
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).s =
      (state.s + (x + state.e) * (1 + w.deltaY)) *
        (1 + w.deltaS) := by
  rw [w.hs, w.hy]
  simp [kahanStepTrace]

/-- Expanded one-step recurrence for the Kahan correction after substituting
the standard-model delta for the displayed `temp - s` subtraction. -/
theorem kahanStepDeltaWitness_e_expanded
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).e =
      (((kahanStepTrace fp x state).temp -
            (kahanStepTrace fp x state).s) *
          (1 + w.deltaSub) +
        (kahanStepTrace fp x state).y) *
        (1 + w.deltaE) := by
  rw [w.he, w.hsub]

/-- Fully expanded one-step recurrence for the Kahan correction, with the
temporary sum and `y` trace variables replaced by the previous state, input, and
standard-model deltas. -/
theorem kahanStepDeltaWitness_e_fully_expanded
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    let y0 := (x + state.e) * (1 + w.deltaY)
    let s0 := (state.s + y0) * (1 + w.deltaS)
    (kahanStepTrace fp x state).e =
      ((state.s - s0) * (1 + w.deltaSub) + y0) *
        (1 + w.deltaE) := by
  dsimp
  rw [kahanStepDeltaWitness_e_expanded fp x state w]
  rw [kahanStepDeltaWitness_s_expanded fp x state w, w.hy]
  simp [kahanStepTrace]

/-- Fully expanded one-step recurrence for the compensated total `s + e`, in
terms of only the previous Kahan state, the new input, and the four
standard-model deltas. -/
theorem kahanStepDeltaWitness_total_fully_expanded
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    let y0 := (x + state.e) * (1 + w.deltaY)
    let s0 := (state.s + y0) * (1 + w.deltaS)
    (kahanStepTrace fp x state).s + (kahanStepTrace fp x state).e =
      s0 + ((state.s - s0) * (1 + w.deltaSub) + y0) *
        (1 + w.deltaE) := by
  dsimp
  rw [kahanStepDeltaWitness_s_expanded fp x state w]
  rw [kahanStepDeltaWitness_e_fully_expanded fp x state w]

/-- Coefficient multiplying the previous Kahan running sum in the fully
expanded compensated-total recurrence.  It is `1 + O(u^2)` under the standard
delta bounds, which is the cancellation exploited in the Knuth/Goldberg
coefficient recursion. -/
def kahanTotalStateCoeff (deltaS deltaSub deltaE : ℝ) : ℝ :=
  (1 + deltaSub) * (1 + deltaE) +
    (1 + deltaS) * (1 - (1 + deltaSub) * (1 + deltaE))

/-- Coefficient multiplying the current exact input-plus-correction term in the
fully expanded compensated-total recurrence. -/
def kahanTotalInputCoeff
    (deltaY deltaS deltaSub deltaE : ℝ) : ℝ :=
  (1 + deltaY) *
    ((1 + deltaS) * (1 - (1 + deltaSub) * (1 + deltaE)) +
      (1 + deltaE))

/-- Residual coefficient on the retained correction when the compensated-total
recurrence is rewritten in terms of the previous compensated total `s+e`
instead of the previous stored running sum `s`.

This term is zero in exact arithmetic.  It is the precise local obstruction
that remains before the ordinary Knuth/Goldberg `mu_i` recursion can be
closed for the returned Kahan sum. -/
def kahanTotalResidualCoeff
    (deltaY deltaS deltaSub deltaE : ℝ) : ℝ :=
  kahanTotalInputCoeff deltaY deltaS deltaSub deltaE -
    kahanTotalStateCoeff deltaS deltaSub deltaE

/-- Coefficient multiplying the previous stored running sum in the fully
expanded correction recurrence for `e`. -/
def kahanCorrectionStateCoeff (deltaS deltaSub deltaE : ℝ) : ℝ :=
  -deltaS * (1 + deltaSub) * (1 + deltaE)

/-- Coefficient multiplying the current exact input-plus-correction term in
the fully expanded correction recurrence for `e`. -/
def kahanCorrectionInputCoeff
    (deltaY deltaS deltaSub deltaE : ℝ) : ℝ :=
  -(1 + deltaY) * (deltaSub + deltaS * (1 + deltaSub)) *
    (1 + deltaE)

/-- Coefficient multiplying the previous stored sum in the directly expanded
stored-sum recurrence.

Unlike the compensated-total old-state coefficient, this coefficient has a
first-order term.  It is recorded separately because the final Knuth/Goldberg
route for the returned `s` must preserve cancellation with the retained
correction rather than bound the final correction as an independent residual. -/
def kahanStoredSumStateCoeff (deltaS : ℝ) : ℝ :=
  1 + deltaS

/-- Coefficient multiplying both the current input and the previous retained
correction in the directly expanded stored-sum recurrence. -/
def kahanStoredSumInputCoeff (deltaY deltaS : ℝ) : ℝ :=
  (1 + deltaY) * (1 + deltaS)

/-- The direct stored-sum current-input coefficient differs from the direct
old-stored-sum coefficient by the first input-roundoff factor. -/
theorem kahanStoredSumInputCoeff_sub_stateCoeff_eq
    (deltaY deltaS : ℝ) :
    kahanStoredSumInputCoeff deltaY deltaS -
      kahanStoredSumStateCoeff deltaS = deltaY * (1 + deltaS) := by
  dsimp [kahanStoredSumInputCoeff, kahanStoredSumStateCoeff]
  ring

/-- One-step coefficient form of the fully expanded Kahan correction
recurrence. -/
theorem kahanStepDeltaWitness_e_coefficients
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).e =
      state.s * kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE +
        (x + state.e) *
          kahanCorrectionInputCoeff
            w.deltaY w.deltaS w.deltaSub w.deltaE := by
  rw [kahanStepDeltaWitness_e_fully_expanded fp x state w]
  dsimp [kahanCorrectionStateCoeff, kahanCorrectionInputCoeff]
  ring

/-- One-step coefficient form of the directly expanded Kahan stored-sum
recurrence.

This is the first cancellation-preserving returned-sum surface for the
ordinary Kahan bound: the previous retained correction is still explicit and
shares the same local coefficient as the current input. -/
theorem kahanStepDeltaWitness_s_coefficients
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).s =
      state.s * kahanStoredSumStateCoeff w.deltaS +
        x * kahanStoredSumInputCoeff w.deltaY w.deltaS +
        state.e * kahanStoredSumInputCoeff w.deltaY w.deltaS := by
  rw [kahanStepDeltaWitness_s_expanded fp x state w]
  dsimp [kahanStoredSumStateCoeff, kahanStoredSumInputCoeff]
  ring

/-- Exact first/second-order expansion of the direct stored-sum current-input
coefficient. -/
theorem kahanStoredSumInputCoeff_sub_one_eq
    (deltaY deltaS : ℝ) :
    kahanStoredSumInputCoeff deltaY deltaS - 1 =
      deltaY + deltaS + deltaY * deltaS := by
  dsimp [kahanStoredSumInputCoeff]
  ring

/-- Local radius for the old stored-sum coefficient in the direct stored-sum
recurrence. -/
theorem kahanStoredSumStateCoeff_abs_sub_one_le
    {deltaS u : ℝ} (hS : |deltaS| ≤ u) :
    |kahanStoredSumStateCoeff deltaS - 1| ≤ u := by
  simpa [kahanStoredSumStateCoeff] using hS

/-- Local radius for the current-input coefficient in the direct stored-sum
recurrence. -/
theorem kahanStoredSumInputCoeff_abs_sub_one_le_two_u_plus_u_sq
    {deltaY deltaS u : ℝ} (hu : 0 ≤ u)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) :
    |kahanStoredSumInputCoeff deltaY deltaS - 1| ≤
      2 * u + u ^ 2 := by
  have hYS : |deltaY * deltaS| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hY hS (abs_nonneg _) hu
  rw [kahanStoredSumInputCoeff_sub_one_eq]
  calc
    |deltaY + deltaS + deltaY * deltaS|
        ≤ |deltaY| + |deltaS| + |deltaY * deltaS| := by
          calc
            |deltaY + deltaS + deltaY * deltaS|
                = |(deltaY + deltaS) + deltaY * deltaS| := by ring
            _ ≤ |deltaY + deltaS| + |deltaY * deltaS| := abs_add_le _ _
            _ ≤ |deltaY| + |deltaS| + |deltaY * deltaS| := by
              nlinarith [abs_add_le deltaY deltaS]
    _ ≤ u + u + u * u := by
      nlinarith [hY, hS, hYS]
    _ = 2 * u + u ^ 2 := by ring

/-- Local radius for the gap between the direct stored-sum input and state
coefficients.  This is the coefficient multiplying the retained correction
when the returned stored sum is propagated in paired `(s+e,e)` coordinates. -/
theorem kahanStoredSumInputCoeff_sub_stateCoeff_abs_le_u_mul_one_add_u
    {deltaY deltaS u : ℝ} (hu : 0 ≤ u)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) :
    |kahanStoredSumInputCoeff deltaY deltaS -
        kahanStoredSumStateCoeff deltaS| ≤
      u * (1 + u) := by
  rw [kahanStoredSumInputCoeff_sub_stateCoeff_eq, abs_mul]
  have hone : |1 + deltaS| ≤ 1 + u := by
    calc
      |1 + deltaS| = |deltaS + 1| := by ring_nf
      _ ≤ |deltaS| + |(1 : ℝ)| := abs_add_le deltaS 1
      _ ≤ u + 1 := by
        exact add_le_add hS (by norm_num : |(1 : ℝ)| ≤ 1)
      _ = 1 + u := by ring
  exact mul_le_mul hY hone (abs_nonneg _) (by nlinarith [hu])

/-- Exact second-order expansion of the previous-running-sum coefficient in
the Kahan compensated-total recurrence. -/
theorem kahanTotalStateCoeff_eq_one_sub_second_order
    (deltaS deltaSub deltaE : ℝ) :
    kahanTotalStateCoeff deltaS deltaSub deltaE =
      1 - deltaS * deltaSub - deltaS * deltaE -
        deltaS * deltaSub * deltaE := by
  dsimp [kahanTotalStateCoeff]
  ring

/-- Exact first/second-order expansion of the current-input coefficient in the
Kahan compensated-total recurrence.  The first-order part is
`deltaY - deltaSub`, which is the local algebra behind the `2*u + O(u^2)`
coefficient radius. -/
theorem kahanTotalInputCoeff_eq_first_second_order
    (deltaY deltaS deltaSub deltaE : ℝ) :
    kahanTotalInputCoeff deltaY deltaS deltaSub deltaE =
      1 + deltaY - deltaSub -
        deltaSub * deltaE - deltaS * deltaSub - deltaS * deltaE -
        deltaS * deltaSub * deltaE -
        deltaY * deltaSub - deltaY * deltaSub * deltaE -
        deltaY * deltaS * deltaSub - deltaY * deltaS * deltaE -
        deltaY * deltaS * deltaSub * deltaE := by
  dsimp [kahanTotalInputCoeff]
  ring

/-- Factorized error form of the current-input coefficient. -/
theorem kahanTotalInputCoeff_sub_one_eq
    (deltaY deltaS deltaSub deltaE : ℝ) :
    kahanTotalInputCoeff deltaY deltaS deltaSub deltaE - 1 =
      deltaY -
        (1 + deltaY) *
          (deltaSub + deltaSub * deltaE + deltaS * deltaSub +
            deltaS * deltaE + deltaS * deltaSub * deltaE) := by
  dsimp [kahanTotalInputCoeff]
  ring

/-- The previous-running-sum coefficient differs from `1` only by
second-order terms in the Kahan step deltas. -/
theorem kahanTotalStateCoeff_abs_sub_one_le
    {deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u)
    (hS : |deltaS| ≤ u) (hSub : |deltaSub| ≤ u)
    (hE : |deltaE| ≤ u) :
    |kahanTotalStateCoeff deltaS deltaSub deltaE - 1| ≤
      2 * u ^ 2 + u ^ 3 := by
  have hSSub : |deltaS * deltaSub| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hSub (abs_nonneg _) hu
  have hSE : |deltaS * deltaE| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hE (abs_nonneg _) hu
  have hSSubE : |deltaS * deltaSub * deltaE| ≤ u * u * u := by
    rw [abs_mul, abs_mul]
    have hprod : |deltaS| * |deltaSub| ≤ u * u :=
      mul_le_mul hS hSub (abs_nonneg _) hu
    exact mul_le_mul hprod hE (abs_nonneg _)
      (mul_nonneg hu hu)
  have hexp :
      kahanTotalStateCoeff deltaS deltaSub deltaE - 1 =
        -(deltaS * deltaSub + deltaS * deltaE +
          deltaS * deltaSub * deltaE) := by
    rw [kahanTotalStateCoeff_eq_one_sub_second_order]
    ring
  rw [hexp, abs_neg]
  calc
    |deltaS * deltaSub + deltaS * deltaE +
        deltaS * deltaSub * deltaE|
        ≤ |deltaS * deltaSub| + |deltaS * deltaE| +
            |deltaS * deltaSub * deltaE| := by
          calc
            |deltaS * deltaSub + deltaS * deltaE +
                deltaS * deltaSub * deltaE|
                = |(deltaS * deltaSub + deltaS * deltaE) +
                    deltaS * deltaSub * deltaE| := by ring
            _ ≤ |deltaS * deltaSub + deltaS * deltaE| +
                  |deltaS * deltaSub * deltaE| := abs_add_le _ _
            _ ≤ |deltaS * deltaSub| + |deltaS * deltaE| +
                  |deltaS * deltaSub * deltaE| := by
                nlinarith [abs_add_le (deltaS * deltaSub) (deltaS * deltaE)]
    _ ≤ u * u + u * u + u * u * u := by
          nlinarith [hSSub, hSE, hSSubE]
    _ = 2 * u ^ 2 + u ^ 3 := by ring

/-- The current-input coefficient has local radius
`2*u + 4*u^2 + 4*u^3 + u^4` under the four standard-model delta bounds. -/
theorem kahanTotalInputCoeff_abs_sub_one_le
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalInputCoeff deltaY deltaS deltaSub deltaE - 1| ≤
      2 * u + 4 * u ^ 2 + 4 * u ^ 3 + u ^ 4 := by
  let q := deltaSub + deltaSub * deltaE + deltaS * deltaSub +
    deltaS * deltaE + deltaS * deltaSub * deltaE
  have hSubE : |deltaSub * deltaE| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hSub hE (abs_nonneg _) hu
  have hSSub : |deltaS * deltaSub| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hSub (abs_nonneg _) hu
  have hSE : |deltaS * deltaE| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hE (abs_nonneg _) hu
  have hSSubE : |deltaS * deltaSub * deltaE| ≤ u * u * u := by
    rw [abs_mul, abs_mul]
    have hprod : |deltaS| * |deltaSub| ≤ u * u :=
      mul_le_mul hS hSub (abs_nonneg _) hu
    exact mul_le_mul hprod hE (abs_nonneg _)
      (mul_nonneg hu hu)
  have hq : |q| ≤ u + 3 * u ^ 2 + u ^ 3 := by
    have htri :
        |q| ≤ |deltaSub| + |deltaSub * deltaE| +
            |deltaS * deltaSub| + |deltaS * deltaE| +
            |deltaS * deltaSub * deltaE| := by
      dsimp [q]
      calc
        |deltaSub + deltaSub * deltaE + deltaS * deltaSub +
            deltaS * deltaE + deltaS * deltaSub * deltaE|
            = |(((deltaSub + deltaSub * deltaE) +
                  deltaS * deltaSub) + deltaS * deltaE) +
                  deltaS * deltaSub * deltaE| := by ring
        _ ≤ |((deltaSub + deltaSub * deltaE) +
                deltaS * deltaSub) + deltaS * deltaE| +
              |deltaS * deltaSub * deltaE| := abs_add_le _ _
        _ ≤ |(deltaSub + deltaSub * deltaE) + deltaS * deltaSub| +
              |deltaS * deltaE| + |deltaS * deltaSub * deltaE| := by
            nlinarith [abs_add_le ((deltaSub + deltaSub * deltaE) +
              deltaS * deltaSub) (deltaS * deltaE)]
        _ ≤ |deltaSub + deltaSub * deltaE| +
              |deltaS * deltaSub| + |deltaS * deltaE| +
              |deltaS * deltaSub * deltaE| := by
            nlinarith [abs_add_le (deltaSub + deltaSub * deltaE)
              (deltaS * deltaSub)]
        _ ≤ |deltaSub| + |deltaSub * deltaE| +
              |deltaS * deltaSub| + |deltaS * deltaE| +
              |deltaS * deltaSub * deltaE| := by
            nlinarith [abs_add_le deltaSub (deltaSub * deltaE)]
    calc
      |q| ≤ |deltaSub| + |deltaSub * deltaE| +
          |deltaS * deltaSub| + |deltaS * deltaE| +
          |deltaS * deltaSub * deltaE| := htri
      _ ≤ u + u * u + u * u + u * u + u * u * u := by
          nlinarith [hSub, hSubE, hSSub, hSE, hSSubE]
      _ = u + 3 * u ^ 2 + u ^ 3 := by ring
  have hone :
      |1 + deltaY| ≤ 1 + u := by
    calc
      |1 + deltaY| ≤ |(1 : ℝ)| + |deltaY| := abs_add_le _ _
      _ = 1 + |deltaY| := by norm_num
      _ ≤ 1 + u := by nlinarith [hY]
  have hprod :
      |(1 + deltaY) * q| ≤ (1 + u) * (u + 3 * u ^ 2 + u ^ 3) := by
    rw [abs_mul]
    exact mul_le_mul hone hq (abs_nonneg _) (by nlinarith [hu])
  have hexp :
      kahanTotalInputCoeff deltaY deltaS deltaSub deltaE - 1 =
        deltaY - (1 + deltaY) * q := by
    dsimp [q]
    exact kahanTotalInputCoeff_sub_one_eq deltaY deltaS deltaSub deltaE
  rw [hexp]
  calc
    |deltaY - (1 + deltaY) * q|
        ≤ |deltaY| + |(1 + deltaY) * q| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le deltaY (-((1 + deltaY) * q))
    _ ≤ u + (1 + u) * (u + 3 * u ^ 2 + u ^ 3) := by
          nlinarith [hY, hprod]
    _ = 2 * u + 4 * u ^ 2 + 4 * u ^ 3 + u ^ 4 := by ring

/-- Readable small-`u` version of the old-state coefficient bound. -/
theorem kahanTotalStateCoeff_abs_sub_one_le_three_u_sq
    {deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hS : |deltaS| ≤ u) (hSub : |deltaSub| ≤ u)
    (hE : |deltaE| ≤ u) :
    |kahanTotalStateCoeff deltaS deltaSub deltaE - 1| ≤
      3 * u ^ 2 := by
  have hbase :=
    kahanTotalStateCoeff_abs_sub_one_le
      (deltaS := deltaS) (deltaSub := deltaSub) (deltaE := deltaE)
      (u := u) hu hS hSub hE
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  nlinarith

/-- Readable small-`u` version of the current-input coefficient bound. -/
theorem kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalInputCoeff deltaY deltaS deltaSub deltaE - 1| ≤
      2 * u + 9 * u ^ 2 := by
  have hbase :=
    kahanTotalInputCoeff_abs_sub_one_le
      (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
      (deltaE := deltaE) (u := u) hu hY hS hSub hE
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  have hu2_le_one : u ^ 2 ≤ 1 := by
    have h :=
      mul_le_mul hu1 hu1 hu (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hu4_le_u2 : u ^ 4 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu2_le_one (sq_nonneg u)
    nlinarith
  nlinarith

/-- Source-shaped nonempty-horizon version of the current-input coefficient
radius, useful before the all-prefix Goldberg/Knuth product collapse. -/
theorem kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_n_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalInputCoeff deltaY deltaS deltaSub deltaE - 1| ≤
      2 * u + 9 * (n : ℝ) * u ^ 2 := by
  have hlocal :=
    kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
      (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
      (deltaE := deltaE) (u := u) hu hu1 hY hS hSub hE
  have hn_real : (1 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hscale : 9 * u ^ 2 ≤ (n : ℝ) * (9 * u ^ 2) :=
    le_mul_of_one_le_left
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) (sq_nonneg u))
      hn_real
  have hscale' : 9 * u ^ 2 ≤ 9 * (n : ℝ) * u ^ 2 := by
    calc
      9 * u ^ 2 ≤ (n : ℝ) * (9 * u ^ 2) := hscale
      _ = 9 * (n : ℝ) * u ^ 2 := by ring
  nlinarith

/-- Small-`u` local bound for the retained-correction residual coefficient. -/
theorem kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE| ≤
      2 * u + 12 * u ^ 2 := by
  let A := kahanTotalStateCoeff deltaS deltaSub deltaE
  let B := kahanTotalInputCoeff deltaY deltaS deltaSub deltaE
  have hA : |A - 1| ≤ 3 * u ^ 2 := by
    simpa [A] using
      kahanTotalStateCoeff_abs_sub_one_le_three_u_sq
        (deltaS := deltaS) (deltaSub := deltaSub) (deltaE := deltaE)
        (u := u) hu hu1 hS hSub hE
  have hB : |B - 1| ≤ 2 * u + 9 * u ^ 2 := by
    simpa [B] using
      kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
        (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
        (deltaE := deltaE) (u := u) hu hu1 hY hS hSub hE
  have htri : |B - A| ≤ |B - 1| + |A - 1| := by
    have hrewrite : B - A = (B - 1) + (1 - A) := by ring
    rw [hrewrite]
    calc
      |(B - 1) + (1 - A)| ≤ |B - 1| + |1 - A| :=
        abs_add_le (B - 1) (1 - A)
      _ = |B - 1| + |A - 1| := by
        rw [abs_sub_comm 1 A]
  have hres :
      |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE| = |B - A| := by
    rfl
  rw [hres]
  nlinarith

/-- Source-shaped nonempty-horizon wrapper for the retained-correction
residual coefficient. -/
theorem kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_n_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    {n : ℕ} (hn : 1 ≤ n)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE| ≤
      2 * u + 12 * (n : ℝ) * u ^ 2 := by
  have hlocal :=
    kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_u_sq
      (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
      (deltaE := deltaE) (u := u) hu hu1 hY hS hSub hE
  have hn_real : (1 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hscale : 12 * u ^ 2 ≤ (n : ℝ) * (12 * u ^ 2) :=
    le_mul_of_one_le_left
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) (sq_nonneg u))
      hn_real
  have hscale' : 12 * u ^ 2 ≤ 12 * (n : ℝ) * u ^ 2 := by
    calc
      12 * u ^ 2 ≤ (n : ℝ) * (12 * u ^ 2) := hscale
      _ = 12 * (n : ℝ) * u ^ 2 := by ring
  nlinarith

/-- Local bound for the previous-running-sum coefficient in the fully expanded
Kahan correction recurrence. -/
theorem kahanCorrectionStateCoeff_abs_le
    {deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u)
    (hS : |deltaS| ≤ u) (hSub : |deltaSub| ≤ u)
    (hE : |deltaE| ≤ u) :
    |kahanCorrectionStateCoeff deltaS deltaSub deltaE| ≤
      u * (1 + u) ^ 2 := by
  have hSub1 : |1 + deltaSub| ≤ 1 + u := by
    calc
      |1 + deltaSub| ≤ |(1 : ℝ)| + |deltaSub| := abs_add_le _ _
      _ = 1 + |deltaSub| := by norm_num
      _ ≤ 1 + u := by nlinarith [hSub]
  have hE1 : |1 + deltaE| ≤ 1 + u := by
    calc
      |1 + deltaE| ≤ |(1 : ℝ)| + |deltaE| := abs_add_le _ _
      _ = 1 + |deltaE| := by norm_num
      _ ≤ 1 + u := by nlinarith [hE]
  have hprod : |deltaS| * |1 + deltaSub| ≤ u * (1 + u) := by
    exact mul_le_mul hS hSub1 (abs_nonneg _) hu
  rw [kahanCorrectionStateCoeff, abs_mul, abs_mul, abs_neg]
  calc
    |deltaS| * |1 + deltaSub| * |1 + deltaE|
        ≤ (u * (1 + u)) * (1 + u) := by
          exact mul_le_mul hprod hE1 (abs_nonneg _)
            (mul_nonneg hu (by nlinarith [hu]))
    _ = u * (1 + u) ^ 2 := by ring

/-- Local bound for the current input-plus-correction coefficient in the fully
expanded Kahan correction recurrence. -/
theorem kahanCorrectionInputCoeff_abs_le
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE| ≤
      u * (1 + u) ^ 2 * (2 + u) := by
  have hY1 : |1 + deltaY| ≤ 1 + u := by
    calc
      |1 + deltaY| ≤ |(1 : ℝ)| + |deltaY| := abs_add_le _ _
      _ = 1 + |deltaY| := by norm_num
      _ ≤ 1 + u := by nlinarith [hY]
  have hSub1 : |1 + deltaSub| ≤ 1 + u := by
    calc
      |1 + deltaSub| ≤ |(1 : ℝ)| + |deltaSub| := abs_add_le _ _
      _ = 1 + |deltaSub| := by norm_num
      _ ≤ 1 + u := by nlinarith [hSub]
  have hE1 : |1 + deltaE| ≤ 1 + u := by
    calc
      |1 + deltaE| ≤ |(1 : ℝ)| + |deltaE| := abs_add_le _ _
      _ = 1 + |deltaE| := by norm_num
      _ ≤ 1 + u := by nlinarith [hE]
  have hSprod : |deltaS * (1 + deltaSub)| ≤ u * (1 + u) := by
    rw [abs_mul]
    exact mul_le_mul hS hSub1 (abs_nonneg _) hu
  have hq : |deltaSub + deltaS * (1 + deltaSub)| ≤ u * (2 + u) := by
    calc
      |deltaSub + deltaS * (1 + deltaSub)|
          ≤ |deltaSub| + |deltaS * (1 + deltaSub)| := abs_add_le _ _
      _ ≤ u + u * (1 + u) := by nlinarith [hSub, hSprod]
      _ = u * (2 + u) := by ring
  rw [kahanCorrectionInputCoeff, abs_mul, abs_mul, abs_neg]
  calc
    |1 + deltaY| * |deltaSub + deltaS * (1 + deltaSub)| *
        |1 + deltaE|
        ≤ (1 + u) * (u * (2 + u)) * (1 + u) := by
          exact mul_le_mul
            (mul_le_mul hY1 hq (abs_nonneg _) (by nlinarith [hu]))
            hE1 (abs_nonneg _)
            (mul_nonneg (by nlinarith [hu])
              (mul_nonneg hu (by nlinarith [hu])))
    _ = u * (1 + u) ^ 2 * (2 + u) := by ring

/-! ### General correction-subtraction cancellation

The exact-subtraction route below sets `deltaSub = 0`.  The ordinary
Goldberg/Higham recurrence instead has to keep `deltaSub`, but it appears with
opposite signs in the stored sum and retained correction rows.  These lemmas
isolate that local cancellation before any suffix product argument is applied.
-/

/-- The paired correction residual is `-deltaSub` plus only higher-order
terms in the four local Kahan roundoff deltas. -/
theorem kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_eq
    (deltaY deltaS deltaSub deltaE : ℝ) :
    kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE -
        kahanCorrectionStateCoeff deltaS deltaSub deltaE + deltaSub =
      -(deltaSub * deltaE + deltaY * deltaSub +
        deltaY * deltaSub * deltaE + deltaY * deltaS +
        deltaY * deltaS * deltaE + deltaY * deltaS * deltaSub +
        deltaY * deltaS * deltaSub * deltaE) := by
  dsimp [kahanCorrectionInputCoeff, kahanCorrectionStateCoeff]
  ring

/-- Small-`u` bound for the higher-order remainder in the general correction
residual cancellation. -/
theorem kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_abs_le_seven_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE -
        kahanCorrectionStateCoeff deltaS deltaSub deltaE + deltaSub| ≤
      7 * u ^ 2 := by
  let a := deltaSub * deltaE
  let b := deltaY * deltaSub
  let c := deltaY * deltaSub * deltaE
  let d := deltaY * deltaS
  let e := deltaY * deltaS * deltaE
  let f := deltaY * deltaS * deltaSub
  let g := deltaY * deltaS * deltaSub * deltaE
  have ha : |a| ≤ u ^ 2 := by
    dsimp [a]
    calc
      |deltaSub * deltaE| = |deltaSub| * |deltaE| := by rw [abs_mul]
      _ ≤ u * u := mul_le_mul hSub hE (abs_nonneg _) hu
      _ = u ^ 2 := by ring
  have hb : |b| ≤ u ^ 2 := by
    dsimp [b]
    calc
      |deltaY * deltaSub| = |deltaY| * |deltaSub| := by rw [abs_mul]
      _ ≤ u * u := mul_le_mul hY hSub (abs_nonneg _) hu
      _ = u ^ 2 := by ring
  have hc : |c| ≤ u ^ 3 := by
    dsimp [c]
    calc
      |deltaY * deltaSub * deltaE| =
          |deltaY| * |deltaSub| * |deltaE| := by rw [abs_mul, abs_mul]
      _ ≤ u * u * u := by
          have hprod : |deltaY| * |deltaSub| ≤ u * u :=
            mul_le_mul hY hSub (abs_nonneg _) hu
          exact mul_le_mul hprod hE (abs_nonneg _)
            (mul_nonneg hu hu)
      _ = u ^ 3 := by ring
  have hd : |d| ≤ u ^ 2 := by
    dsimp [d]
    calc
      |deltaY * deltaS| = |deltaY| * |deltaS| := by rw [abs_mul]
      _ ≤ u * u := mul_le_mul hY hS (abs_nonneg _) hu
      _ = u ^ 2 := by ring
  have he : |e| ≤ u ^ 3 := by
    dsimp [e]
    calc
      |deltaY * deltaS * deltaE| =
          |deltaY| * |deltaS| * |deltaE| := by rw [abs_mul, abs_mul]
      _ ≤ u * u * u := by
          have hprod : |deltaY| * |deltaS| ≤ u * u :=
            mul_le_mul hY hS (abs_nonneg _) hu
          exact mul_le_mul hprod hE (abs_nonneg _)
            (mul_nonneg hu hu)
      _ = u ^ 3 := by ring
  have hf : |f| ≤ u ^ 3 := by
    dsimp [f]
    calc
      |deltaY * deltaS * deltaSub| =
          |deltaY| * |deltaS| * |deltaSub| := by rw [abs_mul, abs_mul]
      _ ≤ u * u * u := by
          have hprod : |deltaY| * |deltaS| ≤ u * u :=
            mul_le_mul hY hS (abs_nonneg _) hu
          exact mul_le_mul hprod hSub (abs_nonneg _)
            (mul_nonneg hu hu)
      _ = u ^ 3 := by ring
  have hg : |g| ≤ u ^ 4 := by
    dsimp [g]
    calc
      |deltaY * deltaS * deltaSub * deltaE| =
          |deltaY| * |deltaS| * |deltaSub| * |deltaE| := by
            rw [abs_mul, abs_mul, abs_mul]
      _ ≤ u * u * u * u := by
          have hYS : |deltaY| * |deltaS| ≤ u * u :=
            mul_le_mul hY hS (abs_nonneg _) hu
          have hYSSub :
              |deltaY| * |deltaS| * |deltaSub| ≤ u * u * u :=
            mul_le_mul hYS hSub (abs_nonneg _)
              (mul_nonneg hu hu)
          exact mul_le_mul hYSSub hE (abs_nonneg _)
            (mul_nonneg (mul_nonneg hu hu) hu)
      _ = u ^ 4 := by ring
  have htri :
      |a + b + c + d + e + f + g| ≤
        |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
    calc
      |a + b + c + d + e + f + g|
          = |((((a + b) + c) + d) + e) + f + g| := by ring
      _ ≤ |((((a + b) + c) + d) + e) + f| + |g| :=
        abs_add_le _ _
      _ ≤ |(((a + b) + c) + d) + e| + |f| + |g| := by
        nlinarith [abs_add_le ((((a + b) + c) + d) + e) f]
      _ ≤ |((a + b) + c) + d| + |e| + |f| + |g| := by
        nlinarith [abs_add_le (((a + b) + c) + d) e]
      _ ≤ |(a + b) + c| + |d| + |e| + |f| + |g| := by
        nlinarith [abs_add_le ((a + b) + c) d]
      _ ≤ |a + b| + |c| + |d| + |e| + |f| + |g| := by
        nlinarith [abs_add_le (a + b) c]
      _ ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
        nlinarith [abs_add_le a b]
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  have hu2_le_one : u ^ 2 ≤ 1 := by
    have h :=
      mul_le_mul hu1 hu1 hu (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hu4_le_u2 : u ^ 4 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu2_le_one (sq_nonneg u)
    nlinarith
  rw [kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_eq, abs_neg]
  have hsum :
      |deltaSub * deltaE + deltaY * deltaSub +
          deltaY * deltaSub * deltaE + deltaY * deltaS +
          deltaY * deltaS * deltaE + deltaY * deltaS * deltaSub +
          deltaY * deltaS * deltaSub * deltaE| ≤
        |a| + |b| + |c| + |d| + |e| + |f| + |g| := by
    simpa [a, b, c, d, e, f, g] using htri
  calc
    |deltaSub * deltaE + deltaY * deltaSub +
        deltaY * deltaSub * deltaE + deltaY * deltaS +
        deltaY * deltaS * deltaE + deltaY * deltaS * deltaSub +
        deltaY * deltaS * deltaSub * deltaE|
        ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| := hsum
    _ ≤ u ^ 2 + u ^ 2 + u ^ 3 + u ^ 2 + u ^ 3 + u ^ 3 +
          u ^ 4 := by
        nlinarith [ha, hb, hc, hd, he, hf, hg]
    _ ≤ 7 * u ^ 2 := by
        nlinarith [hu3_le_u2, hu4_le_u2]

/-- The difference between the paired-total residual and the correction
residual has first-order part `deltaY`. -/
theorem kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_eq
    (deltaY deltaS deltaSub deltaE : ℝ) :
    kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
        (kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE -
          kahanCorrectionStateCoeff deltaS deltaSub deltaE) - deltaY =
      deltaY * deltaS := by
  dsimp [kahanTotalResidualCoeff, kahanTotalInputCoeff,
    kahanTotalStateCoeff, kahanCorrectionInputCoeff,
    kahanCorrectionStateCoeff]
  ring

/-- Small-`u` bound for the higher-order remainder in
`totalResidual - correctionResidual = deltaY + O(u^2)`. -/
theorem kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) :
    |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
        (kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE -
          kahanCorrectionStateCoeff deltaS deltaSub deltaE) - deltaY| ≤
      u ^ 2 := by
  rw [kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_eq]
  calc
    |deltaY * deltaS| = |deltaY| * |deltaS| := by rw [abs_mul]
    _ ≤ u * u := mul_le_mul hY hS (abs_nonneg _) hu
    _ = u ^ 2 := by ring

/-- Combined local residual cancellation: the paired-total residual has
first-order part `deltaY - deltaSub`; all remaining terms are second order. -/
theorem kahanTotalResidualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
    {deltaY deltaS deltaSub deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u)
    (hSub : |deltaSub| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE +
        deltaSub - deltaY| ≤
      8 * u ^ 2 := by
  let correctionResidual :=
    kahanCorrectionInputCoeff deltaY deltaS deltaSub deltaE -
      kahanCorrectionStateCoeff deltaS deltaSub deltaE
  have htotal :
      |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
          correctionResidual - deltaY| ≤ u ^ 2 := by
    simpa [correctionResidual] using
      kahanTotalResidualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
        (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
        (deltaE := deltaE) (u := u) hu hY hS
  have hcorr :
      |correctionResidual + deltaSub| ≤ 7 * u ^ 2 := by
    simpa [correctionResidual] using
      kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_abs_le_seven_u_sq
        (deltaY := deltaY) (deltaS := deltaS) (deltaSub := deltaSub)
        (deltaE := deltaE) (u := u) hu hu1 hY hS hSub hE
  have hrewrite :
      kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE +
          deltaSub - deltaY =
        (kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
            correctionResidual - deltaY) +
          (correctionResidual + deltaSub) := by
    ring
  rw [hrewrite]
  calc
    |(kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
          correctionResidual - deltaY) +
        (correctionResidual + deltaSub)|
        ≤ |kahanTotalResidualCoeff deltaY deltaS deltaSub deltaE -
            correctionResidual - deltaY| +
          |correctionResidual + deltaSub| := abs_add_le _ _
    _ ≤ u ^ 2 + 7 * u ^ 2 := add_le_add htotal hcorr
    _ = 8 * u ^ 2 := by ring

/-! ### Exact correction-subtraction coefficient bounds

The following local lemmas isolate the algebra used by the Goldberg/Higham
route when the correction subtraction `temp - s` is exact.  Under the bare
relative-error model the chosen subtraction delta may be first order; with
`deltaSub = 0`, the paired correction residual drops to second order. -/

/-- With exact correction subtraction, the compensated-total old-state
coefficient differs from one by only `u^2`. -/
theorem kahanTotalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
    {deltaS deltaE u : ℝ} (hu : 0 ≤ u)
    (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalStateCoeff deltaS 0 deltaE - 1| ≤ u ^ 2 := by
  have hSE : |deltaS * deltaE| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hE (abs_nonneg _) hu
  have hrewrite :
      kahanTotalStateCoeff deltaS 0 deltaE - 1 =
        -(deltaS * deltaE) := by
    rw [kahanTotalStateCoeff_eq_one_sub_second_order]
    ring
  rw [hrewrite, abs_neg]
  simpa [pow_two] using hSE

/-- With exact correction subtraction, the compensated-total current-input
coefficient has only one first-order term. -/
theorem kahanTotalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
    {deltaY deltaS deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalInputCoeff deltaY deltaS 0 deltaE - 1| ≤
      u + 2 * u ^ 2 := by
  have hSE : |deltaS * deltaE| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hS hE (abs_nonneg _) hu
  have hYSE : |deltaY * deltaS * deltaE| ≤ u * u * u := by
    rw [abs_mul, abs_mul]
    have hYS : |deltaY| * |deltaS| ≤ u * u :=
      mul_le_mul hY hS (abs_nonneg _) hu
    exact mul_le_mul hYS hE (abs_nonneg _) (mul_nonneg hu hu)
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  have hrewrite :
      kahanTotalInputCoeff deltaY deltaS 0 deltaE - 1 =
        deltaY - deltaS * deltaE - deltaY * deltaS * deltaE := by
    rw [kahanTotalInputCoeff_eq_first_second_order]
    ring
  rw [hrewrite]
  calc
    |deltaY - deltaS * deltaE - deltaY * deltaS * deltaE|
        ≤ |deltaY| + |deltaS * deltaE| +
            |deltaY * deltaS * deltaE| := by
          calc
            |deltaY - deltaS * deltaE - deltaY * deltaS * deltaE|
                = |(deltaY - deltaS * deltaE) -
                    deltaY * deltaS * deltaE| := by ring
            _ ≤ |deltaY - deltaS * deltaE| +
                  |deltaY * deltaS * deltaE| := by
                simpa [sub_eq_add_neg, abs_neg] using
                  abs_add_le (deltaY - deltaS * deltaE)
                    (-(deltaY * deltaS * deltaE))
            _ ≤ |deltaY| + |deltaS * deltaE| +
                  |deltaY * deltaS * deltaE| := by
                have h :
                    |deltaY - deltaS * deltaE| ≤
                      |deltaY| + |deltaS * deltaE| := by
                  simpa [sub_eq_add_neg, abs_neg] using
                  abs_add_le deltaY (-(deltaS * deltaE))
                nlinarith
    _ ≤ u + u * u + u * u * u := by
          nlinarith [hY, hSE, hYSE]
    _ ≤ u + 2 * u ^ 2 := by
          nlinarith

/-- With exact correction subtraction, the compensated-total residual
coefficient is first order only in the input-add delta. -/
theorem kahanTotalResidualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
    {deltaY deltaS deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanTotalResidualCoeff deltaY deltaS 0 deltaE| ≤
      u + u ^ 2 := by
  have hYSE : |deltaY * deltaS * deltaE| ≤ u * u * u := by
    rw [abs_mul, abs_mul]
    have hYS : |deltaY| * |deltaS| ≤ u * u :=
      mul_le_mul hY hS (abs_nonneg _) hu
    exact mul_le_mul hYS hE (abs_nonneg _) (mul_nonneg hu hu)
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  have hrewrite :
      kahanTotalResidualCoeff deltaY deltaS 0 deltaE =
        deltaY - deltaY * deltaS * deltaE := by
    dsimp [kahanTotalResidualCoeff]
    rw [kahanTotalInputCoeff_eq_first_second_order]
    rw [kahanTotalStateCoeff_eq_one_sub_second_order]
    ring
  rw [hrewrite]
  calc
    |deltaY - deltaY * deltaS * deltaE|
        ≤ |deltaY| + |deltaY * deltaS * deltaE| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le deltaY (-(deltaY * deltaS * deltaE))
    _ ≤ u + u * u * u := by
          nlinarith [hY, hYSE]
    _ ≤ u + u ^ 2 := by
          nlinarith

/-- With exact correction subtraction, the correction old-total coefficient
has radius `u + u^2`. -/
theorem kahanCorrectionStateCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
    {deltaS deltaE u : ℝ} (hu : 0 ≤ u)
    (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanCorrectionStateCoeff deltaS 0 deltaE| ≤
      u + u ^ 2 := by
  have hE1 : |1 + deltaE| ≤ 1 + u := by
    calc
      |1 + deltaE| ≤ |(1 : ℝ)| + |deltaE| := abs_add_le _ _
      _ = 1 + |deltaE| := by norm_num
      _ ≤ 1 + u := by nlinarith [hE]
  rw [kahanCorrectionStateCoeff, abs_mul, abs_mul, abs_neg]
  calc
    |deltaS| * |1 + 0| * |1 + deltaE|
        ≤ u * 1 * (1 + u) := by
          have hOneZero : |(1 : ℝ) + 0| ≤ 1 := by norm_num
          exact mul_le_mul
            (mul_le_mul hS hOneZero
              (abs_nonneg _) hu)
            hE1 (abs_nonneg _)
            (mul_nonneg hu (by norm_num))
    _ = u + u ^ 2 := by ring

/-- With exact correction subtraction, the correction current-input
coefficient has radius `u + O(u^2)`. -/
theorem kahanCorrectionInputCoeff_abs_le_u_plus_three_u_sq_of_deltaSub_zero
    {deltaY deltaS deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanCorrectionInputCoeff deltaY deltaS 0 deltaE| ≤
      u + 3 * u ^ 2 := by
  have hY1 : |1 + deltaY| ≤ 1 + u := by
    calc
      |1 + deltaY| ≤ |(1 : ℝ)| + |deltaY| := abs_add_le _ _
      _ = 1 + |deltaY| := by norm_num
      _ ≤ 1 + u := by nlinarith [hY]
  have hE1 : |1 + deltaE| ≤ 1 + u := by
    calc
      |1 + deltaE| ≤ |(1 : ℝ)| + |deltaE| := abs_add_le _ _
      _ = 1 + |deltaE| := by norm_num
      _ ≤ 1 + u := by nlinarith [hE]
  have hprod :
      |1 + deltaY| * |deltaS| * |1 + deltaE| ≤
        (1 + u) * u * (1 + u) := by
    exact mul_le_mul
      (mul_le_mul hY1 hS (abs_nonneg _) (by nlinarith [hu]))
      hE1 (abs_nonneg _)
      (mul_nonneg (by nlinarith [hu]) hu)
  have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
    have h :=
      mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
    nlinarith
  rw [kahanCorrectionInputCoeff, abs_mul, abs_mul, abs_neg]
  calc
    |1 + deltaY| * |0 + deltaS * (1 + 0)| * |1 + deltaE|
        = |1 + deltaY| * |deltaS| * |1 + deltaE| := by ring_nf
    _ ≤ (1 + u) * u * (1 + u) := hprod
    _ = u + 2 * u ^ 2 + u ^ 3 := by ring
    _ ≤ u + 3 * u ^ 2 := by nlinarith

/-- Exact algebra for the correction residual `D - C` when the correction
subtraction has zero roundoff. -/
theorem kahanCorrectionInputCoeff_sub_stateCoeff_eq_deltaSub_zero
    (deltaY deltaS deltaE : ℝ) :
    kahanCorrectionInputCoeff deltaY deltaS 0 deltaE -
        kahanCorrectionStateCoeff deltaS 0 deltaE =
      -deltaY * deltaS * (1 + deltaE) := by
  dsimp [kahanCorrectionInputCoeff, kahanCorrectionStateCoeff]
  ring

/-- With exact correction subtraction, the paired correction residual is
second order. -/
theorem kahanCorrectionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
    {deltaY deltaS deltaE u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hY : |deltaY| ≤ u) (hS : |deltaS| ≤ u) (hE : |deltaE| ≤ u) :
    |kahanCorrectionInputCoeff deltaY deltaS 0 deltaE -
        kahanCorrectionStateCoeff deltaS 0 deltaE| ≤
      2 * u ^ 2 := by
  rw [kahanCorrectionInputCoeff_sub_stateCoeff_eq_deltaSub_zero]
  have hE1 : |1 + deltaE| ≤ 1 + u := by
    calc
      |1 + deltaE| ≤ |(1 : ℝ)| + |deltaE| := abs_add_le _ _
      _ = 1 + |deltaE| := by norm_num
      _ ≤ 1 + u := by nlinarith [hE]
  have hYS : |deltaY * deltaS| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hY hS (abs_nonneg _) hu
  have hprod :
      |deltaY * deltaS * (1 + deltaE)| ≤ u ^ 2 * (1 + u) := by
    rw [abs_mul]
    have hYS' : |deltaY * deltaS| ≤ u ^ 2 := by
      simpa [pow_two] using hYS
    exact mul_le_mul hYS' hE1 (abs_nonneg _) (sq_nonneg u)
  have hneg :
      |-deltaY * deltaS * (1 + deltaE)| =
        |deltaY * deltaS * (1 + deltaE)| := by
    rw [show -deltaY * deltaS * (1 + deltaE) =
        -(deltaY * deltaS * (1 + deltaE)) by ring, abs_neg]
  rw [hneg]
  calc
    |deltaY * deltaS * (1 + deltaE)| ≤ u ^ 2 * (1 + u) := hprod
    _ = u ^ 2 + u ^ 3 := by ring
    _ ≤ 2 * u ^ 2 := by
        have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
          have h :=
            mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
          nlinarith
        nlinarith

/-- Local absolute bound for the retained correction produced by one Kahan
step. -/
theorem kahanStepDeltaWitness_e_abs_le
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    |(kahanStepTrace fp x state).e| ≤
      fp.u * (1 + fp.u) ^ 2 * |state.s| +
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) * |x + state.e| := by
  have hCs := kahanCorrectionStateCoeff_abs_le
    (u := fp.u) fp.u_nonneg w.h_deltaS w.h_deltaSub w.h_deltaE
  have hCx := kahanCorrectionInputCoeff_abs_le
    (u := fp.u) fp.u_nonneg w.h_deltaY w.h_deltaS w.h_deltaSub w.h_deltaE
  rw [kahanStepDeltaWitness_e_coefficients fp x state w]
  calc
    |state.s * kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE +
        (x + state.e) *
          kahanCorrectionInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE|
        ≤ |state.s *
              kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE| +
            |(x + state.e) *
              kahanCorrectionInputCoeff
                w.deltaY w.deltaS w.deltaSub w.deltaE| :=
          abs_add_le _ _
    _ = |state.s| *
          |kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE| +
          |x + state.e| *
            |kahanCorrectionInputCoeff
              w.deltaY w.deltaS w.deltaSub w.deltaE| := by
        rw [abs_mul, abs_mul]
    _ ≤ |state.s| * (fp.u * (1 + fp.u) ^ 2) +
          |x + state.e| *
            (fp.u * (1 + fp.u) ^ 2 * (2 + fp.u)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hCs (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hCx (abs_nonneg _))
    _ = fp.u * (1 + fp.u) ^ 2 * |state.s| +
          fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
            |x + state.e| := by
        ring

/-- Split-input version of the local absolute bound for the retained
correction produced by one Kahan step. -/
theorem kahanStepDeltaWitness_e_abs_le_split
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    |(kahanStepTrace fp x state).e| ≤
      fp.u * (1 + fp.u) ^ 2 * |state.s| +
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
          (|x| + |state.e|) := by
  have hprev := kahanStepDeltaWitness_e_abs_le fp x state w
  have hcoef_nonneg :
      0 ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
    exact mul_nonneg
      (mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u)))
      (by nlinarith [fp.u_nonneg])
  have hmul :
      fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) * |x + state.e| ≤
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
          (|x| + |state.e|) := by
    exact mul_le_mul_of_nonneg_left (abs_add_le x state.e) hcoef_nonneg
  calc
    |(kahanStepTrace fp x state).e| ≤
        fp.u * (1 + fp.u) ^ 2 * |state.s| +
          fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
            |x + state.e| := hprev
    _ ≤ fp.u * (1 + fp.u) ^ 2 * |state.s| +
          fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
            (|x| + |state.e|) := by
        exact add_le_add (le_refl _) hmul

/-- One-step coefficient form of the fully expanded Kahan compensated-total
recurrence.  This is the local algebraic form used before the per-input
Goldberg/Knuth coefficient recursion. -/
theorem kahanStepDeltaWitness_total_coefficients
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).s + (kahanStepTrace fp x state).e =
      state.s * kahanTotalStateCoeff w.deltaS w.deltaSub w.deltaE +
        (x + state.e) *
          kahanTotalInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE := by
  rw [kahanStepDeltaWitness_total_fully_expanded fp x state w]
  dsimp [kahanTotalStateCoeff, kahanTotalInputCoeff]
  ring

/-- One-step compensated-total recurrence rewritten around the previous total
`state.s + state.e`.

The extra residual term is the retained-correction obstruction that the
ordinary Kahan backward-error recursion must still absorb or bound. -/
theorem kahanStepDeltaWitness_total_compensated_total_coefficients
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) :
    (kahanStepTrace fp x state).s + (kahanStepTrace fp x state).e =
      (state.s + state.e) *
          kahanTotalStateCoeff w.deltaS w.deltaSub w.deltaE +
        x * kahanTotalInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE +
        state.e *
          kahanTotalResidualCoeff w.deltaY w.deltaS w.deltaSub w.deltaE := by
  rw [kahanStepDeltaWitness_total_coefficients fp x state w]
  dsimp [kahanTotalResidualCoeff]
  ring

/-- Standard-model roundoff witnesses for the `i`th Algorithm 4.2 trace step,
with the input state supplied by the Kahan prefix trace. -/
noncomputable def kahanTrace_deltaWitness (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)) :=
  kahanStepTrace_deltaWitness fp (v i)
    (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))

/-- The `y` equation from the standard-model witness for the `i`th Kahan
trace step. -/
theorem kahanTrace_deltaWitness_y (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    (kahanTrace fp v i).y =
      (v i + (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)).e) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaY) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    (kahanTrace_deltaWitness fp v i).hy

/-- The `s` equation from the standard-model witness for the `i`th Kahan
trace step. -/
theorem kahanTrace_deltaWitness_s (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    (kahanTrace fp v i).s =
      ((kahanTrace fp v i).temp + (kahanTrace fp v i).y) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaS) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    (kahanTrace_deltaWitness fp v i).hs

/-- The `temp - s` subtraction equation from the standard-model witness for
the `i`th Kahan trace step. -/
theorem kahanTrace_deltaWitness_sub (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    fp.fl_sub (kahanTrace fp v i).temp (kahanTrace fp v i).s =
      ((kahanTrace fp v i).temp - (kahanTrace fp v i).s) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaSub) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    (kahanTrace_deltaWitness fp v i).hsub

/-- The correction `e` equation from the standard-model witness for the `i`th
Kahan trace step. -/
theorem kahanTrace_deltaWitness_e (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    (kahanTrace fp v i).e =
      (fp.fl_sub (kahanTrace fp v i).temp (kahanTrace fp v i).s +
        (kahanTrace fp v i).y) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaE) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    (kahanTrace_deltaWitness fp v i).he

/-- Expanded indexed recurrence for the updated Kahan sum at prefix trace step
`i`, with the `y = fl(x_i + e)` delta already substituted. -/
theorem kahanTrace_deltaWitness_s_expanded (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    (kahanTrace fp v i).s =
      ((kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)).s +
          (v i + (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)).e) *
            (1 + (kahanTrace_deltaWitness fp v i).deltaY)) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaS) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_s_expanded fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Expanded indexed recurrence for the Kahan correction at prefix trace step
`i`, with the displayed subtraction delta already substituted. -/
theorem kahanTrace_deltaWitness_e_expanded (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    (kahanTrace fp v i).e =
      ((((kahanTrace fp v i).temp - (kahanTrace fp v i).s) *
          (1 + (kahanTrace_deltaWitness fp v i).deltaSub)) +
        (kahanTrace fp v i).y) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaE) := by
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_e_expanded fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Fully expanded indexed recurrence for the Kahan correction at prefix trace
step `i`, with no remaining trace-temporary terms on the right-hand side. -/
theorem kahanTrace_deltaWitness_e_fully_expanded (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    let y0 := (v i + state.e) *
      (1 + (kahanTrace_deltaWitness fp v i).deltaY)
    let s0 := (state.s + y0) *
      (1 + (kahanTrace_deltaWitness fp v i).deltaS)
    (kahanTrace fp v i).e =
      ((state.s - s0) *
          (1 + (kahanTrace_deltaWitness fp v i).deltaSub) +
        y0) *
        (1 + (kahanTrace_deltaWitness fp v i).deltaE) := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_e_fully_expanded fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Fully expanded indexed recurrence for the compensated total at prefix trace
step `i`, the algebraic input for the Knuth/Goldberg coefficient recursion. -/
theorem kahanTrace_deltaWitness_total_fully_expanded (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    let y0 := (v i + state.e) *
      (1 + (kahanTrace_deltaWitness fp v i).deltaY)
    let s0 := (state.s + y0) *
      (1 + (kahanTrace_deltaWitness fp v i).deltaS)
    (kahanTrace fp v i).s + (kahanTrace fp v i).e =
      s0 +
        ((state.s - s0) *
            (1 + (kahanTrace_deltaWitness fp v i).deltaSub) +
          y0) *
          (1 + (kahanTrace_deltaWitness fp v i).deltaE) := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_total_fully_expanded fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Indexed coefficient form of the Kahan compensated-total recurrence.  The
right-hand side has named coefficients for the previous running sum and the
current exact input-plus-correction term, ready for the ordinary Kahan
coefficient recursion. -/
theorem kahanTrace_deltaWitness_total_coefficients (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    (kahanTrace fp v i).s + (kahanTrace fp v i).e =
      state.s *
          kahanTotalStateCoeff
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE +
        (v i + state.e) *
          kahanTotalInputCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_total_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Indexed coefficient form of the Kahan retained-correction recurrence.
This is the `e`-component companion to the direct stored-sum recurrence below,
and supplies the coupled returned-sum/correction route. -/
theorem kahanTrace_deltaWitness_e_coefficients (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    (kahanTrace fp v i).e =
      state.s *
          kahanCorrectionStateCoeff
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE +
        (v i + state.e) *
          kahanCorrectionInputCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_e_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Indexed coefficient form of the directly expanded Kahan stored-sum
recurrence.  This exposes the returned-sum local coefficients without charging
the final retained correction as an independent residual. -/
theorem kahanTrace_deltaWitness_s_coefficients (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    (kahanTrace fp v i).s =
      state.s *
          kahanStoredSumStateCoeff
            (kahanTrace_deltaWitness fp v i).deltaS +
        (v i) *
          kahanStoredSumInputCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS +
        state.e *
          kahanStoredSumInputCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_s_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Indexed local radius for the current-input coefficient in the direct
stored-sum recurrence. -/
theorem kahanTrace_deltaWitness_storedSumInputCoeff_abs_sub_one_le_two_u_plus_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |kahanStoredSumInputCoeff
        (kahanTrace_deltaWitness fp v i).deltaY
        (kahanTrace_deltaWitness fp v i).deltaS - 1| ≤
      2 * fp.u + fp.u ^ 2 :=
  kahanStoredSumInputCoeff_abs_sub_one_le_two_u_plus_u_sq fp.u_nonneg
    (kahanTrace_deltaWitness fp v i).h_deltaY
    (kahanTrace_deltaWitness fp v i).h_deltaS

/-- Indexed compensated-total recurrence rewritten around the previous
compensated total.  This is the exact prefix-trace input for the remaining
ordinary-Kahan `mu_i` recursion: besides the previous-total and current-input
coefficients, it exposes the retained-correction residual coefficient. -/
theorem kahanTrace_deltaWitness_total_compensated_total_coefficients
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    (kahanTrace fp v i).s + (kahanTrace fp v i).e =
      (state.s + state.e) *
          kahanTotalStateCoeff
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE +
        (v i) *
          kahanTotalInputCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE +
        state.e *
          kahanTotalResidualCoeff
            (kahanTrace_deltaWitness fp v i).deltaY
            (kahanTrace_deltaWitness fp v i).deltaS
            (kahanTrace_deltaWitness fp v i).deltaSub
            (kahanTrace_deltaWitness fp v i).deltaE := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_total_compensated_total_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- A prefix-indexed family of explicit Kahan roundoff witnesses for the first
`k` Kahan steps.  This avoids depending on the arbitrary witness selected by
`Classical.choice`, which is essential for the exact-subtraction route. -/
def KahanPrefixDeltaWitnessFamily
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Type :=
  (i : Fin k) →
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    KahanStepDeltaWitness fp (v idx)
      (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))

/-- Prefix-level exactness surface for Algorithm 4.2's displayed correction
subtraction `temp - s`.  This is an operation-level bridge: it states the
subtraction is exact in the actual prefix trace, without committing to a
particular roundoff witness selected by `Classical.choice`. -/
def KahanPrefixCorrectionSubExact
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Prop :=
  ∀ i : Fin k,
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    fp.fl_sub (kahanTrace fp v idx).temp (kahanTrace fp v idx).s =
      (kahanTrace fp v idx).temp - (kahanTrace fp v idx).s

/-- Construct an explicit prefix witness family from exact correction
subtraction in every processed Kahan prefix step. -/
noncomputable def kahanPrefixDeltaWitnessFamilyOfExactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hExactSubTrace : KahanPrefixCorrectionSubExact fp v k hk) :
    KahanPrefixDeltaWitnessFamily fp v k hk :=
  fun i =>
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    let hsubExact :
        fp.fl_sub
            (kahanStepTrace fp (v idx)
              (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).temp
            (kahanStepTrace fp (v idx)
              (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).s =
          (kahanStepTrace fp (v idx)
              (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).temp -
            (kahanStepTrace fp (v idx)
              (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))).s := by
      have h := hExactSubTrace i
      simpa [KahanPrefixCorrectionSubExact, kahanTrace, idx] using h
    kahanStepTrace_deltaWitnessOfExactSub fp (v idx)
      (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))
      hsubExact

/-- Bound for the `y` operation's delta in the `i`th Kahan trace step. -/
theorem kahanTrace_deltaWitness_deltaY_bound (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    |(kahanTrace_deltaWitness fp v i).deltaY| ≤ fp.u :=
  (kahanTrace_deltaWitness fp v i).h_deltaY

/-- Bound for the `s` operation's delta in the `i`th Kahan trace step. -/
theorem kahanTrace_deltaWitness_deltaS_bound (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    |(kahanTrace_deltaWitness fp v i).deltaS| ≤ fp.u :=
  (kahanTrace_deltaWitness fp v i).h_deltaS

/-- Bound for the `temp - s` subtraction delta in the `i`th Kahan trace step. -/
theorem kahanTrace_deltaWitness_deltaSub_bound (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    |(kahanTrace_deltaWitness fp v i).deltaSub| ≤ fp.u :=
  (kahanTrace_deltaWitness fp v i).h_deltaSub

/-- Bound for the correction-addition delta in the `i`th Kahan trace step. -/
theorem kahanTrace_deltaWitness_deltaE_bound (fp : FPModel) {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    |(kahanTrace_deltaWitness fp v i).deltaE| ≤ fp.u :=
  (kahanTrace_deltaWitness fp v i).h_deltaE

end NumStability
