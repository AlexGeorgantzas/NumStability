-- Algorithms/Summation/Compensated/Kahan/Coefficients/Coupled.lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Algorithms.Summation.Compensated.Kahan.Internal.FinFold
import NumStability.Algorithms.Summation.Compensated.Kahan.LocalCoefficients

namespace NumStability

/-!
# Kahan compensated summation: coupled coefficients

This module develops the coupled stored-sum/correction coefficient recurrence,
including the actual-trace and supplied-witness realizations. Prefix witness
families remain owned by the Kahan local-coefficient layer.
-/

/-! ### Coupled returned-sum/correction coefficient recursion -/

/-- One coupled coefficient step for the direct Kahan `(s,e)` recurrence.

The step updates both the returned stored sum and the retained correction at
once, so later coefficient unrolls can preserve the cancellation between these
two fields instead of bounding the retained correction as an independent final
residual. -/
structure KahanCoupledCoeffStep where
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  x : ℝ

/-- Apply one coupled coefficient step to a stored-sum/correction pair. -/
def KahanCoupledCoeffStep.next
    (step : KahanCoupledCoeffStep) (state : KahanState) : KahanState :=
  { s := state.s * step.A + step.x * step.B + state.e * step.B
    e := state.s * step.C + (step.x + state.e) * step.D }

/-- Homogeneous propagation part of one coupled coefficient step, with the
new source input suppressed. -/
def KahanCoupledCoeffStep.propagate
    (step : KahanCoupledCoeffStep) (state : KahanState) : KahanState :=
  { s := state.s * step.A + state.e * step.B
    e := state.s * step.C + state.e * step.D }

/-- Source vector injected by one coupled coefficient step. -/
def KahanCoupledCoeffStep.source (step : KahanCoupledCoeffStep) : KahanState :=
  { s := step.x * step.B, e := step.x * step.D }

/-- Unit source-coefficient vector injected by one coupled coefficient step,
before multiplication by the input value. -/
def KahanCoupledCoeffStep.sourceCoeff
    (step : KahanCoupledCoeffStep) : KahanState :=
  { s := step.B, e := step.D }

/-- Coefficient multiplying the previous stored sum when the coupled step is
viewed through the compensated total `s+e`. -/
def KahanCoupledCoeffStep.totalStateCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.A + step.C

/-- Coefficient multiplying the current input and previous retained correction
when the coupled step is viewed through the compensated total `s+e`. -/
def KahanCoupledCoeffStep.totalInputCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.B + step.D

/-- Residual coefficient left when the coupled total recurrence is rewritten
around the previous compensated total `state.s + state.e`. -/
def KahanCoupledCoeffStep.residualCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.totalInputCoeff - step.totalStateCoeff

/-- Residual coefficient for the retained-correction row when the coupled step
is rewritten in `(compensated total, retained correction)` coordinates. -/
def KahanCoupledCoeffStep.correctionResidualCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.D - step.C

/-- Old paired-total coefficient used when recovering the returned stored sum
after one homogeneous step.  Algebraically this is the direct stored-sum
old-state coefficient `A`. -/
def KahanCoupledCoeffStep.returnedStateCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.totalStateCoeff - step.C

/-- Retained-correction coefficient used when recovering the returned stored
sum after one homogeneous step.  Algebraically this is `B - A`. -/
def KahanCoupledCoeffStep.returnedCorrectionCoeff
    (step : KahanCoupledCoeffStep) : ℝ :=
  step.residualCoeff - step.correctionResidualCoeff

/-- Homogeneous propagation in `(compensated total, retained correction)`
coordinates.  Here the input state's `s` field means the compensated total. -/
def KahanCoupledCoeffStep.propagateTotalCorrection
    (step : KahanCoupledCoeffStep) (state : KahanState) : KahanState :=
  { s := state.s * step.totalStateCoeff +
      state.e * step.residualCoeff
    e := state.s * step.C +
      state.e * step.correctionResidualCoeff }

/-- One coupled step is homogeneous propagation plus the current input source
vector. -/
theorem KahanCoupledCoeffStep.next_eq_propagate_add_source
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    step.next state =
      KahanState.add (step.propagate state) step.source := by
  ext <;>
    dsimp [KahanCoupledCoeffStep.next, KahanCoupledCoeffStep.propagate,
      KahanCoupledCoeffStep.source, KahanState.add] <;>
    ring

/-- The source vector is the input value times the unit source-coefficient
vector. -/
theorem KahanCoupledCoeffStep.source_eq_smul_sourceCoeff
    (step : KahanCoupledCoeffStep) :
    step.source = KahanState.smul step.x step.sourceCoeff := by
  rfl

/-- Unit source coefficient in `(compensated total, retained correction)`
coordinates. -/
theorem KahanCoupledCoeffStep.sourceCoeff_totalCorrection
    (step : KahanCoupledCoeffStep) :
    KahanState.totalCorrection step.sourceCoeff =
      { s := step.totalInputCoeff, e := step.D } := by
  ext <;>
    simp [KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff,
      KahanCoupledCoeffStep.totalInputCoeff]

/-- Total component of a coupled source vector. -/
theorem KahanCoupledCoeffStep.source_total
    (step : KahanCoupledCoeffStep) :
    step.source.s + step.source.e =
      step.x * step.totalInputCoeff := by
  dsimp [KahanCoupledCoeffStep.source,
    KahanCoupledCoeffStep.totalInputCoeff]
  ring

/-- Total component after homogeneous coupled propagation. -/
theorem KahanCoupledCoeffStep.propagate_total
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    (step.propagate state).s + (step.propagate state).e =
      state.s * step.totalStateCoeff +
        state.e * step.totalInputCoeff := by
  dsimp [KahanCoupledCoeffStep.propagate,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.totalInputCoeff]
  ring

/-- Homogeneous propagation commutes with the change of coordinates from
`(s,e)` to `(s+e,e)`. -/
theorem KahanCoupledCoeffStep.propagate_totalCorrection
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    KahanState.totalCorrection (step.propagate state) =
      step.propagateTotalCorrection
        (KahanState.totalCorrection state) := by
  ext <;>
    dsimp [KahanState.totalCorrection,
      KahanCoupledCoeffStep.propagate,
      KahanCoupledCoeffStep.propagateTotalCorrection,
      KahanCoupledCoeffStep.totalStateCoeff,
      KahanCoupledCoeffStep.totalInputCoeff,
      KahanCoupledCoeffStep.residualCoeff,
      KahanCoupledCoeffStep.correctionResidualCoeff] <;>
    ring

/-- The returned-coordinate old-state coefficient is exactly the direct
stored-sum coefficient `A`. -/
theorem KahanCoupledCoeffStep.returnedStateCoeff_eq_A
    (step : KahanCoupledCoeffStep) :
    step.returnedStateCoeff = step.A := by
  dsimp [KahanCoupledCoeffStep.returnedStateCoeff,
    KahanCoupledCoeffStep.totalStateCoeff]
  ring

/-- The returned-coordinate correction coefficient is exactly `B - A`. -/
theorem KahanCoupledCoeffStep.returnedCorrectionCoeff_eq_B_sub_A
    (step : KahanCoupledCoeffStep) :
    step.returnedCorrectionCoeff = step.B - step.A := by
  dsimp [KahanCoupledCoeffStep.returnedCorrectionCoeff,
    KahanCoupledCoeffStep.residualCoeff,
    KahanCoupledCoeffStep.correctionResidualCoeff,
    KahanCoupledCoeffStep.totalInputCoeff,
    KahanCoupledCoeffStep.totalStateCoeff]
  ring

/-- Returned stored-sum coordinate after paired-coordinate homogeneous
propagation.  This is the exact algebraic place where the ordinary returned
sum differs from the compensated-total route. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_returned
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    KahanState.returnedFromTotalCorrection
        (step.propagateTotalCorrection state) =
      state.s * step.returnedStateCoeff +
        state.e * step.returnedCorrectionCoeff := by
  dsimp [KahanState.returnedFromTotalCorrection,
    KahanCoupledCoeffStep.propagateTotalCorrection,
    KahanCoupledCoeffStep.returnedStateCoeff,
    KahanCoupledCoeffStep.returnedCorrectionCoeff,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.residualCoeff,
    KahanCoupledCoeffStep.correctionResidualCoeff]
  ring

/-- One-step radius inequality for the returned stored-sum component in paired
coordinates.  Unlike the compensated-total recurrence, the old-state
coefficient here is the direct stored-sum coefficient and therefore carries a
first-order radius in the current abstract model. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_returnedDev_abs_le_of_bounds
    (step : KahanCoupledCoeffStep) (state : KahanState)
    {eta theta : ℝ}
    (hState : |step.returnedStateCoeff - 1| ≤ eta)
    (hCorrection : |step.returnedCorrectionCoeff| ≤ theta) :
    |KahanState.returnedFromTotalCorrection
        (step.propagateTotalCorrection state) - 1| ≤
      |state.s - 1| * (1 + eta) + eta + |state.e| * theta := by
  rw [KahanCoupledCoeffStep.propagateTotalCorrection_returned]
  have hstateAbs : |step.returnedStateCoeff| ≤ 1 + eta := by
    calc
      |step.returnedStateCoeff| =
          |(step.returnedStateCoeff - 1) + 1| := by ring_nf
      _ ≤ |step.returnedStateCoeff - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ = |step.returnedStateCoeff - 1| + 1 := by norm_num
      _ ≤ eta + 1 := by nlinarith
      _ = 1 + eta := by ring
  have hrewrite :
      state.s * step.returnedStateCoeff +
          state.e * step.returnedCorrectionCoeff - 1 =
        (state.s - 1) * step.returnedStateCoeff +
          (step.returnedStateCoeff - 1) +
          state.e * step.returnedCorrectionCoeff := by
    ring
  rw [hrewrite]
  calc
    |(state.s - 1) * step.returnedStateCoeff +
        (step.returnedStateCoeff - 1) +
        state.e * step.returnedCorrectionCoeff|
        ≤ |(state.s - 1) * step.returnedStateCoeff +
            (step.returnedStateCoeff - 1)| +
            |state.e * step.returnedCorrectionCoeff| := abs_add_le _ _
    _ ≤ |(state.s - 1) * step.returnedStateCoeff| +
          |step.returnedStateCoeff - 1| +
          |state.e * step.returnedCorrectionCoeff| := by
        have h :=
          abs_add_le ((state.s - 1) * step.returnedStateCoeff)
            (step.returnedStateCoeff - 1)
        nlinarith
    _ = |state.s - 1| * |step.returnedStateCoeff| +
          |step.returnedStateCoeff - 1| +
          |state.e| * |step.returnedCorrectionCoeff| := by
        simp [abs_mul]
    _ ≤ |state.s - 1| * (1 + eta) + eta +
          |state.e| * theta := by
        have hfirst :
            |state.s - 1| * |step.returnedStateCoeff| ≤
              |state.s - 1| * (1 + eta) :=
          mul_le_mul_of_nonneg_left hstateAbs (abs_nonneg _)
        have hthird :
            |state.e| * |step.returnedCorrectionCoeff| ≤
              |state.e| * theta :=
          mul_le_mul_of_nonneg_left hCorrection (abs_nonneg _)
        nlinarith

/-- One-step radius inequality for the total component in paired
`(s+e,e)` coordinates.  This is the local induction inequality used by the
Goldberg-style coefficient route: the new total deviation is controlled by the
previous total deviation, the old-total coefficient deviation, and the retained
correction residual. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    |(step.propagateTotalCorrection state).s - 1| ≤
      |state.s - 1| * |step.totalStateCoeff| +
        |step.totalStateCoeff - 1| +
        |state.e| * |step.residualCoeff| := by
  dsimp [KahanCoupledCoeffStep.propagateTotalCorrection]
  let totalCoeff := step.totalStateCoeff
  let residual := step.residualCoeff
  have hrewrite :
      state.s * totalCoeff + state.e * residual - 1 =
        (state.s - 1) * totalCoeff + (totalCoeff - 1) +
          state.e * residual := by
    ring
  rw [hrewrite]
  calc
    |(state.s - 1) * totalCoeff + (totalCoeff - 1) +
        state.e * residual|
        ≤ |(state.s - 1) * totalCoeff + (totalCoeff - 1)| +
            |state.e * residual| := abs_add_le _ _
    _ ≤ |(state.s - 1) * totalCoeff| + |totalCoeff - 1| +
          |state.e * residual| := by
        have h :=
          abs_add_le ((state.s - 1) * totalCoeff) (totalCoeff - 1)
        nlinarith
    _ = |state.s - 1| * |step.totalStateCoeff| +
          |step.totalStateCoeff - 1| +
          |state.e| * |step.residualCoeff| := by
        simp [totalCoeff, residual, abs_mul]

/-- Bounded-coefficient form of
`KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le`. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le_of_bounds
    (step : KahanCoupledCoeffStep) (state : KahanState)
    {eta rho : ℝ}
    (hTotal : |step.totalStateCoeff - 1| ≤ eta)
    (hResidual : |step.residualCoeff| ≤ rho) :
    |(step.propagateTotalCorrection state).s - 1| ≤
      |state.s - 1| * (1 + eta) + eta + |state.e| * rho := by
  have hbase :=
    KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le
      step state
  have htotalAbs : |step.totalStateCoeff| ≤ 1 + eta := by
    calc
      |step.totalStateCoeff| =
          |(step.totalStateCoeff - 1) + 1| := by ring_nf
      _ ≤ |step.totalStateCoeff - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ = |step.totalStateCoeff - 1| + 1 := by norm_num
      _ ≤ eta + 1 := by nlinarith
      _ = 1 + eta := by ring
  have hfirst :
      |state.s - 1| * |step.totalStateCoeff| ≤
        |state.s - 1| * (1 + eta) :=
    mul_le_mul_of_nonneg_left htotalAbs (abs_nonneg _)
  have hthird :
      |state.e| * |step.residualCoeff| ≤ |state.e| * rho :=
    mul_le_mul_of_nonneg_left hResidual (abs_nonneg _)
  nlinarith

/-- One-step radius inequality for the retained-correction component in paired
`(s+e,e)` coordinates. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    |(step.propagateTotalCorrection state).e| ≤
      (|state.s - 1| + 1) * |step.C| +
        |state.e| * |step.correctionResidualCoeff| := by
  dsimp [KahanCoupledCoeffStep.propagateTotalCorrection]
  have hs_abs : |state.s| ≤ |state.s - 1| + 1 := by
    calc
      |state.s| = |(state.s - 1) + 1| := by ring_nf
      _ ≤ |state.s - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ = |state.s - 1| + 1 := by norm_num
  calc
    |state.s * step.C + state.e * step.correctionResidualCoeff|
        ≤ |state.s * step.C| +
            |state.e * step.correctionResidualCoeff| := abs_add_le _ _
    _ = |state.s| * |step.C| +
          |state.e| * |step.correctionResidualCoeff| := by
        simp [abs_mul]
    _ ≤ (|state.s - 1| + 1) * |step.C| +
          |state.e| * |step.correctionResidualCoeff| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hs_abs (abs_nonneg _))
          (le_refl _)

/-- Bounded-coefficient form of
`KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le`. -/
theorem KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le_of_bounds
    (step : KahanCoupledCoeffStep) (state : KahanState)
    {sigma chi : ℝ}
    (hC : |step.C| ≤ sigma)
    (hCorrectionResidual : |step.correctionResidualCoeff| ≤ chi) :
    |(step.propagateTotalCorrection state).e| ≤
      (|state.s - 1| + 1) * sigma + |state.e| * chi := by
  have hbase :=
    KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le
      step state
  have hfirst :
      (|state.s - 1| + 1) * |step.C| ≤
        (|state.s - 1| + 1) * sigma := by
    exact mul_le_mul_of_nonneg_left hC (by nlinarith [abs_nonneg (state.s - 1)])
  have hsecond :
      |state.e| * |step.correctionResidualCoeff| ≤ |state.e| * chi :=
    mul_le_mul_of_nonneg_left hCorrectionResidual (abs_nonneg _)
  nlinarith

/-- Total component after one coupled step, rewritten around the previous
compensated total plus the residual coefficient on the retained correction. -/
theorem KahanCoupledCoeffStep.next_total_eq_compensated_total
    (step : KahanCoupledCoeffStep) (state : KahanState) :
    (step.next state).s + (step.next state).e =
      step.totalStateCoeff * (state.s + state.e) +
        step.x * step.totalInputCoeff +
        state.e * step.residualCoeff := by
  dsimp [KahanCoupledCoeffStep.next,
    KahanCoupledCoeffStep.totalStateCoeff,
    KahanCoupledCoeffStep.totalInputCoeff,
    KahanCoupledCoeffStep.residualCoeff]
  ring

/-- Homogeneous coupled propagation is additive. -/
theorem KahanCoupledCoeffStep.propagate_add
    (step : KahanCoupledCoeffStep) (a b : KahanState) :
    step.propagate (KahanState.add a b) =
      KahanState.add (step.propagate a) (step.propagate b) := by
  ext <;>
    dsimp [KahanCoupledCoeffStep.propagate, KahanState.add] <;>
    ring

/-- Homogeneous coupled propagation commutes with scalar multiplication. -/
theorem KahanCoupledCoeffStep.propagate_smul
    (step : KahanCoupledCoeffStep) (c : ℝ) (state : KahanState) :
    step.propagate (KahanState.smul c state) =
      KahanState.smul c (step.propagate state) := by
  ext <;>
    dsimp [KahanCoupledCoeffStep.propagate, KahanState.smul] <;>
    ring

/-- Fold a list of coupled coefficient steps from an initial `(s,e)` state. -/
def kahanCoupledCoeffFold
    (steps : List KahanCoupledCoeffStep) (init : KahanState) : KahanState :=
  steps.foldl (fun state step => step.next state) init

/-- Homogeneous propagation through a list of coupled coefficient steps. -/
def kahanCoupledCoeffPropagate
    (steps : List KahanCoupledCoeffStep) (init : KahanState) : KahanState :=
  steps.foldl (fun state step => step.propagate state) init

/-- Homogeneous propagation through a list in
`(compensated total, retained correction)` coordinates. -/
def kahanCoupledTotalCorrectionPropagate
    (steps : List KahanCoupledCoeffStep) (init : KahanState) : KahanState :=
  steps.foldl (fun state step => step.propagateTotalCorrection state) init

/-- Goldberg's phantom final zero-input step in this file's sign convention.

Goldberg's proof of the compensated-summation coefficient bound appends a
formal zero input with exact local roundoff.  Since Higham's Algorithm 4.2 is
represented here with `y = x + e`, the exact zero step maps `(s,e)` to
`(s+e,0)`.  This theorem family is a source-route dependency for the remaining
equation (4.8) returned-sum coefficient collapse. -/
def kahanCoupledExactZeroStep : KahanCoupledCoeffStep :=
  { A := 1, B := 1, C := 0, D := 0, x := 0 }

/-- The phantom exact zero-input step maps `(s,e)` to `(s+e,0)`. -/
theorem kahanCoupledExactZeroStep_next (state : KahanState) :
    kahanCoupledExactZeroStep.next state =
      { s := state.s + state.e, e := 0 } := by
  ext <;>
    dsimp [kahanCoupledExactZeroStep, KahanCoupledCoeffStep.next] <;>
    ring

/-- The homogeneous part of the phantom exact zero-input step also maps
`(s,e)` to `(s+e,0)`. -/
theorem kahanCoupledExactZeroStep_propagate (state : KahanState) :
    kahanCoupledExactZeroStep.propagate state =
      { s := state.s + state.e, e := 0 } := by
  ext <;>
    dsimp [kahanCoupledExactZeroStep, KahanCoupledCoeffStep.propagate] <;>
    ring

/-- Appending Goldberg's exact zero-input step to a coupled fold turns the
final state into the compensated total with zero retained correction. -/
theorem kahanCoupledCoeffFold_append_exactZeroStep
    (steps : List KahanCoupledCoeffStep) (init : KahanState) :
    kahanCoupledCoeffFold (steps ++ [kahanCoupledExactZeroStep]) init =
      { s := (kahanCoupledCoeffFold steps init).s +
          (kahanCoupledCoeffFold steps init).e, e := 0 } := by
  unfold kahanCoupledCoeffFold
  rw [List.foldl_append]
  dsimp
  exact
    kahanCoupledExactZeroStep_next
      (steps.foldl (fun state step => step.next state) init)

/-- Appending Goldberg's exact zero-input step to homogeneous coefficient
propagation exposes the propagated compensated total in the returned-sum
component. -/
theorem kahanCoupledCoeffPropagate_append_exactZeroStep
    (steps : List KahanCoupledCoeffStep) (init : KahanState) :
    kahanCoupledCoeffPropagate (steps ++ [kahanCoupledExactZeroStep]) init =
      { s := (kahanCoupledCoeffPropagate steps init).s +
          (kahanCoupledCoeffPropagate steps init).e, e := 0 } := by
  unfold kahanCoupledCoeffPropagate
  rw [List.foldl_append]
  dsimp
  exact
    kahanCoupledExactZeroStep_propagate
      (steps.foldl (fun state step => step.propagate state) init)

/-- Product-form unroll of all source vectors in a coupled coefficient
recurrence.  The head source is propagated through all later steps; later
sources are accumulated recursively. -/
def kahanCoupledSourceUnroll : List KahanCoupledCoeffStep → KahanState
  | [] => KahanState.zero
  | step :: steps =>
      KahanState.add
        (kahanCoupledCoeffPropagate steps step.source)
        (kahanCoupledSourceUnroll steps)

/-- Homogeneous list propagation is additive. -/
theorem kahanCoupledCoeffPropagate_add
    (steps : List KahanCoupledCoeffStep) (a b : KahanState) :
    kahanCoupledCoeffPropagate steps (KahanState.add a b) =
      KahanState.add
        (kahanCoupledCoeffPropagate steps a)
        (kahanCoupledCoeffPropagate steps b) := by
  induction steps generalizing a b with
  | nil =>
      ext <;> dsimp [kahanCoupledCoeffPropagate, KahanState.add]
  | cons step steps ih =>
      dsimp [kahanCoupledCoeffPropagate]
      rw [KahanCoupledCoeffStep.propagate_add]
      exact ih (step.propagate a) (step.propagate b)

/-- Homogeneous list propagation commutes with scalar multiplication. -/
theorem kahanCoupledCoeffPropagate_smul
    (steps : List KahanCoupledCoeffStep) (c : ℝ) (state : KahanState) :
    kahanCoupledCoeffPropagate steps (KahanState.smul c state) =
      KahanState.smul c (kahanCoupledCoeffPropagate steps state) := by
  induction steps generalizing state with
  | nil =>
      ext <;> dsimp [kahanCoupledCoeffPropagate, KahanState.smul]
  | cons step steps ih =>
      dsimp [kahanCoupledCoeffPropagate]
      rw [KahanCoupledCoeffStep.propagate_smul]
      exact ih (step.propagate state)

/-- Homogeneous list propagation keeps the zero state zero. -/
theorem kahanCoupledCoeffPropagate_zero
    (steps : List KahanCoupledCoeffStep) :
    kahanCoupledCoeffPropagate steps KahanState.zero = KahanState.zero := by
  induction steps with
  | nil =>
      ext <;> dsimp [kahanCoupledCoeffPropagate, KahanState.zero]
  | cons step steps ih =>
      dsimp [kahanCoupledCoeffPropagate]
      have hstep :
          step.propagate KahanState.zero = KahanState.zero := by
        ext <;>
          dsimp [KahanCoupledCoeffStep.propagate, KahanState.zero] <;>
          ring
      rw [hstep]
      exact ih

/-- List propagation also commutes with the change from raw `(s,e)` to
`(s+e,e)` paired coordinates. -/
theorem kahanCoupledCoeffPropagate_totalCorrection_eq
    (steps : List KahanCoupledCoeffStep) (init : KahanState) :
    KahanState.totalCorrection
        (kahanCoupledCoeffPropagate steps init) =
      kahanCoupledTotalCorrectionPropagate steps
        (KahanState.totalCorrection init) := by
  induction steps generalizing init with
  | nil => rfl
  | cons step steps ih =>
      dsimp [kahanCoupledCoeffPropagate,
        kahanCoupledTotalCorrectionPropagate]
      have hih := ih (step.propagate init)
      dsimp [kahanCoupledCoeffPropagate,
        kahanCoupledTotalCorrectionPropagate] at hih
      rw [hih]
      rw [KahanCoupledCoeffStep.propagate_totalCorrection]

/-- Paired-coordinate coefficient majorant recurrence.

The `S` argument bounds the current total-coefficient deviation
`|totalCoeff - 1|`; the `E` argument bounds the retained-correction
coefficient.  Each list step applies the local paired inequalities with
constant bounds `eta`, `rho`, `sigma`, and `chi`. -/
def kahanCoupledPairedCoeffMajorant
    (eta rho sigma chi : ℝ) :
    List KahanCoupledCoeffStep → ℝ → ℝ → KahanState
  | [], S, E => { s := S, e := E }
  | _step :: steps, S, E =>
      kahanCoupledPairedCoeffMajorant eta rho sigma chi steps
        (S * (1 + eta) + eta + E * rho)
        ((S + 1) * sigma + E * chi)

/-- The paired-coordinate majorant has nonnegative components when started
from nonnegative radii and nonnegative update constants. -/
theorem kahanCoupledPairedCoeffMajorant_nonneg
    {eta rho sigma chi : ℝ}
    (heta : 0 ≤ eta) (hOneEta : 0 ≤ 1 + eta)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hchi : 0 ≤ chi) :
    ∀ (steps : List KahanCoupledCoeffStep) {S E : ℝ},
      0 ≤ S → 0 ≤ E →
      0 ≤ (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).s ∧
        0 ≤ (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).e
  | [], S, E, hS, hE => by
      simp [kahanCoupledPairedCoeffMajorant, hS, hE]
  | _step :: steps, S, E, hS, hE => by
      dsimp [kahanCoupledPairedCoeffMajorant]
      have hS' :
          0 ≤ S * (1 + eta) + eta + E * rho := by
        have hprodS : 0 ≤ S * (1 + eta) :=
          mul_nonneg hS hOneEta
        have hprodE : 0 ≤ E * rho := mul_nonneg hE hrho
        nlinarith
      have hE' :
          0 ≤ (S + 1) * sigma + E * chi := by
        have hS1 : 0 ≤ S + 1 := by nlinarith
        have hprodS : 0 ≤ (S + 1) * sigma :=
          mul_nonneg hS1 hsigma
        have hprodE : 0 ≤ E * chi := mul_nonneg hE hchi
        nlinarith
      exact
        kahanCoupledPairedCoeffMajorant_nonneg
          (eta := eta) (rho := rho) (sigma := sigma) (chi := chi)
          heta hOneEta hrho hsigma hchi steps hS' hE'

set_option maxHeartbeats 800000

/-- Conservative source-shaped collapse for the Kahan paired-coordinate
majorant.  If the initial total deviation is `2*u + A*u^2`, the initial
retained-correction coefficient is at most `12*u`, and the remaining suffix
has budget `(A + 200*m)*u <= 1`, then the propagated total deviation is at most
`2*u + (A + 200*m)*u^2` while the retained-correction coefficient stays
bounded by `12*u`.

The constants are deliberately loose: this is a dependency for the
Goldberg-style paired-coefficient route, not the final sharp hidden constant in
Higham's `O(n*u^2)`. -/
theorem kahanCoupledPairedCoeffMajorant_kahanConstants_le_two_u_plus
    {u A S E : ℝ}
    (hu0 : 0 ≤ u) (huSmall : u ≤ 1 / 64) (hA0 : 0 ≤ A) :
    ∀ (steps : List KahanCoupledCoeffStep),
      (A + 200 * (steps.length : ℝ)) * u ≤ 1 →
      S ≤ 2 * u + A * u ^ 2 →
      E ≤ 12 * u →
      let eta := 3 * u ^ 2
      let rho := 2 * u + 12 * u ^ 2
      let sigma := u * (1 + u) ^ 2
      let chi := u * (1 + u) ^ 2 * (3 + u)
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).s ≤
          2 * u + (A + 200 * (steps.length : ℝ)) * u ^ 2 ∧
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).e ≤
          12 * u
  | [], hBudget, hS, hE => by
      dsimp [kahanCoupledPairedCoeffMajorant]
      constructor
      · simpa using hS
      · exact hE
  | _step :: steps, hBudget, hS, hE => by
      dsimp [kahanCoupledPairedCoeffMajorant]
      have hu1 : u ≤ 1 := by nlinarith
      have hlen_nonneg : 0 ≤ (steps.length : ℝ) := by
        exact_mod_cast Nat.zero_le steps.length
      have hcons_len_nonneg :
          0 ≤ ((List.length (_step :: steps) : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_le (_step :: steps).length
      have hAu : A * u ≤ 1 := by
        have hle :
            A * u ≤ (A + 200 * (((_step :: steps).length : ℕ) : ℝ)) * u := by
          nlinarith [hu0, hcons_len_nonneg]
        exact hle.trans hBudget
      have hAu4 : A * u ^ 4 ≤ u ^ 3 := by
        have hu3_nonneg : 0 ≤ u ^ 3 := by nlinarith [hu0]
        have hmul := mul_le_mul_of_nonneg_right hAu hu3_nonneg
        nlinarith
      have hu3_le : u ^ 3 ≤ (1 / 64) * u ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right huSmall (sq_nonneg u)
        nlinarith
      have hOneEta : 0 ≤ 1 + 3 * u ^ 2 := by
        nlinarith [sq_nonneg u]
      have hrho_nonneg : 0 ≤ 2 * u + 12 * u ^ 2 := by
        nlinarith [hu0, sq_nonneg u]
      have hsigma_nonneg : 0 ≤ u * (1 + u) ^ 2 := by
        exact mul_nonneg hu0 (sq_nonneg (1 + u))
      have hchi_nonneg : 0 ≤ u * (1 + u) ^ 2 * (3 + u) := by
        exact mul_nonneg hsigma_nonneg (by nlinarith [hu0])
      have hsigma_le : u * (1 + u) ^ 2 ≤ 4 * u := by
        have h1u : 1 + u ≤ 2 := by nlinarith
        have h1u_nonneg : 0 ≤ 1 + u := by nlinarith
        have hsquare : (1 + u) ^ 2 ≤ 4 := by
          have hmul := mul_le_mul h1u h1u h1u_nonneg (by norm_num)
          nlinarith
        have hmul := mul_le_mul_of_nonneg_left hsquare hu0
        nlinarith
      have hchi_le : u * (1 + u) ^ 2 * (3 + u) ≤ 16 * u := by
        have h3u : 3 + u ≤ 4 := by nlinarith
        have h3u_nonneg : 0 ≤ 3 + u := by nlinarith [hu0]
        have h4u_nonneg : 0 ≤ 4 * u := by nlinarith [hu0]
        have hmul := mul_le_mul hsigma_le h3u h3u_nonneg h4u_nonneg
        nlinarith
      have hS_le_three_u : S ≤ 3 * u := by
        have hAu2 : A * u ^ 2 ≤ u := by
          have hmul := mul_le_mul_of_nonneg_right hAu hu0
          nlinarith
        nlinarith
      have hnextS :
          S * (1 + 3 * u ^ 2) + 3 * u ^ 2 +
              E * (2 * u + 12 * u ^ 2) ≤
            2 * u + (A + 200) * u ^ 2 := by
        have hS_mul :
            S * (1 + 3 * u ^ 2) ≤
              (2 * u + A * u ^ 2) * (1 + 3 * u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hS hOneEta
        have hE_mul :
            E * (2 * u + 12 * u ^ 2) ≤
              (12 * u) * (2 * u + 12 * u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hE hrho_nonneg
        nlinarith [hS_mul, hE_mul, hAu4, hu3_le]
      have hnextE :
          (S + 1) * (u * (1 + u) ^ 2) +
              E * (u * (1 + u) ^ 2 * (3 + u)) ≤
            12 * u := by
        have hS1 : S + 1 ≤ 1 + 3 * u := by nlinarith
        have hfirst :
            (S + 1) * (u * (1 + u) ^ 2) ≤
              (1 + 3 * u) * (4 * u) := by
          exact mul_le_mul hS1 hsigma_le hsigma_nonneg (by nlinarith)
        have hsecond :
            E * (u * (1 + u) ^ 2 * (3 + u)) ≤
              (12 * u) * (16 * u) := by
          exact mul_le_mul hE hchi_le hchi_nonneg (by nlinarith [hu0])
        have hu_sq_le : u ^ 2 ≤ (1 / 64) * u := by
          have hmul := mul_le_mul_of_nonneg_right huSmall hu0
          nlinarith
        nlinarith [hfirst, hsecond, hu_sq_le]
      have hBudgetTail :
          ((A + 200) + 200 * (steps.length : ℝ)) * u ≤ 1 := by
        have hEq :
            ((A + 200) + 200 * (steps.length : ℝ)) * u =
              (A + 200 * (((_step :: steps).length : ℕ) : ℝ)) * u := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring_nf
        rw [hEq]
        exact hBudget
      have htail :=
        kahanCoupledPairedCoeffMajorant_kahanConstants_le_two_u_plus
          (u := u) (A := A + 200)
          (S := S * (1 + 3 * u ^ 2) + 3 * u ^ 2 +
            E * (2 * u + 12 * u ^ 2))
          (E := (S + 1) * (u * (1 + u) ^ 2) +
            E * (u * (1 + u) ^ 2 * (3 + u)))
          hu0 huSmall (by nlinarith) steps hBudgetTail hnextS hnextE
      constructor
      · calc
          (kahanCoupledPairedCoeffMajorant (3 * u ^ 2)
              (2 * u + 12 * u ^ 2) (u * (1 + u) ^ 2)
              (u * (1 + u) ^ 2 * (3 + u)) steps
              (S * (1 + 3 * u ^ 2) + 3 * u ^ 2 +
                E * (2 * u + 12 * u ^ 2))
              ((S + 1) * (u * (1 + u) ^ 2) +
                E * (u * (1 + u) ^ 2 * (3 + u)))).s
              ≤ 2 * u + (A + 200 + 200 * (steps.length : ℝ)) * u ^ 2 :=
            htail.1
          _ = 2 * u + (A + 200 * (((steps.length + 1 : ℕ) : ℝ))) * u ^ 2 := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring_nf
      · exact htail.2

/-- Paired-majorant collapse for the exact-correction-subtraction route.

When the correction-subtraction delta is zero, the local correction residual
is second order.  With the listed constants, both paired coordinates stay
within `u + O(m*u^2)` through a suffix of length `m`.  The constants are loose
on purpose; the theorem is a reusable majorant dependency for the ordinary
returned Kahan sum. -/
theorem kahanCoupledPairedCoeffMajorant_exactSubConstants_le_one_u_plus
    {u A S E : ℝ}
    (hu0 : 0 ≤ u) (huSmall : u ≤ 1 / 64) (hA0 : 0 ≤ A) :
    ∀ (steps : List KahanCoupledCoeffStep),
      (A + 40 * (steps.length : ℝ)) * u ≤ 1 →
      S ≤ u + A * u ^ 2 →
      E ≤ u + A * u ^ 2 →
      let eta := u ^ 2
      let rho := u + u ^ 2
      let sigma := u + u ^ 2
      let chi := 2 * u ^ 2
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).s ≤
          u + (A + 40 * (steps.length : ℝ)) * u ^ 2 ∧
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).e ≤
          u + (A + 40 * (steps.length : ℝ)) * u ^ 2
  | [], _hBudget, hS, hE => by
      dsimp [kahanCoupledPairedCoeffMajorant]
      constructor <;> simpa using ‹_›
  | _step :: steps, hBudget, hS, hE => by
      dsimp [kahanCoupledPairedCoeffMajorant]
      have hu1 : u ≤ 1 := by nlinarith
      have hcons_len_nonneg :
          0 ≤ ((List.length (_step :: steps) : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_le (_step :: steps).length
      have hAu : A * u ≤ 1 := by
        have hle :
            A * u ≤ (A + 40 * (((_step :: steps).length : ℕ) : ℝ)) * u := by
          nlinarith [hu0, hcons_len_nonneg]
        exact hle.trans hBudget
      have hu3_le_u2 : u ^ 3 ≤ u ^ 2 := by
        have h :=
          mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
        nlinarith
      have hAu3 : A * u ^ 3 ≤ u ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hAu (sq_nonneg u)
        nlinarith
      have hAu4 : A * u ^ 4 ≤ u ^ 2 := by
        have hu3_nonneg : 0 ≤ u ^ 3 := by nlinarith [hu0]
        have hmul := mul_le_mul_of_nonneg_right hAu hu3_nonneg
        nlinarith [hmul, hu3_le_u2]
      have hOneEta : 0 ≤ 1 + u ^ 2 := by
        nlinarith [sq_nonneg u]
      have hrho_nonneg : 0 ≤ u + u ^ 2 := by
        nlinarith [hu0, sq_nonneg u]
      have hchi_nonneg : 0 ≤ 2 * u ^ 2 := by
        nlinarith [sq_nonneg u]
      have hnextS :
          S * (1 + u ^ 2) + u ^ 2 +
              E * (u + u ^ 2) ≤
            u + (A + 40) * u ^ 2 := by
        have hS_mul :
            S * (1 + u ^ 2) ≤
              (u + A * u ^ 2) * (1 + u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hS hOneEta
        have hE_mul :
            E * (u + u ^ 2) ≤
              (u + A * u ^ 2) * (u + u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hE hrho_nonneg
        nlinarith [hS_mul, hE_mul, hAu3, hAu4, hu3_le_u2]
      have hnextE :
          (S + 1) * (u + u ^ 2) + E * (2 * u ^ 2) ≤
            u + (A + 40) * u ^ 2 := by
        have hS1 : S + 1 ≤ 1 + u + A * u ^ 2 := by nlinarith
        have hfirst :
            (S + 1) * (u + u ^ 2) ≤
              (1 + u + A * u ^ 2) * (u + u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hS1 hrho_nonneg
        have hsecond :
            E * (2 * u ^ 2) ≤
              (u + A * u ^ 2) * (2 * u ^ 2) := by
          exact mul_le_mul_of_nonneg_right hE hchi_nonneg
        nlinarith [hfirst, hsecond, hAu3, hAu4, hu3_le_u2, hA0]
      have hBudgetTail :
          ((A + 40) + 40 * (steps.length : ℝ)) * u ≤ 1 := by
        have hEq :
            ((A + 40) + 40 * (steps.length : ℝ)) * u =
              (A + 40 * (((_step :: steps).length : ℕ) : ℝ)) * u := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring_nf
        rw [hEq]
        exact hBudget
      have htail :=
        kahanCoupledPairedCoeffMajorant_exactSubConstants_le_one_u_plus
          (u := u) (A := A + 40)
          (S := S * (1 + u ^ 2) + u ^ 2 + E * (u + u ^ 2))
          (E := (S + 1) * (u + u ^ 2) + E * (2 * u ^ 2))
          hu0 huSmall (by nlinarith) steps hBudgetTail hnextS hnextE
      constructor
      · calc
          (kahanCoupledPairedCoeffMajorant (u ^ 2)
              (u + u ^ 2) (u + u ^ 2) (2 * u ^ 2) steps
              (S * (1 + u ^ 2) + u ^ 2 + E * (u + u ^ 2))
              ((S + 1) * (u + u ^ 2) + E * (2 * u ^ 2))).s
              ≤ u + (A + 40 + 40 * (steps.length : ℝ)) * u ^ 2 :=
            htail.1
          _ = u + (A + 40 * (((steps.length + 1 : ℕ) : ℝ))) * u ^ 2 := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring_nf
      · calc
          (kahanCoupledPairedCoeffMajorant (u ^ 2)
              (u + u ^ 2) (u + u ^ 2) (2 * u ^ 2) steps
              (S * (1 + u ^ 2) + u ^ 2 + E * (u + u ^ 2))
              ((S + 1) * (u + u ^ 2) + E * (2 * u ^ 2))).e
              ≤ u + (A + 40 + 40 * (steps.length : ℝ)) * u ^ 2 :=
            htail.2
          _ = u + (A + 40 * (((steps.length + 1 : ℕ) : ℝ))) * u ^ 2 := by
            simp only [Nat.cast_add, Nat.cast_one]
            ring_nf

/-- Generic list-level paired-coordinate propagation bound.

If every step satisfies the local total-deviation and correction inequalities
with constants `eta`, `rho`, `sigma`, and `chi`, then propagation through the
whole list is bounded by `kahanCoupledPairedCoeffMajorant`. -/
theorem kahanCoupledTotalCorrectionPropagate_abs_le_pairedCoeffMajorant
    {eta rho sigma chi : ℝ}
    (heta : 0 ≤ eta) (hOneEta : 0 ≤ 1 + eta)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hchi : 0 ≤ chi)
    (steps : List KahanCoupledCoeffStep) (init : KahanState)
    {S E : ℝ}
    (hS0 : |init.s - 1| ≤ S) (hE0 : |init.e| ≤ E)
    (hS_nonneg : 0 ≤ S) (hE_nonneg : 0 ≤ E)
    (hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho)
    (hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi) :
    |(kahanCoupledTotalCorrectionPropagate steps init).s - 1| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).s ∧
      |(kahanCoupledTotalCorrectionPropagate steps init).e| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).e := by
  induction steps generalizing init S E with
  | nil =>
      simpa [kahanCoupledTotalCorrectionPropagate,
        kahanCoupledPairedCoeffMajorant] using And.intro hS0 hE0
  | cons step steps ih =>
      dsimp [kahanCoupledTotalCorrectionPropagate,
        kahanCoupledPairedCoeffMajorant]
      let next := step.propagateTotalCorrection init
      let S' := S * (1 + eta) + eta + E * rho
      let E' := (S + 1) * sigma + E * chi
      have hstepTotal :=
        hTotal step (by simp) init
      have hstepCorrection :=
        hCorrection step (by simp) init
      have hnextS : |next.s - 1| ≤ S' := by
        have hfirst :
            |init.s - 1| * (1 + eta) ≤ S * (1 + eta) :=
          mul_le_mul_of_nonneg_right hS0 hOneEta
        have hthird : |init.e| * rho ≤ E * rho :=
          mul_le_mul_of_nonneg_right hE0 hrho
        dsimp [next, S']
        nlinarith
      have hnextE : |next.e| ≤ E' := by
        have hfirst :
            (|init.s - 1| + 1) * sigma ≤ (S + 1) * sigma := by
          exact mul_le_mul_of_nonneg_right (by nlinarith) hsigma
        have hsecond : |init.e| * chi ≤ E * chi :=
          mul_le_mul_of_nonneg_right hE0 hchi
        dsimp [next, E']
        nlinarith
      have hS'_nonneg : 0 ≤ S' := by
        have hprodS : 0 ≤ S * (1 + eta) :=
          mul_nonneg hS_nonneg hOneEta
        have hprodE : 0 ≤ E * rho := mul_nonneg hE_nonneg hrho
        dsimp [S']
        nlinarith
      have hE'_nonneg : 0 ≤ E' := by
        have hS1 : 0 ≤ S + 1 := by nlinarith
        have hprodS : 0 ≤ (S + 1) * sigma :=
          mul_nonneg hS1 hsigma
        have hprodE : 0 ≤ E * chi := mul_nonneg hE_nonneg hchi
        dsimp [E']
        nlinarith
      have htailTotal :
          ∀ step' ∈ steps, ∀ state : KahanState,
            |(step'.propagateTotalCorrection state).s - 1| ≤
              |state.s - 1| * (1 + eta) + eta + |state.e| * rho := by
        intro step' hmem state
        exact hTotal step' (by simp [hmem]) state
      have htailCorrection :
          ∀ step' ∈ steps, ∀ state : KahanState,
            |(step'.propagateTotalCorrection state).e| ≤
              (|state.s - 1| + 1) * sigma + |state.e| * chi := by
        intro step' hmem state
        exact hCorrection step' (by simp [hmem]) state
      exact ih next hnextS hnextE hS'_nonneg hE'_nonneg
        htailTotal htailCorrection

/-- Generic coupled affine unroll: folding coupled steps equals the
homogeneous propagation of the initial state plus all propagated source
vectors. -/
theorem kahanCoupledCoeffFold_eq_propagate_add_sourceUnroll
    (steps : List KahanCoupledCoeffStep) (init : KahanState) :
    kahanCoupledCoeffFold steps init =
      KahanState.add
        (kahanCoupledCoeffPropagate steps init)
        (kahanCoupledSourceUnroll steps) := by
  induction steps generalizing init with
  | nil =>
      ext <;>
        dsimp [kahanCoupledCoeffFold, kahanCoupledCoeffPropagate,
          kahanCoupledSourceUnroll, KahanState.add, KahanState.zero] <;>
        ring
  | cons step steps ih =>
      dsimp [kahanCoupledCoeffFold, kahanCoupledCoeffPropagate,
        kahanCoupledSourceUnroll]
      have hih := ih (step.next init)
      dsimp [kahanCoupledCoeffFold] at hih
      rw [hih]
      rw [KahanCoupledCoeffStep.next_eq_propagate_add_source]
      rw [kahanCoupledCoeffPropagate_add]
      ext <;> dsimp [KahanState.add, kahanCoupledCoeffPropagate] <;>
        ring_nf

/-- Zero-initial coupled folds are exactly the propagated-source unroll. -/
theorem kahanCoupledCoeffFold_zero_eq_sourceUnroll
    (steps : List KahanCoupledCoeffStep) :
    kahanCoupledCoeffFold steps KahanState.zero =
      kahanCoupledSourceUnroll steps := by
  rw [kahanCoupledCoeffFold_eq_propagate_add_sourceUnroll]
  rw [kahanCoupledCoeffPropagate_zero]
  ext <;> dsimp [KahanState.add, KahanState.zero] <;> ring

/-- Source-vector unroll form of Goldberg's phantom exact zero-input step. -/
theorem kahanCoupledSourceUnroll_append_exactZeroStep
    (steps : List KahanCoupledCoeffStep) :
    kahanCoupledSourceUnroll (steps ++ [kahanCoupledExactZeroStep]) =
      { s := (kahanCoupledSourceUnroll steps).s +
          (kahanCoupledSourceUnroll steps).e, e := 0 } := by
  rw [← kahanCoupledCoeffFold_zero_eq_sourceUnroll
    (steps ++ [kahanCoupledExactZeroStep])]
  rw [kahanCoupledCoeffFold_append_exactZeroStep]
  rw [kahanCoupledCoeffFold_zero_eq_sourceUnroll]

/-- Per-input coupled source coefficient vector induced by the source-vector
unroll.  For the step at list index `i`, this is the unit source vector
propagated through all later coupled steps. -/
noncomputable def kahanCoupledSourceCoeff
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    KahanState :=
  kahanCoupledCoeffPropagate
    (steps.drop (i.val + 1)) (steps.get i).sourceCoeff

/-- Per-input coupled source coefficient in
`(compensated total, retained correction)` coordinates. -/
noncomputable def kahanCoupledSourceTotalCorrectionCoeff
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    KahanState :=
  KahanState.totalCorrection (kahanCoupledSourceCoeff steps i)

/-- The propagated source coefficient in paired coordinates is exactly the
source coefficient transformed to `(s+e,e)` and propagated by the transformed
list recurrence. -/
theorem kahanCoupledSourceCoeff_totalCorrection_eq
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    kahanCoupledSourceTotalCorrectionCoeff steps i =
      kahanCoupledTotalCorrectionPropagate
        (steps.drop (i.val + 1))
        (KahanState.totalCorrection (steps.get i).sourceCoeff) := by
  dsimp [kahanCoupledSourceTotalCorrectionCoeff, kahanCoupledSourceCoeff]
  exact kahanCoupledCoeffPropagate_totalCorrection_eq
    (steps.drop (i.val + 1)) (steps.get i).sourceCoeff

/-- Generic paired-majorant bound for a propagated source coefficient.  This
packages the list-level paired-coordinate induction at the exact place where a
source coefficient is propagated through all later coupled steps. -/
theorem kahanCoupledSourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
    {eta rho sigma chi : ℝ}
    (heta : 0 ≤ eta) (hOneEta : 0 ≤ 1 + eta)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hchi : 0 ≤ chi)
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length)
    {S E : ℝ}
    (hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤ S)
    (hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤ E)
    (hS_nonneg : 0 ≤ S) (hE_nonneg : 0 ≤ E)
    (hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho)
    (hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi) :
    |(kahanCoupledSourceTotalCorrectionCoeff steps i).s - 1| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi
          (steps.drop (i.val + 1)) S E).s ∧
      |(kahanCoupledSourceTotalCorrectionCoeff steps i).e| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi
          (steps.drop (i.val + 1)) S E).e := by
  have htailTotal :
      ∀ step ∈ steps.drop (i.val + 1), ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho := by
    intro step hmem state
    exact hTotal step (List.mem_of_mem_drop hmem) state
  have htailCorrection :
      ∀ step ∈ steps.drop (i.val + 1), ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi := by
    intro step hmem state
    exact hCorrection step (List.mem_of_mem_drop hmem) state
  have hprop :=
    kahanCoupledTotalCorrectionPropagate_abs_le_pairedCoeffMajorant
      (eta := eta) (rho := rho) (sigma := sigma) (chi := chi)
      heta hOneEta hrho hsigma hchi
      (steps.drop (i.val + 1))
      (KahanState.totalCorrection (steps.get i).sourceCoeff)
      hS0 hE0 hS_nonneg hE_nonneg htailTotal htailCorrection
  simpa [kahanCoupledSourceCoeff_totalCorrection_eq steps i] using hprop

/-- Generic triangle-route bound for a returned source coefficient.

This is the formal version of the weak route that bounds the ordinary returned
coefficient by the paired total deviation plus the retained-correction
coefficient.  It is useful as an audit theorem, but by itself it preserves a
first-order correction term and therefore does not close Higham equation (4.8)'s
`2*u + O(n*u^2)` coefficient. -/
theorem kahanCoupledSourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum
    {eta rho sigma chi : ℝ}
    (heta : 0 ≤ eta) (hOneEta : 0 ≤ 1 + eta)
    (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) (hchi : 0 ≤ chi)
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length)
    {S E : ℝ}
    (hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤ S)
    (hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤ E)
    (hS_nonneg : 0 ≤ S) (hE_nonneg : 0 ≤ E)
    (hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho)
    (hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi) :
    |(kahanCoupledSourceCoeff steps i).s - 1| ≤
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi
        (steps.drop (i.val + 1)) S E).s +
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi
        (steps.drop (i.val + 1)) S E).e := by
  have hpair :=
    kahanCoupledSourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
      (eta := eta) (rho := rho) (sigma := sigma) (chi := chi)
      heta hOneEta hrho hsigma hchi steps i
      hS0 hE0 hS_nonneg hE_nonneg hTotal hCorrection
  let a := kahanCoupledSourceCoeff steps i
  have htri :
      |a.s - 1| ≤
        |(KahanState.totalCorrection a).s - 1| +
          |(KahanState.totalCorrection a).e| := by
    have hrewrite :
        a.s - 1 = (a.s + a.e - 1) - a.e := by ring
    rw [hrewrite]
    simpa [KahanState.totalCorrection, sub_eq_add_neg, abs_neg] using
      abs_add_le (a.s + a.e - 1) (-a.e)
  exact htri.trans (add_le_add hpair.1 hpair.2)

/-- Generic returned-coefficient collapse for the exact-subtraction local
constants.

If the source coefficient starts with both paired coordinates bounded by
`u + A*u^2`, and every later step satisfies the exact-subtraction paired
inequalities, then the ordinary returned source coefficient has the
source-shaped radius `2*u + O(m*u^2)`. -/
theorem kahanCoupledSourceCoeff_s_abs_sub_one_le_exactSubMajorant
    {u A S E : ℝ}
    (hu0 : 0 ≤ u) (huSmall : u ≤ 1 / 64) (hA0 : 0 ≤ A)
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length)
    (hBudget :
      (A + 40 * ((steps.drop (i.val + 1)).length : ℝ)) * u ≤ 1)
    (hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤ S)
    (hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤ E)
    (hS_nonneg : 0 ≤ S) (hE_nonneg : 0 ≤ E)
    (hS_le : S ≤ u + A * u ^ 2)
    (hE_le : E ≤ u + A * u ^ 2)
    (hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + u ^ 2) + u ^ 2 +
            |state.e| * (u + u ^ 2))
    (hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * (u + u ^ 2) +
            |state.e| * (2 * u ^ 2)) :
    |(kahanCoupledSourceCoeff steps i).s - 1| ≤
      2 * u +
        2 * (A + 40 * ((steps.drop (i.val + 1)).length : ℝ)) *
          u ^ 2 := by
  let suffix := steps.drop (i.val + 1)
  have hOneEta : 0 ≤ 1 + u ^ 2 := by
    nlinarith [sq_nonneg u]
  have hrho : 0 ≤ u + u ^ 2 := by
    nlinarith [hu0, sq_nonneg u]
  have hchi : 0 ≤ 2 * u ^ 2 := by
    nlinarith [sq_nonneg u]
  have hmajorant :=
    kahanCoupledSourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum
      (eta := u ^ 2) (rho := u + u ^ 2)
      (sigma := u + u ^ 2) (chi := 2 * u ^ 2)
      (by nlinarith [sq_nonneg u]) hOneEta hrho hrho hchi
      steps i hS0 hE0 hS_nonneg hE_nonneg hTotal hCorrection
  have hcollapse :=
    kahanCoupledPairedCoeffMajorant_exactSubConstants_le_one_u_plus
      (u := u) (A := A) (S := S) (E := E)
      hu0 huSmall hA0 suffix
      (by simpa [suffix] using hBudget) hS_le hE_le
  calc
    |(kahanCoupledSourceCoeff steps i).s - 1|
        ≤ (kahanCoupledPairedCoeffMajorant (u ^ 2) (u + u ^ 2)
            (u + u ^ 2) (2 * u ^ 2) suffix S E).s +
          (kahanCoupledPairedCoeffMajorant (u ^ 2) (u + u ^ 2)
            (u + u ^ 2) (2 * u ^ 2) suffix S E).e := by
          simpa [suffix] using hmajorant
    _ ≤ (u + (A + 40 * (suffix.length : ℝ)) * u ^ 2) +
          (u + (A + 40 * (suffix.length : ℝ)) * u ^ 2) := by
          exact add_le_add hcollapse.1 hcollapse.2
    _ = 2 * u + 2 * (A + 40 * (suffix.length : ℝ)) * u ^ 2 := by
          ring
    _ = 2 * u +
        2 * (A + 40 * ((steps.drop (i.val + 1)).length : ℝ)) *
          u ^ 2 := by
          simp [suffix]

/-- Returned-stored-sum component of the coupled source-vector unroll as an
explicit per-input coefficient sum. -/
theorem kahanCoupledSourceUnroll_s_eq_sum_sourceCoeff
    (steps : List KahanCoupledCoeffStep) :
    (kahanCoupledSourceUnroll steps).s =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).s := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
      dsimp [kahanCoupledSourceUnroll, KahanState.add]
      change
        (kahanCoupledCoeffPropagate steps step.source).s +
            (kahanCoupledSourceUnroll steps).s =
          ∑ i : Fin (steps.length + 1),
            ((step :: steps).get i).x *
              (kahanCoupledSourceCoeff (step :: steps) i).s
      conv_rhs => rw [Fin.sum_univ_succ]
      rw [ih]
      have hprop :
          kahanCoupledCoeffPropagate steps step.source =
            KahanState.smul step.x
              (kahanCoupledCoeffPropagate steps step.sourceCoeff) := by
        rw [KahanCoupledCoeffStep.source_eq_smul_sourceCoeff]
        exact kahanCoupledCoeffPropagate_smul
          steps step.x step.sourceCoeff
      rw [hprop]
      simp [kahanCoupledSourceCoeff, KahanState.smul]

/-- Retained-correction component of the coupled source-vector unroll as an
explicit per-input coefficient sum. -/
theorem kahanCoupledSourceUnroll_e_eq_sum_sourceCoeff
    (steps : List KahanCoupledCoeffStep) :
    (kahanCoupledSourceUnroll steps).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).e := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
      dsimp [kahanCoupledSourceUnroll, KahanState.add]
      change
        (kahanCoupledCoeffPropagate steps step.source).e +
            (kahanCoupledSourceUnroll steps).e =
          ∑ i : Fin (steps.length + 1),
            ((step :: steps).get i).x *
              (kahanCoupledSourceCoeff (step :: steps) i).e
      conv_rhs => rw [Fin.sum_univ_succ]
      rw [ih]
      have hprop :
          kahanCoupledCoeffPropagate steps step.source =
            KahanState.smul step.x
              (kahanCoupledCoeffPropagate steps step.sourceCoeff) := by
        rw [KahanCoupledCoeffStep.source_eq_smul_sourceCoeff]
        exact kahanCoupledCoeffPropagate_smul
          steps step.x step.sourceCoeff
      rw [hprop]
      simp [kahanCoupledSourceCoeff, KahanState.smul]

/-- Paired source coefficient for the compensated total `s+e`.  In the
Goldberg/Knuth route this is the coefficient of the cancellation-preserving
quantity corresponding to `S-C` once the sign convention for the retained
correction is translated to Higham's Algorithm 4.2. -/
noncomputable def kahanCoupledSourceTotalCoeff
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) : ℝ :=
  (kahanCoupledSourceCoeff steps i).s +
    (kahanCoupledSourceCoeff steps i).e

/-- For an original input index, appending Goldberg's phantom exact zero-input
step makes the new returned-sum coefficient equal to the old compensated-total
coefficient. -/
theorem kahanCoupledSourceCoeff_append_exactZeroStep_s_eq_sourceTotalCoeff
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceCoeff (steps ++ [kahanCoupledExactZeroStep])
      ⟨i.val, by
        simp [List.length_append]⟩).s =
      kahanCoupledSourceTotalCoeff steps i := by
  dsimp [kahanCoupledSourceCoeff, kahanCoupledSourceTotalCoeff]
  have hle : i.val + 1 ≤ steps.length := Nat.succ_le_of_lt i.isLt
  rw [List.drop_append_of_le_length hle]
  simp [kahanCoupledCoeffPropagate_append_exactZeroStep]

/-- For an original input index, appending Goldberg's phantom exact zero-input
step leaves zero retained-correction coefficient in the appended recurrence. -/
theorem kahanCoupledSourceCoeff_append_exactZeroStep_e_eq_zero
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceCoeff (steps ++ [kahanCoupledExactZeroStep])
      ⟨i.val, by
        simp [List.length_append]⟩).e = 0 := by
  dsimp [kahanCoupledSourceCoeff]
  have hle : i.val + 1 ≤ steps.length := Nat.succ_le_of_lt i.isLt
  rw [List.drop_append_of_le_length hle]
  simp [kahanCoupledCoeffPropagate_append_exactZeroStep]

/-- The `s` field of the paired-coordinate source coefficient is the
compensated-total source coefficient. -/
theorem kahanCoupledSourceTotalCorrectionCoeff_s
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceTotalCorrectionCoeff steps i).s =
      kahanCoupledSourceTotalCoeff steps i := by
  rfl

/-- The `e` field of the paired-coordinate source coefficient is the retained
correction source coefficient. -/
theorem kahanCoupledSourceTotalCorrectionCoeff_e
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceTotalCorrectionCoeff steps i).e =
      (kahanCoupledSourceCoeff steps i).e := by
  rfl

/-- The compensated-total source coefficient is the total component of the
transformed propagated source recurrence. -/
theorem kahanCoupledSourceTotalCoeff_eq_totalCorrectionPropagate_s
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    kahanCoupledSourceTotalCoeff steps i =
      (kahanCoupledTotalCorrectionPropagate
        (steps.drop (i.val + 1))
        (KahanState.totalCorrection (steps.get i).sourceCoeff)).s := by
  rw [← kahanCoupledSourceTotalCorrectionCoeff_s]
  rw [kahanCoupledSourceCoeff_totalCorrection_eq]

/-- The retained-correction source coefficient is the correction component of
the transformed propagated source recurrence. -/
theorem kahanCoupledSourceCoeff_e_eq_totalCorrectionPropagate_e
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceCoeff steps i).e =
      (kahanCoupledTotalCorrectionPropagate
        (steps.drop (i.val + 1))
        (KahanState.totalCorrection (steps.get i).sourceCoeff)).e := by
  rw [← kahanCoupledSourceTotalCorrectionCoeff_e]
  rw [kahanCoupledSourceCoeff_totalCorrection_eq]

/-- The returned stored-sum source coefficient is the returned coordinate of
the paired-coordinate propagated source coefficient.

This is the exact bridge from the paired `(s+e,e)` propagation recurrence to
the ordinary returned coefficient needed for Higham equation (4.8). -/
theorem kahanCoupledSourceCoeff_s_eq_returned_totalCorrectionPropagate
    (steps : List KahanCoupledCoeffStep) (i : Fin steps.length) :
    (kahanCoupledSourceCoeff steps i).s =
      KahanState.returnedFromTotalCorrection
        (kahanCoupledTotalCorrectionPropagate
          (steps.drop (i.val + 1))
          (KahanState.totalCorrection (steps.get i).sourceCoeff)) := by
  rw [← kahanCoupledSourceCoeff_totalCorrection_eq steps i]
  dsimp [kahanCoupledSourceTotalCorrectionCoeff]
  exact (KahanState.returnedFromTotalCorrection_totalCorrection
    (kahanCoupledSourceCoeff steps i)).symm

/-- Compensated-total component of the coupled source-vector unroll as an
explicit per-input paired-coefficient sum. -/
theorem kahanCoupledSourceUnroll_total_eq_sum_sourceTotalCoeff
    (steps : List KahanCoupledCoeffStep) :
    (kahanCoupledSourceUnroll steps).s +
        (kahanCoupledSourceUnroll steps).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * kahanCoupledSourceTotalCoeff steps i := by
  rw [kahanCoupledSourceUnroll_s_eq_sum_sourceCoeff,
    kahanCoupledSourceUnroll_e_eq_sum_sourceCoeff]
  calc
    (∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).s) +
        (∑ i : Fin steps.length,
          (steps.get i).x * (kahanCoupledSourceCoeff steps i).e) =
      ∑ i : Fin steps.length,
        ((steps.get i).x * (kahanCoupledSourceCoeff steps i).s +
          (steps.get i).x * (kahanCoupledSourceCoeff steps i).e) := by
        rw [Finset.sum_add_distrib]
    _ = ∑ i : Fin steps.length,
        (steps.get i).x * kahanCoupledSourceTotalCoeff steps i := by
        apply Finset.sum_congr rfl
        intro i _hi
        dsimp [kahanCoupledSourceTotalCoeff]
        ring

/-- The coupled direct coefficient step induced by one indexed Kahan
prefix-trace step, using an explicit roundoff-witness bundle.

This witness-parametric surface is the exact-subtraction route for Higham
equation (4.8): later finite-format work can provide witnesses whose
correction-subtraction delta is definitionally zero, instead of relying on the
arbitrary `Classical.choice` witness used by `kahanTrace_deltaWitness`. -/
def kahanCoupledCoeffStepOfWitness
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    KahanCoupledCoeffStep :=
  { A := kahanStoredSumStateCoeff w.deltaS
    B := kahanStoredSumInputCoeff w.deltaY w.deltaS
    C := kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE
    D := kahanCorrectionInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE
    x := v i }

/-- The explicit-witness coupled step's total old-state coefficient is the
named compensated-total old-state coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_totalStateCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    (kahanCoupledCoeffStepOfWitness fp v i w).totalStateCoeff =
      kahanTotalStateCoeff w.deltaS w.deltaSub w.deltaE := by
  dsimp [kahanCoupledCoeffStepOfWitness,
    KahanCoupledCoeffStep.totalStateCoeff,
    kahanStoredSumStateCoeff, kahanCorrectionStateCoeff,
    kahanTotalStateCoeff]
  ring

/-- The explicit-witness coupled step's total current-input coefficient is the
named compensated-total current-input coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_totalInputCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    (kahanCoupledCoeffStepOfWitness fp v i w).totalInputCoeff =
      kahanTotalInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE := by
  dsimp [kahanCoupledCoeffStepOfWitness,
    KahanCoupledCoeffStep.totalInputCoeff,
    kahanStoredSumInputCoeff, kahanCorrectionInputCoeff,
    kahanTotalInputCoeff]
  ring

/-- The explicit-witness coupled step's paired-total residual coefficient is
the named Kahan total residual coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_residualCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    (kahanCoupledCoeffStepOfWitness fp v i w).residualCoeff =
      kahanTotalResidualCoeff w.deltaY w.deltaS w.deltaSub w.deltaE := by
  rw [KahanCoupledCoeffStep.residualCoeff,
    kahanCoupledCoeffStepOfWitness_totalInputCoeff_eq,
    kahanCoupledCoeffStepOfWitness_totalStateCoeff_eq]
  rfl

/-- General explicit-witness correction-residual cancellation: the coupled
correction residual differs from `-deltaSub` only by a second-order local
remainder. -/
theorem kahanCoupledCoeffStepOfWitness_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).correctionResidualCoeff +
        w.deltaSub| ≤
      7 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfWitness,
    KahanCoupledCoeffStep.correctionResidualCoeff] using
    kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_abs_le_seven_u_sq
      (deltaY := w.deltaY) (deltaS := w.deltaS)
      (deltaSub := w.deltaSub) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS
      w.h_deltaSub w.h_deltaE

/-- General explicit-witness relation between the paired-total residual and
the correction residual: their difference is `deltaY + O(u^2)`. -/
theorem kahanCoupledCoeffStepOfWitness_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).residualCoeff -
        (kahanCoupledCoeffStepOfWitness fp v i w).correctionResidualCoeff -
        w.deltaY| ≤
      fp.u ^ 2 := by
  have hrewrite :
      (kahanCoupledCoeffStepOfWitness fp v i w).residualCoeff -
          (kahanCoupledCoeffStepOfWitness fp v i w).correctionResidualCoeff -
          w.deltaY =
        w.deltaY * w.deltaS := by
    dsimp [kahanCoupledCoeffStepOfWitness,
      KahanCoupledCoeffStep.residualCoeff,
      KahanCoupledCoeffStep.correctionResidualCoeff,
      KahanCoupledCoeffStep.totalInputCoeff,
      KahanCoupledCoeffStep.totalStateCoeff,
      kahanStoredSumInputCoeff, kahanStoredSumStateCoeff]
    ring
  rw [hrewrite]
  calc
    |w.deltaY * w.deltaS| = |w.deltaY| * |w.deltaS| := by rw [abs_mul]
    _ ≤ fp.u * fp.u :=
      mul_le_mul w.h_deltaY w.h_deltaS (abs_nonneg _) fp.u_nonneg
    _ = fp.u ^ 2 := by ring

/-- General explicit-witness combined residual cancellation: the paired-total
residual is `deltaY - deltaSub` up to a second-order local remainder. -/
theorem kahanCoupledCoeffStepOfWitness_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).residualCoeff +
        w.deltaSub - w.deltaY| ≤
      8 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfWitness_residualCoeff_eq]
  exact
    kahanTotalResidualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
      (deltaY := w.deltaY) (deltaS := w.deltaS)
      (deltaSub := w.deltaSub) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS
      w.h_deltaSub w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
paired-total old-state coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_totalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).totalStateCoeff - 1| ≤
      fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfWitness_totalStateCoeff_eq, hSubZero]
  exact
    kahanTotalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
      (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg w.h_deltaS w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
paired-total current-input coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).totalInputCoeff - 1| ≤
      fp.u + 2 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfWitness_totalInputCoeff_eq, hSubZero]
  exact
    kahanTotalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
      (deltaY := w.deltaY) (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
paired-total retained-correction residual. -/
theorem kahanCoupledCoeffStepOfWitness_residualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).residualCoeff| ≤
      fp.u + fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfWitness_residualCoeff_eq, hSubZero]
  exact
    kahanTotalResidualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      (deltaY := w.deltaY) (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
correction old-total coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_C_abs_le_u_plus_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).C| ≤
      fp.u + fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfWitness, hSubZero] using
    kahanCorrectionStateCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg w.h_deltaS w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
correction current-input coefficient. -/
theorem kahanCoupledCoeffStepOfWitness_D_abs_le_u_plus_three_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).D| ≤
      fp.u + 3 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfWitness, hSubZero] using
    kahanCorrectionInputCoeff_abs_le_u_plus_three_u_sq_of_deltaSub_zero
      (deltaY := w.deltaY) (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS w.h_deltaE

/-- Exact-subtraction local bound for an explicit-witness coupled Kahan step's
paired correction residual. -/
theorem kahanCoupledCoeffStepOfWitness_correctionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)))
    (hu1 : fp.u ≤ 1) (hSubZero : w.deltaSub = 0) :
    |(kahanCoupledCoeffStepOfWitness fp v i w).correctionResidualCoeff| ≤
      2 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfWitness,
    KahanCoupledCoeffStep.correctionResidualCoeff, hSubZero] using
    kahanCorrectionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
      (deltaY := w.deltaY) (deltaS := w.deltaS) (deltaE := w.deltaE)
      (u := fp.u) fp.u_nonneg hu1 w.h_deltaY w.h_deltaS w.h_deltaE

/-- One indexed Kahan prefix-trace step satisfies the coupled direct
stored-sum/correction coefficient recurrence for any valid explicit
roundoff-witness bundle. -/
theorem kahanTrace_eq_coupledCoeffStepOfWitness_next
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (w : KahanStepDeltaWitness fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    let step := kahanCoupledCoeffStepOfWitness fp v i w
    (kahanTrace fp v i).nextState = step.next state := by
  have hs :=
    kahanStepDeltaWitness_s_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)) w
  have he :=
    kahanStepDeltaWitness_e_coefficients fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)) w
  dsimp [KahanStepTrace.nextState, KahanCoupledCoeffStep.next,
    kahanCoupledCoeffStepOfWitness, kahanTrace]
  rw [hs, he]

/-- The coupled direct coefficient step induced by one indexed Kahan
prefix-trace step. -/
noncomputable def kahanCoupledCoeffStepOfIndex
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    KahanCoupledCoeffStep :=
  let w := kahanTrace_deltaWitness fp v i
  { A := kahanStoredSumStateCoeff w.deltaS
    B := kahanStoredSumInputCoeff w.deltaY w.deltaS
    C := kahanCorrectionStateCoeff w.deltaS w.deltaSub w.deltaE
    D := kahanCorrectionInputCoeff w.deltaY w.deltaS w.deltaSub w.deltaE
    x := v i }

/-- The coupled step's total old-state coefficient is the already named
compensated-total old-state coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_totalStateCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (kahanCoupledCoeffStepOfIndex fp v i).totalStateCoeff =
      kahanTotalStateCoeff
        (kahanTrace_deltaWitness fp v i).deltaS
        (kahanTrace_deltaWitness fp v i).deltaSub
        (kahanTrace_deltaWitness fp v i).deltaE := by
  dsimp [kahanCoupledCoeffStepOfIndex,
    KahanCoupledCoeffStep.totalStateCoeff,
    kahanStoredSumStateCoeff, kahanCorrectionStateCoeff,
    kahanTotalStateCoeff]
  ring

/-- The coupled step's total current-input coefficient is the already named
compensated-total current-input coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_totalInputCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (kahanCoupledCoeffStepOfIndex fp v i).totalInputCoeff =
      kahanTotalInputCoeff
        (kahanTrace_deltaWitness fp v i).deltaY
        (kahanTrace_deltaWitness fp v i).deltaS
        (kahanTrace_deltaWitness fp v i).deltaSub
        (kahanTrace_deltaWitness fp v i).deltaE := by
  dsimp [kahanCoupledCoeffStepOfIndex,
    KahanCoupledCoeffStep.totalInputCoeff,
    kahanStoredSumInputCoeff, kahanCorrectionInputCoeff,
    kahanTotalInputCoeff]
  ring

/-- The coupled step's total residual coefficient is the retained-correction
residual coefficient already used by the residual-aware affine route. -/
theorem kahanCoupledCoeffStepOfIndex_residualCoeff_eq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (kahanCoupledCoeffStepOfIndex fp v i).residualCoeff =
      kahanTotalResidualCoeff
        (kahanTrace_deltaWitness fp v i).deltaY
        (kahanTrace_deltaWitness fp v i).deltaS
        (kahanTrace_deltaWitness fp v i).deltaSub
        (kahanTrace_deltaWitness fp v i).deltaE := by
  rw [KahanCoupledCoeffStep.residualCoeff,
    kahanCoupledCoeffStepOfIndex_totalInputCoeff_eq,
    kahanCoupledCoeffStepOfIndex_totalStateCoeff_eq]
  rfl

/-- Actual-prefix version of the general correction-residual cancellation:
the paired correction residual differs from the negated subtraction delta only
by a second-order local remainder. -/
theorem kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfIndex fp v i).correctionResidualCoeff +
        (kahanTrace_deltaWitness fp v i).deltaSub| ≤
      7 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex,
    KahanCoupledCoeffStep.correctionResidualCoeff] using
    kahanCorrectionInputCoeff_sub_stateCoeff_add_deltaSub_abs_le_seven_u_sq
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Actual-prefix relation between the paired-total residual and the
correction residual: their difference is the input-addition delta plus a
second-order local remainder. -/
theorem kahanCoupledCoeffStepOfIndex_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).residualCoeff -
        (kahanCoupledCoeffStepOfIndex fp v i).correctionResidualCoeff -
        (kahanTrace_deltaWitness fp v i).deltaY| ≤
      fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanCoupledCoeffStepOfWitness_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
      fp v i (kahanTrace_deltaWitness fp v i)

/-- Actual-prefix combined residual cancellation: the paired-total residual is
`deltaY - deltaSub` up to a second-order local remainder. -/
theorem kahanCoupledCoeffStepOfIndex_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfIndex fp v i).residualCoeff +
        (kahanTrace_deltaWitness fp v i).deltaSub -
        (kahanTrace_deltaWitness fp v i).deltaY| ≤
      8 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanCoupledCoeffStepOfWitness_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
      fp v i (kahanTrace_deltaWitness fp v i) hu1

/-- The total old-state coefficient of an actual coupled Kahan step differs
from one by at most `3*u^2`. -/
theorem kahanCoupledCoeffStepOfIndex_totalStateCoeff_abs_sub_one_le_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfIndex fp v i).totalStateCoeff - 1| ≤
      3 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_totalStateCoeff_eq]
  exact
    kahanTotalStateCoeff_abs_sub_one_le_three_u_sq
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The total current-input coefficient of an actual coupled Kahan step differs
from one by at most `2*u + 9*u^2`. -/
theorem kahanCoupledCoeffStepOfIndex_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfIndex fp v i).totalInputCoeff - 1| ≤
      2 * fp.u + 9 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_totalInputCoeff_eq]
  exact
    kahanTotalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The total residual coefficient of an actual coupled Kahan step satisfies
the same small-`u` residual bound as the affine route. -/
theorem kahanCoupledCoeffStepOfIndex_residualCoeff_abs_le_two_u_plus_twelve_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1) :
    |(kahanCoupledCoeffStepOfIndex fp v i).residualCoeff| ≤
      2 * fp.u + 12 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_residualCoeff_eq]
  exact
    kahanTotalResidualCoeff_abs_le_two_u_plus_twelve_u_sq
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The correction-total coefficient `C` of an actual coupled Kahan step is
bounded by the existing local retained-correction state coefficient radius. -/
theorem kahanCoupledCoeffStepOfIndex_C_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).C| ≤
      fp.u * (1 + fp.u) ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanCorrectionStateCoeff_abs_le
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The correction-residual input coefficient `D` of an actual coupled Kahan
step is bounded by the existing local retained-correction input coefficient
radius. -/
theorem kahanCoupledCoeffStepOfIndex_D_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).D| ≤
      fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanCorrectionInputCoeff_abs_le
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaSub := (kahanTrace_deltaWitness fp v i).deltaSub)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaSub
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The correction residual coefficient `D-C` in paired coordinates is bounded
by the sum of the local correction-row coefficient bounds. -/
theorem kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).correctionResidualCoeff| ≤
      fp.u * (1 + fp.u) ^ 2 * (3 + fp.u) := by
  let step := kahanCoupledCoeffStepOfIndex fp v i
  have hC :
      |step.C| ≤ fp.u * (1 + fp.u) ^ 2 := by
    simpa [step] using kahanCoupledCoeffStepOfIndex_C_abs_le fp v i
  have hD :
      |step.D| ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
    simpa [step] using kahanCoupledCoeffStepOfIndex_D_abs_le fp v i
  have htri : |step.D - step.C| ≤ |step.D| + |step.C| := by
    simpa [sub_eq_add_neg, abs_neg] using
      abs_add_le step.D (-step.C)
  calc
    |step.correctionResidualCoeff| = |step.D - step.C| := by
      rfl
    _ ≤ |step.D| + |step.C| := htri
    _ ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) +
          fp.u * (1 + fp.u) ^ 2 := by
        exact add_le_add hD hC
    _ = fp.u * (1 + fp.u) ^ 2 * (3 + fp.u) := by
        ring

/-- Exact-subtraction local bound for an actual coupled Kahan step's
paired-total old-state coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_totalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).totalStateCoeff - 1| ≤
      fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_totalStateCoeff_eq, hSubZero]
  exact
    kahanTotalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Exact-subtraction local bound for an actual coupled Kahan step's
paired-total current-input coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).totalInputCoeff - 1| ≤
      fp.u + 2 * fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_totalInputCoeff_eq, hSubZero]
  exact
    kahanTotalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Exact-subtraction local bound for an actual coupled Kahan step's
paired-total retained-correction residual. -/
theorem kahanCoupledCoeffStepOfIndex_residualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).residualCoeff| ≤
      fp.u + fp.u ^ 2 := by
  rw [kahanCoupledCoeffStepOfIndex_residualCoeff_eq, hSubZero]
  exact
    kahanTotalResidualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Exact-subtraction local bound for an actual coupled Kahan step's
correction old-total coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_C_abs_le_u_plus_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).C| ≤
      fp.u + fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex, hSubZero] using
    kahanCorrectionStateCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Exact-subtraction local bound for an actual coupled Kahan step's
correction current-input coefficient. -/
theorem kahanCoupledCoeffStepOfIndex_D_abs_le_u_plus_three_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).D| ≤
      fp.u + 3 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex, hSubZero] using
    kahanCorrectionInputCoeff_abs_le_u_plus_three_u_sq_of_deltaSub_zero
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- Exact-subtraction local bound for an actual coupled Kahan step's paired
correction residual. -/
theorem kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hu1 : fp.u ≤ 1)
    (hSubZero : (kahanTrace_deltaWitness fp v i).deltaSub = 0) :
    |(kahanCoupledCoeffStepOfIndex fp v i).correctionResidualCoeff| ≤
      2 * fp.u ^ 2 := by
  simpa [kahanCoupledCoeffStepOfIndex,
    KahanCoupledCoeffStep.correctionResidualCoeff, hSubZero] using
    kahanCorrectionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (deltaE := (kahanTrace_deltaWitness fp v i).deltaE)
      (u := fp.u) fp.u_nonneg hu1
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS
      (kahanTrace_deltaWitness fp v i).h_deltaE

/-- The returned-coordinate old-state coefficient of an actual coupled Kahan
step has only the direct stored-sum first-order radius.  This is the precise
local obstruction that prevents reusing the compensated-total coefficient
collapse for the ordinary returned sum in the bare abstract `FPModel`. -/
theorem kahanCoupledCoeffStepOfIndex_returnedStateCoeff_abs_sub_one_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).returnedStateCoeff - 1| ≤
      fp.u := by
  rw [KahanCoupledCoeffStep.returnedStateCoeff_eq_A]
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanStoredSumStateCoeff_abs_sub_one_le
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (u := fp.u)
      (kahanTrace_deltaWitness fp v i).h_deltaS

/-- The returned-coordinate retained-correction coefficient of an actual
coupled Kahan step is `O(u)`.  Multiplied by the paired correction coefficient
this term is second order, but the returned old-state coefficient above still
carries the first-order radius. -/
theorem kahanCoupledCoeffStepOfIndex_returnedCorrectionCoeff_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    |(kahanCoupledCoeffStepOfIndex fp v i).returnedCorrectionCoeff| ≤
      fp.u * (1 + fp.u) := by
  rw [KahanCoupledCoeffStep.returnedCorrectionCoeff_eq_B_sub_A]
  simpa [kahanCoupledCoeffStepOfIndex] using
    kahanStoredSumInputCoeff_sub_stateCoeff_abs_le_u_mul_one_add_u
      (deltaY := (kahanTrace_deltaWitness fp v i).deltaY)
      (deltaS := (kahanTrace_deltaWitness fp v i).deltaS)
      (u := fp.u) fp.u_nonneg
      (kahanTrace_deltaWitness fp v i).h_deltaY
      (kahanTrace_deltaWitness fp v i).h_deltaS

/-- One indexed Kahan prefix-trace step satisfies the coupled direct
stored-sum/correction coefficient recurrence. -/
theorem kahanTrace_eq_coupledCoeffStep_next
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    let step := kahanCoupledCoeffStepOfIndex fp v i
    (kahanTrace fp v i).nextState = step.next state := by
  have hs := kahanTrace_deltaWitness_s_coefficients fp v i
  have he := kahanTrace_deltaWitness_e_coefficients fp v i
  dsimp at hs he
  dsimp [KahanStepTrace.nextState, KahanCoupledCoeffStep.next,
    kahanCoupledCoeffStepOfIndex]
  rw [hs, he]

/-- The concrete coupled coefficient steps for the first `k` Kahan prefix
steps. -/
noncomputable def kahanCoupledCoeffSteps
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    List KahanCoupledCoeffStep :=
  List.ofFn fun i : Fin k =>
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    kahanCoupledCoeffStepOfIndex fp v idx

/-- Prefix-level exact-subtraction hypothesis for the chosen Kahan
roundoff-witnesses: every correction subtraction in the first `k` steps has
zero subtraction delta.  This is a local bridge hypothesis, not a consequence
of bare `FPModel`. -/
def kahanCoupledCoeffStepsExactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) : Prop :=
  ∀ i : Fin k,
    (kahanTrace_deltaWitness fp v
      ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩).deltaSub = 0

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has total old-state coefficient within `3*u^2` of one. -/
theorem kahanCoupledCoeffSteps_totalStateCoeff_abs_sub_one_le_three_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.totalStateCoeff - 1| ≤ 3 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_totalStateCoeff_abs_sub_one_le_three_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has total current-input coefficient within `2*u + 9*u^2` of one. -/
theorem kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.totalInputCoeff - 1| ≤ 2 * fp.u + 9 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has residual coefficient bounded by `2*u + 12*u^2`. -/
theorem kahanCoupledCoeffSteps_residualCoeff_abs_le_two_u_plus_twelve_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.residualCoeff| ≤ 2 * fp.u + 12 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_residualCoeff_abs_le_two_u_plus_twelve_u_sq
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has correction-total coefficient bounded by `u*(1+u)^2`. -/
theorem kahanCoupledCoeffSteps_C_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.C| ≤ fp.u * (1 + fp.u) ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_C_abs_le
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has correction-input coefficient bounded by `u*(1+u)^2*(2+u)`. -/
theorem kahanCoupledCoeffSteps_D_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.D| ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_D_abs_le
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Every actual coupled coefficient step in the first `k` Kahan prefix steps
has paired-coordinate correction residual coefficient bounded by
`u*(1+u)^2*(3+u)`. -/
theorem kahanCoupledCoeffSteps_correctionResidualCoeff_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.correctionResidualCoeff| ≤
        fp.u * (1 + fp.u) ^ 2 * (3 + fp.u) := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_abs_le
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Prefix-indexed form of the general correction-residual cancellation for
the actual chosen witness used by `kahanCoupledCoeffSteps`. -/
theorem kahanCoupledCoeffSteps_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfIndex fp v idx).correctionResidualCoeff +
          (kahanTrace_deltaWitness fp v idx).deltaSub| ≤
        7 * fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
      fp v idx hu1

/-- Prefix-indexed form of
`residualCoeff - correctionResidualCoeff = deltaY + O(u^2)` for the actual
chosen witness used by `kahanCoupledCoeffSteps`. -/
theorem kahanCoupledCoeffSteps_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfIndex fp v idx).residualCoeff -
          (kahanCoupledCoeffStepOfIndex fp v idx).correctionResidualCoeff -
          (kahanTrace_deltaWitness fp v idx).deltaY| ≤
        fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfIndex_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
      fp v idx

/-- Prefix-indexed combined residual cancellation for the actual chosen
witness used by `kahanCoupledCoeffSteps`. -/
theorem kahanCoupledCoeffSteps_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfIndex fp v idx).residualCoeff +
          (kahanTrace_deltaWitness fp v idx).deltaSub -
          (kahanTrace_deltaWitness fp v idx).deltaY| ≤
        8 * fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfIndex_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
      fp v idx hu1

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step
has paired-total old-state coefficient within `u^2` of one. -/
theorem kahanCoupledCoeffSteps_totalStateCoeff_abs_sub_one_le_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.totalStateCoeff - 1| ≤ fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_totalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ (hExactSub i)

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step
has paired-total current-input coefficient within `u + 2*u^2` of one. -/
theorem kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.totalInputCoeff - 1| ≤ fp.u + 2 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1 (hExactSub i)

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step
has paired-total retained-correction residual bounded by `u + u^2`. -/
theorem kahanCoupledCoeffSteps_residualCoeff_abs_le_u_plus_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.residualCoeff| ≤ fp.u + fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_residualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1 (hExactSub i)

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step's
correction old-total coefficient is bounded by `u + u^2`. -/
theorem kahanCoupledCoeffSteps_C_abs_le_u_plus_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.C| ≤ fp.u + fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_C_abs_le_u_plus_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ (hExactSub i)

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step's
correction current-input coefficient is bounded by `u + 3*u^2`. -/
theorem kahanCoupledCoeffSteps_D_abs_le_u_plus_three_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.D| ≤ fp.u + 3 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_D_abs_le_u_plus_three_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1 (hExactSub i)

/-- Under the prefix exact-subtraction hypothesis, every actual coupled step's
paired correction residual is second order. -/
theorem kahanCoupledCoeffSteps_correctionResidualCoeff_abs_le_two_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.correctionResidualCoeff| ≤ 2 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_correctionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ hu1 (hExactSub i)

/-- Every actual coupled coefficient step has returned-coordinate old-state
coefficient within first-order radius `u` of one. -/
theorem kahanCoupledCoeffSteps_returnedStateCoeff_abs_sub_one_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.returnedStateCoeff - 1| ≤ fp.u := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_returnedStateCoeff_abs_sub_one_le
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Every actual coupled coefficient step has returned-coordinate retained
correction coefficient bounded by `u*(1+u)`. -/
theorem kahanCoupledCoeffSteps_returnedCorrectionCoeff_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk,
      |step.returnedCorrectionCoeff| ≤ fp.u * (1 + fp.u) := by
  intro step hmem
  rw [kahanCoupledCoeffSteps, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  simpa using
    kahanCoupledCoeffStepOfIndex_returnedCorrectionCoeff_abs_le
      fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- One-step paired-coordinate total-deviation inequality for every concrete
Kahan prefix coefficient step.  This is the local recurrence inequality needed
by the next Goldberg-style paired coefficient induction. -/
theorem kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk, ∀ state : KahanState,
      |(step.propagateTotalCorrection state).s - 1| ≤
        |state.s - 1| * (1 + 3 * fp.u ^ 2) +
          3 * fp.u ^ 2 +
          |state.e| * (2 * fp.u + 12 * fp.u ^ 2) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le_of_bounds
      step state
      (eta := 3 * fp.u ^ 2)
      (rho := 2 * fp.u + 12 * fp.u ^ 2)
      (kahanCoupledCoeffSteps_totalStateCoeff_abs_sub_one_le_three_u_sq
        fp v k hk hu1 step hmem)
      (kahanCoupledCoeffSteps_residualCoeff_abs_le_two_u_plus_twelve_u_sq
        fp v k hk hu1 step hmem)

/-- One-step paired-coordinate retained-correction inequality for every
concrete Kahan prefix coefficient step. -/
theorem kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk, ∀ state : KahanState,
      |(step.propagateTotalCorrection state).e| ≤
        (|state.s - 1| + 1) * (fp.u * (1 + fp.u) ^ 2) +
          |state.e| * (fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le_of_bounds
      step state
      (sigma := fp.u * (1 + fp.u) ^ 2)
      (chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u))
      (kahanCoupledCoeffSteps_C_abs_le fp v k hk step hmem)
      (kahanCoupledCoeffSteps_correctionResidualCoeff_abs_le
        fp v k hk step hmem)

/-- Exact-subtraction version of the one-step paired-coordinate total
deviation inequality for concrete Kahan prefix coefficient steps. -/
theorem kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk, ∀ state : KahanState,
      |(step.propagateTotalCorrection state).s - 1| ≤
        |state.s - 1| * (1 + fp.u ^ 2) +
          fp.u ^ 2 +
          |state.e| * (fp.u + fp.u ^ 2) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le_of_bounds
      step state
      (eta := fp.u ^ 2)
      (rho := fp.u + fp.u ^ 2)
      (kahanCoupledCoeffSteps_totalStateCoeff_abs_sub_one_le_u_sq_of_exactSub
        fp v k hk hExactSub step hmem)
      (kahanCoupledCoeffSteps_residualCoeff_abs_le_u_plus_u_sq_of_exactSub
        fp v k hk hu1 hExactSub step hmem)

/-- Exact-subtraction version of the one-step paired-coordinate retained
correction inequality for concrete Kahan prefix coefficient steps. -/
theorem kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk, ∀ state : KahanState,
      |(step.propagateTotalCorrection state).e| ≤
        (|state.s - 1| + 1) * (fp.u + fp.u ^ 2) +
          |state.e| * (2 * fp.u ^ 2) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le_of_bounds
      step state
      (sigma := fp.u + fp.u ^ 2)
      (chi := 2 * fp.u ^ 2)
      (kahanCoupledCoeffSteps_C_abs_le_u_plus_u_sq_of_exactSub
        fp v k hk hExactSub step hmem)
      (kahanCoupledCoeffSteps_correctionResidualCoeff_abs_le_two_u_sq_of_exactSub
        fp v k hk hu1 hExactSub step hmem)

/-- One-step returned-coordinate deviation inequality for every concrete
Kahan prefix coefficient step.  Its old-state term uses `1 + fp.u`, not
`1 + O(fp.u^2)`, which records the exact gap left by the current abstract
coefficient route for Higham equation (4.8). -/
theorem kahanCoupledCoeffSteps_propagateTotalCorrection_returnedDev_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ step ∈ kahanCoupledCoeffSteps fp v k hk, ∀ state : KahanState,
      |KahanState.returnedFromTotalCorrection
          (step.propagateTotalCorrection state) - 1| ≤
        |state.s - 1| * (1 + fp.u) + fp.u +
          |state.e| * (fp.u * (1 + fp.u)) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_returnedDev_abs_le_of_bounds
      step state
      (eta := fp.u)
      (theta := fp.u * (1 + fp.u))
      (kahanCoupledCoeffSteps_returnedStateCoeff_abs_sub_one_le
        fp v k hk step hmem)
      (kahanCoupledCoeffSteps_returnedCorrectionCoeff_abs_le
        fp v k hk step hmem)

/-- Concrete Kahan prefix instance of the paired-coordinate majorant
recurrence.  It bounds propagation through the first `k` Kahan coupled
coefficient steps using the local total/residual and correction-row bounds. -/
theorem kahanCoupledCoeffSteps_totalCorrectionPropagate_abs_le_pairedCoeffMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1) (init : KahanState) {S E : ℝ}
    (hS0 : |init.s - 1| ≤ S) (hE0 : |init.e| ≤ E)
    (hS_nonneg : 0 ≤ S) (hE_nonneg : 0 ≤ E) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let eta := 3 * fp.u ^ 2
    let rho := 2 * fp.u + 12 * fp.u ^ 2
    let sigma := fp.u * (1 + fp.u) ^ 2
    let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
    |(kahanCoupledTotalCorrectionPropagate steps init).s - 1| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).s ∧
      |(kahanCoupledTotalCorrectionPropagate steps init).e| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi steps S E).e := by
  dsimp
  let eta := 3 * fp.u ^ 2
  let rho := 2 * fp.u + 12 * fp.u ^ 2
  let sigma := fp.u * (1 + fp.u) ^ 2
  let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
  let steps := kahanCoupledCoeffSteps fp v k hk
  have heta : 0 ≤ eta := by
    dsimp [eta]
    nlinarith [sq_nonneg fp.u]
  have hOneEta : 0 ≤ 1 + eta := by
    nlinarith
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hsigma : 0 ≤ sigma := by
    dsimp [sigma]
    exact mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))
  have hchi : 0 ≤ chi := by
    dsimp [chi]
    exact mul_nonneg hsigma (by nlinarith [fp.u_nonneg])
  have hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho := by
    intro step hmem state
    simpa [steps, eta, rho] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le
        fp v k hk hu1 step hmem state
  have hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi := by
    intro step hmem state
    simpa [steps, sigma, chi] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le
        fp v k hk step hmem state
  exact
    kahanCoupledTotalCorrectionPropagate_abs_le_pairedCoeffMajorant
      (eta := eta) (rho := rho) (sigma := sigma) (chi := chi)
      heta hOneEta hrho hsigma hchi steps init
      hS0 hE0 hS_nonneg hE_nonneg hTotal hCorrection

/-- Concrete paired-majorant bound for every propagated source coefficient in
the first `k` Kahan prefix steps.  The suffix majorant starts from the local
current-source total coefficient radius and the local retained-correction
source coefficient bound. -/
theorem kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let eta := 3 * fp.u ^ 2
    let rho := 2 * fp.u + 12 * fp.u ^ 2
    let sigma := fp.u * (1 + fp.u) ^ 2
    let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
    let sourceDev := 2 * fp.u + 9 * fp.u ^ 2
    let sourceCorrection := fp.u * (1 + fp.u) ^ 2 * (2 + fp.u)
    |(kahanCoupledSourceTotalCorrectionCoeff steps i).s - 1| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi
          (steps.drop (i.val + 1)) sourceDev sourceCorrection).s ∧
      |(kahanCoupledSourceTotalCorrectionCoeff steps i).e| ≤
        (kahanCoupledPairedCoeffMajorant eta rho sigma chi
          (steps.drop (i.val + 1)) sourceDev sourceCorrection).e := by
  dsimp
  let steps := kahanCoupledCoeffSteps fp v k hk
  let eta := 3 * fp.u ^ 2
  let rho := 2 * fp.u + 12 * fp.u ^ 2
  let sigma := fp.u * (1 + fp.u) ^ 2
  let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
  let sourceDev := 2 * fp.u + 9 * fp.u ^ 2
  let sourceCorrection := fp.u * (1 + fp.u) ^ 2 * (2 + fp.u)
  have heta : 0 ≤ eta := by
    dsimp [eta]
    nlinarith [sq_nonneg fp.u]
  have hOneEta : 0 ≤ 1 + eta := by
    nlinarith
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hsigma : 0 ≤ sigma := by
    dsimp [sigma]
    exact mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))
  have hchi : 0 ≤ chi := by
    dsimp [chi]
    exact mul_nonneg hsigma (by nlinarith [fp.u_nonneg])
  have hsourceDev_nonneg : 0 ≤ sourceDev := by
    dsimp [sourceDev]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hsourceCorrection_nonneg : 0 ≤ sourceCorrection := by
    dsimp [sourceCorrection]
    exact mul_nonneg hsigma (by nlinarith [fp.u_nonneg])
  have hmem : steps.get i ∈ steps := List.get_mem steps i
  have hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤
        sourceDev := by
    have h :=
      kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_two_u_plus_nine_u_sq
        fp v k hk hu1 (steps.get i) hmem
    simpa [steps, sourceDev, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff,
      KahanCoupledCoeffStep.totalInputCoeff] using h
  have hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤
        sourceCorrection := by
    have h :=
      kahanCoupledCoeffSteps_D_abs_le fp v k hk (steps.get i) hmem
    simpa [steps, sourceCorrection, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff] using h
  have hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + eta) + eta + |state.e| * rho := by
    intro step hstep state
    simpa [steps, eta, rho] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le
        fp v k hk hu1 step hstep state
  have hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * sigma + |state.e| * chi := by
    intro step hstep state
    simpa [steps, sigma, chi] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le
        fp v k hk step hstep state
  exact
    kahanCoupledSourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
      (eta := eta) (rho := rho) (sigma := sigma) (chi := chi)
      heta hOneEta hrho hsigma hchi steps i
      hS0 hE0 hsourceDev_nonneg hsourceCorrection_nonneg
      hTotal hCorrection

/-- Concrete Kahan instance of the triangle-route returned-coefficient bound.

The right-hand side is the paired-total majorant plus the paired correction
majorant.  This formalizes the route that is too weak for Higham equation
(4.8), because the retained-correction majorant contributes a first-order
term. -/
theorem kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_pairedCoeffMajorant_sum
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    let eta := 3 * fp.u ^ 2
    let rho := 2 * fp.u + 12 * fp.u ^ 2
    let sigma := fp.u * (1 + fp.u) ^ 2
    let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
    let sourceDev := 2 * fp.u + 9 * fp.u ^ 2
    let sourceCorrection := fp.u * (1 + fp.u) ^ 2 * (2 + fp.u)
    |(kahanCoupledSourceCoeff steps i).s - 1| ≤
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi
        (steps.drop (i.val + 1)) sourceDev sourceCorrection).s +
      (kahanCoupledPairedCoeffMajorant eta rho sigma chi
        (steps.drop (i.val + 1)) sourceDev sourceCorrection).e := by
  dsimp
  let steps := kahanCoupledCoeffSteps fp v k hk
  let eta := 3 * fp.u ^ 2
  let rho := 2 * fp.u + 12 * fp.u ^ 2
  let sigma := fp.u * (1 + fp.u) ^ 2
  let chi := fp.u * (1 + fp.u) ^ 2 * (3 + fp.u)
  let sourceDev := 2 * fp.u + 9 * fp.u ^ 2
  let sourceCorrection := fp.u * (1 + fp.u) ^ 2 * (2 + fp.u)
  have hpair :=
    kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
      fp v k hk hu1 i
  let a := kahanCoupledSourceCoeff steps i
  have htri :
      |a.s - 1| ≤
        |(KahanState.totalCorrection a).s - 1| +
          |(KahanState.totalCorrection a).e| := by
    have hrewrite :
        a.s - 1 = (a.s + a.e - 1) - a.e := by ring
    rw [hrewrite]
    simpa [KahanState.totalCorrection, sub_eq_add_neg, abs_neg] using
      abs_add_le (a.s + a.e - 1) (-a.e)
  exact htri.trans (add_le_add hpair.1 hpair.2)

/-- Conditional returned-source coefficient collapse for ordinary Kahan under
the prefix exact-subtraction hypothesis.

This is the source-shaped theorem needed by Higham equation (4.8), except that
it still assumes the correction-subtraction deltas selected by
`kahanTrace_deltaWitness` are zero.  The remaining finite-format task is to
derive `kahanCoupledCoeffStepsExactSub` from the concrete correction-formula
exactness hypotheses rather than from bare `FPModel`. -/
theorem kahanCoupledCoeffSteps_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (huSmall : fp.u ≤ 1 / 64)
    (hExactSub : kahanCoupledCoeffStepsExactSub fp v k hk)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hBudget :
      (3 + 40 *
        (((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)).length : ℝ)) *
          fp.u ≤ 1) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    |(kahanCoupledSourceCoeff steps i).s - 1| ≤
      2 * fp.u +
        2 * (3 + 40 * ((steps.drop (i.val + 1)).length : ℝ)) *
          fp.u ^ 2 := by
  dsimp
  let steps := kahanCoupledCoeffSteps fp v k hk
  let sourceRadius := fp.u + 3 * fp.u ^ 2
  have hu1 : fp.u ≤ 1 := by nlinarith
  have hmem : steps.get i ∈ steps := List.get_mem steps i
  have hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤
        sourceRadius := by
    have h :=
      kahanCoupledCoeffSteps_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_exactSub
        fp v k hk hu1 hExactSub (steps.get i) hmem
    have hle : fp.u + 2 * fp.u ^ 2 ≤ sourceRadius := by
      dsimp [sourceRadius]
      nlinarith [sq_nonneg fp.u]
    exact
      (by
        simpa [steps, sourceRadius, KahanState.totalCorrection,
          KahanCoupledCoeffStep.sourceCoeff,
          KahanCoupledCoeffStep.totalInputCoeff] using h.trans hle)
  have hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤
        sourceRadius := by
    have h :=
      kahanCoupledCoeffSteps_D_abs_le_u_plus_three_u_sq_of_exactSub
        fp v k hk hu1 hExactSub (steps.get i) hmem
    simpa [steps, sourceRadius, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff] using h
  have hsourceRadius_nonneg : 0 ≤ sourceRadius := by
    dsimp [sourceRadius]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + fp.u ^ 2) + fp.u ^ 2 +
            |state.e| * (fp.u + fp.u ^ 2) := by
    intro step hstep state
    simpa [steps] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_totalDev_abs_le_of_exactSub
        fp v k hk hu1 hExactSub step hstep state
  have hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * (fp.u + fp.u ^ 2) +
            |state.e| * (2 * fp.u ^ 2) := by
    intro step hstep state
    simpa [steps] using
      kahanCoupledCoeffSteps_propagateTotalCorrection_correction_abs_le_of_exactSub
        fp v k hk hu1 hExactSub step hstep state
  exact
    kahanCoupledSourceCoeff_s_abs_sub_one_le_exactSubMajorant
      (u := fp.u) (A := 3) (S := sourceRadius) (E := sourceRadius)
      fp.u_nonneg huSmall (by norm_num) steps i
      (by simpa [steps] using hBudget)
      hS0 hE0 hsourceRadius_nonneg hsourceRadius_nonneg
      (by rfl) (by rfl) hTotal hCorrection


/-- Coupled coefficient steps built from an explicit prefix witness family. -/
def kahanCoupledCoeffStepsOfWitnesses
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    List KahanCoupledCoeffStep :=
  List.ofFn fun i : Fin k =>
    let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
    kahanCoupledCoeffStepOfWitness fp v idx (W i)

/-- Prefix-indexed form of the general correction-residual cancellation for
an explicit witness family. -/
theorem kahanCoupledCoeffStepsOfWitnesses_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfWitness fp v idx (W i)).correctionResidualCoeff +
          (W i).deltaSub| ≤
        7 * fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_correctionResidualCoeff_add_deltaSub_abs_le_seven_u_sq
      fp v idx (W i) hu1

/-- Prefix-indexed form of
`residualCoeff - correctionResidualCoeff = deltaY + O(u^2)` for an explicit
witness family. -/
theorem kahanCoupledCoeffStepsOfWitnesses_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfWitness fp v idx (W i)).residualCoeff -
          (kahanCoupledCoeffStepOfWitness fp v idx (W i)).correctionResidualCoeff -
          (W i).deltaY| ≤
        fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_residualCoeff_sub_correctionResidualCoeff_sub_deltaY_abs_le_u_sq
      fp v idx (W i)

/-- Prefix-indexed combined residual cancellation for an explicit witness
family. -/
theorem kahanCoupledCoeffStepsOfWitnesses_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    ∀ i : Fin k,
      let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
      |(kahanCoupledCoeffStepOfWitness fp v idx (W i)).residualCoeff +
          (W i).deltaSub - (W i).deltaY| ≤
        8 * fp.u ^ 2 := by
  intro i
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_residualCoeff_add_deltaSub_sub_deltaY_abs_le_eight_u_sq
      fp v idx (W i) hu1

/-- Prefix-level exact-subtraction hypothesis for an explicit witness family. -/
def kahanCoupledCoeffStepsOfWitnessesExactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) : Prop :=
  ∀ i : Fin k, (W i).deltaSub = 0

/-- The witness family constructed from exact correction subtraction satisfies
the exact-subtraction predicate used by the coefficient theorem. -/
theorem kahanPrefixDeltaWitnessFamilyOfExactSub_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hExactSubTrace : KahanPrefixCorrectionSubExact fp v k hk) :
    kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk
      (kahanPrefixDeltaWitnessFamilyOfExactSub
        fp v k hk hExactSubTrace) := by
  intro i
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
  simpa [kahanPrefixDeltaWitnessFamilyOfExactSub, idx, hsubExact] using
    kahanStepTrace_deltaWitnessOfExactSub_deltaSub fp (v idx)
      (kahanPrefixState fp v idx.val (Nat.le_of_lt idx.isLt))
      hsubExact

/-- Exact-subtraction list-level old-total coefficient bound for explicit
witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_totalStateCoeff_abs_sub_one_le_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.totalStateCoeff - 1| ≤ fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_totalStateCoeff_abs_sub_one_le_u_sq_of_deltaSub_zero
      fp v idx (W i) (hExactSub i)

/-- Exact-subtraction list-level current-input total coefficient bound for
explicit witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.totalInputCoeff - 1| ≤ fp.u + 2 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_deltaSub_zero
      fp v idx (W i) hu1 (hExactSub i)

/-- Exact-subtraction list-level retained-correction residual bound for
explicit witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_residualCoeff_abs_le_u_plus_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.residualCoeff| ≤ fp.u + fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_residualCoeff_abs_le_u_plus_u_sq_of_deltaSub_zero
      fp v idx (W i) hu1 (hExactSub i)

/-- Exact-subtraction list-level correction old-total coefficient bound for
explicit witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_C_abs_le_u_plus_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.C| ≤ fp.u + fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_C_abs_le_u_plus_u_sq_of_deltaSub_zero
      fp v idx (W i) (hExactSub i)

/-- Exact-subtraction list-level correction current-input coefficient bound
for explicit witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_D_abs_le_u_plus_three_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.D| ≤ fp.u + 3 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_D_abs_le_u_plus_three_u_sq_of_deltaSub_zero
      fp v idx (W i) hu1 (hExactSub i)

/-- Exact-subtraction list-level paired correction residual bound for explicit
witness-family Kahan steps. -/
theorem kahanCoupledCoeffStepsOfWitnesses_correctionResidualCoeff_abs_le_two_u_sq_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      |step.correctionResidualCoeff| ≤ 2 * fp.u ^ 2 := by
  intro step hmem
  rw [kahanCoupledCoeffStepsOfWitnesses, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  simpa [idx] using
    kahanCoupledCoeffStepOfWitness_correctionResidualCoeff_abs_le_two_u_sq_of_deltaSub_zero
      fp v idx (W i) hu1 (hExactSub i)

/-- Exact-subtraction one-step propagation inequality for explicit
witness-family Kahan steps in paired-total coordinates. -/
theorem kahanCoupledCoeffStepsOfWitnesses_propagateTotalCorrection_totalDev_abs_le_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + fp.u ^ 2) + fp.u ^ 2 +
            |state.e| * (fp.u + fp.u ^ 2) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_totalDev_abs_le_of_bounds
      step state
      (kahanCoupledCoeffStepsOfWitnesses_totalStateCoeff_abs_sub_one_le_u_sq_of_exactSub
        fp v k hk W hExactSub step hmem)
      (kahanCoupledCoeffStepsOfWitnesses_residualCoeff_abs_le_u_plus_u_sq_of_exactSub
        fp v k hk hu1 W hExactSub step hmem)

/-- Exact-subtraction one-step correction propagation inequality for explicit
witness-family Kahan steps in paired-total coordinates. -/
theorem kahanCoupledCoeffStepsOfWitnesses_propagateTotalCorrection_correction_abs_le_of_exactSub
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (hu1 : fp.u ≤ 1)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W) :
    ∀ step ∈ kahanCoupledCoeffStepsOfWitnesses fp v k hk W,
      ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * (fp.u + fp.u ^ 2) +
            |state.e| * (2 * fp.u ^ 2) := by
  intro step hmem state
  exact
    KahanCoupledCoeffStep.propagateTotalCorrection_correction_abs_le_of_bounds
      step state
      (kahanCoupledCoeffStepsOfWitnesses_C_abs_le_u_plus_u_sq_of_exactSub
        fp v k hk W hExactSub step hmem)
      (kahanCoupledCoeffStepsOfWitnesses_correctionResidualCoeff_abs_le_two_u_sq_of_exactSub
        fp v k hk hu1 W hExactSub step hmem)

/-- Source-coefficient collapse for the returned Kahan sum along an explicit
exact-subtraction witness-family route. -/
theorem kahanCoupledCoeffStepsOfWitnesses_sourceCoeff_s_abs_sub_one_le_two_u_plus_exactSubMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk)
    (huSmall : fp.u ≤ 1 / 64)
    (hExactSub : kahanCoupledCoeffStepsOfWitnessesExactSub fp v k hk W)
    (i : Fin (kahanCoupledCoeffStepsOfWitnesses fp v k hk W).length)
    (hBudget :
      (3 + 40 *
        (((kahanCoupledCoeffStepsOfWitnesses fp v k hk W).drop
          (i.val + 1)).length : ℝ)) * fp.u ≤ 1) :
    let steps := kahanCoupledCoeffStepsOfWitnesses fp v k hk W
    |(kahanCoupledSourceCoeff steps i).s - 1| ≤
      2 * fp.u +
        2 * (3 + 40 * ((steps.drop (i.val + 1)).length : ℝ)) *
          fp.u ^ 2 := by
  dsimp
  let steps := kahanCoupledCoeffStepsOfWitnesses fp v k hk W
  let sourceRadius := fp.u + 3 * fp.u ^ 2
  have hu1 : fp.u ≤ 1 := by nlinarith
  have hmem : steps.get i ∈ steps := List.get_mem steps i
  have hS0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).s - 1| ≤
        sourceRadius := by
    have h :=
      kahanCoupledCoeffStepsOfWitnesses_totalInputCoeff_abs_sub_one_le_u_plus_two_u_sq_of_exactSub
        fp v k hk hu1 W hExactSub (steps.get i) hmem
    have hle : fp.u + 2 * fp.u ^ 2 ≤ sourceRadius := by
      dsimp [sourceRadius]
      nlinarith [sq_nonneg fp.u]
    exact
      (by
        simpa [steps, sourceRadius, KahanState.totalCorrection,
          KahanCoupledCoeffStep.sourceCoeff,
          KahanCoupledCoeffStep.totalInputCoeff] using h.trans hle)
  have hE0 :
      |(KahanState.totalCorrection (steps.get i).sourceCoeff).e| ≤
        sourceRadius := by
    have h :=
      kahanCoupledCoeffStepsOfWitnesses_D_abs_le_u_plus_three_u_sq_of_exactSub
        fp v k hk hu1 W hExactSub (steps.get i) hmem
    simpa [steps, sourceRadius, KahanState.totalCorrection,
      KahanCoupledCoeffStep.sourceCoeff] using h
  have hsourceRadius_nonneg : 0 ≤ sourceRadius := by
    dsimp [sourceRadius]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hTotal :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).s - 1| ≤
          |state.s - 1| * (1 + fp.u ^ 2) + fp.u ^ 2 +
            |state.e| * (fp.u + fp.u ^ 2) := by
    intro step hstep state
    simpa [steps] using
      kahanCoupledCoeffStepsOfWitnesses_propagateTotalCorrection_totalDev_abs_le_of_exactSub
        fp v k hk hu1 W hExactSub step hstep state
  have hCorrection :
      ∀ step ∈ steps, ∀ state : KahanState,
        |(step.propagateTotalCorrection state).e| ≤
          (|state.s - 1| + 1) * (fp.u + fp.u ^ 2) +
            |state.e| * (2 * fp.u ^ 2) := by
    intro step hstep state
    simpa [steps] using
      kahanCoupledCoeffStepsOfWitnesses_propagateTotalCorrection_correction_abs_le_of_exactSub
        fp v k hk hu1 W hExactSub step hstep state
  exact
    kahanCoupledSourceCoeff_s_abs_sub_one_le_exactSubMajorant
      (u := fp.u) (A := 3) (S := sourceRadius) (E := sourceRadius)
      fp.u_nonneg huSmall (by norm_num) steps i
      (by simpa [steps] using hBudget)
      hS0 hE0 hsourceRadius_nonneg hsourceRadius_nonneg
      (by rfl) (by rfl) hTotal hCorrection

/-- Source-shaped collapse of the paired majorant for the compensated-total
coefficient of each propagated Kahan source vector.  This closes the
majorant-collapse dependency for the `s+e` coefficient; the final returned
stored-sum coefficient still needs the remaining paired-cancellation step. -/
theorem kahanCoupledCoeffSteps_sourceTotalCoeff_abs_sub_one_le_two_u_plus_majorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (huSmall : fp.u ≤ 1 / 64)
    (i : Fin (kahanCoupledCoeffSteps fp v k hk).length)
    (hBudget :
      (9 + 200 *
        (((kahanCoupledCoeffSteps fp v k hk).drop (i.val + 1)).length : ℝ)) *
          fp.u ≤ 1) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    |kahanCoupledSourceTotalCoeff steps i - 1| ≤
      2 * fp.u +
        (9 + 200 * ((steps.drop (i.val + 1)).length : ℝ)) * fp.u ^ 2 := by
  dsimp
  let steps := kahanCoupledCoeffSteps fp v k hk
  let suffix := steps.drop (i.val + 1)
  have hu1 : fp.u ≤ 1 := by nlinarith
  have hpaired :=
    (kahanCoupledCoeffSteps_sourceTotalCorrectionCoeff_abs_le_pairedCoeffMajorant
      fp v k hk hu1 i).1
  have hsigma_nonneg : 0 ≤ fp.u * (1 + fp.u) ^ 2 := by
    exact mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))
  have hsigma_le : fp.u * (1 + fp.u) ^ 2 ≤ 4 * fp.u := by
    have h1u : 1 + fp.u ≤ 2 := by nlinarith
    have h1u_nonneg : 0 ≤ 1 + fp.u := by nlinarith [fp.u_nonneg]
    have hsquare : (1 + fp.u) ^ 2 ≤ 4 := by
      have hmul := mul_le_mul h1u h1u h1u_nonneg (by norm_num)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsquare fp.u_nonneg
    nlinarith
  have hsourceCorrection :
      fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) ≤ 12 * fp.u := by
    have h2u : 2 + fp.u ≤ 3 := by nlinarith
    have h2u_nonneg : 0 ≤ 2 + fp.u := by nlinarith [fp.u_nonneg]
    have h12_nonneg : 0 ≤ 4 * fp.u := by nlinarith [fp.u_nonneg]
    have hmul := mul_le_mul hsigma_le h2u h2u_nonneg h12_nonneg
    nlinarith
  have hcollapse :=
    kahanCoupledPairedCoeffMajorant_kahanConstants_le_two_u_plus
      (u := fp.u) (A := 9)
      (S := 2 * fp.u + 9 * fp.u ^ 2)
      (E := fp.u * (1 + fp.u) ^ 2 * (2 + fp.u))
      fp.u_nonneg huSmall (by norm_num) suffix
      (by simpa [steps, suffix] using hBudget)
      (by rfl) hsourceCorrection
  calc
    |kahanCoupledSourceTotalCoeff steps i - 1|
        = |(kahanCoupledSourceTotalCorrectionCoeff steps i).s - 1| := by
          rfl
    _ ≤
        (kahanCoupledPairedCoeffMajorant (3 * fp.u ^ 2)
          (2 * fp.u + 12 * fp.u ^ 2)
          (fp.u * (1 + fp.u) ^ 2)
          (fp.u * (1 + fp.u) ^ 2 * (3 + fp.u))
          suffix
          (2 * fp.u + 9 * fp.u ^ 2)
          (fp.u * (1 + fp.u) ^ 2 * (2 + fp.u))).s := by
        simpa [steps, suffix] using hpaired
    _ ≤ 2 * fp.u + (9 + 200 * (suffix.length : ℝ)) * fp.u ^ 2 :=
        hcollapse.1
    _ = 2 * fp.u +
        (9 + 200 * ((steps.drop (i.val + 1)).length : ℝ)) * fp.u ^ 2 := by
        simp [suffix]

/-- The list fold over coupled Kahan coefficient steps is the matching
`Fin.foldl` prefix recurrence. -/
theorem kahanCoupledCoeffSteps_fold_eq_finFold
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (init : KahanState) :
    kahanCoupledCoeffFold (kahanCoupledCoeffSteps fp v k hk) init =
      Fin.foldl k
        (fun state i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanCoupledCoeffStepOfIndex fp v idx
          step.next state)
        init := by
  dsimp [kahanCoupledCoeffFold, kahanCoupledCoeffSteps]
  rw [Compensated.Kahan.Internal.listFoldlOfFn_eq_finFoldl]

/-- The coupled coefficient recurrence over the first `k` actual Kahan
prefix-trace steps produces the full stored-sum/correction prefix state. -/
theorem kahanCoupledCoeffSteps_finFold_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      Fin.foldl k
        (fun state i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanCoupledCoeffStepOfIndex fp v idx
          step.next state)
        KahanState.zero =
      kahanPrefixState fp v k hk
  | 0, _hk => by
      simp [kahanPrefixState, KahanState.zero]
  | k + 1, hk => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanPrefixState fp v k hprev_le
      let step := kahanCoupledCoeffStepOfIndex fp v idx
      have hih :=
        kahanCoupledCoeffSteps_finFold_eq_prefix_state fp v k hprev_le
      have hih' :
          Fin.foldl k
            (fun state i =>
              let idx : Fin n := ⟨(i.castSucc).val,
                Nat.lt_of_lt_of_le (i.castSucc).isLt hk⟩
              let step := kahanCoupledCoeffStepOfIndex fp v idx
              step.next state)
            KahanState.zero = prev := by
        simpa [prev] using hih
      have hfoldPrefix :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prev := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hstep :
          kahanStep fp (v idx) prev = step.next prev := by
        have htrace := kahanTrace_eq_coupledCoeffStep_next fp v idx
        dsimp at htrace
        simpa [idx, prev, step, kahanTrace, kahanStep,
          KahanStepTrace.nextState] using htrace
      rw [Fin.foldl_succ_last]
      rw [hih']
      rw [hfoldPrefix, hstep]
      rfl

/-- The list of coupled coefficient steps for the first `k` actual Kahan
steps folds from zero to the full stored-sum/correction prefix state. -/
theorem kahanCoupledCoeffSteps_fold_zero_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    kahanCoupledCoeffFold
        (kahanCoupledCoeffSteps fp v k hk) KahanState.zero =
      kahanPrefixState fp v k hk := by
  rw [kahanCoupledCoeffSteps_fold_eq_finFold]
  exact kahanCoupledCoeffSteps_finFold_eq_prefix_state fp v k hk

/-- The propagated source-vector unroll of the first `k` concrete coupled
Kahan steps is exactly the actual prefix `(s,e)` state. -/
theorem kahanCoupledCoeffSteps_sourceUnroll_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    kahanCoupledSourceUnroll (kahanCoupledCoeffSteps fp v k hk) =
      kahanPrefixState fp v k hk := by
  rw [← kahanCoupledCoeffFold_zero_eq_sourceUnroll]
  exact kahanCoupledCoeffSteps_fold_zero_eq_prefix_state fp v k hk

/-- Returned stored sum of the first `k` concrete Kahan coupled steps as an
explicit source-input coefficient sum. -/
theorem kahanCoupledCoeffSteps_prefixState_s_eq_sum_sourceCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    (kahanPrefixState fp v k hk).s =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).s := by
  dsimp
  rw [← kahanCoupledCoeffSteps_sourceUnroll_eq_prefix_state fp v k hk]
  exact kahanCoupledSourceUnroll_s_eq_sum_sourceCoeff
    (kahanCoupledCoeffSteps fp v k hk)

/-- Retained correction of the first `k` concrete Kahan coupled steps as an
explicit source-input coefficient sum. -/
theorem kahanCoupledCoeffSteps_prefixState_e_eq_sum_sourceCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    (kahanPrefixState fp v k hk).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).e := by
  dsimp
  rw [← kahanCoupledCoeffSteps_sourceUnroll_eq_prefix_state fp v k hk]
  exact kahanCoupledSourceUnroll_e_eq_sum_sourceCoeff
    (kahanCoupledCoeffSteps fp v k hk)

/-- Compensated total of the first `k` concrete Kahan coupled steps as an
explicit source-input sum over the paired source coefficients. -/
theorem kahanCoupledCoeffSteps_prefixState_total_eq_sum_sourceTotalCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    let steps := kahanCoupledCoeffSteps fp v k hk
    (kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * kahanCoupledSourceTotalCoeff steps i := by
  dsimp
  rw [← kahanCoupledCoeffSteps_sourceUnroll_eq_prefix_state fp v k hk]
  exact kahanCoupledSourceUnroll_total_eq_sum_sourceTotalCoeff
    (kahanCoupledCoeffSteps fp v k hk)

/-- The list fold over explicit-witness coupled Kahan coefficient steps is the
matching `Fin.foldl` prefix recurrence. -/
theorem kahanCoupledCoeffStepsOfWitnesses_fold_eq_finFold
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) (init : KahanState) :
    kahanCoupledCoeffFold
        (kahanCoupledCoeffStepsOfWitnesses fp v k hk W) init =
      Fin.foldl k
        (fun state i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanCoupledCoeffStepOfWitness fp v idx (W i)
          step.next state)
        init := by
  dsimp [kahanCoupledCoeffFold, kahanCoupledCoeffStepsOfWitnesses]
  rw [Compensated.Kahan.Internal.listFoldlOfFn_eq_finFoldl]

/-- The explicit-witness coupled coefficient recurrence over the first `k`
Kahan prefix-trace steps produces the actual stored-sum/correction prefix
state. -/
theorem kahanCoupledCoeffStepsOfWitnesses_finFold_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n)
      (W : KahanPrefixDeltaWitnessFamily fp v k hk),
      Fin.foldl k
        (fun state i =>
          let idx : Fin n := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
          let step := kahanCoupledCoeffStepOfWitness fp v idx (W i)
          step.next state)
        KahanState.zero =
      kahanPrefixState fp v k hk
  | 0, _hk, _W => by
      simp [kahanPrefixState, KahanState.zero]
  | k + 1, hk, W => by
      have hprev_le : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let Wprev : KahanPrefixDeltaWitnessFamily fp v k hprev_le :=
        fun i => by
          simpa using W i.castSucc
      let prev := kahanPrefixState fp v k hprev_le
      let step := kahanCoupledCoeffStepOfWitness fp v idx (W last)
      have hih :=
        kahanCoupledCoeffStepsOfWitnesses_finFold_eq_prefix_state
          fp v k hprev_le Wprev
      have hih' :
          Fin.foldl k
            (fun state i =>
              let idx : Fin n := ⟨(i.castSucc).val,
                Nat.lt_of_lt_of_le (i.castSucc).isLt hk⟩
              let step := kahanCoupledCoeffStepOfWitness fp v idx
                (W i.castSucc)
              step.next state)
            KahanState.zero = prev := by
        simpa [Wprev, prev] using hih
      have hfoldPrefix :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prev := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hstep :
          kahanStep fp (v idx) prev = step.next prev := by
        have htrace :=
          kahanTrace_eq_coupledCoeffStepOfWitness_next fp v idx (W last)
        dsimp at htrace
        simpa [idx, last, prev, step, kahanTrace, kahanStep,
          KahanStepTrace.nextState] using htrace
      rw [Fin.foldl_succ_last]
      rw [hih']
      rw [hfoldPrefix, hstep]
      rfl

/-- Explicit-witness coupled Kahan steps fold from zero to the actual prefix
state. -/
theorem kahanCoupledCoeffStepsOfWitnesses_fold_zero_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    kahanCoupledCoeffFold
        (kahanCoupledCoeffStepsOfWitnesses fp v k hk W) KahanState.zero =
      kahanPrefixState fp v k hk := by
  rw [kahanCoupledCoeffStepsOfWitnesses_fold_eq_finFold]
  exact kahanCoupledCoeffStepsOfWitnesses_finFold_eq_prefix_state
    fp v k hk W

/-- The propagated source-vector unroll of explicit-witness coupled Kahan
steps is exactly the actual prefix `(s,e)` state. -/
theorem kahanCoupledCoeffStepsOfWitnesses_sourceUnroll_eq_prefix_state
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    kahanCoupledSourceUnroll
        (kahanCoupledCoeffStepsOfWitnesses fp v k hk W) =
      kahanPrefixState fp v k hk := by
  rw [← kahanCoupledCoeffFold_zero_eq_sourceUnroll]
  exact kahanCoupledCoeffStepsOfWitnesses_fold_zero_eq_prefix_state
    fp v k hk W

/-- Returned stored sum of the first `k` explicit-witness coupled Kahan steps
as an explicit source-input coefficient sum. -/
theorem kahanCoupledCoeffStepsOfWitnesses_prefixState_s_eq_sum_sourceCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    let steps := kahanCoupledCoeffStepsOfWitnesses fp v k hk W
    (kahanPrefixState fp v k hk).s =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).s := by
  dsimp
  rw [← kahanCoupledCoeffStepsOfWitnesses_sourceUnroll_eq_prefix_state
    fp v k hk W]
  exact kahanCoupledSourceUnroll_s_eq_sum_sourceCoeff
    (kahanCoupledCoeffStepsOfWitnesses fp v k hk W)

/-- Retained correction of the first `k` explicit-witness coupled Kahan steps
as an explicit source-input coefficient sum. -/
theorem kahanCoupledCoeffStepsOfWitnesses_prefixState_e_eq_sum_sourceCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    let steps := kahanCoupledCoeffStepsOfWitnesses fp v k hk W
    (kahanPrefixState fp v k hk).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * (kahanCoupledSourceCoeff steps i).e := by
  dsimp
  rw [← kahanCoupledCoeffStepsOfWitnesses_sourceUnroll_eq_prefix_state
    fp v k hk W]
  exact kahanCoupledSourceUnroll_e_eq_sum_sourceCoeff
    (kahanCoupledCoeffStepsOfWitnesses fp v k hk W)

/-- Compensated total of the first `k` explicit-witness coupled Kahan steps as
an explicit source-input sum over paired source coefficients. -/
theorem kahanCoupledCoeffStepsOfWitnesses_prefixState_total_eq_sum_sourceTotalCoeff
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (W : KahanPrefixDeltaWitnessFamily fp v k hk) :
    let steps := kahanCoupledCoeffStepsOfWitnesses fp v k hk W
    (kahanPrefixState fp v k hk).s +
        (kahanPrefixState fp v k hk).e =
      ∑ i : Fin steps.length,
        (steps.get i).x * kahanCoupledSourceTotalCoeff steps i := by
  dsimp
  rw [← kahanCoupledCoeffStepsOfWitnesses_sourceUnroll_eq_prefix_state
    fp v k hk W]
  exact kahanCoupledSourceUnroll_total_eq_sum_sourceTotalCoeff
    (kahanCoupledCoeffStepsOfWitnesses fp v k hk W)

end NumStability
