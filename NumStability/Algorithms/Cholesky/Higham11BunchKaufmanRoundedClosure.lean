/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Algorithm 11.2 and Theorems 11.3--11.4: rounded closure

This module derives the local block-LDLT backward-error facts for the literal
rounded Bunch--Kaufman execution.  In particular, the two-by-two path uses the
actual selected two-step GEPP solve and its proved equation-(11.5)
componentwise backward error.  It never assumes the formally false
coefficient-one absolute coupling from the older `FlMixedPivots` interface.

The honest coupling is

  `|w_i| |c_j| <= (1 + 36 u) |w_i| |E| |w_j|`.

Together with the signed residual consequence of (11.5), this yields a fully
derived local Schur residual with constant 18 in units of `gamma_3`.

Source: Higham, 2nd ed., section 11.1.2, pp. 217--219, Algorithm 11.2,
equation (11.5), and Theorems 11.3--11.4.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedExecution
import NumStability.Algorithms.Cholesky.TwoByTwoSchurStepCh11Closure

open scoped BigOperators

namespace NumStability

open Ch11Closure.Mixed
open Ch11Closure.TwoStep

/-! ## The actual selected two-by-two pivot paths -/

/-- Signed leading-block contribution `w_i E w_j^T` at a rounded case-(4)
stage, in the permuted active coordinates. -/
noncomputable def higham11_2_bunchKaufmanPivotPathTwo (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i j : Fin n) : Real :=
  ∑ p : Fin 2, ∑ q : Fin 2,
    higham11_2_bunchKaufmanFlMultTwo fp A i p *
      higham11_2_bunchKaufmanRoundedActive A
        (embedTwo n p) (embedTwo n q) *
      higham11_2_bunchKaufmanFlMultTwo fp A j q

/-- Absolute leading-block contribution `|w_i| |E| |w_j|`. -/
noncomputable def higham11_2_bunchKaufmanPivotPathTwoAbs (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i j : Fin n) : Real :=
  ∑ p : Fin 2, ∑ q : Fin 2,
    |higham11_2_bunchKaufmanFlMultTwo fp A i p| *
      |higham11_2_bunchKaufmanRoundedActive A
        (embedTwo n p) (embedTwo n q)| *
      |higham11_2_bunchKaufmanFlMultTwo fp A j q|

/-- Absolute pivot-row path `(|E| |w_j|)_p`. -/
noncomputable def higham11_2_bunchKaufmanPivotRowTwoAbs (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (p : Fin 2) (j : Fin n) : Real :=
  ∑ q : Fin 2,
    |higham11_2_bunchKaufmanRoundedActive A
      (embedTwo n p) (embedTwo n q)| *
      |higham11_2_bunchKaufmanFlMultTwo fp A j q|

/-- Absolute pivot-column path `(|w_i| |E|)_q`. -/
noncomputable def higham11_2_bunchKaufmanPivotColTwoAbs (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i : Fin n) (q : Fin 2) : Real :=
  ∑ p : Fin 2,
    |higham11_2_bunchKaufmanFlMultTwo fp A i p| *
      |higham11_2_bunchKaufmanRoundedActive A
        (embedTwo n p) (embedTwo n q)|

/-- Exact dot product `w_i c_j^T` that the rounded Schur update evaluates. -/
noncomputable def higham11_2_bunchKaufmanTrailingDotTwo (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i j : Fin n) : Real :=
  ∑ p : Fin 2,
    higham11_2_bunchKaufmanFlMultTwo fp A i p *
      higham11_2_bunchKaufmanRoundedActive A
        j.succ.succ (embedTwo n p)

theorem higham11_2_bunchKaufmanPivotPathTwoAbs_nonneg (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i j : Fin n) :
    0 <= higham11_2_bunchKaufmanPivotPathTwoAbs fp A i j := by
  unfold higham11_2_bunchKaufmanPivotPathTwoAbs
  exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)

/-! ## Signed residual consequence of equation (11.5) -/

/-- Bilinear form of the componentwise residual lemma.  This is the signed
bridge needed by the Schur update: multiplying the row residual by an
arbitrary vector does not introduce a new premise. -/
theorem higham11_5_twoByTwoPivotSolveStable_bilinear_residual
    (u c : Real) (E DeltaE : Fin 2 -> Fin 2 -> Real)
    (x y f : Fin 2 -> Real)
    (hstable : higham11_5_twoByTwoPivotSolveStable u c E DeltaE)
    (heq : forall p : Fin 2,
      ∑ q : Fin 2, (E p q + DeltaE p q) * y q = f p) :
    |(∑ p : Fin 2, ∑ q : Fin 2, x p * E p q * y q) -
        ∑ p : Fin 2, x p * f p| <=
      c * u * higham11_5_twoByTwoAbsBilinear x E y := by
  have hrow := higham11_5_twoByTwoPivotSolveStable_residual
    u c E DeltaE y f hstable heq
  have hrearrange :
      (∑ p : Fin 2, ∑ q : Fin 2, x p * E p q * y q) -
          ∑ p : Fin 2, x p * f p =
        ∑ p : Fin 2, x p * ((∑ q : Fin 2, E p q * y q) - f p) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [mul_sub, Finset.mul_sum]
    apply congrArg (fun z => z - x p * f p)
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hrearrange]
  calc
    |∑ p : Fin 2, x p * ((∑ q : Fin 2, E p q * y q) - f p)| <=
        ∑ p : Fin 2, |x p * ((∑ q : Fin 2, E p q * y q) - f p)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : Fin 2, |x p| *
        |(∑ q : Fin 2, E p q * y q) - f p| := by
      apply Finset.sum_congr rfl
      intro p _
      rw [abs_mul]
    _ <= ∑ p : Fin 2, |x p| *
        (c * u * higham11_5_twoByTwoAbsRow E y p) := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_left (hrow p) (abs_nonneg _)
    _ = c * u * higham11_5_twoByTwoAbsBilinear x E y := by
      simp only [higham11_5_twoByTwoAbsRow,
        higham11_5_twoByTwoAbsBilinear, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring

/-- The actual selected pivot-row residual, fully produced by the GEPP
equation-(11.5) certificate. -/
theorem higham11_2_bunchKaufmanPivotRowTwo_residual
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (p : Fin 2) (j : Fin n) :
    |(∑ q : Fin 2,
        higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) (embedTwo n q) *
          higham11_2_bunchKaufmanFlMultTwo fp A j q) -
        higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n p) j.succ.succ| <=
      36 * fp.u * higham11_2_bunchKaufmanPivotRowTwoAbs fp A p j := by
  obtain ⟨DeltaE, hstable, heq⟩ :=
    higham11_2_bunchKaufmanFlMultTwo_active_certificate
      fp hval9 hsmall9 A hA hbranch hsecond j
  have hres := higham11_5_twoByTwoPivotSolveStable_residual
    fp.u 36
    (fun p q => higham11_2_bunchKaufmanRoundedActive A
      (embedTwo n p) (embedTwo n q))
    DeltaE
      (higham11_2_bunchKaufmanFlMultTwo fp A j)
      (fun p => higham11_2_bunchKaufmanRoundedActive A
        j.succ.succ (embedTwo n p)) hstable heq p
  have hB := higham11_2_bunchKaufmanRoundedActive_symmetric A hA
  rw [hB j.succ.succ (embedTwo n p)] at hres
  simpa [higham11_2_bunchKaufmanPivotRowTwoAbs,
    higham11_5_twoByTwoAbsRow] using hres

/-- The actual selected pivot-column residual.  It is the row residual after
using symmetry of the active pivot block and active matrix. -/
theorem higham11_2_bunchKaufmanPivotColTwo_residual
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (i : Fin n) (q : Fin 2) :
    |(∑ p : Fin 2,
        higham11_2_bunchKaufmanFlMultTwo fp A i p *
          higham11_2_bunchKaufmanRoundedActive A
            (embedTwo n p) (embedTwo n q)) -
        higham11_2_bunchKaufmanRoundedActive A
          i.succ.succ (embedTwo n q)| <=
      36 * fp.u * higham11_2_bunchKaufmanPivotColTwoAbs fp A i q := by
  have hrow := higham11_2_bunchKaufmanPivotRowTwo_residual
    fp hval9 hsmall9 A hA hbranch hsecond q i
  have hB := higham11_2_bunchKaufmanRoundedActive_symmetric A hA
  have hsum :
      (∑ p : Fin 2,
        higham11_2_bunchKaufmanFlMultTwo fp A i p *
          higham11_2_bunchKaufmanRoundedActive A
            (embedTwo n p) (embedTwo n q)) =
        ∑ p : Fin 2,
          higham11_2_bunchKaufmanRoundedActive A
            (embedTwo n q) (embedTwo n p) *
            higham11_2_bunchKaufmanFlMultTwo fp A i p := by
    apply Finset.sum_congr rfl
    intro p _
    rw [hB (embedTwo n p) (embedTwo n q)]
    ring
  have hentry :
      higham11_2_bunchKaufmanRoundedActive A
          i.succ.succ (embedTwo n q) =
        higham11_2_bunchKaufmanRoundedActive A
          (embedTwo n q) i.succ.succ :=
    hB i.succ.succ (embedTwo n q)
  have habs :
      higham11_2_bunchKaufmanPivotColTwoAbs fp A i q =
        higham11_2_bunchKaufmanPivotRowTwoAbs fp A q i := by
    unfold higham11_2_bunchKaufmanPivotColTwoAbs
      higham11_2_bunchKaufmanPivotRowTwoAbs
    apply Finset.sum_congr rfl
    intro p _
    rw [hB (embedTwo n p) (embedTwo n q)]
    ring
  rw [hsum, hentry, habs]
  exact hrow

/-- Signed case-(4) Schur coupling derived from (11.5): the exact block path
differs from the dot product used by the update by at most
`36 u |w_i| |E| |w_j|`. -/
theorem higham11_2_bunchKaufmanPivotPathTwo_sub_dot_bound
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (i j : Fin n) :
    |higham11_2_bunchKaufmanPivotPathTwo fp A i j -
        higham11_2_bunchKaufmanTrailingDotTwo fp A i j| <=
      36 * fp.u * higham11_2_bunchKaufmanPivotPathTwoAbs fp A i j := by
  obtain ⟨DeltaE, hstable, heq⟩ :=
    higham11_2_bunchKaufmanFlMultTwo_active_certificate
      fp hval9 hsmall9 A hA hbranch hsecond j
  simpa [higham11_2_bunchKaufmanPivotPathTwo,
    higham11_2_bunchKaufmanTrailingDotTwo,
    higham11_2_bunchKaufmanPivotPathTwoAbs,
    higham11_5_twoByTwoAbsBilinear] using
    (higham11_5_twoByTwoPivotSolveStable_bilinear_residual
      fp.u 36
      (fun p q => higham11_2_bunchKaufmanRoundedActive A
        (embedTwo n p) (embedTwo n q))
      DeltaE
      (higham11_2_bunchKaufmanFlMultTwo fp A i)
      (higham11_2_bunchKaufmanFlMultTwo fp A j)
      (fun p => higham11_2_bunchKaufmanRoundedActive A
        j.succ.succ (embedTwo n p)) hstable heq)

/-! ## Fully derived rounded Schur residual -/

/-- Pure rounding error of the actual case-(4) raw Schur update. -/
theorem higham11_2_bunchKaufmanRawSchurTwo_dot_residual
    (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) (i j : Fin n) :
    |higham11_2_bunchKaufmanTrailingDotTwo fp A i j +
        higham11_2_bunchKaufmanRawSchurTwo fp A i j -
        higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ| <=
      ((1 + fp.u) ^ 3 - 1) *
        (|higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ| +
          ∑ p : Fin 2,
            |higham11_2_bunchKaufmanFlMultTwo fp A i p| *
              |higham11_2_bunchKaufmanRoundedActive A
                j.succ.succ (embedTwo n p)|) := by
  let B := higham11_2_bunchKaufmanRoundedActive A
  let w0 := higham11_2_bunchKaufmanFlMultTwo fp A i 0
  let w1 := higham11_2_bunchKaufmanFlMultTwo fp A i 1
  let c0 := B j.succ.succ 0
  let c1 := B j.succ.succ (Fin.succ 0)
  let b := B i.succ.succ j.succ.succ
  obtain ⟨sigma, hsigma, hsub⟩ :=
    fp.model_sub b
      (fp.fl_add (fp.fl_mul w0 c0) (fp.fl_mul w1 c1))
  obtain ⟨alpha, halpha, hadd⟩ :=
    fp.model_add (fp.fl_mul w0 c0) (fp.fl_mul w1 c1)
  obtain ⟨mu0, hmu0, hmul0⟩ := fp.model_mul w0 c0
  obtain ⟨mu1, hmu1, hmul1⟩ := fp.model_mul w1 c1
  have hround := round_residual_bound fp.u (w0 * c0) (w1 * c1) b
    mu0 mu1 alpha sigma fp.u_nonneg hmu0 hmu1 halpha hsigma
  rw [abs_mul w0 c0, abs_mul w1 c1] at hround
  simp only [higham11_2_bunchKaufmanTrailingDotTwo,
    higham11_2_bunchKaufmanRawSchurTwo, Fin.sum_univ_two,
    embedTwo_zero, embedTwo_one]
  change |(w0 * c0 + w1 * c1) +
      fp.fl_sub b
        (fp.fl_add (fp.fl_mul w0 c0) (fp.fl_mul w1 c1)) - b| <=
    ((1 + fp.u) ^ 3 - 1) *
      (|b| + (|w0| * |c0| + |w1| * |c1|))
  rw [hsub, hadd, hmul0, hmul1]
  simpa [add_assoc] using hround

/-- The honest `(1+36u)` coupling bounds the magnitude entering the rounded
Schur update. -/
theorem higham11_2_bunchKaufmanTrailingDotTwo_abs_input_bound
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (i j : Fin n) :
    (∑ p : Fin 2,
        |higham11_2_bunchKaufmanFlMultTwo fp A i p| *
          |higham11_2_bunchKaufmanRoundedActive A
            j.succ.succ (embedTwo n p)|) <=
      (1 + 36 * fp.u) *
        higham11_2_bunchKaufmanPivotPathTwoAbs fp A i j := by
  simpa [higham11_2_bunchKaufmanPivotPathTwoAbs] using
    higham11_2_bunchKaufmanFlMultTwo_active_abs_coupling
      fp hval9 hsmall9 A hA hbranch hsecond i j

/-- Numeric conversion used by the corrected local Schur theorem. -/
theorem higham11_2_thirtySix_u_le_twelve_gamma3
    (fp : FPModel) (hval3 : gammaValid fp 3) :
    36 * fp.u <= 12 * gamma fp 3 := by
  have h := n_mul_u_le_gamma fp 3 hval3
  calc
    36 * fp.u = 12 * ((3 : Real) * fp.u) := by ring
    _ <= 12 * gamma fp 3 := mul_le_mul_of_nonneg_left h (by norm_num)

/-- Under the actual GEPP run radius, the corrected coupling factor is at most
three. -/
theorem higham11_2_one_add_thirtySix_u_le_three
    (fp : FPModel) (hsmall9 : (9 : Real) * fp.u <= 1 / 2) :
    1 + 36 * fp.u <= 3 := by
  nlinarith [fp.u_nonneg]

/-- Fully derived case-(4) raw-Schur residual.  Constant 18 consists of 12
for the signed equation-(11.5) solve residual and 6 for the three rounded
Schur-update operations after the honest `(1+36u)` coupling. -/
theorem higham11_2_bunchKaufmanRawSchurTwo_residual_bound
    (fp : FPModel) (hval3 : gammaValid fp 3)
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (i j : Fin n) :
    |higham11_2_bunchKaufmanPivotPathTwo fp A i j +
        higham11_2_bunchKaufmanRawSchurTwo fp A i j -
        higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ| <=
      18 * gamma fp 3 *
        (|higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ| +
          higham11_2_bunchKaufmanPivotPathTwoAbs fp A i j) := by
  let Babs :=
    |higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ|
  let Pabs := higham11_2_bunchKaufmanPivotPathTwoAbs fp A i j
  let Cabs := ∑ p : Fin 2,
    |higham11_2_bunchKaufmanFlMultTwo fp A i p| *
      |higham11_2_bunchKaufmanRoundedActive A j.succ.succ (embedTwo n p)|
  have hP0 : 0 <= Pabs :=
    higham11_2_bunchKaufmanPivotPathTwoAbs_nonneg fp A i j
  have hB0 : 0 <= Babs := abs_nonneg _
  have hBP0 : 0 <= Babs + Pabs := add_nonneg hB0 hP0
  have hsolve := higham11_2_bunchKaufmanPivotPathTwo_sub_dot_bound
    fp hval9 hsmall9 A hA hbranch hsecond i j
  have hround := higham11_2_bunchKaufmanRawSchurTwo_dot_residual fp A i j
  have hC := higham11_2_bunchKaufmanTrailingDotTwo_abs_input_bound
    fp hval9 hsmall9 A hA hbranch hsecond i j
  have huGamma := higham11_2_thirtySix_u_le_twelve_gamma3 fp hval3
  have hcouple := higham11_2_one_add_thirtySix_u_le_three fp hsmall9
  have hgamma0 : 0 <= gamma fp 3 := gamma_nonneg fp hval3
  have hcube := cube_sub_one_le_two_gamma3 fp hval3
  have hcube0 : 0 <= (1 + fp.u) ^ 3 - 1 := by
    nlinarith [fp.u_nonneg, mul_nonneg fp.u_nonneg fp.u_nonneg,
      mul_nonneg (mul_nonneg fp.u_nonneg fp.u_nonneg) fp.u_nonneg]
  have hsolve' :
      |higham11_2_bunchKaufmanPivotPathTwo fp A i j -
          higham11_2_bunchKaufmanTrailingDotTwo fp A i j| <=
        12 * gamma fp 3 * (Babs + Pabs) := by
    calc
      |higham11_2_bunchKaufmanPivotPathTwo fp A i j -
          higham11_2_bunchKaufmanTrailingDotTwo fp A i j| <=
          36 * fp.u * Pabs := hsolve
      _ <= 12 * gamma fp 3 * Pabs :=
        mul_le_mul_of_nonneg_right huGamma hP0
      _ <= 12 * gamma fp 3 * (Babs + Pabs) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by norm_num) hgamma0)
  have hround' :
      |higham11_2_bunchKaufmanTrailingDotTwo fp A i j +
          higham11_2_bunchKaufmanRawSchurTwo fp A i j -
          higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ| <=
        6 * gamma fp 3 * (Babs + Pabs) := by
    have hinput : Babs + Cabs <= 3 * (Babs + Pabs) := by
      have hC3 : Cabs <= 3 * Pabs := by
        calc Cabs <= (1 + 36 * fp.u) * Pabs := hC
          _ <= 3 * Pabs := mul_le_mul_of_nonneg_right hcouple hP0
      nlinarith
    calc
      |higham11_2_bunchKaufmanTrailingDotTwo fp A i j +
          higham11_2_bunchKaufmanRawSchurTwo fp A i j -
          higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ| <=
          ((1 + fp.u) ^ 3 - 1) * (Babs + Cabs) := hround
      _ <= ((1 + fp.u) ^ 3 - 1) * (3 * (Babs + Pabs)) :=
        mul_le_mul_of_nonneg_left hinput hcube0
      _ <= (2 * gamma fp 3) * (3 * (Babs + Pabs)) :=
        mul_le_mul_of_nonneg_right hcube (mul_nonneg (by norm_num) hBP0)
      _ = 6 * gamma fp 3 * (Babs + Pabs) := by ring
  have hsplit :
      higham11_2_bunchKaufmanPivotPathTwo fp A i j +
          higham11_2_bunchKaufmanRawSchurTwo fp A i j -
          higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ =
        (higham11_2_bunchKaufmanPivotPathTwo fp A i j -
          higham11_2_bunchKaufmanTrailingDotTwo fp A i j) +
        (higham11_2_bunchKaufmanTrailingDotTwo fp A i j +
          higham11_2_bunchKaufmanRawSchurTwo fp A i j -
          higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ) := by
    ring
  rw [hsplit]
  calc
    |(higham11_2_bunchKaufmanPivotPathTwo fp A i j -
        higham11_2_bunchKaufmanTrailingDotTwo fp A i j) +
      (higham11_2_bunchKaufmanTrailingDotTwo fp A i j +
        higham11_2_bunchKaufmanRawSchurTwo fp A i j -
        higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ)| <=
      |higham11_2_bunchKaufmanPivotPathTwo fp A i j -
        higham11_2_bunchKaufmanTrailingDotTwo fp A i j| +
      |higham11_2_bunchKaufmanTrailingDotTwo fp A i j +
        higham11_2_bunchKaufmanRawSchurTwo fp A i j -
        higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ| :=
      abs_add_le _ _
    _ <= 12 * gamma fp 3 * (Babs + Pabs) +
        6 * gamma fp 3 * (Babs + Pabs) := add_le_add hsolve' hround'
    _ = 18 * gamma fp 3 * (Babs + Pabs) := by ring

/-! ## Stored symmetry and the one-by-one stages -/

theorem higham11_2_bunchKaufmanPivotPathTwo_symm (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) (i j : Fin n) :
    higham11_2_bunchKaufmanPivotPathTwo fp A i j =
      higham11_2_bunchKaufmanPivotPathTwo fp A j i := by
  have hB := higham11_2_bunchKaufmanRoundedActive_symmetric A hA
  have h01 := hB (embedTwo n (0 : Fin 2)) (embedTwo n (1 : Fin 2))
  simp only [higham11_2_bunchKaufmanPivotPathTwo, Fin.sum_univ_two]
  rw [h01]
  ring

theorem higham11_2_bunchKaufmanPivotPathTwoAbs_symm (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A) (i j : Fin n) :
    higham11_2_bunchKaufmanPivotPathTwoAbs fp A i j =
      higham11_2_bunchKaufmanPivotPathTwoAbs fp A j i := by
  have hB := higham11_2_bunchKaufmanRoundedActive_symmetric A hA
  have h01 := hB (embedTwo n (0 : Fin 2)) (embedTwo n (1 : Fin 2))
  simp only [higham11_2_bunchKaufmanPivotPathTwoAbs, Fin.sum_univ_two]
  rw [h01]
  ring

/-- The stored-symmetric case-(4) Schur matrix satisfies the same local
factorization residual as the raw computed triangle. -/
theorem higham11_2_bunchKaufmanRoundedSchurTwo_residual_bound
    (fp : FPModel) (hval3 : gammaValid fp 3)
    (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hbranch : higham11_2_bunchKaufmanFirstBranch (by omega)
      higham11_1_bunchParlettAlpha A = BunchKaufmanCase.case4)
    (hsecond : higham11_2_flSelectedTwoByTwoSecondPivot fp (by omega) A ≠ 0)
    (i j : Fin n) :
    |higham11_2_bunchKaufmanPivotPathTwo fp A i j +
        higham11_2_bunchKaufmanRoundedSchurTwo fp A i j -
        higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ| <=
      18 * gamma fp 3 *
        (|higham11_2_bunchKaufmanRoundedActive A i.succ.succ j.succ.succ| +
          higham11_2_bunchKaufmanPivotPathTwoAbs fp A i j) := by
  classical
  by_cases hij : i.val <= j.val
  · simpa [higham11_2_bunchKaufmanRoundedSchurTwo, hij] using
      higham11_2_bunchKaufmanRawSchurTwo_residual_bound
        fp hval3 hval9 hsmall9 A hA hbranch hsecond i j
  · have hji : j.val <= i.val := (Nat.le_total j.val i.val).resolve_right hij
    have h := higham11_2_bunchKaufmanRawSchurTwo_residual_bound
      fp hval3 hval9 hsmall9 A hA hbranch hsecond j i
    rw [higham11_2_bunchKaufmanPivotPathTwo_symm fp A hA j i,
      higham11_2_bunchKaufmanPivotPathTwoAbs_symm fp A hA j i,
      (higham11_2_bunchKaufmanRoundedActive_symmetric A hA)
        j.succ.succ i.succ.succ] at h
    simpa [higham11_2_bunchKaufmanRoundedSchurTwo, hij, hji] using h

/-- Actual rounded scalar multiplier for a selected one-by-one stage in active
coordinates. -/
noncomputable def higham11_2_bunchKaufmanFlMultOne (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i : Fin (n + 1)) : Real :=
  let B := higham11_2_bunchKaufmanRoundedActive A
  fp.fl_div (B i.succ 0) (B 0 0)

noncomputable def higham11_2_bunchKaufmanPivotPathOne (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i j : Fin (n + 1)) : Real :=
  higham11_2_bunchKaufmanFlMultOne fp A i *
    higham11_2_bunchKaufmanRoundedActive A 0 0 *
    higham11_2_bunchKaufmanFlMultOne fp A j

noncomputable def higham11_2_bunchKaufmanPivotPathOneAbs (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i j : Fin (n + 1)) : Real :=
  |higham11_2_bunchKaufmanFlMultOne fp A i| *
    |higham11_2_bunchKaufmanRoundedActive A 0 0| *
    |higham11_2_bunchKaufmanFlMultOne fp A j|

noncomputable def higham11_2_bunchKaufmanRawSchurOne (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2)) :
    Higham11RoundedBunchKaufmanMatrix (n + 1) :=
  flSchurCompl (n + 1) fp (higham11_2_bunchKaufmanRoundedActive A)

theorem higham11_2_bunchKaufmanFlMultOne_row_residual
    (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hpivot : higham11_2_bunchKaufmanRoundedActive A 0 0 ≠ 0)
    (j : Fin (n + 1)) :
    |higham11_2_bunchKaufmanRoundedActive A 0 0 *
        higham11_2_bunchKaufmanFlMultOne fp A j -
      higham11_2_bunchKaufmanRoundedActive A 0 j.succ| <=
      fp.u * |higham11_2_bunchKaufmanRoundedActive A 0 j.succ| := by
  let B := higham11_2_bunchKaufmanRoundedActive A
  have hB := higham11_2_bunchKaufmanRoundedActive_symmetric A hA
  obtain ⟨delta, hdelta, hdiv⟩ := fp.model_div (B j.succ 0) (B 0 0) hpivot
  have hB' : B j.succ 0 = B 0 j.succ := hB j.succ 0
  have heq : B 0 0 * (B j.succ 0 / B 0 0 * (1 + delta)) - B 0 j.succ =
      B 0 j.succ * delta := by
    rw [hB']
    calc
      B 0 0 * (B 0 j.succ / B 0 0 * (1 + delta)) - B 0 j.succ =
          (B 0 j.succ / B 0 0 * B 0 0) * (1 + delta) - B 0 j.succ := by ring
      _ = B 0 j.succ * (1 + delta) - B 0 j.succ := by
        rw [div_mul_cancel₀ _ hpivot]
      _ = B 0 j.succ * delta := by ring
  change |B 0 0 * fp.fl_div (B j.succ 0) (B 0 0) - B 0 j.succ| <=
    fp.u * |B 0 j.succ|
  rw [hdiv, heq, abs_mul]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hdelta (abs_nonneg (B 0 j.succ)))

theorem higham11_2_bunchKaufmanFlMultOne_col_residual
    (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hpivot : higham11_2_bunchKaufmanRoundedActive A 0 0 ≠ 0)
    (i : Fin (n + 1)) :
    |higham11_2_bunchKaufmanFlMultOne fp A i *
        higham11_2_bunchKaufmanRoundedActive A 0 0 -
      higham11_2_bunchKaufmanRoundedActive A i.succ 0| <=
      fp.u * |higham11_2_bunchKaufmanRoundedActive A i.succ 0| := by
  let B := higham11_2_bunchKaufmanRoundedActive A
  obtain ⟨delta, hdelta, hdiv⟩ := fp.model_div (B i.succ 0) (B 0 0) hpivot
  have heq : B i.succ 0 / B 0 0 * (1 + delta) * B 0 0 - B i.succ 0 =
      B i.succ 0 * delta := by
    calc
      B i.succ 0 / B 0 0 * (1 + delta) * B 0 0 - B i.succ 0 =
          (B i.succ 0 / B 0 0 * B 0 0) * (1 + delta) - B i.succ 0 := by ring
      _ = B i.succ 0 * (1 + delta) - B i.succ 0 := by
        rw [div_mul_cancel₀ _ hpivot]
      _ = B i.succ 0 * delta := by ring
  change |fp.fl_div (B i.succ 0) (B 0 0) * B 0 0 - B i.succ 0| <=
    fp.u * |B i.succ 0|
  rw [hdiv, heq, abs_mul]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hdelta (abs_nonneg (B i.succ 0)))

/-- Finite-precision correction to the scalar absolute coupling. -/
theorem higham11_2_bunchKaufmanFlMultOne_abs_coupling
    (fp : FPModel) (hsmall9 : (9 : Real) * fp.u <= 1 / 2)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hpivot : higham11_2_bunchKaufmanRoundedActive A 0 0 ≠ 0)
    (j : Fin (n + 1)) :
    |higham11_2_bunchKaufmanRoundedActive A 0 j.succ| <=
      2 * |higham11_2_bunchKaufmanRoundedActive A 0 0| *
        |higham11_2_bunchKaufmanFlMultOne fp A j| := by
  have hres := higham11_2_bunchKaufmanFlMultOne_row_residual
    fp A hA hpivot j
  have htri :
      |higham11_2_bunchKaufmanRoundedActive A 0 j.succ| <=
        |higham11_2_bunchKaufmanRoundedActive A 0 0 *
          higham11_2_bunchKaufmanFlMultOne fp A j| +
        |higham11_2_bunchKaufmanRoundedActive A 0 0 *
          higham11_2_bunchKaufmanFlMultOne fp A j -
          higham11_2_bunchKaufmanRoundedActive A 0 j.succ| := by
    calc
      |higham11_2_bunchKaufmanRoundedActive A 0 j.succ| =
          |higham11_2_bunchKaufmanRoundedActive A 0 0 *
              higham11_2_bunchKaufmanFlMultOne fp A j -
            (higham11_2_bunchKaufmanRoundedActive A 0 0 *
              higham11_2_bunchKaufmanFlMultOne fp A j -
              higham11_2_bunchKaufmanRoundedActive A 0 j.succ)| := by
            congr 1
            ring
      _ <= |higham11_2_bunchKaufmanRoundedActive A 0 0 *
              higham11_2_bunchKaufmanFlMultOne fp A j| +
            |higham11_2_bunchKaufmanRoundedActive A 0 0 *
              higham11_2_bunchKaufmanFlMultOne fp A j -
              higham11_2_bunchKaufmanRoundedActive A 0 j.succ| :=
          abs_sub _ _
  rw [abs_mul] at htri
  have hu : fp.u <= 1 / 18 := by nlinarith [fp.u_nonneg]
  nlinarith [abs_nonneg (higham11_2_bunchKaufmanRoundedActive A 0 j.succ),
    mul_nonneg (abs_nonneg (higham11_2_bunchKaufmanRoundedActive A 0 0))
      (abs_nonneg (higham11_2_bunchKaufmanFlMultOne fp A j))]

theorem higham11_2_bunchKaufmanRawSchurOne_dot_residual
    (fp : FPModel) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i j : Fin (n + 1)) :
    |higham11_2_bunchKaufmanFlMultOne fp A i *
        higham11_2_bunchKaufmanRoundedActive A 0 j.succ +
      higham11_2_bunchKaufmanRawSchurOne fp A i j -
        higham11_2_bunchKaufmanRoundedActive A i.succ j.succ| <=
      ((1 + fp.u) ^ 3 - 1) *
        (|higham11_2_bunchKaufmanRoundedActive A i.succ j.succ| +
          |higham11_2_bunchKaufmanFlMultOne fp A i| *
            |higham11_2_bunchKaufmanRoundedActive A 0 j.succ|) := by
  let B := higham11_2_bunchKaufmanRoundedActive A
  let w := higham11_2_bunchKaufmanFlMultOne fp A i
  let c := B 0 j.succ
  let b := B i.succ j.succ
  obtain ⟨sigma, hsigma, hsub⟩ := fp.model_sub b (fp.fl_mul w c)
  obtain ⟨mu, hmu, hmul⟩ := fp.model_mul w c
  have hround := round_residual_bound fp.u (w * c) 0 b mu 0 0 sigma
    fp.u_nonneg hmu (by simpa using fp.u_nonneg) (by simpa using fp.u_nonneg) hsigma
  rw [abs_mul w c, abs_zero, add_zero] at hround
  change |w * c + fp.fl_sub b (fp.fl_mul w c) - b| <=
    ((1 + fp.u) ^ 3 - 1) * (|b| + |w| * |c|)
  rw [hsub, hmul]
  simpa [add_assoc] using hround

/-- Fully derived one-by-one raw-Schur residual, with the computed scalar
division coupling kept honest. -/
theorem higham11_2_bunchKaufmanRawSchurOne_residual_bound
    (fp : FPModel) (hval3 : gammaValid fp 3)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hpivot : higham11_2_bunchKaufmanRoundedActive A 0 0 ≠ 0)
    (i j : Fin (n + 1)) :
    |higham11_2_bunchKaufmanPivotPathOne fp A i j +
        higham11_2_bunchKaufmanRawSchurOne fp A i j -
        higham11_2_bunchKaufmanRoundedActive A i.succ j.succ| <=
      5 * gamma fp 3 *
        (|higham11_2_bunchKaufmanRoundedActive A i.succ j.succ| +
          higham11_2_bunchKaufmanPivotPathOneAbs fp A i j) := by
  let Babs := |higham11_2_bunchKaufmanRoundedActive A i.succ j.succ|
  let Pabs := higham11_2_bunchKaufmanPivotPathOneAbs fp A i j
  let Cabs := |higham11_2_bunchKaufmanFlMultOne fp A i| *
    |higham11_2_bunchKaufmanRoundedActive A 0 j.succ|
  have hP0 : 0 <= Pabs := by
    unfold Pabs higham11_2_bunchKaufmanPivotPathOneAbs
    positivity
  have hB0 : 0 <= Babs := abs_nonneg _
  have hgamma0 : 0 <= gamma fp 3 := gamma_nonneg fp hval3
  have hcouple0 := higham11_2_bunchKaufmanFlMultOne_abs_coupling
    fp hsmall9 A hA hpivot j
  have hcouple : Cabs <= 2 * Pabs := by
    unfold Cabs Pabs higham11_2_bunchKaufmanPivotPathOneAbs
    calc
      |higham11_2_bunchKaufmanFlMultOne fp A i| *
          |higham11_2_bunchKaufmanRoundedActive A 0 j.succ| <=
        |higham11_2_bunchKaufmanFlMultOne fp A i| *
          (2 * |higham11_2_bunchKaufmanRoundedActive A 0 0| *
            |higham11_2_bunchKaufmanFlMultOne fp A j|) :=
          mul_le_mul_of_nonneg_left hcouple0 (abs_nonneg _)
      _ = 2 * (|higham11_2_bunchKaufmanFlMultOne fp A i| *
          |higham11_2_bunchKaufmanRoundedActive A 0 0| *
          |higham11_2_bunchKaufmanFlMultOne fp A j|) := by ring
  have hrow := higham11_2_bunchKaufmanFlMultOne_row_residual
    fp A hA hpivot j
  have hsolve :
      |higham11_2_bunchKaufmanPivotPathOne fp A i j -
        higham11_2_bunchKaufmanFlMultOne fp A i *
          higham11_2_bunchKaufmanRoundedActive A 0 j.succ| <=
        gamma fp 3 * Pabs := by
    have hmul := mul_le_mul_of_nonneg_left hrow
      (abs_nonneg (higham11_2_bunchKaufmanFlMultOne fp A i))
    have h3u := n_mul_u_le_gamma fp 3 hval3
    have h2u : 2 * fp.u <= gamma fp 3 := by
      calc
        2 * fp.u <= 3 * fp.u :=
          mul_le_mul_of_nonneg_right (by norm_num) fp.u_nonneg
        _ <= gamma fp 3 := by simpa using h3u
    have hraw :
        |higham11_2_bunchKaufmanPivotPathOne fp A i j -
          higham11_2_bunchKaufmanFlMultOne fp A i *
            higham11_2_bunchKaufmanRoundedActive A 0 j.succ| <=
          fp.u * Cabs := by
      unfold higham11_2_bunchKaufmanPivotPathOne Cabs
      have heq :
          higham11_2_bunchKaufmanFlMultOne fp A i *
                higham11_2_bunchKaufmanRoundedActive A 0 0 *
                higham11_2_bunchKaufmanFlMultOne fp A j -
              higham11_2_bunchKaufmanFlMultOne fp A i *
                higham11_2_bunchKaufmanRoundedActive A 0 j.succ =
            higham11_2_bunchKaufmanFlMultOne fp A i *
              (higham11_2_bunchKaufmanRoundedActive A 0 0 *
                higham11_2_bunchKaufmanFlMultOne fp A j -
                higham11_2_bunchKaufmanRoundedActive A 0 j.succ) := by ring
      rw [heq, abs_mul]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    calc
      |higham11_2_bunchKaufmanPivotPathOne fp A i j -
          higham11_2_bunchKaufmanFlMultOne fp A i *
            higham11_2_bunchKaufmanRoundedActive A 0 j.succ| <=
          fp.u * Cabs := hraw
      _ <= fp.u * (2 * Pabs) := mul_le_mul_of_nonneg_left hcouple fp.u_nonneg
      _ = (2 * fp.u) * Pabs := by ring
      _ <= gamma fp 3 * Pabs := mul_le_mul_of_nonneg_right h2u hP0
  have hround := higham11_2_bunchKaufmanRawSchurOne_dot_residual fp A i j
  have hcube := cube_sub_one_le_two_gamma3 fp hval3
  have hcube0 : 0 <= (1 + fp.u) ^ 3 - 1 := by
    nlinarith [fp.u_nonneg, mul_nonneg fp.u_nonneg fp.u_nonneg,
      mul_nonneg (mul_nonneg fp.u_nonneg fp.u_nonneg) fp.u_nonneg]
  have hround' :
      |higham11_2_bunchKaufmanFlMultOne fp A i *
          higham11_2_bunchKaufmanRoundedActive A 0 j.succ +
        higham11_2_bunchKaufmanRawSchurOne fp A i j -
          higham11_2_bunchKaufmanRoundedActive A i.succ j.succ| <=
        4 * gamma fp 3 * (Babs + Pabs) := by
    have hinput : Babs + Cabs <= 2 * (Babs + Pabs) := by nlinarith
    calc
      |higham11_2_bunchKaufmanFlMultOne fp A i *
          higham11_2_bunchKaufmanRoundedActive A 0 j.succ +
        higham11_2_bunchKaufmanRawSchurOne fp A i j -
          higham11_2_bunchKaufmanRoundedActive A i.succ j.succ| <=
          ((1 + fp.u) ^ 3 - 1) * (Babs + Cabs) := hround
      _ <= ((1 + fp.u) ^ 3 - 1) * (2 * (Babs + Pabs)) :=
        mul_le_mul_of_nonneg_left hinput hcube0
      _ <= (2 * gamma fp 3) * (2 * (Babs + Pabs)) :=
        mul_le_mul_of_nonneg_right hcube
          (mul_nonneg (by norm_num) (add_nonneg hB0 hP0))
      _ = 4 * gamma fp 3 * (Babs + Pabs) := by ring
  have hsplit :
      higham11_2_bunchKaufmanPivotPathOne fp A i j +
          higham11_2_bunchKaufmanRawSchurOne fp A i j -
          higham11_2_bunchKaufmanRoundedActive A i.succ j.succ =
        (higham11_2_bunchKaufmanPivotPathOne fp A i j -
          higham11_2_bunchKaufmanFlMultOne fp A i *
            higham11_2_bunchKaufmanRoundedActive A 0 j.succ) +
        (higham11_2_bunchKaufmanFlMultOne fp A i *
            higham11_2_bunchKaufmanRoundedActive A 0 j.succ +
          higham11_2_bunchKaufmanRawSchurOne fp A i j -
          higham11_2_bunchKaufmanRoundedActive A i.succ j.succ) := by ring
  rw [hsplit]
  calc
    |_ + _| <=
        |higham11_2_bunchKaufmanPivotPathOne fp A i j -
          higham11_2_bunchKaufmanFlMultOne fp A i *
            higham11_2_bunchKaufmanRoundedActive A 0 j.succ| +
        |higham11_2_bunchKaufmanFlMultOne fp A i *
            higham11_2_bunchKaufmanRoundedActive A 0 j.succ +
          higham11_2_bunchKaufmanRawSchurOne fp A i j -
          higham11_2_bunchKaufmanRoundedActive A i.succ j.succ| := abs_add_le _ _
    _ <= gamma fp 3 * Pabs + 4 * gamma fp 3 * (Babs + Pabs) :=
      add_le_add hsolve hround'
    _ <= 5 * gamma fp 3 * (Babs + Pabs) := by
      nlinarith [mul_nonneg hgamma0 hB0]

theorem higham11_2_bunchKaufmanPivotPathOne_symm (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i j : Fin (n + 1)) :
    higham11_2_bunchKaufmanPivotPathOne fp A i j =
      higham11_2_bunchKaufmanPivotPathOne fp A j i := by
  unfold higham11_2_bunchKaufmanPivotPathOne
  ring

theorem higham11_2_bunchKaufmanPivotPathOneAbs_symm (fp : FPModel)
    {n : Nat} (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (i j : Fin (n + 1)) :
    higham11_2_bunchKaufmanPivotPathOneAbs fp A i j =
      higham11_2_bunchKaufmanPivotPathOneAbs fp A j i := by
  unfold higham11_2_bunchKaufmanPivotPathOneAbs
  ring

theorem higham11_2_bunchKaufmanRoundedSchurOne_residual_bound
    (fp : FPModel) (hval3 : gammaValid fp 3)
    (hsmall9 : (9 : Real) * fp.u <= 1 / 2) {n : Nat}
    (A : Higham11RoundedBunchKaufmanMatrix (n + 2))
    (hA : IsSymmetricFiniteMatrix A)
    (hpivot : higham11_2_bunchKaufmanRoundedActive A 0 0 ≠ 0)
    (i j : Fin (n + 1)) :
    |higham11_2_bunchKaufmanPivotPathOne fp A i j +
        flStoredSymSchurCompl (n + 1) fp
          (higham11_2_bunchKaufmanRoundedActive A) i j -
        higham11_2_bunchKaufmanRoundedActive A i.succ j.succ| <=
      5 * gamma fp 3 *
        (|higham11_2_bunchKaufmanRoundedActive A i.succ j.succ| +
          higham11_2_bunchKaufmanPivotPathOneAbs fp A i j) := by
  classical
  by_cases hij : i.val <= j.val
  · simpa [flStoredSymSchurCompl, hij,
      higham11_2_bunchKaufmanRawSchurOne] using
      higham11_2_bunchKaufmanRawSchurOne_residual_bound
        fp hval3 hsmall9 A hA hpivot i j
  · have hji : j.val <= i.val := (Nat.le_total j.val i.val).resolve_right hij
    have h := higham11_2_bunchKaufmanRawSchurOne_residual_bound
      fp hval3 hsmall9 A hA hpivot j i
    rw [higham11_2_bunchKaufmanPivotPathOne_symm fp A j i,
      higham11_2_bunchKaufmanPivotPathOneAbs_symm fp A j i,
      (higham11_2_bunchKaufmanRoundedActive_symmetric A hA) j.succ i.succ] at h
    simpa [flStoredSymSchurCompl, hij, hji,
      higham11_2_bunchKaufmanRawSchurOne] using h

end NumStability
