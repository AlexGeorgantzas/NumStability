/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreDeterminantMoment
import NumStability.Algorithms.TestMatrices.Higham28GinibreRecurrence
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Higham Chapter 28: scalar glue for the Ginibre expectation

The determinant-moment recurrence and the finite expected-count recurrence
use superficially different Gamma factors.  Legendre duplication shows that
the Corollary 3.1 normalization converts the former increment exactly into
the latter one.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Multiplying the determinant-moment increment by the Corollary 3.1
normalization produces the Gamma-ratio increment in the expected-count
recurrence. -/
theorem ginibreCorollary31Factor_mul_increment (m : ℕ) (hm : 0 < m) :
    ginibreCorollary31Factor (m + 1) *
        ginibreAbsoluteCharacteristicMomentIncrement m =
      Real.sqrt (2 / Real.pi) *
        (Real.Gamma ((m : ℝ) - 1 / 2) / Real.Gamma (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hGm : Real.Gamma (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos hmR)
  have hGhalf : Real.Gamma ((m : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hGhalf' : Real.Gamma ((m : ℝ) / 2 + 1 / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have hpow : Real.rpow 2 ((3 - (m : ℝ)) / 2) /
        Real.rpow 2 ((m : ℝ) / 2) =
      Real.sqrt 2 * Real.rpow 2 (1 - (m : ℝ)) := by
    change (2 : ℝ) ^ ((3 - (m : ℝ)) / 2) /
        (2 : ℝ) ^ ((m : ℝ) / 2) =
      Real.sqrt 2 * (2 : ℝ) ^ (1 - (m : ℝ))
    calc
      (2 : ℝ) ^ ((3 - (m : ℝ)) / 2) /
          (2 : ℝ) ^ ((m : ℝ) / 2) =
          (2 : ℝ) ^ (((3 - (m : ℝ)) / 2) - ((m : ℝ) / 2)) :=
        (Real.rpow_sub (by norm_num : (0 : ℝ) < 2) _ _).symm
      _ = (2 : ℝ) ^ ((1 / 2 : ℝ) + (1 - (m : ℝ))) := by
        congr 1
        ring
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 - (m : ℝ)) := by
        exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
      _ = Real.sqrt 2 * (2 : ℝ) ^ (1 - (m : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
  have hdup := Real.Gamma_mul_Gamma_add_half ((m : ℝ) / 2)
  have htwo : 2 * ((m : ℝ) / 2) = (m : ℝ) := by ring
  rw [htwo] at hdup
  change Real.Gamma ((m : ℝ) / 2) *
      Real.Gamma ((m : ℝ) / 2 + 1 / 2) =
    Real.Gamma (m : ℝ) * Real.rpow 2 (1 - (m : ℝ)) *
      Real.sqrt Real.pi at hdup
  have hsqrtRatio : Real.sqrt (2 / Real.pi) =
      Real.sqrt 2 / Real.sqrt Real.pi := by
    rw [Real.sqrt_div (by positivity : 0 ≤ (2 : ℝ))]
  unfold ginibreCorollary31Factor
  unfold ginibreAbsoluteCharacteristicMomentIncrement
  push_cast
  rw [show ((m : ℝ) + 1 - 1) / 2 = (m : ℝ) / 2 by ring]
  rw [show ((m : ℝ) + 1) / 2 = (m : ℝ) / 2 + 1 / 2 by ring]
  rw [hsqrtRatio]
  have hpow0 : Real.rpow 2 ((m : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hpow1 : Real.rpow 2 (1 - (m : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hmge : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hGshift : Real.Gamma ((m : ℝ) - 1 / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  field_simp [hGm, hGhalf, hGhalf', hsqrtPi, hpow0, hpow1, hGshift]
  rw [show ((m : ℝ) * 2 - 1) / 2 = (m : ℝ) - 1 / 2 by ring]
  rw [show ((m : ℝ) + 1) / 2 = (m : ℝ) / 2 + 1 / 2 by ring]
  have hpowCross : Real.rpow 2 ((3 - (m : ℝ)) / 2) =
      Real.sqrt 2 * Real.rpow 2 (1 - (m : ℝ)) *
        Real.rpow 2 ((m : ℝ) / 2) :=
    (div_eq_iff hpow0).mp hpow
  calc
    Real.sqrt Real.pi * Real.rpow 2 ((3 - (m : ℝ)) / 2) *
          Real.Gamma ((m : ℝ) - 1 / 2) * Real.Gamma (m : ℝ) =
        Real.sqrt 2 * Real.rpow 2 ((m : ℝ) / 2) *
          Real.Gamma ((m : ℝ) - 1 / 2) *
            (Real.Gamma (m : ℝ) * Real.rpow 2 (1 - (m : ℝ)) *
              Real.sqrt Real.pi) := by
      rw [hpowCross]
      ring
    _ = Real.sqrt 2 * Real.rpow 2 ((m : ℝ) / 2) *
          Real.Gamma ((m : ℝ) - 1 / 2) *
            (Real.Gamma ((m : ℝ) / 2) *
              Real.Gamma ((m : ℝ) / 2 + 1 / 2)) := by
      rw [hdup]
    _ = Real.rpow 2 ((m : ℝ) / 2) *
          Real.Gamma ((m : ℝ) / 2 + 1 / 2) *
          Real.Gamma ((m : ℝ) - 1 / 2) *
          Real.Gamma ((m : ℝ) / 2) * Real.sqrt 2 := by
      ring

/-- The normalized determinant-moment increment is exactly the two-step
increment of the finite real-Ginibre closed form. -/
theorem ginibreCorollary31Factor_mul_increment_eq_closedForm_shift
    (m : ℕ) (hm : 0 < m) :
    ginibreCorollary31Factor (m + 2) *
        ginibreAbsoluteCharacteristicMomentIncrement (m + 1) =
      realGinibreExpectedCountClosedForm (m + 2) -
        realGinibreExpectedCountClosedForm m := by
  rw [ginibreCorollary31Factor_mul_increment (m + 1) (Nat.zero_lt_succ m)]
  push_cast
  rw [show (m : ℝ) + 1 - 1 / 2 = (m : ℝ) + 1 / 2 by ring]
  exact (realGinibreExpectedCountClosedForm_shift_two m hm).symm

end
end NumStability
