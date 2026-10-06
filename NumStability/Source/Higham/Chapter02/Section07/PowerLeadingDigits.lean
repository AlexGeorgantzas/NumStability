/-
SPDX-License-Identifier: MIT
-/

import NumStability.Analysis.LeadingDigits.DecimalPowers

noncomputable section

open scoped BigOperators ENNReal NNReal Topology ComplexConjugate
open Filter Set MeasureTheory ProbabilityTheory TopologicalSpace ContinuousMap

namespace NumStability

/-!
# Higham, Chapter 2, Section 2.7: leading digits of powers

This source-facing module states the precise power-sequence result while the
reusable equidistribution and leading-digit machinery lives under `Analysis`.
-/

/-- Higham Chapter 2's precise power-sequence statement: if `q > 0` is not a
rational power of ten, then the asymptotic frequency with which `q^k` has
decimal leading digit `d+1` is `log_10 ((d+2)/(d+1))`.

The count is over the actual leading-digit predicate for the first `N+1`
powers, including `q^0`; it is not an abstract or assumed histogram. -/
theorem higham2_power_decimalLeadingDigit_frequency_tendsto
    {q : ℝ} (hq : 0 < q) (hnot : ¬ IsRationalPowerOfTen q) (d : Fin 9) :
    Tendsto
      (fun N : ℕ ↦
        (({i : Fin (N + 1) |
              problem2_11_decimalLeadingDigit (q ^ i.val) d}.ncard : ℕ) : ℝ≥0∞) /
          ((N + 1 : ℕ) : ℝ≥0∞))
      atTop
      (𝓝 (ENNReal.ofReal (logarithmicLeadingDigitMass 10 (d.val + 1)))) := by
  have hfreq := orbit_halfOpenArc_frequency_tendsto
    (addOrderOf_logb_ten_eq_zero hq hnot)
    (decimalDigitLo d) (decimalDigitHi d)
    (by
      exact div_nonneg (decimalDigit_interval_length_nonneg d) (by norm_num))
    (by
      convert decimalDigit_interval_length_le_one d using 1 <;> ring)
  change Tendsto
      (fun N : ℕ ↦
        (({i : Fin (N + 1) |
              i.val • ((Real.logb 10 q : ℝ) : AddCircle (1 : ℝ)) ∈
                decimalDigitArc d}.ncard : ℕ) : ℝ≥0∞) /
          ((N + 1 : ℕ) : ℝ≥0∞))
      atTop
      (𝓝 (ENNReal.ofReal (decimalDigitHi d - decimalDigitLo d))) at hfreq
  simpa only [orbit_mem_decimalDigitArc_iff hq d,
    decimalDigit_interval_length_eq_mass d] using hfreq

end NumStability
