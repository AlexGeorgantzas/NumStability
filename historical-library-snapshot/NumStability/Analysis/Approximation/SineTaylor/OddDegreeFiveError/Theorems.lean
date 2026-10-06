-- NumStability/Analysis/Approximation/SineTaylor/OddDegreeFiveError/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Split component of a mixed/multi-destination owner.
-- Historical owner: `NumStability.Analysis.AccuracyTests`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.Rounding
import NumStability.Source.Higham.Chapter02.Section11.AccuracyTests.Basic

/-!
# Theorems

Relocated from `NumStability.Analysis.AccuracyTests` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# AccuracyTests (compatibility module)

Historical path, retained so existing imports of `NumStability.Analysis.AccuracyTests`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

noncomputable section

namespace NumStability

private theorem summable_sine_odd_terms (x : ℝ) :
    Summable
      (fun n : ℕ => x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) := by
  simpa only [Function.comp_apply] using
    (Real.summable_pow_div_factorial x).comp_injective
      (by
        intro a b h
        have hsucc : Nat.succ (2 * a) = Nat.succ (2 * b) := by
          simpa [Nat.succ_eq_add_one] using h
        have hmul : 2 * a = 2 * b := Nat.succ.inj hsucc
        exact Nat.mul_left_cancel (by norm_num : 0 < 2) hmul)


private theorem sine_odd_terms_antitone {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone
      (fun n : ℕ => x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)) := by
  refine antitone_nat_of_succ_le ?_
  intro n
  have hx2 : x ^ 2 ≤ 1 := by
    have hmul := mul_le_mul hx1 hx1 hx0 zero_le_one
    nlinarith [hmul]
  have hpow : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) := by
    have hnon : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
    calc
      x ^ (2 * (n + 1) + 1) = x ^ (2 * n + 1) * x ^ 2 := by
        have hn : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
        rw [hn, pow_add]
      _ ≤ x ^ (2 * n + 1) * 1 := mul_le_mul_of_nonneg_left hx2 hnon
      _ = x ^ (2 * n + 1) := by ring
  have hden_nonneg : 0 ≤ (Nat.factorial (2 * (n + 1) + 1) : ℝ) := by positivity
  have hden_pos : 0 < (Nat.factorial (2 * n + 1) : ℝ) := by positivity
  have hden_le :
      (Nat.factorial (2 * n + 1) : ℝ) ≤
        (Nat.factorial (2 * (n + 1) + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : 2 * n + 1 ≤ 2 * (n + 1) + 1)
  have hnum_nonneg : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
  exact (div_le_div_of_nonneg_right hpow hden_nonneg).trans
    (div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le)


/-- Alternating-series remainder bound for the five-term odd Taylor polynomial
for `sin` on `[0, 1]`. -/
theorem sineTaylorOdd5_abs_error_le_next (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sin x - sineTaylorOdd5 x| ≤ x ^ 11 / (Nat.factorial 11 : ℝ) := by
  let f : ℕ → ℝ :=
    fun n => x ^ (2 * n + 1) / (Nat.factorial (2 * n + 1) : ℝ)
  have hsummable : Summable f := by
    simpa [f] using summable_sine_odd_terms x
  have hant : Antitone f := by
    simpa [f] using sine_odd_terms_antitone (x := x) hx0 hx1
  have h := alternating_series_error_bound f hant hsummable 5
  have htsum : (∑' i : ℕ, (-1 : ℝ) ^ i * f i) = Real.sin x := by
    simpa [f, div_eq_mul_inv, mul_assoc] using (Real.hasSum_sin x).tsum_eq
  rw [htsum] at h
  have hpartial : (∑ i ∈ Finset.range 5, (-1 : ℝ) ^ i * f i) =
      sineTaylorOdd5 x := by
    simp [f, sineTaylorOdd5]
  have hnext : f 5 = x ^ 11 / (Nat.factorial 11 : ℝ) := by
    norm_num [f]
  simpa [hpartial, hnext] using h

end NumStability
