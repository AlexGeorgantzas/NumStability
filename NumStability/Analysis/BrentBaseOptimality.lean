-- Analysis/BrentBaseOptimality.lean
--
-- Higham Chapter 2, Section 2.7: the base-optimality comparison attributed
-- to Brent (1973).

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace NumStability

noncomputable section

/-!
# Brent's base-optimality formula comparison

Higham states that, for the logarithmic distribution, worst-case and mean
square representation errors are minimized by normalized base two when its
leading bit is implicit.  The cited paper compares bases `beta = 2^k` at fixed
word length and range.  Its equations (4.7) and (5.8) reduce the comparison to
the two formulas below, where `p = 2` records the saved leading bit and `p = 1`
records an explicitly stored leading bit.

This file verifies the exact algebraic comparison of those formulas.  It does
not silently claim a derivation of Brent's probabilistic error formulas from a
finite floating-point implementation: the paper explicitly makes its fixed
word-length/range model assumptions and neglects higher-order terms in the RMS
derivation.  Keeping that boundary visible is essential to the source audit.
-/

/-- Brent (1973), equation (4.7): worst-case error divided by the logarithmic
system's optimum, for base `2^k` and leading-bit parameter `p`. -/
def brentWorstCaseRatioFormula (k p : ℕ) : ℝ :=
  (2 : ℝ) ^ k / ((k : ℝ) * (p : ℝ) * Real.log 2)

/-- The square of Brent (1973), equation (5.8): RMS error divided by the
logarithmic system's RMS error.  Squaring removes the outer square root while
preserving comparisons because both quantities are nonnegative. -/
def brentRmsRatioSquaredFormula (k p : ℕ) : ℝ :=
  ((4 : ℝ) ^ k - 1) /
    ((2 : ℝ) ^ (2 * p - 1) * (((k : ℝ) * Real.log 2) ^ 3))

/-- The elementary exponential domination used in the worst-case comparison. -/
theorem brent_natCast_le_two_pow (k : ℕ) :
    (k : ℝ) ≤ (2 : ℝ) ^ k := by
  exact_mod_cast (Nat.lt_two_pow_self : k < 2 ^ k).le

/-- A shifted form of the cubic-versus-exponential inequality needed for the
RMS comparison. -/
private theorem brent_three_mul_succ_cube_add_four_le_four_pow (n : ℕ) :
    3 * (((n + 1 : ℕ) : ℝ) ^ 3) + 4 ≤ (4 : ℝ) ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      let x : ℝ := n + 1
      have hx : 0 ≤ x + 1 := by
        dsimp [x]
        positivity
      have hfactor : 0 ≤ (x - 1) ^ 2 * (x + 1) :=
        mul_nonneg (sq_nonneg (x - 1)) hx
      have hpoly :
          3 * (x + 1) ^ 3 + 4 ≤ 4 * (3 * x ^ 3 + 4) := by
        nlinarith [hfactor]
      have hscaled :
          4 * (3 * x ^ 3 + 4) ≤ 4 * (4 : ℝ) ^ (n + 2) := by
        apply mul_le_mul_of_nonneg_left
        · simpa [x, Nat.cast_add, Nat.cast_one] using ih
        · norm_num
      calc
        3 * ((((n + 1).succ : ℕ) : ℝ) ^ 3) + 4
            = 3 * (x + 1) ^ 3 + 4 := by
                simp [x, Nat.cast_add, Nat.cast_one]
        _ ≤ 4 * (3 * x ^ 3 + 4) := hpoly
        _ ≤ 4 * (4 : ℝ) ^ (n + 2) := hscaled
        _ = (4 : ℝ) ^ (n + 1 + 2) := by
              rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
              ring

/-- The exact numerator inequality behind the RMS base comparison. -/
theorem brent_three_cube_le_four_mul_four_pow_sub_one (k : ℕ)
    (hk : 1 ≤ k) :
    3 * (k : ℝ) ^ 3 ≤ 4 * ((4 : ℝ) ^ k - 1) := by
  cases k with
  | zero => simp at hk
  | succ n =>
      have h := brent_three_mul_succ_cube_add_four_le_four_pow n
      have hpow :
          (4 : ℝ) ^ (n + 2) = 4 * (4 : ℝ) ^ (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        ring
      rw [hpow] at h
      norm_num only [Nat.cast_add, Nat.cast_one] at h ⊢
      nlinarith

/-- Formula-level closure of Higham Chapter 2's attributed worst-case claim:
implicit-leading-bit binary (`k = 1`, `p = 2`) is no worse than any explicit
base `2^k` (`p = 1`). -/
theorem brentWorstCaseRatioFormula_hiddenBinary_le_explicit (k : ℕ)
    (hk : 1 ≤ k) :
    brentWorstCaseRatioFormula 1 2 ≤
      brentWorstCaseRatioFormula k 1 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hkposNat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkposNat
  have hpow : (k : ℝ) ≤ (2 : ℝ) ^ k := brent_natCast_le_two_pow k
  unfold brentWorstCaseRatioFormula
  norm_num only [pow_one, Nat.cast_one, one_mul, mul_one]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.log 2)
      (by positivity : 0 < (k : ℝ) * Real.log 2)).2
  have hscaled := mul_le_mul_of_nonneg_right hpow hlog.le
  nlinarith

/-- Formula-level closure of Higham Chapter 2's attributed mean-square claim,
stated before the monotone square root: implicit-leading-bit binary minimizes
Brent's squared RMS ratio among the explicit bases `2^k`. -/
theorem brentRmsRatioSquaredFormula_hiddenBinary_le_explicit (k : ℕ)
    (hk : 1 ≤ k) :
    brentRmsRatioSquaredFormula 1 2 ≤
      brentRmsRatioSquaredFormula k 1 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hkposNat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkposNat
  have hcore := brent_three_cube_le_four_mul_four_pow_sub_one k hk
  unfold brentRmsRatioSquaredFormula
  norm_num only [pow_one, Nat.cast_one, one_mul, mul_one]
  rw [mul_pow]
  apply (div_le_div_iff₀
    (by positivity : 0 < (8 : ℝ) * (Real.log 2) ^ 3)
    (by positivity : 0 < (2 : ℝ) * ((k : ℝ) ^ 3 * (Real.log 2) ^ 3))).2
  have hscale : 0 ≤ 2 * (Real.log 2) ^ 3 := by positivity
  calc
    3 * (2 * ((k : ℝ) ^ 3 * (Real.log 2) ^ 3)) =
        (3 * (k : ℝ) ^ 3) * (2 * (Real.log 2) ^ 3) := by ring
    _ ≤ (4 * ((4 : ℝ) ^ k - 1)) * (2 * (Real.log 2) ^ 3) :=
      mul_le_mul_of_nonneg_right hcore hscale
    _ = ((4 : ℝ) ^ k - 1) * (8 * (Real.log 2) ^ 3) := by ring

/-- The RMS (rather than squared-RMS) version of the Brent comparison. -/
theorem brentRmsRatioFormula_hiddenBinary_le_explicit (k : ℕ)
    (hk : 1 ≤ k) :
    Real.sqrt (brentRmsRatioSquaredFormula 1 2) ≤
      Real.sqrt (brentRmsRatioSquaredFormula k 1) := by
  exact Real.sqrt_le_sqrt
    (brentRmsRatioSquaredFormula_hiddenBinary_le_explicit k hk)

end

end NumStability
