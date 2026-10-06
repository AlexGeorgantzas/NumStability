/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28HilbertAsymptotic

/-!
# Higham Chapter 28: the literal Hilbert determinant ratio is false

Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., equation
(28.2), prints the exact Hilbert determinant followed by
`det(H_n) ~ 2^(-2n^2)`.  The exact formula is correct, and
`hilbertDetLeadingLogRate_proved` formalizes its valid leading-log content.
The strict ratio-to-one interpretation recorded by `HilbertDetAsymptotic` is,
however, false.

The normalized ratio

`R_n = det(H_n) * 4^(n^2)`

has successor factor

`4^(2n+1) / ((2n+1) * centralBinom(n)^2)`.

An elementary Wallis-type induction gives
`(2n+1) * centralBinom(n)^2 <= 16^n`; hence every successor factor is at least
`4`, so `R_n >= 4^n` and in fact `R_n -> +infinity`.  This directly refutes
the literal ratio reading without weakening or replacing the already proved
leading-log correction.
-/

namespace NumStability

open Filter Asymptotics
open scoped Topology

noncomputable section

/-- The ratio of the exact Hilbert determinant to the natural-power form of
the leading exponential model in (28.2). -/
noncomputable def higham28NormalizedHilbertDet (n : Nat) : Real :=
  Matrix.det (hilbertMatrix n) * (4 : Real) ^ (n ^ 2)

/-- The exact determinant successor factor, rewritten with the central
binomial coefficient. -/
theorem higham28_hilbert_det_succ_centralBinomial (n : Nat) :
    Matrix.det (hilbertMatrix (n + 1)) =
      Matrix.det (hilbertMatrix n) /
        ((((2 * n + 1 : Nat) : Real) * (Nat.centralBinom n : Real) ^ 2)) := by
  rw [hilbert_det_formula, hilbert_det_formula, hilbertDetFormula_succ,
    hilbertRNat_diag_sq_eq_centralBinomial]
  have hodd : (((2 * n + 1 : Nat) : Real)) ≠ 0 := by positivity
  have hcb : (Nat.centralBinom n : Real) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos n).ne'
  field_simp [hodd, hcb]

/-- Elementary Wallis bound in the exact form needed for the normalized
Hilbert determinant successor ratio. -/
theorem higham28_centralBinomial_sq_mul_odd_le_sixteen_pow (n : Nat) :
    ((2 * n + 1 : Nat) : Real) * (Nat.centralBinom n : Real) ^ 2 ≤
      (16 : Real) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      let s : Real := (n + 1 : Nat)
      let odd : Real := (2 * n + 1 : Nat)
      let odd' : Real := (2 * (n + 1) + 1 : Nat)
      let c : Real := Nat.centralBinom n
      let c' : Real := Nat.centralBinom (n + 1)
      change odd * c ^ 2 ≤ (16 : Real) ^ n at ih
      change odd' * c' ^ 2 ≤ (16 : Real) ^ (n + 1)
      have hrec : s * c' = 2 * odd * c := by
        dsimp [s, odd, c, c']
        exact_mod_cast Nat.succ_mul_centralBinom_succ n
      have hsq : s ^ 2 * c' ^ 2 = (2 * odd * c) ^ 2 := by
        calc
          s ^ 2 * c' ^ 2 = (s * c') ^ 2 := by ring
          _ = (2 * odd * c) ^ 2 := by rw [hrec]
      have hspos : 0 < s := by
        dsimp [s]
        positivity
      have hpoly : 4 * odd' * odd ≤ 16 * s ^ 2 := by
        dsimp [odd', odd, s]
        push_cast
        nlinarith
      apply le_of_mul_le_mul_left ?_ (sq_pos_of_pos hspos)
      calc
        s ^ 2 * (odd' * c' ^ 2) = odd' * (s ^ 2 * c' ^ 2) := by ring
        _ = odd' * (2 * odd * c) ^ 2 := by rw [hsq]
        _ = (4 * odd' * odd) * (odd * c ^ 2) := by ring
        _ ≤ (4 * odd' * odd) * (16 : Real) ^ n :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ (16 * s ^ 2) * (16 : Real) ^ n :=
          mul_le_mul_of_nonneg_right hpoly (by positivity)
        _ = s ^ 2 * (16 : Real) ^ (n + 1) := by
          rw [pow_succ]
          ring

/-- Exact recurrence for the determinant normalized by the literal
`2^(-2n^2)` model. -/
theorem higham28NormalizedHilbertDet_succ (n : Nat) :
    higham28NormalizedHilbertDet (n + 1) =
      higham28NormalizedHilbertDet n *
        ((4 : Real) ^ (2 * n + 1) /
          (((2 * n + 1 : Nat) : Real) * (Nat.centralBinom n : Real) ^ 2)) := by
  rw [higham28NormalizedHilbertDet, higham28NormalizedHilbertDet,
    higham28_hilbert_det_succ_centralBinomial]
  rw [show (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) by ring, pow_add]
  have hodd : (((2 * n + 1 : Nat) : Real)) ≠ 0 := by positivity
  have hcb : (Nat.centralBinom n : Real) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos n).ne'
  field_simp [hodd, hcb]

/-- Every normalized successor factor is at least four. -/
theorem higham28_normalizedHilbert_step_factor_ge_four (n : Nat) :
    (4 : Real) ≤
      (4 : Real) ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real) * (Nat.centralBinom n : Real) ^ 2) := by
  have hdenpos : 0 <
      ((2 * n + 1 : Nat) : Real) * (Nat.centralBinom n : Real) ^ 2 := by
    have hcb : 0 < (Nat.centralBinom n : Real) := by
      exact_mod_cast Nat.centralBinom_pos n
    positivity
  apply (le_div_iff₀ hdenpos).mpr
  calc
    (4 : Real) *
        (((2 * n + 1 : Nat) : Real) * (Nat.centralBinom n : Real) ^ 2) ≤
        4 * (16 : Real) ^ n :=
      mul_le_mul_of_nonneg_left
        (higham28_centralBinomial_sq_mul_odd_le_sixteen_pow n) (by norm_num)
    _ = (4 : Real) ^ (2 * n + 1) := by
      rw [pow_add, pow_mul]
      norm_num
      ring

/-- The normalized determinant is nonnegative. -/
theorem higham28NormalizedHilbertDet_nonneg (n : Nat) :
    0 ≤ higham28NormalizedHilbertDet n := by
  rw [higham28NormalizedHilbertDet, hilbertMatrix_eq_choleskyGram,
    Matrix.det_mul, Matrix.det_transpose]
  exact mul_nonneg (mul_self_nonneg _) (by positivity)

/-- Quantitative refutation: the normalized ratio grows at least as `4^n`. -/
theorem higham28_four_pow_le_normalizedHilbertDet (n : Nat) :
    (4 : Real) ^ n ≤ higham28NormalizedHilbertDet n := by
  induction n with
  | zero =>
      simp [higham28NormalizedHilbertDet]
  | succ n ih =>
      rw [higham28NormalizedHilbertDet_succ, pow_succ]
      calc
        (4 : Real) ^ n * 4 ≤ higham28NormalizedHilbertDet n * 4 :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ higham28NormalizedHilbertDet n *
            ((4 : Real) ^ (2 * n + 1) /
              (((2 * n + 1 : Nat) : Real) *
                (Nat.centralBinom n : Real) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (higham28_normalizedHilbert_step_factor_ge_four n)
            (higham28NormalizedHilbertDet_nonneg n)

/-- The literal determinant ratio diverges to positive infinity. -/
theorem higham28NormalizedHilbertDet_tendsto_atTop :
    Tendsto higham28NormalizedHilbertDet atTop atTop := by
  exact Filter.tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall higham28_four_pow_le_normalizedHilbertDet)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Real) < 4))

/-- The real-power model printed in (28.2) equals the reciprocal natural-power
model used by `higham28NormalizedHilbertDet`. -/
theorem higham28_hilbert_literal_model_eq_inv_four_pow (n : Nat) :
    (2 : Real) ^ (-2 * (n : Real) ^ 2) =
      ((4 : Real) ^ (n ^ 2))⁻¹ := by
  rw [show -2 * (n : Real) ^ 2 = -((2 * n ^ 2 : Nat) : Real) by
    push_cast
    ring]
  rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), Real.rpow_natCast]
  rw [show 2 * n ^ 2 = 2 * (n ^ 2) by rfl, pow_mul]
  norm_num

/-- The quotient occurring in the ratio-equivalence definition is exactly the
normalized determinant. -/
theorem higham28_hilbert_literal_ratio_eq_normalized (n : Nat) :
    Matrix.det (hilbertMatrix n) /
        (2 : Real) ^ (-2 * (n : Real) ^ 2) =
      higham28NormalizedHilbertDet n := by
  rw [higham28_hilbert_literal_model_eq_inv_four_pow]
  simp [higham28NormalizedHilbertDet]

/-- Source correction for Higham (28.2): its literal ratio-to-one reading is
false.  The valid leading-log statement remains
`hilbertDetLeadingLogRate_proved`. -/
theorem higham28_not_HilbertDetAsymptotic : ¬ HilbertDetAsymptotic := by
  intro h
  unfold HilbertDetAsymptotic at h
  have hmodel_ne : ∀ᶠ n : Nat in atTop,
      (2 : Real) ^ (-2 * (n : Real) ^ 2) ≠ 0 := by
    filter_upwards with n
    exact (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 2) _).ne'
  have hratio : Tendsto
      (fun n : Nat => Matrix.det (hilbertMatrix n) /
        (2 : Real) ^ (-2 * (n : Real) ^ 2))
      atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hmodel_ne).mp h
  have hnormalized : Tendsto higham28NormalizedHilbertDet atTop (nhds 1) := by
    apply hratio.congr'
    exact Filter.Eventually.of_forall fun n =>
      higham28_hilbert_literal_ratio_eq_normalized n
  exact (not_tendsto_nhds_of_tendsto_atTop
    higham28NormalizedHilbertDet_tendsto_atTop 1) hnormalized

end

end NumStability
