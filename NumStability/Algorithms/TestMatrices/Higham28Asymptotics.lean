/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Exact
import Mathlib.Analysis.SpecialFunctions.Stirling

/-! # Higham Chapter 28: precise asymptotic statement surfaces

This module separates exact filter-based targets from the chapter's rounded
or leading-order shorthand.  It deliberately supplies no theorem asserting a
citation-dependent limit that has not been derived locally.
-/

namespace NumStability

open Filter Asymptotics

/-- Spectral two-norm condition number using the proved explicit Hilbert
inverse (28.1). -/
noncomputable def hilbertConditionTwo (n : ℕ) : ℝ :=
  opNorm2 (hilbertMatrix n) * opNorm2 (hilbertInverseFormula n)

/-- The shifted Hilbert family `1/(i+j+2)` from p. 514. -/
noncomputable def shiftedHilbertMatrix (n : ℕ) : RSqMat n :=
  fun i j => 1 / (i.val + j.val + 2 : ℕ)

/-- Two-norm condition number of the symmetric Pascal matrix, using its proved
`SᵀS` inverse. -/
noncomputable def pascalConditionTwo (n : ℕ) : ℝ :=
  opNorm2 (pascalMatrix n) *
    opNorm2 ((signedPascal n).transpose * signedPascal n)

/-- Two-norm condition number of the second-difference Toeplitz matrix, using
the proved Green-function inverse. -/
noncomputable def secondDifferenceConditionTwo (n : ℕ) : ℝ :=
  opNorm2 (tridiagonalToeplitz n (-1) 2 (-1)) *
    opNorm2 (secondDifferenceInverse n)

/-- A literal ratio-equivalence reading of the determinant display after
(28.2).  This proposition is retained only to record that strong reading; no
theorem asserts it, and the printed display is more faithfully understood as
a leading-exponential statement. -/
def HilbertDetAsymptotic : Prop :=
  IsEquivalent atTop
    (fun n : ℕ => Matrix.det (hilbertMatrix n))
    (fun n : ℕ => (2 : ℝ) ^ (-2 * (n : ℝ) ^ 2))

/-- A log-scale formulation of the leading exponential content in
`det(Hₙ) ~ 2^{-2n²}`. -/
def HilbertDetLeadingLogRate : Prop :=
  Tendsto
    (fun n : ℕ => Real.log (Matrix.det (hilbertMatrix n)) / (n : ℝ) ^ 2)
    atTop (nhds (-2 * Real.log 2))

/-- Literal ratio-equivalence reading of `κ₂(Hₙ) ~ exp(3.5n)`.  The printed
`3.5` is rounded, so this is a recorded surface rather than a claimed precise
asymptotic theorem. -/
def HilbertConditionAsymptotic : Prop :=
  IsEquivalent atTop
    hilbertConditionTwo
    (fun n : ℕ => Real.exp (3.5 * n))

/-- Precise Big-O reading of `‖H̃ₙ‖₂ = π + O(1/log n)`. -/
def ShiftedHilbertNormAsymptotic : Prop :=
  (fun n : ℕ => opNorm2 (shiftedHilbertMatrix n) - Real.pi) =O[atTop]
    (fun n : ℕ => 1 / Real.log n)

/-- Literal ratio-equivalence reading of the full Pascal condition estimate
on p. 520.  This is retained as a source-audit surface, not as a valid target:
the bound `p_nn ≤ ‖P‖₂ ≤ 2 p_nn` printed on the same page gives a constant
factor incompatible with ratio-to-one equivalence to the displayed central
binomial model.  The faithful remaining target is a constant-factor or
logarithmic-rate statement. -/
def PascalConditionAsymptotic : Prop :=
  IsEquivalent atTop
    pascalConditionTwo
    (fun n : ℕ => (16 : ℝ) ^ n / (n * Real.pi))

/-- The elementary factor in Stirling's formula, named here to keep the
Pascal condition-number calculation readable. -/
noncomputable def pascalStirlingFactorialModel (n : ℕ) : ℝ :=
  Real.sqrt (2 * n * Real.pi) * (n / Real.exp 1) ^ n

/-- Exact simplification of the quotient of the Stirling models occurring in
the central binomial coefficient. -/
theorem pascalStirling_two_mul_div_sq (n : ℕ) (hn : 0 < n) :
    pascalStirlingFactorialModel (2 * n) /
        pascalStirlingFactorialModel n ^ 2 =
      (4 : ℝ) ^ n / Real.sqrt (Real.pi * n) := by
  unfold pascalStirlingFactorialModel
  norm_num [Nat.cast_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ha : (n : ℝ) / Real.exp 1 ≠ 0 :=
    div_ne_zero hnR (Real.exp_ne_zero 1)
  have hsqrt2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [Real.mul_self_sqrt] <;> norm_num
  have hsqrtn : Real.sqrt (n : ℝ) * Real.sqrt n = n := by
    rw [Real.mul_self_sqrt] <;> positivity
  have hsqrtpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
    rw [Real.mul_self_sqrt] <;> positivity
  have hpow :
      (2 * (n : ℝ) / Real.exp 1) ^ (2 * n) =
        (4 : ℝ) ^ n * ((n : ℝ) / Real.exp 1) ^ (2 * n) := by
    rw [show 2 * (n : ℝ) / Real.exp 1 =
      2 * ((n : ℝ) / Real.exp 1) by ring]
    calc
      (2 * ((n : ℝ) / Real.exp 1)) ^ (2 * n) =
          ((2 * ((n : ℝ) / Real.exp 1)) ^ 2) ^ n := by rw [pow_mul]
      _ = (4 * (((n : ℝ) / Real.exp 1) ^ 2)) ^ n := by
        congr 1
        ring
      _ = (4 : ℝ) ^ n * ((((n : ℝ) / Real.exp 1) ^ 2) ^ n) := by
        rw [mul_pow]
      _ = (4 : ℝ) ^ n * ((n : ℝ) / Real.exp 1) ^ (2 * n) := by
        rw [pow_mul]
  rw [hpow]
  field_simp [ha, hsqrt2, hsqrtn, hsqrtpi]
  ring

/-- The central binomial coefficient's direct Stirling asymptotic. -/
theorem pascalCentralBinomial_isEquivalent :
    IsEquivalent atTop
      (fun n : ℕ => (Nat.centralBinom n : ℝ))
      (fun n : ℕ => (4 : ℝ) ^ n / Real.sqrt (Real.pi * n)) := by
  have hfac :
      IsEquivalent atTop
        (fun n : ℕ => (n.factorial : ℝ))
        pascalStirlingFactorialModel := by
    exact Stirling.factorial_isEquivalent_stirling
  have hfac2 :
      IsEquivalent atTop
        (fun n : ℕ => ((2 * n).factorial : ℝ))
        (fun n : ℕ => pascalStirlingFactorialModel (2 * n)) := by
    simpa [Function.comp_def] using
      hfac.comp_tendsto
        (tendsto_id.const_mul_atTop' (by positivity : 0 < (2 : ℕ)))
  have hratio :
      IsEquivalent atTop
        (fun n : ℕ => ((2 * n).factorial : ℝ) / (n.factorial : ℝ) ^ 2)
        (fun n : ℕ => pascalStirlingFactorialModel (2 * n) /
          pascalStirlingFactorialModel n ^ 2) :=
    hfac2.div (hfac.pow 2)
  have hchoose :
      IsEquivalent atTop
        (fun n : ℕ => (Nat.centralBinom n : ℝ))
        (fun n : ℕ => pascalStirlingFactorialModel (2 * n) /
          pascalStirlingFactorialModel n ^ 2) := by
    apply hratio.congr_left
    filter_upwards with n
    rw [Nat.centralBinom_eq_two_mul_choose]
    simpa [two_mul, pow_two] using
      (Nat.cast_add_choose ℝ (a := n) (b := n)).symm
  apply hchoose.congr_right
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  exact pascalStirling_two_mul_div_sq n (show 0 < n from hn)

/-- Higham, 2nd ed., Section 28.4, p. 520: the second, purely Stirling,
endpoint in
`((2n)!/(n!)²)² ∼ 16ⁿ/(nπ)`.

This is a genuine unconditional filter theorem.  It verifies only the
central-binomial Stirling endpoint; it does not validate a strict
ratio-equivalence interpretation of the preceding condition-number display,
which is incompatible with the norm bound printed on the same page. -/
theorem pascalCentralBinomial_sq_isEquivalent :
    IsEquivalent atTop
      (fun n : ℕ => (Nat.centralBinom n : ℝ) ^ 2)
      (fun n : ℕ => (16 : ℝ) ^ n / (n * Real.pi)) := by
  have hsquare :
      IsEquivalent atTop
        (fun n : ℕ => (Nat.centralBinom n : ℝ) ^ 2)
        (fun n : ℕ =>
          ((4 : ℝ) ^ n / Real.sqrt (Real.pi * n)) ^ 2) := by
    simpa [Pi.pow_apply] using pascalCentralBinomial_isEquivalent.pow 2
  apply hsquare.congr_right
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show 0 < n from hn).ne'
  have hsqrt : Real.sqrt (Real.pi * n) ^ 2 = Real.pi * n := by
    rw [Real.sq_sqrt] <;> positivity
  rw [div_pow, hsqrt]
  field_simp [hnR, Real.pi_ne_zero]
  rw [← pow_mul, mul_comm n 2, pow_mul]
  norm_num

/-- The reciprocal central-binomial endpoint used for the order estimate of
the smallest Pascal singularizing perturbation on p. 520. -/
theorem pascalInverseCentralBinomial_isEquivalent :
    IsEquivalent atTop
      (fun n : ℕ => (Nat.centralBinom n : ℝ)⁻¹)
      (fun n : ℕ => Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n) := by
  apply pascalCentralBinomial_isEquivalent.inv.congr_right
  filter_upwards with n
  simp [inv_div]

/-- The factorial ratio printed on p. 520 is exactly the reciprocal central
binomial coefficient. -/
theorem pascalFactorialRatio_eq_invCentralBinomial (n : ℕ) :
    (n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ) =
      (Nat.centralBinom n : ℝ)⁻¹ := by
  have hchoose :
      ((2 * n).factorial : ℝ) / (n.factorial : ℝ) ^ 2 =
        (Nat.centralBinom n : ℝ) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    simpa [two_mul, pow_two] using
      (Nat.cast_add_choose ℝ (a := n) (b := n)).symm
  rw [← hchoose]
  have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2fac : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Higham, p. 520: the unconditional Stirling endpoint
`(n!)²/(2n)! ∼ 4⁻ⁿ sqrt(nπ)` used in the optimal-perturbation discussion. -/
theorem pascalFactorialRatio_isEquivalent :
    IsEquivalent atTop
      (fun n : ℕ => (n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ))
      (fun n : ℕ => Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n) := by
  apply pascalInverseCentralBinomial_isEquivalent.congr_left
  filter_upwards with n
  exact (pascalFactorialRatio_eq_invCentralBinomial n).symm

/-- Precise asymptotic-equivalence reading of the p. 522 second-difference
condition estimate. -/
def SecondDifferenceConditionAsymptotic : Prop :=
  IsEquivalent atTop
    secondDifferenceConditionTwo
    (fun n : ℕ => 4 * (n : ℝ) ^ 2 / Real.pi ^ 2)

/-- The exact extremal-eigenvalue quotient suggested by the proved discrete
sine diagonalization.  Identifying `secondDifferenceConditionTwo` with this
closed form still requires the operator-norm/extremal-spectrum bridge. -/
noncomputable def secondDifferenceConditionClosedForm (n : ℕ) : ℝ :=
  let θ := Real.pi / (n + 1 : ℕ)
  (2 + 2 * Real.cos θ) / (2 - 2 * Real.cos θ)

end NumStability
