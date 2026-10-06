import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Asymptotics.Asymptotics
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.Probability

/-!
# Chapter28 Section02 RealGinibre FiniteExpectation Ginibre

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Ginibre` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open Filter Asymptotics Polynomial MeasureTheory

/-- A real characteristic polynomial has at most `n` real roots, counted
with algebraic multiplicity. -/
theorem realEigenvalueCount_le (n : ℕ) (A : RSqMat n) :
    realEigenvalueCount n A ≤ n := by
  unfold realEigenvalueCount
  exact (Polynomial.card_roots' (Matrix.charpoly A)).trans_eq (by simp)

/-- The exact finite-dimensional expression of Edelman--Kostlan--Shub for
the expected number of real roots of an `n x n` real Ginibre matrix.  Its
identification with `expectedRealEigenvalueCount` is intentionally kept as a
separate theorem surface. -/
noncomputable def realGinibreExpectedCountClosedForm (n : ℕ) : ℝ :=
  1 / 2 +
    Real.sqrt (2 / Real.pi) *
      (Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma (n : ℝ)) *
      (₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ))

/-- At positive integers, the Gamma ratio in the real-Ginibre formula is a
central-binomial expression. -/
theorem realGinibre_gammaRatio_eq_centralBinom (n : ℕ) (hn : 0 < n) :
    Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma (n : ℝ) =
      Real.sqrt Real.pi * (n : ℝ) * (Nat.centralBinom n : ℝ) /
        (4 : ℝ) ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hcentral :
      (Nat.centralBinom (k + 1) : ℝ) =
        (((2 * (k + 1)).factorial : ℝ) /
          (((k + 1).factorial : ℝ) ^ 2)) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    simpa [two_mul, pow_two] using
      (Nat.cast_add_choose ℝ (a := k + 1) (b := k + 1))
  have hdoubleNat :
      (2 * (k + 1)).factorial =
        2 ^ (k + 1) * (k + 1).factorial *
          Nat.doubleFactorial (2 * (k + 1) - 1) := by
    have hfac := Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
    have heven := Nat.doubleFactorial_two_mul (k + 1)
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    rw [hfac]
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, heven]
    congr 2
  have hdouble :
      ((2 * (k + 1)).factorial : ℝ) =
        (2 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) *
          (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) := by
    exact_mod_cast hdoubleNat
  rw [Real.Gamma_nat_add_half]
  have hgamma : Real.Gamma ((k + 1 : ℕ) : ℝ) = (k.factorial : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using Real.Gamma_nat_eq_factorial k
  rw [hgamma, hcentral, hdouble]
  have hkfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hskfac : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
  have hpow2 : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have hpow4 : (4 : ℝ) ^ (k + 1) ≠ 0 := by positivity
  have hdf : (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) ≠ 0 := by
    positivity
  rw [show (4 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1)) ^ 2 by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_two]]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- The half-step Gamma ratio occurring in the finite real-Ginibre formula
has its expected square-root asymptotic. -/
theorem realGinibre_gammaRatio_div_sqrt_tendsto_one :
    Tendsto
      (fun n : ℕ =>
        (Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma (n : ℝ)) /
          Real.sqrt n)
      atTop (nhds 1) := by
  have hden : ∀ᶠ n : ℕ in atTop,
      (4 : ℝ) ^ n / Real.sqrt (Real.pi * n) ≠ 0 := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hratio :
      Tendsto
        ((fun n : ℕ => (Nat.centralBinom n : ℝ)) /
          (fun n : ℕ => (4 : ℝ) ^ n / Real.sqrt (Real.pi * n)))
        atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hden).mp
      pascalCentralBinomial_isEquivalent
  apply hratio.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  rw [Pi.div_apply, realGinibre_gammaRatio_eq_centralBinom n hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
  have hpow : (4 : ℝ) ^ n ≠ 0 := by positivity
  rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = n := by
    rw [Real.sq_sqrt (le_of_lt hnR)]
  field_simp
  nlinarith [hsqrt_sq]

/-- The `k`th scalar term in the hypergeometric factor of the real-Ginibre
finite formula. -/
noncomputable def ginibreHypergeometricTerm (n k : ℕ) : ℝ :=
  ((k.factorial : ℝ)⁻¹ * (ascPochhammer ℝ k).eval 1 *
      (ascPochhammer ℝ k).eval (-1 / 2) *
      ((ascPochhammer ℝ k).eval (n : ℝ))⁻¹) *
    (1 / 2 : ℝ) ^ k

/-- Expansion of the real-Ginibre hypergeometric factor into its defining
power series. -/
theorem realGinibre_hypergeometric_eq_tsum (n : ℕ) :
    ₂F₁ (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ) (1 / 2 : ℝ) =
      ∑' k : ℕ, ginibreHypergeometricTerm n k := by
  simpa [ginibreHypergeometricTerm, smul_eq_mul] using
    congrFun
      (ordinaryHypergeometric_eq_tsum
        (1 : ℝ) (-1 / 2 : ℝ) (n : ℝ))
      (1 / 2 : ℝ)

/-- Cancellation of the `(1)_k/k!` factor in each Ginibre term. -/
theorem ginibreHypergeometricTerm_eq (n k : ℕ) :
    ginibreHypergeometricTerm n k =
      (ascPochhammer ℝ k).eval (-1 / 2) *
        ((ascPochhammer ℝ k).eval (n : ℝ))⁻¹ *
        (1 / 2 : ℝ) ^ k := by
  simp [ginibreHypergeometricTerm, ascPochhammer_eval_one,
    Nat.factorial_ne_zero]

@[simp]
theorem ginibreHypergeometricTerm_zero (n : ℕ) :
    ginibreHypergeometricTerm n 0 = 1 := by
  simp [ginibreHypergeometricTerm]

/-- Successive Ginibre hypergeometric terms differ by the elementary ratio
`(k - 1/2)/(n+k) * 1/2`. -/
theorem ginibreHypergeometricTerm_succ (n k : ℕ) :
    ginibreHypergeometricTerm n (k + 1) =
      ginibreHypergeometricTerm n k *
        ((k : ℝ) - 1 / 2) * ((n : ℝ) + k)⁻¹ * (1 / 2) := by
  rw [ginibreHypergeometricTerm_eq, ginibreHypergeometricTerm_eq]
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, pow_succ]
  rw [mul_inv_rev]
  ring

/-- The first nonconstant term is `-1/(4n)`. -/
theorem ginibreHypergeometricTerm_one (n : ℕ) (hn : 0 < n) :
    ginibreHypergeometricTerm n 1 = -(1 / (4 * n : ℝ)) := by
  rw [ginibreHypergeometricTerm_eq]
  simp
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

end NumStability
