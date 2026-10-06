/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.HighamChapter9
import NumStability.Analysis.Rounding

namespace NumStability

open scoped BigOperators
open ComplexConjugate

/-! # Higham Chapter 24: exact DFT and FFT error coefficients

The exact DFT foundations are shared with Chapter 9.  This module exposes
Chapter-24-facing names, proves the forward/inverse round trip, and formalizes
the scalar accumulation step used in equation (24.5).  The implementation-level
Cooley--Tukey factorization and rounded FFT execution are recorded as open
dependencies in the chapter report.
-/

/-- The DFT matrix `F_n` from section 24.1, with zero-based `Fin` indices. -/
noncomputable def higham24DFT (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (higham9_13_fourierVandermonde n)

/-- The displayed inverse transform `F_n⁻¹ = n⁻¹ F_nᴴ`. -/
noncomputable def higham24DFTInverse (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of (higham9_13_fourierVandermondeScaledAdjoint n)

/-- Source-facing action of the DFT matrix. -/
noncomputable def higham24DFTApply {n : ℕ} (x : Fin n → ℂ) : Fin n → ℂ :=
  (higham24DFT n).mulVec x

/-- Source-facing action of the inverse DFT matrix. -/
noncomputable def higham24DFTInverseApply {n : ℕ} (y : Fin n → ℂ) : Fin n → ℂ :=
  (higham24DFTInverse n).mulVec y

/-- The Chapter 9 roots-of-unity proof supplies the exact left-inverse identity
needed in Chapter 24. -/
theorem higham24_dftInverse_mul_dft (n : ℕ) :
    higham24DFTInverse n * higham24DFT n = 1 := by
  ext s t
  simpa [higham24DFTInverse, higham24DFT, Matrix.mul_apply, Matrix.one_apply]
    using higham9_13_scaledAdjoint_mul_fourierVandermonde (n := n) s t

/-- The scaled adjoint is also a right inverse. -/
theorem higham24_dft_mul_dftInverse (n : ℕ) :
    higham24DFT n * higham24DFTInverse n = 1 := by
  ext r q
  simpa [higham24DFTInverse, higham24DFT, Matrix.mul_apply, Matrix.one_apply]
    using higham9_13_fourierVandermonde_mul_scaledAdjoint (n := n) r q

/-- Exact inverse-after-forward DFT round trip. -/
theorem higham24_inverse_after_forward {n : ℕ} (x : Fin n → ℂ) :
    higham24DFTInverseApply (higham24DFTApply x) = x := by
  rw [higham24DFTInverseApply, higham24DFTApply, Matrix.mulVec_mulVec,
    higham24_dftInverse_mul_dft, Matrix.one_mulVec]

/-- Exact forward-after-inverse DFT round trip. -/
theorem higham24_forward_after_inverse {n : ℕ} (y : Fin n → ℂ) :
    higham24DFTApply (higham24DFTInverseApply y) = y := by
  rw [higham24DFTInverseApply, higham24DFTApply, Matrix.mulVec_mulVec,
    higham24_dft_mul_dftInverse, Matrix.one_mulVec]

/-- The exact backward-error representation behind the prose consequence of
Theorem 24.2.  Any computed transform is the exact DFT of the input plus the
explicit inverse-transformed output error. -/
noncomputable def higham24DFTBackwardPerturbation {n : ℕ}
    (x yHat : Fin n → ℂ) : Fin n → ℂ :=
  (higham24DFTInverse n).mulVec
    (yHat - (higham24DFT n).mulVec x)

theorem higham24_dft_backward_error_representation {n : ℕ}
    (x yHat : Fin n → ℂ) :
    (higham24DFT n).mulVec
        (x + higham24DFTBackwardPerturbation x yHat) = yHat := by
  unfold higham24DFTBackwardPerturbation
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec,
    higham24_dft_mul_dftInverse, Matrix.one_mulVec]
  simp

/-- Equation (24.2): an explicitly represented computed FFT weight with its
absolute-error certificate. -/
structure Higham24WeightApproximation (exact computed : ℂ) (mu : ℝ) where
  error : ℂ
  representation : computed = exact + error
  bound : ‖error‖ ≤ mu

/-- Equation (24.2) in subtraction form. -/
theorem higham24_eq24_2_error_bound
    {exact computed : ℂ} {mu : ℝ}
    (h : Higham24WeightApproximation exact computed mu) :
    ‖computed - exact‖ ≤ mu := by
  rw [h.representation]
  simpa using h.bound

/-- The local relative perturbation coefficient `η` in Theorem 24.2. -/
noncomputable def higham24Eta (mu gamma4 : ℝ) : ℝ :=
  mu + gamma4 * (Real.sqrt 2 + mu)

/-- The relative bound `tη/(1-tη)` displayed in Theorem 24.2. -/
noncomputable def higham24RelativeFFTBound (t : ℕ) (eta : ℝ) : ℝ :=
  (t : ℝ) * eta / (1 - (t : ℝ) * eta)

/-- The scalar product-perturbation step used in (24.5).  This is a direct
reuse of Higham's proved product lemma from Chapter 3. -/
theorem higham24_eq24_5_product_bound
    (t : ℕ) (eta : ℝ) (heta : 0 ≤ eta)
    (hvalid : (t : ℝ) * eta < 1) :
    (1 + eta) ^ t - 1 ≤ higham24RelativeFFTBound t eta := by
  let fp := FPModel.exactWithUnitRoundoff eta heta
  have hgammaValid : gammaValid fp t := by
    simpa [gammaValid, fp, FPModel.exactWithUnitRoundoff] using hvalid
  have hdelta : ∀ _i : Fin t, |eta| ≤ fp.u := by
    intro _i
    simp [fp, FPModel.exactWithUnitRoundoff, abs_of_nonneg heta]
  obtain ⟨theta, htheta, hproduct⟩ :=
    prod_error_bound fp t (fun _i => eta) hdelta hgammaValid
  have hpower : (1 + eta) ^ t = 1 + theta := by
    simpa using hproduct
  calc
    (1 + eta) ^ t - 1 = theta := by linarith
    _ ≤ |theta| := le_abs_self theta
    _ ≤ gamma fp t := htheta
    _ = higham24RelativeFFTBound t eta := by
      simp [gamma, higham24RelativeFFTBound, fp, FPModel.exactWithUnitRoundoff]

/-- Equation (24.6), the absolute DFT perturbation envelope `f(n,u)`, with the
dependence on `u` carried through `eta`. -/
noncomputable def higham24Eq24_6Bound (n t : ℕ) (eta : ℝ) : ℝ :=
  Real.sqrt n * higham24RelativeFFTBound t eta

theorem higham24_relativeFFTBound_nonneg
    (t : ℕ) (eta : ℝ) (heta : 0 ≤ eta)
    (hvalid : (t : ℝ) * eta < 1) :
    0 ≤ higham24RelativeFFTBound t eta := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg t) heta) (by linarith)

theorem higham24_eq24_6_bound_nonneg
    (n t : ℕ) (eta : ℝ) (heta : 0 ≤ eta)
    (hvalid : (t : ℝ) * eta < 1) :
    0 ≤ higham24Eq24_6Bound n t eta := by
  exact mul_nonneg (Real.sqrt_nonneg _) (higham24_relativeFFTBound_nonneg t eta heta hvalid)

end NumStability
