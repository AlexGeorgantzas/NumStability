/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter24.InverseFFT

namespace NumStability

open scoped Matrix.Norms.L2Operator

/-!
# Quantitative backward stability after Theorem 24.2

The book's immediate consequence of Theorem 24.2 is now proved with the exact
Euclidean scaling of the forward and inverse DFT.  In particular, the explicit
inverse-transformed output error from `Higham24.lean` has the same relative
norm as the forward output error.
-/

/-- The inverse length-`2^t` DFT has spectral norm `1 / sqrt(2^t)`. -/
theorem higham24_dftInverse_l2_opNorm (t : ℕ) :
    ‖higham24DFTInverse (2 ^ t)‖ =
      (Real.sqrt (((2 ^ t : ℕ) : ℝ)))⁻¹ := by
  rw [higham24_dftInverse_eq_scaled_entrywiseConjugate,
    norm_smul, higham24_entrywiseConjugateMatrix_norm,
    higham24_dft_l2_opNorm]
  have hscalar :
      ‖((((2 ^ t : ℕ) : ℂ))⁻¹)‖ = (((2 ^ t : ℕ) : ℝ))⁻¹ := by
    simp [norm_inv]
  rw [hscalar]
  have hspos : 0 < Real.sqrt (((2 ^ t : ℕ) : ℝ)) := by positivity
  have hsquare : (Real.sqrt (((2 ^ t : ℕ) : ℝ))) ^ 2 =
      (((2 ^ t : ℕ) : ℝ)) := by
    rw [Real.sq_sqrt]
    positivity
  field_simp [hspos.ne']
  nlinarith

/-- The unnormalized forward DFT scales every Euclidean vector norm exactly
by `sqrt(2^t)`. -/
theorem higham24_dftApply_finEuclideanNorm_eq
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) :
    higham24FinEuclideanNorm (higham24DFTApply x) =
      Real.sqrt (((2 ^ t : ℕ) : ℝ)) * higham24FinEuclideanNorm x := by
  let s := Real.sqrt (((2 ^ t : ℕ) : ℝ))
  have hspos : 0 < s := by dsimp [s]; positivity
  apply le_antisymm
  · exact higham24_dftApply_finEuclideanNorm_le t x
  · have hInv := Matrix.l2_opNorm_mulVec (higham24DFTInverse (2 ^ t))
      (WithLp.toLp (2 : ENNReal) (higham24DFTApply x) :
        EuclideanSpace ℂ (Fin (2 ^ t)))
    have hround :
        (higham24DFTInverse (2 ^ t)).mulVec (higham24DFTApply x) = x := by
      exact higham24_inverse_after_forward x
    have hle : higham24FinEuclideanNorm x ≤
        s⁻¹ * higham24FinEuclideanNorm (higham24DFTApply x) := by
      rw [higham24_dftInverse_l2_opNorm] at hInv
      simpa [higham24FinEuclideanNorm, hround, s] using hInv
    calc
      s * higham24FinEuclideanNorm x ≤
          s * (s⁻¹ * higham24FinEuclideanNorm (higham24DFTApply x)) :=
        mul_le_mul_of_nonneg_left hle hspos.le
      _ = higham24FinEuclideanNorm (higham24DFTApply x) := by
        field_simp [hspos.ne']

/-- The scaled inverse DFT correspondingly divides every Euclidean norm by
`sqrt(2^t)`. -/
theorem higham24_dftInverseApply_finEuclideanNorm_eq
    (t : ℕ) (y : Fin (2 ^ t) → ℂ) :
    higham24FinEuclideanNorm (higham24DFTInverseApply y) =
      (Real.sqrt (((2 ^ t : ℕ) : ℝ)))⁻¹ * higham24FinEuclideanNorm y := by
  let s := Real.sqrt (((2 ^ t : ℕ) : ℝ))
  have hspos : 0 < s := by dsimp [s]; positivity
  have hforward := higham24_dftApply_finEuclideanNorm_eq t
    (higham24DFTInverseApply y)
  rw [higham24_forward_after_inverse] at hforward
  rw [inv_mul_eq_div]
  apply (eq_div_iff hspos.ne').2
  simpa [s, mul_comm] using hforward.symm

/-- The explicit backward perturbation following Theorem 24.2 has exactly the
same relative Euclidean norm as the output error, including the zero-input
case under Lean's total division. -/
theorem higham24_dft_backwardPerturbation_relative_norm
    (t : ℕ) (x yHat : Fin (2 ^ t) → ℂ) :
    higham24FinEuclideanNorm
        (higham24DFTBackwardPerturbation x yHat) /
        higham24FinEuclideanNorm x =
      higham24FinEuclideanNorm (yHat - higham24DFTApply x) /
        higham24FinEuclideanNorm (higham24DFTApply x) := by
  rw [higham24_dftApply_finEuclideanNorm_eq]
  unfold higham24DFTBackwardPerturbation
  change higham24FinEuclideanNorm
      (higham24DFTInverseApply (yHat - higham24DFTApply x)) /
        higham24FinEuclideanNorm x = _
  rw [higham24_dftInverseApply_finEuclideanNorm_eq]
  have hspos : 0 < Real.sqrt (((2 ^ t : ℕ) : ℝ)) := by positivity
  field_simp [hspos.ne']

/-- The literal Cooley--Tukey computation is normwise backward stable with
the same printed coefficient as Theorem 24.2. -/
theorem higham24_literalFFT_backward_stable
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ)
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1) :
    higham24FinEuclideanNorm
        (higham24DFTBackwardPerturbation x
          (higham24RoundedRadix2FFTFin fp weight t x)) /
      higham24FinEuclideanNorm x ≤
        higham24RelativeFFTBound t (higham24Eta mu (gamma fp 4)) := by
  let rho := higham24RelativeFFTBound t (higham24Eta mu (gamma fp 4))
  have heta : 0 ≤ higham24Eta mu (gamma fp 4) := by
    unfold higham24Eta
    exact add_nonneg hmu
      (mul_nonneg (gamma_nonneg fp hgamma4)
        (add_nonneg (Real.sqrt_nonneg _) hmu))
  have hrho : 0 ≤ rho :=
    higham24_relativeFFTBound_nonneg t
      (higham24Eta mu (gamma fp 4)) heta hvalid
  by_cases hx : x = 0
  · subst x
    have herror := higham24_forwardFFTError_eq_zero_of_input_eq_zero
      fp hgamma4 weight mu hmu hw t (0 : Fin (2 ^ t) → ℂ) rfl
    have hyhat :
        higham24RoundedRadix2FFTFin fp weight t
          (0 : Fin (2 ^ t) → ℂ) = 0 := by
      simpa [higham24ForwardFFTError, higham24DFTApply] using herror
    rw [hyhat]
    simpa [higham24DFTBackwardPerturbation,
      higham24FinEuclideanNorm, rho] using hrho
  · have hxnorm : 0 < higham24FinEuclideanNorm x := by
      apply lt_of_le_of_ne (norm_nonneg _)
      intro hzero
      apply hx
      have hxE : (WithLp.toLp (2 : ENNReal) x :
          EuclideanSpace ℂ (Fin (2 ^ t))) = 0 := norm_eq_zero.mp hzero.symm
      have := congrArg WithLp.ofLp hxE
      simpa using this
    rw [higham24_dft_backwardPerturbation_relative_norm]
    apply (div_le_iff₀
      (by rw [higham24_dftApply_finEuclideanNorm_eq]; positivity)).2
    simpa [higham24ForwardFFTError, rho] using
      higham24_forwardFFTError_norm_le_relative
        fp hgamma4 weight mu hmu hw t x hvalid

end NumStability
