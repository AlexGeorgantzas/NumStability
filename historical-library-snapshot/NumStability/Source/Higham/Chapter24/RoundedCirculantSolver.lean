/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter24.InverseFFT
import NumStability.Source.Higham.Chapter24.RoundedDiagonalSolve

namespace NumStability

open scoped Matrix.Norms.L2Operator

/-!
# Literal four-stage rounded circulant solver

This module composes the actual producers for all four steps on printed page
455: two literal forward radix-2 FFTs, the literal componentwise rounded
complex division, and the conjugated-forward literal inverse FFT.  The only
extra condition is algorithmic nonbreakdown of the computed diagonal.
-/

/-- The actual four-stage rounded computation.  Complex division is total in
the repository model; the nonzero computed-diagonal condition is needed only
for its source perturbation proof. -/
noncomputable def higham24LiteralRoundedCirculantSolve
    (fp : FPModel) (weight : ∀ s, Higham24BitIndex s → ℂ)
    (t : ℕ) (c b : Fin (2 ^ t) → ℂ) : Fin (2 ^ t) → ℂ :=
  let dHat := higham24RoundedRadix2FFTFin fp weight t c
  let gHat := higham24RoundedRadix2FFTFin fp weight t b
  let hHat := higham24RoundedDiagonalSolve fp dHat gHat
  higham24RoundedInverseRadix2FFTFin fp weight t hHat

/-- The literal executor's computed eigenvalue vector. -/
noncomputable def higham24LiteralRoundedCirculantEigenvalues
    (fp : FPModel) (weight : ∀ s, Higham24BitIndex s → ℂ)
    (t : ℕ) (c : Fin (2 ^ t) → ℂ) : Fin (2 ^ t) → ℂ :=
  higham24RoundedRadix2FFTFin fp weight t c

/-- The literal executor's computed transformed right-hand side. -/
noncomputable def higham24LiteralRoundedCirculantRhs
    (fp : FPModel) (weight : ∀ s, Higham24BitIndex s → ℂ)
    (t : ℕ) (b : Fin (2 ^ t) → ℂ) : Fin (2 ^ t) → ℂ :=
  higham24RoundedRadix2FFTFin fp weight t b

/-- The literal componentwise scaling result used as inverse-FFT input. -/
noncomputable def higham24LiteralRoundedCirculantScaledRhs
    (fp : FPModel) (weight : ∀ s, Higham24BitIndex s → ℂ)
    (t : ℕ) (c b : Fin (2 ^ t) → ℂ) : Fin (2 ^ t) → ℂ :=
  higham24RoundedDiagonalSolve fp
    (higham24LiteralRoundedCirculantEigenvalues fp weight t c)
    (higham24LiteralRoundedCirculantRhs fp weight t b)

private theorem higham24_literalSolver_eta_nonneg
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (mu : ℝ) (hmu : 0 ≤ mu) :
    0 ≤ higham24Eta mu (gamma fp 4) := by
  unfold higham24Eta
  exact add_nonneg hmu
    (mul_nonneg (gamma_nonneg fp hgamma4)
      (add_nonneg (Real.sqrt_nonneg _) hmu))

private theorem higham24_powTwo_inv_le_one (t : ℕ) :
    (((2 ^ t : ℕ) : ℝ)⁻¹) ≤ 1 := by
  have hpos : (0 : ℝ) < ((2 ^ t : ℕ) : ℝ) := by positivity
  apply (inv_le_one₀ hpos).2
  simpa using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) :
    (1 : ℝ) ≤ 2 ^ t)

/-- The sharp inverse-FFT perturbation budget is no larger than the common
forward budget used by the pre-existing four-stage composition record. -/
theorem higham24_literalInversePerturbation_norm_le_forwardBound
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ)
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1) :
    ‖higham24LiteralInversePerturbation fp weight t x‖ ≤
      higham24Eq24_6Bound (2 ^ t) t
        (higham24Eta mu (gamma fp 4)) := by
  let eta := higham24Eta mu (gamma fp 4)
  let bound := higham24Eq24_6Bound (2 ^ t) t eta
  have heta : 0 ≤ eta :=
    higham24_literalSolver_eta_nonneg fp hgamma4 mu hmu
  have hbound : 0 ≤ bound :=
    higham24_eq24_6_bound_nonneg (2 ^ t) t eta heta hvalid
  calc
    ‖higham24LiteralInversePerturbation fp weight t x‖ ≤
        (((2 ^ t : ℕ) : ℝ)⁻¹) * bound := by
      simpa [eta, bound] using
        higham24_literalInversePerturbation_norm_le
          fp hgamma4 weight mu hmu hw t x hvalid
    _ ≤ 1 * bound :=
      mul_le_mul_of_nonneg_right (higham24_powTwo_inv_le_one t) hbound
    _ = bound := one_mul _

/-- Every local equation and norm budget in the four-stage rounded solver is
produced from its literal operations.  The hypothesis `hdHat` is precisely the
computed-diagonal nonbreakdown condition needed by complex division. -/
noncomputable def higham24LiteralRoundedCirculantSolveExecution
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (c b : Fin (2 ^ t) → ℂ)
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1)
    (hdHat : ∀ i,
      higham24LiteralRoundedCirculantEigenvalues fp weight t c i ≠ 0) :
    Higham24RoundedCirculantSolveExecution
      (higham24DFT (2 ^ t)) (higham24DFTInverse (2 ^ t))
      (higham24InverseDiagonal
        (higham24LiteralRoundedCirculantEigenvalues fp weight t c)) b
      (higham24Eq24_6Bound (2 ^ t) t
        (higham24Eta mu (gamma fp 4)))
      (Real.sqrt 2 * gamma fp 4) where
  delta2 := higham24LiteralForwardPerturbation fp weight t b
  delta3 := higham24LiteralInversePerturbation fp weight t
    (higham24LiteralRoundedCirculantScaledRhs fp weight t c b)
  E := higham24DiagonalSolvePerturbation fp hgamma4
    (higham24LiteralRoundedCirculantEigenvalues fp weight t c)
    (higham24LiteralRoundedCirculantRhs fp weight t b) hdHat
  gHat := higham24LiteralRoundedCirculantRhs fp weight t b
  hHat := higham24LiteralRoundedCirculantScaledRhs fp weight t c b
  xHat := higham24LiteralRoundedCirculantSolve fp weight t c b
  forward_stage := by
    exact higham24_literalForwardFFT_representation
      fp hgamma4 weight mu hmu hw t b
  scaling_stage := by
    exact higham24_roundedDiagonalSolve_representation fp hgamma4
      (higham24LiteralRoundedCirculantEigenvalues fp weight t c)
      (higham24LiteralRoundedCirculantRhs fp weight t b) hdHat
  inverse_stage := by
    exact higham24_literalInverseFFT_representation fp hgamma4
      weight mu hmu hw t
        (higham24LiteralRoundedCirculantScaledRhs fp weight t c b)
  delta2_bound := higham24_literalForwardPerturbation_norm_le
    fp hgamma4 weight mu hmu hw t b hvalid
  delta3_bound := higham24_literalInversePerturbation_norm_le_forwardBound
    fp hgamma4 weight mu hmu hw t
      (higham24LiteralRoundedCirculantScaledRhs fp weight t c b) hvalid
  scaling_bound := higham24_diagonalSolvePerturbation_norm_le fp hgamma4
    (higham24LiteralRoundedCirculantEigenvalues fp weight t c)
    (higham24LiteralRoundedCirculantRhs fp weight t b) hdHat

/-- End-to-end matrix expression (24.7)--(24.8) for the literal four-stage
executor.  All three perturbations in the conclusion are the explicit values
constructed above. -/
theorem higham24_literalRoundedCirculantSolve_composed
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (c b : Fin (2 ^ t) → ℂ)
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1)
    (hdHat : ∀ i,
      higham24LiteralRoundedCirculantEigenvalues fp weight t c i ≠ 0) :
    let execution := higham24LiteralRoundedCirculantSolveExecution
      fp hgamma4 weight mu hmu hw t c b hvalid hdHat
    higham24LiteralRoundedCirculantSolve fp weight t c b =
      ((higham24DFTInverse (2 ^ t) + execution.delta3) *
        (1 + execution.E) *
        higham24InverseDiagonal
          (higham24LiteralRoundedCirculantEigenvalues fp weight t c) *
        (higham24DFT (2 ^ t) + execution.delta2)).mulVec b := by
  dsimp only
  exact higham24_roundedCirculantSolve_composed
    (higham24LiteralRoundedCirculantSolveExecution
      fp hgamma4 weight mu hmu hw t c b hvalid hdHat)

end NumStability
