/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter24.ForwardFFTPerturbation

namespace NumStability

open scoped Matrix.Norms.L2Operator
open ComplexConjugate

/-!
# The rounded inverse FFT as a conjugated forward FFT

The inverse-transform implementation used here is the standard identity
`F_n⁻¹ x = n⁻¹ conj (F_n (conj x))`.  Thus a perturbation matrix produced by
the literal forward executor gives an inverse-transform perturbation with the
printed extra factor `n⁻¹`; no inverse-stage error certificate is assumed.
-/

/-- Entrywise complex conjugation of a finite matrix. -/
noncomputable def higham24EntrywiseConjugateMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => conj (A i j)

/-- Coordinatewise conjugation on complex Euclidean space. -/
noncomputable def higham24ConjugateEuclidean {n : ℕ}
    (x : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => conj (WithLp.ofLp x i))

theorem higham24_conjugateEuclidean_norm {n : ℕ}
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖higham24ConjugateEuclidean x‖ = ‖x‖ := by
  have hsquares : ‖higham24ConjugateEuclidean x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp [higham24ConjugateEuclidean]
  nlinarith [norm_nonneg (higham24ConjugateEuclidean x), norm_nonneg x]

/-- Entrywise conjugation preserves the spectral norm. -/
theorem higham24_entrywiseConjugateMatrix_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖higham24EntrywiseConjugateMatrix A‖ = ‖A‖ := by
  have haction (M : Matrix (Fin n) (Fin n) ℂ)
      (x : EuclideanSpace ℂ (Fin n)) :
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
          (higham24EntrywiseConjugateMatrix M) x =
        higham24ConjugateEuclidean
          ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) M
            (higham24ConjugateEuclidean x)) := by
    ext i
    simp [higham24EntrywiseConjugateMatrix, higham24ConjugateEuclidean,
      Matrix.mulVec, dotProduct]
  have hle (M : Matrix (Fin n) (Fin n) ℂ) :
      ‖higham24EntrywiseConjugateMatrix M‖ ≤ ‖M‖ := by
    change ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
      (higham24EntrywiseConjugateMatrix M)‖ ≤ ‖M‖
    refine ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))
      (higham24EntrywiseConjugateMatrix M)).opNorm_le_bound
        (norm_nonneg M) ?_
    intro x
    rw [haction]
    rw [higham24_conjugateEuclidean_norm]
    simpa only [higham24_conjugateEuclidean_norm] using
      (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) M).le_opNorm
        (higham24ConjugateEuclidean x))
  apply le_antisymm (hle A)
  have hinvolution :
      higham24EntrywiseConjugateMatrix
          (higham24EntrywiseConjugateMatrix A) = A := by
    ext i j
    simp [higham24EntrywiseConjugateMatrix]
  simpa [hinvolution] using hle (higham24EntrywiseConjugateMatrix A)

/-- Conjugating a matrix-vector product conjugates the matrix entries and the
input coordinates. -/
theorem higham24_entrywiseConjugateMatrix_mulVec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (higham24EntrywiseConjugateMatrix A).mulVec x =
      fun i => conj (A.mulVec (fun j => conj (x j)) i) := by
  funext i
  simp [higham24EntrywiseConjugateMatrix, Matrix.mulVec, dotProduct]

/-- The exact inverse DFT is the scaled entrywise conjugate of the symmetric
forward DFT. -/
theorem higham24_dftInverse_eq_scaled_entrywiseConjugate (n : ℕ) :
    higham24DFTInverse n =
      ((n : ℂ)⁻¹) • higham24EntrywiseConjugateMatrix (higham24DFT n) := by
  ext i j
  simp [higham24DFTInverse, higham24DFT,
    higham9_13_fourierVandermondeScaledAdjoint,
    higham24EntrywiseConjugateMatrix, Matrix.smul_apply,
    higham9_13_fourierVandermonde_symm]

/-- Standard inverse-FFT executor formed from any concrete forward executor.
The later producer instantiates `forward` with the literal rounded radix-2
implementation. -/
noncomputable def higham24RoundedInverseFromForward {n : ℕ}
    (forward : (Fin n → ℂ) → Fin n → ℂ) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun i => ((n : ℂ)⁻¹) * conj (forward (fun j => conj (x j)) i)

/-- The inverse perturbation produced from a forward perturbation. -/
noncomputable def higham24InversePerturbationFromForward {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((n : ℂ)⁻¹) • higham24EntrywiseConjugateMatrix Delta

/-- A concrete forward-stage matrix equation yields the inverse-stage matrix
equation for the standard conjugated-forward implementation. -/
theorem higham24_roundedInverseFromForward_representation {n : ℕ}
    (forward : (Fin n → ℂ) → Fin n → ℂ)
    (x : Fin n → ℂ) (Delta : Matrix (Fin n) (Fin n) ℂ)
    (hforward :
      forward (fun j => conj (x j)) =
        (higham24DFT n + Delta).mulVec (fun j => conj (x j))) :
    higham24RoundedInverseFromForward forward x =
      (higham24DFTInverse n +
        higham24InversePerturbationFromForward Delta).mulVec x := by
  rw [higham24_dftInverse_eq_scaled_entrywiseConjugate]
  unfold higham24RoundedInverseFromForward
    higham24InversePerturbationFromForward
  rw [hforward]
  funext i
  simp [Matrix.add_mulVec, Matrix.smul_mulVec,
    higham24_entrywiseConjugateMatrix_mulVec]
  ring

/-- The inverse perturbation has exactly the source factor `n⁻¹` times the
forward perturbation norm. -/
theorem higham24_inversePerturbationFromForward_norm {n : ℕ}
    (Delta : Matrix (Fin n) (Fin n) ℂ) :
    ‖higham24InversePerturbationFromForward Delta‖ =
      (n : ℝ)⁻¹ * ‖Delta‖ := by
  rw [higham24InversePerturbationFromForward, norm_smul,
    higham24_entrywiseConjugateMatrix_norm]
  simp [norm_inv]

/-- Producer bridge with the printed inverse-FFT budget.  Its only premise is
the forward perturbation generated for the conjugated input. -/
theorem higham24_roundedInverseFromForward_exists_perturbation {n : ℕ}
    (forward : (Fin n → ℂ) → Fin n → ℂ)
    (x : Fin n → ℂ) (bound : ℝ)
    (hforward : ∃ Delta : Matrix (Fin n) (Fin n) ℂ,
      forward (fun j => conj (x j)) =
          (higham24DFT n + Delta).mulVec (fun j => conj (x j)) ∧
        ‖Delta‖ ≤ bound) :
    ∃ Delta3 : Matrix (Fin n) (Fin n) ℂ,
      higham24RoundedInverseFromForward forward x =
          (higham24DFTInverse n + Delta3).mulVec x ∧
        ‖Delta3‖ ≤ (n : ℝ)⁻¹ * bound := by
  rcases hforward with ⟨Delta, hstage, hbound⟩
  refine ⟨higham24InversePerturbationFromForward Delta,
    higham24_roundedInverseFromForward_representation forward x Delta hstage, ?_⟩
  rw [higham24_inversePerturbationFromForward_norm]
  exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (by positivity))

/-! ## Literal radix-2 inverse producer -/

/-- The actual inverse FFT used by the rounded circulant solver: conjugate the
input, run the literal rounded forward radix-2 executor, conjugate the output,
and scale exactly by `2⁻ᵗ`. -/
noncomputable def higham24RoundedInverseRadix2FFTFin
    (fp : FPModel) (weight : ∀ s, Higham24BitIndex s → ℂ)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) : Fin (2 ^ t) → ℂ :=
  higham24RoundedInverseFromForward
    (higham24RoundedRadix2FFTFin fp weight t) x

/-- The inverse perturbation obtained from the explicit rank-one forward
perturbation on the conjugated inverse-FFT input. -/
noncomputable def higham24LiteralInversePerturbation
    (fp : FPModel) (weight : ∀ s, Higham24BitIndex s → ℂ)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) :
    Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℂ :=
  higham24InversePerturbationFromForward
    (higham24LiteralForwardPerturbation fp weight t (fun j => conj (x j)))

/-- The literal inverse executor has the source matrix-perturbation form. -/
theorem higham24_literalInverseFFT_representation
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) :
    higham24RoundedInverseRadix2FFTFin fp weight t x =
      (higham24DFTInverse (2 ^ t) +
        higham24LiteralInversePerturbation fp weight t x).mulVec x := by
  apply higham24_roundedInverseFromForward_representation
  exact higham24_literalForwardFFT_representation
    fp hgamma4 weight mu hmu hw t (fun j => conj (x j))

/-- The produced inverse perturbation has the sharp printed
`n⁻¹ f(n,u)` bound. -/
theorem higham24_literalInversePerturbation_norm_le
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
      (((2 ^ t : ℕ) : ℝ)⁻¹) *
        higham24Eq24_6Bound (2 ^ t) t
          (higham24Eta mu (gamma fp 4)) := by
  rw [higham24LiteralInversePerturbation,
    higham24_inversePerturbationFromForward_norm]
  exact mul_le_mul_of_nonneg_left
    (higham24_literalForwardPerturbation_norm_le
      fp hgamma4 weight mu hmu hw t (fun j => conj (x j)) hvalid)
    (inv_nonneg.mpr (by positivity))

/-- Producer form of the actual inverse-FFT stage, with no assumed inverse
trace or target equality. -/
theorem higham24_literalInverseFFT_exists_perturbation
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ)
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1) :
    ∃ Delta3 : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℂ,
      higham24RoundedInverseRadix2FFTFin fp weight t x =
          (higham24DFTInverse (2 ^ t) + Delta3).mulVec x ∧
        ‖Delta3‖ ≤ (((2 ^ t : ℕ) : ℝ)⁻¹) *
          higham24Eq24_6Bound (2 ^ t) t
            (higham24Eta mu (gamma fp 4)) := by
  exact ⟨higham24LiteralInversePerturbation fp weight t x,
    higham24_literalInverseFFT_representation
      fp hgamma4 weight mu hmu hw t x,
    higham24_literalInversePerturbation_norm_le
      fp hgamma4 weight mu hmu hw t x hvalid⟩

end NumStability
