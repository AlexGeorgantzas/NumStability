/-
# Unconditional finite-dimensional Kreiss endpoints

This small public endpoint module applies the proved Spijker arc-length
theorem from `MatrixPowersSpijkerPlanarAnalysis` to the interface results in
`MatrixPowersKreissSpijker`.
-/

import NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis

namespace NumStability

open scoped Real Topology ComplexOrder
open Complex Metric Set MeasureTheory

noncomputable section

/-- Unconditional pointwise sharp reverse Kreiss estimate. -/
theorem norm_pow_le_exp_mul_dim_proved
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ) {K : ℝ}
    (hK : KreissResolventBound A K) (k : ℕ) :
    ‖A ^ k‖ ≤ Real.exp 1 * n * K :=
  norm_pow_le_exp_mul_dim_of_spijker
    (spijkerArcLengthBound_proved n) A hK k

/-- Unconditional uniform power bound from the sharp Spijker theorem. -/
theorem powerBound_exp_mul_dim_proved
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ) {K : ℝ}
    (hK : KreissResolventBound A K) :
    PowerBound A (Real.exp 1 * n * K) :=
  powerBound_exp_mul_dim_of_spijker
    (spijkerArcLengthBound_proved n) A hK

/-- Unconditional literal upper endpoint in Higham's notation. -/
theorem higham18_kreiss_upper_proved
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (hres : ∀ z : ℂ, 1 < ‖z‖ → z ∈ resolventSet ℂ A)
    (hbdd : BddAbove (kreissResolventValueSet A)) :
    matrixPowerNormSup A ≤
      Real.exp 1 * n * kreissConstant A :=
  higham18_kreiss_upper_of_spijker
    (spijkerArcLengthBound_proved n) A hres hbdd

/-- Unconditional two-sided finite-dimensional Kreiss theorem, closing the
Chapter 18 Spijker dependency. -/
theorem higham18_kreiss_two_sided_proved
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (hres : ∀ z : ℂ, 1 < ‖z‖ → z ∈ resolventSet ℂ A)
    (hbdd : BddAbove (kreissResolventValueSet A)) :
    kreissConstant A ≤ matrixPowerNormSup A ∧
      matrixPowerNormSup A ≤ Real.exp 1 * n * kreissConstant A :=
  higham18_kreiss_two_sided_of_spijker
    (spijkerArcLengthBound_proved n) A hres hbdd

end
end NumStability
