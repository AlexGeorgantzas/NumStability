import NumStability.Algorithms.LeastSquares.LSQRSolve

namespace HighamBenchCandidate

open NumStability

/-- The matrix-only value at the zero approximate solution, including `b = 0`. -/
noncomputable def zeroSolutionMatrixOnlyValue {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) : ℝ :=
  if b = 0 then 0 else vecNorm2 (rectLSRhs A b) / vecNorm2 b

/-- Higham, Problem 20.8: `y = 0`, `θ = ∞`, hence `Δb = 0`.
The witness and universal bound state that the value is an attained minimum. -/
theorem target {m n : ℕ} (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    lsNormwiseBackwardErrorMatrixOnlyEtaF A b (0 : Fin n → ℝ) =
        zeroSolutionMatrixOnlyValue A b ∧
      ∃ DeltaA : Fin m → Fin n → ℝ,
        LSNormwiseBackwardErrorFeasible A b (0 : Fin n → ℝ)
          DeltaA (0 : Fin m → ℝ) ∧
        frobNormRect DeltaA = zeroSolutionMatrixOnlyValue A b ∧
        ∀ E : Fin m → Fin n → ℝ,
          LSNormwiseBackwardErrorFeasible A b (0 : Fin n → ℝ)
            E (0 : Fin m → ℝ) →
          frobNormRect DeltaA ≤ frobNormRect E := by
  sorry

end HighamBenchCandidate
