import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Demmel
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Source.Higham.Chapter08.Equation15.FanInExecutor.FirstOrderResidual
import NumStability.Source.Higham.Chapter08.Equation18.FanInExecutor.FirstOrderForwardError

/-!
# Chapter10 Theorem07 FailureVacuity Vacuity

Canonical destination for material split out of
`NumStability.Algorithms.Ch10Theorem107FailureVacuity` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

/-- Positive definiteness transports backwards through a positive diagonal
congruence `A = D H D`. -/
theorem higham10_7_scaled_matrix_spd_of_diag_congruence
    (n : ℕ) (A H : Fin n → Fin n → ℝ) (D : Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hA : IsSymPosDef n A)
    (hcongr : ∀ i j, A i j = D i * H i j * D j) :
    IsSymPosDef n H := by
  let Dinv : Fin n → ℝ := fun i => (D i)⁻¹
  have hDinv : ∀ i, 0 < Dinv i := fun i => inv_pos.mpr (hD i)
  have hscaled : IsSymPosDef n (fun i j => Dinv i * A i j * Dinv j) :=
    isSymPosDef_diagCongr n Dinv A hDinv hA
  have heq : (fun i j => Dinv i * A i j * Dinv j) = H := by
    funext i j
    rw [hcongr i j]
    dsimp [Dinv]
    field_simp [ne_of_gt (hD i), ne_of_gt (hD j)]
  simpa [heq] using hscaled

/-- The scaled matrix in the literal Theorem 10.7 hypotheses has strictly
positive minimum eigenvalue. -/
theorem higham10_7_printed_scaled_minEigenvalue_pos
    (n : ℕ) (hn : 0 < n) (A H : Fin n → Fin n → ℝ) (D : Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hA : IsSymPosDef n A)
    (hHsym : IsSymmetricFiniteMatrix H)
    (hcongr : ∀ i j, A i j = D i * H i j * D j) :
    0 < finiteMinEigenvalue hn H hHsym := by
  have hHspd := higham10_7_scaled_matrix_spd_of_diag_congruence
    n A H D hD hA hcongr
  have hpos := higham7_finiteMinEigenvalue_pos_of_spd hn H hHspd
  simpa only [Subsingleton.elim hHspd.1 hHsym] using hpos

/-- **Literal Theorem 10.7 failure clause is vacuous.**  Under the source
premise that `A = D H D` is SPD, `lambda_min(H)` cannot be below the printed
negative threshold.  The floating-point assumptions are exactly those used
to make that threshold nonnegative. -/
theorem higham10_7_printed_failure_antecedent_impossible
    (n : ℕ) (hn : 0 < n) (fp : FPModel)
    (A H : Fin n → Fin n → ℝ) (D : Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hA : IsSymPosDef n A)
    (hHsym : IsSymmetricFiniteMatrix H)
    (hcongr : ∀ i j, A i j = D i * H i j * D j)
    (hn1 : gammaValid fp (n + 1))
    (hgamma_lt : gamma fp (n + 1) < 1) :
    ¬ finiteMinEigenvalue hn H hHsym ≤
      -((n : ℝ) * gamma fp (n + 1) / (1 - gamma fp (n + 1))) := by
  intro hfail
  have hminpos := higham10_7_printed_scaled_minEigenvalue_pos
    n hn A H D hD hA hHsym hcongr
  have hgamma0 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  have hden0 : 0 < 1 - gamma fp (n + 1) := by linarith
  have hthreshold0 :
      0 ≤ (n : ℝ) * gamma fp (n + 1) /
        (1 - gamma fp (n + 1)) := by positivity
  linarith

end NumStability
