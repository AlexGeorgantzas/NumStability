import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Source.Higham.Chapter28.Section04.Pascal.PascalCondition
import NumStability.Source.Higham.Chapter28.Section04.Pascal.SingularizingPerturbation

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28PascalCondition under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

noncomputable section

namespace NumStability

open Filter

open scoped BigOperators Topology Matrix.Norms.L2Operator

/-- The smallest Pascal singularizing perturbation has exact exponential
rate `4^{-n}`.  The separately proved factorial-ratio Stirling theorem refines
the comparison model by its `sqrt(n*pi)` subexponential factor. -/
theorem pascalOptimalPerturbation_log_rate :
    Tendsto
      (fun n : ℕ =>
        Real.log (opNorm2 (pascalOptimalSingularizingPerturbation n)) /
          (n : ℝ))
      atTop (nhds (-Real.log 4)) := by
  have hcondHalf : Tendsto
      (fun n : ℕ => (2 : ℝ)⁻¹ *
        (Real.log (pascalConditionTwo (n + 1)) / (n : ℝ)))
      atTop (nhds ((2 : ℝ)⁻¹ * Real.log 16)) :=
    tendsto_const_nhds.mul pascalConditionTwo_log_rate
  have hnorm : Tendsto
      (fun n : ℕ =>
        Real.log (opNorm2 (pascalMatrix (n + 1))) / (n : ℝ))
      atTop (nhds (Real.log 4)) := by
    have hcongr : (fun n : ℕ => (2 : ℝ)⁻¹ *
          (Real.log (pascalConditionTwo (n + 1)) / (n : ℝ))) =ᶠ[atTop]
        (fun n : ℕ =>
          Real.log (opNorm2 (pascalMatrix (n + 1))) / (n : ℝ)) := by
      filter_upwards with n
      have hPpos : 0 < opNorm2 (pascalMatrix (n + 1)) :=
        lt_of_lt_of_le (by
          exact_mod_cast Nat.centralBinom_pos n)
          (centralBinom_le_opNorm2_pascalMatrix n)
      rw [pascalConditionTwo_eq_opNorm2_sq, Real.log_pow]
      ring
    have h := hcondHalf.congr' hcongr
    convert h using 1
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.log_pow]
    norm_num
    ring
  have hneg : Tendsto
      (fun n : ℕ =>
        -(Real.log (opNorm2 (pascalMatrix (n + 1))) / (n : ℝ)))
      atTop (nhds (-Real.log 4)) := hnorm.neg
  apply hneg.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  have hPpos : 0 < opNorm2 (pascalMatrix (n + 1)) :=
    lt_of_lt_of_le (by exact_mod_cast Nat.centralBinom_pos n)
      (centralBinom_le_opNorm2_pascalMatrix n)
  have hopt : opNorm2 (pascalOptimalSingularizingPerturbation n) =
      (opNorm2 (pascalMatrix (n + 1)))⁻¹ := by
    calc
      opNorm2 (pascalOptimalSingularizingPerturbation n) =
          (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ :=
        (pascalOptimalPerturbation_is_operator2_minimal n).1
      _ = (opNorm2 (pascalMatrix (n + 1)))⁻¹ := by
        rw [opNorm2_pascalInverseMatrix_eq_pascalMatrix]
  rw [hopt, Real.log_inv]
  ring

end NumStability

end
