import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Underdetermined.BackwardError.Rowwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Foundations.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.CorrectedRecurrence.Core
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Section03.MethodComparison.Core

/-!
# Source.Higham.Chapter21.Theorem04.ModifiedGramSchmidtQMethod.Core

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 21, unnumbered MGS discussion in Section 21.3 (printed pp. 412-413).



namespace NumStability

open scoped BigOperators

noncomputable section

/-! ## The displayed comparison bound -/




































































/-! ## Naive forward formation and its two exact error channels -/











































































































































































































































































/-! ## The corrected backward recurrence -/


































































/-! ## Rowwise stability handoff -/



























/-- The combined corrected-MGS certificate yields exactly the rowwise
    backward-error predicate used by Theorem 21.4. -/
theorem higham21_mgs_corrected_rowwise_backward_stable {m n : Nat}
    {A : Fin m -> Fin n -> Real} {b : Fin m -> Real}
    {Qhat : Fin n -> Fin m -> Real} {Rrepair : Fin m -> Fin m -> Real}
    {Qrepair DeltaAT : Fin n -> Fin m -> Real}
    {y : Fin m -> Real} {state : Fin (m + 1) -> Fin n -> Real}
    {xhat : Fin n -> Real} {eta : Real}
    (hcert : Higham21MGSCorrectedRowwiseCertificate
      A b Qhat Rrepair Qrepair DeltaAT y state xhat eta) :
    UndetRowwiseBackwardErrorBounded m n A b xhat eta := by
  rcases hcert.right_inverse with ⟨Rinv, hRight⟩
  have hfactor :
      finiteTranspose
          (fun i j => A i j + finiteTranspose DeltaAT i j) =
        matMulRect n m m Qrepair Rrepair := by
    ext i j
    simpa [finiteTranspose] using hcert.factor i j
  have hminQ :
      RectMinNormSolution m n
        (fun i j => A i j + finiteTranspose DeltaAT i j) b
        (higham21MGSNaiveFormation Qrepair y) :=
    higham21_mgs_economy_qr_min_norm
      (fun i j => A i j + finiteTranspose DeltaAT i j) b
      Qrepair Rrepair Rinv y hfactor hcert.triangular_solve
      hcert.orthonormal hRight
  have hmin :
      RectMinNormSolution m n
        (fun i j => A i j + finiteTranspose DeltaAT i j) b xhat := by
    rw [hcert.repaired_output]
    exact hminQ
  have hrows :=
    higham21_row_bounds_of_transposed_qr_column_bounds
      (finiteTranspose A) DeltaAT hcert.column_bound
  have hrow : forall i : Fin m,
      rectRowNorm2 (finiteTranspose DeltaAT) i <=
        eta * rectRowNorm2 A i := by
    intro i
    simpa only [finiteTranspose_finiteTranspose] using hrows i
  exact higham21_rowwise_backward_error_bound_witness
    m n A (finiteTranspose DeltaAT) b xhat eta
    hcert.eta_nonneg hmin hrow













































/-- Exact-solve specialization that reuses the Chapter 19 MGS certificate.
    The compatibility hypothesis is precisely the corrected-recurrence
    stability fact not present in the current rounded MGS infrastructure. -/
theorem higham21_mgs_corrected_rowwise_backward_stable_of_mgs_repair
    {m n : Nat} {A : Fin m -> Fin n -> Real} {b : Fin m -> Real}
    {Qhat : Fin n -> Fin m -> Real} {Rhat : Fin m -> Fin m -> Real}
    {y : Fin m -> Real} {state : Fin (m + 1) -> Fin n -> Real}
    {xhat : Fin n -> Real}
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hMGS : ModifiedGramSchmidtBackwardError n m
      (finiteTranspose A) Qhat Rhat
      c1 c2 c3 u normA kappaA higherOrder)
    (hrec : Higham21MGSCorrectedBackwardRecurrence Qhat y state xhat)
    (hsolve : rectMatMulVec (finiteTranspose Rhat) y = b)
    (hRight : Exists fun Rinv : Fin m -> Fin m -> Real =>
      IsRightInverse m Rhat Rinv)
    (heta : 0 <= c3 * u)
    (hcompat : Higham21MGSCorrectedMGSRepairCompatibility hMGS y xhat) :
    UndetRowwiseBackwardErrorBounded m n A b xhat (c3 * u) := by
  rcases hcompat with
    ⟨Qrepair, DeltaAT, hQ, hfactor, hcolumn, houtput⟩
  let hcert : Higham21MGSCorrectedRowwiseCertificate
      A b Qhat Rhat Qrepair DeltaAT y state xhat (c3 * u) :=
    { recurrence := hrec
      upper := hMGS.upper
      orthonormal := hQ
      factor := hfactor
      triangular_solve := hsolve
      right_inverse := hRight
      repaired_output := houtput
      column_bound := hcolumn
      eta_nonneg := heta }
  exact higham21_mgs_corrected_rowwise_backward_stable hcert

end

end NumStability
