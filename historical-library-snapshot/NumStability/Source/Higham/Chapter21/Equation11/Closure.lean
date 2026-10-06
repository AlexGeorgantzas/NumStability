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
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.ComputedOutput.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.Forward
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.Householder.EndToEnd
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.TriangularSolves.EnvelopeTransfer
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Closure
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Signed

/-!
# Source.Higham.Chapter21.Equation11.Closure

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Concrete Householder-QR closure for the seminormal-equations path.







namespace NumStability

open scoped BigOperators

/-!
# Concrete signed SNE closure

The analysis-only QR perturbation below is chosen from the proved
implementation-backed Householder panel theorem.  The computed objects remain
the actual panel `Q`, its actual top square `R_hat`, the two rounded triangular
solves, and the rounded final `A^T` action.
-/
























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 21, Section 21.3, equation (21.11), SNE
Householder path up to the QR-perturbed exact reference.

The theorem instantiates the actual panel top block, both rounded triangular
solves, and the final rounded `A^T` product.  Its three quantitative premises
are local: the QR perturbation acting on the exact dual vector, a majorant for
the final matrix-vector call, and the explicit signed higher-order expression.
None of them assumes the displayed output-error conclusion. -/
theorem higham21_sne_householder_actual_output_signed_reference_bound
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (cF cg C : Real)
    (hQRAction :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
      let ybar := higham21SNEHouseholderReferenceY fp A b
      let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
      vecNorm2 (rectTransposeMulVec F ybar) <=
        gamma fp m * cF *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar)
    (hFormationMajorant :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
      let R_hat := higham21SNEHouseholderRHat fp A
      let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
      let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y_hat i|)) <=
        cg * higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar)
    (hSignedRemainder :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let Q := higham21SNEHouseholderEconomyQ fp A
      let R := higham21SNEHouseholderRHat fp A
      let Rinv := higham21SNEHouseholderRInv fp A
      let ybar := higham21SNEHouseholderReferenceY fp A b
      let yhat := higham21SNEComputedNormalSolution fp m R b
      forall DeltaR1 DeltaR2 : Fin m -> Fin m -> Real,
        (forall i j, |DeltaR1 i j| <= gamma fp m * |R i j|) ->
        (forall i j, |DeltaR2 i j| <= gamma fp m * |R i j|) ->
        (forall i,
          (∑ r : Fin m, (R r i + DeltaR1 r i) *
            (∑ j : Fin m, (R r j + DeltaR2 r j) * yhat j)) = b i) ->
        vecNorm2
          (higham21SNEDHSignedRemainderAt
            F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar) <=
          gamma fp m ^ 2 * C) :
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let R_hat := higham21SNEHouseholderRHat fp A
    let x_hat := higham21SNEActualOutput fp m (m + k) A R_hat b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    vecNorm2 (fun j => x_hat j - xbar j) <=
      gamma fp m *
          ((m : Real) + Real.sqrt (m : Real) + cF + cg) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar +
        gamma fp m ^ 2 * C := by
  dsimp only at hQRAction hFormationMajorant hSignedRemainder ⊢
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let g := higham21SNEHouseholderFormationError fp A b
  have hupper : forall i j : Fin m, j.val < i.val -> R i j = 0 := by
    simpa [R] using
      higham21_sne_householder_RHat_upper fp A hm hvalidQR
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hbar :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) = b := by
    simpa [R, ybar] using
      higham21_sne_householder_referenceY_normal_eq
        fp A b hm hvalidQR hdiag
  obtain ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsolve⟩ :=
    higham21_sne_split_triangular_solve_backward_error
      fp m R b (by simpa [R] using hdiag) hupper hmGamma
  have hhat :
      rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) = b := by
    funext i
    simpa [rectMatMulVec, finiteTranspose, yhat] using hsolve i
  have hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) :=
    hbar.trans hhat.symm
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hxbar : xbar = rectTransposeMulVec B ybar := by
    rfl
  have hg0 : vecNorm2 g <=
      gamma fp m *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) := by
    simpa [g, R, yhat] using
      higham21_sne_householder_formation_error_norm fp A b hmGamma
  have hg : vecNorm2 g <=
      gamma fp m * cg *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
        vecNorm2 xbar := by
    calc
      vecNorm2 g <= gamma fp m *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) := hg0
      _ <= gamma fp m *
          (cg * higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar) :=
        mul_le_mul_of_nonneg_left (by simpa [B, F, R, yhat, xbar] using
          hFormationMajorant) (gamma_nonneg fp hmGamma)
      _ = gamma fp m * cg *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by ring
  have hrem := hSignedRemainder DeltaR1 DeltaR2
    (by simpa [R] using hDeltaR1) (by simpa [R] using hDeltaR2)
    (by simpa [R, yhat] using hsolve)
  have hCore := higham21_dh1993_signed_output_bound
    hm (gamma fp m) cF cg C (gamma_nonneg fp hmGamma)
      A F Q R Rinv DeltaR1 DeltaR2 ybar yhat xbar g
      hQ hFactor hInv hxbar hNormal hDeltaR1 hDeltaR2
      (by simpa [F, B, ybar, xbar] using hQRAction) hg
      (by simpa [F, Q, R, Rinv, ybar, yhat] using hrem)
  have herr :
      (fun j => rectTransposeMulVec A yhat j + g j - xbar j) =
        fun j => higham21SNEActualOutput fp m (m + k) A R b j - xbar j := by
    ext j
    simp [g, higham21SNEHouseholderFormationError, R, yhat]
  rw [herr] at hCore
  simpa [F, B, R, xbar] using hCore

/-- Concrete signed Householder-SNE bound with the QR-action premise closed
from the actual panel's componentwise Higham certificate.

Unlike the compatibility wrapper above, the coefficient keeps the exact
`rho / (1-rho)` term.  Thus it is valid at finite roundoff and separates into
the linear `rho` contribution plus a genuine quadratic geometric remainder. -/
theorem higham21_sne_householder_actual_output_signed_reference_bound_closed_qr
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hmGamma : gammaValid fp m)
    (hdiag : forall i : Fin m,
      higham21SNEHouseholderRHat fp A i i ≠ 0)
    (hrho_lt : higham21SNEHouseholderRho fp m k < 1)
    (cg C : Real)
    (hFormationMajorant :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
      let R_hat := higham21SNEHouseholderRHat fp A
      let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
      let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y_hat i|)) <=
        cg * higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar)
    (hSignedRemainder :
      let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
      let Q := higham21SNEHouseholderEconomyQ fp A
      let R := higham21SNEHouseholderRHat fp A
      let Rinv := higham21SNEHouseholderRInv fp A
      let ybar := higham21SNEHouseholderReferenceY fp A b
      let yhat := higham21SNEComputedNormalSolution fp m R b
      forall DeltaR1 DeltaR2 : Fin m -> Fin m -> Real,
        (forall i j, |DeltaR1 i j| <= gamma fp m * |R i j|) ->
        (forall i j, |DeltaR2 i j| <= gamma fp m * |R i j|) ->
        (forall i,
          (∑ r : Fin m, (R r i + DeltaR1 r i) *
            (∑ j : Fin m, (R r j + DeltaR2 r j) * yhat j)) = b i) ->
        vecNorm2
          (higham21SNEDHSignedRemainderAt
            F Q R Rinv DeltaR1 DeltaR2 ybar yhat ybar) <=
          gamma fp m ^ 2 * C) :
    let rho := higham21SNEHouseholderRho fp m k
    let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
    let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
    let R_hat := higham21SNEHouseholderRHat fp A
    let x_hat := higham21SNEActualOutput fp m (m + k) A R_hat b
    let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
    vecNorm2 (fun j => x_hat j - xbar j) <=
      (gamma fp m * ((m : Real) + Real.sqrt (m : Real)) +
          rho / (1 - rho) + gamma fp m * cg) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar +
        gamma fp m ^ 2 * C := by
  dsimp only at hFormationMajorant hSignedRemainder ⊢
  let rho := higham21SNEHouseholderRho fp m k
  let F := higham21SNEHouseholderDeltaA fp A hm hvalidQR
  let B : Fin m -> Fin (m + k) -> Real := fun i j => A i j + F i j
  let Q := higham21SNEHouseholderEconomyQ fp A
  let R := higham21SNEHouseholderRHat fp A
  let Rinv := higham21SNEHouseholderRInv fp A
  let ybar := higham21SNEHouseholderReferenceY fp A b
  let yhat := higham21SNEComputedNormalSolution fp m R b
  let xbar := higham21SNEHouseholderReferenceOutput fp A b hm hvalidQR
  let g := higham21SNEHouseholderFormationError fp A b
  have hupper : forall i j : Fin m, j.val < i.val -> R i j = 0 := by
    simpa [R] using
      higham21_sne_householder_RHat_upper fp A hm hvalidQR
  have hInv : IsInverse m R Rinv := by
    simpa [R, Rinv] using
      higham21_sne_householder_RHat_inverse fp A hm hvalidQR hdiag
  have hbar :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) = b := by
    simpa [R, ybar] using
      higham21_sne_householder_referenceY_normal_eq
        fp A b hm hvalidQR hdiag
  obtain ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsolve⟩ :=
    higham21_sne_split_triangular_solve_backward_error
      fp m R b (by simpa [R] using hdiag) hupper hmGamma
  have hhat :
      rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) = b := by
    funext i
    simpa [rectMatMulVec, finiteTranspose, yhat] using hsolve i
  have hNormal :
      rectMatMulVec (finiteTranspose R) (rectMatMulVec R ybar) =
        rectMatMulVec (finiteTranspose (fun i j => R i j + DeltaR1 i j))
          (rectMatMulVec (fun i j => R i j + DeltaR2 i j) yhat) :=
    hbar.trans hhat.symm
  have hQ : GramSchmidtOrthonormalColumns Q := by
    simpa [Q] using
      higham21_sne_householder_economyQ_orthonormal fp A hm hvalidQR
  have hFactor : finiteTranspose B = rectMatMul Q R := by
    simpa [B, F, Q, R] using
      higham21_sne_householder_economy_factor fp A hm hvalidQR
  have hxbar : xbar = rectTransposeMulVec B ybar := by rfl
  have hqr : vecNorm2 (rectTransposeMulVec F ybar) <=
      rho / (1 - rho) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by
    simpa [rho, F, B, ybar, xbar] using
      higham21_sne_householder_qr_action_absorbed
        fp A b hm hvalidQR hdiag hrho_lt
  have hg0 : vecNorm2 g <=
      gamma fp m *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) := by
    simpa [g, R, yhat] using
      higham21_sne_householder_formation_error_norm fp A b hmGamma
  have hg : vecNorm2 g <=
      gamma fp m * cg *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by
    calc
      vecNorm2 g <= gamma fp m *
          vecNorm2
            (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) := hg0
      _ <= gamma fp m *
          (cg * higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar) :=
        mul_le_mul_of_nonneg_left (by simpa [B, F, R, yhat, xbar] using
          hFormationMajorant) (gamma_nonneg fp hmGamma)
      _ = gamma fp m * cg *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar := by ring
  have hrem := hSignedRemainder DeltaR1 DeltaR2
    (by simpa [R] using hDeltaR1) (by simpa [R] using hDeltaR2)
    (by simpa [R, yhat] using hsolve)
  have hCore := higham21_dh1993_signed_output_bound_separate
    hm (gamma fp m)
      (rho / (1 - rho) *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar)
      (gamma fp m * cg *
        higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar)
      (gamma fp m ^ 2 * C)
      (gamma_nonneg fp hmGamma)
      A F Q R Rinv DeltaR1 DeltaR2 ybar yhat xbar g
      hQ hFactor hInv hxbar hNormal hDeltaR1 hDeltaR2 hqr hg
      (by simpa [F, Q, R, Rinv, ybar, yhat] using hrem)
  have herr :
      (fun j => rectTransposeMulVec A yhat j + g j - xbar j) =
        fun j => higham21SNEActualOutput fp m (m + k) A R b j - xbar j := by
    ext j
    simp [g, higham21SNEHouseholderFormationError, R, yhat]
  rw [herr] at hCore
  calc
    vecNorm2 (fun j =>
        higham21SNEActualOutput fp m (m + k) A R b j - xbar j) <=
      gamma fp m * ((m : Real) + Real.sqrt (m : Real)) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar +
        rho / (1 - rho) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar +
        gamma fp m * cg *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
            vecNorm2 xbar +
        gamma fp m ^ 2 * C := hCore
    _ = (gamma fp m * ((m : Real) + Real.sqrt (m : Real)) +
          rho / (1 - rho) + gamma fp m * cg) *
          higham21Cond2With B (undetAplusOfGramNonsingInv B) *
          vecNorm2 xbar +
        gamma fp m ^ 2 * C := by ring







































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
