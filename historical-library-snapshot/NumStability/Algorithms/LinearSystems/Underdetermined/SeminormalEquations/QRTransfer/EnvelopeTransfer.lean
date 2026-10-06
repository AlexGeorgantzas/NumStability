import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.CondEstimation
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.LeastSquares.QRSolve
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates
import NumStability.Algorithms.LinearSystems.QR.GivensQR
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication
import NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Algorithms.LinearSystems.QR.HouseholderSpec
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.ComputedOutput.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.Forward
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Asymptotics.Bounds
import NumStability.Analysis.Conditioning.DistanceToSingularity
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.LinearOperators.Basic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.Comparisons
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.MatrixNorms.SpectralRadius
import NumStability.Analysis.MatrixNorms.UnitarilyInvariant
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.OperatorNorms.Basic
import NumStability.Analysis.Perturbation.LeastSquares.AugmentedSystem
import NumStability.Analysis.Perturbation.LeastSquares.BackwardError
import NumStability.Analysis.Perturbation.LeastSquares.Basic
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification
import NumStability.Analysis.Summation.Signs
import NumStability.Analysis.VectorNorms.Basic
import NumStability.FloatingPoint.Model

/-!
# Algorithms.LinearSystems.Underdetermined.SeminormalEquations.QRTransfer.EnvelopeTransfer

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Transfer of the SNE factor envelope through a QR factorization of A^T.



namespace NumStability

open scoped BigOperators

/-!
# SNE envelope transfer

The aggregate SNE theorem bounds its Gram perturbation by

  `eta * |R_hat^T| |R_hat|`.

The declarations below transport this quantity through the componentwise
Householder-QR certificate for `A^T`.  They deliberately stop at an explicit
source-data majorant.  Demmel--Higham's sharper first-order argument
(equations (3.17)--(3.20) of their 1993 paper) keeps the two triangular
perturbations separate and cancels QR factors before taking absolute values.
That cancellation is no longer present in `higham21SNEForwardEnvelope`, which
already contains `|(A A^T)^-1|`.

`Higham21SNEAggregateQRMajorantCond2Bridge` names the stronger aggregate
estimate that would be needed to fill the existing `hTransferred` premise by
this route.  It is intentionally an explicit proposition, not a claimed
consequence of the QR certificate.  The split triangular-solve certificate
retaining `DeltaR1` and `DeltaR2` is recovered below.  The genuinely missing
upstream input for the printed coefficient is the factorwise QR-cancellation
estimate consuming that certificate, corresponding to Demmel--Higham (3.18)
and (3.20).
-/














































/-- Entrywise source-data majorant for the square top block of a computed
    QR factor.  Here `G` is the nonnegative matrix from the componentwise
    Householder-QR error `|DeltaAT| <= rhoQR * G * |A^T|`. -/
noncomputable def higham21SNEQRFactorEntryMajorant
    {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (Q G : Fin (m + k) -> Fin (m + k) -> Real)
    (rhoQR : Real) (r i : Fin m) : Real :=
  ∑ p : Fin (m + k),
    |Q p (Fin.castAdd k r)| *
      (|A i p| + rhoQR *
        ∑ s : Fin (m + k), G p s * |A i s|)

/-- The QR-source majorant for the SNE Gram envelope
    `eta * |R_hat^T| |R_hat|`. -/
noncomputable def higham21SNEQRGramEnvelopeMajorant
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (Q G : Fin (m + k) -> Fin (m + k) -> Real)
    (rhoQR : Real) (i j : Fin m) : Real :=
  Higham21SNEBackwardCoefficient fp m *
    ∑ r : Fin m,
      higham21SNEQRFactorEntryMajorant A Q G rhoQR r i *
        higham21SNEQRFactorEntryMajorant A Q G rhoQR r j

/-- Propagate the QR-source Gram majorant through `|(A A^T)^-1|`. -/
noncomputable def higham21SNEQRForwardEnvelopeMajorant
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (AAT_inv : Fin m -> Fin m -> Real)
    (Q G : Fin (m + k) -> Fin (m + k) -> Real)
    (rhoQR : Real) (y_hat : Fin m -> Real) : Fin m -> Real :=
  fun i =>
    ∑ j : Fin m, |AAT_inv i j| *
      ∑ l : Fin m,
        higham21SNEQRGramEnvelopeMajorant fp A Q G rhoQR j l *
          |y_hat l|

/-- Final `|A|^T` transfer of the componentwise QR-source majorant. -/
noncomputable def higham21SNEQRTransferredEnvelopeMajorant
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (AAT_inv : Fin m -> Fin m -> Real)
    (Q G : Fin (m + k) -> Fin (m + k) -> Real)
    (rhoQR : Real) (y_hat : Fin m -> Real) : Fin (m + k) -> Real :=
  rectTransposeMulVec (absMatrixRect A)
    (higham21SNEQRForwardEnvelopeMajorant
      fp A AAT_inv Q G rhoQR y_hat)

theorem higham21_sne_qr_factor_entry_majorant_nonneg
    {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (Q G : Fin (m + k) -> Fin (m + k) -> Real)
    {rhoQR : Real} (hrhoQR : 0 <= rhoQR)
    (hG : forall p s, 0 <= G p s) (r i : Fin m) :
    0 <= higham21SNEQRFactorEntryMajorant A Q G rhoQR r i := by
  unfold higham21SNEQRFactorEntryMajorant
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg (abs_nonneg _)
  apply add_nonneg (abs_nonneg _)
  exact mul_nonneg hrhoQR
    (Finset.sum_nonneg (fun s hs => mul_nonneg (hG p s) (abs_nonneg _)))

/-- An explicit componentwise QR factor-error certificate bounds every entry
    of the computed square top block.  This is the direct formal counterpart
    of substituting `R_hat = Q_1^T (A^T + DeltaAT)` into the SNE analysis. -/
theorem higham21_sne_qr_top_factor_entry_le_source_majorant
    {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (Q : Fin (m + k) -> Fin (m + k) -> Real)
    (R_tall : Fin (m + k) -> Fin m -> Real)
    (R_hat : Fin m -> Fin m -> Real)
    (DeltaAT : Fin (m + k) -> Fin m -> Real)
    (G : Fin (m + k) -> Fin (m + k) -> Real)
    (rhoQR : Real)
    (hTop : forall r i,
      R_hat r i = R_tall (Fin.castAdd k r) i)
    (hR : forall a i,
      R_tall a i =
        matMulRect (m + k) (m + k) m (matTranspose Q)
          (fun p j => finiteTranspose A p j + DeltaAT p j) a i)
    (hDeltaAT : forall p i,
      |DeltaAT p i| <= rhoQR *
        ∑ s : Fin (m + k), G p s * |A i s|) :
    forall r i,
      |R_hat r i| <=
        higham21SNEQRFactorEntryMajorant A Q G rhoQR r i := by
  intro r i
  rw [hTop r i, hR (Fin.castAdd k r) i]
  simp only [matMulRect, matTranspose, finiteTranspose]
  calc
    |∑ p : Fin (m + k),
        Q p (Fin.castAdd k r) * (A i p + DeltaAT p i)| <=
        ∑ p : Fin (m + k),
          |Q p (Fin.castAdd k r) * (A i p + DeltaAT p i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : Fin (m + k),
          |Q p (Fin.castAdd k r)| * |A i p + DeltaAT p i| := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [abs_mul]
    _ <= ∑ p : Fin (m + k),
          |Q p (Fin.castAdd k r)| * (|A i p| + |DeltaAT p i|) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ <= ∑ p : Fin (m + k),
          |Q p (Fin.castAdd k r)| *
            (|A i p| + rhoQR *
              ∑ s : Fin (m + k), G p s * |A i s|) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (add_le_add (le_refl _) (hDeltaAT p i)) (abs_nonneg _)
    _ = higham21SNEQRFactorEntryMajorant A Q G rhoQR r i := rfl

/-- The actual SNE factor envelope is bounded entrywise by the source-data QR
    majorant. -/
theorem higham21_sne_rhat_gram_envelope_le_qr_source_majorant
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (Q : Fin (m + k) -> Fin (m + k) -> Real)
    (R_tall : Fin (m + k) -> Fin m -> Real)
    (R_hat : Fin m -> Fin m -> Real)
    (DeltaAT : Fin (m + k) -> Fin m -> Real)
    (G : Fin (m + k) -> Fin (m + k) -> Real)
    {rhoQR : Real} (hrhoQR : 0 <= rhoQR)
    (hG : forall p s, 0 <= G p s)
    (hm1 : gammaValid fp (m + 1))
    (hTop : forall r i,
      R_hat r i = R_tall (Fin.castAdd k r) i)
    (hR : forall a i,
      R_tall a i =
        matMulRect (m + k) (m + k) m (matTranspose Q)
          (fun p j => finiteTranspose A p j + DeltaAT p j) a i)
    (hDeltaAT : forall p i,
      |DeltaAT p i| <= rhoQR *
        ∑ s : Fin (m + k), G p s * |A i s|) :
    forall i j,
      higham21SNERHatGramEnvelope fp m R_hat i j <=
        higham21SNEQRGramEnvelopeMajorant fp A Q G rhoQR i j := by
  have hentry :=
    higham21_sne_qr_top_factor_entry_le_source_majorant
      A Q R_tall R_hat DeltaAT G rhoQR hTop hR hDeltaAT
  have hcoeff : 0 <= Higham21SNEBackwardCoefficient fp m :=
    Higham21SNEBackwardCoefficient_nonneg_of_gammaValid fp m hm1
  intro i j
  unfold higham21SNERHatGramEnvelope
  unfold higham21SNEQRGramEnvelopeMajorant
  apply mul_le_mul_of_nonneg_left _ hcoeff
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul (hentry r i) (hentry r j) (abs_nonneg _)
    (higham21_sne_qr_factor_entry_majorant_nonneg
      A Q G hrhoQR hG r i)

/-- The `DeltaC` returned by `sne_backward_error` inherits the explicit
    source-matrix QR majorant. -/
theorem higham21_sne_deltaC_le_qr_source_majorant
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (Q : Fin (m + k) -> Fin (m + k) -> Real)
    (R_tall : Fin (m + k) -> Fin m -> Real)
    (R_hat DeltaC : Fin m -> Fin m -> Real)
    (DeltaAT : Fin (m + k) -> Fin m -> Real)
    (G : Fin (m + k) -> Fin (m + k) -> Real)
    {rhoQR : Real} (hrhoQR : 0 <= rhoQR)
    (hG : forall p s, 0 <= G p s)
    (hm1 : gammaValid fp (m + 1))
    (hTop : forall r i,
      R_hat r i = R_tall (Fin.castAdd k r) i)
    (hR : forall a i,
      R_tall a i =
        matMulRect (m + k) (m + k) m (matTranspose Q)
          (fun p j => finiteTranspose A p j + DeltaAT p j) a i)
    (hDeltaAT : forall p i,
      |DeltaAT p i| <= rhoQR *
        ∑ s : Fin (m + k), G p s * |A i s|)
    (hDeltaC : forall i j,
      |DeltaC i j| <= higham21SNERHatGramEnvelope fp m R_hat i j) :
    forall i j,
      |DeltaC i j| <=
        higham21SNEQRGramEnvelopeMajorant fp A Q G rhoQR i j := by
  intro i j
  exact (hDeltaC i j).trans
    (higham21_sne_rhat_gram_envelope_le_qr_source_majorant
      fp A Q R_tall R_hat DeltaAT G hrhoQR hG hm1 hTop hR hDeltaAT i j)

theorem higham21_sne_forward_envelope_nonneg
    (fp : FPModel) (m : Nat)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (y_hat : Fin m -> Real)
    (hm1 : gammaValid fp (m + 1)) :
    forall i,
      0 <= higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat i := by
  have hcoeff : 0 <= Higham21SNEBackwardCoefficient fp m :=
    Higham21SNEBackwardCoefficient_nonneg_of_gammaValid fp m hm1
  intro i
  unfold higham21SNEForwardEnvelope
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg (abs_nonneg _)
  apply Finset.sum_nonneg
  intro l hl
  apply mul_nonneg _ (abs_nonneg _)
  unfold higham21SNERHatGramEnvelope
  exact mul_nonneg hcoeff
    (Finset.sum_nonneg (fun r hr =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)))

/-- Monotonicity of the inverse-action envelope after replacing the computed
    factor Gram envelope by a source-side majorant. -/
theorem higham21_sne_forward_envelope_le_qr_source_majorant
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (Q G : Fin (m + k) -> Fin (m + k) -> Real)
    (rhoQR : Real) (y_hat : Fin m -> Real)
    (hGram : forall i j,
      higham21SNERHatGramEnvelope fp m R_hat i j <=
        higham21SNEQRGramEnvelopeMajorant fp A Q G rhoQR i j) :
    forall i,
      higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat i <=
        higham21SNEQRForwardEnvelopeMajorant
          fp A AAT_inv Q G rhoQR y_hat i := by
  intro i
  unfold higham21SNEForwardEnvelope
  unfold higham21SNEQRForwardEnvelopeMajorant
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Finset.sum_le_sum
  intro l hl
  exact mul_le_mul_of_nonneg_right (hGram j l) (abs_nonneg _)

/-- Strongest unconditional transfer available from the aggregate SNE
    envelope and explicit componentwise QR factor error: the final envelope is
    bounded by a finite majorant involving only `A`, the orthogonal QR witness,
    and the QR componentwise-error witness `G`. -/
theorem higham21_sne_transferred_envelope_le_qr_source_majorant
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (AAT_inv : Fin m -> Fin m -> Real)
    (Q : Fin (m + k) -> Fin (m + k) -> Real)
    (R_tall : Fin (m + k) -> Fin m -> Real)
    (R_hat : Fin m -> Fin m -> Real)
    (DeltaAT : Fin (m + k) -> Fin m -> Real)
    (G : Fin (m + k) -> Fin (m + k) -> Real)
    {rhoQR : Real} (hrhoQR : 0 <= rhoQR)
    (hG : forall p s, 0 <= G p s)
    (y_hat : Fin m -> Real)
    (hm1 : gammaValid fp (m + 1))
    (hTop : forall r i,
      R_hat r i = R_tall (Fin.castAdd k r) i)
    (hR : forall a i,
      R_tall a i =
        matMulRect (m + k) (m + k) m (matTranspose Q)
          (fun p j => finiteTranspose A p j + DeltaAT p j) a i)
    (hDeltaAT : forall p i,
      |DeltaAT p i| <= rhoQR *
        ∑ s : Fin (m + k), G p s * |A i s|) :
    vecNorm2
        (higham21SNETransferredForwardEnvelope
          fp m (m + k) A AAT_inv R_hat y_hat) <=
      vecNorm2
        (higham21SNEQRTransferredEnvelopeMajorant
          fp A AAT_inv Q G rhoQR y_hat) := by
  have hGram :=
    higham21_sne_rhat_gram_envelope_le_qr_source_majorant
      fp A Q R_tall R_hat DeltaAT G hrhoQR hG hm1 hTop hR hDeltaAT
  have hForward :=
    higham21_sne_forward_envelope_le_qr_source_majorant
      fp A AAT_inv R_hat Q G rhoQR y_hat hGram
  apply vecNorm2_le_of_abs_le
  intro j
  have hsource_nonneg :
      0 <= rectTransposeMulVec (absMatrixRect A)
        (higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat) j := by
    unfold rectTransposeMulVec absMatrixRect
    exact Finset.sum_nonneg (fun i hi =>
      mul_nonneg (abs_nonneg _)
        (higham21_sne_forward_envelope_nonneg
          fp m AAT_inv R_hat y_hat hm1 i))
  unfold higham21SNETransferredForwardEnvelope
  rw [abs_of_nonneg hsource_nonneg]
  unfold higham21SNEQRTransferredEnvelopeMajorant
  unfold rectTransposeMulVec absMatrixRect
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hForward i) (abs_nonneg _)

/-- Concrete Householder QR on `A^T` supplies every witness needed by the
    preceding source-majorant theorem.  This is unconditional under the actual
    QR gamma domain; no abstract factorization relation is left to the caller. -/
theorem higham21_sne_concrete_householder_qr_transferred_envelope_majorant
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (AAT_inv : Fin m -> Fin m -> Real)
    (y_hat : Fin m -> Real)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hm1 : gammaValid fp (m + 1)) :
    let Q :=
      fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A)
    let R_tall :=
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m -> Fin m -> Real :=
      fun i j => R_tall (Fin.castAdd k i) j
    let rhoQR : Real :=
      (m + k : Real) *
        gamma fp (m * householderConstructApplyGammaIndex (m + k))
    exists (DeltaAT : Fin (m + k) -> Fin m -> Real)
      (G : Fin (m + k) -> Fin (m + k) -> Real),
      (forall a i,
        R_tall a i =
          matMulRect (m + k) (m + k) m (matTranspose Q)
            (fun p j => finiteTranspose A p j + DeltaAT p j) a i) /\
      (forall p s, 0 <= G p s) /\
      frobNorm G = 1 /\
      (forall p i,
        |DeltaAT p i| <= rhoQR *
          ∑ s : Fin (m + k), G p s * |A i s|) /\
      vecNorm2
          (higham21SNETransferredForwardEnvelope
            fp m (m + k) A AAT_inv R_hat y_hat) <=
        vecNorm2
          (higham21SNEQRTransferredEnvelopeMajorant
            fp A AAT_inv Q G rhoQR y_hat) := by
  dsimp only
  have hmk : m <= m + k := Nat.le_add_right m k
  have hsteps : 0 < Nat.min (m + k) m := by
    simpa [Nat.min_eq_right hmk] using hm
  have hvalidMin :
      gammaValid fp
        (Nat.min (m + k) m *
          householderConstructApplyGammaIndex (m + k)) := by
    simpa [Nat.min_eq_right hmk] using hvalidQR
  have hQR :=
    fl_householderQRPanel_R_higham_backward_error_gammaHigham_of_global_gammaValid
      fp (m + k) m (finiteTranspose A) hsteps hvalidMin
  rcases hQR.result with
    ⟨DeltaAT, G, hR, hDeltaATNorm, hG, hGNorm, hDeltaAT⟩
  have hrhoQR :
      0 <= (m + k : Real) *
        gamma fp (m * householderConstructApplyGammaIndex (m + k)) :=
    mul_nonneg (by positivity) (gamma_nonneg fp hvalidQR)
  have hDeltaAT' : forall p i,
      |DeltaAT p i| <=
        ((m + k : Real) *
          gamma fp (m * householderConstructApplyGammaIndex (m + k))) *
          ∑ s : Fin (m + k), G p s * |A i s| := by
    intro p i
    simpa [Nat.min_eq_right hmk, matMulRect, finiteTranspose] using
      hDeltaAT p i
  have hTransfer :=
    higham21_sne_transferred_envelope_le_qr_source_majorant
      fp A AAT_inv
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
        (fun i j =>
          fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
            (Fin.castAdd k i) j)
        DeltaAT G hrhoQR hG y_hat hm1 (by intro r i; rfl) hR hDeltaAT'
  exact ⟨DeltaAT, G, hR, hG, hGNorm, hDeltaAT', hTransfer⟩

/-- The exact source-faithful input still missing from the library.

    Unlike `higham21SNEForwardEnvelope`, `splitEnvelope` is to be constructed
    before merging the two triangular perturbations.  Demmel--Higham's
    factorwise QR cancellations should prove both its pointwise validity and
    the displayed transferred `cond2` estimate. -/
def Higham21SNESplitFactorwiseCond2TransferInput
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (AAT_inv R_hat : Fin m -> Fin m -> Real)
    (b y : Fin m -> Real) (C : Real) : Prop :=
  let eta := Higham21SNEBackwardCoefficient fp m
  let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
  let x := rectTransposeMulVec A y
  let Aplus := undetAplusOfGramInv A AAT_inv
  exists splitEnvelope : Fin m -> Real,
    (forall i, |y_hat i - y i| <= splitEnvelope i) /\
    vecNorm2 (rectTransposeMulVec (absMatrixRect A) splitEnvelope) <=
      ((m + k : Real) - 1) * eta * higham21Cond2With A Aplus *
          vecNorm2 x +
        eta ^ 2 * C



































































































































































































/-- Exact remaining input for the existing `hTransferred` premise.

    A proof of this proposition cannot in general be obtained by monotonicity
    from the aggregate absolute envelope: even at exact QR, taking
    `|(A A^T)^-1|` before the QR cancellations can introduce an additional
    condition factor.  The source proof instead establishes a factorwise
    analogue using separate `DeltaR1` and `DeltaR2` certificates. -/
def Higham21SNEAggregateQRMajorantCond2Bridge
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (AAT_inv : Fin m -> Fin m -> Real)
    (Q G : Fin (m + k) -> Fin (m + k) -> Real)
    (rhoQR C : Real) (y y_hat : Fin m -> Real) : Prop :=
  let eta := Higham21SNEBackwardCoefficient fp m
  let x := rectTransposeMulVec A y
  let Aplus := undetAplusOfGramInv A AAT_inv
  vecNorm2
      (higham21SNEQRTransferredEnvelopeMajorant
        fp A AAT_inv Q G rhoQR y_hat) <=
    ((m + k : Real) - 1) * eta * higham21Cond2With A Aplus *
        vecNorm2 x +
      eta ^ 2 * C

/-- Fill the precise `hTransferred` shape if the stronger aggregate-majorant
    `cond2` bridge is supplied.  All movement from the actual computed
    `R_hat` to source data is proved here.  The source proof does not establish
    `hBridge`; it instead needs the split triangular-solve input named in the
    module documentation. -/
theorem higham21_sne_hTransferred_of_componentwise_qr_factor_error
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real)
    (AAT_inv : Fin m -> Fin m -> Real)
    (Q : Fin (m + k) -> Fin (m + k) -> Real)
    (R_tall : Fin (m + k) -> Fin m -> Real)
    (R_hat : Fin m -> Fin m -> Real)
    (DeltaAT : Fin (m + k) -> Fin m -> Real)
    (G : Fin (m + k) -> Fin (m + k) -> Real)
    {rhoQR : Real} (hrhoQR : 0 <= rhoQR)
    (hG : forall p s, 0 <= G p s)
    (y y_hat : Fin m -> Real) (C : Real)
    (hm1 : gammaValid fp (m + 1))
    (hTop : forall r i,
      R_hat r i = R_tall (Fin.castAdd k r) i)
    (hR : forall a i,
      R_tall a i =
        matMulRect (m + k) (m + k) m (matTranspose Q)
          (fun p j => finiteTranspose A p j + DeltaAT p j) a i)
    (hDeltaAT : forall p i,
      |DeltaAT p i| <= rhoQR *
        ∑ s : Fin (m + k), G p s * |A i s|)
    (hBridge : Higham21SNEAggregateQRMajorantCond2Bridge
      fp A AAT_inv Q G rhoQR C y y_hat) :
    let eta := Higham21SNEBackwardCoefficient fp m
    let x := rectTransposeMulVec A y
    let Aplus := undetAplusOfGramInv A AAT_inv
    vecNorm2
        (higham21SNETransferredForwardEnvelope
          fp m (m + k) A AAT_inv R_hat y_hat) <=
      ((m + k : Real) - 1) * eta * higham21Cond2With A Aplus *
          vecNorm2 x +
        eta ^ 2 * C := by
  dsimp only [Higham21SNEAggregateQRMajorantCond2Bridge] at hBridge ⊢
  exact
    (higham21_sne_transferred_envelope_le_qr_source_majorant
      fp A AAT_inv Q R_tall R_hat DeltaAT G hrhoQR hG y_hat hm1
        hTop hR hDeltaAT).trans hBridge

end NumStability
