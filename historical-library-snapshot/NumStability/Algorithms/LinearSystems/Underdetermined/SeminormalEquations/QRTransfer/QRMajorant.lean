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
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates
import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.LeastSquares.QRSolve
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR
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
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
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
# Algorithms.LinearSystems.Underdetermined.SeminormalEquations.QRTransfer.QRMajorant

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Componentwise QR-action estimates for the signed SNE analysis.



namespace NumStability

open scoped BigOperators

/-!
# QR perturbation action without an aggregate Gram envelope

The Householder backward-error theorem supplies

`|F i p| <= rho * sum_s G p s * |A i s|`,

where `G` is nonnegative and has operator norm at most one.  The lemmas below
keep this action on the dual vector.  This is the cancellation-compatible
route used by Demmel--Higham; it does not introduce `|(A A^T)⁻¹|`.
-/

/-- A componentwise Householder QR perturbation controls its transposed action
by the nonnegative QR majorant acting on `|A|ᵀ |y|`. -/
theorem higham21_sne_qr_error_transpose_action_le_majorant
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real)
    (G : Fin n -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho)
    (hG : forall p s, 0 <= G p s)
    (hF : forall p i,
      |F i p| <= rho * ∑ s : Fin n, G p s * |A i s|)
    (y : Fin m -> Real) :
    vecNorm2 (rectTransposeMulVec F y) <=
      rho * vecNorm2
        (rectMatMulVec G
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|))) := by
  let w : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)
  let Gw : Fin n -> Real := rectMatMulVec G w
  have hw : forall s, 0 <= w s := by
    intro s
    dsimp [w, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hGw : forall p, 0 <= Gw p := by
    intro p
    dsimp [Gw, rectMatMulVec]
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (hG p s) (hw s))
  have hpoint : forall p,
      |rectTransposeMulVec F y p| <= rho * Gw p := by
    intro p
    calc
      |rectTransposeMulVec F y p| <=
          ∑ i : Fin m, |F i p| * |y i| := by
        simpa [rectTransposeMulVec, finiteTranspose] using
          (abs_rectMatMulVec_le (finiteTranspose F) y p)
      _ <= ∑ i : Fin m,
          (rho * ∑ s : Fin n, G p s * |A i s|) * |y i| := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hF p i) (abs_nonneg _)
      _ = ∑ i : Fin m, ∑ s : Fin n,
          rho * (G p s * |A i s|) * |y i| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
      _ = ∑ s : Fin n, ∑ i : Fin m,
          rho * (G p s * |A i s|) * |y i| := Finset.sum_comm
      _ = rho * ∑ s : Fin n,
          G p s * (∑ i : Fin m, |A i s| * |y i|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = rho * Gw p := by rfl
  calc
    vecNorm2 (rectTransposeMulVec F y) <=
        vecNorm2 (fun p => rho * Gw p) := by
      apply vecNorm2_le_of_abs_le
      intro p
      simpa [abs_of_nonneg (mul_nonneg hrho (hGw p))] using hpoint p
    _ = rho * vecNorm2 Gw := by
      rw [vecNorm2_smul, abs_of_nonneg hrho]
    _ = rho * vecNorm2
        (rectMatMulVec G
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|))) := by
      rfl

/-- If the nonnegative QR majorant has operator norm at most one, the QR
perturbation action is at most `rho * || |A|ᵀ |y| ||₂`. -/
theorem higham21_sne_qr_error_transpose_action_le_source
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real)
    (G : Fin n -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho)
    (hG : forall p s, 0 <= G p s)
    (hGop : rectOpNorm2Le G 1)
    (hF : forall p i,
      |F i p| <= rho * ∑ s : Fin n, G p s * |A i s|)
    (y : Fin m -> Real) :
    vecNorm2 (rectTransposeMulVec F y) <=
      rho * vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)) := by
  have hmajorant :=
    higham21_sne_qr_error_transpose_action_le_majorant
      A F G rho hrho hG hF y
  calc
    vecNorm2 (rectTransposeMulVec F y) <=
        rho * vecNorm2
          (rectMatMulVec G
            (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|))) :=
      hmajorant
    _ <= rho *
        (1 * vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|))) :=
      mul_le_mul_of_nonneg_left (hGop _) hrho
    _ = rho * vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)) := by ring

/-- The same componentwise QR certificate controls the absolute action
`|F|ᵀ |y|`, which is the quantity needed before the signed cancellation. -/
theorem higham21_sne_qr_abs_error_transpose_action_le_source
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real)
    (G : Fin n -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho)
    (hG : forall p s, 0 <= G p s)
    (hGop : rectOpNorm2Le G 1)
    (hF : forall p i,
      |F i p| <= rho * ∑ s : Fin n, G p s * |A i s|)
    (y : Fin m -> Real) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect F) (fun i => |y i|)) <=
      rho * vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)) := by
  have hFabs : forall p i,
      |absMatrixRect F i p| <=
        rho * ∑ s : Fin n, G p s * |A i s| := by
    intro p i
    simpa [absMatrixRect] using hF p i
  simpa [absMatrixRect] using
    (higham21_sne_qr_error_transpose_action_le_source
      A (absMatrixRect F) G rho hrho hG hGop hFabs (fun i => |y i|))

/-- For `B = A + F`, the exact source action is bounded by the nearby action
plus the QR perturbation action. -/
theorem higham21_sne_source_dual_action_le_nearby_add_error
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real) (y : Fin m -> Real) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)) <=
      vecNorm2
          (rectTransposeMulVec
            (absMatrixRect (fun i j => A i j + F i j))
            (fun i => |y i|)) +
        vecNorm2
          (rectTransposeMulVec (absMatrixRect F) (fun i => |y i|)) := by
  let wA : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)
  let wB : Fin n -> Real :=
    rectTransposeMulVec
      (absMatrixRect (fun i j => A i j + F i j)) (fun i => |y i|)
  let wF : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect F) (fun i => |y i|)
  have hwA : forall j, 0 <= wA j := by
    intro j
    dsimp [wA, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hwB : forall j, 0 <= wB j := by
    intro j
    dsimp [wB, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hwF : forall j, 0 <= wF j := by
    intro j
    dsimp [wF, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hpoint : forall j, |wA j| <= wB j + wF j := by
    intro j
    rw [abs_of_nonneg (hwA j)]
    dsimp [wA, wB, wF, rectTransposeMulVec, absMatrixRect]
    calc
      ∑ i : Fin m, |A i j| * |y i| <=
          ∑ i : Fin m,
            (|A i j + F i j| + |F i j|) * |y i| := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |A i j| <= |A i j + F i j| + |F i j| := by
          calc
            |A i j| = |(A i j + F i j) - F i j| := by ring_nf
            _ <= |A i j + F i j| + |F i j| := abs_sub _ _
        exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)
      _ = (∑ i : Fin m, |A i j + F i j| * |y i|) +
          ∑ i : Fin m, |F i j| * |y i| := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hnorm : vecNorm2 wA <= vecNorm2 (fun j => wB j + wF j) := by
    apply vecNorm2_le_of_abs_le
    intro j
    simpa [abs_of_nonneg (add_nonneg (hwB j) (hwF j))] using hpoint j
  calc
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)) =
        vecNorm2 wA := by rfl
    _ <= vecNorm2 (fun j => wB j + wF j) := hnorm
    _ <= vecNorm2 wB + vecNorm2 wF := vecNorm2_add_le wB wF
    _ = vecNorm2
          (rectTransposeMulVec
            (absMatrixRect (fun i j => A i j + F i j))
            (fun i => |y i|)) +
        vecNorm2
          (rectTransposeMulVec (absMatrixRect F) (fun i => |y i|)) := by rfl




















































































































end NumStability
