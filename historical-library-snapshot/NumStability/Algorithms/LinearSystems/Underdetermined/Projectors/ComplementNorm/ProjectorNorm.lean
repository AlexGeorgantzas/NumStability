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
# Algorithms.LinearSystems.Underdetermined.Projectors.ComplementNorm.ProjectorNorm

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- The exact norm of the complementary Moore--Penrose domain projector.




namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- A real `m`-by-`n` matrix with `m < n` has a nonzero right-nullspace
    vector.  This is the rank-nullity step needed for the strict
    underdetermined branch of the projector norm equality. -/
theorem higham21_exists_nonzero_rectMatMulVec_eq_zero_of_lt
    {m n : Nat} (A : Fin m -> Fin n -> Real) (hmn : m < n) :
    ∃ x : Fin n -> Real, x ≠ 0 ∧ rectMatMulVec A x = 0 := by
  classical
  let T : (Fin n -> Real) →ₗ[Real] (Fin m -> Real) :=
    (Matrix.of A).mulVecLin
  have hdim :
      Module.finrank Real (Fin m -> Real) <
        Module.finrank Real (Fin n -> Real) := by
    simpa using hmn
  have hker : LinearMap.ker T ≠ (⊥ : Submodule Real (Fin n -> Real)) :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := T) hdim
  rcases (Submodule.ne_bot_iff (LinearMap.ker T)).1 hker with
    ⟨x, hxmem, hxne⟩
  have hTx : T x = 0 := by
    simpa [LinearMap.mem_ker] using hxmem
  refine ⟨x, hxne, ?_⟩
  ext i
  have hi := congrFun hTx i
  simpa [T, rectMatMulVec, Matrix.mulVecLin, Matrix.mulVec,
    dotProduct, Matrix.of] using hi

/-- Unit-vector form of the strict rectangular nullspace witness. -/
theorem higham21_exists_unit_rectMatMulVec_eq_zero_of_lt
    {m n : Nat} (A : Fin m -> Fin n -> Real) (hmn : m < n) :
    ∃ x : Fin n -> Real, vecNorm2 x = 1 ∧ rectMatMulVec A x = 0 := by
  obtain ⟨x, hxne, hAx⟩ :=
    higham21_exists_nonzero_rectMatMulVec_eq_zero_of_lt A hmn
  have hxnorm_ne : vecNorm2 x ≠ 0 := by
    intro hxnorm
    apply hxne
    funext j
    exact (vecNorm2_eq_zero_iff x).mp hxnorm j
  have hxpos : 0 < vecNorm2 x :=
    lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm_ne)
  let y : Fin n -> Real := fun j => (vecNorm2 x)⁻¹ * x j
  refine ⟨y, ?_, ?_⟩
  · simpa [y] using vecNorm2_inv_smul_self_of_pos x hxpos
  · calc
      rectMatMulVec A y =
          fun i => (vecNorm2 x)⁻¹ * rectMatMulVec A x i := by
        simpa [y] using rectMatMulVec_smul A (vecNorm2 x)⁻¹ x
      _ = 0 := by
        rw [hAx]
        funext i
        simp

/-- The Chapter 20 block notation used by equations (21.8) and (21.9) is
    entrywise the source matrix `I - Aplus*A`. -/
theorem higham21_lsAugmentedProjectionBlock_eq_complement
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) :
    lsAugmentedProjectionBlock Aplus A =
      fun i j => idMatrix n i j - rectMatMul Aplus A i j := by
  ext i j
  simp only [lsAugmentedProjectionBlock, rectMatMulVec, rectMatMul]













/-- If `m < n`, the complement `I - Aplus*A` fixes a unit vector in the
    nullspace of `A`, independently of any pseudoinverse identities. -/
theorem higham21_complement_projector_exists_unit_fixed_vector_of_lt
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m < n) :
    ∃ x : Fin n -> Real,
      vecNorm2 x = 1 ∧
        rectMatMulVec (lsAugmentedProjectionBlock Aplus A) x = x := by
  obtain ⟨x, hxnorm, hAx⟩ :=
    higham21_exists_unit_rectMatMulVec_eq_zero_of_lt A hmn
  refine ⟨x, hxnorm, ?_⟩
  rw [lsAugmentedProjectionBlock_mulVec, hAx]
  ext j
  simp [rectMatMulVec]

/-- The strict underdetermined nullspace witness gives the missing lower
    bound for the exact complexified Euclidean operator norm. -/
theorem higham21_one_le_complement_projector_complexMatrixOp2_of_lt
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m < n) :
    1 <= complexMatrixOp2
      (realRectToCMatrix (lsAugmentedProjectionBlock Aplus A)) := by
  let Q : Fin n -> Fin n -> Real := lsAugmentedProjectionBlock Aplus A
  obtain ⟨x, hxnorm, hxfix⟩ :=
    higham21_complement_projector_exists_unit_fixed_vector_of_lt
      A Aplus hmn
  have hQx : rectMatMulVec Q x = x := by
    simpa [Q] using hxfix
  calc
    1 = vecNorm2 (rectMatMulVec Q x) := by rw [hQx, hxnorm]
    _ = norm
        (complexMatrixEuclideanLin (realRectToCMatrix Q)
          (realVecToEuclidean x)) := by
      symm
      exact
        realRectToCMatrix_euclideanLin_realVecToEuclidean_norm Q x
    _ <= complexMatrixOp2 (realRectToCMatrix Q) *
        norm (realVecToEuclidean x) := by
      rw [complexMatrixOp2_eq_norm_euclideanLin]
      exact ContinuousLinearMap.le_opNorm
        ((complexMatrixEuclideanLin
          (realRectToCMatrix Q)).toContinuousLinearMap)
        (realVecToEuclidean x)
    _ = complexMatrixOp2 (realRectToCMatrix Q) := by
      rw [realVecToEuclidean_norm, hxnorm, mul_one]





















































































/-- The repository's exact real square `opNorm2` agrees with the exact norm
    of the complexification used by the rectangular spectral API. -/
theorem higham21_opNorm2_eq_complexMatrixOp2_realRectToCMatrix
    {n : Nat} (M : Fin n -> Fin n -> Real) :
    opNorm2 M = complexMatrixOp2 (realRectToCMatrix M) := by
  apply le_antisymm
  · exact opNorm2_le_of_opNorm2Le M
      (complexMatrixOp2_nonneg (realRectToCMatrix M))
      (opNorm2Le_complexMatrixOp2_realRectToCMatrix M)
  · exact complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le M
      (opNorm2_nonneg M) (opNorm2Le_opNorm2 M)


























































































































end NumStability
