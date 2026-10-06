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
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation09.EquationClosure
import NumStability.Source.Higham.Chapter21.Equation09.ProjectorNorm
import NumStability.Source.Higham.Chapter21.RowScalingInvariance

/-!
# Source.Higham.Chapter21.Equation08.ProjectorNorm

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

















































































































































































































































































































/-- Sharpened equation-(21.8) residual adapter: the projection residual carries
    the exact zero/one factor instead of only the uniform contractive bound. -/
theorem higham21_eq21_8_projection_residual_norm_le_projectorFactor
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus)
    (w : Fin n -> Real) :
    vecNorm2
        (fun j => w j - rectMatMulVec Aplus (rectMatMulVec A w) j) <=
      higham21Eq21_9ProjectorFactor m n * vecNorm2 w := by
  have hcert :=
    higham21_complement_projector_rectOpNorm2Le_exact
      A Aplus hmn hRight hMP.domain_projection_symmetric
  have haction := hcert w
  rw [lsAugmentedProjectionBlock_mulVec] at haction
  exact haction














end NumStability
