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
import NumStability.Algorithms.LinearSystems.Underdetermined.Projectors.ComplementNorm.ProjectorNorm
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation04.UnderdeterminedSpec
import NumStability.Source.Higham.Chapter21.Equation08.EquationClosure
import NumStability.Source.Higham.Chapter21.Equation09.EquationClosure
import NumStability.Source.Higham.Chapter21.RowScalingInvariance

/-!
# Source.Higham.Chapter21.Equation09.ProjectorNorm

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





























































/-- In the square branch, a right inverse makes the complementary domain
    projector identically zero. -/
theorem higham21_complement_projector_eq_zero_of_square
    {n : Nat} (A Aplus : Fin n -> Fin n -> Real)
    (hRight : rectMatMul A Aplus = idMatrix n) :
    lsAugmentedProjectionBlock Aplus A = 0 := by
  have hLeft : rectMatMul Aplus A = idMatrix n :=
    higham21_eq21_8_square_left_inverse A Aplus hRight
  rw [higham21_lsAugmentedProjectionBlock_eq_complement A Aplus, hLeft]
  ext i j
  simp















































/-- Exact source radius as a repository-native `rectOpNorm2Le` certificate.
    This is the common adapter for the projector steps in (21.8) and (21.9). -/
theorem higham21_complement_projector_rectOpNorm2Le_exact
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A)) :
    rectOpNorm2Le (lsAugmentedProjectionBlock Aplus A)
      (higham21Eq21_9ProjectorFactor m n) :=
  higham21_eq21_9_complement_projector_rectOpNorm2Le
    A Aplus hmn hRight hSym

/-- Literal `I - Aplus*A` form of the exact rectangular operator certificate. -/
theorem higham21_projector_complement_rectOpNorm2Le_exact
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A)) :
    rectOpNorm2Le
        (fun i j => idMatrix n i j - rectMatMul Aplus A i j)
      (higham21Eq21_9ProjectorFactor m n) := by
  rw [← higham21_lsAugmentedProjectionBlock_eq_complement A Aplus]
  exact higham21_complement_projector_rectOpNorm2Le_exact
    A Aplus hmn hRight hSym

/-- The exact norm represented by the repository's complexified Euclidean
    operator norm: zero when `m = n`, and one when `m < n`. -/
theorem higham21_complement_projector_complexMatrixOp2_eq_projectorFactor
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A)) :
    complexMatrixOp2
        (realRectToCMatrix (lsAugmentedProjectionBlock Aplus A)) =
      higham21Eq21_9ProjectorFactor m n := by
  by_cases heq : m = n
  · subst n
    have hQzero : lsAugmentedProjectionBlock Aplus A = 0 :=
      higham21_complement_projector_eq_zero_of_square A Aplus hRight
    have hupper :
        complexMatrixOp2
            (realRectToCMatrix (lsAugmentedProjectionBlock Aplus A)) <= 0 := by
      apply complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le
        (lsAugmentedProjectionBlock Aplus A) le_rfl
      rw [hQzero]
      intro x
      have hzero :
          rectMatMulVec (0 : Fin m -> Fin m -> Real) x =
            (fun _ : Fin m => 0) := by
        funext i
        simp [rectMatMulVec]
      rw [hzero, vecNorm2_zero]
      simp
    have hopzero :
        complexMatrixOp2
            (realRectToCMatrix (lsAugmentedProjectionBlock Aplus A)) = 0 :=
      le_antisymm hupper (complexMatrixOp2_nonneg _)
    simpa [higham21Eq21_9ProjectorFactor] using hopzero
  · have hlt : m < n := lt_of_le_of_ne hmn heq
    have hminNat : Nat.min 1 (n - m) = 1 :=
      Nat.min_eq_left (Nat.sub_pos_of_lt hlt)
    have hmin : ((Nat.min 1 (n - m) : Nat) : Real) = 1 := by
      exact_mod_cast hminNat
    have hcontractive :
        rectOpNorm2Le (lsAugmentedProjectionBlock Aplus A) 1 := by
      simpa [higham21Eq21_9ProjectorFactor, hmin] using
        higham21_complement_projector_rectOpNorm2Le_exact
          A Aplus hmn hRight hSym
    have hupper :
        complexMatrixOp2
            (realRectToCMatrix (lsAugmentedProjectionBlock Aplus A)) <= 1 :=
      complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le
        (lsAugmentedProjectionBlock Aplus A) (by norm_num) hcontractive
    have hlower :
        1 <= complexMatrixOp2
          (realRectToCMatrix (lsAugmentedProjectionBlock Aplus A)) :=
      higham21_one_le_complement_projector_complexMatrixOp2_of_lt
        A Aplus hlt
    have hopone :
        complexMatrixOp2
            (realRectToCMatrix (lsAugmentedProjectionBlock Aplus A)) = 1 :=
      le_antisymm hupper hlower
    simpa [higham21Eq21_9ProjectorFactor, hmin] using hopone













/-- Complexified exact-operator-norm form of the equality immediately before
    equation (21.8). -/
theorem higham21_projector_complement_complexMatrixOp2_eq_min_one_sub
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A)) :
    complexMatrixOp2
        (realRectToCMatrix
          (fun i j => idMatrix n i j - rectMatMul Aplus A i j)) =
      ((Nat.min 1 (n - m) : Nat) : Real) := by
  have h :=
    higham21_complement_projector_complexMatrixOp2_eq_projectorFactor
      A Aplus hmn hRight hSym
  rw [higham21_lsAugmentedProjectionBlock_eq_complement A Aplus] at h
  simpa [higham21Eq21_9ProjectorFactor] using h

/-- Higham, 2nd ed., equality immediately preceding equation (21.8):

    `||I - Aplus*A||_2 = min {1, n-m}`.

    The left side is the repository's exact real square operator `2`-norm. -/
theorem higham21_projector_complement_opNorm2_eq_min_one_sub
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A)) :
    opNorm2 (fun i j => idMatrix n i j - rectMatMul Aplus A i j) =
      ((Nat.min 1 (n - m) : Nat) : Real) := by
  rw [higham21_opNorm2_eq_complexMatrixOp2_realRectToCMatrix]
  exact higham21_projector_complement_complexMatrixOp2_eq_min_one_sub
    A Aplus hmn hRight hSym

/-- Moore--Penrose adapter matching the supplied-pseudoinverse hypotheses of
    the equation-(21.8) development. -/
theorem higham21_projector_complement_opNorm2_eq_min_one_sub_of_moorePenrose
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus) :
    opNorm2 (fun i j => idMatrix n i j - rectMatMul Aplus A i j) =
      ((Nat.min 1 (n - m) : Nat) : Real) :=
  higham21_projector_complement_opNorm2_eq_min_one_sub
    A Aplus hmn hRight hMP.domain_projection_symmetric

/-- Canonical Gram-pseudoinverse version used by the source-facing (21.8) and
    (21.9) endpoints. -/
theorem higham21_projector_complement_opNorm2_eq_min_one_sub_of_gram_det_ne_zero
    {m n : Nat} (A : Fin m -> Fin n -> Real) (hmn : m <= n)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0) :
    opNorm2
        (fun i j => idMatrix n i j -
          rectMatMul (undetAplusOfGramNonsingInv A) A i j) =
      ((Nat.min 1 (n - m) : Nat) : Real) :=
  higham21_projector_complement_opNorm2_eq_min_one_sub_of_moorePenrose
    A (undetAplusOfGramNonsingInv A) hmn
    (higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
      A hdet)
    (higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero A hdet)

/-- On a nonempty domain, the source factor is not merely an admissible
    `rectOpNorm2Le` radius: it is the least such radius. -/
theorem higham21_complement_projector_rectOpNorm2Le_iff
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m <= n) (hn : 0 < n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A)) {c : Real} :
    rectOpNorm2Le (lsAugmentedProjectionBlock Aplus A) c ↔
      higham21Eq21_9ProjectorFactor m n <= c := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let Q : Fin n -> Fin n -> Real := lsAugmentedProjectionBlock Aplus A
  have hEq :
      complexMatrixOp2 (realRectToCMatrix Q) =
        higham21Eq21_9ProjectorFactor m n := by
    simpa [Q] using
      higham21_complement_projector_complexMatrixOp2_eq_projectorFactor
        A Aplus hmn hRight hSym
  constructor
  · intro hQc
    have hc : 0 <= c := rectOpNorm2Le_radius_nonneg Q hQc
    have hop : complexMatrixOp2 (realRectToCMatrix Q) <= c :=
      complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le Q hc hQc
    rw [hEq] at hop
    exact hop
  · intro hfactor
    apply rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le Q
    rw [hEq]
    exact hfactor



















/-- Exact operator-norm adapter named for the equation-(21.9) projector
    certificate that it strengthens. -/
theorem higham21_eq21_9_complement_projector_complexMatrixOp2_eq
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A)) :
    complexMatrixOp2
        (realRectToCMatrix (lsAugmentedProjectionBlock Aplus A)) =
      higham21Eq21_9ProjectorFactor m n :=
  higham21_complement_projector_complexMatrixOp2_eq_projectorFactor
    A Aplus hmn hRight hSym

end NumStability
