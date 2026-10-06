/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- The exact norm of the complementary Moore--Penrose domain projector.

import NumStability.Algorithms.Underdetermined.Higham21Eq21_8
import NumStability.Algorithms.Underdetermined.Higham21Eq21_9

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
