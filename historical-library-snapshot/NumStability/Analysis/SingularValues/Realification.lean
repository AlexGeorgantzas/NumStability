-- Analysis/SingularValues/Realification.lean
--
-- Real/complex transfer lemmas for singular values and operator norms.

import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.SingularValues.Basic

/-!
# Realification of singular-value bounds

Relates real matrices to their complexifications, transporting transpose,
product, operator-norm, and singular-value witnesses between the two settings.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Complexification of a real rectangular matrix, used to transfer the
    rank-sensitive Lemma 6.6 absolute-matrix bound back to the older real
    rectangular operator-bound API. -/
noncomputable def realRectToCMatrix {m n : Nat}
    (A : Fin m -> Fin n -> Real) : CMatrix m n :=
  fun i j => (A i j : Complex)

/-- Complexification commutes with the repository's real finite transpose. -/
theorem realRectToCMatrix_matTranspose {n : Nat}
    (A : Fin n -> Fin n -> Real) :
    realRectToCMatrix (matTranspose A) =
      complexMatrixAdjoint (realRectToCMatrix A) := by
  ext i j
  simp [realRectToCMatrix, matTranspose, complexMatrixAdjoint,
    complexMatrixTranspose, complexConjMatrix]

/-- Complexification commutes with the repository's rectangular real finite
    transpose. -/
theorem realRectToCMatrix_finiteTranspose {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    realRectToCMatrix (finiteTranspose A) =
      complexMatrixAdjoint (realRectToCMatrix A) := by
  ext j i
  simp [realRectToCMatrix, finiteTranspose, complexMatrixAdjoint,
    complexMatrixTranspose, complexConjMatrix]

/-- The exact Euclidean operator `2`-norm of a complexified real rectangular
    matrix is invariant under the repository's finite transpose. -/
theorem complexMatrixOp2_realRectToCMatrix_finiteTranspose_eq {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    complexMatrixOp2 (realRectToCMatrix (finiteTranspose A)) =
      complexMatrixOp2 (realRectToCMatrix A) := by
  rw [realRectToCMatrix_finiteTranspose, complexMatrixOp2_adjoint_eq]

/-- Complexification commutes with the repository's real square matrix
    multiplication. -/
theorem realRectToCMatrix_matMul {n : Nat}
    (A B : Fin n -> Fin n -> Real) :
    realRectToCMatrix (matMul n A B) =
      complexMatrixMul (realRectToCMatrix A) (realRectToCMatrix B) := by
  ext i j
  simp [realRectToCMatrix, matMul, complexMatrixMul]

/-- Complexification commutes with the repository's real rectangular matrix
    multiplication. -/
theorem realRectToCMatrix_rectMatMul {m n p : Nat}
    (A : Fin m -> Fin n -> Real) (B : Fin n -> Fin p -> Real) :
    realRectToCMatrix (rectMatMul A B) =
      complexMatrixMul (realRectToCMatrix A) (realRectToCMatrix B) := by
  ext i j
  simp [realRectToCMatrix, rectMatMul, complexMatrixMul]

/-- Real square Gram matrices satisfy `‖AᵀA‖₂ = ‖A‖₂²` after
    complexification. -/
theorem complexMatrixOp2_realRectToCMatrix_transpose_mul_self_eq_sq {n : Nat}
    (A : Fin n -> Fin n -> Real) :
    complexMatrixOp2 (realRectToCMatrix (matMul n (matTranspose A) A)) =
      complexMatrixOp2 (realRectToCMatrix A) ^ 2 := by
  rw [realRectToCMatrix_matMul, realRectToCMatrix_matTranspose]
  exact complexMatrixOp2_adjoint_mul_self_eq_sq (realRectToCMatrix A)

/-- Real square right-Gram matrices satisfy `‖AAᵀ‖₂ = ‖A‖₂²` after
    complexification. -/
theorem complexMatrixOp2_realRectToCMatrix_mul_transpose_self_eq_sq {n : Nat}
    (A : Fin n -> Fin n -> Real) :
    complexMatrixOp2 (realRectToCMatrix (matMul n A (matTranspose A))) =
      complexMatrixOp2 (realRectToCMatrix A) ^ 2 := by
  rw [realRectToCMatrix_matMul, realRectToCMatrix_matTranspose]
  exact complexMatrixOp2_mul_adjoint_self_eq_sq (realRectToCMatrix A)

/-- Real rectangular Gram matrices satisfy `‖AᵀA‖₂ = ‖A‖₂²` after
    complexification. -/
theorem complexMatrixOp2_realRectToCMatrix_finiteTranspose_mul_self_eq_sq {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    complexMatrixOp2 (realRectToCMatrix (rectMatMul (finiteTranspose A) A)) =
      complexMatrixOp2 (realRectToCMatrix A) ^ 2 := by
  rw [realRectToCMatrix_rectMatMul, realRectToCMatrix_finiteTranspose]
  exact complexMatrixOp2_adjoint_mul_self_eq_sq (realRectToCMatrix A)

/-- Real rectangular right-Gram matrices satisfy `‖AAᵀ‖₂ = ‖A‖₂²` after
    complexification. -/
theorem complexMatrixOp2_realRectToCMatrix_mul_finiteTranspose_self_eq_sq {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    complexMatrixOp2 (realRectToCMatrix (rectMatMul A (finiteTranspose A))) =
      complexMatrixOp2 (realRectToCMatrix A) ^ 2 := by
  rw [realRectToCMatrix_rectMatMul, realRectToCMatrix_finiteTranspose]
  exact complexMatrixOp2_mul_adjoint_self_eq_sq (realRectToCMatrix A)

/-- A nonnegative real number has the same norm after embedding into `Complex`. -/
lemma complexNorm_ofReal_of_nonneg {a : Real} (ha : 0 <= a) :
    ‖((a : Real) : Complex)‖ = a := by
  have hsq : ‖((a : Real) : Complex)‖ ^ 2 = a ^ 2 := by
    rw [(Complex.normSq_eq_norm_sq ((a : Real) : Complex)).symm, Complex.normSq_ofReal]
    ring
  have habs := (sq_eq_sq_iff_abs_eq_abs ‖((a : Real) : Complex)‖ a).mp hsq
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg ha] at habs
  exact habs

/-- The complex norm of a real scalar is its absolute value. -/
lemma complexNorm_ofReal_eq_abs (a : Real) :
    ‖((a : Real) : Complex)‖ = |a| := by
  have hsq : ‖((a : Real) : Complex)‖ ^ 2 = |a| ^ 2 := by
    rw [(Complex.normSq_eq_norm_sq ((a : Real) : Complex)).symm,
      Complex.normSq_ofReal, sq_abs]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg a)).mp hsq

lemma opNorm2Le_to_rectOpNorm2Le {n : Nat}
    {A : Fin n -> Fin n -> Real} {c : Real}
    (hA : opNorm2Le A c) : rectOpNorm2Le A c := by
  intro x
  simpa [opNorm2Le, rectOpNorm2Le, matMulVec, rectMatMulVec] using hA x

/-- Rank of a real rectangular matrix through its complexification.  This is
    the rank notion used by the real rectangular Lemma 6.6 wrapper below. -/
noncomputable def realRectMatrixRank {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Nat :=
  complexMatrixRank (realRectToCMatrix A)

-- Keep the lazily generated equation theorem in its frozen semantic owner.
run_meta
  discard <| Lean.Meta.getEqnsFor? ``NumStability.realRectMatrixRank

/-- Real part of a complex Euclidean vector as the repository's real finite
    vector shape. -/
noncomputable def euclideanReVec {n : Nat}
    (z : EuclideanSpace Complex (Fin n)) : Fin n -> Real :=
  fun j => (WithLp.ofLp z j).re

/-- Imaginary part of a complex Euclidean vector as the repository's real finite
    vector shape. -/
noncomputable def euclideanImVec {n : Nat}
    (z : EuclideanSpace Complex (Fin n)) : Fin n -> Real :=
  fun j => (WithLp.ofLp z j).im

section

attribute [local instance]
  NumStability.ComplexSquareContractionMidpointProperty.«_proof_1»

/-- Embed a real finite vector into the complex Euclidean-space model used by
    `complexMatrixOp2`. -/
noncomputable def realVecToEuclidean {n : Nat}
    (x : Fin n -> Real) : EuclideanSpace Complex (Fin n) :=
  WithLp.toLp (2 : ENNReal) (fun j : Fin n => (x j : Complex))

end

theorem realRectToCMatrix_vecMul_re {m n : Nat}
    (A : Fin m -> Fin n -> Real) (z : EuclideanSpace Complex (Fin n))
    (i : Fin m) :
    ((complexMatrixVecMul (realRectToCMatrix A) (WithLp.ofLp z)) i).re =
      rectMatMulVec A (euclideanReVec z) i := by
  simp [complexMatrixVecMul, realRectToCMatrix, rectMatMulVec, euclideanReVec,
    Complex.mul_re]

theorem realRectToCMatrix_vecMul_im {m n : Nat}
    (A : Fin m -> Fin n -> Real) (z : EuclideanSpace Complex (Fin n))
    (i : Fin m) :
    ((complexMatrixVecMul (realRectToCMatrix A) (WithLp.ofLp z)) i).im =
      rectMatMulVec A (euclideanImVec z) i := by
  simp [complexMatrixVecMul, realRectToCMatrix, rectMatMulVec, euclideanImVec,
    Complex.mul_im]

/-- Squared Euclidean norm decomposition into real and imaginary parts. -/
theorem euclidean_norm_sq_re_im {n : Nat}
    (z : EuclideanSpace Complex (Fin n)) :
    ‖z‖ ^ 2 =
      vecNorm2 (euclideanReVec z) ^ 2 + vecNorm2 (euclideanImVec z) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [vecNorm2_sq, vecNorm2_sq]
  unfold vecNorm2Sq euclideanReVec euclideanImVec
  calc
    ∑ x : Fin n, ‖WithLp.ofLp z x‖ ^ 2 =
        ∑ x : Fin n,
          ((WithLp.ofLp z x).re ^ 2 + (WithLp.ofLp z x).im ^ 2) := by
          apply Finset.sum_congr rfl
          intro x _hx
          rw [← Complex.normSq_eq_norm_sq]
          simp [Complex.normSq_apply, pow_two]
    _ = (∑ x : Fin n, (WithLp.ofLp z x).re ^ 2) +
          ∑ x : Fin n, (WithLp.ofLp z x).im ^ 2 := by
          rw [Finset.sum_add_distrib]

theorem realRectToCMatrix_euclideanLin_ofLp {m n : Nat}
    (A : Fin m -> Fin n -> Real) (z : EuclideanSpace Complex (Fin n)) :
    WithLp.ofLp (complexMatrixEuclideanLin (realRectToCMatrix A) z) =
      complexMatrixVecMul (realRectToCMatrix A) (WithLp.ofLp z) := by
  rfl

/-- The complexified action has squared norm equal to the squared norms of the
    real and imaginary real-matrix actions. -/
theorem realRectToCMatrix_euclideanLin_norm_sq {m n : Nat}
    (A : Fin m -> Fin n -> Real) (z : EuclideanSpace Complex (Fin n)) :
    ‖complexMatrixEuclideanLin (realRectToCMatrix A) z‖ ^ 2 =
      vecNorm2 (rectMatMulVec A (euclideanReVec z)) ^ 2 +
        vecNorm2 (rectMatMulVec A (euclideanImVec z)) ^ 2 := by
  have hre :
      euclideanReVec (complexMatrixEuclideanLin (realRectToCMatrix A) z) =
        rectMatMulVec A (euclideanReVec z) := by
    ext i
    rw [euclideanReVec, realRectToCMatrix_euclideanLin_ofLp]
    exact realRectToCMatrix_vecMul_re A z i
  have him :
      euclideanImVec (complexMatrixEuclideanLin (realRectToCMatrix A) z) =
        rectMatMulVec A (euclideanImVec z) := by
    ext i
    rw [euclideanImVec, realRectToCMatrix_euclideanLin_ofLp]
    exact realRectToCMatrix_vecMul_im A z i
  rw [euclidean_norm_sq_re_im, hre, him]

/-- A real rectangular operator-bound certificate bounds the Euclidean operator
    norm of the complexified matrix. -/
theorem complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le {m n : Nat}
    (A : Fin m -> Fin n -> Real) {c : Real} (hc : 0 <= c)
    (hA : rectOpNorm2Le A c) :
    complexMatrixOp2 (realRectToCMatrix A) <= c := by
  rw [complexMatrixOp2_eq_norm_euclideanLin]
  refine ContinuousLinearMap.opNorm_le_bound
    ((complexMatrixEuclideanLin (realRectToCMatrix A)).toContinuousLinearMap) hc ?_
  intro z
  have hre_sq :
      vecNorm2 (rectMatMulVec A (euclideanReVec z)) ^ 2 <=
        (c * vecNorm2 (euclideanReVec z)) ^ 2 :=
    (sq_le_sq₀ (vecNorm2_nonneg _) (mul_nonneg hc (vecNorm2_nonneg _))).mpr
      (hA (euclideanReVec z))
  have him_sq :
      vecNorm2 (rectMatMulVec A (euclideanImVec z)) ^ 2 <=
        (c * vecNorm2 (euclideanImVec z)) ^ 2 :=
    (sq_le_sq₀ (vecNorm2_nonneg _) (mul_nonneg hc (vecNorm2_nonneg _))).mpr
      (hA (euclideanImVec z))
  have hsq :
      ‖complexMatrixEuclideanLin (realRectToCMatrix A) z‖ ^ 2 <=
        (c * ‖z‖) ^ 2 := by
    rw [realRectToCMatrix_euclideanLin_norm_sq]
    calc
      vecNorm2 (rectMatMulVec A (euclideanReVec z)) ^ 2 +
          vecNorm2 (rectMatMulVec A (euclideanImVec z)) ^ 2
          <= (c * vecNorm2 (euclideanReVec z)) ^ 2 +
              (c * vecNorm2 (euclideanImVec z)) ^ 2 := by
            exact add_le_add hre_sq him_sq
      _ = c ^ 2 *
            (vecNorm2 (euclideanReVec z) ^ 2 +
              vecNorm2 (euclideanImVec z) ^ 2) := by
            ring
      _ = c ^ 2 * ‖z‖ ^ 2 := by
            rw [← euclidean_norm_sq_re_im z]
      _ = (c * ‖z‖) ^ 2 := by
            ring
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hc (norm_nonneg z))).mp hsq

@[simp]
theorem euclideanReVec_realVecToEuclidean {n : Nat}
    (x : Fin n -> Real) :
    euclideanReVec (realVecToEuclidean x) = x := by
  ext i
  simp [euclideanReVec, realVecToEuclidean]

@[simp]
theorem euclideanImVec_realVecToEuclidean {n : Nat}
    (x : Fin n -> Real) :
    euclideanImVec (realVecToEuclidean x) = fun _i : Fin n => 0 := by
  ext i
  simp [euclideanImVec, realVecToEuclidean]

/-- The real-vector embedding into complex Euclidean space preserves the
    repository's real `2`-norm. -/
theorem realVecToEuclidean_norm {n : Nat} (x : Fin n -> Real) :
    ‖realVecToEuclidean x‖ = vecNorm2 x := by
  apply (sq_eq_sq₀ (norm_nonneg _) (vecNorm2_nonneg x)).mp
  have h := euclidean_norm_sq_re_im (realVecToEuclidean x)
  simpa [vecNorm2_zero] using h

theorem realRectToCMatrix_euclideanLin_realVecToEuclidean_norm {m n : Nat}
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) :
    ‖complexMatrixEuclideanLin (realRectToCMatrix A) (realVecToEuclidean x)‖ =
      vecNorm2 (rectMatMulVec A x) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (vecNorm2_nonneg _)).mp
  have hzero :
      rectMatMulVec A (fun _j : Fin n => 0) = fun _i : Fin m => 0 := by
    ext i
    simp [rectMatMulVec]
  rw [realRectToCMatrix_euclideanLin_norm_sq]
  simp [hzero, vecNorm2_zero]

/-- The smallest singular value of a real rectangular matrix, viewed through
    the complexification used by the shared spectral API, is attained by a
    nonzero real vector. -/
theorem realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq
    {m k : Nat} (A : Fin m -> Fin (k + 1) -> Real) :
    ∃ x : Fin (k + 1) -> Real, x ≠ 0 ∧
      vecNorm2Sq (rectMatMulVec A x) =
        (complexMatrixSingularValue (realRectToCMatrix A) (Fin.last k)) ^ 2 *
          vecNorm2Sq x := by
  let C : CMatrix m (k + 1) := realRectToCMatrix A
  let i : Fin (k + 1) := Fin.last k
  let z : EuclideanSpace Complex (Fin (k + 1)) :=
    complexMatrixGramEigenvectorBasis C i
  let xr : Fin (k + 1) -> Real := euclideanReVec z
  let xim : Fin (k + 1) -> Real := euclideanImVec z
  let sigma : Real := complexMatrixSingularValue C i
  have hattain :
      ‖complexMatrixEuclideanLin C z‖ ^ 2 = sigma ^ 2 * ‖z‖ ^ 2 := by
    have h :=
      complexMatrixSingularValue_mul_norm_gramEigenvectorBasis_eq_norm_euclideanLin
        C i
    change sigma * ‖z‖ = ‖complexMatrixEuclideanLin C z‖ at h
    calc
      ‖complexMatrixEuclideanLin C z‖ ^ 2 = (sigma * ‖z‖) ^ 2 := by
        rw [h]
      _ = sigma ^ 2 * ‖z‖ ^ 2 := by
        ring
  have hsum :
      vecNorm2 (rectMatMulVec A xr) ^ 2 +
          vecNorm2 (rectMatMulVec A xim) ^ 2 =
        sigma ^ 2 * (vecNorm2 xr ^ 2 + vecNorm2 xim ^ 2) := by
    calc
      vecNorm2 (rectMatMulVec A xr) ^ 2 +
          vecNorm2 (rectMatMulVec A xim) ^ 2 =
          ‖complexMatrixEuclideanLin C z‖ ^ 2 := by
            dsimp [C, xr, xim]
            rw [realRectToCMatrix_euclideanLin_norm_sq]
      _ = sigma ^ 2 * ‖z‖ ^ 2 := hattain
      _ = sigma ^ 2 * (vecNorm2 xr ^ 2 + vecNorm2 xim ^ 2) := by
            rw [euclidean_norm_sq_re_im z]
  have hsum_expanded :
      vecNorm2 (rectMatMulVec A xr) ^ 2 +
          vecNorm2 (rectMatMulVec A xim) ^ 2 =
        sigma ^ 2 * vecNorm2 xr ^ 2 +
          sigma ^ 2 * vecNorm2 xim ^ 2 := by
    calc
      vecNorm2 (rectMatMulVec A xr) ^ 2 +
          vecNorm2 (rectMatMulVec A xim) ^ 2 =
          sigma ^ 2 * (vecNorm2 xr ^ 2 + vecNorm2 xim ^ 2) := hsum
      _ = sigma ^ 2 * vecNorm2 xr ^ 2 +
          sigma ^ 2 * vecNorm2 xim ^ 2 := by
            ring
  have hsigma_nonneg : 0 ≤ sigma := by
    simpa [sigma, C, i] using
      complexMatrixSingularValue_nonneg C i
  have hlower_re :
      sigma * vecNorm2 xr ≤ vecNorm2 (rectMatMulVec A xr) := by
    have h :=
      complexMatrixSingularValue_last_mul_norm_le_norm_euclideanLin
        (realRectToCMatrix A) (realVecToEuclidean xr)
    simpa [sigma, C, i, realVecToEuclidean_norm,
      realRectToCMatrix_euclideanLin_realVecToEuclidean_norm] using h
  have hlower_im :
      sigma * vecNorm2 xim ≤ vecNorm2 (rectMatMulVec A xim) := by
    have h :=
      complexMatrixSingularValue_last_mul_norm_le_norm_euclideanLin
        (realRectToCMatrix A) (realVecToEuclidean xim)
    simpa [sigma, C, i, realVecToEuclidean_norm,
      realRectToCMatrix_euclideanLin_realVecToEuclidean_norm] using h
  have hsq_re :
      sigma ^ 2 * vecNorm2 xr ^ 2 ≤
        vecNorm2 (rectMatMulVec A xr) ^ 2 := by
    have hsq :=
      (sq_le_sq₀
        (mul_nonneg hsigma_nonneg (vecNorm2_nonneg xr))
        (vecNorm2_nonneg (rectMatMulVec A xr))).mpr hlower_re
    calc
      sigma ^ 2 * vecNorm2 xr ^ 2 = (sigma * vecNorm2 xr) ^ 2 := by
        ring
      _ ≤ vecNorm2 (rectMatMulVec A xr) ^ 2 := hsq
  have hsq_im :
      sigma ^ 2 * vecNorm2 xim ^ 2 ≤
        vecNorm2 (rectMatMulVec A xim) ^ 2 := by
    have hsq :=
      (sq_le_sq₀
        (mul_nonneg hsigma_nonneg (vecNorm2_nonneg xim))
        (vecNorm2_nonneg (rectMatMulVec A xim))).mpr hlower_im
    calc
      sigma ^ 2 * vecNorm2 xim ^ 2 = (sigma * vecNorm2 xim) ^ 2 := by
        ring
      _ ≤ vecNorm2 (rectMatMulVec A xim) ^ 2 := hsq
  have hxr_eq :
      vecNorm2 (rectMatMulVec A xr) ^ 2 =
        sigma ^ 2 * vecNorm2 xr ^ 2 := by
    linarith
  have hxim_eq :
      vecNorm2 (rectMatMulVec A xim) ^ 2 =
        sigma ^ 2 * vecNorm2 xim ^ 2 := by
    linarith
  by_cases hxr_ne : xr ≠ 0
  · refine ⟨xr, hxr_ne, ?_⟩
    rw [← vecNorm2_sq, ← vecNorm2_sq]
    exact hxr_eq
  · have hxr_zero : xr = 0 := not_not.mp hxr_ne
    have hxim_ne : xim ≠ 0 := by
      intro hxim_zero
      have hnorm_zero : ‖z‖ ^ 2 = 0 := by
        calc
          ‖z‖ ^ 2 = vecNorm2 xr ^ 2 + vecNorm2 xim ^ 2 := by
            simpa [xr, xim] using euclidean_norm_sq_re_im z
          _ = 0 := by
            rw [hxr_zero, hxim_zero]
            change
              vecNorm2 (fun _i : Fin (k + 1) => 0) ^ 2 +
                vecNorm2 (fun _i : Fin (k + 1) => 0) ^ 2 = 0
            rw [vecNorm2_zero]
            norm_num
      have hnorm_one : ‖z‖ ^ 2 = 1 := by
        rw [complexMatrixGramEigenvectorBasis_norm C i]
        norm_num
      linarith
    refine ⟨xim, hxim_ne, ?_⟩
    rw [← vecNorm2_sq, ← vecNorm2_sq]
    exact hxim_eq

/-- A complex Euclidean operator-norm bound for the complexified matrix gives a
    real rectangular operator-bound certificate. -/
theorem rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le {m n : Nat}
    (A : Fin m -> Fin n -> Real) {c : Real}
    (hOp : complexMatrixOp2 (realRectToCMatrix A) <= c) :
    rectOpNorm2Le A c := by
  intro x
  have hlin :=
    ContinuousLinearMap.le_opNorm
      ((complexMatrixEuclideanLin (realRectToCMatrix A)).toContinuousLinearMap)
      (realVecToEuclidean x)
  calc
    vecNorm2 (rectMatMulVec A x)
        = ‖complexMatrixEuclideanLin (realRectToCMatrix A) (realVecToEuclidean x)‖ := by
          rw [realRectToCMatrix_euclideanLin_realVecToEuclidean_norm]
    _ <= complexMatrixOp2 (realRectToCMatrix A) * ‖realVecToEuclidean x‖ := by
          rw [complexMatrixOp2_eq_norm_euclideanLin]
          exact hlin
    _ = complexMatrixOp2 (realRectToCMatrix A) * vecNorm2 x := by
          rw [realVecToEuclidean_norm]
    _ <= c * vecNorm2 x := by
          exact mul_le_mul_of_nonneg_right hOp (vecNorm2_nonneg x)

/-- Transfer a rectangular real operator-2 bound across equality of exact
    complexified Euclidean operator norms. -/
theorem rectOpNorm2Le_of_complexMatrixOp2_eq_of_rectOpNorm2Le {m n : Nat}
    (A B : Fin m -> Fin n -> Real) {c : Real}
    (hc : 0 <= c)
    (hEq :
      complexMatrixOp2 (realRectToCMatrix A) =
        complexMatrixOp2 (realRectToCMatrix B))
    (hB : rectOpNorm2Le B c) :
    rectOpNorm2Le A c := by
  have hBop :
      complexMatrixOp2 (realRectToCMatrix B) <= c :=
    complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le B hc hB
  have hAop :
      complexMatrixOp2 (realRectToCMatrix A) <= c := by
    simpa [hEq] using hBop
  exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le A hAop

/-- A square real operator-bound certificate bounds the exact Euclidean
    operator norm of its complexification. -/
theorem complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le {n : Nat}
    (A : Fin n -> Fin n -> Real) {c : Real}
    (hc : 0 <= c) (hA : opNorm2Le A c) :
    complexMatrixOp2 (realRectToCMatrix A) <= c :=
  complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le A hc
    (opNorm2Le_to_rectOpNorm2Le hA)

/-- The exact Euclidean operator norm of a square real matrix's
    complexification is itself an admissible real operator-bound certificate. -/
theorem opNorm2Le_complexMatrixOp2_realRectToCMatrix {n : Nat}
    (A : Fin n -> Fin n -> Real) :
    opNorm2Le A (complexMatrixOp2 (realRectToCMatrix A)) := by
  have hrect :
      rectOpNorm2Le A (complexMatrixOp2 (realRectToCMatrix A)) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le A le_rfl
  intro x
  simpa [opNorm2Le, rectOpNorm2Le, matMulVec, rectMatMulVec] using hrect x

theorem realRectToCMatrix_absMatrixRect {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    realRectToCMatrix (absMatrixRect A) =
      complexAbsMatrix (realRectToCMatrix A) := by
  ext i j
  simp [realRectToCMatrix, absMatrixRect, complexAbsMatrix]
end NumStability
