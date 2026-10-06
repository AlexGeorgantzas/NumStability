/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.UnitaryGroup
import NumStability.Algorithms.QR.Higham19WYApplicationClosure

namespace NumStability

open scoped BigOperators RealInnerProductSpace

noncomputable section

/-!
# Higham Chapter 19: the Sun--Bischof basis--kernel representation

Higham's notes on printed page 376 cite Sun and Bischof's exact theorem that
every real orthogonal matrix has a representation

`Q = I - Y S Yᵀ`

with a triangular kernel `S`.  The existing compact-WY development starts
from an already supplied sequence of reflectors; this file discharges the
missing universal existence step.  The proof has two independent pieces:

* finite-dimensional Cartan--Dieudonne gives at most `n` hyperplane
  reflections for an `n x n` orthogonal matrix;
* an explicit block recurrence converts any such ordered list of reflections
  into one basis--kernel table with a lower-triangular kernel.

No factorization, reflector list, basis, or kernel is assumed by the public
source theorem below.
-/

abbrev Ch19SBEuclidean (n : Nat) := EuclideanSpace Real (Fin n)

/-- Squared Euclidean coordinate norm, kept as an explicit finite sum for the
rank-one reflector algebra. -/
def ch19SBVecNormSq {n : Nat} (v : Ch19SBEuclidean n) : Real :=
  ∑ i : Fin n, v i * v i

/-- The coefficient of the hyperplane reflection normal to `v`.  At `v=0`
the corresponding reflection is the identity, so the zero coefficient is the
correct total convention. -/
def ch19SBReflectionBeta {n : Nat} (v : Ch19SBEuclidean n) : Real :=
  if ch19SBVecNormSq v = 0 then 0 else 2 / ch19SBVecNormSq v

/-- Matrix of the hyperplane reflection normal to `v`. -/
def ch19SBReflectionMatrix {n : Nat} (v : Ch19SBEuclidean n) :
    Matrix (Fin n) (Fin n) Real :=
  fun i j => idMatrix n i j - ch19SBReflectionBeta v * v i * v j

/-- Append a column to a finite rectangular matrix. -/
def ch19SBAppendColumn {n k : Nat}
    (v : Ch19SBEuclidean n) (Y : Matrix (Fin n) (Fin k) Real) :
    Matrix (Fin n) (Fin (k + 1)) Real :=
  fun i j => Fin.lastCases (v i) (fun q => Y i q) j

@[simp] theorem ch19SBAppendColumn_castSucc {n k : Nat}
    (v : Ch19SBEuclidean n) (Y : Matrix (Fin n) (Fin k) Real)
    (i : Fin n) (j : Fin k) :
    ch19SBAppendColumn v Y i j.castSucc = Y i j := by
  simp [ch19SBAppendColumn]

@[simp] theorem ch19SBAppendColumn_last {n k : Nat}
    (v : Ch19SBEuclidean n) (Y : Matrix (Fin n) (Fin k) Real)
    (i : Fin n) :
    ch19SBAppendColumn v Y i (Fin.last k) = v i := by
  simp [ch19SBAppendColumn]

/-- A local, unambiguous lower-triangular predicate.  Sun--Bischof allow
either triangular orientation; the append-on-the-right recurrence below
naturally produces the lower orientation. -/
def Ch19SBIsLowerTriangular {k : Nat}
    (S : Matrix (Fin k) (Fin k) Real) : Prop :=
  ∀ i j, i.val < j.val → S i j = 0

/-- Append the kernel row/column for left multiplication by the reflection
`I - beta v vᵀ`.  If the old factor is `I - Y S Yᵀ`, the new lower-left row is
`-beta (vᵀ Y) S`, the upper-right column is zero, and the new diagonal entry
is `beta`. -/
def ch19SBAppendKernel {n k : Nat}
    (v : Ch19SBEuclidean n) (Y : Matrix (Fin n) (Fin k) Real)
    (S : Matrix (Fin k) (Fin k) Real) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) Real :=
  fun i => Fin.lastCases
    (fun j => Fin.lastCases (ch19SBReflectionBeta v)
      (fun q => -ch19SBReflectionBeta v *
        (∑ p : Fin k, (∑ a : Fin n, v a * Y a p) * S p q)) j)
    (fun p j => Fin.lastCases 0 (fun q => S p q) j) i

@[simp] theorem ch19SBAppendKernel_old_old {n k : Nat}
    (v : Ch19SBEuclidean n) (Y : Matrix (Fin n) (Fin k) Real)
    (S : Matrix (Fin k) (Fin k) Real) (p q : Fin k) :
    ch19SBAppendKernel v Y S p.castSucc q.castSucc = S p q := by
  simp [ch19SBAppendKernel]

@[simp] theorem ch19SBAppendKernel_old_last {n k : Nat}
    (v : Ch19SBEuclidean n) (Y : Matrix (Fin n) (Fin k) Real)
    (S : Matrix (Fin k) (Fin k) Real) (p : Fin k) :
    ch19SBAppendKernel v Y S p.castSucc (Fin.last k) = 0 := by
  simp [ch19SBAppendKernel]

@[simp] theorem ch19SBAppendKernel_last_old {n k : Nat}
    (v : Ch19SBEuclidean n) (Y : Matrix (Fin n) (Fin k) Real)
    (S : Matrix (Fin k) (Fin k) Real) (q : Fin k) :
    ch19SBAppendKernel v Y S (Fin.last k) q.castSucc =
      -ch19SBReflectionBeta v *
        (∑ p : Fin k, (∑ a : Fin n, v a * Y a p) * S p q) := by
  simp [ch19SBAppendKernel]

@[simp] theorem ch19SBAppendKernel_last_last {n k : Nat}
    (v : Ch19SBEuclidean n) (Y : Matrix (Fin n) (Fin k) Real)
    (S : Matrix (Fin k) (Fin k) Real) :
    ch19SBAppendKernel v Y S (Fin.last k) (Fin.last k) =
      ch19SBReflectionBeta v := by
  simp [ch19SBAppendKernel]

theorem ch19SBAppendKernel_lower {n k : Nat}
    (v : Ch19SBEuclidean n) (Y : Matrix (Fin n) (Fin k) Real)
    (S : Matrix (Fin k) (Fin k) Real)
    (hS : Ch19SBIsLowerTriangular S) :
    Ch19SBIsLowerTriangular (ch19SBAppendKernel v Y S) := by
  intro i j hij
  refine Fin.lastCases (motive := fun i => i.val < j.val →
      ch19SBAppendKernel v Y S i j = 0) ?_ (fun p hp => ?_) i hij
  · intro h
    have hj := j.isLt
    simp at h
    omega
  · refine Fin.lastCases (motive := fun j => p.castSucc.val < j.val →
        ch19SBAppendKernel v Y S p.castSucc j = 0)
      ?_ (fun q hpq => ?_) j hp
    · simp [ch19SBAppendKernel]
    · simp only [ch19SBAppendKernel_old_old]
      exact hS p q (by simpa using hpq)

/-- The matrix represented by basis `Y` and kernel `S`. -/
def ch19SBBasisKernelMatrix {n k : Nat}
    (Y : Matrix (Fin n) (Fin k) Real)
    (S : Matrix (Fin k) (Fin k) Real) :
    Matrix (Fin n) (Fin n) Real :=
  fun i j => idMatrix n i j -
    rectMatMul (rectMatMul Y S) (finiteTranspose Y) i j

/-- Algebraic heart of the append recurrence. -/
theorem ch19SBAppendKernel_product {n k : Nat}
    (v : Ch19SBEuclidean n) (Y : Matrix (Fin n) (Fin k) Real)
    (S : Matrix (Fin k) (Fin k) Real) (i j : Fin n) :
    rectMatMul
        (rectMatMul (ch19SBAppendColumn v Y) (ch19SBAppendKernel v Y S))
        (finiteTranspose (ch19SBAppendColumn v Y)) i j =
      rectMatMul (rectMatMul Y S) (finiteTranspose Y) i j +
        ch19SBReflectionBeta v * v i * v j -
        ch19SBReflectionBeta v * v i *
          (∑ a : Fin n, v a *
            rectMatMul (rectMatMul Y S) (finiteTranspose Y) a j) := by
  classical
  let b := ch19SBReflectionBeta v
  let P : Matrix (Fin n) (Fin n) Real :=
    rectMatMul (rectMatMul Y S) (finiteTranspose Y)
  have hcontract :
      (∑ q : Fin k,
          (∑ p : Fin k, (∑ a : Fin n, v a * Y a p) * S p q) * Y j q) =
        ∑ a : Fin n, v a * P a j := by
    simp only [P, rectMatMul, finiteTranspose]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    change
      (∑ q : Fin k, ∑ p : Fin k, ∑ a : Fin n,
        v a * Y a p * S p q * Y j q) =
      ∑ a : Fin n, ∑ q : Fin k, ∑ p : Fin k,
        v a * (Y a p * S p q * Y j q)
    calc
      (∑ q : Fin k, ∑ p : Fin k, ∑ a : Fin n,
          v a * Y a p * S p q * Y j q) =
          ∑ p : Fin k, ∑ q : Fin k, ∑ a : Fin n,
            v a * Y a p * S p q * Y j q := Finset.sum_comm
      _ = ∑ p : Fin k, ∑ a : Fin n, ∑ q : Fin k,
            v a * Y a p * S p q * Y j q := by
          apply Finset.sum_congr rfl
          intro p _
          exact Finset.sum_comm
      _ = ∑ a : Fin n, ∑ p : Fin k, ∑ q : Fin k,
            v a * Y a p * S p q * Y j q := Finset.sum_comm
      _ = ∑ a : Fin n, ∑ q : Fin k, ∑ p : Fin k,
            v a * Y a p * S p q * Y j q := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
      _ = ∑ a : Fin n, ∑ q : Fin k, ∑ p : Fin k,
            v a * (Y a p * S p q * Y j q) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro q _
          apply Finset.sum_congr rfl
          intro p _
          ring
  unfold rectMatMul finiteTranspose
  rw [Fin.sum_univ_castSucc]
  simp only [ch19SBAppendColumn_castSucc, ch19SBAppendColumn_last]
  simp_rw [Fin.sum_univ_castSucc]
  simp only [ch19SBAppendColumn_castSucc, ch19SBAppendColumn_last,
    ch19SBAppendKernel_old_old, ch19SBAppendKernel_old_last,
    ch19SBAppendKernel_last_old, ch19SBAppendKernel_last_last]
  change
    (∑ q : Fin k,
        ((∑ p : Fin k, Y i p * S p q) +
          v i * (-b *
            ∑ p : Fin k, (∑ a : Fin n, v a * Y a p) * S p q)) * Y j q) +
        ((∑ p : Fin k, Y i p * 0) + v i * b) * v j =
      P i j + b * v i * v j - b * v i * (∑ a : Fin n, v a * P a j)
  rw [show (∑ p : Fin k, Y i p * 0) = 0 by simp]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hP :
      (∑ q : Fin k, (∑ p : Fin k, Y i p * S p q) * Y j q) = P i j := by
    rfl
  rw [hP]
  rw [show
      (∑ q : Fin k,
        (v i * (-b *
          ∑ p : Fin k, (∑ a : Fin n, v a * Y a p) * S p q)) * Y j q) =
        -b * v i *
          (∑ q : Fin k,
            (∑ p : Fin k, (∑ a : Fin n, v a * Y a p) * S p q) * Y j q) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring]
  rw [hcontract]
  ring

/-- Appending the displayed basis column and kernel row represents left
multiplication by the corresponding reflection. -/
theorem ch19SBBasisKernel_append {n k : Nat}
    (v : Ch19SBEuclidean n) (Y : Matrix (Fin n) (Fin k) Real)
    (S : Matrix (Fin k) (Fin k) Real) :
    rectMatMul (ch19SBReflectionMatrix v) (ch19SBBasisKernelMatrix Y S) =
      ch19SBBasisKernelMatrix
        (ch19SBAppendColumn v Y) (ch19SBAppendKernel v Y S) := by
  classical
  ext i j
  let b := ch19SBReflectionBeta v
  let P : Matrix (Fin n) (Fin n) Real :=
    rectMatMul (rectMatMul Y S) (finiteTranspose Y)
  have hleft :
      rectMatMul (ch19SBReflectionMatrix v) (ch19SBBasisKernelMatrix Y S) i j =
        idMatrix n i j - P i j - b * v i * v j +
          b * v i * (∑ a : Fin n, v a * P a j) := by
    unfold rectMatMul ch19SBReflectionMatrix ch19SBBasisKernelMatrix
    simp_rw [sub_mul, mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
    have hidLeft :
        (∑ a : Fin n, idMatrix n i a * idMatrix n a j) = idMatrix n i j := by
      simpa [rectMatMul] using congrFun (congrFun (rectMatMul_id_left (idMatrix n)) i) j
    have hidP :
        (∑ a : Fin n, idMatrix n i a * P a j) = P i j := by
      simpa [rectMatMul] using congrFun (congrFun (rectMatMul_id_left P) i) j
    have vvId :
        (∑ a : Fin n, (b * v i * v a) * idMatrix n a j) = b * v i * v j := by
      simp [idMatrix]
    rw [hidLeft, hidP, vvId]
    have hcross :
        (∑ a : Fin n, (b * v i * v a) * P a j) =
          b * v i * (∑ a : Fin n, v a * P a j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hcross]
    ring
  rw [hleft]
  unfold ch19SBBasisKernelMatrix
  rw [ch19SBAppendKernel_product]
  ring

/-! ## Any finite reflection product has a triangular basis--kernel table -/

def ch19SBMatrixListProduct {n : Nat} :
    List (Matrix (Fin n) (Fin n) Real) → Matrix (Fin n) (Fin n) Real
  | [] => idMatrix n
  | A :: As => rectMatMul A (ch19SBMatrixListProduct As)

@[simp] theorem ch19SBMatrixListProduct_nil {n : Nat} :
    ch19SBMatrixListProduct ([] : List (Matrix (Fin n) (Fin n) Real)) =
      idMatrix n := rfl

@[simp] theorem ch19SBMatrixListProduct_cons {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real)
    (As : List (Matrix (Fin n) (Fin n) Real)) :
    ch19SBMatrixListProduct (A :: As) =
      rectMatMul A (ch19SBMatrixListProduct As) := rfl

/-- Explicit compact representation for every ordered finite list of
hyperplane-reflection normals.  The number of basis columns is exactly the
list length and the produced kernel is lower triangular. -/
theorem ch19SB_reflectionList_basisKernel {n : Nat} :
    ∀ l : List (Ch19SBEuclidean n),
      ∃ (Y : Matrix (Fin n) (Fin l.length) Real)
        (S : Matrix (Fin l.length) (Fin l.length) Real),
        Ch19SBIsLowerTriangular S ∧
        ch19SBMatrixListProduct (l.map ch19SBReflectionMatrix) =
          ch19SBBasisKernelMatrix Y S := by
  intro l
  induction l with
  | nil =>
      let Y : Matrix (Fin n) (Fin 0) Real := fun _ j => Fin.elim0 j
      let S : Matrix (Fin 0) (Fin 0) Real := fun i => Fin.elim0 i
      refine ⟨Y, S, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · ext i j
        simp [ch19SBBasisKernelMatrix, rectMatMul, Y, S]
  | cons v l ih =>
      obtain ⟨Y, S, hS, hrepr⟩ := ih
      let Ynew : Matrix (Fin n) (Fin (l.length + 1)) Real :=
        ch19SBAppendColumn v Y
      let Snew : Matrix (Fin (l.length + 1)) (Fin (l.length + 1)) Real :=
        ch19SBAppendKernel v Y S
      refine ⟨Ynew, Snew, ch19SBAppendKernel_lower v Y S hS, ?_⟩
      change rectMatMul (ch19SBReflectionMatrix v)
          (ch19SBMatrixListProduct (l.map ch19SBReflectionMatrix)) =
        ch19SBBasisKernelMatrix Ynew Snew
      rw [hrepr]
      exact ch19SBBasisKernel_append v Y S

/-! ## Coordinate matrix of Mathlib's hyperplane reflection -/

theorem ch19SBVecNormSq_eq_norm_sq {n : Nat} (v : Ch19SBEuclidean n) :
    ch19SBVecNormSq v = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp [pow_two]

theorem ch19SBReflectionBeta_eq {n : Nat} (v : Ch19SBEuclidean n) :
    ch19SBReflectionBeta v = if v = 0 then 0 else 2 / ‖v‖ ^ 2 := by
  by_cases hv : v = 0
  · subst v
    simp [ch19SBReflectionBeta, ch19SBVecNormSq]
  · rw [ch19SBReflectionBeta, ch19SBVecNormSq_eq_norm_sq]
    simp [hv, norm_ne_zero_iff.mpr hv]

lemma ch19SB_real_inner_eq_mul (a b : Real) : inner Real a b = a * b := by
  calc
    inner Real a b = inner Real (a • (1 : Real)) (b • (1 : Real)) := by simp
    _ = a * (b * inner Real (1 : Real) (1 : Real)) := by
      rw [real_inner_smul_left, real_inner_smul_right]
    _ = a * b := by
      rw [real_inner_self_eq_norm_sq]
      norm_num

/-- The explicit rank-one matrix above acts exactly as Mathlib's reflection
in the hyperplane perpendicular to `v`. -/
theorem ch19SBReflectionMatrix_toEuclideanLin {n : Nat}
    (v : Ch19SBEuclidean n) (x : Ch19SBEuclidean n) :
    Matrix.toEuclideanLin (ch19SBReflectionMatrix v) x =
      ((Real ∙ v)ᗮ).reflection x := by
  classical
  rw [Submodule.reflection_orthogonal_apply]
  rw [Submodule.reflection_singleton_apply]
  ext i
  simp only [PiLp.neg_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [show
      (Matrix.toEuclideanLin (ch19SBReflectionMatrix v) x) i =
        ∑ j : Fin n,
          (idMatrix n i j - ch19SBReflectionBeta v * v i * v j) * x j by
      rfl]
  rw [ch19SBReflectionBeta_eq]
  by_cases hv : v = 0
  · subst v
    simp [idMatrix]
  · rw [if_neg hv]
    have hinner : inner Real v x =
        ∑ j : Fin n, v j * x j := by
      simp only [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro j _
      exact ch19SB_real_inner_eq_mul (v j) (x j)
    rw [hinner]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    have hid : (∑ j : Fin n, idMatrix n i j * x j) = x i := by
      simp [idMatrix]
    rw [hid]
    have hsum :
        (∑ j : Fin n, (2 / ‖v‖ ^ 2 * v i * v j) * x j) =
          (2 / ‖v‖ ^ 2 * v i) * (∑ j : Fin n, v j * x j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    rw [two_smul]
    simp only [RCLike.ofReal_alg, smul_eq_mul, mul_one]
    ring

/-! ## Cartan--Dieudonne and the universal source theorem -/

/-- Bundle the repository's two-sided `IsOrthogonal` certificate as Mathlib's
orthogonal-group element. -/
noncomputable def ch19SBOrthogonalGroup {n : Nat}
    (Q : Matrix (Fin n) (Fin n) Real) (hQ : IsOrthogonal n Q) :
    Matrix.orthogonalGroup (Fin n) Real :=
  ⟨Q, by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, matTranspose,
      Matrix.one_apply, idMatrix] using hQ.right_inv i j⟩

/-- Ordinary Euclidean linear equivalence induced by an orthogonal matrix. -/
noncomputable def ch19SBOrthogonalLinearEquiv {n : Nat}
    (Q : Matrix (Fin n) (Fin n) Real) (hQ : IsOrthogonal n Q) :
    Ch19SBEuclidean n ≃ₗ[Real] Ch19SBEuclidean n :=
  (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin n => Real)).toLinearEquiv |>.trans
    (Matrix.UnitaryGroup.toLinearEquiv (ch19SBOrthogonalGroup Q hQ)) |>.trans
      (PiLp.continuousLinearEquiv 2 Real
        (fun _ : Fin n => Real)).symm.toLinearEquiv

@[simp] theorem ch19SBOrthogonalLinearEquiv_apply {n : Nat}
    (Q : Matrix (Fin n) (Fin n) Real) (hQ : IsOrthogonal n Q)
    (x : Ch19SBEuclidean n) :
    ch19SBOrthogonalLinearEquiv Q hQ x = Matrix.toEuclideanLin Q x := by
  rfl

/-- The same action, bundled as a surjective linear isometry so that the
finite-dimensional Cartan--Dieudonne theorem applies. -/
noncomputable def ch19SBOrthogonalIsometry {n : Nat}
    (Q : Matrix (Fin n) (Fin n) Real) (hQ : IsOrthogonal n Q) :
    Ch19SBEuclidean n ≃ₗᵢ[Real] Ch19SBEuclidean n :=
  (ch19SBOrthogonalLinearEquiv Q hQ).isometryOfInner (by
    intro x y
    let A : Ch19SBEuclidean n →ₗ[Real] Ch19SBEuclidean n :=
      Matrix.toEuclideanLin Q
    change inner Real (A x) (A y) = inner Real x y
    have hcomp : A.adjoint.comp A = LinearMap.id := by
      rw [show A.adjoint = Matrix.toEuclideanLin Q.conjTranspose by
        simpa [A] using
          (Matrix.toEuclideanLin_conjTranspose_eq_adjoint Q).symm]
      rw [← Matrix.toLpLin_mul_same]
      have hQtQ : Q.conjTranspose * Q = 1 := by
        have hm := (ch19SBOrthogonalGroup Q hQ).property
        simpa only [Matrix.star_eq_conjTranspose] using
          (Matrix.UnitaryGroup.star_mul_self (ch19SBOrthogonalGroup Q hQ))
      rw [hQtQ, Matrix.toLpLin_one]
    calc
      inner Real (A x) (A y) = inner Real x (A.adjoint (A y)) :=
        (LinearMap.adjoint_inner_right A x (A y)).symm
      _ = inner Real x y := by
        rw [← LinearMap.comp_apply, hcomp, LinearMap.id_apply])

@[simp] theorem ch19SBOrthogonalIsometry_apply {n : Nat}
    (Q : Matrix (Fin n) (Fin n) Real) (hQ : IsOrthogonal n Q)
    (x : Ch19SBEuclidean n) :
    ch19SBOrthogonalIsometry Q hQ x = Matrix.toEuclideanLin Q x := by
  rfl

def ch19SBReflectionIsometry {n : Nat} (v : Ch19SBEuclidean n) :
    Ch19SBEuclidean n ≃ₗᵢ[Real] Ch19SBEuclidean n :=
  ((Real ∙ v)ᗮ).reflection

theorem ch19SB_toEuclideanLin_rectMatMul {n : Nat}
    (A B : Matrix (Fin n) (Fin n) Real) (x : Ch19SBEuclidean n) :
    Matrix.toEuclideanLin (rectMatMul A B) x =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) := by
  exact LinearMap.congr_fun (Matrix.toLpLin_mul_same 2 A B) x

/-- Coordinate action of the matrix-list product agrees with the group
product of the corresponding Mathlib reflections. -/
theorem ch19SBMatrixListProduct_reflection_action {n : Nat}
    (l : List (Ch19SBEuclidean n)) (x : Ch19SBEuclidean n) :
    Matrix.toEuclideanLin
        (ch19SBMatrixListProduct (l.map ch19SBReflectionMatrix)) x =
      (l.map ch19SBReflectionIsometry).prod x := by
  induction l generalizing x with
  | nil =>
      change Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) Real) x = x
      rw [Matrix.toLpLin_one]
      rfl
  | cons v l ih =>
      simp only [List.map_cons, ch19SBMatrixListProduct_cons, List.prod_cons]
      rw [ch19SB_toEuclideanLin_rectMatMul]
      rw [ch19SBReflectionMatrix_toEuclideanLin]
      change ch19SBReflectionIsometry v
          (Matrix.toEuclideanLin
            (ch19SBMatrixListProduct (List.map ch19SBReflectionMatrix l)) x) =
        ch19SBReflectionIsometry v
          ((List.map ch19SBReflectionIsometry l).prod x)
      rw [ih]

/-- **Sun--Bischof (1995), as cited by Higham on printed page 376.**

Every real `n x n` orthogonal matrix is `I - Y S Yᵀ` for a basis with at
most `n` columns and a triangular kernel.  The theorem constructs all data
from `Q` and its orthogonality proof; it assumes no reflector factorization or
basis--kernel certificate. -/
theorem higham19_sun_bischof_triangular_basisKernel {n : Nat}
    (Q : Matrix (Fin n) (Fin n) Real) (hQ : IsOrthogonal n Q) :
    ∃ k : Nat, k ≤ n ∧
      ∃ (Y : Matrix (Fin n) (Fin k) Real)
        (S : Matrix (Fin k) (Fin k) Real),
        Ch19SBIsLowerTriangular S ∧
        Q = ch19SBBasisKernelMatrix Y S := by
  let U := ch19SBOrthogonalIsometry Q hQ
  obtain ⟨l, hl, hU⟩ := U.reflections_generate_dim
  dsimp [U] at hU
  have hl_n : l.length ≤ n := by
    simpa [Ch19SBEuclidean] using hl
  have hQproduct :
      Q = ch19SBMatrixListProduct (l.map ch19SBReflectionMatrix) := by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro x
    rw [← ch19SBOrthogonalIsometry_apply Q hQ x]
    rw [hU]
    change (l.map ch19SBReflectionIsometry).prod x =
      Matrix.toEuclideanLin
        (ch19SBMatrixListProduct (l.map ch19SBReflectionMatrix)) x
    exact (ch19SBMatrixListProduct_reflection_action l x).symm
  obtain ⟨Y, S, hS, hrepr⟩ := ch19SB_reflectionList_basisKernel l
  refine ⟨l.length, hl_n, Y, S, hS, ?_⟩
  rw [hQproduct, hrepr]

/-- Entrywise source spelling of the same result: `Q_ij = δ_ij -
(Y S Yᵀ)_ij`. -/
theorem higham19_sun_bischof_triangular_YSYt {n : Nat}
    (Q : Matrix (Fin n) (Fin n) Real) (hQ : IsOrthogonal n Q) :
    ∃ k : Nat, k ≤ n ∧
      ∃ (Y : Matrix (Fin n) (Fin k) Real)
        (S : Matrix (Fin k) (Fin k) Real),
        Ch19SBIsLowerTriangular S ∧
        ∀ i j, Q i j = idMatrix n i j -
          rectMatMul (rectMatMul Y S) (finiteTranspose Y) i j := by
  obtain ⟨k, hk, Y, S, hS, hrepr⟩ :=
    higham19_sun_bischof_triangular_basisKernel Q hQ
  refine ⟨k, hk, Y, S, hS, ?_⟩
  intro i j
  exact congrFun (congrFun hrepr i) j

end

end NumStability
