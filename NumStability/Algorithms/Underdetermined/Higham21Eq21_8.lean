-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- The Euclidean componentwise perturbation bound in equation (21.8).

import NumStability.Algorithms.Underdetermined.Higham21PerturbationRadius
import NumStability.Source.Higham.Chapter21.RowScalingInvariance

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- The source specialization `E = |A| Hadamard H` used in (21.8). -/
noncomputable def higham21Eq21_8HadamardEnvelope {m n : Nat}
    (A H : Fin m -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  fun i j => |A i j| * H i j

/-- The Euclidean operator norm of the nonnegative Hadamard factor `H`. -/
noncomputable def higham21Eq21_8HNorm2 {m n : Nat}
    (H : Fin m -> Fin n -> Real) : Real :=
  complexMatrixOp2 (realRectToCMatrix H)

/-- The natural-number dimension factor printed in (21.8). -/
def higham21Eq21_8DimensionFactorNat (m n : Nat) : Nat :=
  Nat.min 3 (n - m + 2)

/-- The real scalar corresponding to the dimension factor in (21.8). -/
def higham21Eq21_8DimensionFactor (m n : Nat) : Real :=
  (higham21Eq21_8DimensionFactorNat m n : Real)

@[simp] theorem higham21Eq21_8DimensionFactor_square (m : Nat) :
    higham21Eq21_8DimensionFactor m m = 2 := by
  simp [higham21Eq21_8DimensionFactor,
    higham21Eq21_8DimensionFactorNat]

theorem higham21Eq21_8DimensionFactor_of_lt {m n : Nat} (hmn : m < n) :
    higham21Eq21_8DimensionFactor m n = 3 := by
  have hthree : 3 <= n - m + 2 := by omega
  simp [higham21Eq21_8DimensionFactor,
    higham21Eq21_8DimensionFactorNat, Nat.min_eq_left hthree]

theorem higham21Eq21_8HNorm2_nonneg {m n : Nat}
    (H : Fin m -> Fin n -> Real) :
    0 <= higham21Eq21_8HNorm2 H :=
  complexMatrixOp2_nonneg _

/-- Every nonnegative entry of `H` is bounded by its Euclidean operator norm. -/
theorem higham21_eq21_8_H_entry_le_norm2 {m n : Nat}
    (H : Fin m -> Fin n -> Real)
    (hH : forall i j, 0 <= H i j) (i : Fin m) (j : Fin n) :
    H i j <= higham21Eq21_8HNorm2 H := by
  have hcoord :=
    complexMatrixEntrywiseMaxNorm_coord_le (realRectToCMatrix H) i j
  have hmax :=
    complexMatrixEntrywiseMaxNorm_le_op2 (realRectToCMatrix H)
  have habs : |H i j| <= complexMatrixOp2 (realRectToCMatrix H) := by
    calc
      |H i j| = norm (realRectToCMatrix H i j) := by
        simp [realRectToCMatrix, Complex.norm_real, Real.norm_eq_abs]
      _ <= complexMatrixEntrywiseMaxNorm (realRectToCMatrix H) := hcoord
      _ <= complexMatrixOp2 (realRectToCMatrix H) := hmax
  simpa [higham21Eq21_8HNorm2, abs_of_nonneg (hH i j)] using habs

/-- The null-space term in the source first-order formula (21.7), with a
    supplied Moore--Penrose table. -/
noncomputable def higham21Eq21_8NullspaceTermWith {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (DeltaA : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    Fin n -> Real :=
  let x := rectMatMulVec Aplus b
  let z := rectTransposeMulVec Aplus x
  let w := rectTransposeMulVec DeltaA z
  fun j => w j - rectMatMulVec Aplus (rectMatMulVec A w) j

/-- The pseudoinverse-range data term in the source first-order formula
    (21.7), with a supplied Moore--Penrose table. -/
noncomputable def higham21Eq21_8DataTermWith {m n : Nat}
    (Aplus : Fin n -> Fin m -> Real)
    (DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) : Fin n -> Real :=
  let x := rectMatMulVec Aplus b
  rectMatMulVec Aplus
    (fun i => Deltab i - rectMatMulVec DeltaA x i)

/-- The source first-order vector in (21.7), retaining its two printed terms. -/
noncomputable def higham21Eq21_8FirstOrderWith {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (DeltaA : Fin m -> Fin n -> Real) (b Deltab : Fin m -> Real) :
    Fin n -> Real :=
  fun j =>
    higham21Eq21_8NullspaceTermWith A Aplus DeltaA b j +
      higham21Eq21_8DataTermWith Aplus DeltaA b Deltab j

/-- The Euclidean two-term first-order coefficient used to obtain (21.8). -/
noncomputable def higham21Eq21_8FirstOrderTwoTermCoefficientWith {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (DeltaA : Fin m -> Fin n -> Real) (b Deltab : Fin m -> Real) : Real :=
  vecNorm2 (higham21Eq21_8NullspaceTermWith A Aplus DeltaA b) +
    vecNorm2 (higham21Eq21_8DataTermWith Aplus DeltaA b Deltab)

/-- The source first-order vector is bounded by its two-term coefficient. -/
theorem higham21_eq21_8_firstOrder_norm_le_twoTerm_coefficient_with
    {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (DeltaA : Fin m -> Fin n -> Real) (b Deltab : Fin m -> Real) :
    vecNorm2 (higham21Eq21_8FirstOrderWith A Aplus DeltaA b Deltab) <=
      higham21Eq21_8FirstOrderTwoTermCoefficientWith
        A Aplus DeltaA b Deltab := by
  simpa [higham21Eq21_8FirstOrderWith,
    higham21Eq21_8FirstOrderTwoTermCoefficientWith] using
      (vecNorm2_add_le
        (higham21Eq21_8NullspaceTermWith A Aplus DeltaA b)
        (higham21Eq21_8DataTermWith Aplus DeltaA b Deltab))

/-- The supplied right inverse sends the pseudoinverse solution back to `b`. -/
theorem higham21_eq21_8_base_system_with {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (b : Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m) :
    rectMatMulVec A (rectMatMulVec Aplus b) = b := by
  calc
    rectMatMulVec A (rectMatMulVec Aplus b) =
        rectMatMulVec (rectMatMul A Aplus) b :=
      (rectMatMulVec_rectMatMul A Aplus b).symm
    _ = rectMatMulVec (idMatrix m) b := by rw [hRight]
    _ = b := rectMatMulVec_idMatrix b

/-- The product `Aplus*DeltaA` has the exact (21.8) operator bound under
    `|DeltaA| <= |A| Hadamard H`. -/
theorem higham21_eq21_8_pseudoinverse_product_rectOpNorm2Le
    {m n : Nat}
    (A DeltaA H : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (hH : forall i j, 0 <= H i j)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_8HadamardEnvelope A H i j) :
    rectOpNorm2Le (rectMatMul Aplus DeltaA)
      (higham21Eq21_8HNorm2 H * higham21Cond2With A Aplus) := by
  let C : Fin n -> Fin n -> Real :=
    rectMatMul (absMatrixRect Aplus) (absMatrixRect A)
  let h : Real := higham21Eq21_8HNorm2 H
  have hh : 0 <= h := by
    simpa [h] using higham21Eq21_8HNorm2_nonneg H
  have hC : rectOpNorm2Le C (higham21Cond2With A Aplus) := by
    simpa [C, higham21Cond2With] using
      (rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le C le_rfl)
  have hentry : forall k j,
      |rectMatMul Aplus DeltaA k j| <= h * C k j := by
    intro k j
    calc
      |rectMatMul Aplus DeltaA k j| =
          |Finset.univ.sum (fun i : Fin m => Aplus k i * DeltaA i j)| := by
            rfl
      _ <= Finset.univ.sum
          (fun i : Fin m => |Aplus k i * DeltaA i j|) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = Finset.univ.sum
          (fun i : Fin m => |Aplus k i| * |DeltaA i j|) := by
        apply Finset.sum_congr rfl
        intro i _
        exact abs_mul (Aplus k i) (DeltaA i j)
      _ <= Finset.univ.sum
          (fun i : Fin m =>
            |Aplus k i| * (|A i j| * H i j)) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hDeltaA i j) (abs_nonneg _)
      _ <= Finset.univ.sum
          (fun i : Fin m => |Aplus k i| * (|A i j| * h)) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (higham21_eq21_8_H_entry_le_norm2 H hH i j)
            (abs_nonneg _))
          (abs_nonneg _)
      _ = h * C k j := by
        simp only [C, rectMatMul, absMatrixRect]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  exact rectOpNorm2Le_of_abs_entry_le hentry
    (higham21_rectOpNorm2Le_const_mul_of_nonneg C hh hC)

/-- Transposing the source product turns
    `DeltaA^T (Aplus^T x)` into `(Aplus*DeltaA)^T x`. -/
theorem higham21_eq21_8_transpose_product_action {m n : Nat}
    (Aplus : Fin n -> Fin m -> Real)
    (DeltaA : Fin m -> Fin n -> Real) (x : Fin n -> Real) :
    rectTransposeMulVec DeltaA (rectTransposeMulVec Aplus x) =
      rectMatMulVec (finiteTranspose (rectMatMul Aplus DeltaA)) x := by
  ext j
  unfold rectTransposeMulVec rectMatMulVec rectMatMul finiteTranspose
  calc
    Finset.univ.sum (fun i : Fin m =>
        DeltaA i j * Finset.univ.sum (fun l : Fin n => Aplus l i * x l)) =
        Finset.univ.sum (fun i : Fin m =>
          Finset.univ.sum (fun l : Fin n =>
            DeltaA i j * (Aplus l i * x l))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = Finset.univ.sum (fun l : Fin n =>
        Finset.univ.sum (fun i : Fin m =>
          DeltaA i j * (Aplus l i * x l))) := by
      rw [Finset.sum_comm]
    _ = Finset.univ.sum (fun l : Fin n =>
        (Finset.univ.sum (fun i : Fin m => Aplus l i * DeltaA i j)) * x l) := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- The symmetric idempotent domain projection has a contractive residual.
    This is the `z = 0` instance of the finite projection best-approximation
    lemma; no lower bound for the projector-complement norm is needed. -/
theorem higham21_eq21_8_projection_residual_norm_le {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A))
    (w : Fin n -> Real) :
    vecNorm2
        (fun j => w j - rectMatMulVec Aplus (rectMatMulVec A w) j) <=
      vecNorm2 w := by
  let P : Fin n -> Fin n -> Real := rectMatMul Aplus A
  have hIdemEq : rectMatMul P P = P := by
    simpa [P] using
      rectMatMul_domainProjection_idempotent_of_right_inverse A Aplus hRight
  have hIdem : forall i j, finiteMatMul P P i j = P i j := by
    intro i j
    simpa [finiteMatMul, rectMatMul] using
      congrFun (congrFun hIdemEq i) j
  have hbest :=
    finiteVecNorm2_projection_residual_le_residual_to_range_of_symmetric_idempotent
      P (by simpa [P] using hSym) hIdem w (0 : Fin n -> Real)
  have hbest' :
      vecNorm2 (fun j => w j - rectMatMulVec P w j) <= vecNorm2 w := by
    simpa [finiteVecNorm2_fin, finiteMatVec, rectMatMulVec] using hbest
  have haction :
      rectMatMulVec P w = rectMatMulVec Aplus (rectMatMulVec A w) := by
    simpa [P] using rectMatMulVec_rectMatMul Aplus A w
  rw [haction] at hbest'
  exact hbest'

/-- In the square case, `A*Aplus = I` implies `Aplus*A = I`. -/
theorem higham21_eq21_8_square_left_inverse {n : Nat}
    (A Aplus : Fin n -> Fin n -> Real)
    (hRight : rectMatMul A Aplus = idMatrix n) :
    rectMatMul Aplus A = idMatrix n := by
  have hRightPred : IsRightInverse n A Aplus := by
    intro i j
    have hij := congrFun (congrFun hRight i) j
    simpa [rectMatMul, idMatrix] using hij
  have hLeftPred : IsLeftInverse n A Aplus :=
    isLeftInverse_of_isRightInverse A Aplus hRightPred
  ext i j
  simpa [rectMatMul, idMatrix] using hLeftPred i j

/-- Consequently, the null-space term in (21.7) vanishes in the square case. -/
theorem higham21_eq21_8_nullspaceTerm_eq_zero_of_square {n : Nat}
    (A Aplus DeltaA : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (hRight : rectMatMul A Aplus = idMatrix n) :
    higham21Eq21_8NullspaceTermWith A Aplus DeltaA b = 0 := by
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let z : Fin n -> Real := rectTransposeMulVec Aplus x
  let w : Fin n -> Real := rectTransposeMulVec DeltaA z
  have hLeft : rectMatMul Aplus A = idMatrix n :=
    higham21_eq21_8_square_left_inverse A Aplus hRight
  have hApply : rectMatMulVec Aplus (rectMatMulVec A w) = w := by
    calc
      rectMatMulVec Aplus (rectMatMulVec A w) =
          rectMatMulVec (rectMatMul Aplus A) w :=
        (rectMatMulVec_rectMatMul Aplus A w).symm
      _ = rectMatMulVec (idMatrix n) w := by rw [hLeft]
      _ = w := rectMatMulVec_idMatrix w
  ext j
  change w j - rectMatMulVec Aplus (rectMatMulVec A w) j = 0
  rw [hApply]
  exact sub_self (w j)

/-- The right-hand-side contribution is bounded by
    `cond2With(A,Aplus) * ||x||_2` when `|Deltab| <= |b|`. -/
theorem higham21_eq21_8_rhs_image_norm_le_cond2With {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (b Deltab : Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hDeltab : forall i, |Deltab i| <= |b i|) :
    vecNorm2 (rectMatMulVec Aplus Deltab) <=
      higham21Cond2With A Aplus * vecNorm2 (rectMatMulVec Aplus b) := by
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let C : Fin n -> Fin n -> Real :=
    rectMatMul (absMatrixRect Aplus) (absMatrixRect A)
  have hAx : rectMatMulVec A x = b := by
    simpa [x] using higham21_eq21_8_base_system_with A Aplus b hRight
  have hC : rectOpNorm2Le C (higham21Cond2With A Aplus) := by
    simpa [C, higham21Cond2With] using
      (rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le C le_rfl)
  have hpoint : forall j,
      |rectMatMulVec Aplus Deltab j| <=
        rectMatMulVec C (fun k => |x k|) j := by
    intro j
    calc
      |rectMatMulVec Aplus Deltab j| <=
          rectMatMulVec (absMatrixRect Aplus) (fun i => |Deltab i|) j := by
        simpa [rectMatMulVec, absMatrixRect] using
          abs_rectMatMulVec_le Aplus Deltab j
      _ <= rectMatMulVec (absMatrixRect Aplus) (fun i => |b i|) j := by
        unfold rectMatMulVec
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hDeltab i) (abs_nonneg _)
      _ = rectMatMulVec (absMatrixRect Aplus)
          (fun i => |rectMatMulVec A x i|) j := by
        rw [hAx]
      _ <= rectMatMulVec (absMatrixRect Aplus)
          (rectMatMulVec (absMatrixRect A) (fun k => |x k|)) j := by
        unfold rectMatMulVec
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (by
            simpa [rectMatMulVec, absMatrixRect] using
              abs_rectMatMulVec_le A x i)
          (abs_nonneg _)
      _ = rectMatMulVec C (fun k => |x k|) j := by
        simpa [C] using
          congrFun
            (rectMatMulVec_rectMatMul
              (absMatrixRect Aplus) (absMatrixRect A)
              (fun k => |x k|)).symm j
  calc
    vecNorm2 (rectMatMulVec Aplus Deltab) <=
        vecNorm2 (rectMatMulVec C (fun k => |x k|)) :=
      vecNorm2_le_of_abs_le _ _ hpoint
    _ <= higham21Cond2With A Aplus * vecNorm2 (fun k => |x k|) :=
      hC (fun k => |x k|)
    _ = higham21Cond2With A Aplus * vecNorm2 x := by
      rw [vecNorm2_abs]
    _ = higham21Cond2With A Aplus *
        vecNorm2 (rectMatMulVec Aplus b) := by rfl

/-- The null-space contribution has the one-projector-factor bound used in
    the strict underdetermined branch of (21.8). -/
theorem higham21_eq21_8_nullspaceTerm_norm_le {m n : Nat}
    (A DeltaA H : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (b : Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A))
    (hH : forall i j, 0 <= H i j)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_8HadamardEnvelope A H i j) :
    vecNorm2 (higham21Eq21_8NullspaceTermWith A Aplus DeltaA b) <=
      higham21Eq21_8HNorm2 H * higham21Cond2With A Aplus *
        vecNorm2 (rectMatMulVec Aplus b) := by
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let z : Fin m -> Real := rectTransposeMulVec Aplus x
  let w : Fin n -> Real := rectTransposeMulVec DeltaA z
  let B : Fin n -> Fin n -> Real := rectMatMul Aplus DeltaA
  let radius : Real := higham21Eq21_8HNorm2 H * higham21Cond2With A Aplus
  have hradius : 0 <= radius := by
    exact mul_nonneg (higham21Eq21_8HNorm2_nonneg H)
      (higham21Cond2With_nonneg A Aplus)
  have hB : rectOpNorm2Le B radius := by
    simpa [B, radius] using
      higham21_eq21_8_pseudoinverse_product_rectOpNorm2Le
        A DeltaA H Aplus hH hDeltaA
  have hBt : rectOpNorm2Le (finiteTranspose B) radius :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le B hradius hB
  have hwEq : w = rectMatMulVec (finiteTranspose B) x := by
    simpa [w, z, B] using
      higham21_eq21_8_transpose_product_action Aplus DeltaA x
  have hw : vecNorm2 w <= radius * vecNorm2 x := by
    rw [hwEq]
    exact hBt x
  have hres :
      vecNorm2 (fun j => w j -
          rectMatMulVec Aplus (rectMatMulVec A w) j) <= vecNorm2 w :=
    higham21_eq21_8_projection_residual_norm_le
      A Aplus hRight hSym w
  simpa [higham21Eq21_8NullspaceTermWith, x, z, w, radius,
    mul_assoc] using hres.trans hw

/-- The data contribution consists of one `f = |b|` term and one
    `E = |A| Hadamard H` term. -/
theorem higham21_eq21_8_dataTerm_norm_le {m n : Nat}
    (A DeltaA H : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (b Deltab : Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hH : forall i j, 0 <= H i j)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_8HadamardEnvelope A H i j)
    (hDeltab : forall i, |Deltab i| <= |b i|) :
    vecNorm2 (higham21Eq21_8DataTermWith Aplus DeltaA b Deltab) <=
      higham21Cond2With A Aplus * vecNorm2 (rectMatMulVec Aplus b) +
        higham21Eq21_8HNorm2 H * higham21Cond2With A Aplus *
          vecNorm2 (rectMatMulVec Aplus b) := by
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let B : Fin n -> Fin n -> Real := rectMatMul Aplus DeltaA
  let u : Fin n -> Real := rectMatMulVec Aplus Deltab
  let v : Fin n -> Real := rectMatMulVec B x
  let radius : Real := higham21Eq21_8HNorm2 H * higham21Cond2With A Aplus
  have hB : rectOpNorm2Le B radius := by
    simpa [B, radius] using
      higham21_eq21_8_pseudoinverse_product_rectOpNorm2Le
        A DeltaA H Aplus hH hDeltaA
  have hu : vecNorm2 u <= higham21Cond2With A Aplus * vecNorm2 x := by
    simpa [u, x] using
      higham21_eq21_8_rhs_image_norm_le_cond2With
        A Aplus b Deltab hRight hDeltab
  have hv : vecNorm2 v <= radius * vecNorm2 x := by
    exact hB x
  have hterm :
      higham21Eq21_8DataTermWith Aplus DeltaA b Deltab =
        fun j => u j - v j := by
    calc
      higham21Eq21_8DataTermWith Aplus DeltaA b Deltab =
          rectMatMulVec Aplus
            (fun i => Deltab i - rectMatMulVec DeltaA x i) := by
        rfl
      _ = fun j => rectMatMulVec Aplus Deltab j -
          rectMatMulVec Aplus (rectMatMulVec DeltaA x) j :=
        rectMatMulVec_sub Aplus Deltab (rectMatMulVec DeltaA x)
      _ = fun j => u j - v j := by
        ext j
        simp only [u, v, B]
        rw [rectMatMulVec_rectMatMul]
  have htri : vecNorm2 (fun j => u j - v j) <= vecNorm2 u + vecNorm2 v := by
    calc
      vecNorm2 (fun j => u j - v j) =
          vecNorm2 (fun j => u j + (-v j)) := by rfl
      _ <= vecNorm2 u + vecNorm2 (fun j => -v j) :=
        vecNorm2_add_le u (fun j => -v j)
      _ = vecNorm2 u + vecNorm2 v := by rw [vecNorm2_neg]
  rw [hterm]
  calc
    vecNorm2 (fun j => u j - v j) <= vecNorm2 u + vecNorm2 v := htri
    _ <= higham21Cond2With A Aplus * vecNorm2 x +
        radius * vecNorm2 x := add_le_add hu hv
    _ = higham21Cond2With A Aplus *
          vecNorm2 (rectMatMulVec Aplus b) +
        higham21Eq21_8HNorm2 H * higham21Cond2With A Aplus *
          vecNorm2 (rectMatMulVec Aplus b) := by
      rfl

/-- Higham, 2nd ed., equation (21.8), supplied-pseudoinverse coefficient
    bound.  The proof splits into `m = n`, where the null-space term is zero,
    and `m < n`, where the projector residual is contractive. -/
theorem higham21_eq21_8_firstOrder_twoTerm_coefficient_bound_with
    {m n : Nat}
    (A DeltaA H : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (b Deltab : Fin m -> Real)
    (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus)
    (hH : forall i j, 0 <= H i j)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_8HadamardEnvelope A H i j)
    (hDeltab : forall i, |Deltab i| <= |b i|) :
    higham21Eq21_8FirstOrderTwoTermCoefficientWith
        A Aplus DeltaA b Deltab <=
      higham21Eq21_8DimensionFactor m n *
        max (higham21Eq21_8HNorm2 H) 1 *
          higham21Cond2With A Aplus *
            vecNorm2 (rectMatMulVec Aplus b) := by
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let h : Real := higham21Eq21_8HNorm2 H
  let c : Real := higham21Cond2With A Aplus
  let M : Real := max h 1
  let base : Real := M * c * vecNorm2 x
  have hc : 0 <= c := by
    simpa [c] using higham21Cond2With_nonneg A Aplus
  have hcx : 0 <= c * vecNorm2 x :=
    mul_nonneg hc (vecNorm2_nonneg x)
  have hhBase : h * c * vecNorm2 x <= base := by
    have hle := mul_le_mul_of_nonneg_right (le_max_left h 1) hcx
    simpa [base, M, mul_assoc] using hle
  have honeBase : c * vecNorm2 x <= base := by
    have hle := mul_le_mul_of_nonneg_right (le_max_right h 1) hcx
    simpa [base, M, mul_assoc] using hle
  have hdata := higham21_eq21_8_dataTerm_norm_le
    A DeltaA H Aplus b Deltab hRight hH hDeltaA hDeltab
  by_cases heq : m = n
  · subst n
    have hzero :=
      higham21_eq21_8_nullspaceTerm_eq_zero_of_square
        A Aplus DeltaA b hRight
    calc
      higham21Eq21_8FirstOrderTwoTermCoefficientWith
          A Aplus DeltaA b Deltab =
          vecNorm2 (higham21Eq21_8DataTermWith
            Aplus DeltaA b Deltab) := by
        simp only [higham21Eq21_8FirstOrderTwoTermCoefficientWith, hzero,
          add_eq_right]
        simpa only [Pi.zero_apply] using (vecNorm2_zero (n := m))
      _ <= c * vecNorm2 x + h * c * vecNorm2 x := by
        simpa [c, h, x, mul_assoc] using hdata
      _ <= base + base := add_le_add honeBase hhBase
      _ = 2 * base := by ring
      _ = higham21Eq21_8DimensionFactor m m * M * c * vecNorm2 x := by
        rw [higham21Eq21_8DimensionFactor_square]
        simp only [base]
        ring
      _ = higham21Eq21_8DimensionFactor m m *
          max (higham21Eq21_8HNorm2 H) 1 *
            higham21Cond2With A Aplus *
              vecNorm2 (rectMatMulVec Aplus b) := by
        rfl
  · have hlt : m < n := lt_of_le_of_ne hmn heq
    have hnull := higham21_eq21_8_nullspaceTerm_norm_le
      A DeltaA H Aplus b hRight hMP.domain_projection_symmetric
        hH hDeltaA
    calc
      higham21Eq21_8FirstOrderTwoTermCoefficientWith
          A Aplus DeltaA b Deltab <=
          h * c * vecNorm2 x +
            (c * vecNorm2 x + h * c * vecNorm2 x) := by
        exact add_le_add
          (by simpa [h, c, x, mul_assoc] using hnull)
          (by simpa [h, c, x, mul_assoc] using hdata)
      _ <= base + (base + base) :=
        add_le_add hhBase (add_le_add honeBase hhBase)
      _ = 3 * base := by ring
      _ = higham21Eq21_8DimensionFactor m n * M * c * vecNorm2 x := by
        rw [higham21Eq21_8DimensionFactor_of_lt hlt]
        simp only [base]
        ring
      _ = higham21Eq21_8DimensionFactor m n *
          max (higham21Eq21_8HNorm2 H) 1 *
            higham21Cond2With A Aplus *
              vecNorm2 (rectMatMulVec Aplus b) := by
        rfl

/-- The corresponding supplied-pseudoinverse bound for the first-order
    vector itself. -/
theorem higham21_eq21_8_firstOrder_norm_bound_with
    {m n : Nat}
    (A DeltaA H : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (b Deltab : Fin m -> Real)
    (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus)
    (hH : forall i j, 0 <= H i j)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_8HadamardEnvelope A H i j)
    (hDeltab : forall i, |Deltab i| <= |b i|) :
    vecNorm2 (higham21Eq21_8FirstOrderWith A Aplus DeltaA b Deltab) <=
      higham21Eq21_8DimensionFactor m n *
        max (higham21Eq21_8HNorm2 H) 1 *
          higham21Cond2With A Aplus *
            vecNorm2 (rectMatMulVec Aplus b) := by
  exact
    (higham21_eq21_8_firstOrder_norm_le_twoTerm_coefficient_with
      A Aplus DeltaA b Deltab).trans
    (higham21_eq21_8_firstOrder_twoTerm_coefficient_bound_with
      A DeltaA H Aplus b Deltab hmn hRight hMP hH hDeltaA hDeltab)

/-- A nonzero right-hand side gives a nonzero minimum-norm solution whenever
    the supplied pseudoinverse is a right inverse. -/
theorem higham21_eq21_8_base_norm_pos_with {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (b : Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hb : Not (b = 0)) :
    0 < vecNorm2 (rectMatMulVec Aplus b) := by
  let x : Fin n -> Real := rectMatMulVec Aplus b
  have hAx : rectMatMulVec A x = b := by
    simpa [x] using higham21_eq21_8_base_system_with A Aplus b hRight
  have hx : Not (x = 0) := by
    intro hx0
    apply hb
    rw [<- hAx, hx0]
    ext i
    simp [rectMatMulVec]
  have hxnorm : Not (vecNorm2 x = 0) := by
    intro hzero
    apply hx
    funext i
    exact (vecNorm2_eq_zero_iff x).mp hzero i
  simpa [x] using
    lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm)

/-- Supplied-pseudoinverse relative first-order form of equation (21.8). -/
theorem higham21_eq21_8_firstOrder_relative_bound_with
    {m n : Nat}
    (A DeltaA H : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (b Deltab : Fin m -> Real)
    (eps : Real) (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus)
    (hb : Not (b = 0))
    (hH : forall i j, 0 <= H i j)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_8HadamardEnvelope A H i j)
    (hDeltab : forall i, |Deltab i| <= |b i|) :
    vecNorm2 (fun j => eps *
        higham21Eq21_8FirstOrderWith A Aplus DeltaA b Deltab j) /
        vecNorm2 (rectMatMulVec Aplus b) <=
      |eps| *
        (higham21Eq21_8DimensionFactor m n *
          max (higham21Eq21_8HNorm2 H) 1 *
            higham21Cond2With A Aplus) := by
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let firstOrder : Fin n -> Real :=
    higham21Eq21_8FirstOrderWith A Aplus DeltaA b Deltab
  let K : Real := higham21Eq21_8DimensionFactor m n *
    max (higham21Eq21_8HNorm2 H) 1 * higham21Cond2With A Aplus
  have hxpos : 0 < vecNorm2 x := by
    simpa [x] using higham21_eq21_8_base_norm_pos_with A Aplus b hRight hb
  have hfirst : vecNorm2 firstOrder <= K * vecNorm2 x := by
    simpa [firstOrder, K, x, mul_assoc] using
      higham21_eq21_8_firstOrder_norm_bound_with
        A DeltaA H Aplus b Deltab hmn hRight hMP hH hDeltaA hDeltab
  have hscaled : vecNorm2 (fun j => eps * firstOrder j) <=
      |eps| * (K * vecNorm2 x) := by
    rw [vecNorm2_smul]
    exact mul_le_mul_of_nonneg_left hfirst (abs_nonneg eps)
  change vecNorm2 (fun j => eps * firstOrder j) / vecNorm2 x <= |eps| * K
  calc
    vecNorm2 (fun j => eps * firstOrder j) / vecNorm2 x <=
        (|eps| * (K * vecNorm2 x)) / vecNorm2 x :=
      div_le_div_of_nonneg_right hscaled hxpos.le
    _ = |eps| * K := by
      field_simp [ne_of_gt hxpos] <;> ring

/-- The canonical source first-order expression agrees with the existing
    equation-(21.7) first-order vector, now for a perturbed right-hand side. -/
theorem higham21_eq21_8_canonical_firstOrder_eq_eq21_7_firstOrder
    {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real) (b Deltab : Fin m -> Real)
    (hdet : Not
      (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0)) :
    higham21Eq21_8FirstOrderWith
        A (undetAplusOfGramNonsingInv A) DeltaA b Deltab =
      higham21Eq21_7FirstOrder A DeltaA b Deltab
        (undetGramNonsingInv A) := by
  let G_inv : Fin m -> Fin m -> Real := undetGramNonsingInv A
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let y : Fin m -> Real := matMulVec m G_inv b
  let z : Fin m -> Real := rectTransposeMulVec Aplus x
  let w : Fin n -> Real := rectTransposeMulVec DeltaA z
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hRightEntry : forall r i : Fin m,
      Finset.univ.sum (fun k : Fin n => A r k * Aplus k i) =
        if r = i then 1 else 0 := by
    intro r i
    have hri := congrFun (congrFun hRight r) i
    simpa [rectMatMul, idMatrix] using hri
  have hx : x = rectTransposeMulVec A y := by
    simpa [x, Aplus, y, G_inv, undetAplusOfGramNonsingInv] using
      rectMatMulVec_undetAplusOfGramInv A G_inv b
  have hyz : y = z := by
    ext i
    symm
    rw [show z = rectTransposeMulVec Aplus x by rfl, hx]
    unfold rectTransposeMulVec
    calc
      Finset.univ.sum (fun j : Fin n =>
          Aplus j i * Finset.univ.sum (fun r : Fin m => A r j * y r)) =
          Finset.univ.sum (fun j : Fin n =>
            Finset.univ.sum (fun r : Fin m =>
              Aplus j i * (A r j * y r))) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
      _ = Finset.univ.sum (fun r : Fin m =>
          Finset.univ.sum (fun j : Fin n =>
            Aplus j i * (A r j * y r))) := by
        rw [Finset.sum_comm]
      _ = Finset.univ.sum (fun r : Fin m =>
          (Finset.univ.sum (fun j : Fin n => A r j * Aplus j i)) * y r) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = Finset.univ.sum (fun r : Fin m =>
          (if r = i then 1 else 0) * y r) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hRightEntry r i]
      _ = y i := by simp
  ext j
  change
    (w j - rectMatMulVec Aplus (rectMatMulVec A w) j) +
        rectMatMulVec Aplus
          (fun i => Deltab i - rectMatMulVec DeltaA x i) j =
      rectTransposeMulVec DeltaA y j -
          rectMatMulVec Aplus
            (rectMatMulVec A (rectTransposeMulVec DeltaA y)) j +
        rectMatMulVec Aplus
          (fun i => Deltab i - rectMatMulVec DeltaA x i) j
  rw [hyz]

/-- Canonical-Gram version of the two-term coefficient bound in (21.8). -/
theorem higham21_eq21_8_firstOrder_twoTerm_coefficient_bound
    {m n : Nat}
    (A DeltaA H : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (hmn : m <= n)
    (hdet : Not
      (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hH : forall i j, 0 <= H i j)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_8HadamardEnvelope A H i j)
    (hDeltab : forall i, |Deltab i| <= |b i|) :
    higham21Eq21_8FirstOrderTwoTermCoefficientWith
        A (undetAplusOfGramNonsingInv A) DeltaA b Deltab <=
      higham21Eq21_8DimensionFactor m n *
        max (higham21Eq21_8HNorm2 H) 1 *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) *
            vecNorm2
              (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  exact higham21_eq21_8_firstOrder_twoTerm_coefficient_bound_with
    A DeltaA H (undetAplusOfGramNonsingInv A) b Deltab hmn
    (higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
      A hdet)
    (higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero A hdet)
    hH hDeltaA hDeltab

/-- Canonical equation-(21.7) first-order vector bound used by (21.8). -/
theorem higham21_eq21_8_firstOrder_norm_bound
    {m n : Nat}
    (A DeltaA H : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (hmn : m <= n)
    (hdet : Not
      (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hH : forall i j, 0 <= H i j)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_8HadamardEnvelope A H i j)
    (hDeltab : forall i, |Deltab i| <= |b i|) :
    vecNorm2
        (higham21Eq21_7FirstOrder A DeltaA b Deltab
          (undetGramNonsingInv A)) <=
      higham21Eq21_8DimensionFactor m n *
        max (higham21Eq21_8HNorm2 H) 1 *
          higham21Cond2With A (undetAplusOfGramNonsingInv A) *
            vecNorm2
              (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  rw [<- higham21_eq21_8_canonical_firstOrder_eq_eq21_7_firstOrder
    A DeltaA b Deltab hdet]
  exact higham21_eq21_8_firstOrder_norm_bound_with
    A DeltaA H (undetAplusOfGramNonsingInv A) b Deltab hmn
    (higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
      A hdet)
    (higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero A hdet)
    hH hDeltaA hDeltab

/-- Higham, 2nd ed., equation (21.8), canonical relative first-order form. -/
theorem higham21_eq21_8_firstOrder_relative_bound
    {m n : Nat}
    (A DeltaA H : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (eps : Real) (hmn : m <= n)
    (hdet : Not
      (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hb : Not (b = 0))
    (hH : forall i j, 0 <= H i j)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_8HadamardEnvelope A H i j)
    (hDeltab : forall i, |Deltab i| <= |b i|) :
    vecNorm2
        (fun j => eps *
          higham21Eq21_7FirstOrder A DeltaA b Deltab
            (undetGramNonsingInv A) j) /
        vecNorm2
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b) <=
      |eps| *
        (higham21Eq21_8DimensionFactor m n *
          max (higham21Eq21_8HNorm2 H) 1 *
            higham21Cond2With A (undetAplusOfGramNonsingInv A)) := by
  rw [<- higham21_eq21_8_canonical_firstOrder_eq_eq21_7_firstOrder
    A DeltaA b Deltab hdet]
  exact higham21_eq21_8_firstOrder_relative_bound_with
    A DeltaA H (undetAplusOfGramNonsingInv A) b Deltab eps hmn
    (higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
      A hdet)
    (higham21_eq21_4_rect_moore_penrose_of_gram_det_ne_zero A hdet)
    hb hH hDeltaA hDeltab

/-- Equation (21.8) with the exact finite Theorem 21.1 endpoint: the displayed
    first-order coefficient is followed by the explicit
    `|eps|^2*C/||x||_2` fixed-radius remainder. -/
theorem higham21_eq21_8_relative_bound_with_fixed_radius_remainder
    {m n : Nat}
    (A DeltaA H : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (rho beta eps : Real) (hmn : m <= n)
    (hdet : Not
      (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hdet_eps : Not
      (Matrix.det
        (rectGram (higham21Eq21_7ScaledMatrix A DeltaA eps) :
          Matrix (Fin m) (Fin m) Real) = 0))
    (hb : Not (b = 0))
    (hH : forall i j, 0 <= H i j)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_8HadamardEnvelope A H i j)
    (hDeltab : forall i, |Deltab i| <= |b i|)
    (hrho : 0 <= rho) (hbeta : 0 <= beta) (heps : |eps| <= rho)
    (hG_eps_inv :
      frobNorm
        (undetGramNonsingInv
          (higham21Eq21_7ScaledMatrix A DeltaA eps)) <= beta) :
    vecNorm2
        (fun j =>
          higham21Eq21_7PerturbedSolution A DeltaA b Deltab
                (undetGramNonsingInv
                  (higham21Eq21_7ScaledMatrix A DeltaA eps)) eps j -
            higham21Eq21_7BaseSolution A b
              (undetGramNonsingInv A) j) /
        vecNorm2
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b) <=
      |eps| *
          (higham21Eq21_8DimensionFactor m n *
            max (higham21Eq21_8HNorm2 H) 1 *
              higham21Cond2With A (undetAplusOfGramNonsingInv A)) +
        (|eps| ^ 2 *
            higham21Eq21_7FixedRadiusCoefficient
              A DeltaA b Deltab (undetGramNonsingInv A) rho beta) /
          vecNorm2
            (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  let x : Fin n -> Real :=
    rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let firstOrder : Fin n -> Real :=
    higham21Eq21_7FirstOrder A DeltaA b Deltab
      (undetGramNonsingInv A)
  let remainder : Fin n -> Real :=
    higham21Eq21_7ExactRemainder A DeltaA b Deltab
      (undetGramNonsingInv A)
      (undetGramNonsingInv
        (higham21Eq21_7ScaledMatrix A DeltaA eps)) eps
  let K : Real := higham21Eq21_8DimensionFactor m n *
    max (higham21Eq21_8HNorm2 H) 1 *
      higham21Cond2With A (undetAplusOfGramNonsingInv A)
  let C : Real := higham21Eq21_7FixedRadiusCoefficient
    A DeltaA b Deltab (undetGramNonsingInv A) rho beta
  have hxpos : 0 < vecNorm2 x := by
    simpa [x] using
      higham21_eq21_8_base_norm_pos_with
        A (undetAplusOfGramNonsingInv A) b
        (higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
          A hdet) hb
  have hfirst :
      vecNorm2 (fun j => eps * firstOrder j) / vecNorm2 x <= |eps| * K := by
    simpa [firstOrder, x, K] using
      higham21_eq21_8_firstOrder_relative_bound
        A DeltaA H b Deltab eps hmn hdet hb hH hDeltaA hDeltab
  have hrem : vecNorm2 remainder <= |eps| ^ 2 * C := by
    simpa [remainder, C] using
      higham21Eq21_7_exactRemainder_vecNorm2_le_fixed_radius
        A DeltaA b Deltab (undetGramNonsingInv A)
        (undetGramNonsingInv
          (higham21Eq21_7ScaledMatrix A DeltaA eps))
        rho beta eps hrho hbeta heps hG_eps_inv
  have hExpansion :
      (fun j =>
        higham21Eq21_7PerturbedSolution A DeltaA b Deltab
              (undetGramNonsingInv
                (higham21Eq21_7ScaledMatrix A DeltaA eps)) eps j -
          higham21Eq21_7BaseSolution A b
            (undetGramNonsingInv A) j) =
        fun j => eps * firstOrder j + remainder j := by
    simpa [firstOrder, remainder] using
      higham21Eq21_7_exact_expansion_of_gram_det_ne_zero
        A DeltaA b Deltab eps hdet hdet_eps
  rw [hExpansion]
  change vecNorm2 (fun j => eps * firstOrder j + remainder j) /
      vecNorm2 x <= |eps| * K + (|eps| ^ 2 * C) / vecNorm2 x
  calc
    vecNorm2 (fun j => eps * firstOrder j + remainder j) / vecNorm2 x <=
        (vecNorm2 (fun j => eps * firstOrder j) + vecNorm2 remainder) /
          vecNorm2 x :=
      div_le_div_of_nonneg_right
        (vecNorm2_add_le (fun j => eps * firstOrder j) remainder) hxpos.le
    _ = vecNorm2 (fun j => eps * firstOrder j) / vecNorm2 x +
        vecNorm2 remainder / vecNorm2 x := by ring
    _ <= |eps| * K + (|eps| ^ 2 * C) / vecNorm2 x :=
      add_le_add hfirst (div_le_div_of_nonneg_right hrem hxpos.le)

/-- Higham, 2nd ed., Chapter 21, equation (21.8), in its literal asymptotic
    form.  The remainder is the normalized exact remainder from (21.7), proved
    `O(t^2)` on a derived full-row-rank neighborhood; the displayed linear
    coefficient is exactly
    `min {3,n-m+2} max {||H||_2,1} cond_2(A)`. -/
theorem higham21_eq21_8_relative_asymptotic_bound
    {m n : Nat}
    (A DeltaA H : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (hmn : m <= n)
    (hdet : Not
      (Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) = 0))
    (hb : Not (b = 0))
    (hH : forall i j, 0 <= H i j)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_8HadamardEnvelope A H i j)
    (hDeltab : forall i, |Deltab i| <= |b i|) :
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let E := higham21Eq21_8HadamardEnvelope A H
    let K := higham21Eq21_8DimensionFactor m n *
      max (higham21Eq21_8HNorm2 H) 1 *
        higham21Cond2With A (undetAplusOfGramNonsingInv A)
    let remainderRatio : Real -> Real := fun t =>
      vecNorm2
          (higham21Eq21_7ExactRemainder A DeltaA b Deltab
            (undetGramNonsingInv A)
            (undetGramNonsingInv
              (higham21Eq21_7ScaledMatrix A DeltaA t)) t) /
        vecNorm2 x
    And
      (remainderRatio =O[nhds 0] (fun t : Real => t ^ 2))
      (forall t,
        abs t <= higham21PerturbationDirectionRadius A DeltaA E ->
        vecNorm2
            (fun j =>
              higham21Eq21_7PerturbedSolution A DeltaA b Deltab
                    (undetGramNonsingInv
                      (higham21Eq21_7ScaledMatrix A DeltaA t)) t j -
                higham21Eq21_7BaseSolution A b
                  (undetGramNonsingInv A) j) /
            vecNorm2 x <=
          abs t * K + remainderRatio t) := by
  dsimp only
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let E : Fin m -> Fin n -> Real := higham21Eq21_8HadamardEnvelope A H
  let K : Real := higham21Eq21_8DimensionFactor m n *
    max (higham21Eq21_8HNorm2 H) 1 * higham21Cond2With A Aplus
  have hm : 0 < m := higham21_row_dimension_pos_of_rhs_ne_zero b hb
  have hE : forall i j, 0 <= E i j := by
    intro i j
    exact mul_nonneg (abs_nonneg (A i j)) (hH i j)
  have hxpos :
      0 < vecNorm2 (rectMatMulVec Aplus b) := by
    exact higham21_eq21_8_base_norm_pos_with A Aplus b
      (by
        simpa [Aplus] using
          higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
            A hdet)
      hb
  have hfirst :
      vecNorm2
          (higham21Eq21_7FirstOrder A DeltaA b Deltab
            (undetGramNonsingInv A)) <=
        K * vecNorm2 (rectMatMulVec Aplus b) := by
    simpa [K, Aplus, mul_assoc] using
      (higham21_eq21_8_firstOrder_norm_bound
        A DeltaA H b Deltab hmn hdet hH hDeltaA hDeltab)
  simpa [Aplus, E, K] using
    (higham21_eq21_7_euclidean_relative_asymptotic_bound_of_firstOrder_bound
      A DeltaA E b Deltab K hm hdet hE
      (by simpa [E] using hDeltaA) (by simpa [Aplus] using hxpos)
      (by simpa [Aplus] using hfirst))

end NumStability
