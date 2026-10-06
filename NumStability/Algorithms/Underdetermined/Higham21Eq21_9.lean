/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/

import NumStability.Algorithms.Underdetermined.Higham21PerturbationRadius
import NumStability.Algorithms.Underdetermined.Higham21RankStability

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-! # Higham, Chapter 21, equation (21.9)

The perturbation directions satisfy the normwise component budgets

`|DeltaA i j| <= Aop` and `|Deltab i| <= ||b||_2`.

The proof retains the two source terms in Theorem 21.1.  The complementary
projector contributes zero in the square case and one operator-norm factor in
the strictly underdetermined case.  Both matrix occurrences are then bounded
from the supplied operator certificates, giving the factor
`min {3, n - m + 2} * sqrt (m*n)` in (21.9).
-/

/-- The constant matrix budget used in the normwise specialization (21.9). -/
noncomputable def higham21Eq21_9NormwiseMatrixBudget {m n : Nat}
    (Aop : Real) : Fin m -> Fin n -> Real :=
  fun _ _ => Aop

/-- The constant right-hand-side budget used in (21.9). -/
noncomputable def higham21Eq21_9NormwiseRhsBudget {m : Nat}
    (b : Fin m -> Real) : Fin m -> Real :=
  fun _ => vecNorm2 b

/-- The projector contribution in (21.9): zero for `m = n`, one for `m < n`. -/
noncomputable def higham21Eq21_9ProjectorFactor (m n : Nat) : Real :=
  (Nat.min 1 (n - m) : Nat)

/-- The dimension-dependent coefficient printed in equation (21.9). -/
noncomputable def higham21Eq21_9DimensionCoefficient
    (m n : Nat) (kappa : Real) : Real :=
  (Nat.min 3 (n - m + 2) : Nat) *
    Real.sqrt ((m : Real) * (n : Real)) * kappa

/-- The canonical `kappa_2(A)` used in (21.9), with `A^+` fixed to the
    Moore--Penrose table `A^T(AA^T)^{-1}`. -/
noncomputable def higham21Eq21_9Kappa2 {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  higham21RectKappa2With A (undetAplusOfGramNonsingInv A)

theorem higham21Eq21_9Kappa2_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    0 <= higham21Eq21_9Kappa2 A := by
  exact higham21RectKappa2With_nonneg A
    (undetAplusOfGramNonsingInv A)

/-- The first source term in Theorem 21.1, equation (21.7). -/
noncomputable def higham21Eq21_9NullspaceTerm {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let z := rectTransposeMulVec Aplus x
  let w := rectTransposeMulVec DeltaA z
  rectMatMulVec (lsAugmentedProjectionBlock Aplus A) w

/-- The second source term in Theorem 21.1, equation (21.7). -/
noncomputable def higham21Eq21_9DataTerm {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) : Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  rectMatMulVec Aplus
    (fun i => Deltab i - rectMatMulVec DeltaA x i)

/-- The Euclidean two-term coefficient obtained from the source first-order
    formula, before any dimension-dependent estimates are made. -/
noncomputable def higham21Eq21_9FirstOrderTwoTermCoefficient {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) : Real :=
  vecNorm2 (higham21Eq21_9NullspaceTerm A DeltaA b) +
    vecNorm2 (higham21Eq21_9DataTerm A DeltaA b Deltab)

/-- The intermediate scalar coefficient supplied by the two exact operator
    certificates. -/
noncomputable def higham21Eq21_9OperatorCertificateCoefficient
    (m n : Nat) (Aop AplusOp : Real)
    (b : Fin m -> Real) (x : Fin n -> Real) : Real :=
  let d := Real.sqrt ((m : Real) * (n : Real))
  higham21Eq21_9ProjectorFactor m n *
      ((d * Aop) * (AplusOp * vecNorm2 x)) +
    AplusOp *
      (Real.sqrt (m : Real) * vecNorm2 b +
        (d * Aop) * vecNorm2 x)

private theorem higham21_eq21_9_dimensions_pos_of_rhs_ne_zero
    {m n : Nat} (b : Fin m -> Real) (hmn : m <= n) (hb : b ≠ 0) :
    0 < m /\ 0 < n := by
  have hmne : m ≠ 0 := by
    intro hm
    subst m
    apply hb
    funext i
    exact Fin.elim0 i
  have hm : 0 < m := Nat.pos_of_ne_zero hmne
  exact ⟨hm, lt_of_lt_of_le hm hmn⟩

/-- The elementary `l1 <= sqrt(n) l2` estimate used when the constant budget
    is expanded entrywise. -/
theorem higham21_eq21_9_sum_abs_le_sqrt_card_mul_vecNorm2 {n : Nat}
    (x : Fin n -> Real) :
    (Finset.univ.sum fun j : Fin n => |x j|) <=
      Real.sqrt (n : Real) * vecNorm2 x := by
  have hcs :
      (Finset.univ.sum fun j : Fin n => |x j| * 1) ^ 2 <=
        (Finset.univ.sum fun j : Fin n => |x j| ^ 2) *
          (Finset.univ.sum fun _j : Fin n => (1 : Real) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun j => |x j|) (fun _ => 1)
  have habsSq :
      (Finset.univ.sum fun j : Fin n => |x j| ^ 2) = vecNorm2Sq x := by
    unfold vecNorm2Sq
    apply Finset.sum_congr rfl
    intro j _
    rw [sq_abs]
  have hleft :
      (Finset.univ.sum fun j : Fin n => |x j| * 1) =
        Finset.univ.sum fun j : Fin n => |x j| := by
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_one]
  have hsumOne :
      (Finset.univ.sum fun _j : Fin n => (1 : Real) ^ 2) =
        (n : Real) := by
    simp
  rw [hleft, hsumOne, habsSq] at hcs
  have hl : 0 <= Finset.univ.sum fun j : Fin n => |x j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg (x j)
  have hr : 0 <= Real.sqrt (n : Real) * vecNorm2 x :=
    mul_nonneg (Real.sqrt_nonneg _) (vecNorm2_nonneg x)
  have hrsq :
      (Real.sqrt (n : Real) * vecNorm2 x) ^ 2 =
        vecNorm2Sq x * (n : Real) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), vecNorm2_sq]
    ring
  have hsq :
      (Finset.univ.sum fun j : Fin n => |x j|) ^ 2 <=
        (Real.sqrt (n : Real) * vecNorm2 x) ^ 2 := by
    rw [hrsq]
    exact hcs
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hl, Real.sqrt_sq hr] at hsqrt

/-- A matrix lying in the constant normwise budget has the required
    `sqrt(m*n) * Aop` Frobenius bound. -/
theorem higham21_eq21_9_frobNormRect_le_normwise_matrix_budget
    {m n : Nat} (DeltaA : Fin m -> Fin n -> Real) (Aop : Real)
    (hAop : 0 <= Aop)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_9NormwiseMatrixBudget Aop i j) :
    frobNormRect DeltaA <=
      Real.sqrt ((m : Real) * (n : Real)) * Aop := by
  apply frobNormRect_le_sqrt_mul_nat_of_entry_abs_le DeltaA hAop
  intro i j
  simpa [higham21Eq21_9NormwiseMatrixBudget] using hDeltaA i j

/-- Operator form of the constant matrix-budget estimate. -/
theorem higham21_eq21_9_matrix_perturbation_rectOpNorm2Le
    {m n : Nat} (DeltaA : Fin m -> Fin n -> Real) (Aop : Real)
    (hAop : 0 <= Aop)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_9NormwiseMatrixBudget Aop i j) :
    rectOpNorm2Le DeltaA
      (Real.sqrt ((m : Real) * (n : Real)) * Aop) :=
  rectOpNorm2Le_of_frobNormRect_le DeltaA
    (higham21_eq21_9_frobNormRect_le_normwise_matrix_budget
      DeltaA Aop hAop hDeltaA)

/-- The constant right-hand-side budget has Euclidean radius
    `sqrt(m) * ||b||_2`. -/
theorem higham21_eq21_9_rhs_perturbation_vecNorm2_le
    {m : Nat} (b Deltab : Fin m -> Real)
    (hDeltab : forall i,
      |Deltab i| <= higham21Eq21_9NormwiseRhsBudget b i) :
    vecNorm2 Deltab <= Real.sqrt (m : Real) * vecNorm2 b := by
  apply vecNorm2_le_sqrt_card_mul_of_abs_le Deltab (vecNorm2_nonneg b)
  intro i
  simpa [higham21Eq21_9NormwiseRhsBudget] using hDeltab i

/-- The constant matrix budget applied to `|x|` is controlled by the usual
    `l1 <= sqrt(n) l2` estimate. -/
theorem higham21_eq21_9_normwise_matrix_budget_abs_action
    {m n : Nat} (Aop : Real) (x : Fin n -> Real) (i : Fin m) :
    rectMatMulVec (higham21Eq21_9NormwiseMatrixBudget Aop)
        (fun j => |x j|) i =
      Aop * (Finset.univ.sum fun j : Fin n => |x j|) := by
  unfold rectMatMulVec higham21Eq21_9NormwiseMatrixBudget
  rw [Finset.mul_sum]

/-- The absolute pseudoinverse inherits the rank-sensitive
    `sqrt(m) * AplusOp` certificate. -/
theorem higham21_eq21_9_abs_pseudoinverse_rectOpNorm2Le
    {m n : Nat} (hm : 0 < m) (Aplus : Fin n -> Fin m -> Real)
    (AplusOp : Real) (hAplusOp : 0 <= AplusOp)
    (hAplus : rectOpNorm2Le Aplus AplusOp) :
    rectOpNorm2Le (absMatrixRect Aplus)
      (Real.sqrt (m : Real) * AplusOp) := by
  classical
  have hrank : realRectMatrixRank Aplus <= m := by
    unfold realRectMatrixRank complexMatrixRank
    simpa using
      (Matrix.rank_le_card_width
        (realRectToCMatrix Aplus : Matrix (Fin n) (Fin m) Complex))
  have hsqrt :
      Real.sqrt (realRectMatrixRank Aplus : Real) <=
        Real.sqrt (m : Real) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hrank)
  have hbase :=
    rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le
      hm Aplus hAplusOp hAplus
  exact rectOpNorm2Le_mono
    (mul_le_mul_of_nonneg_right hsqrt hAplusOp) hbase

/-- In the square case a right inverse is also a left inverse. -/
theorem higham21_eq21_9_square_left_inverse {n : Nat}
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

/-- The complement `I - Aplus*A` has exactly the source factor used in
    (21.9): zero in the square branch and at most one otherwise. -/
theorem higham21_eq21_9_complement_projector_rectOpNorm2Le
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (hmn : m <= n)
    (hRight : rectMatMul A Aplus = idMatrix m)
    (hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A)) :
    rectOpNorm2Le (lsAugmentedProjectionBlock Aplus A)
      (higham21Eq21_9ProjectorFactor m n) := by
  by_cases heq : m = n
  · subst n
    have hLeft : rectMatMul Aplus A = idMatrix m :=
      higham21_eq21_9_square_left_inverse A Aplus hRight
    intro u
    have happly : rectMatMulVec Aplus (rectMatMulVec A u) = u := by
      calc
        rectMatMulVec Aplus (rectMatMulVec A u) =
            rectMatMulVec (rectMatMul Aplus A) u :=
          (rectMatMulVec_rectMatMul Aplus A u).symm
        _ = rectMatMulVec (idMatrix m) u := by rw [hLeft]
        _ = u := rectMatMulVec_idMatrix u
    have hblock := lsAugmentedProjectionBlock_mulVec Aplus A u
    rw [happly] at hblock
    rw [hblock]
    simp [higham21Eq21_9ProjectorFactor, vecNorm2_zero]
  · have hlt : m < n := lt_of_le_of_ne hmn heq
    have hcontractive :
        rectOpNorm2Le
          (fun i j => idMatrix n i j - rectMatMul Aplus A i j) 1 :=
      wedinLemma20_12_rectOpNorm2Le_projectionComplement_of_symmetric_left_inverse
        Aplus A hRight hSym
    have hgap : 1 <= n - m := by omega
    have hmin : Nat.min 1 (n - m) = 1 := Nat.min_eq_left hgap
    simpa [higham21Eq21_9ProjectorFactor, hmin,
      lsAugmentedProjectionBlock, rectMatMul] using hcontractive

/-- A supplied right inverse sends the pseudoinverse solution back to `b`. -/
theorem higham21_eq21_9_base_system
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (b : Fin m -> Real)
    (hRight : rectMatMul A Aplus = idMatrix m) :
    rectMatMulVec A (rectMatMulVec Aplus b) = b := by
  calc
    rectMatMulVec A (rectMatMulVec Aplus b) =
        rectMatMulVec (rectMatMul A Aplus) b :=
      (rectMatMulVec_rectMatMul A Aplus b).symm
    _ = rectMatMulVec (idMatrix m) b := by rw [hRight]
    _ = b := rectMatMulVec_idMatrix b

/-- Consequently `||b||_2 <= Aop ||x||_2` follows from the supplied
    operator certificate for `A`; it is not assumed as a certificate. -/
theorem higham21_eq21_9_rhs_norm_le_matrix_op_mul_solution_norm
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real) (b : Fin m -> Real)
    (Aop : Real) (hRight : rectMatMul A Aplus = idMatrix m)
    (hA : rectOpNorm2Le A Aop) :
    vecNorm2 b <= Aop * vecNorm2 (rectMatMulVec Aplus b) := by
  have hsystem := higham21_eq21_9_base_system A Aplus b hRight
  calc
    vecNorm2 b = vecNorm2 (rectMatMulVec A (rectMatMulVec Aplus b)) := by
      rw [hsystem]
    _ <= Aop * vecNorm2 (rectMatMulVec Aplus b) :=
      hA (rectMatMulVec Aplus b)

private theorem higham21_eq21_9_rectOpNorm2Le_const_mul_abs
    {m n : Nat} (M : Fin m -> Fin n -> Real) (t c : Real)
    (hM : rectOpNorm2Le M c) :
    rectOpNorm2Le (fun i j => t * M i j) (|t| * c) := by
  intro x
  have hscale :
      rectMatMulVec (fun i j => t * M i j) x =
        fun i => t * rectMatMulVec M x i := by
    ext i
    unfold rectMatMulVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    vecNorm2 (rectMatMulVec (fun i j => t * M i j) x) =
        |t| * vecNorm2 (rectMatMulVec M x) := by
      rw [hscale, vecNorm2_smul]
    _ <= |t| * (c * vecNorm2 x) :=
      mul_le_mul_of_nonneg_left (hM x) (abs_nonneg t)
    _ = (|t| * c) * vecNorm2 x := by ring

/-- The canonical two-term source vector equals the existing exact
    equation-(21.7) first-order vector. -/
theorem higham21_eq21_9_source_firstOrder_eq_eq21_7_firstOrder
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0) :
    (fun j => higham21Eq21_9NullspaceTerm A DeltaA b j +
        higham21Eq21_9DataTerm A DeltaA b Deltab j) =
      higham21Eq21_7FirstOrder A DeltaA b Deltab
        (undetGramNonsingInv A) := by
  let G_inv : Fin m -> Fin m -> Real := undetGramNonsingInv A
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let y : Fin m -> Real := matMulVec m G_inv b
  let z : Fin m -> Real := rectTransposeMulVec Aplus x
  let w : Fin n -> Real := rectTransposeMulVec DeltaA z
  let q : Fin m -> Real :=
    fun i => Deltab i - rectMatMulVec DeltaA x i
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hRightEntry : forall r i : Fin m,
      (Finset.univ.sum fun k : Fin n => A r k * Aplus k i) =
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
      (Finset.univ.sum fun j : Fin n =>
          Aplus j i * (Finset.univ.sum fun r : Fin m => A r j * y r)) =
          Finset.univ.sum fun j : Fin n =>
            Finset.univ.sum fun r : Fin m =>
              Aplus j i * (A r j * y r) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
      _ = Finset.univ.sum fun r : Fin m =>
          Finset.univ.sum fun j : Fin n =>
            Aplus j i * (A r j * y r) := by
        rw [Finset.sum_comm]
      _ = Finset.univ.sum fun r : Fin m =>
          (Finset.univ.sum fun j : Fin n => A r j * Aplus j i) * y r := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = Finset.univ.sum fun r : Fin m =>
          (if r = i then 1 else 0) * y r := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hRightEntry r i]
      _ = y i := by simp
  ext j
  have hblock := congrFun
    (lsAugmentedProjectionBlock_mulVec Aplus A w) j
  change
    rectMatMulVec (lsAugmentedProjectionBlock Aplus A) w j +
        rectMatMulVec Aplus q j =
      rectTransposeMulVec DeltaA y j -
          rectMatMulVec Aplus
            (rectMatMulVec A (rectTransposeMulVec DeltaA y)) j +
        rectMatMulVec Aplus q j
  rw [hblock, hyz]

/-- The first-order vector is bounded by the exact two-term coefficient. -/
theorem higham21_eq21_9_firstOrder_norm_le_twoTermCoefficient
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0) :
    vecNorm2
        (higham21Eq21_7FirstOrder A DeltaA b Deltab
          (undetGramNonsingInv A)) <=
      higham21Eq21_9FirstOrderTwoTermCoefficient A DeltaA b Deltab := by
  rw [<- higham21_eq21_9_source_firstOrder_eq_eq21_7_firstOrder
    A DeltaA b Deltab hdet]
  simpa [higham21Eq21_9FirstOrderTwoTermCoefficient] using
    vecNorm2_add_le
      (higham21Eq21_9NullspaceTerm A DeltaA b)
      (higham21Eq21_9DataTerm A DeltaA b Deltab)

/-- The exact source two-term coefficient is bounded using the supplied
    operator certificates and the two constant normwise budgets. -/
theorem higham21_eq21_9_firstOrder_twoTermCoefficient_le_operatorCertificate
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (Aop AplusOp : Real)
    (hmn : m <= n)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hb : b ≠ 0)
    (hA : rectOpNorm2Le A Aop)
    (hAplus : rectOpNorm2Le
      (undetAplusOfGramNonsingInv A) AplusOp)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_9NormwiseMatrixBudget Aop i j)
    (hDeltab : forall i,
      |Deltab i| <= higham21Eq21_9NormwiseRhsBudget b i) :
    higham21Eq21_9FirstOrderTwoTermCoefficient A DeltaA b Deltab <=
      higham21Eq21_9OperatorCertificateCoefficient
        m n Aop AplusOp b
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  obtain ⟨hm, hn⟩ :=
    higham21_eq21_9_dimensions_pos_of_rhs_ne_zero b hmn hb
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let z : Fin m -> Real := rectTransposeMulVec Aplus x
  let w : Fin n -> Real := rectTransposeMulVec DeltaA z
  let q : Fin m -> Real :=
    fun i => Deltab i - rectMatMulVec DeltaA x i
  let d : Real := Real.sqrt ((m : Real) * (n : Real))
  let radius : Real := d * Aop
  let p : Real := higham21Eq21_9ProjectorFactor m n
  have hAop : 0 <= Aop := rectOpNorm2Le_radius_nonneg A hA
  have hAplusOp : 0 <= AplusOp :=
    rectOpNorm2Le_radius_nonneg Aplus hAplus
  have hradius : 0 <= radius :=
    mul_nonneg (Real.sqrt_nonneg _) hAop
  have hp : 0 <= p := by
    simp [p, higham21Eq21_9ProjectorFactor]
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hSym : IsSymmetricFiniteMatrix (rectMatMul Aplus A) := by
    simpa [Aplus] using
      undetAplusOfGramNonsingInv_domain_projection_symmetric A
  have hP :
      rectOpNorm2Le (lsAugmentedProjectionBlock Aplus A) p := by
    simpa [p] using
      higham21_eq21_9_complement_projector_rectOpNorm2Le
        A Aplus hmn hRight hSym
  have hDeltaOp : rectOpNorm2Le DeltaA radius := by
    simpa [radius, d] using
      higham21_eq21_9_matrix_perturbation_rectOpNorm2Le
        DeltaA Aop hAop hDeltaA
  have hDeltaT :
      rectOpNorm2Le (finiteTranspose DeltaA) radius :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      DeltaA hradius hDeltaOp
  have hAplusT :
      rectOpNorm2Le (finiteTranspose Aplus) AplusOp :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
      Aplus hAplusOp hAplus
  have hz : vecNorm2 z <= AplusOp * vecNorm2 x := by
    simpa [z, finiteTranspose] using hAplusT x
  have hw : vecNorm2 w <= radius * (AplusOp * vecNorm2 x) := by
    calc
      vecNorm2 w <= radius * vecNorm2 z := by
        simpa [w, finiteTranspose] using hDeltaT z
      _ <= radius * (AplusOp * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left hz hradius
  have hnull :
      vecNorm2 (higham21Eq21_9NullspaceTerm A DeltaA b) <=
        p * (radius * (AplusOp * vecNorm2 x)) := by
    calc
      vecNorm2 (higham21Eq21_9NullspaceTerm A DeltaA b) =
          vecNorm2
            (rectMatMulVec (lsAugmentedProjectionBlock Aplus A) w) := by
        rfl
      _ <= p * vecNorm2 w := hP w
      _ <= p * (radius * (AplusOp * vecNorm2 x)) :=
        mul_le_mul_of_nonneg_left hw hp
  have hDeltabNorm :
      vecNorm2 Deltab <= Real.sqrt (m : Real) * vecNorm2 b :=
    higham21_eq21_9_rhs_perturbation_vecNorm2_le b Deltab hDeltab
  have hDeltaX :
      vecNorm2 (rectMatMulVec DeltaA x) <= radius * vecNorm2 x :=
    hDeltaOp x
  have hq :
      vecNorm2 q <=
        Real.sqrt (m : Real) * vecNorm2 b + radius * vecNorm2 x := by
    calc
      vecNorm2 q =
          vecNorm2 (fun i => Deltab i + (-rectMatMulVec DeltaA x i)) := by
        rfl
      _ <= vecNorm2 Deltab +
          vecNorm2 (fun i => -rectMatMulVec DeltaA x i) :=
        vecNorm2_add_le Deltab (fun i => -rectMatMulVec DeltaA x i)
      _ = vecNorm2 Deltab + vecNorm2 (rectMatMulVec DeltaA x) := by
        rw [vecNorm2_neg]
      _ <= Real.sqrt (m : Real) * vecNorm2 b + radius * vecNorm2 x :=
        add_le_add hDeltabNorm hDeltaX
  have hdata :
      vecNorm2 (higham21Eq21_9DataTerm A DeltaA b Deltab) <=
        AplusOp *
          (Real.sqrt (m : Real) * vecNorm2 b + radius * vecNorm2 x) := by
    calc
      vecNorm2 (higham21Eq21_9DataTerm A DeltaA b Deltab) =
          vecNorm2 (rectMatMulVec Aplus q) := by rfl
      _ <= AplusOp * vecNorm2 q := hAplus q
      _ <= AplusOp *
          (Real.sqrt (m : Real) * vecNorm2 b + radius * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left hq hAplusOp
  simpa [higham21Eq21_9FirstOrderTwoTermCoefficient,
    higham21Eq21_9OperatorCertificateCoefficient, x, d, radius, p,
    Aplus] using add_le_add hnull hdata

/-- The operator-certificate coefficient collapses to the exact dimension
    factor in (21.9), using `||b|| <= Aop ||x||` derived from `A*x = b`. -/
theorem higham21_eq21_9_operatorCertificateCoefficient_le_dimensionCoefficient
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (b : Fin m -> Real) (Aop AplusOp kappa : Real)
    (hmn : m <= n) (hb : b ≠ 0)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hA : rectOpNorm2Le A Aop)
    (hAplus : rectOpNorm2Le
      (undetAplusOfGramNonsingInv A) AplusOp)
    (hkappa : kappa = AplusOp * Aop) :
    higham21Eq21_9OperatorCertificateCoefficient
        m n Aop AplusOp b
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b) <=
      higham21Eq21_9DimensionCoefficient m n kappa *
        vecNorm2 (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  obtain ⟨hm, hn⟩ :=
    higham21_eq21_9_dimensions_pos_of_rhs_ne_zero b hmn hb
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let d : Real := Real.sqrt ((m : Real) * (n : Real))
  let p : Real := higham21Eq21_9ProjectorFactor m n
  have hAop : 0 <= Aop := rectOpNorm2Le_radius_nonneg A hA
  have hAplusOp : 0 <= AplusOp :=
    rectOpNorm2Le_radius_nonneg Aplus hAplus
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hbNorm : vecNorm2 b <= Aop * vecNorm2 x := by
    simpa [x] using
      higham21_eq21_9_rhs_norm_le_matrix_op_mul_solution_norm
        A Aplus b Aop hRight hA
  have hn_one : 1 <= n := hn
  have hmprod : m <= m * n := by
    simpa using Nat.mul_le_mul_left m hn_one
  have hsqrt : Real.sqrt (m : Real) <= d := by
    dsimp [d]
    apply Real.sqrt_le_sqrt
    exact_mod_cast hmprod
  have hAopx : 0 <= Aop * vecNorm2 x :=
    mul_nonneg hAop (vecNorm2_nonneg x)
  have hrhs :
      Real.sqrt (m : Real) * vecNorm2 b <=
        d * (Aop * vecNorm2 x) := by
    calc
      Real.sqrt (m : Real) * vecNorm2 b <=
          Real.sqrt (m : Real) * (Aop * vecNorm2 x) :=
        mul_le_mul_of_nonneg_left hbNorm (Real.sqrt_nonneg _)
      _ <= d * (Aop * vecNorm2 x) :=
        mul_le_mul_of_nonneg_right hsqrt hAopx
  have hinner :
      Real.sqrt (m : Real) * vecNorm2 b +
          (d * Aop) * vecNorm2 x <=
        d * (Aop * vecNorm2 x) + d * (Aop * vecNorm2 x) := by
    convert add_le_add hrhs le_rfl using 1 <;> ring
  have hnat :
      Nat.min 1 (n - m) + 2 = Nat.min 3 (n - m + 2) := by
    by_cases hgap : n - m = 0
    · simp [hgap]
    · have hone : 1 <= n - m := Nat.one_le_iff_ne_zero.mpr hgap
      have hthree : 3 <= n - m + 2 := by omega
      have hmin_one : Nat.min 1 (n - m) = 1 := Nat.min_eq_left hone
      have hmin_three : Nat.min 3 (n - m + 2) = 3 :=
        Nat.min_eq_left hthree
      calc
        Nat.min 1 (n - m) + 2 = 1 + 2 :=
          congrArg (fun t : Nat => t + 2) hmin_one
        _ = 3 := by norm_num
        _ = Nat.min 3 (n - m + 2) := hmin_three.symm
  have hfactor :
      p + 2 = (Nat.min 3 (n - m + 2) : Nat) := by
    dsimp [p, higham21Eq21_9ProjectorFactor]
    exact_mod_cast hnat
  calc
    higham21Eq21_9OperatorCertificateCoefficient
        m n Aop AplusOp b x <=
      p * ((d * Aop) * (AplusOp * vecNorm2 x)) +
        AplusOp *
          (d * (Aop * vecNorm2 x) + d * (Aop * vecNorm2 x)) := by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left hinner hAplusOp
    _ = (p + 2) * d * (AplusOp * Aop) * vecNorm2 x := by ring
    _ = (Nat.min 3 (n - m + 2) : Nat) * d * kappa * vecNorm2 x := by
      rw [hfactor, hkappa]
    _ = higham21Eq21_9DimensionCoefficient m n kappa * vecNorm2 x := by
      rfl

/-- Higham, 2nd ed., Chapter 21, equation (21.9): the exact Euclidean
    first-order two-term coefficient is bounded by the printed normwise
    coefficient, derived from the supplied operator certificates. -/
theorem higham21_eq21_9_firstOrder_twoTermCoefficient_le
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (Aop AplusOp kappa : Real)
    (hmn : m <= n)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hb : b ≠ 0)
    (hA : rectOpNorm2Le A Aop)
    (hAplus : rectOpNorm2Le
      (undetAplusOfGramNonsingInv A) AplusOp)
    (hkappa : kappa = AplusOp * Aop)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_9NormwiseMatrixBudget Aop i j)
    (hDeltab : forall i,
      |Deltab i| <= higham21Eq21_9NormwiseRhsBudget b i) :
    higham21Eq21_9FirstOrderTwoTermCoefficient A DeltaA b Deltab <=
      higham21Eq21_9DimensionCoefficient m n kappa *
        vecNorm2 (rectMatMulVec (undetAplusOfGramNonsingInv A) b) :=
  (higham21_eq21_9_firstOrder_twoTermCoefficient_le_operatorCertificate
      A DeltaA b Deltab Aop AplusOp hmn hdet hb hA hAplus
      hDeltaA hDeltab).trans
    (higham21_eq21_9_operatorCertificateCoefficient_le_dimensionCoefficient
      A b Aop AplusOp kappa hmn hb hdet hA hAplus hkappa)

/-- Numerator form of the Euclidean first-order part of (21.9). -/
theorem higham21_eq21_9_firstOrder_numerator_le
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (Aop AplusOp kappa : Real)
    (hmn : m <= n)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hb : b ≠ 0)
    (hA : rectOpNorm2Le A Aop)
    (hAplus : rectOpNorm2Le
      (undetAplusOfGramNonsingInv A) AplusOp)
    (hkappa : kappa = AplusOp * Aop)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_9NormwiseMatrixBudget Aop i j)
    (hDeltab : forall i,
      |Deltab i| <= higham21Eq21_9NormwiseRhsBudget b i) :
    vecNorm2
        (higham21Eq21_7FirstOrder A DeltaA b Deltab
          (undetGramNonsingInv A)) <=
      higham21Eq21_9DimensionCoefficient m n kappa *
        vecNorm2 (rectMatMulVec (undetAplusOfGramNonsingInv A) b) :=
  (higham21_eq21_9_firstOrder_norm_le_twoTermCoefficient
      A DeltaA b Deltab hdet).trans
    (higham21_eq21_9_firstOrder_twoTermCoefficient_le
      A DeltaA b Deltab Aop AplusOp kappa hmn hdet hb hA hAplus
      hkappa hDeltaA hDeltab)

/-- A nonzero right-hand side gives a positive denominator in (21.9). -/
theorem higham21_eq21_9_base_solution_norm_pos
    {m n : Nat} (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hb : b ≠ 0) :
    0 < vecNorm2
      (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  have hRight : rectMatMul A Aplus = idMatrix m := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hAx : rectMatMulVec A x = b := by
    simpa [x] using higham21_eq21_9_base_system A Aplus b hRight
  have hx : x ≠ 0 := by
    intro hx0
    apply hb
    rw [<- hAx, hx0]
    ext i
    simp [rectMatMulVec]
  have hxnorm : vecNorm2 x ≠ 0 := by
    intro hzero
    apply hx
    funext i
    exact (vecNorm2_eq_zero_iff x).mp hzero i
  simpa [x, Aplus] using
    lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm hxnorm)

/-- Relative first-order form of source equation (21.9). -/
theorem higham21_eq21_9_relative_firstOrder
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (Aop AplusOp kappa eps : Real)
    (hmn : m <= n)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hb : b ≠ 0)
    (hA : rectOpNorm2Le A Aop)
    (hAplus : rectOpNorm2Le
      (undetAplusOfGramNonsingInv A) AplusOp)
    (hkappa : kappa = AplusOp * Aop)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_9NormwiseMatrixBudget Aop i j)
    (hDeltab : forall i,
      |Deltab i| <= higham21Eq21_9NormwiseRhsBudget b i) :
    vecNorm2
        (fun j => eps *
          higham21Eq21_7FirstOrder A DeltaA b Deltab
            (undetGramNonsingInv A) j) /
        vecNorm2
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b) <=
      |eps| * higham21Eq21_9DimensionCoefficient m n kappa := by
  let x : Fin n -> Real :=
    rectMatMulVec (undetAplusOfGramNonsingInv A) b
  let firstOrder : Fin n -> Real :=
    higham21Eq21_7FirstOrder A DeltaA b Deltab
      (undetGramNonsingInv A)
  let K : Real := higham21Eq21_9DimensionCoefficient m n kappa
  have hxpos : 0 < vecNorm2 x := by
    simpa [x] using higham21_eq21_9_base_solution_norm_pos A b hdet hb
  have hfirst : vecNorm2 firstOrder <= K * vecNorm2 x := by
    simpa [firstOrder, K, x] using
      higham21_eq21_9_firstOrder_numerator_le
        A DeltaA b Deltab Aop AplusOp kappa hmn hdet hb hA hAplus
        hkappa hDeltaA hDeltab
  have hscaled :
      vecNorm2 (fun j => eps * firstOrder j) <=
        |eps| * (K * vecNorm2 x) := by
    rw [vecNorm2_smul]
    exact mul_le_mul_of_nonneg_left hfirst (abs_nonneg eps)
  change vecNorm2 (fun j => eps * firstOrder j) / vecNorm2 x <=
    |eps| * K
  calc
    vecNorm2 (fun j => eps * firstOrder j) / vecNorm2 x <=
        (|eps| * (K * vecNorm2 x)) / vecNorm2 x :=
      div_le_div_of_nonneg_right hscaled hxpos.le
    _ = |eps| * K := by
      field_simp [ne_of_gt hxpos]
      <;> ring

/-- The smallness radius used to derive perturbed full row rank from the
    supplied operator certificates. -/
noncomputable def higham21Eq21_9RankStabilityRadius
    (m n : Nat) (eps kappa : Real) : Real :=
  |eps| * Real.sqrt ((m : Real) * (n : Real)) * kappa

/-- Equation (21.9) with the exact finite Theorem 21.1 endpoint.  Perturbed
    Gram nonsingularity is derived from the imported rank-stability theorem;
    the final term is the explicit `|eps|^2*C/||x||_2` remainder. -/
theorem higham21_eq21_9_relative_bound_with_fixed_radius_remainder
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (Aop AplusOp kappa : Real)
    (rho beta eps : Real) (hmn : m <= n)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hb : b ≠ 0)
    (hA : rectOpNorm2Le A Aop)
    (hAplus : rectOpNorm2Le
      (undetAplusOfGramNonsingInv A) AplusOp)
    (hkappa : kappa = AplusOp * Aop)
    (hDeltaA : forall i j,
      |DeltaA i j| <= higham21Eq21_9NormwiseMatrixBudget Aop i j)
    (hDeltab : forall i,
      |Deltab i| <= higham21Eq21_9NormwiseRhsBudget b i)
    (hsmall : higham21Eq21_9RankStabilityRadius m n eps kappa < 1)
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
      |eps| * higham21Eq21_9DimensionCoefficient m n kappa +
        (|eps| ^ 2 *
            higham21Eq21_7FixedRadiusCoefficient
              A DeltaA b Deltab (undetGramNonsingInv A) rho beta) /
          vecNorm2
            (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  obtain ⟨hm, hn⟩ :=
    higham21_eq21_9_dimensions_pos_of_rhs_ne_zero b hmn hb
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let d : Real := Real.sqrt ((m : Real) * (n : Real))
  let matrixRadius : Real := d * Aop
  let rankRadius : Real := higham21Eq21_9RankStabilityRadius m n eps kappa
  let firstOrder : Fin n -> Real :=
    higham21Eq21_7FirstOrder A DeltaA b Deltab
      (undetGramNonsingInv A)
  let remainder : Fin n -> Real :=
    higham21Eq21_7ExactRemainder A DeltaA b Deltab
      (undetGramNonsingInv A)
      (undetGramNonsingInv
        (higham21Eq21_7ScaledMatrix A DeltaA eps)) eps
  let K : Real := higham21Eq21_9DimensionCoefficient m n kappa
  let C : Real := higham21Eq21_7FixedRadiusCoefficient
    A DeltaA b Deltab (undetGramNonsingInv A) rho beta
  have hAop : 0 <= Aop := rectOpNorm2Le_radius_nonneg A hA
  have hAplusOp : 0 <= AplusOp :=
    rectOpNorm2Le_radius_nonneg Aplus hAplus
  have hmatrixRadius : 0 <= matrixRadius :=
    mul_nonneg (Real.sqrt_nonneg _) hAop
  have hDeltaOp : rectOpNorm2Le DeltaA matrixRadius := by
    simpa [matrixRadius, d] using
      higham21_eq21_9_matrix_perturbation_rectOpNorm2Le
        DeltaA Aop hAop hDeltaA
  have hScaledDelta :
      rectOpNorm2Le (fun i j => eps * DeltaA i j)
        (|eps| * matrixRadius) :=
    higham21_eq21_9_rectOpNorm2Le_const_mul_abs
      DeltaA eps matrixRadius hDeltaOp
  have hProduct0 :
      rectOpNorm2Le
        (rectMatMul Aplus (fun i j => eps * DeltaA i j))
        (AplusOp * (|eps| * matrixRadius)) :=
    rectOpNorm2Le_rectMatMul Aplus (fun i j => eps * DeltaA i j)
      hAplusOp hAplus hScaledDelta
  have hProduct :
      rectOpNorm2Le
        (rectMatMul Aplus (fun i j => eps * DeltaA i j)) rankRadius := by
    convert hProduct0 using 1
    simp only [rankRadius, higham21Eq21_9RankStabilityRadius,
      matrixRadius, d, hkappa]
    ring
  have hrankRadius : 0 <= rankRadius := by
    have hkappaNonneg : 0 <= kappa := by
      rw [hkappa]
      exact mul_nonneg hAplusOp hAop
    exact mul_nonneg
      (mul_nonneg (abs_nonneg eps) (Real.sqrt_nonneg _)) hkappaNonneg
  have hdet_eps0 :=
    higham21_theorem21_1_perturbed_gram_det_ne_zero_of_gram_det_ne_zero
      A (fun i j => eps * DeltaA i j) hdet hProduct
        hrankRadius (by simpa [rankRadius] using hsmall)
  have hdet_eps :
      Matrix.det
        (rectGram (higham21Eq21_7ScaledMatrix A DeltaA eps) :
          Matrix (Fin m) (Fin m) Real) ≠ 0 := by
    simpa [higham21Eq21_7ScaledMatrix] using hdet_eps0
  have hxpos : 0 < vecNorm2 x := by
    simpa [x, Aplus] using
      higham21_eq21_9_base_solution_norm_pos A b hdet hb
  have hfirst :
      vecNorm2 (fun j => eps * firstOrder j) / vecNorm2 x <=
        |eps| * K := by
    simpa [firstOrder, x, Aplus, K] using
      higham21_eq21_9_relative_firstOrder
        A DeltaA b Deltab Aop AplusOp kappa eps hmn hdet hb hA hAplus
        hkappa hDeltaA hDeltab
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

/-- Canonical first-order numerator form of equation (21.9).  Unlike the
    certificate-level theorem above, all three scalar parameters are fixed to
    exact rectangular operator norms, so the coefficient is the source
    `kappa_2(A)` rather than an arbitrary upper certificate. -/
theorem higham21_eq21_9_firstOrder_numerator_le_canonical
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (hmn : m <= n)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hb : b ≠ 0)
    (hDeltaA : forall i j,
      |DeltaA i j| <=
        higham21Eq21_9NormwiseMatrixBudget
          (higham21RectOpNorm2 A) i j)
    (hDeltab : forall i,
      |Deltab i| <= higham21Eq21_9NormwiseRhsBudget b i) :
    vecNorm2
        (higham21Eq21_7FirstOrder A DeltaA b Deltab
          (undetGramNonsingInv A)) <=
      higham21Eq21_9DimensionCoefficient m n
          (higham21Eq21_9Kappa2 A) *
        vecNorm2
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let Aop : Real := higham21RectOpNorm2 A
  let AplusOp : Real := higham21RectOpNorm2 Aplus
  have hA : rectOpNorm2Le A Aop := by
    simpa [Aop] using higham21_rectOpNorm2Le_exact A
  have hAplus : rectOpNorm2Le Aplus AplusOp := by
    simpa [AplusOp] using higham21_rectOpNorm2Le_exact Aplus
  have hkappa : higham21Eq21_9Kappa2 A = AplusOp * Aop := by
    simp [higham21Eq21_9Kappa2, higham21RectKappa2With,
      Aplus, Aop, AplusOp, mul_comm]
  simpa [Aplus, Aop, AplusOp] using
    (higham21_eq21_9_firstOrder_numerator_le
      A DeltaA b Deltab Aop AplusOp (higham21Eq21_9Kappa2 A)
      hmn hdet hb hA hAplus hkappa hDeltaA hDeltab)

/-- Higham, 2nd ed., Chapter 21, equation (21.9), in its literal asymptotic
    form with exact rectangular `kappa_2(A)`.  The returned remainder is the
    normalized exact remainder from (21.7) and is proved `O(t^2)` on a derived
    full-row-rank neighborhood. -/
theorem higham21_eq21_9_relative_asymptotic_bound
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) (hmn : m <= n)
    (hdet : Matrix.det
      (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (hb : b ≠ 0)
    (hDeltaA : forall i j,
      |DeltaA i j| <=
        higham21Eq21_9NormwiseMatrixBudget
          (higham21RectOpNorm2 A) i j)
    (hDeltab : forall i,
      |Deltab i| <= higham21Eq21_9NormwiseRhsBudget b i) :
    let x := rectMatMulVec (undetAplusOfGramNonsingInv A) b
    let E := higham21Eq21_9NormwiseMatrixBudget (higham21RectOpNorm2 A)
    let K := higham21Eq21_9DimensionCoefficient m n
      (higham21Eq21_9Kappa2 A)
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
  let E : Fin m -> Fin n -> Real :=
    higham21Eq21_9NormwiseMatrixBudget (higham21RectOpNorm2 A)
  let K : Real := higham21Eq21_9DimensionCoefficient m n
    (higham21Eq21_9Kappa2 A)
  have hm : 0 < m := higham21_row_dimension_pos_of_rhs_ne_zero b hb
  have hE : forall i j, 0 <= E i j := by
    intro i j
    simpa [E, higham21Eq21_9NormwiseMatrixBudget] using
      higham21RectOpNorm2_nonneg A
  have hxpos :
      0 < vecNorm2
        (rectMatMulVec (undetAplusOfGramNonsingInv A) b) :=
    higham21_eq21_9_base_solution_norm_pos A b hdet hb
  have hfirst :
      vecNorm2
          (higham21Eq21_7FirstOrder A DeltaA b Deltab
            (undetGramNonsingInv A)) <=
        K * vecNorm2
          (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
    simpa [K] using
      (higham21_eq21_9_firstOrder_numerator_le_canonical
        A DeltaA b Deltab hmn hdet hb hDeltaA hDeltab)
  simpa [E, K] using
    (higham21_eq21_7_euclidean_relative_asymptotic_bound_of_firstOrder_bound
      A DeltaA E b Deltab K hm hdet hE
      (by simpa [E] using hDeltaA) hxpos hfirst)

end NumStability
