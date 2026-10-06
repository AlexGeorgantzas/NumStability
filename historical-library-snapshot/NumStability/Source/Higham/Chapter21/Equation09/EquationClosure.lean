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
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.Radius
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
import NumStability.Source.Higham.Chapter21.Equation04.UnderdeterminedSpec
import NumStability.Source.Higham.Chapter21.Equation07.UnderdeterminedSolve

/-!
# Source.Higham.Chapter21.Equation09.EquationClosure

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/




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




















































/-- The smallness radius used to derive perturbed full row rank from the
    supplied operator certificates. -/
noncomputable def higham21Eq21_9RankStabilityRadius
    (m n : Nat) (eps kappa : Real) : Real :=
  |eps| * Real.sqrt ((m : Real) * (n : Real)) * kappa


























































































































































































































































end NumStability
