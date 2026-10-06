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
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
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
import NumStability.Source.Higham.Chapter21.Equation11.UnderdeterminedSolve

/-!
# Source.Higham.Chapter21.Equation11.Scalar

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- The scalar square endpoint of equation (21.11).



namespace NumStability

set_option maxHeartbeats 1200000

/-- In the scalar square case the nullspace component of the first-order
    perturbation vanishes.  The remaining component therefore has the printed
    `n * eta * cond2(A)` bound with `n = 1`. -/
theorem higham21_eq21_11_firstOrder_norm_le_rowwise_cond2_scalar
    (A DeltaA : Fin 1 -> Fin 1 -> Real) (b : Fin 1 -> Real)
    {eta : Real}
    (hdet : Matrix.det (rectGram A : Matrix (Fin 1) (Fin 1) Real) ≠ 0)
    (heta : 0 <= eta)
    (hrow : forall i : Fin 1,
      rectRowNorm2 DeltaA i <= eta * rectRowNorm2 A i) :
    vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) <=
      (1 : Real) * eta *
        higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2
            (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  let Aplus : Fin 1 -> Fin 1 -> Real := undetAplusOfGramNonsingInv A
  let x : Fin 1 -> Real := rectMatMulVec Aplus b
  let z : Fin 1 -> Real := rectTransposeMulVec Aplus x
  let w : Fin 1 -> Real := rectTransposeMulVec DeltaA z
  let p : Fin 1 -> Real := fun j =>
    w j - rectMatMulVec Aplus (rectMatMulVec A w) j
  let v : Fin 1 -> Real := rectMatMulVec Aplus (rectMatMulVec DeltaA x)
  let q : Fin 1 -> Real :=
    rectMatMulVec Aplus
      (fun i => (0 : Real) - rectMatMulVec DeltaA x i)
  let B : Fin 1 -> Fin 1 -> Real := rectMatMul Aplus DeltaA
  let cond : Real := higham21Cond2With A Aplus
  let rho : Real := eta * Real.sqrt (1 : Real) * cond
  have hRight : rectMatMul A Aplus = idMatrix 1 := by
    simpa [Aplus] using
      higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero
        A hdet
  have hLeft : rectMatMul Aplus A = idMatrix 1 := by
    funext i j
    fin_cases i
    fin_cases j
    have h00 := congrFun (congrFun hRight (0 : Fin 1)) (0 : Fin 1)
    simpa [rectMatMul, idMatrix, mul_comm] using h00
  have hcond : 0 <= cond := by
    simpa [cond] using higham21Cond2With_nonneg A Aplus
  have hrho : 0 <= rho := by
    exact mul_nonneg (mul_nonneg heta (Real.sqrt_nonneg _)) hcond
  have hB : rectOpNorm2Le B rho := by
    simpa [B, rho, cond] using
      higham21_rectOpNorm2Le_pseudoinverse_product_of_row_bounds
        A DeltaA Aplus eta heta hrow
  have hv : vecNorm2 v <= rho * vecNorm2 x := by
    simpa [v, B, rectMatMulVec_rectMatMul] using hB x
  have hqEq : q = fun j => -v j := by
    ext j
    unfold q v rectMatMulVec
    rw [<- Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hq : vecNorm2 q <= rho * vecNorm2 x := by
    rw [hqEq, vecNorm2_neg]
    exact hv
  have hAw : rectMatMulVec Aplus (rectMatMulVec A w) = w := by
    rw [<- rectMatMulVec_rectMatMul, hLeft]
    ext i
    fin_cases i
    simp [rectMatMulVec, idMatrix]
  have hp : p = 0 := by
    ext j
    simp [p, hAw]
  have hfirst : higham21Eq21_11FirstOrder A DeltaA b = q := by
    ext j
    change w j - rectMatMulVec Aplus (rectMatMulVec A w) j -
        rectMatMulVec Aplus (rectMatMulVec DeltaA x) j = q j
    have hpj := congrFun hp j
    rw [hqEq]
    simp [p] at hpj
    dsimp [v]
    linarith
  rw [hfirst]
  have hsqrt : Real.sqrt (1 : Real) = 1 := by norm_num
  simpa [rho, cond, x, Aplus, hsqrt] using hq

/-- Dimension-polymorphic wrapper for the scalar first-order estimate.  The
    hypotheses `0 < m`, `m <= n`, and `n <= 1` force `m = n = 1`. -/
theorem higham21_eq21_11_firstOrder_norm_le_rowwise_cond2_of_card_le_one
    {m n : Nat} (A DeltaA : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    {eta : Real} (hm : 0 < m) (hmn : m <= n) (hn : n <= 1)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0)
    (heta : 0 <= eta)
    (hrow : forall i : Fin m,
      rectRowNorm2 DeltaA i <= eta * rectRowNorm2 A i) :
    vecNorm2 (higham21Eq21_11FirstOrder A DeltaA b) <=
      (n : Real) * eta *
        higham21Cond2With A (undetAplusOfGramNonsingInv A) *
          vecNorm2
            (rectMatMulVec (undetAplusOfGramNonsingInv A) b) := by
  have hm1 : m = 1 := by omega
  have hn1 : n = 1 := by omega
  subst m
  subst n
  simpa using
    higham21_eq21_11_firstOrder_norm_le_rowwise_cond2_scalar
      A DeltaA b hdet heta hrow









































































































































































































































end NumStability
