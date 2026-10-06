import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation

namespace NumStability

open scoped BigOperators

/-!
# WeightedLimit

Canonical reusable module extracted without change from Higham20WeightedLimit.
-/

/-- A nonzero weight preserves the full-column-rank condition of the stacked
matrix `[A; B]`. -/
theorem lseWeightedMatrix_injective_of_lseStackedFullColumnRank
    {m n p : ℕ} {mu : ℝ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hmu : mu ≠ 0) (hstack : LSEStackedFullColumnRank A B) :
    Function.Injective (rectMatMulVec (lseWeightedMatrix mu A B)) := by
  intro x y hxy
  apply hstack
  ext i
  refine Fin.addCases
    (motive := fun i : Fin (m + p) =>
      rectMatMulVec (lseStackedMatrix A B) x i =
        rectMatMulVec (lseStackedMatrix A B) y i)
    ?left ?right i
  · intro i
    have hi := congrFun hxy (Fin.castAdd p i)
    rw [lseWeightedMatrix_mulVec, lseWeightedMatrix_mulVec] at hi
    simpa [lseStackedMatrix_mulVec, Fin.append_left] using hi
  · intro i
    have hi := congrFun hxy (Fin.natAdd m i)
    rw [lseWeightedMatrix_mulVec, lseWeightedMatrix_mulVec] at hi
    have hBi : rectMatMulVec B x i = rectMatMulVec B y i := by
      apply mul_left_cancel₀ hmu
      simpa [Fin.append_right] using hi
    simpa [lseStackedMatrix_mulVec, Fin.append_right] using hBi
/-- The canonical exact solution of the weighted problem (20.26), obtained
from the nonsingular Gram inverse of `[A; mu B]`.  Its definition is total;
the source rank assumptions and `mu ≠ 0` prove that it is the unique
least-squares solution. -/
noncomputable def higham20WeightedSolution {m n p : ℕ}
    (mu : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B : Fin p → Fin n → ℝ) (d : Fin p → ℝ) : Fin n → ℝ :=
  let W := lseWeightedMatrix mu A B
  lsAugmentedInverseActionBottom
    (lsAplusOfGramNonsingInv W) (lsGramNonsingInv W)
    (lseWeightedRhs mu b d) 0
/-- The basic penalty-energy estimate.  It is derived from weighted
optimality against the feasible LSE solution and the source Lagrange normal
equations; no boundedness or convergence hypothesis on the weighted branch is
used. -/
theorem lseWeightedMinimizer_energy_le_lagrange
    {m n p : ℕ} {mu : ℝ}
    {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {B : Fin p → Fin n → ℝ} {d : Fin p → ℝ}
    {x_mu y : Fin n → ℝ} {lambda : Fin p → ℝ}
    (hmin : IsLeastSquaresMinimizer
      (lseWeightedMatrix mu A B) (lseWeightedRhs mu b d) x_mu)
    (hy : IsLSEMinimizer A b B d y)
    (hlambda : ∀ j : Fin n,
      ∑ i : Fin m, A i j * lsResidualHigham A b y i =
        ∑ r : Fin p, B r j * lambda r) :
    vecNorm2 (rectMatMulVec A (fun j => x_mu j - y j)) ^ 2 +
        mu ^ 2 * vecNorm2 (rectMatMulVec B (fun j => x_mu j - y j)) ^ 2 ≤
      2 * vecNorm2 lambda *
        vecNorm2 (rectMatMulVec B (fun j => x_mu j - y j)) := by
  let v : Fin n → ℝ := fun j => x_mu j - y j
  have hx_eq : x_mu = fun j => y j + v j := by
    ext j
    dsimp [v]
    ring
  have hconstraint :
      lseConstraintResidual B d x_mu = rectMatMulVec B v := by
    ext r
    unfold lseConstraintResidual
    rw [congrFun (rectMatMulVec_sub B x_mu y) r, hy.1 r]
  have hhigham :
      (∑ j : Fin n,
        v j * (∑ i : Fin m, A i j * lsResidualHigham A b y i)) =
        ∑ r : Fin p, lambda r * rectMatMulVec B v r := by
    calc
      (∑ j : Fin n,
        v j * (∑ i : Fin m, A i j * lsResidualHigham A b y i)) =
          ∑ j : Fin n, v j * (∑ r : Fin p, B r j * lambda r) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hlambda j]
      _ = ∑ j : Fin n, ∑ r : Fin p,
            v j * (B r j * lambda r) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
      _ = ∑ r : Fin p, ∑ j : Fin n,
            v j * (B r j * lambda r) := by
            rw [Finset.sum_comm]
      _ = ∑ r : Fin p, lambda r * rectMatMulVec B v r := by
            apply Finset.sum_congr rfl
            intro r _
            unfold rectMatMulVec
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
  have hcross :
      (∑ j : Fin n,
        v j * (∑ i : Fin m, A i j * lsResidual A b y i)) =
        -(∑ r : Fin p, lambda r * rectMatMulVec B v r) := by
    have hsign :
        (∑ j : Fin n,
          v j * (∑ i : Fin m, A i j * lsResidual A b y i)) =
          -(∑ j : Fin n,
            v j * (∑ i : Fin m, A i j * lsResidualHigham A b y i)) := by
      calc
        (∑ j : Fin n,
          v j * (∑ i : Fin m, A i j * lsResidual A b y i)) =
            ∑ j : Fin n,
              v j * (- (∑ i : Fin m,
                A i j * lsResidualHigham A b y i)) := by
                apply Finset.sum_congr rfl
                intro j _
                congr 1
                rw [lsResidualHigham_eq_neg_lsResidual A b y]
                simp
        _ = -(∑ j : Fin n,
            v j * (∑ i : Fin m, A i j * lsResidualHigham A b y i)) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
    rw [hsign, hhigham]
  have hobj :
      lsObjective A b x_mu +
          mu ^ 2 * vecNorm2Sq (lseConstraintResidual B d x_mu) ≤
        lsObjective A b y := by
    calc
      lsObjective A b x_mu +
          mu ^ 2 * vecNorm2Sq (lseConstraintResidual B d x_mu) =
          lsObjective (lseWeightedMatrix mu A B)
            (lseWeightedRhs mu b d) x_mu :=
        (lseWeightedObjective_eq mu A b B d x_mu).symm
      _ ≤ lsObjective (lseWeightedMatrix mu A B)
            (lseWeightedRhs mu b d) y := hmin y
      _ = lsObjective A b y :=
        lseWeightedObjective_eq_of_feasible mu A b B d y hy.1
  have hexp := lsObjective_add_direction_eq A b y v
  rw [← hx_eq] at hexp
  rw [hexp, hcross, hconstraint] at hobj
  have hraw :
      vecNorm2Sq (rectMatMulVec A v) +
          mu ^ 2 * vecNorm2Sq (rectMatMulVec B v) ≤
        2 * (∑ r : Fin p, lambda r * rectMatMulVec B v r) := by
    linarith
  have hdot :
      (∑ r : Fin p, lambda r * rectMatMulVec B v r) ≤
        vecNorm2 lambda * vecNorm2 (rectMatMulVec B v) :=
    (le_abs_self _).trans
      (abs_vecInnerProduct_le_vecNorm2_mul lambda (rectMatMulVec B v))
  have hraw' := hraw.trans (mul_le_mul_of_nonneg_left hdot (by norm_num))
  simpa only [← vecNorm2_sq, v, mul_assoc] using hraw'

end NumStability
