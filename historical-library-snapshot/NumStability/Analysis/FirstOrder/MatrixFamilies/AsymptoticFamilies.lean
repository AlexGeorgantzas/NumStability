import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Analysis FirstOrder MatrixFamilies AsymptoticFamilies

Canonical destination for material split out of
`NumStability.Algorithms.Ch14AsymptoticFamilies` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- Entrywise local boundedness of a matrix family along a filter. -/
def MatrixFamilyIsBigOOne {ι : Type*} (l : Filter ι) {m n : ℕ}
    (M : ι → Fin m → Fin n → ℝ) : Prop :=
  ∀ i j, (fun t => M t i j) =O[l] (fun _ : ι => (1 : ℝ))

/-- Componentwise local boundedness of a vector family along a filter. -/
def VectorFamilyIsBigOOne {ι : Type*} (l : Filter ι) {n : ℕ}
    (v : ι → Fin n → ℝ) : Prop :=
  ∀ i, (fun t => v t i) =O[l] (fun _ : ι => (1 : ℝ))

theorem matrixFamily_abs_isBigOOne {ι : Type*} {l : Filter ι} {m n : ℕ}
    {M : ι → Fin m → Fin n → ℝ} (hM : MatrixFamilyIsBigOOne l M) :
    MatrixFamilyIsBigOOne l (fun t i j => |M t i j|) := by
  intro i j
  simpa only [Real.norm_eq_abs] using (hM i j).norm_left

theorem fixedMatrix_mul_family_isBigOOne {ι : Type*} {l : Filter ι}
    {n : ℕ} (A : Fin n → Fin n → ℝ)
    {M : ι → Fin n → Fin n → ℝ} (hM : MatrixFamilyIsBigOOne l M) :
    MatrixFamilyIsBigOOne l (fun t => matMul n A (M t)) := by
  intro i j
  simpa only [matMul] using
    (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
      (hM k j).const_mul_left (A i k)))

theorem family_mul_fixedMatrix_isBigOOne {ι : Type*} {l : Filter ι}
    {n : ℕ} {M : ι → Fin n → Fin n → ℝ}
    (A : Fin n → Fin n → ℝ) (hM : MatrixFamilyIsBigOOne l M) :
    MatrixFamilyIsBigOOne l (fun t => matMul n (M t) A) := by
  intro i j
  have hsum := Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
    (hM i k).const_mul_left (A k j))
  simpa only [matMul, mul_comm] using hsum

theorem fixedMatrix_mul_vectorFamily_isBigOOne {ι : Type*} {l : Filter ι}
    {n : ℕ} (A : Fin n → Fin n → ℝ) {v : ι → Fin n → ℝ}
    (hv : VectorFamilyIsBigOOne l v) :
    VectorFamilyIsBigOOne l (fun t => matMulVec n A (v t)) := by
  intro i
  simpa only [matMulVec] using
    (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
      (hv k).const_mul_left (A i k)))

theorem matrixFamily_mul_fixedVector_isBigOOne {ι : Type*} {l : Filter ι}
    {n : ℕ} {M : ι → Fin n → Fin n → ℝ} (v : Fin n → ℝ)
    (hM : MatrixFamilyIsBigOOne l M) :
    VectorFamilyIsBigOOne l (fun t => matMulVec n (M t) v) := by
  intro i
  have hsum := Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
    (hM i k).const_mul_left (v k))
  simpa only [matMulVec, mul_comm] using hsum

/-- In fixed finite dimension, entrywise `O(g)` control implies `O(g)`
control of the matrix infinity norm. -/
theorem matrixFamily_infNorm_isBigO {ι : Type*} {l : Filter ι} {n : ℕ}
    {M : ι → Fin n → Fin n → ℝ} {g : ι → ℝ}
    (hM : ∀ i j, (fun t => M t i j) =O[l] g) :
    (fun t => infNorm (M t)) =O[l] g := by
  let total : ι → ℝ := fun t => ∑ i : Fin n, ∑ j : Fin n, |M t i j|
  have htotal : total =O[l] g := by
    dsimp [total]
    apply Asymptotics.IsBigO.sum
    intro i _hi
    apply Asymptotics.IsBigO.sum
    intro j _hj
    simpa only [Real.norm_eq_abs] using (hM i j).norm_left
  have hnorm_total : (fun t => infNorm (M t)) =O[l] total := by
    apply Asymptotics.IsBigO.of_norm_le
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (infNorm_nonneg (M t))]
    apply infNorm_le_of_row_sum_le
    · intro i
      exact Finset.single_le_sum
        (fun a _ => Finset.sum_nonneg (fun j _ => abs_nonneg (M t a j)))
        (Finset.mem_univ i)
    · exact Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => abs_nonneg (M t i j)))
  exact hnorm_total.trans htotal

end Ch14Ext
end NumStability
