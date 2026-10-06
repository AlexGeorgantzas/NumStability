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
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GaussJordanAccumulation
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanStep

/-!
# Chapter14 Theorem05 ForwardError GJEAsymptoticFamilies

Canonical destination for material split out of
`NumStability.Algorithms.Ch14GJEAsymptoticFamilies` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- Entrywise `O(1)` matrix families are closed under matrix multiplication
in fixed finite dimension. -/
theorem ch14ext_matrixFamily_mul_family_isBigOOne {ι : Type*}
    {l : Filter ι} {n : ℕ}
    {M N : ι → Fin n → Fin n → ℝ}
    (hM : MatrixFamilyIsBigOOne l M) (hN : MatrixFamilyIsBigOOne l N) :
    MatrixFamilyIsBigOOne l (fun t => matMul n (M t) (N t)) := by
  intro i j
  simpa only [matMul, one_mul] using
    (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
      (hM i k).mul (hN k j)))

/-- An entrywise `O(1)` matrix family acting on a componentwise `O(1)` vector
family remains componentwise `O(1)` in fixed finite dimension. -/
theorem ch14ext_matrixFamily_mul_vectorFamily_isBigOOne {ι : Type*}
    {l : Filter ι} {n : ℕ}
    {M : ι → Fin n → Fin n → ℝ} {v : ι → Fin n → ℝ}
    (hM : MatrixFamilyIsBigOOne l M) (hv : VectorFamilyIsBigOOne l v) :
    VectorFamilyIsBigOOne l (fun t => matMulVec n (M t) (v t)) := by
  intro i
  simpa only [matMulVec, one_mul] using
    (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
      (hM i k).mul (hv k)))

/-- Componentwise absolute values preserve componentwise `O(1)`. -/
theorem ch14ext_vectorFamily_abs_isBigOOne {ι : Type*} {l : Filter ι}
    {n : ℕ} {v : ι → Fin n → ℝ} (hv : VectorFamilyIsBigOOne l v) :
    VectorFamilyIsBigOOne l (fun t i => |v t i|) := by
  intro i
  simpa only [Real.norm_eq_abs] using (hv i).norm_left

/-- A fixed matrix, viewed as a constant family, is entrywise `O(1)`. -/
theorem ch14ext_fixedMatrix_family_isBigOOne {ι : Type*} (l : Filter ι)
    {n : ℕ} (A : Fin n → Fin n → ℝ) :
    MatrixFamilyIsBigOOne l (fun _ : ι => A) := by
  intro i j
  exact Asymptotics.isBigO_const_const (A i j) one_ne_zero l

/-- A family of concrete executions supplying exactly the LU,
forward-substitution, and rounded Gauss-Jordan recurrence certificates used by
the pointwise (14.31) and (14.32) theorems.  The local boundedness fields are
data assumptions, not endpoint conclusions. -/
structure Ch14GJEConcreteFamily (ι : Type*) (l : Filter ι) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (start : ℕ) where
  model : ι → FPModel
  L_hat : ι → Fin n → Fin n → ℝ
  V : ι → ℕ → Fin n → Fin n → ℝ
  xseq : ι → ℕ → Fin n → ℝ
  x_hat : ι → Fin n → ℝ
  unit_tendsto_zero : Tendsto (fun t => (model t).u) l (𝓝 0)
  lu_certificate : ∀ t,
    LUBackwardError n A (L_hat t) (V t start) (gamma (model t) n)
  valid_n : ∀ t, gammaValid (model t) n
  dimension_pos : 1 ≤ n
  valid_three : ∀ t, gammaValid (model t) 3
  index_valid : ∀ q : ℕ, q < n - 1 → start + q < n
  final_matrix : ∀ t, V t (start + (n - 1)) = idMatrix n
  final_vector : ∀ t i, x_hat t i = xseq t (start + (n - 1)) i
  forward_start : ∀ t,
    xseq t start = fl_forwardSub (model t) n (L_hat t) b
  matrix_recurrence : ∀ t : ι, ∀ q : ℕ, (hq : q < n - 1) →
    V t (start + (q + 1)) =
      ch14ext_gjeStepMatrix (model t) n (V t (start + q))
        ⟨start + q, index_valid q hq⟩
  vector_recurrence : ∀ t : ι, ∀ q : ℕ, (hq : q < n - 1) →
    xseq t (start + (q + 1)) =
      ch14ext_gjeStepVec (model t) n (V t (start + q))
        ⟨start + q, index_valid q hq⟩ (xseq t (start + q))
  pivots_nonzero : ∀ t : ι, ∀ q : ℕ, (hq : q < n - 1) →
    V t (start + q) ⟨start + q, index_valid q hq⟩
      ⟨start + q, index_valid q hq⟩ ≠ 0
  L_hat_isBigO_one : MatrixFamilyIsBigOOne l L_hat
  U_hat_isBigO_one : MatrixFamilyIsBigOOne l (fun t => V t start)
  X_abs_isBigO_one : MatrixFamilyIsBigOOne l
    (fun t => ch14ext_gjeXabs n (ch14ext_gjeSeqStages n (V t))
      (ch14ext_gjeConstructedQ n (V t) start) start (n - 1))
  y_isBigO_one : VectorFamilyIsBigOOne l (fun t => xseq t start)
  x_hat_isBigO_one : VectorFamilyIsBigOOne l x_hat

/-- The residual envelope built from the constructed left inverse.  This is
deliberately distinct from the cumulative-product envelope used by (14.32). -/
noncomputable def ch14ext_gjeConcreteFamilyXabs
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (F : Ch14GJEConcreteFamily ι l n A b start) (t : ι) :
    Fin n → Fin n → ℝ :=
  ch14ext_gjeXabs n (ch14ext_gjeSeqStages n (F.V t))
    (ch14ext_gjeConstructedQ n (F.V t) start) start (n - 1)

/-- The absolute cumulative stage product in the literal forward endpoint.
No equality with `ch14ext_gjeConcreteFamilyXabs` is asserted. -/
noncomputable def ch14ext_gjeConcreteFamilyPabs
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (F : Ch14GJEConcreteFamily ι l n A b start) (t : ι) :
    Fin n → Fin n → ℝ :=
  ch14ext_absCumProd n (ch14ext_gjeSeqStages n (F.V t)) start (n - 1)

end Ch14Ext
end NumStability
