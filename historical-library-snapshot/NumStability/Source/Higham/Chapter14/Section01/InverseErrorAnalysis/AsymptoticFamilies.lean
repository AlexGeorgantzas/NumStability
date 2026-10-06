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
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ForwardErrorEndpoint

/-!
# Chapter14 Section01 InverseErrorAnalysis AsymptoticFamilies

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

theorem rightResidualEnvelope_family_isBigOOne {ι : Type*} {l : Filter ι}
    (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    {X : ι → Fin n → Fin n → ℝ} (hX : MatrixFamilyIsBigOOne l X) :
    MatrixFamilyIsBigOOne l
      (fun t => ch14ext_rightResidualEnvelopeRemainder n A A_inv (X t)) := by
  have hAbsX := matrixFamily_abs_isBigOOne hX
  have hAX := fixedMatrix_mul_family_isBigOOne (absMatrix n A) hAbsX
  have hAinvAX := fixedMatrix_mul_family_isBigOOne (absMatrix n A_inv) hAX
  intro i j
  simpa only [ch14ext_rightResidualEnvelopeRemainder, matMul, absMatrix] using
    hAinvAX i j

theorem leftResidualEnvelope_family_isBigOOne {ι : Type*} {l : Filter ι}
    (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    {Y : ι → Fin n → Fin n → ℝ} (hY : MatrixFamilyIsBigOOne l Y) :
    MatrixFamilyIsBigOOne l
      (fun t => ch14ext_leftResidualEnvelopeRemainder n A A_inv (Y t)) := by
  have hAbsY := matrixFamily_abs_isBigOOne hY
  let B : Fin n → Fin n → ℝ := matMul n (absMatrix n A) (absMatrix n A_inv)
  have hYB := family_mul_fixedMatrix_isBigOOne B hAbsY
  intro i j
  simpa only [ch14ext_leftResidualEnvelopeRemainder, B, matMul, absMatrix,
    Finset.mul_sum] using hYB i j

/-- A genuine vanishing perturbation family for equation (14.3).  Local
boundedness of the inverse family is the minimal uniformity needed to make the
coefficient hidden by `O(epsilon^2)` independent of the family index. -/
structure Ch14Eq143Family (ι : Type*) (l : Filter ι) (n : ℕ)
    (A : Fin n → Fin n → ℝ) where
  scale : ι → ℝ
  perturbation : ι → Fin n → Fin n → ℝ
  approxInverse : ι → Fin n → Fin n → ℝ
  scale_tendsto_zero : Tendsto scale l (𝓝 0)
  scale_nonneg : ∀ t, 0 ≤ scale t
  perturbation_bound : ∀ t i j,
    |perturbation t i j| ≤ scale t * |A i j|
  perturbed_inverse_equation : ∀ t i j,
    ∑ k : Fin n, (A i k + perturbation t i k) * approxInverse t k j =
      if i = j then 1 else 0
  approxInverse_isBigO_one : MatrixFamilyIsBigOOne l approxInverse

/-- The actual varying-family remainder in (14.3). -/
noncomputable def ch14ext_eq14_3_familyRemainder {ι : Type*} {l : Filter ι}
    (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    (F : Ch14Eq143Family ι l n A) (i j : Fin n) (t : ι) : ℝ :=
  ch14ext_eq14_3_quadraticRemainder n A A_inv (F.approxInverse t)
    i j (F.scale t)

/-- The coefficient multiplying `epsilon^2` in (14.3) is uniformly `O(1)`
for a locally bounded inverse family. -/
theorem ch14ext_eq14_3_familyRemainder_isBigO {ι : Type*} {l : Filter ι}
    (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    (F : Ch14Eq143Family ι l n A) (i j : Fin n) :
    (fun t => ch14ext_eq14_3_familyRemainder n A A_inv F i j t)
      =O[l] (fun t => F.scale t ^ 2) := by
  have hY := matrixFamily_abs_isBigOOne F.approxInverse_isBigO_one
  have h1 := fixedMatrix_mul_family_isBigOOne (absMatrix n A) hY
  have h2 := fixedMatrix_mul_family_isBigOOne (absMatrix n A_inv) h1
  have h3 := fixedMatrix_mul_family_isBigOOne (absMatrix n A) h2
  have h4 := fixedMatrix_mul_family_isBigOOne (absMatrix n A_inv) h3
  have hCoeff :
      (fun t => ∑ k1 : Fin n, |A_inv i k1| *
        (∑ k2 : Fin n, |A k1 k2| *
          (∑ m1 : Fin n, |A_inv k2 m1| *
            (∑ m2 : Fin n, |A m1 m2| * |F.approxInverse t m2 j|))))
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa only [matMul, absMatrix] using h4 i j
  have hsq : (fun t => F.scale t ^ 2) =O[l] (fun t => F.scale t ^ 2) :=
    Asymptotics.isBigO_refl _ l
  simpa only [ch14ext_eq14_3_familyRemainder,
    ch14ext_eq14_3_quadraticRemainder, mul_one] using hsq.mul hCoeff

/-- Pointwise source inequality (14.3) for every member of the family. -/
theorem ch14ext_eq14_3_family_bound {ι : Type*} {l : Filter ι}
    (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    (F : Ch14Eq143Family ι l n A)
    (hInv : IsLeftInverse n A A_inv) (hRInv : IsRightInverse n A A_inv) :
    ∀ t i j, |A_inv i j - F.approxInverse t i j| ≤
      F.scale t * (∑ k1 : Fin n, |A_inv i k1| *
        (∑ k2 : Fin n, |A k1 k2| * |A_inv k2 j|)) +
      ch14ext_eq14_3_familyRemainder n A A_inv F i j t := by
  intro t i j
  simpa only [ch14ext_eq14_3_familyRemainder] using
    ch14ext_eq14_3_forward_error_endpoint n A A_inv (F.approxInverse t)
      (F.perturbation t) (F.scale t) (F.scale_nonneg t)
      (F.perturbation_bound t) hInv hRInv (F.perturbed_inverse_equation t) i j

/-- Genuine family-level closure of Higham (14.3): the displayed first-order
bound holds memberwise and its varying remainder is uniformly `O(epsilon^2)`
along a family with `epsilon -> 0`. -/
theorem ch14ext_eq14_3_vanishing_family_endpoint {ι : Type*} {l : Filter ι}
    [NeBot l]
    (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    (F : Ch14Eq143Family ι l n A)
    (hInv : IsLeftInverse n A A_inv) (hRInv : IsRightInverse n A A_inv) :
    (∀ t i j, |A_inv i j - F.approxInverse t i j| ≤
        F.scale t * (∑ k1 : Fin n, |A_inv i k1| *
          (∑ k2 : Fin n, |A k1 k2| * |A_inv k2 j|)) +
        ch14ext_eq14_3_familyRemainder n A A_inv F i j t) ∧
      ∀ i j,
        (fun t => ch14ext_eq14_3_familyRemainder n A A_inv F i j t)
          =O[l] (fun t => F.scale t ^ 2) := by
  exact ⟨ch14ext_eq14_3_family_bound n A A_inv F hInv hRInv,
    ch14ext_eq14_3_familyRemainder_isBigO n A A_inv F⟩

/-- A vanishing-roundoff family of Method 1 executions.  The only uniform
assumption is local boundedness of the computed inverse entries. -/
structure Ch14Eq146Family (ι : Type*) (l : Filter ι) (n : ℕ)
    (L : Fin n → Fin n → ℝ) where
  model : ι → FPModel
  unit_tendsto_zero : Tendsto (fun t => (model t).u) l (𝓝 0)
  valid : ∀ t, gammaValid (model t) n
  computedInverse_isBigO_one : MatrixFamilyIsBigOOne l
    (fun t i j =>
      fl_forwardSub (model t) n L (fun k => if k = j then 1 else 0) i)

/-- A family of approximate right inverses satisfying the source residual
model, with the local boundedness needed for a uniform remainder. -/
structure Ch14Problem145RightFamily (ι : Type*) (l : Filter ι) (n : ℕ)
    (A : Fin n → Fin n → ℝ) where
  model : ι → FPModel
  inverse : ι → Fin n → Fin n → ℝ
  unit_tendsto_zero : Tendsto (fun t => (model t).u) l (𝓝 0)
  valid : ∀ t, gammaValid (model t) (n + 1)
  residual : ∀ t i j,
    |inverseRightResidual n A (inverse t) i j| ≤
      (model t).u * ∑ k : Fin n, |A i k| * |inverse t k j|
  inverse_isBigO_one : MatrixFamilyIsBigOOne l inverse

/-- A family of approximate left inverses satisfying the source residual
model. -/
structure Ch14Problem145LeftFamily (ι : Type*) (l : Filter ι) (n : ℕ)
    (A : Fin n → Fin n → ℝ) where
  model : ι → FPModel
  inverse : ι → Fin n → Fin n → ℝ
  unit_tendsto_zero : Tendsto (fun t => (model t).u) l (𝓝 0)
  valid : ∀ t, gammaValid (model t) (n + 1)
  residual : ∀ t i j,
    |inverseLeftResidual n A (inverse t) i j| ≤
      (model t).u * ∑ k : Fin n, |inverse t i k| * |A k j|
  inverse_isBigO_one : MatrixFamilyIsBigOOne l inverse

end Ch14Ext
end NumStability
