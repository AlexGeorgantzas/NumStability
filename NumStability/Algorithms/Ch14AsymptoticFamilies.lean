-- Algorithms/Ch14AsymptoticFamilies.lean
--
-- Genuine vanishing-roundoff families for Higham, Chapter 14.
--
-- A pointwise formula of the form `u^2 * C` is not, by itself, a uniform
-- `O(u^2)` statement when the computed matrix hidden in `C` also varies with
-- the precision.  This module supplies the missing family-level contracts and
-- proves the corresponding Landau statements.  The only uniformity contract
-- imposed on a computed matrix is entrywise local boundedness (`O(1)`); no
-- forward-error conclusion is assumed.

import NumStability.Algorithms.Ch14ForwardErrorEndpoint
import Mathlib.Analysis.Asymptotics.Lemmas

namespace NumStability.Ch14Ext

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

/-! ## Uniform finite-dimensional family vocabulary -/

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

private theorem composed_gammaUnitCoefficient_isBigO_one {ι : Type*}
    {l : Filter ι} (k : ℕ) {u : ι → ℝ} (hu : Tendsto u l (𝓝 0)) :
    (fun t => ch14ext_gammaUnitCoefficientScalar k (u t))
      =O[l] (fun _ : ι => (1 : ℝ)) := by
  simpa only [Function.comp_apply] using
    (ch14ext_gammaUnitCoefficientScalar_isBigO_one k).comp_tendsto hu

private theorem composed_gammaQuadraticCoefficient_isBigO_one {ι : Type*}
    {l : Filter ι} (k : ℕ) {u : ι → ℝ} (hu : Tendsto u l (𝓝 0)) :
    (fun t => ch14ext_gammaQuadraticCoefficientScalar k (u t))
      =O[l] (fun _ : ι => (1 : ℝ)) := by
  simpa only [Function.comp_apply] using
    (ch14ext_gammaQuadraticCoefficientScalar_isBigO_one k).comp_tendsto hu

/-! ## Equation (14.3) -/

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

/-! ## Equation (14.6) -/

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

/-- The Method 1 inverse produced at one member of a family. -/
noncomputable def ch14ext_eq14_6_familyX {ι : Type*} {l : Filter ι}
    (n : ℕ) (L : Fin n → Fin n → ℝ) (F : Ch14Eq146Family ι l n L)
    (t : ι) : Fin n → Fin n → ℝ :=
  fun i j => fl_forwardSub (F.model t) n L
    (fun k => if k = j then 1 else 0) i

/-- The actual varying quadratic remainder in the Method 1 endpoint. -/
noncomputable def ch14ext_eq14_6_familyRemainder {ι : Type*} {l : Filter ι}
    (n : ℕ) (L L_inv : Fin n → Fin n → ℝ)
    (F : Ch14Eq146Family ι l n L) (i j : Fin n) (t : ι) : ℝ :=
  (F.model t).u ^ 2 *
    (ch14ext_gammaQuadraticCoefficient (F.model t) n *
        (∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
      (ch14ext_gammaUnitCoefficient (F.model t) n) ^ 2 *
        (∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| *
            ch14ext_rightResidualEnvelopeRemainder n L L_inv
              (ch14ext_eq14_6_familyX n L F t) k₂ j)))

/-- The Method 1 remainder is uniformly `O(u^2)` for a locally bounded
computed-inverse family. -/
theorem ch14ext_eq14_6_familyRemainder_isBigO {ι : Type*} {l : Filter ι}
    (n : ℕ) (L L_inv : Fin n → Fin n → ℝ)
    (F : Ch14Eq146Family ι l n L) (i j : Fin n) :
    (fun t => ch14ext_eq14_6_familyRemainder n L L_inv F i j t)
      =O[l] (fun t => (F.model t).u ^ 2) := by
  have hq :
      (fun t => ch14ext_gammaQuadraticCoefficient (F.model t) n)
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa [ch14ext_gammaQuadraticCoefficientScalar,
      ch14ext_gammaQuadraticCoefficient] using
      (composed_gammaQuadraticCoefficient_isBigO_one n F.unit_tendsto_zero)
  have hu :
      (fun t => ch14ext_gammaUnitCoefficient (F.model t) n)
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa [ch14ext_gammaUnitCoefficientScalar,
      ch14ext_gammaUnitCoefficient] using
      (composed_gammaUnitCoefficient_isBigO_one n F.unit_tendsto_zero)
  have hu_sq :
      (fun t => (ch14ext_gammaUnitCoefficient (F.model t) n) ^ 2)
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa [pow_two] using hu.mul hu
  let base : ℝ :=
    matMul n (absMatrix n L_inv)
      (matMul n (absMatrix n L) (absMatrix n L_inv)) i j
  have hbase : (fun _ : ι => base) =O[l] (fun _ : ι => (1 : ℝ)) :=
    Asymptotics.isBigO_const_const base one_ne_zero l
  have hR := rightResidualEnvelope_family_isBigOOne n L L_inv
    F.computedInverse_isBigO_one
  have hLR := fixedMatrix_mul_family_isBigOOne (absMatrix n L) hR
  have hLIR := fixedMatrix_mul_family_isBigOOne (absMatrix n L_inv) hLR
  have hterm1 :
      (fun t => ch14ext_gammaQuadraticCoefficient (F.model t) n * base)
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa using hq.mul hbase
  have hterm2 :
      (fun t => (ch14ext_gammaUnitCoefficient (F.model t) n) ^ 2 *
        matMul n (absMatrix n L_inv)
          (matMul n (absMatrix n L)
            (ch14ext_rightResidualEnvelopeRemainder n L L_inv
              (ch14ext_eq14_6_familyX n L F t))) i j)
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa [ch14ext_eq14_6_familyX] using hu_sq.mul (hLIR i j)
  have hcoeff := hterm1.add hterm2
  have hsq : (fun t => (F.model t).u ^ 2)
      =O[l] (fun t => (F.model t).u ^ 2) :=
    Asymptotics.isBigO_refl _ l
  simpa [ch14ext_eq14_6_familyRemainder, base, matMul, absMatrix]
    using hsq.mul hcoeff

/-- Pointwise Method 1 inequality with a genuinely uniform family remainder. -/
theorem ch14ext_eq14_6_vanishing_family_endpoint {ι : Type*} {l : Filter ι}
    [NeBot l]
    (n : ℕ) (L L_inv : Fin n → Fin n → ℝ)
    (F : Ch14Eq146Family ι l n L)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv) :
    (∀ t i j,
      |ch14ext_eq14_6_familyX n L F t i j - L_inv i j| ≤
        ((n : ℝ) * (F.model t).u) *
          (∑ k₁ : Fin n, |L_inv i k₁| *
            (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
          ch14ext_eq14_6_familyRemainder n L L_inv F i j t) ∧
      ∀ i j,
        (fun t => ch14ext_eq14_6_familyRemainder n L L_inv F i j t)
          =O[l] (fun t => (F.model t).u ^ 2) := by
  constructor
  · intro t i j
    simpa [ch14ext_eq14_6_familyX, ch14ext_eq14_6_familyRemainder] using
      (ch14ext_eq14_6_method1_forward_error_endpoint n (F.model t)
        L L_inv hL_diag hLT hInv (F.valid t) i j)
  · exact ch14ext_eq14_6_familyRemainder_isBigO n L L_inv F

/-! ## Problem 14.5 -/

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

/-- The varying right-inverse remainder from Problem 14.5. -/
noncomputable def ch14ext_problem14_5_right_familyRemainder
    {ι : Type*} {l : Filter ι} (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (F : Ch14Problem145RightFamily ι l n A) (i : Fin n) (t : ι) : ℝ :=
  (F.model t).u ^ 2 *
    (ch14ext_gammaQuadraticCoefficient (F.model t) (n + 1) *
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A)
            (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
      ch14ext_gammaUnitCoefficient (F.model t) (n + 1) *
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A)
            (matMulVec n
              (ch14ext_rightResidualEnvelopeRemainder n A A_inv (F.inverse t))
              (absVec n b))) i)

theorem ch14ext_problem14_5_right_familyRemainder_isBigO
    {ι : Type*} {l : Filter ι} (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (F : Ch14Problem145RightFamily ι l n A) (i : Fin n) :
    (fun t => ch14ext_problem14_5_right_familyRemainder
      n A A_inv b F i t) =O[l] (fun t => (F.model t).u ^ 2) := by
  have hq :
      (fun t => ch14ext_gammaQuadraticCoefficient (F.model t) (n + 1))
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa [ch14ext_gammaQuadraticCoefficientScalar,
      ch14ext_gammaQuadraticCoefficient] using
      (composed_gammaQuadraticCoefficient_isBigO_one (n + 1)
        F.unit_tendsto_zero)
  have hu :
      (fun t => ch14ext_gammaUnitCoefficient (F.model t) (n + 1))
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa [ch14ext_gammaUnitCoefficientScalar,
      ch14ext_gammaUnitCoefficient] using
      (composed_gammaUnitCoefficient_isBigO_one (n + 1)
        F.unit_tendsto_zero)
  let base : ℝ :=
    matMulVec n (absMatrix n A_inv)
      (matMulVec n (absMatrix n A)
        (matMulVec n (absMatrix n A_inv) (absVec n b))) i
  have hbase : (fun _ : ι => base) =O[l] (fun _ : ι => (1 : ℝ)) :=
    Asymptotics.isBigO_const_const base one_ne_zero l
  have hR := rightResidualEnvelope_family_isBigOOne n A A_inv
    F.inverse_isBigO_one
  have hRb := matrixFamily_mul_fixedVector_isBigOOne (absVec n b) hR
  have hARb := fixedMatrix_mul_vectorFamily_isBigOOne (absMatrix n A) hRb
  have hAinvARb :=
    fixedMatrix_mul_vectorFamily_isBigOOne (absMatrix n A_inv) hARb
  have hterm1 :
      (fun t => ch14ext_gammaQuadraticCoefficient (F.model t) (n + 1) * base)
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa using hq.mul hbase
  have hterm2 :
      (fun t => ch14ext_gammaUnitCoefficient (F.model t) (n + 1) *
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A)
            (matMulVec n
              (ch14ext_rightResidualEnvelopeRemainder n A A_inv (F.inverse t))
              (absVec n b))) i) =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa using hu.mul (hAinvARb i)
  have hcoeff := hterm1.add hterm2
  have hsq : (fun t => (F.model t).u ^ 2)
      =O[l] (fun t => (F.model t).u ^ 2) :=
    Asymptotics.isBigO_refl _ l
  simpa [ch14ext_problem14_5_right_familyRemainder, base]
    using hsq.mul hcoeff

/-- Genuine family-level right-inverse endpoint for Problem 14.5. -/
theorem ch14ext_problem14_5_right_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x b : Fin n → ℝ)
    (F : Ch14Problem145RightFamily ι l n A)
    (hLeft : IsLeftInverse n A A_inv) (hsolve : matMulVec n A x = b) :
    (∀ t i,
      let x_hat := fl_matVec (F.model t) n n (F.inverse t) b
      |x_hat i - x i| ≤
        (((n + 1 : ℕ) : ℝ) * (F.model t).u) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A)
              (matMulVec n (absMatrix n A_inv) (absVec n b))) i +
        ch14ext_problem14_5_right_familyRemainder n A A_inv b F i t) ∧
      ∀ i, (fun t => ch14ext_problem14_5_right_familyRemainder
        n A A_inv b F i t) =O[l] (fun t => (F.model t).u ^ 2) := by
  constructor
  · intro t i
    simpa [ch14ext_problem14_5_right_familyRemainder] using
      (ch14ext_problem14_5_right_inverse_solve_forward_error_endpoint
        n (F.model t) A A_inv (F.inverse t) x b (F.valid t) hLeft hsolve
        (F.residual t) i)
  · exact ch14ext_problem14_5_right_familyRemainder_isBigO n A A_inv b F

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

noncomputable def ch14ext_problem14_5_left_familyRemainder
    {ι : Type*} {l : Filter ι} (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (F : Ch14Problem145LeftFamily ι l n A) (i : Fin n) (t : ι) : ℝ :=
  (F.model t).u ^ 2 *
    (ch14ext_gammaQuadraticCoefficient (F.model t) (n + 1) *
        matMulVec n (absMatrix n A_inv)
          (matMulVec n (absMatrix n A) (absVec n x)) i +
      ch14ext_gammaUnitCoefficient (F.model t) (n + 1) *
        matMulVec n
          (ch14ext_leftResidualEnvelopeRemainder n A A_inv (F.inverse t))
          (matMulVec n (absMatrix n A) (absVec n x)) i)

theorem ch14ext_problem14_5_left_familyRemainder_isBigO
    {ι : Type*} {l : Filter ι} (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (F : Ch14Problem145LeftFamily ι l n A) (i : Fin n) :
    (fun t => ch14ext_problem14_5_left_familyRemainder
      n A A_inv x F i t) =O[l] (fun t => (F.model t).u ^ 2) := by
  have hq :
      (fun t => ch14ext_gammaQuadraticCoefficient (F.model t) (n + 1))
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa [ch14ext_gammaQuadraticCoefficientScalar,
      ch14ext_gammaQuadraticCoefficient] using
      (composed_gammaQuadraticCoefficient_isBigO_one (n + 1)
        F.unit_tendsto_zero)
  have hu :
      (fun t => ch14ext_gammaUnitCoefficient (F.model t) (n + 1))
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa [ch14ext_gammaUnitCoefficientScalar,
      ch14ext_gammaUnitCoefficient] using
      (composed_gammaUnitCoefficient_isBigO_one (n + 1)
        F.unit_tendsto_zero)
  let base : ℝ := matMulVec n (absMatrix n A_inv)
    (matMulVec n (absMatrix n A) (absVec n x)) i
  have hbase : (fun _ : ι => base) =O[l] (fun _ : ι => (1 : ℝ)) :=
    Asymptotics.isBigO_const_const base one_ne_zero l
  have hR := leftResidualEnvelope_family_isBigOOne n A A_inv
    F.inverse_isBigO_one
  let v : Fin n → ℝ := matMulVec n (absMatrix n A) (absVec n x)
  have hRv := matrixFamily_mul_fixedVector_isBigOOne v hR
  have hterm1 :
      (fun t => ch14ext_gammaQuadraticCoefficient (F.model t) (n + 1) * base)
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa using hq.mul hbase
  have hterm2 :
      (fun t => ch14ext_gammaUnitCoefficient (F.model t) (n + 1) *
        matMulVec n
          (ch14ext_leftResidualEnvelopeRemainder n A A_inv (F.inverse t))
          v i) =O[l] (fun _ : ι => (1 : ℝ)) := by
    simpa using hu.mul (hRv i)
  have hcoeff := hterm1.add hterm2
  have hsq : (fun t => (F.model t).u ^ 2)
      =O[l] (fun t => (F.model t).u ^ 2) :=
    Asymptotics.isBigO_refl _ l
  simpa [ch14ext_problem14_5_left_familyRemainder, base, v]
    using hsq.mul hcoeff

/-- Genuine family-level left-inverse endpoint for Problem 14.5. -/
theorem ch14ext_problem14_5_left_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (F : Ch14Problem145LeftFamily ι l n A)
    (hRight : IsRightInverse n A A_inv) :
    (∀ t i,
      let b := matMulVec n A x
      let y_hat := fl_matVec (F.model t) n n (F.inverse t) b
      |y_hat i - x i| ≤
        (((n + 1 : ℕ) : ℝ) * (F.model t).u) *
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n A) (absVec n x)) i +
        ch14ext_problem14_5_left_familyRemainder n A A_inv x F i t) ∧
      ∀ i, (fun t => ch14ext_problem14_5_left_familyRemainder
        n A A_inv x F i t) =O[l] (fun t => (F.model t).u ^ 2) := by
  constructor
  · intro t i
    simpa [ch14ext_problem14_5_left_familyRemainder] using
      (ch14ext_problem14_5_left_inverse_solve_forward_error_endpoint
        n (F.model t) A A_inv (F.inverse t) x (F.valid t) hRight
        (F.residual t) i)
  · exact ch14ext_problem14_5_left_familyRemainder_isBigO n A A_inv x F

/-! ## Equation (14.7) -/

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

/-- The matrix product defining `cond(L⁻¹)` has infinity norm at most the
repository Skeel condition number. -/
theorem ch14ext_eq14_7_inverseProduct_infNorm_le_condSkeel
    (n : ℕ) (hn : 0 < n) (L L_inv : Fin n → Fin n → ℝ) :
    infNorm (matMul n (absMatrix n L) (absMatrix n L_inv)) ≤
      condSkeel n hn L_inv L := by
  apply infNorm_le_of_row_sum_le
  · intro i
    have hentry : ∀ j : Fin n,
        |matMul n (absMatrix n L) (absMatrix n L_inv) i j| =
          ∑ k : Fin n, |L i k| * |L_inv k j| := by
      intro j
      rw [abs_of_nonneg]
      · rfl
      · exact Finset.sum_nonneg
          (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    calc
      ∑ j : Fin n,
          |matMul n (absMatrix n L) (absMatrix n L_inv) i j| =
          ∑ j : Fin n, ∑ k : Fin n, |L i k| * |L_inv k j| :=
        Finset.sum_congr rfl (fun j _ => hentry j)
      _ = ∑ k : Fin n, ∑ j : Fin n, |L i k| * |L_inv k j| :=
        Finset.sum_comm
      _ = ∑ k : Fin n, |L i k| * ∑ j : Fin n, |L_inv k j| := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [Finset.mul_sum]
      _ ≤ condSkeel n hn L_inv L := by
        unfold condSkeel
        exact Finset.le_sup'
          (fun a => ∑ k : Fin n, |L a k| * ∑ j : Fin n, |L_inv k j|)
          (Finset.mem_univ i)
  · unfold condSkeel
    let i : Fin n := ⟨0, hn⟩
    exact le_trans
      (Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (Finset.sum_nonneg
          (fun j _ => abs_nonneg (L_inv k j)))))
      (Finset.le_sup'
        (fun a => ∑ k : Fin n, |L a k| * ∑ j : Fin n, |L_inv k j|)
        (Finset.mem_univ i))

/-- The fixed leading matrix in (14.6), normalized by `||L⁻¹||∞`, is bounded
by the printed `cond(L⁻¹)`. -/
theorem ch14ext_eq14_7_leading_infNorm_le
    (n : ℕ) (hn : 0 < n) (L L_inv : Fin n → Fin n → ℝ) :
    infNorm
        (matMul n (absMatrix n L_inv)
          (matMul n (absMatrix n L) (absMatrix n L_inv))) ≤
      infNorm L_inv * condSkeel n hn L_inv L := by
  calc
    infNorm
        (matMul n (absMatrix n L_inv)
          (matMul n (absMatrix n L) (absMatrix n L_inv))) ≤
        infNorm (absMatrix n L_inv) *
          infNorm (matMul n (absMatrix n L) (absMatrix n L_inv)) :=
      infNorm_matMul_le hn _ _
    _ = infNorm L_inv *
          infNorm (matMul n (absMatrix n L) (absMatrix n L_inv)) := by
      rw [infNorm_absMatrix hn]
    _ ≤ infNorm L_inv * condSkeel n hn L_inv L :=
      mul_le_mul_of_nonneg_left
        (ch14ext_eq14_7_inverseProduct_infNorm_le_condSkeel n hn L L_inv)
        (infNorm_nonneg L_inv)

/-- Matrix of explicit entrywise remainders used by the normwise endpoint. -/
noncomputable def ch14ext_eq14_7_familyRemainderMatrix
    {ι : Type*} {l : Filter ι} (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ) (F : Ch14Eq146Family ι l n L)
    (t : ι) : Fin n → Fin n → ℝ :=
  fun i j => ch14ext_eq14_6_familyRemainder n L L_inv F i j t

/-- The normalized normwise remainder in equation (14.7). -/
noncomputable def ch14ext_eq14_7_familyRemainder
    {ι : Type*} {l : Filter ι} (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ) (F : Ch14Eq146Family ι l n L)
    (t : ι) : ℝ :=
  infNorm (ch14ext_eq14_7_familyRemainderMatrix n L L_inv F t) /
    infNorm L_inv

theorem ch14ext_eq14_7_familyRemainder_isBigO
    {ι : Type*} {l : Filter ι} (n : ℕ) (hn : 0 < n)
    (L L_inv : Fin n → Fin n → ℝ) (F : Ch14Eq146Family ι l n L)
    (hInv : IsLeftInverse n L L_inv) :
    (fun t => ch14ext_eq14_7_familyRemainder n L L_inv F t)
      =O[l] (fun t => (F.model t).u ^ 2) := by
  have hdet : Matrix.det (L_inv : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    apply Matrix.det_ne_zero_of_right_inverse
    ext i j
    simpa [Matrix.mul_apply] using hInv i j
  have hpos : 0 < infNorm L_inv := infNorm_pos_of_det_ne_zero hn L_inv hdet
  have hmatrix := matrixFamily_infNorm_isBigO
    (fun i j => ch14ext_eq14_6_familyRemainder_isBigO n L L_inv F i j)
  have hscaled := hmatrix.const_mul_left (infNorm L_inv)⁻¹
  simpa [ch14ext_eq14_7_familyRemainder,
    ch14ext_eq14_7_familyRemainderMatrix, div_eq_mul_inv, mul_comm]
    using hscaled

/-- Genuine family-level closure of equation (14.7). -/
theorem ch14ext_eq14_7_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] (n : ℕ) (hn : 0 < n)
    (L L_inv : Fin n → Fin n → ℝ) (F : Ch14Eq146Family ι l n L)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv) :
    (∀ t,
      infNorm (fun i j => ch14ext_eq14_6_familyX n L F t i j - L_inv i j) /
          infNorm L_inv ≤
        (n : ℝ) * (F.model t).u * condSkeel n hn L_inv L +
          ch14ext_eq14_7_familyRemainder n L L_inv F t) ∧
      (fun t => ch14ext_eq14_7_familyRemainder n L L_inv F t)
        =O[l] (fun t => (F.model t).u ^ 2) := by
  have hdet : Matrix.det (L_inv : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
    apply Matrix.det_ne_zero_of_right_inverse
    ext i j
    simpa [Matrix.mul_apply] using hInv i j
  have hpos : 0 < infNorm L_inv := infNorm_pos_of_det_ne_zero hn L_inv hdet
  constructor
  · intro t
    let B := matMul n (absMatrix n L_inv)
      (matMul n (absMatrix n L) (absMatrix n L_inv))
    let R := ch14ext_eq14_7_familyRemainderMatrix n L L_inv F t
    let E : Fin n → Fin n → ℝ :=
      fun i j => ch14ext_eq14_6_familyX n L F t i j - L_inv i j
    have hentry := (ch14ext_eq14_6_vanishing_family_endpoint
      n L L_inv F hL_diag hLT hInv).1 t
    have hnorm : infNorm E ≤
        ((n : ℝ) * (F.model t).u) * infNorm B + infNorm R := by
      apply infNorm_le_of_row_sum_le
      · intro i
        calc
          ∑ j : Fin n, |E i j| ≤
              ∑ j : Fin n,
                (((n : ℝ) * (F.model t).u) * B i j + R i j) := by
            apply Finset.sum_le_sum
            intro j _hj
            simpa [E, B, R, matMul, absMatrix,
              ch14ext_eq14_7_familyRemainderMatrix] using hentry i j
          _ ≤ ((n : ℝ) * (F.model t).u) *
                (∑ j : Fin n, |B i j|) + ∑ j : Fin n, |R i j| := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left
              · exact Finset.sum_le_sum (fun j _ => le_abs_self (B i j))
              · exact mul_nonneg (Nat.cast_nonneg n) (F.model t).u_nonneg
            · exact Finset.sum_le_sum (fun j _ => le_abs_self (R i j))
          _ ≤ ((n : ℝ) * (F.model t).u) * infNorm B + infNorm R := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (row_sum_le_infNorm B i)
                (mul_nonneg (Nat.cast_nonneg n) (F.model t).u_nonneg))
              (row_sum_le_infNorm R i)
      · exact add_nonneg
          (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg n) (F.model t).u_nonneg)
            (infNorm_nonneg B))
          (infNorm_nonneg R)
    have hB := ch14ext_eq14_7_leading_infNorm_le n hn L L_inv
    have hscale : 0 ≤ (n : ℝ) * (F.model t).u :=
      mul_nonneg (Nat.cast_nonneg n) (F.model t).u_nonneg
    have hlead :
        (((n : ℝ) * (F.model t).u) * infNorm B) / infNorm L_inv ≤
          (n : ℝ) * (F.model t).u * condSkeel n hn L_inv L := by
      rw [div_le_iff₀ hpos]
      simpa [B, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hB hscale)
    calc
      infNorm E / infNorm L_inv ≤
          ((((n : ℝ) * (F.model t).u) * infNorm B) + infNorm R) /
            infNorm L_inv := div_le_div_of_nonneg_right hnorm hpos.le
      _ = (((n : ℝ) * (F.model t).u) * infNorm B) / infNorm L_inv +
          infNorm R / infNorm L_inv := by rw [add_div]
      _ ≤ (n : ℝ) * (F.model t).u * condSkeel n hn L_inv L +
          infNorm R / infNorm L_inv := add_le_add hlead (le_refl _)
      _ = (n : ℝ) * (F.model t).u * condSkeel n hn L_inv L +
          ch14ext_eq14_7_familyRemainder n L L_inv F t := by
        rfl
  · exact ch14ext_eq14_7_familyRemainder_isBigO n hn L L_inv F hInv

end NumStability.Ch14Ext
