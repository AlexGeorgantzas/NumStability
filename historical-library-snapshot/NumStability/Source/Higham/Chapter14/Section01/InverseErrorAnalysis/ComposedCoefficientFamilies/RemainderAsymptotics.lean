import Mathlib.Analysis.Asymptotics.Lemmas
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatVec
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.PerturbationTheory
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.AsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.AsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ForwardErrorEndpoint
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ScaledPerturbationEndpoints.ForwardError
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1.AsymptoticFamilies

/-!
# RemainderAsymptotics

Canonical destination for the Chapter14.Section01 declarations relocated from the
historical path `NumStability.Algorithms.Ch14AsymptoticFamilies` during wave R08.
Holds 10 declaration(s): 8 public and 2 authored-private.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

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

end Ch14Ext
end NumStability
