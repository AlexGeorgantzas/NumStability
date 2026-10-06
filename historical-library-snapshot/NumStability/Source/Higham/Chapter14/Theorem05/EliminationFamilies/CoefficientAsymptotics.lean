import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ForwardErrorEndpoint
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEAsymptoticFamilies

/-!
# CoefficientAsymptotics

Canonical destination for the Chapter14.Theorem05 declarations relocated from the
historical path `NumStability.Algorithms.Ch14GJEAsymptoticFamilies` during wave R08.
Holds 22 declaration(s): 8 public and 14 authored-private.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

private theorem ch14ext_gammaUnitCoefficient_family_isBigO_one
    {ι : Type*} {l : Filter ι} (k : ℕ) (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => ch14ext_gammaUnitCoefficient (fp t) k)
      =O[l] (fun _ : ι => (1 : ℝ)) := by
  simpa only [ch14ext_gammaUnitCoefficientScalar,
    ch14ext_gammaUnitCoefficient, Function.comp_apply] using
    (ch14ext_gammaUnitCoefficientScalar_isBigO_one k).comp_tendsto hu

private theorem ch14ext_gammaQuadraticCoefficient_family_isBigO_one
    {ι : Type*} {l : Filter ι} (k : ℕ) (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => ch14ext_gammaQuadraticCoefficient (fp t) k)
      =O[l] (fun _ : ι => (1 : ℝ)) := by
  simpa only [ch14ext_gammaQuadraticCoefficientScalar,
    ch14ext_gammaQuadraticCoefficient, Function.comp_apply] using
    (ch14ext_gammaQuadraticCoefficientScalar_isBigO_one k).comp_tendsto hu

/-- With dimension fixed, `gamma_k` is `O(u)` along every model family whose
unit roundoff tends to zero. -/
theorem ch14ext_gamma_family_isBigO_unit {ι : Type*} {l : Filter ι}
    (k : ℕ) (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => gamma (fp t) k) =O[l] (fun t => (fp t).u) := by
  have hu_refl :
      (fun t => (fp t).u) =O[l] (fun t => (fp t).u) :=
    Asymptotics.isBigO_refl _ l
  have hc := ch14ext_gammaUnitCoefficient_family_isBigO_one k fp hu
  simpa only [ch14ext_gamma_eq_u_mul_unitCoefficient, mul_one] using
    hu_refl.mul hc

/-- The explicit quadratic remainder in `gamma_k = k*u + gammaRem` is
uniformly `O(u^2)` along a vanishing-roundoff family. -/
theorem ch14ext_gammaRem_family_isBigO_unit_sq {ι : Type*} {l : Filter ι}
    (k : ℕ) (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => ch14ext_gammaRem (fp t) k)
      =O[l] (fun t => (fp t).u ^ 2) := by
  have hsq :
      (fun t => (fp t).u ^ 2) =O[l] (fun t => (fp t).u ^ 2) :=
    Asymptotics.isBigO_refl _ l
  have hc := ch14ext_gammaQuadraticCoefficient_family_isBigO_one k fp hu
  have heq :
      (fun t => ch14ext_gammaRem (fp t) k) =
        (fun t => (fp t).u ^ 2 *
          ch14ext_gammaQuadraticCoefficient (fp t) k) := by
    funext t
    unfold ch14ext_gammaRem ch14ext_gammaQuadraticCoefficient
    ring
  rw [heq]
  simpa only [mul_one] using hsq.mul hc

private theorem ch14ext_one_add_gamma_family_isBigO_one
    {ι : Type*} {l : Filter ι} (k : ℕ) (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => 1 + gamma (fp t) k) =O[l] (fun _ : ι => (1 : ℝ)) := by
  have hgamma := ch14ext_gamma_family_isBigO_unit k fp hu
  have hu_one :
      (fun t => (fp t).u) =O[l] (fun _ : ι => (1 : ℝ)) :=
    hu.isBigO_one ℝ
  have hone :
      (fun _ : ι => (1 : ℝ)) =O[l] (fun _ : ι => (1 : ℝ)) :=
    Asymptotics.isBigO_refl _ l
  exact hone.add (hgamma.trans hu_one)

private theorem ch14ext_one_add_gamma_pow_family_isBigO_one
    {ι : Type*} {l : Filter ι} (k p : ℕ) (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => (1 + gamma (fp t) k) ^ p)
      =O[l] (fun _ : ι => (1 : ℝ)) := by
  simpa only [one_pow] using
    (ch14ext_one_add_gamma_family_isBigO_one k fp hu).pow p

private theorem ch14ext_one_add_gamma_pow_sub_one_family_isBigO_unit
    {ι : Type*} {l : Filter ι} (k p : ℕ) (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => (1 + gamma (fp t) k) ^ p - 1)
      =O[l] (fun t => (fp t).u) := by
  have hgamma := ch14ext_gamma_family_isBigO_unit k fp hu
  have hbase := ch14ext_one_add_gamma_family_isBigO_one k fp hu
  have hsum :
      (fun t => ∑ r ∈ Finset.range p, (1 + gamma (fp t) k) ^ r)
        =O[l] (fun _ : ι => (1 : ℝ)) := by
    apply Asymptotics.IsBigO.sum
    intro r hr
    simpa only [one_pow] using hbase.pow r
  have heq :
      (fun t => (1 + gamma (fp t) k) ^ p - 1) =
        (fun t => gamma (fp t) k *
          ∑ r ∈ Finset.range p, (1 + gamma (fp t) k) ^ r) := by
    funext t
    simpa only [add_sub_cancel_left] using
      (mul_geom_sum (1 + gamma (fp t) k) p).symm
  rw [heq]
  simpa only [mul_one] using hgamma.mul hsum

/-- The Gauss-Jordan accumulation coefficient `c3` is `O(u)` when dimension
is fixed. -/
theorem ch14ext_gje_c3_family_isBigO_unit {ι : Type*} {l : Filter ι}
    (n : ℕ) (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => gje_c₃ (fp t) n) =O[l] (fun t => (fp t).u) := by
  have hgamma := ch14ext_gamma_family_isBigO_unit 3 fp hu
  have hpow :=
    ch14ext_one_add_gamma_pow_family_isBigO_one 3 (n - 2) fp hu
  simpa only [gje_c₃, mul_assoc, mul_one] using
    (hgamma.mul hpow).const_mul_left ((n : ℝ) - 1)

/-- The explicit remainder in the first-order expansion of `c3` is
uniformly `O(u^2)` for fixed dimension. -/
theorem ch14ext_gje_c3_quadratic_remainder_family_isBigO_unit_sq
    {ι : Type*} {l : Filter ι} (n : ℕ) (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => gje_c3_quadratic_remainder (fp t) n)
      =O[l] (fun t => (fp t).u ^ 2) := by
  have hrem := ch14ext_gammaRem_family_isBigO_unit_sq 3 fp hu
  have hpow :=
    ch14ext_one_add_gamma_pow_family_isBigO_one 3 (n - 2) fp hu
  have hpow_sub :=
    ch14ext_one_add_gamma_pow_sub_one_family_isBigO_unit 3 (n - 2) fp hu
  have hu_refl :
      (fun t => (fp t).u) =O[l] (fun t => (fp t).u) :=
    Asymptotics.isBigO_refl _ l
  have hfirst :
      (fun t => ch14ext_gammaRem (fp t) 3 *
        (1 + gamma (fp t) 3) ^ (n - 2))
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hrem.mul hpow
  have hsecond :
      (fun t => 3 * (fp t).u *
        ((1 + gamma (fp t) 3) ^ (n - 2) - 1))
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two, mul_assoc] using
      (hu_refl.mul hpow_sub).const_mul_left (3 : ℝ)
  simpa only [gje_c3_quadratic_remainder, ch14ext_gammaRem, mul_assoc] using
    (hfirst.add hsecond).const_mul_left ((n : ℝ) - 1)

private theorem ch14ext_gjeResidualS2_family_isBigOOne
    {ι : Type*} {l : Filter ι} (n : ℕ)
    {L X U : ι → Fin n → Fin n → ℝ} {x_hat : ι → Fin n → ℝ}
    (hL : MatrixFamilyIsBigOOne l L) (hX : MatrixFamilyIsBigOOne l X)
    (hU : MatrixFamilyIsBigOOne l U)
    (hx : VectorFamilyIsBigOOne l x_hat) :
    VectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeResidualS2 n (L t) (X t) (U t) (x_hat t) i) := by
  have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hU) (ch14ext_vectorFamily_abs_isBigOOne hx)
  have hXUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hX) hUx
  have hLXUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hL) hXUx
  simpa only [ch14ext_gjeResidualS2, absMatrix, absVec] using hLXUx

private theorem ch14ext_gjeResidualS22_family_isBigOOne
    {ι : Type*} {l : Filter ι} (n : ℕ)
    {L X U : ι → Fin n → Fin n → ℝ} {x_hat : ι → Fin n → ℝ}
    (hL : MatrixFamilyIsBigOOne l L) (hX : MatrixFamilyIsBigOOne l X)
    (hU : MatrixFamilyIsBigOOne l U)
    (hx : VectorFamilyIsBigOOne l x_hat) :
    VectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeResidualS22 n (L t) (X t) (U t) (x_hat t) i) := by
  have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hU) (ch14ext_vectorFamily_abs_isBigOOne hx)
  have hXUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hX) hUx
  have hXXUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hX) hXUx
  have hLXXUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hL) hXXUx
  simpa only [ch14ext_gjeResidualS22, absMatrix, absVec] using hLXXUx

private theorem ch14ext_gjeResidualS23_family_isBigOOne
    {ι : Type*} {l : Filter ι} (n : ℕ)
    {L X : ι → Fin n → Fin n → ℝ} {y : ι → Fin n → ℝ}
    (hL : MatrixFamilyIsBigOOne l L) (hX : MatrixFamilyIsBigOOne l X)
    (hy : VectorFamilyIsBigOOne l y) :
    VectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeResidualS23 n (L t) (X t) (y t) i) := by
  have hXy := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hX) (ch14ext_vectorFamily_abs_isBigOOne hy)
  have hXXy := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hX) hXy
  have hLXXy := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hL) hXXy
  simpa only [ch14ext_gjeResidualS23, absMatrix, absVec] using hLXXy

/-- The explicit residual remainder used in the concrete (14.31) theorem is
entrywise `O(u^2)` when every varying matrix and vector source object is
entrywise/componentwise `O(1)`. -/
theorem ch14ext_gjeResidualHigherOrder_family_isBigO
    {ι : Type*} {l : Filter ι} (n : ℕ) (fp : ι → FPModel)
    (L X U : ι → Fin n → Fin n → ℝ)
    (y x_hat : ι → Fin n → ℝ)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hL : MatrixFamilyIsBigOOne l L) (hX : MatrixFamilyIsBigOOne l X)
    (hU : MatrixFamilyIsBigOOne l U)
    (hy : VectorFamilyIsBigOOne l y)
    (hx : VectorFamilyIsBigOOne l x_hat) (i : Fin n) :
    (fun t => ch14ext_gjeResidualHigherOrder n (fp t)
      (L t) (X t) (U t) (y t) (x_hat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
  have hgamma := ch14ext_gamma_family_isBigO_unit n fp hu
  have hgammaRem := ch14ext_gammaRem_family_isBigO_unit_sq n fp hu
  have hc3 := ch14ext_gje_c3_family_isBigO_unit n fp hu
  have hc3Rem :=
    ch14ext_gje_c3_quadratic_remainder_family_isBigO_unit_sq n fp hu
  have hgamma_c3 :
      (fun t => gamma (fp t) n * gje_c₃ (fp t) n)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hgamma.mul hc3
  have hcoeff1 :
      (fun t => 2 * ch14ext_gammaRem (fp t) n +
        2 * gje_c3_quadratic_remainder (fp t) n +
        2 * gamma (fp t) n * gje_c₃ (fp t) n)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_assoc] using
      ((hgammaRem.const_mul_left 2).add
        (hc3Rem.const_mul_left 2)).add
          (hgamma_c3.const_mul_left 2)
  have hs2 := ch14ext_gjeResidualS2_family_isBigOOne n hL hX hU hx
  have hterm1 :
      (fun t =>
        (2 * ch14ext_gammaRem (fp t) n +
          2 * gje_c3_quadratic_remainder (fp t) n +
          2 * gamma (fp t) n * gje_c₃ (fp t) n) *
          ch14ext_gjeResidualS2 n (L t) (X t) (U t) (x_hat t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hcoeff1.mul (hs2 i)
  have hc3_sq :
      (fun t => gje_c₃ (fp t) n * gje_c₃ (fp t) n)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hc3.mul hc3
  have hgamma_one := ch14ext_one_add_gamma_family_isBigO_one n fp hu
  have hcoeff2 :
      (fun t => gje_c₃ (fp t) n * gje_c₃ (fp t) n *
        (1 + gamma (fp t) n)) =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hc3_sq.mul hgamma_one
  have hs22 := ch14ext_gjeResidualS22_family_isBigOOne n hL hX hU hx
  have hs23 := ch14ext_gjeResidualS23_family_isBigOOne n hL hX hy
  have hterm2 :
      (fun t => gje_c₃ (fp t) n * gje_c₃ (fp t) n *
        (1 + gamma (fp t) n) *
          (ch14ext_gjeResidualS22 n (L t) (X t) (U t) (x_hat t) i +
            ch14ext_gjeResidualS23 n (L t) (X t) (y t) i))
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one] using hcoeff2.mul ((hs22 i).add (hs23 i))
  simpa only [ch14ext_gjeResidualHigherOrder] using hterm1.add hterm2

private theorem ch14ext_gjeForwardRaw_family_isBigOOne
    {ι : Type*} {l : Filter ι} (n : ℕ)
    {X U : ι → Fin n → Fin n → ℝ} {z y : ι → Fin n → ℝ}
    (hX : MatrixFamilyIsBigOOne l X) (hU : MatrixFamilyIsBigOOne l U)
    (hz : VectorFamilyIsBigOOne l z) (hy : VectorFamilyIsBigOOne l y) :
    VectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeForwardRaw n (X t) (U t) (z t) (y t) i) := by
  have hUz := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hU) (ch14ext_vectorFamily_abs_isBigOOne hz)
  have hXUz := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hX hUz
  have hXy := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hX
    (ch14ext_vectorFamily_abs_isBigOOne hy)
  intro i
  simpa only [ch14ext_gjeForwardRaw, absMatrix, absVec] using
    (hXUz i).add (hXy i)

private theorem ch14ext_gjeForwardT1_family_isBigOOne
    {ι : Type*} {l : Filter ι} (n : ℕ)
    {A_inv L U : ι → Fin n → Fin n → ℝ} {x_hat : ι → Fin n → ℝ}
    (hA : MatrixFamilyIsBigOOne l A_inv)
    (hL : MatrixFamilyIsBigOOne l L) (hU : MatrixFamilyIsBigOOne l U)
    (hx : VectorFamilyIsBigOOne l x_hat) :
    VectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeForwardT1 n (A_inv t) (L t) (U t) (x_hat t) i) := by
  have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hU) (ch14ext_vectorFamily_abs_isBigOOne hx)
  have hLUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hL) hUx
  have hALUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hA) hLUx
  simpa only [ch14ext_gjeForwardT1, absMatrix, absVec] using hALUx

private theorem ch14ext_gjeForwardT2_family_isBigOOne
    {ι : Type*} {l : Filter ι} (n : ℕ)
    {X U : ι → Fin n → Fin n → ℝ} {x_hat : ι → Fin n → ℝ}
    (hX : MatrixFamilyIsBigOOne l X) (hU : MatrixFamilyIsBigOOne l U)
    (hx : VectorFamilyIsBigOOne l x_hat) :
    VectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeForwardT2 n (X t) (U t) (x_hat t) i) := by
  have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hU) (ch14ext_vectorFamily_abs_isBigOOne hx)
  have hXUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hX hUx
  simpa only [ch14ext_gjeForwardT2, absMatrix, absVec] using hXUx

private theorem ch14ext_gjeForwardQ1_family_isBigOOne
    {ι : Type*} {l : Filter ι} (n : ℕ)
    {A_inv L U X : ι → Fin n → Fin n → ℝ}
    {z y : ι → Fin n → ℝ}
    (hA : MatrixFamilyIsBigOOne l A_inv)
    (hL : MatrixFamilyIsBigOOne l L) (hU : MatrixFamilyIsBigOOne l U)
    (hX : MatrixFamilyIsBigOOne l X)
    (hz : VectorFamilyIsBigOOne l z) (hy : VectorFamilyIsBigOOne l y) :
    VectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeForwardQ1 n (A_inv t) (L t) (U t) (X t)
        (z t) (y t) i) := by
  have hraw := ch14ext_gjeForwardRaw_family_isBigOOne n hX hU hz hy
  have hUraw := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hU) hraw
  have hLUraw := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hL) hUraw
  have hALUraw := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hA) hLUraw
  simpa only [ch14ext_gjeForwardQ1, absMatrix] using hALUraw

private theorem ch14ext_gjeForwardQ2_family_isBigOOne
    {ι : Type*} {l : Filter ι} (n : ℕ)
    {X U : ι → Fin n → Fin n → ℝ} {z y : ι → Fin n → ℝ}
    (hX : MatrixFamilyIsBigOOne l X) (hU : MatrixFamilyIsBigOOne l U)
    (hz : VectorFamilyIsBigOOne l z) (hy : VectorFamilyIsBigOOne l y) :
    VectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeForwardQ2 n (X t) (U t) (z t) (y t) i) := by
  have hraw := ch14ext_gjeForwardRaw_family_isBigOOne n hX hU hz hy
  have hUraw := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hU) hraw
  have hXUraw := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hX hUraw
  simpa only [ch14ext_gjeForwardQ2, absMatrix] using hXUraw

private theorem ch14ext_gjeForwardUinvCorrection_family_isBigOOne
    {ι : Type*} {l : Filter ι} (n : ℕ)
    {X U U_inv : ι → Fin n → Fin n → ℝ} {x_hat : ι → Fin n → ℝ}
    (hX : MatrixFamilyIsBigOOne l X) (hU : MatrixFamilyIsBigOOne l U)
    (hUinv : MatrixFamilyIsBigOOne l U_inv)
    (hx : VectorFamilyIsBigOOne l x_hat) :
    VectorFamilyIsBigOOne l
      (fun t i => ch14ext_gjeForwardUinvCorrection n (X t) (U t) (U_inv t)
        (x_hat t) i) := by
  have hUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hU) (ch14ext_vectorFamily_abs_isBigOOne hx)
  have hUinvUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hUinv) hUx
  have hUUinvUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne
    (matrixFamily_abs_isBigOOne hU) hUinvUx
  have hXUUinvUx := ch14ext_matrixFamily_mul_vectorFamily_isBigOOne hX hUUinvUx
  simpa only [ch14ext_gjeForwardUinvCorrection, absMatrix, absVec] using hXUUinvUx

/-- The literal (14.32) higher-order expression, including the explicit
`|Uhat^-1|` replacement correction, is entrywise `O(u^2)` under explicit
local boundedness hypotheses for all algorithm data. -/
theorem ch14ext_gjeForwardLiteralHigherOrder_family_isBigO
    {ι : Type*} {l : Filter ι} (n : ℕ) (fp : ι → FPModel)
    (A_inv L U X U_inv : ι → Fin n → Fin n → ℝ)
    (z y x_hat : ι → Fin n → ℝ)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hA : MatrixFamilyIsBigOOne l A_inv)
    (hL : MatrixFamilyIsBigOOne l L) (hU : MatrixFamilyIsBigOOne l U)
    (hX : MatrixFamilyIsBigOOne l X)
    (hUinv : MatrixFamilyIsBigOOne l U_inv)
    (hz : VectorFamilyIsBigOOne l z) (hy : VectorFamilyIsBigOOne l y)
    (hx : VectorFamilyIsBigOOne l x_hat) (i : Fin n) :
    (fun t => ch14ext_gjeForwardLiteralHigherOrder n (fp t)
      (A_inv t) (L t) (U t) (X t) (U_inv t)
      (z t) (y t) (x_hat t) i)
      =O[l] (fun t => (fp t).u ^ 2) := by
  have hgamma := ch14ext_gamma_family_isBigO_unit n fp hu
  have hgammaRem := ch14ext_gammaRem_family_isBigO_unit_sq n fp hu
  have hc3 := ch14ext_gje_c3_family_isBigO_unit n fp hu
  have hc3Rem :=
    ch14ext_gje_c3_quadratic_remainder_family_isBigO_unit_sq n fp hu
  have ht1 := ch14ext_gjeForwardT1_family_isBigOOne n hA hL hU hx
  have ht2 := ch14ext_gjeForwardT2_family_isBigOOne n hX hU hx
  have hq1 := ch14ext_gjeForwardQ1_family_isBigOOne n hA hL hU hX hz hy
  have hq2 := ch14ext_gjeForwardQ2_family_isBigOOne n hX hU hz hy
  have hgamma_c3 :
      (fun t => gamma (fp t) n * gje_c₃ (fp t) n)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hgamma.mul hc3
  have hc3_sq :
      (fun t => gje_c₃ (fp t) n * gje_c₃ (fp t) n)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hc3.mul hc3
  have hterm1 :
      (fun t => 2 * ch14ext_gammaRem (fp t) n *
        ch14ext_gjeForwardT1 n (A_inv t) (L t) (U t) (x_hat t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one, mul_assoc] using
      (hgammaRem.const_mul_left 2).mul (ht1 i)
  have hterm2 :
      (fun t => 2 * gje_c3_quadratic_remainder (fp t) n *
        ch14ext_gjeForwardT2 n (X t) (U t) (x_hat t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one, mul_assoc] using
      (hc3Rem.const_mul_left 2).mul (ht2 i)
  have hterm3 :
      (fun t => 2 * gamma (fp t) n * gje_c₃ (fp t) n *
        ch14ext_gjeForwardQ1 n (A_inv t) (L t) (U t) (X t)
          (z t) (y t) i) =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one, mul_assoc] using
      (hgamma_c3.const_mul_left 2).mul (hq1 i)
  have hterm4 :
      (fun t => 2 * gje_c₃ (fp t) n * gje_c₃ (fp t) n *
        ch14ext_gjeForwardQ2 n (X t) (U t) (z t) (y t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one, mul_assoc] using
      (hc3_sq.const_mul_left 2).mul (hq2 i)
  have hhigher :
      (fun t => ch14ext_gjeForwardHigherOrder n (fp t)
        (A_inv t) (L t) (U t) (X t) (z t) (y t) (x_hat t) i)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [ch14ext_gjeForwardHigherOrder] using
      ((hterm1.add hterm2).add hterm3).add hterm4
  have hcorr := ch14ext_gjeForwardUinvCorrection_family_isBigOOne
    n hX hU hUinv hx
  have hu_refl :
      (fun t => (fp t).u) =O[l] (fun t => (fp t).u) :=
    Asymptotics.isBigO_refl _ l
  have hu_c3 :
      (fun t => (fp t).u * gje_c₃ (fp t) n)
        =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [pow_two] using hu_refl.mul hc3
  have hcorrection :
      (fun t => 6 * (n : ℝ) * (fp t).u * gje_c₃ (fp t) n *
        ch14ext_gjeForwardUinvCorrection n (X t) (U t) (U_inv t)
          (x_hat t) i) =O[l] (fun t => (fp t).u ^ 2) := by
    simpa only [mul_one, mul_assoc] using
      (hu_c3.const_mul_left (6 * (n : ℝ))).mul (hcorr i)
  simpa only [ch14ext_gjeForwardLiteralHigherOrder] using
    hhigher.add hcorrection

/-- Family-level closure of the concrete (14.31) recurrence theorem: the
source inequality holds for every execution, and its explicit varying
remainder is entrywise `O(u^2)`. -/
theorem ch14ext_gjeConcrete_residual_14_31_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] (n : ℕ)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (start : ℕ)
    (F : Ch14GJEConcreteFamily ι l n A b start) :
    (∀ t i,
      |b i - matMulVec n A (F.x_hat t) i| ≤
        8 * (n : ℝ) * (F.model t).u *
          ch14ext_gjeResidualS2 n (F.L_hat t)
            (ch14ext_gjeConcreteFamilyXabs F t) (F.V t start)
            (F.x_hat t) i +
        ch14ext_gjeResidualHigherOrder n (F.model t) (F.L_hat t)
          (ch14ext_gjeConcreteFamilyXabs F t) (F.V t start)
          (F.xseq t start) (F.x_hat t) i) ∧
      ∀ i,
        (fun t => ch14ext_gjeResidualHigherOrder n (F.model t) (F.L_hat t)
          (ch14ext_gjeConcreteFamilyXabs F t) (F.V t start)
          (F.xseq t start) (F.x_hat t) i)
          =O[l] (fun t => (F.model t).u ^ 2) := by
  constructor
  · intro t
    simpa only [ch14ext_gjeConcreteFamilyXabs] using
      ch14ext_gjeConcrete_overall_residual_14_31 n (F.model t) A (F.L_hat t)
        b (F.x_hat t) (F.V t) (F.xseq t) start (F.lu_certificate t)
        (F.valid_n t) F.dimension_pos (F.valid_three t) F.index_valid
        (F.final_matrix t) (F.final_vector t) (F.forward_start t)
        (F.matrix_recurrence t) (F.vector_recurrence t) (F.pivots_nonzero t)
  · intro i
    exact ch14ext_gjeResidualHigherOrder_family_isBigO n F.model F.L_hat
      (ch14ext_gjeConcreteFamilyXabs F) (fun t => F.V t start)
      (fun t => F.xseq t start) F.x_hat F.unit_tendsto_zero
      F.L_hat_isBigO_one F.X_abs_isBigO_one F.U_hat_isBigO_one
      F.y_isBigO_one F.x_hat_isBigO_one i

/-- Family-level closure of literal (14.32).  Its pointwise half uses the
actual LU/GJE certificates and right-inverse certificate; its asymptotic half
requires only explicit `O(1)` data, including a separate `Pabs` hypothesis. -/
theorem ch14ext_gjeConcrete_forward_14_32_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (b x : Fin n → ℝ) (start : ℕ)
    (F : Ch14GJEConcreteFamily ι l n A b start)
    (U_inv : ι → Fin n → Fin n → ℝ) (z : ι → Fin n → ℝ)
    (hAinv : IsLeftInverse n A A_inv)
    (hUinv : ∀ t, IsRightInverse n (F.V t start) (U_inv t))
    (hExact : ∀ i, matMulVec n A x i = b i)
    (hUz : ∀ t i, matMulVec n (F.V t start) (z t) i = F.xseq t start i)
    (hUinv_one : MatrixFamilyIsBigOOne l U_inv)
    (hz_one : VectorFamilyIsBigOOne l z)
    (hPabs_one : MatrixFamilyIsBigOOne l
      (ch14ext_gjeConcreteFamilyPabs F)) :
    (∀ t i,
      |x i - F.x_hat t i| ≤
        2 * (n : ℝ) * (F.model t).u *
          ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.V t start)
            (F.x_hat t) i +
        6 * (n : ℝ) * (F.model t).u *
          ch14ext_gjeForwardT2 n (absMatrix n (U_inv t)) (F.V t start)
            (F.x_hat t) i +
        ch14ext_gjeForwardLiteralHigherOrder n (F.model t) A_inv
          (F.L_hat t) (F.V t start) (ch14ext_gjeConcreteFamilyPabs F t)
          (U_inv t) (z t) (F.xseq t start) (F.x_hat t) i) ∧
      ∀ i,
        (fun t => ch14ext_gjeForwardLiteralHigherOrder n (F.model t) A_inv
          (F.L_hat t) (F.V t start) (ch14ext_gjeConcreteFamilyPabs F t)
          (U_inv t) (z t) (F.xseq t start) (F.x_hat t) i)
          =O[l] (fun t => (F.model t).u ^ 2) := by
  constructor
  · intro t
    simpa only [ch14ext_gjeConcreteFamilyPabs] using
      ch14ext_gjeConcrete_overall_forward_error_14_32 n (F.model t)
        A A_inv (F.L_hat t) (U_inv t) b x (z t) (F.x_hat t)
        (F.V t) (F.xseq t) start (F.lu_certificate t) hAinv (hUinv t)
        (F.valid_n t) F.dimension_pos (F.valid_three t) F.index_valid
        (F.final_matrix t) (F.final_vector t) (F.forward_start t) hExact
        (hUz t) (F.matrix_recurrence t) (F.vector_recurrence t)
        (F.pivots_nonzero t)
  · intro i
    exact ch14ext_gjeForwardLiteralHigherOrder_family_isBigO n F.model
      (fun _ => A_inv) F.L_hat (fun t => F.V t start)
      (ch14ext_gjeConcreteFamilyPabs F) U_inv z (fun t => F.xseq t start)
      F.x_hat F.unit_tendsto_zero
      (ch14ext_fixedMatrix_family_isBigOOne l A_inv) F.L_hat_isBigO_one
      F.U_hat_isBigO_one hPabs_one hUinv_one hz_one F.y_isBigO_one
      F.x_hat_isBigO_one i

end Ch14Ext
end NumStability
