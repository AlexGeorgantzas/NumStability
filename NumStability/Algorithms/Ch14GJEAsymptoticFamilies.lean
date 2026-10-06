-- Algorithms/Ch14GJEAsymptoticFamilies.lean
--
-- Uniform vanishing-roundoff families for the Gauss-Jordan endpoints in
-- Higham, Chapter 14.  The pointwise algorithm certificates remain separate
-- from the local boundedness hypotheses used by the Landau estimates.

import NumStability.Algorithms.Ch14AsymptoticFamilies
import NumStability.Algorithms.Ch14GaussJordanQConstruction

namespace NumStability.Ch14Ext

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

/-! ## Finite-dimensional closure lemmas -/

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

/-! ## Scalar gamma and c3 families -/

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

/-! ## Locally bounded GJE source objects -/

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

/-! ## Theorem 14.5 residual remainder -/

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

/-! ## Locally bounded forward-error source objects -/

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

/-! ## Theorem 14.5 forward-error remainder -/

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

/-! ## Concrete source-facing family endpoints -/

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

end NumStability.Ch14Ext
