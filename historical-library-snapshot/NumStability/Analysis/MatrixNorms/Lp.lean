-- Analysis/MatrixNorms/Lp.lean
--
-- Induced finite-dimensional complex matrix `L^p` norms.

import Mathlib.Analysis.Complex.Hadamard
import NumStability.Analysis.MatrixNorms.Basic

/-!
# Induced matrix Lp norms

Defines induced matrix `L^p` norm values and bounds, proves their core
algebraic laws, and supplies interpolation results for real exponents.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


theorem hasComplexMatrixLpBound_nonneg
    {m n : ℕ} {p : ℝ≥0∞} {A : CMatrix m n} {C : ℝ}
    (h : HasComplexMatrixLpBound p A C) :
    0 ≤ C :=
  h.1

theorem hasComplexMatrixLpBound_mixedSubordinateMatrixBound
    {m n : ℕ} {p : ℝ≥0∞} {A : CMatrix m n} {C : ℝ}
    (h : HasComplexMatrixLpBound p A C) :
    MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A C :=
  h.2

theorem hasComplexMatrixLpBound_apply
    {m n : ℕ} {p : ℝ≥0∞} {A : CMatrix m n} {C : ℝ}
    (h : HasComplexMatrixLpBound p A C) (x : CVec n) :
    complexVecLpNorm p (complexMatrixVecMul A x) ≤
      C * complexVecLpNorm p x :=
  h.2 x

theorem hasComplexMatrixLpBound_of_nonneg_mixedSubordinateMatrixBound
    {m n : ℕ} {p : ℝ≥0∞} {A : CMatrix m n} {C : ℝ}
    (hC : 0 ≤ C)
    (hbound : MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A C) :
    HasComplexMatrixLpBound p A C :=
  ⟨hC, hbound⟩

/-- Left-boundary matrix-image estimate for the finite-dimensional
    Riesz-Thorin analytic vector family. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_affine_le_bound_of_re_zero
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {p scale left right target M : ℝ} {z : ℂ}
    (hp : 0 < p) (htarget_pos : 0 < target) (hz : z.re = 0)
    (hpow : (scale * left) * p = target)
    (hx : complexVecLpNorm (ENNReal.ofReal target) x ≤ 1)
    (hA : HasComplexMatrixLpBound (ENNReal.ofReal p) A M) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexMatrixVecMul A
          (complexRieszThorinAnalyticVec x
            (complexRieszThorinAffineExponent scale left right z))) ≤ M := by
  let X : CVec n :=
    complexRieszThorinAnalyticVec x
      (complexRieszThorinAffineExponent scale left right z)
  have hX : complexVecLpNorm (ENNReal.ofReal p) X ≤ 1 :=
    complexRieszThorinAnalyticVec_lpNorm_affine_le_one_of_re_zero
      (right := right) hp htarget_pos hz hpow hx
  have hAX :
      complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) ≤
        M * complexVecLpNorm (ENNReal.ofReal p) X :=
    hasComplexMatrixLpBound_apply hA X
  have hM : 0 ≤ M := hasComplexMatrixLpBound_nonneg hA
  calc
    complexVecLpNorm (ENNReal.ofReal p)
        (complexMatrixVecMul A
          (complexRieszThorinAnalyticVec x
            (complexRieszThorinAffineExponent scale left right z)))
        = complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) := by
            rfl
    _ ≤ M * complexVecLpNorm (ENNReal.ofReal p) X := hAX
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hX hM
    _ = M := by ring

/-- Left-boundary matrix-image estimate for the endpoint source exponent
    `p = infinity`.  This is the `p = infinity` sibling of
    `complexRieszThorinAnalyticVec_matrixImage_lpNorm_affine_le_bound_of_re_zero`. -/
lemma complexRieszThorinAnalyticVec_matrixImage_infNorm_affine_le_bound_of_re_zero
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {scale right target M : ℝ} {z : ℂ}
    [Fact (1 ≤ ENNReal.ofReal target)]
    (hscale : 0 ≤ scale) (hright : 0 ≤ right) (hz : z.re = 0)
    (hx : complexVecLpNorm (ENNReal.ofReal target) x ≤ 1)
    (hA : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M) :
    complexVecInfNorm
        (complexMatrixVecMul A
          (complexRieszThorinAnalyticVec x
            (complexRieszThorinAffineExponent scale 0 right z))) ≤ M := by
  let X : CVec n :=
    complexRieszThorinAnalyticVec x
      (complexRieszThorinAffineExponent scale 0 right z)
  have hX : complexVecInfNorm X ≤ 1 :=
    complexRieszThorinAnalyticVec_infNorm_affine_le_one_of_re_zero
      (x := x) (scale := scale) (right := right) (target := target)
      (z := z) hscale hright hz hx
  have hAX :
      complexVecLpNorm ∞ (complexMatrixVecMul A X) ≤
        M * complexVecLpNorm ∞ X :=
    hasComplexMatrixLpBound_apply hA X
  have hAX_inf :
      complexVecInfNorm (complexMatrixVecMul A X) ≤
        M * complexVecInfNorm X := by
    simpa [complexVecLpNorm_infty_eq_complexVecInfNorm] using hAX
  have hM : 0 ≤ M := hasComplexMatrixLpBound_nonneg hA
  calc
    complexVecInfNorm
        (complexMatrixVecMul A
          (complexRieszThorinAnalyticVec x
            (complexRieszThorinAffineExponent scale 0 right z)))
        = complexVecInfNorm (complexMatrixVecMul A X) := by
            rfl
    _ ≤ M * complexVecInfNorm X := hAX_inf
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hX hM
    _ = M := by ring

/-- Right-boundary matrix-image estimate for the finite-dimensional
    Riesz-Thorin analytic vector family. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_affine_le_bound_of_re_one
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {p scale left right target M : ℝ} {z : ℂ}
    (hp : 0 < p) (htarget_pos : 0 < target) (hz : z.re = 1)
    (hpow : (scale * right) * p = target)
    (hx : complexVecLpNorm (ENNReal.ofReal target) x ≤ 1)
    (hA : HasComplexMatrixLpBound (ENNReal.ofReal p) A M) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexMatrixVecMul A
          (complexRieszThorinAnalyticVec x
            (complexRieszThorinAffineExponent scale left right z))) ≤ M := by
  let X : CVec n :=
    complexRieszThorinAnalyticVec x
      (complexRieszThorinAffineExponent scale left right z)
  have hX : complexVecLpNorm (ENNReal.ofReal p) X ≤ 1 :=
    complexRieszThorinAnalyticVec_lpNorm_affine_le_one_of_re_one
      (left := left) hp htarget_pos hz hpow hx
  have hAX :
      complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) ≤
        M * complexVecLpNorm (ENNReal.ofReal p) X :=
    hasComplexMatrixLpBound_apply hA X
  have hM : 0 ≤ M := hasComplexMatrixLpBound_nonneg hA
  calc
    complexVecLpNorm (ENNReal.ofReal p)
        (complexMatrixVecMul A
          (complexRieszThorinAnalyticVec x
            (complexRieszThorinAffineExponent scale left right z)))
        = complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) := by
            rfl
    _ ≤ M * complexVecLpNorm (ENNReal.ofReal p) X := hAX
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hX hM
    _ = M := by ring

/-- Left vertical-line specialization of the Riesz-Thorin matrix-image
    boundary estimate. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_affine_left_vertical_le_bound
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {p scale left right target M t : ℝ}
    (hp : 0 < p) (htarget_pos : 0 < target)
    (hpow : (scale * left) * p = target)
    (hx : complexVecLpNorm (ENNReal.ofReal target) x ≤ 1)
    (hA : HasComplexMatrixLpBound (ENNReal.ofReal p) A M) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexMatrixVecMul A
          (complexRieszThorinAnalyticVec x
            (complexRieszThorinAffineExponent scale left right
              (Complex.I * (t : ℂ))))) ≤ M := by
  exact complexRieszThorinAnalyticVec_matrixImage_lpNorm_affine_le_bound_of_re_zero
    (right := right) hp htarget_pos (by simp) hpow hx hA

/-- Right vertical-line specialization of the Riesz-Thorin matrix-image
    boundary estimate. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_affine_right_vertical_le_bound
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {p scale left right target M t : ℝ}
    (hp : 0 < p) (htarget_pos : 0 < target)
    (hpow : (scale * right) * p = target)
    (hx : complexVecLpNorm (ENNReal.ofReal target) x ≤ 1)
    (hA : HasComplexMatrixLpBound (ENNReal.ofReal p) A M) :
    complexVecLpNorm (ENNReal.ofReal p)
        (complexMatrixVecMul A
          (complexRieszThorinAnalyticVec x
            (complexRieszThorinAffineExponent scale left right
              ((1 : ℂ) + Complex.I * (t : ℂ))))) ≤ M := by
  exact complexRieszThorinAnalyticVec_matrixImage_lpNorm_affine_le_bound_of_re_one
    (left := left) hp htarget_pos (by simp) hpow hx hA

/-- Left-boundary scalar pairing estimate for the finite-dimensional
    Riesz-Thorin analytic families. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_zero
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {p q scaleX leftX rightX targetX scaleY leftY rightY targetY M : ℝ} {z : ℂ}
    (hpq : p.HolderConjugate q) (htargetX_pos : 0 < targetX)
    (htargetY_pos : 0 < targetY) (hz : z.re = 0)
    (hpowX : (scaleX * leftX) * p = targetX)
    (hpowY : (scaleY * leftY) * q = targetY)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hA : HasComplexMatrixLpBound (ENNReal.ofReal p) A M) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖ ≤ M := by
  let X : CVec n :=
    complexRieszThorinAnalyticVec x
      (complexRieszThorinAffineExponent scaleX leftX rightX z)
  let Y : CVec m :=
    complexRieszThorinAnalyticVec y
      (complexRieszThorinAffineExponent scaleY leftY rightY z)
  have hY : complexVecLpNorm (ENNReal.ofReal q) Y ≤ 1 :=
    complexRieszThorinAnalyticVec_lpNorm_affine_le_one_of_re_zero
      (right := rightY) hpq.symm.pos htargetY_pos hz hpowY hy
  have hAX : complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) ≤ M :=
    complexRieszThorinAnalyticVec_matrixImage_lpNorm_affine_le_bound_of_re_zero
      (A := A) (x := x) (right := rightX) hpq.pos htargetX_pos hz hpowX hx hA
  have hholder :
      ‖∑ i : Fin m, Y i * complexMatrixVecMul A X i‖ ≤
        complexVecLpNorm (ENNReal.ofReal q) Y *
          complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) :=
    complexVecLpNorm_holder hpq Y (complexMatrixVecMul A X)
  have hAX_nonneg :
      0 ≤ complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) :=
    complexVecLpNorm_ofReal_nonneg hpq.pos (complexMatrixVecMul A X)
  calc
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖
        = ‖∑ i : Fin m, Y i * complexMatrixVecMul A X i‖ := by
            rfl
    _ ≤ complexVecLpNorm (ENNReal.ofReal q) Y *
          complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) := hholder
    _ ≤ 1 * M := mul_le_mul hY hAX hAX_nonneg zero_le_one
    _ = M := by ring

/-- Left-boundary scalar pairing estimate for the endpoint `1`/`∞` side of
    the finite-dimensional Riesz-Thorin analytic families. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_zero_one_top
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {scaleX leftX rightX targetX scaleY rightY targetY M : ℝ} {z : ℂ}
    [Fact (1 ≤ ENNReal.ofReal targetY)]
    (htargetX_pos : 0 < targetX) (hz : z.re = 0)
    (hpowX : (scaleX * leftX) * (1 : ℝ) = targetX)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hscaleY : 0 ≤ scaleY) (hrightY : 0 ≤ rightY)
    (hA : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY 0 rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖ ≤ M := by
  let X : CVec n :=
    complexRieszThorinAnalyticVec x
      (complexRieszThorinAffineExponent scaleX leftX rightX z)
  let Y : CVec m :=
    complexRieszThorinAnalyticVec y
      (complexRieszThorinAffineExponent scaleY 0 rightY z)
  have hY : complexVecInfNorm Y ≤ 1 :=
    complexRieszThorinAnalyticVec_infNorm_affine_le_one_of_re_zero
      (x := y) (scale := scaleY) (right := rightY) (target := targetY)
      (z := z) hscaleY hrightY hz hy
  have hAX : complexVecLpNorm (ENNReal.ofReal (1 : ℝ)) (complexMatrixVecMul A X) ≤ M :=
    complexRieszThorinAnalyticVec_matrixImage_lpNorm_affine_le_bound_of_re_zero
      (A := A) (x := x) (right := rightX) (p := (1 : ℝ))
      (scale := scaleX) (left := leftX) (target := targetX)
      (M := M) (z := z) (by norm_num) htargetX_pos hz hpowX hx hA
  have hAX_one : complexVecOneNorm (complexMatrixVecMul A X) ≤ M := by
    simpa [complexVecLpNorm_one_eq_complexVecOneNorm] using hAX
  have hholder :
      ‖∑ i : Fin m, Y i * complexMatrixVecMul A X i‖ ≤
        complexVecInfNorm Y * complexVecOneNorm (complexMatrixVecMul A X) :=
    complexVecInfNorm_mul_oneNorm_pairing_le Y (complexMatrixVecMul A X)
  have hAX_one_nonneg : 0 ≤ complexVecOneNorm (complexMatrixVecMul A X) :=
    (complexVecOneNorm_isComplexVectorNorm (n := m)).nonneg (complexMatrixVecMul A X)
  calc
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY 0 rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖
        = ‖∑ i : Fin m, Y i * complexMatrixVecMul A X i‖ := by
            rfl
    _ ≤ complexVecInfNorm Y * complexVecOneNorm (complexMatrixVecMul A X) := hholder
    _ ≤ 1 * M := mul_le_mul hY hAX_one hAX_one_nonneg zero_le_one
    _ = M := by ring

/-- Left-boundary scalar pairing estimate for the endpoint `infinity`/`1`
    side of the finite-dimensional Riesz-Thorin analytic families. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_zero_top_one
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {scaleX rightX targetX scaleY leftY rightY targetY M : ℝ} {z : ℂ}
    [Fact (1 ≤ ENNReal.ofReal targetX)]
    (htargetY_pos : 0 < targetY) (hz : z.re = 0)
    (hpowY : (scaleY * leftY) * (1 : ℝ) = targetY)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hrightX : 0 ≤ rightX)
    (hA : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX 0 rightX z)) i‖ ≤ M := by
  let X : CVec n :=
    complexRieszThorinAnalyticVec x
      (complexRieszThorinAffineExponent scaleX 0 rightX z)
  let Y : CVec m :=
    complexRieszThorinAnalyticVec y
      (complexRieszThorinAffineExponent scaleY leftY rightY z)
  have hY_lp : complexVecLpNorm (ENNReal.ofReal (1 : ℝ)) Y ≤ 1 :=
    complexRieszThorinAnalyticVec_lpNorm_affine_le_one_of_re_zero
      (x := y) (p := (1 : ℝ))
      (scale := scaleY) (left := leftY) (right := rightY)
      (target := targetY) (z := z)
      (by norm_num) htargetY_pos hz hpowY hy
  have hY_one : complexVecOneNorm Y ≤ 1 := by
    simpa [complexVecLpNorm_one_eq_complexVecOneNorm] using hY_lp
  have hAX : complexVecInfNorm (complexMatrixVecMul A X) ≤ M :=
    complexRieszThorinAnalyticVec_matrixImage_infNorm_affine_le_bound_of_re_zero
      (A := A) (x := x)
      (scale := scaleX) (right := rightX) (target := targetX)
      (M := M) (z := z) hscaleX hrightX hz hx hA
  have hholder :
      ‖∑ i : Fin m, Y i * complexMatrixVecMul A X i‖ ≤
        complexVecOneNorm Y * complexVecInfNorm (complexMatrixVecMul A X) :=
    complexVecOneNorm_mul_infNorm_pairing_le Y (complexMatrixVecMul A X)
  have hAX_nonneg : 0 ≤ complexVecInfNorm (complexMatrixVecMul A X) :=
    complexVecInfNorm_nonneg (complexMatrixVecMul A X)
  calc
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX 0 rightX z)) i‖
        = ‖∑ i : Fin m, Y i * complexMatrixVecMul A X i‖ := by
            rfl
    _ ≤ complexVecOneNorm Y * complexVecInfNorm (complexMatrixVecMul A X) := hholder
    _ ≤ 1 * M := mul_le_mul hY_one hAX hAX_nonneg zero_le_one
    _ = M := by ring

/-- Right-boundary scalar pairing estimate for the finite-dimensional
    Riesz-Thorin analytic families. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_one
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {p q scaleX leftX rightX targetX scaleY leftY rightY targetY M : ℝ} {z : ℂ}
    (hpq : p.HolderConjugate q) (htargetX_pos : 0 < targetX)
    (htargetY_pos : 0 < targetY) (hz : z.re = 1)
    (hpowX : (scaleX * rightX) * p = targetX)
    (hpowY : (scaleY * rightY) * q = targetY)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hA : HasComplexMatrixLpBound (ENNReal.ofReal p) A M) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖ ≤ M := by
  let X : CVec n :=
    complexRieszThorinAnalyticVec x
      (complexRieszThorinAffineExponent scaleX leftX rightX z)
  let Y : CVec m :=
    complexRieszThorinAnalyticVec y
      (complexRieszThorinAffineExponent scaleY leftY rightY z)
  have hY : complexVecLpNorm (ENNReal.ofReal q) Y ≤ 1 :=
    complexRieszThorinAnalyticVec_lpNorm_affine_le_one_of_re_one
      (left := leftY) hpq.symm.pos htargetY_pos hz hpowY hy
  have hAX : complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) ≤ M :=
    complexRieszThorinAnalyticVec_matrixImage_lpNorm_affine_le_bound_of_re_one
      (A := A) (x := x) (left := leftX) hpq.pos htargetX_pos hz hpowX hx hA
  have hholder :
      ‖∑ i : Fin m, Y i * complexMatrixVecMul A X i‖ ≤
        complexVecLpNorm (ENNReal.ofReal q) Y *
          complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) :=
    complexVecLpNorm_holder hpq Y (complexMatrixVecMul A X)
  have hAX_nonneg :
      0 ≤ complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) :=
    complexVecLpNorm_ofReal_nonneg hpq.pos (complexMatrixVecMul A X)
  calc
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖
        = ‖∑ i : Fin m, Y i * complexMatrixVecMul A X i‖ := by
            rfl
    _ ≤ complexVecLpNorm (ENNReal.ofReal q) Y *
          complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A X) := hholder
    _ ≤ 1 * M := mul_le_mul hY hAX hAX_nonneg zero_le_one
    _ = M := by ring

/-- Left vertical-line scalar pairing estimate for the finite-dimensional
    Riesz-Thorin analytic families. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_affine_left_vertical_le_bound
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {p q scaleX leftX rightX targetX scaleY leftY rightY targetY M t : ℝ}
    (hpq : p.HolderConjugate q) (htargetX_pos : 0 < targetX)
    (htargetY_pos : 0 < targetY)
    (hpowX : (scaleX * leftX) * p = targetX)
    (hpowY : (scaleY * leftY) * q = targetY)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hA : HasComplexMatrixLpBound (ENNReal.ofReal p) A M) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY
              (Complex.I * (t : ℂ))) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX
                (Complex.I * (t : ℂ)))) i‖ ≤ M := by
  exact complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_zero
    (A := A) (x := x) (y := y) (rightX := rightX) (rightY := rightY)
    hpq htargetX_pos htargetY_pos (by simp) hpowX hpowY hx hy hA

/-- Right vertical-line scalar pairing estimate for the finite-dimensional
    Riesz-Thorin analytic families. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_affine_right_vertical_le_bound
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {p q scaleX leftX rightX targetX scaleY leftY rightY targetY M t : ℝ}
    (hpq : p.HolderConjugate q) (htargetX_pos : 0 < targetX)
    (htargetY_pos : 0 < targetY)
    (hpowX : (scaleX * rightX) * p = targetX)
    (hpowY : (scaleY * rightY) * q = targetY)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hA : HasComplexMatrixLpBound (ENNReal.ofReal p) A M) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY
              ((1 : ℂ) + Complex.I * (t : ℂ))) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX
                ((1 : ℂ) + Complex.I * (t : ℂ)))) i‖ ≤ M := by
  exact complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_one
    (A := A) (x := x) (y := y) (leftX := leftX) (leftY := leftY)
    hpq htargetX_pos htargetY_pos (by simp) hpowX hpowY hx hy hA

/-- At the interpolation point, the finite-dimensional Riesz-Thorin scalar
    pairing recovers the original matrix pairing. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_at_real_interpolation
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {θ scaleX leftX rightX scaleY leftY rightY : ℝ}
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1) :
    (∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY (θ : ℂ)) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX (θ : ℂ))) i) =
      ∑ i : Fin m, y i * complexMatrixVecMul A x i := by
  rw [complexRieszThorinAnalyticVec_at_affineExponent_real_one y hY,
    complexRieszThorinAnalyticVec_at_affineExponent_real_one x hX]

/-- Norm form of the interpolation-point recovery for the Riesz-Thorin scalar
    matrix pairing. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_norm_at_real_interpolation
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {θ scaleX leftX rightX scaleY leftY rightY : ℝ}
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY (θ : ℂ)) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX (θ : ℂ))) i‖ =
      ‖∑ i : Fin m, y i * complexMatrixVecMul A x i‖ := by
  rw [complexRieszThorinAnalyticVec_matrixPairing_at_real_interpolation hX hY]

lemma complexRieszThorinAnalyticVec_matrixImage_coord_differentiable
    {m n : ℕ} (A : CMatrix m n) (x : CVec n)
    (scale left right : ℝ) (i : Fin m) :
    Differentiable ℂ (fun z : ℂ =>
      complexMatrixVecMul A
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z)) i) := by
  classical
  simpa [complexMatrixVecMul] using
    (Differentiable.fun_sum (u := Finset.univ) (fun j _ =>
      (complexRieszThorinAnalyticVec_coord_differentiable
        x scale left right j).const_mul (A i j)))

lemma complexRieszThorinAnalyticVec_matrixImage_coord_diffContOnCl
    {m n : ℕ} (A : CMatrix m n) (x : CVec n)
    (scale left right : ℝ) (i : Fin m) (s : Set ℂ) :
    DiffContOnCl ℂ
      (fun z : ℂ =>
        complexMatrixVecMul A
          (complexRieszThorinAnalyticVec x
            (complexRieszThorinAffineExponent scale left right z)) i) s :=
  (complexRieszThorinAnalyticVec_matrixImage_coord_differentiable
    A x scale left right i).diffContOnCl

lemma complexRieszThorinAnalyticVec_matrixPairing_differentiable
    {m n : ℕ} (A : CMatrix m n) (x : CVec n) (y : CVec m)
    (scaleX leftX rightX scaleY leftY rightY : ℝ) :
    Differentiable ℂ (fun z : ℂ =>
      ∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i) := by
  classical
  simpa using
    (Differentiable.fun_sum (u := Finset.univ) (fun i _ =>
    (complexRieszThorinAnalyticVec_coord_differentiable
      y scaleY leftY rightY i).mul
      (complexRieszThorinAnalyticVec_matrixImage_coord_differentiable
        A x scaleX leftX rightX i)))

lemma complexRieszThorinAnalyticVec_matrixPairing_diffContOnCl
    {m n : ℕ} (A : CMatrix m n) (x : CVec n) (y : CVec m)
    (scaleX leftX rightX scaleY leftY rightY : ℝ) (s : Set ℂ) :
    DiffContOnCl ℂ
      (fun z : ℂ =>
        ∑ i : Fin m,
          complexRieszThorinAnalyticVec y
              (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
            complexMatrixVecMul A
              (complexRieszThorinAnalyticVec x
                (complexRieszThorinAffineExponent scaleX leftX rightX z)) i) s :=
  (complexRieszThorinAnalyticVec_matrixPairing_differentiable
    A x y scaleX leftX rightX scaleY leftY rightY).diffContOnCl

/-- Closed-strip row estimate for the Riesz-Thorin analytic source-vector
    family.  This is the finite-dimensional boundedness ingredient used before
    applying Hadamard three-lines. -/
lemma complexRieszThorinAnalyticVec_matrixImage_coord_norm_le_entrywiseRowSum_of_re_mem_Icc
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {scale left right : ℝ} {z : ℂ}
    (hx : ∀ j : Fin n, ‖x j‖ ≤ 1)
    (hscale : 0 ≤ scale) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (i : Fin m) :
    ‖complexMatrixVecMul A
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z)) i‖ ≤
      ∑ j : Fin n, ‖A i j‖ := by
  let X : CVec n :=
    complexRieszThorinAnalyticVec x
      (complexRieszThorinAffineExponent scale left right z)
  have hX : ∀ j : Fin n, ‖X j‖ ≤ 1 := by
    intro j
    exact complexRieszThorinAnalyticVec_coord_norm_le_one_of_affineExponent_re_mem_Icc
      hx hscale hleft hright hz0 hz1 j
  calc
    ‖complexMatrixVecMul A
        (complexRieszThorinAnalyticVec x
          (complexRieszThorinAffineExponent scale left right z)) i‖
        = ‖∑ j : Fin n, A i j * X j‖ := by
            rfl
    _ ≤ ∑ j : Fin n, ‖A i j * X j‖ := norm_sum_le _ _
    _ = ∑ j : Fin n, ‖A i j‖ * ‖X j‖ := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [norm_mul]
    _ ≤ ∑ j : Fin n, ‖A i j‖ * 1 := by
          refine Finset.sum_le_sum ?_
          intro j _hj
          exact mul_le_mul_of_nonneg_left (hX j) (norm_nonneg (A i j))
    _ = ∑ j : Fin n, ‖A i j‖ := by
          simp

/-- Closed-strip scalar pairing estimate for the Riesz-Thorin analytic source
    and dual vector families.  The bound is the finite entrywise `1`-sum of the
    matrix, so it is independent of the imaginary part of the strip variable. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_norm_le_entrywiseSum_of_re_mem_Icc
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {scaleX leftX rightX scaleY leftY rightY : ℝ} {z : ℂ}
    (hx : ∀ j : Fin n, ‖x j‖ ≤ 1)
    (hy : ∀ i : Fin m, ‖y i‖ ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖ ≤
      ∑ i : Fin m, ∑ j : Fin n, ‖A i j‖ := by
  let X : CVec n :=
    complexRieszThorinAnalyticVec x
      (complexRieszThorinAffineExponent scaleX leftX rightX z)
  let Y : CVec m :=
    complexRieszThorinAnalyticVec y
      (complexRieszThorinAffineExponent scaleY leftY rightY z)
  have hY : ∀ i : Fin m, ‖Y i‖ ≤ 1 := by
    intro i
    exact complexRieszThorinAnalyticVec_coord_norm_le_one_of_affineExponent_re_mem_Icc
      hy hscaleY hleftY hrightY hz0 hz1 i
  have hAX : ∀ i : Fin m,
      ‖complexMatrixVecMul A X i‖ ≤ ∑ j : Fin n, ‖A i j‖ := by
    intro i
    exact complexRieszThorinAnalyticVec_matrixImage_coord_norm_le_entrywiseRowSum_of_re_mem_Icc
      (A := A) (x := x) (scale := scaleX) (left := leftX) (right := rightX)
      hx hscaleX hleftX hrightX hz0 hz1 i
  calc
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖
        = ‖∑ i : Fin m, Y i * complexMatrixVecMul A X i‖ := by
            rfl
    _ ≤ ∑ i : Fin m, ‖Y i * complexMatrixVecMul A X i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin m, ∑ j : Fin n, ‖A i j‖ := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          have hrow_nonneg : 0 ≤ ∑ j : Fin n, ‖A i j‖ :=
            Finset.sum_nonneg (fun j _hj => norm_nonneg (A i j))
          calc
            ‖Y i * complexMatrixVecMul A X i‖ =
                ‖Y i‖ * ‖complexMatrixVecMul A X i‖ := by
                  rw [norm_mul]
            _ ≤ 1 * (∑ j : Fin n, ‖A i j‖) :=
                mul_le_mul (hY i) (hAX i)
                  (norm_nonneg (complexMatrixVecMul A X i)) zero_le_one
            _ = ∑ j : Fin n, ‖A i j‖ := by
                rw [one_mul]

/-- Closed-strip scalar pairing estimate with source and dual coordinate
    bounds obtained from arbitrary finite-product `L^p` unit-ball hypotheses. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_norm_le_entrywiseSum_of_lpNorm_le_one_of_re_mem_Icc
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {pX pY : ℝ≥0∞} [Fact (1 ≤ pX)] [Fact (1 ≤ pY)]
    {scaleX leftX rightX scaleY leftY rightY : ℝ} {z : ℂ}
    (hx : complexVecLpNorm pX x ≤ 1)
    (hy : complexVecLpNorm pY y ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖ ≤
      ∑ i : Fin m, ∑ j : Fin n, ‖A i j‖ := by
  exact complexRieszThorinAnalyticVec_matrixPairing_norm_le_entrywiseSum_of_re_mem_Icc
    (A := A) (x := x) (y := y)
    (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
    (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
    (fun j => complexVecLpNorm_coord_le_one_of_le_one pX hx j)
    (fun i => complexVecLpNorm_coord_le_one_of_le_one pY hy i)
    hscaleX hleftX hrightX hscaleY hleftY hrightY hz0 hz1

lemma complexRieszThorinAnalyticVec_matrixPairing_bddAbove_closedStrip_of_lpNorm_le_one
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {pX pY : ℝ≥0∞} [Fact (1 ≤ pX)] [Fact (1 ≤ pY)]
    {scaleX leftX rightX scaleY leftY rightY : ℝ}
    (hx : complexVecLpNorm pX x ≤ 1)
    (hy : complexVecLpNorm pY y ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY) :
    BddAbove
      ((norm ∘
        (fun z : ℂ =>
          ∑ i : Fin m,
            complexRieszThorinAnalyticVec y
                (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
              complexMatrixVecMul A
                (complexRieszThorinAnalyticVec x
                  (complexRieszThorinAffineExponent scaleX leftX rightX z)) i)) ''
        Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  refine ⟨∑ i : Fin m, ∑ j : Fin n, ‖A i j‖, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hzIcc : z.re ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  exact complexRieszThorinAnalyticVec_matrixPairing_norm_le_entrywiseSum_of_lpNorm_le_one_of_re_mem_Icc
    (A := A) (x := x) (y := y)
    (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
    (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
    hx hy hscaleX hleftX hrightX hscaleY hleftY hrightY hzIcc.1 hzIcc.2

lemma complexRieszThorinAnalyticVec_matrixPairing_hadamard_norm_le_of_boundary
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {pX pY : ℝ≥0∞} [Fact (1 ≤ pX)] [Fact (1 ≤ pY)]
    {scaleX leftX rightX scaleY leftY rightY M0 M1 : ℝ} {z : ℂ}
    (hx : complexVecLpNorm pX x ≤ 1)
    (hy : complexVecLpNorm pY y ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1)
    (hleft :
      ∀ w ∈ Complex.re ⁻¹' ({0} : Set ℝ),
        ‖∑ i : Fin m,
          complexRieszThorinAnalyticVec y
              (complexRieszThorinAffineExponent scaleY leftY rightY w) i *
            complexMatrixVecMul A
              (complexRieszThorinAnalyticVec x
                (complexRieszThorinAffineExponent scaleX leftX rightX w)) i‖ ≤ M0)
    (hright :
      ∀ w ∈ Complex.re ⁻¹' ({1} : Set ℝ),
        ‖∑ i : Fin m,
          complexRieszThorinAnalyticVec y
              (complexRieszThorinAffineExponent scaleY leftY rightY w) i *
            complexMatrixVecMul A
              (complexRieszThorinAnalyticVec x
                (complexRieszThorinAffineExponent scaleX leftX rightX w)) i‖ ≤ M1) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖ ≤
      M0 ^ (1 - z.re) * M1 ^ z.re := by
  let F : ℂ → ℂ := fun w : ℂ =>
    ∑ i : Fin m,
      complexRieszThorinAnalyticVec y
          (complexRieszThorinAffineExponent scaleY leftY rightY w) i *
        complexMatrixVecMul A
          (complexRieszThorinAnalyticVec x
            (complexRieszThorinAffineExponent scaleX leftX rightX w)) i
  have hzIcc : z.re ∈ Set.Icc (0 : ℝ) 1 := ⟨hz0, hz1⟩
  have hzStrip : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hzIcc
  have hd : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    simpa [F] using
      (complexRieszThorinAnalyticVec_matrixPairing_diffContOnCl
        A x y scaleX leftX rightX scaleY leftY rightY
        (Complex.HadamardThreeLines.verticalStrip 0 1))
  have hB : BddAbove ((norm ∘ F) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    simpa [F] using
      (complexRieszThorinAnalyticVec_matrixPairing_bddAbove_closedStrip_of_lpNorm_le_one
        (A := A) (x := x) (y := y)
        (pX := pX) (pY := pY)
        (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
        (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
        hx hy hscaleX hleftX hrightX hscaleY hleftY hrightY)
  have hleftF : ∀ w ∈ Complex.re ⁻¹' ({0} : Set ℝ), ‖F w‖ ≤ M0 := by
    intro w hw
    simpa [F] using hleft w hw
  have hrightF : ∀ w ∈ Complex.re ⁻¹' ({1} : Set ℝ), ‖F w‖ ≤ M1 := by
    intro w hw
    simpa [F] using hright w hw
  have hhad :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      (f := F) (z := z) (a := M0) (b := M1)
      hzStrip hd hB hleftF hrightF
  simpa [F] using hhad

lemma complexRieszThorinAnalyticVec_matrixPairing_hadamard_affine_le_bound
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {p0 q0 p1 q1 scaleX leftX rightX targetX
      scaleY leftY rightY targetY M0 M1 : ℝ} {z : ℂ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (htargetX_pos : 0 < targetX) (htargetY_pos : 0 < targetY)
    (hpowX0 : (scaleX * leftX) * p0 = targetX)
    (hpowY0 : (scaleY * leftY) * q0 = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖ ≤
      M0 ^ (1 - z.re) * M1 ^ z.re := by
  refine
    complexRieszThorinAnalyticVec_matrixPairing_hadamard_norm_le_of_boundary
      (A := A) (x := x) (y := y)
      (pX := ENNReal.ofReal targetX) (pY := ENNReal.ofReal targetY)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (M0 := M0) (M1 := M1) (z := z)
      hx hy hscaleX hleftX hrightX hscaleY hleftY hrightY hz0 hz1 ?_ ?_
  · intro w hw
    have hwre : w.re = 0 := by
      simpa using hw
    exact complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_zero
      (A := A) (x := x) (y := y)
      (p := p0) (q := q0)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (targetY := targetY) (M := M0) (z := w)
      hpq0 htargetX_pos htargetY_pos hwre hpowX0 hpowY0 hx hy hA0
  · intro w hw
    have hwre : w.re = 1 := by
      simpa using hw
    exact complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_one
      (A := A) (x := x) (y := y)
      (p := p1) (q := q1)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (targetY := targetY) (M := M1) (z := w)
      hpq1 htargetX_pos htargetY_pos hwre hpowX1 hpowY1 hx hy hA1

/-- Interpolation-point lift of the scalar Hadamard estimate to a matrix-image
    bound, assuming the chosen dual vector norms the target image.  This is the
    final local bridge before constructing such a norming vector in the full
    finite-dimensional Riesz-Thorin theorem. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_norming_pair
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {p0 q0 p1 q1 scaleX leftX rightX targetX
      scaleY leftY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (htargetX_pos : 0 < targetX) (htargetY_pos : 0 < targetY)
    (hpowX0 : (scaleX * leftX) * p0 = targetX)
    (hpowY0 : (scaleY * leftY) * q0 = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1)
    (hpair :
      complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) =
        ‖∑ i : Fin m, y i * complexMatrixVecMul A x i‖) :
    complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) ≤
      M0 ^ (1 - θ) * M1 ^ θ := by
  have hhad :
      ‖∑ i : Fin m,
          complexRieszThorinAnalyticVec y
              (complexRieszThorinAffineExponent scaleY leftY rightY (θ : ℂ)) i *
            complexMatrixVecMul A
              (complexRieszThorinAnalyticVec x
                (complexRieszThorinAffineExponent scaleX leftX rightX (θ : ℂ))) i‖ ≤
        M0 ^ (1 - (θ : ℂ).re) * M1 ^ (θ : ℂ).re :=
    complexRieszThorinAnalyticVec_matrixPairing_hadamard_affine_le_bound
      (A := A) (x := x) (y := y)
      (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (targetY := targetY) (M0 := M0) (M1 := M1) (z := (θ : ℂ))
      hpq0 hpq1 htargetX_pos htargetY_pos
      hpowX0 hpowY0 hpowX1 hpowY1 hx hy
      hscaleX hleftX hrightX hscaleY hleftY hrightY
      (by simpa using hθ0) (by simpa using hθ1) hA0 hA1
  have hrecover :=
    complexRieszThorinAnalyticVec_matrixPairing_norm_at_real_interpolation
      (A := A) (x := x) (y := y)
      (θ := θ) (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      hX hY
  rw [hrecover] at hhad
  simpa [hpair] using hhad

/-- Interpolation-point matrix-image bound with the finite-dimensional dual
    normer supplied automatically from `L^p`/`L^q` duality. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_finite_dual_normer
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {p0 q0 p1 q1 scaleX leftX rightX targetX
      scaleY leftY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowX0 : (scaleX * leftX) * p0 = targetX)
    (hpowY0 : (scaleY * leftY) * q0 = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) ≤
      M0 ^ (1 - θ) * M1 ^ θ := by
  obtain ⟨y, hy, hpair_row⟩ :=
    complexVecLpNorm_exists_rowNormingVector
      (n := m) (p := targetY) (q := targetX)
      htargetYX (complexMatrixVecMul A x)
  have hpair :
      complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) =
        ‖∑ i : Fin m, y i * complexMatrixVecMul A x i‖ := by
    have hsum_comm :
        (∑ i : Fin m, y i * complexMatrixVecMul A x i) =
          ∑ i : Fin m, complexMatrixVecMul A x i * y i := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [← hpair_row, hsum_comm]
  exact
    complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_norming_pair
      (A := A) (x := x) (y := y)
      (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (targetY := targetY) (M0 := M0) (M1 := M1) (θ := θ)
      hpq0 hpq1 htargetYX.symm.pos htargetYX.pos
      hpowX0 hpowY0 hpowX1 hpowY1 hX hY hx hy
      hscaleX hleftX hrightX hscaleY hleftY hrightY hθ0 hθ1 hA0 hA1 hpair

set_option linter.unusedTactic false in
/-- Arbitrary-vector form of the finite-dual Riesz-Thorin matrix-image bound:
    rescale a nonzero source vector to the target unit ball, and handle the zero
    vector through the vector-norm zero law. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_scaled
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {p0 q0 p1 q1 scaleX leftX rightX targetX
      scaleY leftY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowX0 : (scaleX * leftX) * p0 = targetX)
    (hpowY0 : (scaleY * leftY) * q0 = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) ≤
      (M0 ^ (1 - θ) * M1 ^ θ) *
        complexVecLpNorm (ENNReal.ofReal targetX) x := by
  -- Preserve frozen auxiliary names across the semantic module split.
  run_tac do
    let ngen ← Lean.getDeclNGen
    Lean.setDeclNGen { ngen with idx := 2 }
  let ν : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal targetX)
  let μ : CVec m → ℝ := complexVecLpNorm (n := m) (ENNReal.ofReal targetX)
  let C : ℝ := M0 ^ (1 - θ) * M1 ^ θ
  have hν : IsComplexVectorNorm ν :=
    complexVecLpNorm_isComplexVectorNorm (n := n) (ENNReal.ofReal targetX)
  have hμ : IsComplexVectorNorm μ :=
    complexVecLpNorm_isComplexVectorNorm (n := m) (ENNReal.ofReal targetX)
  by_cases hxzero : ν x = 0
  · have hx_eq : x = 0 := (hν.eq_zero_iff x).mp hxzero
    have hAx_zero : complexMatrixVecMul A x = 0 := by
      subst x
      ext i
      simp [complexMatrixVecMul]
    have hleft_zero : μ (complexMatrixVecMul A x) = 0 :=
      (hμ.eq_zero_iff (complexMatrixVecMul A x)).mpr hAx_zero
    change μ (complexMatrixVecMul A x) ≤ C * ν x
    rw [hleft_zero, hxzero, mul_zero]
  · have hxpos : 0 < ν x := lt_of_le_of_ne (hν.nonneg x) (Ne.symm hxzero)
    let c : ℂ := (((ν x)⁻¹ : ℝ) : ℂ)
    let x₀ : CVec n := complexVecSMul c x
    have hc_norm : ‖c‖ = (ν x)⁻¹ := by
      dsimp [c]
      exact Complex.norm_of_nonneg (inv_nonneg.mpr (hν.nonneg x))
    have hx₀_norm : ν x₀ = 1 := by
      dsimp [x₀]
      rw [hν.smul, hc_norm]
      field_simp [ne_of_gt hxpos]
    have hx₀_le : complexVecLpNorm (ENNReal.ofReal targetX) x₀ ≤ 1 := by
      change ν x₀ ≤ 1
      rw [hx₀_norm]
    have hnormed :=
      complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_finite_dual_normer
        (A := A) (x := x₀)
        (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1)
        (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
        (targetX := targetX)
        (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
        (targetY := targetY) (M0 := M0) (M1 := M1) (θ := θ)
        hpq0 hpq1 htargetYX
        hpowX0 hpowY0 hpowX1 hpowY1 hX hY hx₀_le
        hscaleX hleftX hrightX hscaleY hleftY hrightY hθ0 hθ1 hA0 hA1
    have hAx₀ :
        complexMatrixVecMul A x₀ =
          complexVecSMul c (complexMatrixVecMul A x) := by
      ext i
      dsimp [x₀, c, complexMatrixVecMul, complexVecSMul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    have hAx₀_norm :
        μ (complexMatrixVecMul A x₀) = (ν x)⁻¹ * μ (complexMatrixVecMul A x) := by
      rw [hAx₀]
      rw [hμ.smul, hc_norm]
    change μ (complexMatrixVecMul A x) ≤ C * ν x
    change μ (complexMatrixVecMul A x₀) ≤ C at hnormed
    rw [hAx₀_norm] at hnormed
    have hmul := mul_le_mul_of_nonneg_right hnormed (le_of_lt hxpos)
    calc
      μ (complexMatrixVecMul A x) =
          ((ν x)⁻¹ * μ (complexMatrixVecMul A x)) * ν x := by
            field_simp [ne_of_gt hxpos]
      _ ≤ C * ν x := hmul

/-- Scalar Hadamard bound for the endpoint Riesz-Thorin case with left
    exponents `1` and `∞`, and a finite conjugate right endpoint. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_hadamard_affine_le_bound_one_top
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {p1 q1 scaleX leftX rightX targetX
      scaleY rightY targetY M0 M1 : ℝ} {z : ℂ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq1 : p1.HolderConjugate q1)
    (htargetX_pos : 0 < targetX) (htargetY_pos : 0 < targetY)
    (hpowX0 : (scaleX * leftX) * (1 : ℝ) = targetX)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hrightY : 0 ≤ rightY)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY 0 rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX leftX rightX z)) i‖ ≤
      M0 ^ (1 - z.re) * M1 ^ z.re := by
  refine
    complexRieszThorinAnalyticVec_matrixPairing_hadamard_norm_le_of_boundary
      (A := A) (x := x) (y := y)
      (pX := ENNReal.ofReal targetX) (pY := ENNReal.ofReal targetY)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (scaleY := scaleY) (leftY := 0) (rightY := rightY)
      (M0 := M0) (M1 := M1) (z := z)
      hx hy hscaleX hleftX hrightX hscaleY (by norm_num) hrightY hz0 hz1 ?_ ?_
  · intro w hw
    have hwre : w.re = 0 := by
      simpa using hw
    exact complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_zero_one_top
      (A := A) (x := x) (y := y)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (rightY := rightY)
      (targetY := targetY) (M := M0) (z := w)
      htargetX_pos hwre hpowX0 hx hy hscaleY hrightY hA0
  · intro w hw
    have hwre : w.re = 1 := by
      simpa using hw
    exact complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_one
      (A := A) (x := x) (y := y)
      (p := p1) (q := q1)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := 0) (rightY := rightY)
      (targetY := targetY) (M := M1) (z := w)
      hpq1 htargetX_pos htargetY_pos hwre hpowX1 hpowY1 hx hy hA1

/-- Interpolation-point matrix-image bound for the endpoint Riesz-Thorin case,
    assuming an explicit finite dual norming vector at the target exponent. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_norming_pair_one_top
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {p1 q1 scaleX leftX rightX targetX
      scaleY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq1 : p1.HolderConjugate q1)
    (htargetX_pos : 0 < targetX) (htargetY_pos : 0 < targetY)
    (hpowX0 : (scaleX * leftX) * (1 : ℝ) = targetX)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * 0 + θ * rightY) = 1)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1)
    (hpair :
      complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) =
        ‖∑ i : Fin m, y i * complexMatrixVecMul A x i‖) :
    complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) ≤
      M0 ^ (1 - θ) * M1 ^ θ := by
  have hhad :
      ‖∑ i : Fin m,
          complexRieszThorinAnalyticVec y
              (complexRieszThorinAffineExponent scaleY 0 rightY (θ : ℂ)) i *
            complexMatrixVecMul A
              (complexRieszThorinAnalyticVec x
                (complexRieszThorinAffineExponent scaleX leftX rightX (θ : ℂ))) i‖ ≤
        M0 ^ (1 - (θ : ℂ).re) * M1 ^ (θ : ℂ).re :=
    complexRieszThorinAnalyticVec_matrixPairing_hadamard_affine_le_bound_one_top
      (A := A) (x := x) (y := y)
      (p1 := p1) (q1 := q1)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (rightY := rightY)
      (targetY := targetY) (M0 := M0) (M1 := M1) (z := (θ : ℂ))
      hpq1 htargetX_pos htargetY_pos
      hpowX0 hpowX1 hpowY1 hx hy
      hscaleX hleftX hrightX hscaleY hrightY
      (by simpa using hθ0) (by simpa using hθ1) hA0 hA1
  have hrecover :=
    complexRieszThorinAnalyticVec_matrixPairing_norm_at_real_interpolation
      (A := A) (x := x) (y := y)
      (θ := θ) (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (scaleY := scaleY) (leftY := 0) (rightY := rightY)
      hX hY
  rw [hrecover] at hhad
  simpa [hpair] using hhad

/-- Endpoint Riesz-Thorin matrix-image bound with the finite-dimensional dual
    normer supplied automatically at the target exponent. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_finite_dual_normer_one_top
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {p1 q1 scaleX leftX rightX targetX
      scaleY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowX0 : (scaleX * leftX) * (1 : ℝ) = targetX)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * 0 + θ * rightY) = 1)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) ≤
      M0 ^ (1 - θ) * M1 ^ θ := by
  obtain ⟨y, hy, hpair_row⟩ :=
    complexVecLpNorm_exists_rowNormingVector
      (n := m) (p := targetY) (q := targetX)
      htargetYX (complexMatrixVecMul A x)
  have hpair :
      complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) =
        ‖∑ i : Fin m, y i * complexMatrixVecMul A x i‖ := by
    have hsum_comm :
        (∑ i : Fin m, y i * complexMatrixVecMul A x i) =
          ∑ i : Fin m, complexMatrixVecMul A x i * y i := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [← hpair_row, hsum_comm]
  exact
    complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_norming_pair_one_top
      (A := A) (x := x) (y := y)
      (p1 := p1) (q1 := q1)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (rightY := rightY)
      (targetY := targetY) (M0 := M0) (M1 := M1) (θ := θ)
      hpq1 htargetYX.symm.pos htargetYX.pos
      hpowX0 hpowX1 hpowY1 hX hY hx hy
      hscaleX hleftX hrightX hscaleY hrightY hθ0 hθ1 hA0 hA1 hpair

set_option linter.unusedTactic false in
/-- Arbitrary-vector form of the endpoint Riesz-Thorin matrix-image bound. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_scaled_one_top
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {p1 q1 scaleX leftX rightX targetX
      scaleY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowX0 : (scaleX * leftX) * (1 : ℝ) = targetX)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * 0 + θ * rightY) = 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) ≤
      (M0 ^ (1 - θ) * M1 ^ θ) *
        complexVecLpNorm (ENNReal.ofReal targetX) x := by
  -- Preserve frozen auxiliary names across the semantic module split.
  run_tac do
    let ngen ← Lean.getDeclNGen
    Lean.setDeclNGen { ngen with idx := 2 }
  let ν : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal targetX)
  let μ : CVec m → ℝ := complexVecLpNorm (n := m) (ENNReal.ofReal targetX)
  let C : ℝ := M0 ^ (1 - θ) * M1 ^ θ
  have hν : IsComplexVectorNorm ν :=
    complexVecLpNorm_isComplexVectorNorm (n := n) (ENNReal.ofReal targetX)
  have hμ : IsComplexVectorNorm μ :=
    complexVecLpNorm_isComplexVectorNorm (n := m) (ENNReal.ofReal targetX)
  by_cases hxzero : ν x = 0
  · have hx_eq : x = 0 := (hν.eq_zero_iff x).mp hxzero
    have hAx_zero : complexMatrixVecMul A x = 0 := by
      subst x
      ext i
      simp [complexMatrixVecMul]
    have hleft_zero : μ (complexMatrixVecMul A x) = 0 :=
      (hμ.eq_zero_iff (complexMatrixVecMul A x)).mpr hAx_zero
    change μ (complexMatrixVecMul A x) ≤ C * ν x
    rw [hleft_zero, hxzero, mul_zero]
  · have hxpos : 0 < ν x := lt_of_le_of_ne (hν.nonneg x) (Ne.symm hxzero)
    let c : ℂ := (((ν x)⁻¹ : ℝ) : ℂ)
    let x₀ : CVec n := complexVecSMul c x
    have hc_norm : ‖c‖ = (ν x)⁻¹ := by
      dsimp [c]
      exact Complex.norm_of_nonneg (inv_nonneg.mpr (hν.nonneg x))
    have hx₀_norm : ν x₀ = 1 := by
      dsimp [x₀]
      rw [hν.smul, hc_norm]
      field_simp [ne_of_gt hxpos]
    have hx₀_le : complexVecLpNorm (ENNReal.ofReal targetX) x₀ ≤ 1 := by
      change ν x₀ ≤ 1
      rw [hx₀_norm]
    have hnormed :=
      complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_finite_dual_normer_one_top
        (A := A) (x := x₀)
        (p1 := p1) (q1 := q1)
        (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
        (targetX := targetX)
        (scaleY := scaleY) (rightY := rightY)
        (targetY := targetY) (M0 := M0) (M1 := M1) (θ := θ)
        hpq1 htargetYX
        hpowX0 hpowX1 hpowY1 hX hY hx₀_le
        hscaleX hleftX hrightX hscaleY hrightY hθ0 hθ1 hA0 hA1
    have hAx₀ :
        complexMatrixVecMul A x₀ =
          complexVecSMul c (complexMatrixVecMul A x) := by
      ext i
      dsimp [x₀, c, complexMatrixVecMul, complexVecSMul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    have hAx₀_norm :
        μ (complexMatrixVecMul A x₀) = (ν x)⁻¹ * μ (complexMatrixVecMul A x) := by
      rw [hAx₀]
      rw [hμ.smul, hc_norm]
    change μ (complexMatrixVecMul A x) ≤ C * ν x
    change μ (complexMatrixVecMul A x₀) ≤ C at hnormed
    rw [hAx₀_norm] at hnormed
    have hmul := mul_le_mul_of_nonneg_right hnormed (le_of_lt hxpos)
    calc
      μ (complexMatrixVecMul A x) =
          ((ν x)⁻¹ * μ (complexMatrixVecMul A x)) * ν x := by
            field_simp [ne_of_gt hxpos]
      _ ≤ C * ν x := hmul

/-- Endpoint Riesz-Thorin matrix-bound package with left endpoint `p = 1`,
    `q = ∞`, and a finite conjugate right endpoint. -/
theorem hasComplexMatrixLpBound_of_rieszThorin_one_top_finite_right
    {m n : ℕ} {A : CMatrix m n}
    {p1 q1 scaleX leftX rightX targetX
      scaleY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowX0 : (scaleX * leftX) * (1 : ℝ) = targetX)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * 0 + θ * rightY) = 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    HasComplexMatrixLpBound (ENNReal.ofReal targetX) A
      (M0 ^ (1 - θ) * M1 ^ θ) := by
  refine ⟨?_, ?_⟩
  · exact mul_nonneg
      (Real.rpow_nonneg hA0.1 (1 - θ))
      (Real.rpow_nonneg hA1.1 θ)
  · intro x
    exact
      complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_scaled_one_top
        (A := A) (x := x)
        (p1 := p1) (q1 := q1)
        (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
        (targetX := targetX)
        (scaleY := scaleY) (rightY := rightY)
        (targetY := targetY) (M0 := M0) (M1 := M1) (θ := θ)
        hpq1 htargetYX
        hpowX0 hpowX1 hpowY1 hX hY
        hscaleX hleftX hrightX hscaleY hrightY hθ0 hθ1 hA0 hA1

/-- Scalar Hadamard bound for the endpoint Riesz-Thorin case with left
    exponents `infinity` and `1`, and a finite conjugate right endpoint. -/
lemma complexRieszThorinAnalyticVec_matrixPairing_hadamard_affine_le_bound_top_one
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {p1 q1 scaleX rightX targetX
      scaleY leftY rightY targetY M0 M1 : ℝ} {z : ℂ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq1 : p1.HolderConjugate q1)
    (htargetX_pos : 0 < targetX) (htargetY_pos : 0 < targetY)
    (hpowY0 : (scaleY * leftY) * (1 : ℝ) = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1)
    (hA0 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    ‖∑ i : Fin m,
        complexRieszThorinAnalyticVec y
            (complexRieszThorinAffineExponent scaleY leftY rightY z) i *
          complexMatrixVecMul A
            (complexRieszThorinAnalyticVec x
              (complexRieszThorinAffineExponent scaleX 0 rightX z)) i‖ ≤
      M0 ^ (1 - z.re) * M1 ^ z.re := by
  refine
    complexRieszThorinAnalyticVec_matrixPairing_hadamard_norm_le_of_boundary
      (A := A) (x := x) (y := y)
      (pX := ENNReal.ofReal targetX) (pY := ENNReal.ofReal targetY)
      (scaleX := scaleX) (leftX := 0) (rightX := rightX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (M0 := M0) (M1 := M1) (z := z)
      hx hy hscaleX (by norm_num) hrightX hscaleY hleftY hrightY hz0 hz1 ?_ ?_
  · intro w hw
    have hwre : w.re = 0 := by
      simpa using hw
    exact complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_zero_top_one
      (A := A) (x := x) (y := y)
      (scaleX := scaleX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (targetY := targetY) (M := M0) (z := w)
      htargetY_pos hwre hpowY0 hx hy hscaleX hrightX hA0
  · intro w hw
    have hwre : w.re = 1 := by
      simpa using hw
    exact complexRieszThorinAnalyticVec_matrixPairing_affine_le_bound_of_re_one
      (A := A) (x := x) (y := y)
      (p := p1) (q := q1)
      (scaleX := scaleX) (leftX := 0) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (targetY := targetY) (M := M1) (z := w)
      hpq1 htargetX_pos htargetY_pos hwre hpowX1 hpowY1 hx hy hA1

/-- Interpolation-point matrix-image bound for the `infinity`/`1` endpoint
    case, assuming an explicit finite dual norming vector at the target
    exponent. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_norming_pair_top_one
    {m n : ℕ} {A : CMatrix m n} {x : CVec n} {y : CVec m}
    {p1 q1 scaleX rightX targetX
      scaleY leftY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq1 : p1.HolderConjugate q1)
    (htargetX_pos : 0 < targetX) (htargetY_pos : 0 < targetY)
    (hpowY0 : (scaleY * leftY) * (1 : ℝ) = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * 0 + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hy : complexVecLpNorm (ENNReal.ofReal targetY) y ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1)
    (hpair :
      complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) =
        ‖∑ i : Fin m, y i * complexMatrixVecMul A x i‖) :
    complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) ≤
      M0 ^ (1 - θ) * M1 ^ θ := by
  have hhad :
      ‖∑ i : Fin m,
          complexRieszThorinAnalyticVec y
              (complexRieszThorinAffineExponent scaleY leftY rightY (θ : ℂ)) i *
            complexMatrixVecMul A
              (complexRieszThorinAnalyticVec x
                (complexRieszThorinAffineExponent scaleX 0 rightX (θ : ℂ))) i‖ ≤
        M0 ^ (1 - (θ : ℂ).re) * M1 ^ (θ : ℂ).re :=
    complexRieszThorinAnalyticVec_matrixPairing_hadamard_affine_le_bound_top_one
      (A := A) (x := x) (y := y)
      (p1 := p1) (q1 := q1)
      (scaleX := scaleX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (targetY := targetY) (M0 := M0) (M1 := M1) (z := (θ : ℂ))
      hpq1 htargetX_pos htargetY_pos
      hpowY0 hpowX1 hpowY1 hx hy
      hscaleX hrightX hscaleY hleftY hrightY
      (by simpa using hθ0) (by simpa using hθ1) hA0 hA1
  have hrecover :=
    complexRieszThorinAnalyticVec_matrixPairing_norm_at_real_interpolation
      (A := A) (x := x) (y := y)
      (θ := θ) (scaleX := scaleX) (leftX := 0) (rightX := rightX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      hX hY
  rw [hrecover] at hhad
  simpa [hpair] using hhad

/-- Endpoint Riesz-Thorin matrix-image bound for the `infinity`/`1` left
    endpoint, with the finite-dimensional dual normer supplied automatically at
    the target exponent. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_finite_dual_normer_top_one
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {p1 q1 scaleX rightX targetX
      scaleY leftY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowY0 : (scaleY * leftY) * (1 : ℝ) = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * 0 + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hx : complexVecLpNorm (ENNReal.ofReal targetX) x ≤ 1)
    (hscaleX : 0 ≤ scaleX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) ≤
      M0 ^ (1 - θ) * M1 ^ θ := by
  obtain ⟨y, hy, hpair_row⟩ :=
    complexVecLpNorm_exists_rowNormingVector
      (n := m) (p := targetY) (q := targetX)
      htargetYX (complexMatrixVecMul A x)
  have hpair :
      complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) =
        ‖∑ i : Fin m, y i * complexMatrixVecMul A x i‖ := by
    have hsum_comm :
        (∑ i : Fin m, y i * complexMatrixVecMul A x i) =
          ∑ i : Fin m, complexMatrixVecMul A x i * y i := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [← hpair_row, hsum_comm]
  exact
    complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_norming_pair_top_one
      (A := A) (x := x) (y := y)
      (p1 := p1) (q1 := q1)
      (scaleX := scaleX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (targetY := targetY) (M0 := M0) (M1 := M1) (θ := θ)
      hpq1 htargetYX.symm.pos htargetYX.pos
      hpowY0 hpowX1 hpowY1 hX hY hx hy
      hscaleX hrightX hscaleY hleftY hrightY hθ0 hθ1 hA0 hA1 hpair

set_option linter.unusedTactic false in
/-- Arbitrary-vector form of the endpoint Riesz-Thorin matrix-image bound with
    left endpoint `p = infinity`, `q = 1`. -/
lemma complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_scaled_top_one
    {m n : ℕ} {A : CMatrix m n} {x : CVec n}
    {p1 q1 scaleX rightX targetX
      scaleY leftY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowY0 : (scaleY * leftY) * (1 : ℝ) = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * 0 + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hscaleX : 0 ≤ scaleX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    complexVecLpNorm (ENNReal.ofReal targetX) (complexMatrixVecMul A x) ≤
      (M0 ^ (1 - θ) * M1 ^ θ) *
        complexVecLpNorm (ENNReal.ofReal targetX) x := by
  -- Preserve frozen auxiliary names across the semantic module split.
  run_tac do
    let ngen ← Lean.getDeclNGen
    Lean.setDeclNGen { ngen with idx := 2 }
  let ν : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal targetX)
  let μ : CVec m → ℝ := complexVecLpNorm (n := m) (ENNReal.ofReal targetX)
  let C : ℝ := M0 ^ (1 - θ) * M1 ^ θ
  have hν : IsComplexVectorNorm ν :=
    complexVecLpNorm_isComplexVectorNorm (n := n) (ENNReal.ofReal targetX)
  have hμ : IsComplexVectorNorm μ :=
    complexVecLpNorm_isComplexVectorNorm (n := m) (ENNReal.ofReal targetX)
  by_cases hxzero : ν x = 0
  · have hx_eq : x = 0 := (hν.eq_zero_iff x).mp hxzero
    have hAx_zero : complexMatrixVecMul A x = 0 := by
      subst x
      ext i
      simp [complexMatrixVecMul]
    have hleft_zero : μ (complexMatrixVecMul A x) = 0 :=
      (hμ.eq_zero_iff (complexMatrixVecMul A x)).mpr hAx_zero
    change μ (complexMatrixVecMul A x) ≤ C * ν x
    rw [hleft_zero, hxzero, mul_zero]
  · have hxpos : 0 < ν x := lt_of_le_of_ne (hν.nonneg x) (Ne.symm hxzero)
    let c : ℂ := (((ν x)⁻¹ : ℝ) : ℂ)
    let x₀ : CVec n := complexVecSMul c x
    have hc_norm : ‖c‖ = (ν x)⁻¹ := by
      dsimp [c]
      exact Complex.norm_of_nonneg (inv_nonneg.mpr (hν.nonneg x))
    have hx₀_norm : ν x₀ = 1 := by
      dsimp [x₀]
      rw [hν.smul, hc_norm]
      field_simp [ne_of_gt hxpos]
    have hx₀_le : complexVecLpNorm (ENNReal.ofReal targetX) x₀ ≤ 1 := by
      change ν x₀ ≤ 1
      rw [hx₀_norm]
    have hnormed :=
      complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_of_finite_dual_normer_top_one
        (A := A) (x := x₀)
        (p1 := p1) (q1 := q1)
        (scaleX := scaleX) (rightX := rightX)
        (targetX := targetX)
        (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
        (targetY := targetY) (M0 := M0) (M1 := M1) (θ := θ)
        hpq1 htargetYX
        hpowY0 hpowX1 hpowY1 hX hY hx₀_le
        hscaleX hrightX hscaleY hleftY hrightY hθ0 hθ1 hA0 hA1
    have hAx₀ :
        complexMatrixVecMul A x₀ =
          complexVecSMul c (complexMatrixVecMul A x) := by
      ext i
      dsimp [x₀, c, complexMatrixVecMul, complexVecSMul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    have hAx₀_norm :
        μ (complexMatrixVecMul A x₀) = (ν x)⁻¹ * μ (complexMatrixVecMul A x) := by
      rw [hAx₀]
      rw [hμ.smul, hc_norm]
    change μ (complexMatrixVecMul A x) ≤ C * ν x
    change μ (complexMatrixVecMul A x₀) ≤ C at hnormed
    rw [hAx₀_norm] at hnormed
    have hmul := mul_le_mul_of_nonneg_right hnormed (le_of_lt hxpos)
    calc
      μ (complexMatrixVecMul A x) =
          ((ν x)⁻¹ * μ (complexMatrixVecMul A x)) * ν x := by
            field_simp [ne_of_gt hxpos]
      _ ≤ C * ν x := hmul

/-- Endpoint Riesz-Thorin matrix-bound package with left endpoint `p = ∞`,
    `q = 1`, and a finite conjugate right endpoint. -/
theorem hasComplexMatrixLpBound_of_rieszThorin_top_one_finite_right
    {m n : ℕ} {A : CMatrix m n}
    {p1 q1 scaleX rightX targetX
      scaleY leftY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowY0 : (scaleY * leftY) * (1 : ℝ) = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * 0 + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hscaleX : 0 ≤ scaleX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    HasComplexMatrixLpBound (ENNReal.ofReal targetX) A
      (M0 ^ (1 - θ) * M1 ^ θ) := by
  refine ⟨?_, ?_⟩
  · exact mul_nonneg
      (Real.rpow_nonneg hA0.1 (1 - θ))
      (Real.rpow_nonneg hA1.1 θ)
  · intro x
    exact
      complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_scaled_top_one
        (A := A) (x := x)
        (p1 := p1) (q1 := q1)
        (scaleX := scaleX) (rightX := rightX)
        (targetX := targetX)
        (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
        (targetY := targetY) (M0 := M0) (M1 := M1) (θ := θ)
        hpq1 htargetYX
        hpowY0 hpowX1 hpowY1 hX hY
        hscaleX hrightX hscaleY hleftY hrightY hθ0 hθ1 hA0 hA1

/-- Endpoint Riesz-Thorin matrix-bound package with a finite conjugate left
    endpoint and right endpoint `p = ∞`, `q = 1`.  This is obtained from the
    left-endpoint `∞`/`1` package by swapping endpoints and replacing `θ` by
    `1 - θ`. -/
theorem hasComplexMatrixLpBound_of_rieszThorin_finite_left_top_one
    {m n : ℕ} {A : CMatrix m n}
    {p0 q0 scaleX leftX targetX
      scaleY leftY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq0 : p0.HolderConjugate q0)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowX0 : (scaleX * leftX) * p0 = targetX)
    (hpowY0 : (scaleY * leftY) * q0 = targetY)
    (hpowY1 : (scaleY * rightY) * (1 : ℝ) = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * 0) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M1) :
    HasComplexMatrixLpBound (ENNReal.ofReal targetX) A
      (M0 ^ (1 - θ) * M1 ^ θ) := by
  have hXswap :
      scaleX * ((1 - (1 - θ)) * 0 + (1 - θ) * leftX) = 1 := by
    calc
      scaleX * ((1 - (1 - θ)) * 0 + (1 - θ) * leftX)
          = scaleX * ((1 - θ) * leftX + θ * 0) := by ring
      _ = 1 := hX
  have hYswap :
      scaleY * ((1 - (1 - θ)) * rightY + (1 - θ) * leftY) = 1 := by
    calc
      scaleY * ((1 - (1 - θ)) * rightY + (1 - θ) * leftY)
          = scaleY * ((1 - θ) * leftY + θ * rightY) := by ring
      _ = 1 := hY
  have hθswap0 : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hθswap1 : 1 - θ ≤ 1 := by linarith
  have hswap :
      HasComplexMatrixLpBound (ENNReal.ofReal targetX) A
        (M1 ^ (1 - (1 - θ)) * M0 ^ (1 - θ)) :=
    hasComplexMatrixLpBound_of_rieszThorin_top_one_finite_right
      (A := A)
      (p1 := p0) (q1 := q0)
      (scaleX := scaleX) (rightX := leftX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := rightY) (rightY := leftY)
      (targetY := targetY) (M0 := M1) (M1 := M0) (θ := 1 - θ)
      hpq0 htargetYX
      hpowY1 hpowX0 hpowY0 hXswap hYswap
      hscaleX hleftX hscaleY hrightY hleftY hθswap0 hθswap1 hA1 hA0
  refine ⟨?_, ?_⟩
  · exact mul_nonneg
      (Real.rpow_nonneg hA0.1 (1 - θ))
      (Real.rpow_nonneg hA1.1 θ)
  · intro x
    have hx := hswap.2 x
    simpa [mul_comm, mul_left_comm, mul_assoc] using hx

/-- Endpoint Riesz-Thorin matrix-bound package with a finite conjugate left
    endpoint and right endpoint `p = 1`, `q = ∞`.  This is obtained from the
    left-endpoint `1`/`∞` package by swapping endpoints and replacing `θ` by
    `1 - θ`. -/
theorem hasComplexMatrixLpBound_of_rieszThorin_finite_left_one_top
    {m n : ℕ} {A : CMatrix m n}
    {p0 q0 scaleX leftX rightX targetX
      scaleY leftY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq0 : p0.HolderConjugate q0)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowX0 : (scaleX * leftX) * p0 = targetX)
    (hpowY0 : (scaleY * leftY) * q0 = targetY)
    (hpowX1 : (scaleX * rightX) * (1 : ℝ) = targetX)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * 0) = 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M1) :
    HasComplexMatrixLpBound (ENNReal.ofReal targetX) A
      (M0 ^ (1 - θ) * M1 ^ θ) := by
  have hXswap :
      scaleX * ((1 - (1 - θ)) * rightX + (1 - θ) * leftX) = 1 := by
    calc
      scaleX * ((1 - (1 - θ)) * rightX + (1 - θ) * leftX)
          = scaleX * ((1 - θ) * leftX + θ * rightX) := by ring
      _ = 1 := hX
  have hYswap :
      scaleY * ((1 - (1 - θ)) * 0 + (1 - θ) * leftY) = 1 := by
    calc
      scaleY * ((1 - (1 - θ)) * 0 + (1 - θ) * leftY)
          = scaleY * ((1 - θ) * leftY + θ * 0) := by ring
      _ = 1 := hY
  have hθswap0 : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hθswap1 : 1 - θ ≤ 1 := by linarith
  have hswap :
      HasComplexMatrixLpBound (ENNReal.ofReal targetX) A
        (M1 ^ (1 - (1 - θ)) * M0 ^ (1 - θ)) :=
    hasComplexMatrixLpBound_of_rieszThorin_one_top_finite_right
      (A := A)
      (p1 := p0) (q1 := q0)
      (scaleX := scaleX) (leftX := rightX) (rightX := leftX)
      (targetX := targetX)
      (scaleY := scaleY) (rightY := leftY)
      (targetY := targetY) (M0 := M1) (M1 := M0) (θ := 1 - θ)
      hpq0 htargetYX
      hpowX1 hpowX0 hpowY0 hXswap hYswap
      hscaleX hrightX hleftX hscaleY hleftY hθswap0 hθswap1 hA1 hA0
  refine ⟨?_, ?_⟩
  · exact mul_nonneg
      (Real.rpow_nonneg hA0.1 (1 - θ))
      (Real.rpow_nonneg hA1.1 θ)
  · intro x
    have hx := hswap.2 x
    simpa [mul_comm, mul_left_comm, mul_assoc] using hx

/-- Source-facing endpoint Riesz-Thorin matrix-bound wrapper with left endpoint
    `p₀ = 1`, `q₀ = ∞` and a finite conjugate right endpoint, with the source
    exponent relation stated through `LpInterpolationData`. -/
theorem hasComplexMatrixLpBound_of_rieszThorin_one_top_left_of_interpolationData
    {m n : ℕ} {A : CMatrix m n}
    {p1 q1 r q θ M0 M1 : ℝ}
    (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData 1 (ENNReal.ofReal p1) (ENNReal.ofReal r) θ)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    HasComplexMatrixLpBound (ENNReal.ofReal r) A
      (M0 ^ (1 - θ) * M1 ^ θ) := by
  haveI htargetXFact : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.lt⟩
  haveI htargetYFact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.symm.lt⟩
  have hθq : LpInterpolationData ∞ (ENNReal.ofReal q1) (ENNReal.ofReal q) θ :=
    LpInterpolationData.conjugate
      LpConjugateExponents.one_top
      (LpConjugateExponents.ofReal_holderConjugate hpq1)
      (LpConjugateExponents.ofReal_holderConjugate hrq)
      hθ
  have hX : r * ((1 - θ) * (1 : ℝ) + θ * p1⁻¹) = 1 :=
    LpInterpolationData.affineExponent_eq_one_one_left_ofReal
      hpq1.pos hrq.pos hθ
  have hY : q * ((1 - θ) * (0 : ℝ) + θ * q1⁻¹) = 1 :=
    LpInterpolationData.affineExponent_eq_one_top_left_ofReal
      hpq1.symm.pos hrq.symm.pos hθq
  have hpowX0 : (r * (1 : ℝ)) * (1 : ℝ) = r := by ring
  have hpowX1 : (r * p1⁻¹) * p1 = r := by
    field_simp [ne_of_gt hpq1.pos]
  have hpowY1 : (q * q1⁻¹) * q1 = q := by
    field_simp [ne_of_gt hpq1.symm.pos]
  exact
    hasComplexMatrixLpBound_of_rieszThorin_one_top_finite_right
      (A := A)
      (p1 := p1) (q1 := q1)
      (scaleX := r) (leftX := (1 : ℝ)) (rightX := p1⁻¹)
      (targetX := r)
      (scaleY := q) (rightY := q1⁻¹)
      (targetY := q) (M0 := M0) (M1 := M1) (θ := θ)
      hpq1 hrq.symm hpowX0 hpowX1 hpowY1 hX hY
      (le_of_lt hrq.pos) zero_le_one (inv_nonneg.mpr (le_of_lt hpq1.pos))
      (le_of_lt hrq.symm.pos) (inv_nonneg.mpr (le_of_lt hpq1.symm.pos))
      hθ.theta_nonneg hθ.theta_le_one hA0 hA1

/-- Source-facing endpoint Riesz-Thorin matrix-bound wrapper with left endpoint
    `p₀ = ∞`, `q₀ = 1` and a finite conjugate right endpoint, with the source
    exponent relation stated through `LpInterpolationData`. -/
theorem hasComplexMatrixLpBound_of_rieszThorin_top_one_left_of_interpolationData
    {m n : ℕ} {A : CMatrix m n}
    {p1 q1 r q θ M0 M1 : ℝ}
    (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData ∞ (ENNReal.ofReal p1) (ENNReal.ofReal r) θ)
    (hA0 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    HasComplexMatrixLpBound (ENNReal.ofReal r) A
      (M0 ^ (1 - θ) * M1 ^ θ) := by
  haveI htargetXFact : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.lt⟩
  haveI htargetYFact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.symm.lt⟩
  have hθq : LpInterpolationData 1 (ENNReal.ofReal q1) (ENNReal.ofReal q) θ :=
    LpInterpolationData.conjugate
      LpConjugateExponents.top_one
      (LpConjugateExponents.ofReal_holderConjugate hpq1)
      (LpConjugateExponents.ofReal_holderConjugate hrq)
      hθ
  have hX : r * ((1 - θ) * (0 : ℝ) + θ * p1⁻¹) = 1 :=
    LpInterpolationData.affineExponent_eq_one_top_left_ofReal
      hpq1.pos hrq.pos hθ
  have hY : q * ((1 - θ) * (1 : ℝ) + θ * q1⁻¹) = 1 :=
    LpInterpolationData.affineExponent_eq_one_one_left_ofReal
      hpq1.symm.pos hrq.symm.pos hθq
  have hpowY0 : (q * (1 : ℝ)) * (1 : ℝ) = q := by ring
  have hpowX1 : (r * p1⁻¹) * p1 = r := by
    field_simp [ne_of_gt hpq1.pos]
  have hpowY1 : (q * q1⁻¹) * q1 = q := by
    field_simp [ne_of_gt hpq1.symm.pos]
  exact
    hasComplexMatrixLpBound_of_rieszThorin_top_one_finite_right
      (A := A)
      (p1 := p1) (q1 := q1)
      (scaleX := r) (rightX := p1⁻¹)
      (targetX := r)
      (scaleY := q) (leftY := (1 : ℝ)) (rightY := q1⁻¹)
      (targetY := q) (M0 := M0) (M1 := M1) (θ := θ)
      hpq1 hrq.symm hpowY0 hpowX1 hpowY1 hX hY
      (le_of_lt hrq.pos) (inv_nonneg.mpr (le_of_lt hpq1.pos))
      (le_of_lt hrq.symm.pos) zero_le_one (inv_nonneg.mpr (le_of_lt hpq1.symm.pos))
      hθ.theta_nonneg hθ.theta_le_one hA0 hA1

/-- Source-facing endpoint Riesz-Thorin matrix-bound wrapper with a finite
    conjugate left endpoint and right endpoint `p₁ = ∞`, `q₁ = 1`, with the
    source exponent relation stated through `LpInterpolationData`. -/
theorem hasComplexMatrixLpBound_of_rieszThorin_finite_left_top_one_of_interpolationData
    {m n : ℕ} {A : CMatrix m n}
    {p0 q0 r q θ M0 M1 : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData (ENNReal.ofReal p0) ∞ (ENNReal.ofReal r) θ)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M1) :
    HasComplexMatrixLpBound (ENNReal.ofReal r) A
      (M0 ^ (1 - θ) * M1 ^ θ) := by
  haveI htargetXFact : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.lt⟩
  haveI htargetYFact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.symm.lt⟩
  have hθq : LpInterpolationData (ENNReal.ofReal q0) 1 (ENNReal.ofReal q) θ :=
    LpInterpolationData.conjugate
      (LpConjugateExponents.ofReal_holderConjugate hpq0)
      LpConjugateExponents.top_one
      (LpConjugateExponents.ofReal_holderConjugate hrq)
      hθ
  have hX : r * ((1 - θ) * p0⁻¹ + θ * (0 : ℝ)) = 1 :=
    LpInterpolationData.affineExponent_eq_one_top_right_ofReal
      hpq0.pos hrq.pos hθ
  have hY : q * ((1 - θ) * q0⁻¹ + θ * (1 : ℝ)) = 1 :=
    LpInterpolationData.affineExponent_eq_one_one_right_ofReal
      hpq0.symm.pos hrq.symm.pos hθq
  have hpowX0 : (r * p0⁻¹) * p0 = r := by
    field_simp [ne_of_gt hpq0.pos]
  have hpowY0 : (q * q0⁻¹) * q0 = q := by
    field_simp [ne_of_gt hpq0.symm.pos]
  have hpowY1 : (q * (1 : ℝ)) * (1 : ℝ) = q := by ring
  exact
    hasComplexMatrixLpBound_of_rieszThorin_finite_left_top_one
      (A := A)
      (p0 := p0) (q0 := q0)
      (scaleX := r) (leftX := p0⁻¹)
      (targetX := r)
      (scaleY := q) (leftY := q0⁻¹) (rightY := (1 : ℝ))
      (targetY := q) (M0 := M0) (M1 := M1) (θ := θ)
      hpq0 hrq.symm hpowX0 hpowY0 hpowY1 hX hY
      (le_of_lt hrq.pos) (inv_nonneg.mpr (le_of_lt hpq0.pos))
      (le_of_lt hrq.symm.pos) (inv_nonneg.mpr (le_of_lt hpq0.symm.pos)) zero_le_one
      hθ.theta_nonneg hθ.theta_le_one hA0 hA1

/-- Source-facing endpoint Riesz-Thorin matrix-bound wrapper with a finite
    conjugate left endpoint and right endpoint `p₁ = 1`, `q₁ = ∞`, with the
    source exponent relation stated through `LpInterpolationData`. -/
theorem hasComplexMatrixLpBound_of_rieszThorin_finite_left_one_top_of_interpolationData
    {m n : ℕ} {A : CMatrix m n}
    {p0 q0 r q θ M0 M1 : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData (ENNReal.ofReal p0) 1 (ENNReal.ofReal r) θ)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M1) :
    HasComplexMatrixLpBound (ENNReal.ofReal r) A
      (M0 ^ (1 - θ) * M1 ^ θ) := by
  haveI htargetXFact : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.lt⟩
  haveI htargetYFact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.symm.lt⟩
  have hθq : LpInterpolationData (ENNReal.ofReal q0) ∞ (ENNReal.ofReal q) θ :=
    LpInterpolationData.conjugate
      (LpConjugateExponents.ofReal_holderConjugate hpq0)
      LpConjugateExponents.one_top
      (LpConjugateExponents.ofReal_holderConjugate hrq)
      hθ
  have hX : r * ((1 - θ) * p0⁻¹ + θ * (1 : ℝ)) = 1 :=
    LpInterpolationData.affineExponent_eq_one_one_right_ofReal
      hpq0.pos hrq.pos hθ
  have hY : q * ((1 - θ) * q0⁻¹ + θ * (0 : ℝ)) = 1 :=
    LpInterpolationData.affineExponent_eq_one_top_right_ofReal
      hpq0.symm.pos hrq.symm.pos hθq
  have hpowX0 : (r * p0⁻¹) * p0 = r := by
    field_simp [ne_of_gt hpq0.pos]
  have hpowY0 : (q * q0⁻¹) * q0 = q := by
    field_simp [ne_of_gt hpq0.symm.pos]
  have hpowX1 : (r * (1 : ℝ)) * (1 : ℝ) = r := by ring
  exact
    hasComplexMatrixLpBound_of_rieszThorin_finite_left_one_top
      (A := A)
      (p0 := p0) (q0 := q0)
      (scaleX := r) (leftX := p0⁻¹) (rightX := (1 : ℝ))
      (targetX := r)
      (scaleY := q) (leftY := q0⁻¹)
      (targetY := q) (M0 := M0) (M1 := M1) (θ := θ)
      hpq0 hrq.symm hpowX0 hpowY0 hpowX1 hX hY
      (le_of_lt hrq.pos) (inv_nonneg.mpr (le_of_lt hpq0.pos)) zero_le_one
      (le_of_lt hrq.symm.pos) (inv_nonneg.mpr (le_of_lt hpq0.symm.pos))
      hθ.theta_nonneg hθ.theta_le_one hA0 hA1

/-- Finite-real Riesz-Thorin matrix-bound package for the analytic interior
    parameterization, assuming the source/dual affine exponents and endpoint
    matrix bounds already match the target exponent data. -/
theorem hasComplexMatrixLpBound_of_rieszThorin_finite_dual_normer
    {m n : ℕ} {A : CMatrix m n}
    {p0 q0 p1 q1 scaleX leftX rightX targetX
      scaleY leftY rightY targetY M0 M1 θ : ℝ}
    [Fact (1 ≤ ENNReal.ofReal targetX)] [Fact (1 ≤ ENNReal.ofReal targetY)]
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowX0 : (scaleX * leftX) * p0 = targetX)
    (hpowY0 : (scaleY * leftY) * q0 = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    HasComplexMatrixLpBound (ENNReal.ofReal targetX) A
      (M0 ^ (1 - θ) * M1 ^ θ) := by
  refine ⟨?_, ?_⟩
  · exact mul_nonneg
      (Real.rpow_nonneg hA0.1 (1 - θ))
      (Real.rpow_nonneg hA1.1 θ)
  · intro x
    exact
      complexRieszThorinAnalyticVec_matrixImage_lpNorm_le_hadamard_scaled
        (A := A) (x := x)
        (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1)
        (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
        (targetX := targetX)
        (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
        (targetY := targetY) (M0 := M0) (M1 := M1) (θ := θ)
        hpq0 hpq1 htargetYX
        hpowX0 hpowY0 hpowX1 hpowY1 hX hY
        hscaleX hleftX hrightX hscaleY hleftY hrightY hθ0 hθ1 hA0 hA1

theorem hasComplexMatrixLpBound_congr_exponent
    {m n : ℕ} {p q : ℝ≥0∞} {A : CMatrix m n} {C : ℝ}
    (hpq : p = q) (hbound : HasComplexMatrixLpBound p A C) :
    HasComplexMatrixLpBound q A C := by
  subst q
  exact hbound

/-- Endpoint case for the future Riesz-Thorin matrix-bound theorem: when
    `theta = 0`, reciprocal-exponent injectivity identifies `r` with `p₀`,
    so the left endpoint bound is already an `r`-bound. -/
theorem hasComplexMatrixLpBound_of_interpolation_theta_zero
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₀ : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ0 : θ = 0)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀) :
    HasComplexMatrixLpBound r A M₀ := by
  have hrp₀ : r = p₀ :=
    hθ.eq_left_of_theta_zero hp₀ hr hθ0
  exact hasComplexMatrixLpBound_congr_exponent hrp₀.symm h₀

/-- Endpoint case for the future Riesz-Thorin matrix-bound theorem: when
    `theta = 1`, reciprocal-exponent injectivity identifies `r` with `p₁`,
    so the right endpoint bound is already an `r`-bound. -/
theorem hasComplexMatrixLpBound_of_interpolation_theta_one
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₁ : ℝ}
    {A : CMatrix m n}
    (hp₁ : 1 ≤ p₁) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ1 : θ = 1)
    (h₁ : HasComplexMatrixLpBound p₁ A M₁) :
    HasComplexMatrixLpBound r A M₁ := by
  have hrp₁ : r = p₁ :=
    hθ.eq_right_of_theta_one hp₁ hr hθ1
  exact hasComplexMatrixLpBound_congr_exponent hrp₁.symm h₁

/-- Strict-interior endpoint reduction for the future Riesz-Thorin
    matrix-bound theorem: if `0 < theta < 1` and the interpolated exponent is
    `1`, both endpoint exponents are also `1`, so any left endpoint bound is an
    `r`-bound. -/
theorem hasComplexMatrixLpBound_of_interpolation_strict_eq_one
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₀ : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = 1)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀) :
    HasComplexMatrixLpBound r A M₀ := by
  obtain ⟨hp₀_one, _hp₁_one⟩ :=
    hθ.endpoints_eq_one_of_strict_of_eq_one hp₀ hp₁ hθ0 hθ1 hr
  have hp₀r : p₀ = r := by
    rw [hp₀_one, hr]
  exact hasComplexMatrixLpBound_congr_exponent hp₀r h₀

/-- Strict-interior endpoint reduction for the future Riesz-Thorin
    matrix-bound theorem: if `0 < theta < 1` and the interpolated exponent is
    infinity, both endpoint exponents are infinity, so any left endpoint bound
    is an `r`-bound. -/
theorem hasComplexMatrixLpBound_of_interpolation_strict_eq_top
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₀ : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = ∞)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀) :
    HasComplexMatrixLpBound r A M₀ := by
  obtain ⟨hp₀_top, _hp₁_top⟩ :=
    hθ.endpoints_eq_top_of_strict_of_eq_top hp₀ hp₁ hθ0 hθ1 hr
  have hp₀r : p₀ = r := by
    rw [hp₀_top, hr]
  exact hasComplexMatrixLpBound_congr_exponent hp₀r h₀

/-- Scalar endpoint reduction used in the endpoint-unified Riesz-Thorin
    package: the smaller of two nonnegative endpoint bounds is bounded by
    their geometric interpolation.  Mathlib's `Real.rpow` convention includes
    `0 ^ 0 = 1`, so this also covers `θ = 0` and `θ = 1`. -/
theorem min_le_rpow_interp_of_nonneg {a b θ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min a b ≤ a ^ (1 - θ) * b ^ θ := by
  by_cases hab : a ≤ b
  · by_cases ha0 : a = 0
    · subst a
      have hnonneg : 0 ≤ 0 ^ (1 - θ) * b ^ θ :=
        mul_nonneg (Real.rpow_nonneg (le_refl 0) (1 - θ))
          (Real.rpow_nonneg hb θ)
      simpa [min_eq_left hb] using hnonneg
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hratio : 1 ≤ b / a := by
      rw [one_le_div hapos]
      exact hab
    have hone : 1 ≤ (b / a) ^ θ := Real.one_le_rpow hratio hθ0
    have hmain : a ≤ a * (b / a) ^ θ := by
      simpa using mul_le_mul_of_nonneg_left hone ha
    calc
      min a b = a := min_eq_left hab
      _ ≤ a * (b / a) ^ θ := hmain
      _ = a ^ (1 - θ) * b ^ θ := by
        calc
          a * (b / a) ^ θ =
              (a ^ (1 - θ) * a ^ θ) * (b / a) ^ θ := by
                rw [← Real.rpow_add hapos]
                · rw [show 1 - θ + θ = 1 by ring, Real.rpow_one]
          _ = a ^ (1 - θ) * (a ^ θ * (b / a) ^ θ) := by ring
          _ = a ^ (1 - θ) * (a * (b / a)) ^ θ := by
                rw [Real.mul_rpow (le_of_lt hapos) (div_nonneg hb ha)]
          _ = a ^ (1 - θ) * b ^ θ := by
                rw [show a * (b / a) = b by field_simp [ne_of_gt hapos]]
  · have hba : b ≤ a := le_of_not_ge hab
    by_cases hb0 : b = 0
    · subst b
      have hnonneg : 0 ≤ a ^ (1 - θ) * 0 ^ θ :=
        mul_nonneg (Real.rpow_nonneg ha (1 - θ))
          (Real.rpow_nonneg (le_refl 0) θ)
      simpa [min_eq_right ha] using hnonneg
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hratio : 1 ≤ a / b := by
      rw [one_le_div hbpos]
      exact hba
    have h_exp_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    have hone : 1 ≤ (a / b) ^ (1 - θ) :=
      Real.one_le_rpow hratio h_exp_nonneg
    have hmain : b ≤ b * (a / b) ^ (1 - θ) := by
      simpa using mul_le_mul_of_nonneg_left hone hb
    calc
      min a b = b := min_eq_right hba
      _ ≤ b * (a / b) ^ (1 - θ) := hmain
      _ = a ^ (1 - θ) * b ^ θ := by
        calc
          b * (a / b) ^ (1 - θ) =
              (b ^ θ * b ^ (1 - θ)) * (a / b) ^ (1 - θ) := by
                rw [← Real.rpow_add hbpos]
                · rw [show θ + (1 - θ) = 1 by ring, Real.rpow_one]
          _ = b ^ θ * (b ^ (1 - θ) * (a / b) ^ (1 - θ)) := by ring
          _ = b ^ θ * (b * (a / b)) ^ (1 - θ) := by
                rw [Real.mul_rpow (le_of_lt hbpos) (div_nonneg ha hb)]
          _ = b ^ θ * a ^ (1 - θ) := by
                rw [show b * (a / b) = a by field_simp [ne_of_gt hbpos]]
          _ = a ^ (1 - θ) * b ^ θ := by ring

theorem isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound
    {m n : ℕ} {p : ℝ≥0∞} {A : CMatrix m n} {c C : ℝ}
    (hA : IsComplexMatrixLpNormValue p A c)
    (hbound : HasComplexMatrixLpBound p A C) :
    c ≤ C := by
  exact hA.2 C hbound.2

/-- Any two local least values for the same complex matrix `p`-norm coincide.
    This lets source-facing existence predicates be converted back to the
    concrete chosen norm without adding a new mathematical assumption. -/
theorem isComplexMatrixLpNormValue_unique
    {m n : ℕ} {p : ℝ≥0∞} {A : CMatrix m n} {c d : ℝ}
    (hc : IsComplexMatrixLpNormValue p A c)
    (hd : IsComplexMatrixLpNormValue p A d) :
    c = d := by
  exact le_antisymm (hc.2 d hd.1) (hd.2 c hc.1)

/-- Source-facing endpoint wrapper for the `theta = 0` interpolation reduction:
    the target least `r`-norm value is bounded by the left endpoint bound. -/
theorem isComplexMatrixLpNormValue_le_of_interpolation_theta_zero
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₀ N : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ0 : θ = 0)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀)
    (hN : IsComplexMatrixLpNormValue r A N) :
    N ≤ M₀ :=
  isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
    (hasComplexMatrixLpBound_of_interpolation_theta_zero
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀) (A := A) hp₀ hr hθ hθ0 h₀)

/-- Source-facing endpoint wrapper for the `theta = 1` interpolation reduction:
    the target least `r`-norm value is bounded by the right endpoint bound. -/
theorem isComplexMatrixLpNormValue_le_of_interpolation_theta_one
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₁ N : ℝ}
    {A : CMatrix m n}
    (hp₁ : 1 ≤ p₁) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ1 : θ = 1)
    (h₁ : HasComplexMatrixLpBound p₁ A M₁)
    (hN : IsComplexMatrixLpNormValue r A N) :
    N ≤ M₁ :=
  isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
    (hasComplexMatrixLpBound_of_interpolation_theta_one
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₁ := M₁) (A := A) hp₁ hr hθ hθ1 h₁)

/-- Geometric Riesz-Thorin endpoint wrapper for `theta = 0`: the logarithmic
    interpolation right-hand side reduces to the left endpoint bound. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_endpoint_theta_zero
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₀ M₁ N : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ0 : θ = 0)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀)
    (hN : IsComplexMatrixLpNormValue r A N) :
    N ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  have hmain :
      N ≤ M₀ :=
    isComplexMatrixLpNormValue_le_of_interpolation_theta_zero
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀) (N := N) (A := A)
      hp₀ hr hθ hθ0 h₀ hN
  simpa [hθ0] using hmain

/-- Geometric Riesz-Thorin endpoint wrapper for `theta = 1`: the logarithmic
    interpolation right-hand side reduces to the right endpoint bound. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_endpoint_theta_one
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₀ M₁ N : ℝ}
    {A : CMatrix m n}
    (hp₁ : 1 ≤ p₁) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ1 : θ = 1)
    (h₁ : HasComplexMatrixLpBound p₁ A M₁)
    (hN : IsComplexMatrixLpNormValue r A N) :
    N ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  have hmain :
      N ≤ M₁ :=
    isComplexMatrixLpNormValue_le_of_interpolation_theta_one
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₁ := M₁) (N := N) (A := A)
      hp₁ hr hθ hθ1 h₁ hN
  simpa [hθ1] using hmain

/-- Source-facing strict-interior endpoint wrapper: if the interpolated exponent
    is `1`, the target least norm value is bounded by the left endpoint bound. -/
theorem isComplexMatrixLpNormValue_le_of_interpolation_strict_eq_one
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₀ N : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = 1)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀)
    (hN : IsComplexMatrixLpNormValue r A N) :
    N ≤ M₀ :=
  isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
    (hasComplexMatrixLpBound_of_interpolation_strict_eq_one
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀) (A := A) hp₀ hp₁ hθ hθ0 hθ1 hr h₀)

/-- Source-facing strict-interior endpoint wrapper: if the interpolated exponent
    is infinity, the target least norm value is bounded by the left endpoint
    bound. -/
theorem isComplexMatrixLpNormValue_le_of_interpolation_strict_eq_top
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₀ N : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = ∞)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀)
    (hN : IsComplexMatrixLpNormValue r A N) :
    N ≤ M₀ :=
  isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
    (hasComplexMatrixLpBound_of_interpolation_strict_eq_top
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀) (A := A) hp₀ hp₁ hθ hθ0 hθ1 hr h₀)

/-- Strict-interior endpoint wrapper with the geometric Riesz-Thorin right-hand
    side for the case `r = 1`.  Since strict interpolation can hit `1` only
    when both endpoint exponents are `1`, both endpoint bounds are available
    at the target exponent and the smaller one is bounded by the geometric
    interpolation of the endpoint constants. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_strict_eq_one
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₀ M₁ N : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = 1)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀)
    (h₁ : HasComplexMatrixLpBound p₁ A M₁)
    (hN : IsComplexMatrixLpNormValue r A N) :
    N ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  obtain ⟨hp₀_one, hp₁_one⟩ :=
    hθ.endpoints_eq_one_of_strict_of_eq_one hp₀ hp₁ hθ0 hθ1 hr
  have hN0 : N ≤ M₀ :=
    isComplexMatrixLpNormValue_le_of_interpolation_strict_eq_one
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀) (N := N) (A := A)
      hp₀ hp₁ hθ hθ0 hθ1 hr h₀ hN
  have hp₁r : p₁ = r := by
    rw [hp₁_one, hr]
  have hN1 : N ≤ M₁ :=
    isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
      (hasComplexMatrixLpBound_congr_exponent hp₁r h₁)
  exact (le_min hN0 hN1).trans
    (min_le_rpow_interp_of_nonneg h₀.1 h₁.1 hθ.theta_nonneg hθ.theta_le_one)

/-- Strict-interior endpoint wrapper with the geometric Riesz-Thorin right-hand
    side for the case `r = ∞`. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_strict_eq_top
    {m n : ℕ} {p₀ p₁ r : ℝ≥0∞} {θ M₀ M₁ N : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = ∞)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀)
    (h₁ : HasComplexMatrixLpBound p₁ A M₁)
    (hN : IsComplexMatrixLpNormValue r A N) :
    N ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  obtain ⟨hp₀_top, hp₁_top⟩ :=
    hθ.endpoints_eq_top_of_strict_of_eq_top hp₀ hp₁ hθ0 hθ1 hr
  have hN0 : N ≤ M₀ :=
    isComplexMatrixLpNormValue_le_of_interpolation_strict_eq_top
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀) (N := N) (A := A)
      hp₀ hp₁ hθ hθ0 hθ1 hr h₀ hN
  have hp₁r : p₁ = r := by
    rw [hp₁_top, hr]
  have hN1 : N ≤ M₁ :=
    isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
      (hasComplexMatrixLpBound_congr_exponent hp₁r h₁)
  exact (le_min hN0 hN1).trans
    (min_le_rpow_interp_of_nonneg h₀.1 h₁.1 hθ.theta_nonneg hθ.theta_le_one)

/-- Upper-bound half of Problem 6.11(a): the maximum column norm is always a
    valid mixed subordinate bound from the source 1-norm to the target norm.
    Unlike the least-value theorem, this direction does not need a nonempty
    source dimension. -/
theorem complexMatrixColumnMaxVectorNorm_mixedSubordinateMatrixBound
    {m n : ℕ} {νβ : CVec m → ℝ} (hβ : IsComplexVectorNorm νβ)
    (A : CMatrix m n) :
    MixedSubordinateMatrixBound complexVecOneNorm νβ A
      (complexMatrixColumnMaxVectorNorm νβ A) := by
  intro x
  have hsum :
      νβ (fun i : Fin m =>
          ∑ j : Fin n, complexVecSMul (x j) (fun k : Fin m => A k j) i) ≤
        ∑ j : Fin n, νβ (complexVecSMul (x j) (fun k : Fin m => A k j)) :=
    hβ.sum_le (fun j : Fin n => complexVecSMul (x j) (fun k : Fin m => A k j))
  have hAx :
      complexMatrixVecMul A x =
        fun i : Fin m =>
          ∑ j : Fin n, complexVecSMul (x j) (fun k : Fin m => A k j) i := by
    ext i
    unfold complexMatrixVecMul complexVecSMul
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  calc
    νβ (complexMatrixVecMul A x)
        = νβ (fun i : Fin m =>
            ∑ j : Fin n, complexVecSMul (x j) (fun k : Fin m => A k j) i) := by
            rw [hAx]
    _ ≤ ∑ j : Fin n, νβ (complexVecSMul (x j) (fun k : Fin m => A k j)) := hsum
    _ = ∑ j : Fin n, ‖x j‖ * νβ (fun i : Fin m => A i j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          exact hβ.smul (x j) (fun i : Fin m => A i j)
    _ ≤ ∑ j : Fin n, complexMatrixColumnMaxVectorNorm νβ A * ‖x j‖ := by
          apply Finset.sum_le_sum
          intro j _hj
          have hcol :=
            mul_le_mul_of_nonneg_left
              (complexMatrixColumnMaxVectorNorm_col_le hβ A j) (norm_nonneg (x j))
          simpa [mul_comm, mul_left_comm, mul_assoc] using hcol
    _ = complexMatrixColumnMaxVectorNorm νβ A * ∑ j : Fin n, ‖x j‖ := by
          rw [Finset.mul_sum]
    _ = complexMatrixColumnMaxVectorNorm νβ A * complexVecOneNorm x := by
          rfl

/-- General upper-bound half of Higham equation (6.12), as a mixed subordinate
    bound: the matrix acting from finite `L^p` to finite `L^p` is bounded by
    `n^(1-1/p)` times the maximum `L^p` norm of its columns. -/
theorem complexMatrixLpNorm_upper_bound_by_columnMax_lpNorm
    {m n : ℕ} {p : ℝ} (hp : 1 ≤ p) (A : CMatrix m n) :
    MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A
      ((n : ℝ) ^ (1 - p⁻¹) *
        complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A) := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  let νβ : CVec m → ℝ := complexVecLpNorm (n := m) (ENNReal.ofReal p)
  let M : ℝ := complexMatrixColumnMaxVectorNorm νβ A
  let c : ℝ := (n : ℝ) ^ (1 - p⁻¹)
  have hβ : IsComplexVectorNorm νβ :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hM_nonneg : 0 ≤ M := complexMatrixColumnMaxVectorNorm_nonneg νβ A
  have hcol :
      MixedSubordinateMatrixBound complexVecOneNorm νβ A M :=
    complexMatrixColumnMaxVectorNorm_mixedSubordinateMatrixBound hβ A
  intro x
  calc
    complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A x)
        ≤ M * complexVecOneNorm x := hcol x
    _ ≤ M * (c * complexVecLpNorm (ENNReal.ofReal p) x) :=
          mul_le_mul_of_nonneg_left
            (complexVecOneNorm_le_card_rpow_mul_complexVecLpNorm hp x) hM_nonneg
    _ = (c * M) * complexVecLpNorm (ENNReal.ofReal p) x := by
          ring

/-- General upper-bound half of Higham equation (6.12), relative to the local
    least-bound matrix-norm API. -/
theorem complexMatrixLpNorm_le_card_rpow_mul_columnMax_lpNorm_of_mixedSubordinateMatrixNormValue
    {m n : ℕ} {p : ℝ} (hp : 1 ≤ p) {A : CMatrix m n} {d : ℝ}
    (hA : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A d) :
    d ≤
      (n : ℝ) ^ (1 - p⁻¹) *
        complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A :=
  hA.2 _ (complexMatrixLpNorm_upper_bound_by_columnMax_lpNorm hp A)

/-- A column power sum is bounded by the `p`th power of the maximum column
    `L^p` norm. -/
theorem complexMatrixColumn_powerSum_le_columnMaxLpNorm_rpow
    {m n : ℕ} {p : ℝ} (hp : 1 ≤ p) (A : CMatrix m n) (j : Fin n) :
    (∑ i : Fin m, ‖A i j‖ ^ p) ≤
      (complexMatrixColumnMaxVectorNorm
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A) ^ p := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let νβ : CVec m → ℝ := complexVecLpNorm (n := m) (ENNReal.ofReal p)
  have hβ : IsComplexVectorNorm νβ :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hcol_nonneg : 0 ≤ νβ (fun i : Fin m => A i j) :=
    hβ.nonneg (fun i : Fin m => A i j)
  have hcol_le :
      νβ (fun i : Fin m => A i j) ≤
        complexMatrixColumnMaxVectorNorm νβ A :=
    complexMatrixColumnMaxVectorNorm_col_le hβ A j
  calc
    (∑ i : Fin m, ‖A i j‖ ^ p)
        = νβ (fun i : Fin m => A i j) ^ p := by
            simpa [νβ] using
              (complexVecLpNorm_rpow_eq_sum_rpow
                (n := m) (p := p) hp_pos (fun i : Fin m => A i j)).symm
    _ ≤ (complexMatrixColumnMaxVectorNorm νβ A) ^ p :=
        Real.rpow_le_rpow hcol_nonneg hcol_le hp_nonneg
    _ =
        (complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A) ^ p := by
            rfl

/-- Sparse-row upper-bound half of Higham Problem 6.14, equation (6.23), as a
    local mixed subordinate bound: if every row has at most `μ` nonzeros, then
    the ambient column-count factor in equation (6.12)'s upper bound improves to
    `μ^(1-1/p)`. -/
theorem complexMatrixLpNorm_upper_bound_by_sparseRows_columnMax_lpNorm
    {m n μ : ℕ} {p : ℝ} (hp : 1 ≤ p) {A : CMatrix m n}
    (hrows : complexMatrixRowsSupportCardLe A μ) :
    MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A
      ((μ : ℝ) ^ (1 - p⁻¹) *
        complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A) := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let νn : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal p)
  let νm : CVec m → ℝ := complexVecLpNorm (n := m) (ENNReal.ofReal p)
  let M : ℝ := complexMatrixColumnMaxVectorNorm νm A
  let c : ℝ := (μ : ℝ) ^ (1 - p⁻¹)
  let C : ℝ := c * M
  have hM_nonneg : 0 ≤ M := complexMatrixColumnMaxVectorNorm_nonneg νm A
  have hc_nonneg : 0 ≤ c :=
    Real.rpow_nonneg (Nat.cast_nonneg μ) (1 - p⁻¹)
  have hC_nonneg : 0 ≤ C := mul_nonneg hc_nonneg hM_nonneg
  intro x
  let SAx : ℝ := ∑ i : Fin m, ‖complexMatrixVecMul A x i‖ ^ p
  let Sx : ℝ := ∑ j : Fin n, ‖x j‖ ^ p
  have hSAx_nonneg : 0 ≤ SAx := by
    dsimp [SAx]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (complexMatrixVecMul A x i)) p)
  have hSx_nonneg : 0 ≤ Sx := by
    dsimp [Sx]
    exact Finset.sum_nonneg (fun j _hj =>
      Real.rpow_nonneg (norm_nonneg (x j)) p)
  have hc_pow_nonneg : 0 ≤ c ^ p := Real.rpow_nonneg hc_nonneg p
  have hrow_power :
      SAx ≤ c ^ p *
        (∑ i : Fin m,
          (complexVecLpNorm (ENNReal.ofReal p)
            (fun j : Fin n => A i j * x j)) ^ p) := by
    dsimp [SAx]
    calc
      (∑ i : Fin m, ‖complexMatrixVecMul A x i‖ ^ p)
          ≤ ∑ i : Fin m,
              c ^ p *
                (complexVecLpNorm (ENNReal.ofReal p)
                  (fun j : Fin n => A i j * x j)) ^ p := by
            apply Finset.sum_le_sum
            intro i _hi
            let rowProd : CVec n := fun j : Fin n => A i j * x j
            have hrow_nonneg :
                0 ≤ complexVecLpNorm (ENNReal.ofReal p) rowProd := by
              unfold complexVecLpNorm
              exact norm_nonneg _
            have hcoord :=
              complexMatrixVecMul_row_norm_le_sparseRow_rpow_mul_lpProduct
                (m := m) (n := n) (μ := μ) (p := p) hp hrows x i
            calc
              ‖complexMatrixVecMul A x i‖ ^ p
                  ≤ (c * complexVecLpNorm (ENNReal.ofReal p) rowProd) ^ p :=
                    Real.rpow_le_rpow (norm_nonneg _) (by simpa [c, rowProd] using hcoord)
                      hp_nonneg
              _ = c ^ p * (complexVecLpNorm (ENNReal.ofReal p) rowProd) ^ p := by
                    rw [Real.mul_rpow hc_nonneg hrow_nonneg]
      _ = c ^ p *
          (∑ i : Fin m,
            (complexVecLpNorm (ENNReal.ofReal p)
              (fun j : Fin n => A i j * x j)) ^ p) := by
            rw [Finset.mul_sum]
  have hrowLp_sum :
      (∑ i : Fin m,
        (complexVecLpNorm (ENNReal.ofReal p)
          (fun j : Fin n => A i j * x j)) ^ p) =
        ∑ i : Fin m, ∑ j : Fin n, ‖A i j * x j‖ ^ p := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact complexVecLpNorm_rpow_eq_sum_rpow
      (n := n) (p := p) hp_pos (fun j : Fin n => A i j * x j)
  have hcolumn_products :
      (∑ j : Fin n, ∑ i : Fin m, ‖A i j * x j‖ ^ p) ≤
        ∑ j : Fin n, M ^ p * ‖x j‖ ^ p := by
    apply Finset.sum_le_sum
    intro j _hj
    have hprod_eq :
        (∑ i : Fin m, ‖A i j * x j‖ ^ p) =
          (∑ i : Fin m, ‖A i j‖ ^ p) * ‖x j‖ ^ p := by
      calc
        (∑ i : Fin m, ‖A i j * x j‖ ^ p)
            = ∑ i : Fin m, (‖A i j‖ * ‖x j‖) ^ p := by
                apply Finset.sum_congr rfl
                intro i _hi
                rw [norm_mul]
        _ = ∑ i : Fin m, ‖A i j‖ ^ p * ‖x j‖ ^ p := by
                apply Finset.sum_congr rfl
                intro i _hi
                rw [Real.mul_rpow (norm_nonneg (A i j)) (norm_nonneg (x j))]
        _ = (∑ i : Fin m, ‖A i j‖ ^ p) * ‖x j‖ ^ p := by
                rw [Finset.sum_mul]
    calc
      (∑ i : Fin m, ‖A i j * x j‖ ^ p)
          = (∑ i : Fin m, ‖A i j‖ ^ p) * ‖x j‖ ^ p := hprod_eq
      _ ≤ M ^ p * ‖x j‖ ^ p :=
          mul_le_mul_of_nonneg_right
            (by
              simpa [M, νm] using
                complexMatrixColumn_powerSum_le_columnMaxLpNorm_rpow
                  (m := m) (n := n) (p := p) hp A j)
            (Real.rpow_nonneg (norm_nonneg (x j)) p)
  have hrowLp_bound :
      (∑ i : Fin m,
        (complexVecLpNorm (ENNReal.ofReal p)
          (fun j : Fin n => A i j * x j)) ^ p) ≤
        M ^ p * Sx := by
    calc
      (∑ i : Fin m,
        (complexVecLpNorm (ENNReal.ofReal p)
          (fun j : Fin n => A i j * x j)) ^ p)
          = ∑ i : Fin m, ∑ j : Fin n, ‖A i j * x j‖ ^ p := hrowLp_sum
      _ = ∑ j : Fin n, ∑ i : Fin m, ‖A i j * x j‖ ^ p := by
            rw [Finset.sum_comm]
      _ ≤ ∑ j : Fin n, M ^ p * ‖x j‖ ^ p := hcolumn_products
      _ = M ^ p * Sx := by
            dsimp [Sx]
            rw [Finset.mul_sum]
  have hSAx_le : SAx ≤ C ^ p * Sx := by
    calc
      SAx ≤ c ^ p *
          (∑ i : Fin m,
            (complexVecLpNorm (ENNReal.ofReal p)
              (fun j : Fin n => A i j * x j)) ^ p) := hrow_power
      _ ≤ c ^ p * (M ^ p * Sx) :=
            mul_le_mul_of_nonneg_left hrowLp_bound hc_pow_nonneg
      _ = C ^ p * Sx := by
            rw [show C ^ p = c ^ p * M ^ p by
              dsimp [C]
              rw [Real.mul_rpow hc_nonneg hM_nonneg]]
            ring
  have hLpAx :
      complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A x) =
        SAx ^ p⁻¹ := by
    simpa [SAx] using
      complexVecLpNorm_ofReal_eq_sum_rpow hp_pos (complexMatrixVecMul A x)
  have hLpx :
      complexVecLpNorm (ENNReal.ofReal p) x = Sx ^ p⁻¹ := by
    simpa [Sx] using complexVecLpNorm_ofReal_eq_sum_rpow hp_pos x
  have hroot :
      SAx ^ p⁻¹ ≤ (C ^ p * Sx) ^ p⁻¹ :=
    Real.rpow_le_rpow hSAx_nonneg hSAx_le (inv_nonneg.mpr hp_nonneg)
  have hfactor : (C ^ p * Sx) ^ p⁻¹ = C * Sx ^ p⁻¹ := by
    calc
      (C ^ p * Sx) ^ p⁻¹ =
          (C ^ p) ^ p⁻¹ * Sx ^ p⁻¹ := by
            rw [Real.mul_rpow (Real.rpow_nonneg hC_nonneg p) hSx_nonneg]
      _ = C * Sx ^ p⁻¹ := by
            rw [Real.rpow_rpow_inv hC_nonneg hp_pos.ne']
  calc
    complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A x)
        = SAx ^ p⁻¹ := hLpAx
    _ ≤ (C ^ p * Sx) ^ p⁻¹ := hroot
    _ = C * Sx ^ p⁻¹ := hfactor
    _ = ((μ : ℝ) ^ (1 - p⁻¹) *
        complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A) *
        complexVecLpNorm (ENNReal.ofReal p) x := by
          rw [hLpx]

/-- Sparse-row upper-bound half of Higham Problem 6.14, equation (6.23),
    relative to the local least-bound matrix-norm API. -/
theorem complexMatrixLpNorm_le_sparseRows_rpow_mul_columnMax_lpNorm_of_mixedSubordinateMatrixNormValue
    {m n μ : ℕ} {p : ℝ} (hp : 1 ≤ p) {A : CMatrix m n} {d : ℝ}
    (hrows : complexMatrixRowsSupportCardLe A μ)
    (hA : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A d) :
    d ≤
      (μ : ℝ) ^ (1 - p⁻¹) *
        complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A :=
  hA.2 _ (complexMatrixLpNorm_upper_bound_by_sparseRows_columnMax_lpNorm hp hrows)

/-- Sparse-column upper-bound half of Higham Problem 6.14, equation (6.24), as a
    local mixed subordinate bound: if every column has at most `μ` nonzeros,
    then the ambient row-count factor in equation (6.13)'s upper bound improves
    to `μ^(1/p)`. -/
theorem complexMatrixLpNorm_upper_bound_by_sparseColumns_rowDualMax_lpNorm
    {m n μ : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    {A : CMatrix m n} (hcols : complexMatrixColumnsSupportCardLe A μ) :
    MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A
      ((μ : ℝ) ^ p⁻¹ *
        complexMatrixRowDualMaxNorm
          (fun i : Fin m =>
            complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j))) := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.lt⟩
  let νn : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal p)
  let νm : CVec m → ℝ := complexVecLpNorm (n := m) (ENNReal.ofReal p)
  let R : ℝ :=
    complexMatrixRowDualMaxNorm
      (fun i : Fin m =>
        complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j))
  let c : ℝ := (μ : ℝ) ^ p⁻¹
  let C : ℝ := c * R
  have hp_nonneg : 0 ≤ p := hpq.nonneg
  have hp_pos : 0 < p := hpq.pos
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact complexMatrixRowDualMaxNorm_nonneg _
  have hc_nonneg : 0 ≤ c :=
    Real.rpow_nonneg (Nat.cast_nonneg μ) p⁻¹
  have hC_nonneg : 0 ≤ C := mul_nonneg hc_nonneg hR_nonneg
  have hc_pow : c ^ p = (μ : ℝ) := by
    dsimp [c]
    exact Real.rpow_inv_rpow (Nat.cast_nonneg μ) hp_pos.ne'
  intro x
  let SAx : ℝ := ∑ i : Fin m, ‖complexMatrixVecMul A x i‖ ^ p
  let Sx : ℝ := ∑ j : Fin n, ‖x j‖ ^ p
  let supportPower : ℝ :=
    ∑ i : Fin m, (complexMatrixRowSupport A i).sum (fun j => ‖x j‖ ^ p)
  have hSAx_nonneg : 0 ≤ SAx := by
    dsimp [SAx]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (complexMatrixVecMul A x i)) p)
  have hSx_nonneg : 0 ≤ Sx := by
    dsimp [Sx]
    exact Finset.sum_nonneg (fun j _hj =>
      Real.rpow_nonneg (norm_nonneg (x j)) p)
  have hR_pow_nonneg : 0 ≤ R ^ p := Real.rpow_nonneg hR_nonneg p
  have hrow_power : SAx ≤ R ^ p * supportPower := by
    dsimp [SAx, supportPower]
    calc
      (∑ i : Fin m, ‖complexMatrixVecMul A x i‖ ^ p)
          ≤ ∑ i : Fin m,
              R ^ p * (complexMatrixRowSupport A i).sum (fun j => ‖x j‖ ^ p) := by
            apply Finset.sum_le_sum
            intro i _hi
            simpa [R] using
              complexMatrixVecMul_row_norm_rpow_le_rowDualMax_lpNorm_rpow_mul_rowSupport_powerSum
                (m := m) (n := n) (p := p) (q := q) hpq A x i
      _ = R ^ p * ∑ i : Fin m,
            (complexMatrixRowSupport A i).sum (fun j => ‖x j‖ ^ p) := by
            rw [Finset.mul_sum]
  have hsupportPower :
      supportPower ≤ (μ : ℝ) * Sx := by
    dsimp [supportPower, Sx]
    exact complexMatrix_rowSupport_sum_le_columnsSupportCard_mul
      (m := m) (n := n) (μ := μ) (A := A) hcols
      (fun j : Fin n => ‖x j‖ ^ p)
      (fun j => Real.rpow_nonneg (norm_nonneg (x j)) p)
  have hSAx_le : SAx ≤ C ^ p * Sx := by
    calc
      SAx ≤ R ^ p * supportPower := hrow_power
      _ ≤ R ^ p * ((μ : ℝ) * Sx) :=
            mul_le_mul_of_nonneg_left hsupportPower hR_pow_nonneg
      _ = C ^ p * Sx := by
            have hC_pow : C ^ p = (μ : ℝ) * R ^ p := by
              calc
                C ^ p = (c * R) ^ p := rfl
                _ = c ^ p * R ^ p := by
                      rw [Real.mul_rpow hc_nonneg hR_nonneg]
                _ = (μ : ℝ) * R ^ p := by
                      rw [hc_pow]
            rw [hC_pow]
            ring
  have hLpAx :
      complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A x) =
        SAx ^ p⁻¹ := by
    simpa [SAx] using
      complexVecLpNorm_ofReal_eq_sum_rpow hp_pos (complexMatrixVecMul A x)
  have hLpx :
      complexVecLpNorm (ENNReal.ofReal p) x = Sx ^ p⁻¹ := by
    simpa [Sx] using complexVecLpNorm_ofReal_eq_sum_rpow hp_pos x
  have hroot :
      SAx ^ p⁻¹ ≤ (C ^ p * Sx) ^ p⁻¹ :=
    Real.rpow_le_rpow hSAx_nonneg hSAx_le (inv_nonneg.mpr hp_nonneg)
  have hfactor : (C ^ p * Sx) ^ p⁻¹ = C * Sx ^ p⁻¹ := by
    calc
      (C ^ p * Sx) ^ p⁻¹ =
          (C ^ p) ^ p⁻¹ * Sx ^ p⁻¹ := by
            rw [Real.mul_rpow (Real.rpow_nonneg hC_nonneg p) hSx_nonneg]
      _ = C * Sx ^ p⁻¹ := by
            rw [Real.rpow_rpow_inv hC_nonneg hp_pos.ne']
  calc
    complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A x)
        = SAx ^ p⁻¹ := hLpAx
    _ ≤ (C ^ p * Sx) ^ p⁻¹ := hroot
    _ = C * Sx ^ p⁻¹ := hfactor
    _ = ((μ : ℝ) ^ p⁻¹ *
          complexMatrixRowDualMaxNorm
            (fun i : Fin m =>
              complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j))) *
        complexVecLpNorm (ENNReal.ofReal p) x := by
          rw [hLpx]

/-- Sparse-column upper-bound half of Higham Problem 6.14, equation (6.24),
    relative to the local least-bound matrix-norm API. -/
theorem complexMatrixLpNorm_le_sparseColumns_rpow_mul_rowDualMax_lpNorm_of_mixedSubordinateMatrixNormValue
    {m n μ : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    {A : CMatrix m n} {d : ℝ}
    (hcols : complexMatrixColumnsSupportCardLe A μ)
    (hA : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A d) :
    d ≤
      (μ : ℝ) ^ p⁻¹ *
        complexMatrixRowDualMaxNorm
          (fun i : Fin m =>
            complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) :=
  hA.2 _ (complexMatrixLpNorm_upper_bound_by_sparseColumns_rowDualMax_lpNorm hpq hcols)

/-- Equation (6.16) dependency: for `1 <= p`, the maximum finite `L^p`
    column norm is bounded by the concrete matrix 1-norm. -/
theorem complexMatrixColumnMaxLpNorm_le_complexMatrixOneNorm
    {m n : ℕ} {p : ℝ} (hp : 1 ≤ p) (A : CMatrix m n) :
    complexMatrixColumnMaxVectorNorm
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A ≤
      complexMatrixOneNorm A := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have hβ : IsComplexVectorNorm
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  apply complexMatrixColumnMaxVectorNorm_le_of_col_le hβ
    (complexMatrixOneNorm_nonneg A)
  intro j
  calc
    complexVecLpNorm (ENNReal.ofReal p) (fun i : Fin m => A i j)
        ≤ complexVecLpNorm (ENNReal.ofReal (1 : ℝ)) (fun i : Fin m => A i j) := by
          simpa using
            (complexVecLpNorm_le_complexVecLpNorm_of_exponent_le
              (n := m) (p := p) (q := 1) (by norm_num) hp
              (fun i : Fin m => A i j))
    _ = complexVecOneNorm (fun i : Fin m => A i j) := by
          simpa using
            (complexVecLpNorm_one_eq_complexVecOneNorm
              (n := m) (fun i : Fin m => A i j))
    _ ≤ complexMatrixOneNorm A :=
          complexMatrixOneNorm_column_oneNorm_le A j

/-- Higham, 2nd ed., Chapter 6, equation (6.16), left inequality in product
    form, relative to the local mixed-subordinate `p -> p` norm value. -/
theorem complexMatrixOneNorm_le_card_rpow_mul_complexMatrixLpNorm_of_mixedSubordinateMatrixNormValue
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix n n} {d : ℝ}
    (hA : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A d) :
    complexMatrixOneNorm A ≤ (n : ℝ) ^ (1 - p⁻¹) * d := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  let c : ℝ := (n : ℝ) ^ (1 - p⁻¹)
  have hc_nonneg : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg n) (1 - p⁻¹)
  have hsrc : IsComplexVectorNorm
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have htgt : IsComplexVectorNorm
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hd_nonneg : 0 ≤ d := by
    obtain ⟨u, hu⟩ := exists_unit_complexVectorNorm hsrc hn
    have h := hA.1 u
    rw [hu, mul_one] at h
    exact (htgt.nonneg (complexMatrixVecMul A u)).trans h
  apply complexMatrixOneNorm_le_of_col_sum_le (mul_nonneg hc_nonneg hd_nonneg)
  intro j
  calc
    complexVecOneNorm (fun i : Fin n => A i j)
        ≤ c * complexVecLpNorm (ENNReal.ofReal p) (fun i : Fin n => A i j) := by
          simpa [c] using
            (complexVecOneNorm_le_card_rpow_mul_complexVecLpNorm
              (n := n) (p := p) hp (fun i : Fin n => A i j))
    _ ≤ c * d :=
          have hcol :
              complexVecLpNorm (ENNReal.ofReal p) (fun i : Fin n => A i j) ≤ d := by
            have h := hA.1 (standardBasisCVec j)
            rw [complexMatrixVecMul_standardBasisCVec A j,
              complexVecLpNorm_standardBasisCVec (ENNReal.ofReal p) j, mul_one] at h
            exact h
          mul_le_mul_of_nonneg_left hcol hc_nonneg

/-- Higham, 2nd ed., Chapter 6, equation (6.16), right inequality, relative
    to the local mixed-subordinate `p -> p` norm value. -/
theorem complexMatrixLpNorm_le_card_rpow_mul_complexMatrixOneNorm_of_mixedSubordinateMatrixNormValue
    {n : ℕ} {p : ℝ} (hp : 1 ≤ p) {A : CMatrix n n} {d : ℝ}
    (hA : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A d) :
    d ≤ (n : ℝ) ^ (1 - p⁻¹) * complexMatrixOneNorm A := by
  let c : ℝ := (n : ℝ) ^ (1 - p⁻¹)
  have hc_nonneg : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg n) (1 - p⁻¹)
  calc
    d ≤ c *
        complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A := by
          simpa [c] using
            (complexMatrixLpNorm_le_card_rpow_mul_columnMax_lpNorm_of_mixedSubordinateMatrixNormValue
              (m := n) (n := n) (p := p) hp hA)
    _ ≤ c * complexMatrixOneNorm A :=
          mul_le_mul_of_nonneg_left
            (complexMatrixColumnMaxLpNorm_le_complexMatrixOneNorm
              (m := n) (n := n) (p := p) hp A)
            hc_nonneg

/-- Higham, 2nd ed., Chapter 6, equation (6.16), source-facing divided left
    inequality, relative to the local mixed-subordinate `p -> p` norm value. -/
theorem complexMatrixOneNorm_div_card_rpow_le_complexMatrixLpNorm_of_mixedSubordinateMatrixNormValue
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix n n} {d : ℝ}
    (hA : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A d) :
    complexMatrixOneNorm A / ((n : ℝ) ^ (1 - p⁻¹)) ≤ d := by
  have hc_pos : 0 < (n : ℝ) ^ (1 - p⁻¹) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) (1 - p⁻¹)
  rw [div_le_iff₀ hc_pos]
  simpa [mul_comm] using
    (complexMatrixOneNorm_le_card_rpow_mul_complexMatrixLpNorm_of_mixedSubordinateMatrixNormValue
      hn hp hA)

/-- Higham, 2nd ed., Chapter 6, equation (6.16), bundled two-sided local
    comparison between the concrete matrix 1-norm and a square `p -> p`
    mixed-subordinate norm value. -/
theorem complexMatrixOneNorm_lpNorm_equiv_bounds_of_mixedSubordinateMatrixNormValue
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix n n} {d : ℝ}
    (hA : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A d) :
    complexMatrixOneNorm A / ((n : ℝ) ^ (1 - p⁻¹)) ≤ d ∧
      d ≤ (n : ℝ) ^ (1 - p⁻¹) * complexMatrixOneNorm A :=
  ⟨complexMatrixOneNorm_div_card_rpow_le_complexMatrixLpNorm_of_mixedSubordinateMatrixNormValue
      hn hp hA,
    complexMatrixLpNorm_le_card_rpow_mul_complexMatrixOneNorm_of_mixedSubordinateMatrixNormValue
      hp hA⟩

/-- Source-facing form of Higham equation (6.16), using the local matrix
    `p`-norm value predicate. -/
theorem complexMatrixLpNormValue_oneNorm_equiv_bounds
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix n n} {d : ℝ}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d) :
    complexMatrixOneNorm A / ((n : ℝ) ^ (1 - p⁻¹)) ≤ d ∧
      d ≤ (n : ℝ) ^ (1 - p⁻¹) * complexMatrixOneNorm A := by
  have hA_mixed :
      IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A d := by
    simpa [IsComplexMatrixLpNormValue] using hA
  exact complexMatrixOneNorm_lpNorm_equiv_bounds_of_mixedSubordinateMatrixNormValue
    (n := n) hn (p := p) hp hA_mixed

/-- A simple finite column-sum upper bound for the matrix `p`-norm.  This is
    mainly an existence ingredient for the concrete source-facing `||A||_p`
    function. -/
noncomputable def complexMatrixLpColumnSumNorm {m n : ℕ}
    (p : ℝ≥0∞) (A : CMatrix m n) : ℝ :=
  ∑ j : Fin n, complexVecLpNorm (n := m) p (fun i : Fin m => A i j)

/-- The column-sum expression is always a valid `p -> p` mixed subordinate
    upper bound for `1 <= p`. -/
theorem complexMatrixLpColumnSumNorm_mixedSubordinateMatrixBound
    {m n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : CMatrix m n) :
    MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A
      (complexMatrixLpColumnSumNorm p A) := by
  let νm : CVec m → ℝ := complexVecLpNorm (n := m) p
  let νn : CVec n → ℝ := complexVecLpNorm (n := n) p
  have hνm : IsComplexVectorNorm νm :=
    complexVecLpNorm_isComplexVectorNorm p
  intro x
  have hAx :
      complexMatrixVecMul A x =
        fun i : Fin m =>
          ∑ j : Fin n, complexVecSMul (x j) (fun k : Fin m => A k j) i := by
    ext i
    unfold complexMatrixVecMul complexVecSMul
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  calc
    complexVecLpNorm p (complexMatrixVecMul A x)
        = νm (fun i : Fin m =>
            ∑ j : Fin n, complexVecSMul (x j) (fun k : Fin m => A k j) i) := by
            rw [hAx]
    _ ≤ ∑ j : Fin n,
          νm (complexVecSMul (x j) (fun k : Fin m => A k j)) :=
        hνm.sum_le (fun j : Fin n => complexVecSMul (x j) (fun k : Fin m => A k j))
    _ = ∑ j : Fin n, ‖x j‖ * νm (fun i : Fin m => A i j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          exact hνm.smul (x j) (fun i : Fin m => A i j)
    _ ≤ ∑ j : Fin n, νn x * νm (fun i : Fin m => A i j) := by
          apply Finset.sum_le_sum
          intro j _hj
          exact mul_le_mul_of_nonneg_right
            (complexVecLpNorm_coord_le (n := n) p x j)
            (hνm.nonneg (fun i : Fin m => A i j))
    _ = νn x *
          (∑ j : Fin n, νm (fun i : Fin m => A i j)) := by
          rw [Finset.mul_sum]
    _ = complexMatrixLpColumnSumNorm p A * complexVecLpNorm p x := by
          dsimp [complexMatrixLpColumnSumNorm, νn, νm]
          ring

/-- General existence theorem for the source-facing local matrix `p`-norm
    predicate in nonempty source dimension. -/
theorem exists_complexMatrixLpNormValue_nonempty
    {m n : ℕ} (hn : 0 < n) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : CMatrix m n) :
    ∃ c : ℝ, IsComplexMatrixLpNormValue p A c := by
  exact exists_mixedSubordinateMatrixNormValue_of_bound_nonempty
    hn (complexVecLpNorm_isComplexVectorNorm (n := n) p)
    (complexVecLpNorm_isComplexVectorNorm (n := m) p) A
    (complexMatrixLpColumnSumNorm_mixedSubordinateMatrixBound p A)

/-- Concrete source-facing matrix `p`-norm value, chosen from the local
    least-bound existence theorem.  This is the first reusable function-level
    bridge for Higham's printed `||A||_p` notation; the theorem below records
    its actual least-bound meaning. -/
noncomputable def complexMatrixLpNorm {m n : ℕ} (hn : 0 < n)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : CMatrix m n) : ℝ :=
  Classical.choose (exists_complexMatrixLpNormValue_nonempty (m := m) hn p A)

/-- The concrete chosen matrix `p`-norm satisfies the local least-bound
    predicate. -/
theorem complexMatrixLpNorm_isComplexMatrixLpNormValue
    {m n : ℕ} (hn : 0 < n) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : CMatrix m n) :
    IsComplexMatrixLpNormValue p A (complexMatrixLpNorm hn p A) :=
  Classical.choose_spec
    (exists_complexMatrixLpNormValue_nonempty (m := m) hn p A)

/-- Any proved local least matrix `p`-norm value identifies the concrete chosen
    source-facing matrix `p`-norm. -/
theorem complexMatrixLpNorm_eq_of_isComplexMatrixLpNormValue
    {m n : ℕ} (hn : 0 < n) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {A : CMatrix m n} {c : ℝ}
    (hA : IsComplexMatrixLpNormValue p A c) :
    complexMatrixLpNorm hn p A = c := by
  exact isComplexMatrixLpNormValue_unique
    (complexMatrixLpNorm_isComplexMatrixLpNormValue
      (m := m) (n := n) hn p A)
    hA

/-- The concrete source-facing matrix `p`-norm is continuous in the matrix
    entries.  The proof identifies the chosen least subordinate bound with the
    operator norm of the matrix as a continuous linear map between the matching
    finite-dimensional `L^p` normed vector spaces. -/
theorem continuous_complexMatrixLpNorm
    {m n : ℕ} (hn : 0 < n) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Continuous (fun A : CMatrix m n => complexMatrixLpNorm hn p A) := by
  let νn : CVec n → ℝ := complexVecLpNorm (n := n) p
  let νm : CVec m → ℝ := complexVecLpNorm (n := m) p
  have hνn : IsComplexVectorNorm νn := by
    simpa [νn] using complexVecLpNorm_isComplexVectorNorm (n := n) p
  have hνm : IsComplexVectorNorm νm := by
    simpa [νm] using complexVecLpNorm_isComplexVectorNorm (n := m) p
  letI : NormedAddCommGroup (NormedCVec n νn) := NormedCVec.normedAddCommGroup hνn
  letI : NormedAddCommGroup (NormedCVec m νm) := NormedCVec.normedAddCommGroup hνm
  letI : Module ℂ (NormedCVec n νn) := (NormedCVec.equiv n νn).module ℂ
  letI : Module ℂ (NormedCVec m νm) := (NormedCVec.equiv m νm).module ℂ
  letI : NormedSpace ℂ (NormedCVec n νn) :=
    NormedSpace.ofCore (𝕜 := ℂ) (NormedCVec.normedSpaceCore hνn)
  letI : NormedSpace ℂ (NormedCVec m νm) :=
    NormedSpace.ofCore (𝕜 := ℂ) (NormedCVec.normedSpaceCore hνm)
  let Lmat : CMatrix m n →ₗ[ℂ] (NormedCVec n νn →L[ℂ] NormedCVec m νm) :=
    { toFun := fun A =>
        let L0 : NormedCVec n νn →ₗ[ℂ] NormedCVec m νm :=
          { toFun := fun x => ⟨complexMatrixVecMul A x.val⟩
            map_add' := by
              intro x y
              apply NormedCVec.ext
              ext i
              change (∑ j : Fin n, A i j * (x.val j + y.val j)) =
                (∑ j : Fin n, A i j * x.val j) +
                  ∑ j : Fin n, A i j * y.val j
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro j _hj
              ring
            map_smul' := by
              intro a x
              apply NormedCVec.ext
              ext i
              change (∑ j : Fin n, A i j * (a * x.val j)) =
                a * ∑ j : Fin n, A i j * x.val j
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j _hj
              ring }
        L0.mkContinuous (complexMatrixLpColumnSumNorm p A) (by
          intro x
          change complexVecLpNorm p (complexMatrixVecMul A x.val) ≤
            complexMatrixLpColumnSumNorm p A * complexVecLpNorm p x.val
          exact complexMatrixLpColumnSumNorm_mixedSubordinateMatrixBound p A x.val)
      map_add' := by
        intro A B
        apply ContinuousLinearMap.ext
        intro x
        apply NormedCVec.ext
        ext i
        change (∑ j : Fin n, (A i j + B i j) * x.val j) =
          (∑ j : Fin n, A i j * x.val j) +
            ∑ j : Fin n, B i j * x.val j
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        ring
      map_smul' := by
        intro a A
        apply ContinuousLinearMap.ext
        intro x
        apply NormedCVec.ext
        ext i
        change (∑ j : Fin n, (a * A i j) * x.val j) =
          a * ∑ j : Fin n, A i j * x.val j
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        ring }
  have hLcont : Continuous fun A : CMatrix m n => Lmat A :=
    LinearMap.continuous_of_finiteDimensional Lmat
  have hOpValue : ∀ A : CMatrix m n, IsComplexMatrixLpNormValue p A ‖Lmat A‖ := by
    intro A
    dsimp [IsComplexMatrixLpNormValue, IsMixedSubordinateMatrixNormValue,
      IsMixedSubordinateNormValue]
    refine ⟨?_, ?_⟩
    · intro x
      have h := (Lmat A).le_opNorm (⟨x⟩ : NormedCVec n νn)
      simpa [Lmat, NormedCVec.norm_eq, νn, νm] using h
    · intro d hd
      have hd_nonneg : 0 ≤ d := by
        exact mixedSubordinateBound_nonneg_of_nonempty hn hνn hνm hd
      apply ContinuousLinearMap.opNorm_le_bound (Lmat A) hd_nonneg
      intro x
      have hdx := hd x.val
      simpa [Lmat, NormedCVec.norm_eq, νn, νm] using hdx
  have hEq : (fun A : CMatrix m n => complexMatrixLpNorm hn p A) =
      fun A : CMatrix m n => ‖Lmat A‖ := by
    funext A
    exact complexMatrixLpNorm_eq_of_isComplexMatrixLpNormValue hn p (hOpValue A)
  rw [hEq]
  exact hLcont.norm

/-- Finite real-exponent wrapper for the concrete matrix `p`-norm value. -/
theorem complexMatrixLpNorm_ofReal_isComplexMatrixLpNormValue
    {m n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    (A : CMatrix m n) :
    IsComplexMatrixLpNormValue (ENNReal.ofReal p) A
      (@complexMatrixLpNorm m n hn (ENNReal.ofReal p)
        ⟨by
          rw [ENNReal.one_le_ofReal]
          exact hp⟩ A) := by
  haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  exact @complexMatrixLpNorm_isComplexMatrixLpNormValue m n hn
    (ENNReal.ofReal p) hpFact A

/-- Finite real-exponent convenience wrapper for the concrete matrix `p`-norm.
    This keeps source-facing theorem statements readable while still using the
    endpoint-aware `ℝ≥0∞` implementation underneath. -/
noncomputable def complexMatrixLpNormOfReal {m n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp : 1 ≤ p) (A : CMatrix m n) : ℝ :=
  @complexMatrixLpNorm m n hn (ENNReal.ofReal p)
    ⟨by
      rw [ENNReal.one_le_ofReal]
      exact hp⟩ A

/-- The finite real-exponent convenience wrapper satisfies the local
    least-bound matrix `p`-norm predicate. -/
theorem complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
    {m n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 1 ≤ p)
    (A : CMatrix m n) :
    IsComplexMatrixLpNormValue (ENNReal.ofReal p) A
      (complexMatrixLpNormOfReal hn p hp A) := by
  simpa [complexMatrixLpNormOfReal] using
    complexMatrixLpNorm_ofReal_isComplexMatrixLpNormValue
      (m := m) (n := n) hn hp A

/-- Finite real-exponent matrix `p`-norms are continuous in the matrix
    entries. -/
theorem continuous_complexMatrixLpNormOfReal
    {m n : ℕ} (hn : 0 < n) (p : ℝ) (hp : 1 ≤ p) :
    Continuous (fun A : CMatrix m n => complexMatrixLpNormOfReal hn p hp A) := by
  haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  simpa [complexMatrixLpNormOfReal] using
    (continuous_complexMatrixLpNorm (m := m) (n := n) hn (ENNReal.ofReal p))

/-- Finite real-exponent version of
    `complexMatrixLpNorm_eq_of_isComplexMatrixLpNormValue`. -/
theorem complexMatrixLpNormOfReal_eq_of_isComplexMatrixLpNormValue
    {m n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix m n} {c : ℝ}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A c) :
    complexMatrixLpNormOfReal hn p hp A = c := by
  exact isComplexMatrixLpNormValue_unique
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := m) (n := n) hn p hp A)
    hA

/-- A local least matrix `p`-norm value is also a nonnegative matrix `p`-norm
    upper bound when the source dimension is nonempty. -/
theorem hasComplexMatrixLpBound_of_complexMatrixLpNormValue_nonempty
    {m n : ℕ} (hn : 0 < n) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {A : CMatrix m n} {c : ℝ}
    (hA : IsComplexMatrixLpNormValue p A c) :
    HasComplexMatrixLpBound p A c := by
  have hνsrc : IsComplexVectorNorm (complexVecLpNorm (n := n) p) :=
    complexVecLpNorm_isComplexVectorNorm p
  have hνtgt : IsComplexVectorNorm (complexVecLpNorm (n := m) p) :=
    complexVecLpNorm_isComplexVectorNorm p
  have hA_mixed :
      IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A c := by
    simpa [IsComplexMatrixLpNormValue] using hA
  exact ⟨mixedSubordinateMatrixNormValue_nonneg_of_nonempty
      hn hνsrc hνtgt hA_mixed, hA_mixed.1⟩

/-- Finite real-exponent wrapper: a local least matrix `p`-norm value gives the
    corresponding nonnegative upper-bound predicate. -/
theorem hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
    {m n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix m n} {c : ℝ}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A c) :
    HasComplexMatrixLpBound (ENNReal.ofReal p) A c := by
  haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  exact hasComplexMatrixLpBound_of_complexMatrixLpNormValue_nonempty hn hA

/-- Finite real-exponent matrix `p`-norms are submultiplicative for compatible
    matrix products. -/
theorem complexMatrixLpNormOfReal_mul_le
    {l m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {p : ℝ} (hp : 1 ≤ p) (A : CMatrix l m) (B : CMatrix m n) :
    complexMatrixLpNormOfReal hn p hp (complexMatrixMul A B) ≤
      complexMatrixLpNormOfReal hm p hp A *
        complexMatrixLpNormOfReal hn p hp B := by
  let q : ℝ≥0∞ := ENNReal.ofReal p
  let a : ℝ := complexMatrixLpNormOfReal hm p hp A
  let b : ℝ := complexMatrixLpNormOfReal hn p hp B
  have hAvalue : IsComplexMatrixLpNormValue q A a := by
    simpa [q, a] using
      complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := l) (n := m) hm p hp A
  have hBvalue : IsComplexMatrixLpNormValue q B b := by
    simpa [q, b] using
      complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn p hp B
  have hProdValue : IsComplexMatrixLpNormValue q (complexMatrixMul A B)
      (complexMatrixLpNormOfReal hn p hp (complexMatrixMul A B)) := by
    simpa [q] using
      complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := l) (n := n) hn p hp (complexMatrixMul A B)
  have hAbound : HasComplexMatrixLpBound q A a := by
    simpa [q, a] using
      hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
        (m := l) (n := m) hm hp hAvalue
  have hBbound : HasComplexMatrixLpBound q B b := by
    simpa [q, b] using
      hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
        (m := m) (n := n) hn hp hBvalue
  have hProdBound : HasComplexMatrixLpBound q (complexMatrixMul A B) (a * b) := by
    refine ⟨mul_nonneg hAbound.1 hBbound.1, ?_⟩
    intro x
    calc
      complexVecLpNorm q (complexMatrixVecMul (complexMatrixMul A B) x)
          = complexVecLpNorm q (complexMatrixVecMul A (complexMatrixVecMul B x)) := by
            rw [complexMatrixVecMul_mul]
      _ ≤ a * complexVecLpNorm q (complexMatrixVecMul B x) :=
            hAbound.2 (complexMatrixVecMul B x)
      _ ≤ a * (b * complexVecLpNorm q x) :=
            mul_le_mul_of_nonneg_left (hBbound.2 x) hAbound.1
      _ = (a * b) * complexVecLpNorm q x := by ring
  simpa [q, a, b] using
    isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hProdValue hProdBound

/-- Concrete chosen matrix-norm endpoint wrapper for `theta = 0`: the
    interpolated `r`-norm is bounded by the left endpoint bound. -/
theorem complexMatrixLpNorm_le_of_interpolation_theta_zero
    {m n : ℕ} (hn : 0 < n) {p₀ p₁ r : ℝ≥0∞} {θ M₀ : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ0 : θ = 0)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀) :
    @complexMatrixLpNorm m n hn r ⟨hr⟩ A ≤ M₀ := by
  letI hrFact : Fact (1 ≤ r) := ⟨hr⟩
  simpa using
    isComplexMatrixLpNormValue_le_of_interpolation_theta_zero
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀)
      (N := complexMatrixLpNorm hn r A) (A := A)
      hp₀ hr hθ hθ0 h₀
      (complexMatrixLpNorm_isComplexMatrixLpNormValue (m := m) (n := n) hn r A)

/-- Concrete chosen matrix-norm endpoint wrapper for `theta = 1`: the
    interpolated `r`-norm is bounded by the right endpoint bound. -/
theorem complexMatrixLpNorm_le_of_interpolation_theta_one
    {m n : ℕ} (hn : 0 < n) {p₀ p₁ r : ℝ≥0∞} {θ M₁ : ℝ}
    {A : CMatrix m n}
    (hp₁ : 1 ≤ p₁) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ1 : θ = 1)
    (h₁ : HasComplexMatrixLpBound p₁ A M₁) :
    @complexMatrixLpNorm m n hn r ⟨hr⟩ A ≤ M₁ := by
  letI hrFact : Fact (1 ≤ r) := ⟨hr⟩
  simpa using
    isComplexMatrixLpNormValue_le_of_interpolation_theta_one
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₁ := M₁)
      (N := complexMatrixLpNorm hn r A) (A := A)
      hp₁ hr hθ hθ1 h₁
      (complexMatrixLpNorm_isComplexMatrixLpNormValue (m := m) (n := n) hn r A)

/-- Concrete chosen matrix-norm geometric endpoint wrapper for `theta = 0`. -/
theorem complexMatrixLpNorm_le_rieszThorin_endpoint_theta_zero
    {m n : ℕ} (hn : 0 < n) {p₀ p₁ r : ℝ≥0∞} {θ M₀ M₁ : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ0 : θ = 0)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀) :
    @complexMatrixLpNorm m n hn r ⟨hr⟩ A ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  letI hrFact : Fact (1 ≤ r) := ⟨hr⟩
  simpa using
    isComplexMatrixLpNormValue_le_rieszThorin_endpoint_theta_zero
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀) (M₁ := M₁)
      (N := complexMatrixLpNorm hn r A) (A := A)
      hp₀ hr hθ hθ0 h₀
      (complexMatrixLpNorm_isComplexMatrixLpNormValue (m := m) (n := n) hn r A)

/-- Concrete chosen matrix-norm geometric endpoint wrapper for `theta = 1`. -/
theorem complexMatrixLpNorm_le_rieszThorin_endpoint_theta_one
    {m n : ℕ} (hn : 0 < n) {p₀ p₁ r : ℝ≥0∞} {θ M₀ M₁ : ℝ}
    {A : CMatrix m n}
    (hp₁ : 1 ≤ p₁) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p₀ p₁ r θ) (hθ1 : θ = 1)
    (h₁ : HasComplexMatrixLpBound p₁ A M₁) :
    @complexMatrixLpNorm m n hn r ⟨hr⟩ A ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  letI hrFact : Fact (1 ≤ r) := ⟨hr⟩
  simpa using
    isComplexMatrixLpNormValue_le_rieszThorin_endpoint_theta_one
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀) (M₁ := M₁)
      (N := complexMatrixLpNorm hn r A) (A := A)
      hp₁ hr hθ hθ1 h₁
      (complexMatrixLpNorm_isComplexMatrixLpNormValue (m := m) (n := n) hn r A)

/-- Concrete chosen matrix-norm strict-interior endpoint wrapper for `r = 1`. -/
theorem complexMatrixLpNorm_le_of_interpolation_strict_eq_one
    {m n : ℕ} (hn : 0 < n) {p₀ p₁ r : ℝ≥0∞} {θ M₀ : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = 1)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀) :
    @complexMatrixLpNorm m n hn r ⟨by rw [hr]⟩ A ≤ M₀ := by
  letI hrFact : Fact (1 ≤ r) := ⟨by rw [hr]⟩
  simpa using
    isComplexMatrixLpNormValue_le_of_interpolation_strict_eq_one
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀)
      (N := complexMatrixLpNorm hn r A) (A := A)
      hp₀ hp₁ hθ hθ0 hθ1 hr h₀
      (complexMatrixLpNorm_isComplexMatrixLpNormValue (m := m) (n := n) hn r A)

/-- Concrete chosen matrix-norm strict-interior endpoint wrapper for `r = ∞`. -/
theorem complexMatrixLpNorm_le_of_interpolation_strict_eq_top
    {m n : ℕ} (hn : 0 < n) {p₀ p₁ r : ℝ≥0∞} {θ M₀ : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = ∞)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀) :
    @complexMatrixLpNorm m n hn r ⟨by rw [hr]; exact le_top⟩ A ≤ M₀ := by
  letI hrFact : Fact (1 ≤ r) := ⟨by rw [hr]; exact le_top⟩
  simpa using
    isComplexMatrixLpNormValue_le_of_interpolation_strict_eq_top
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀)
      (N := complexMatrixLpNorm hn r A) (A := A)
      hp₀ hp₁ hθ hθ0 hθ1 hr h₀
      (complexMatrixLpNorm_isComplexMatrixLpNormValue (m := m) (n := n) hn r A)

/-- Concrete chosen matrix-norm strict endpoint wrapper with the geometric
    Riesz-Thorin right-hand side for `r = 1`. -/
theorem complexMatrixLpNorm_le_rieszThorin_strict_eq_one
    {m n : ℕ} (hn : 0 < n) {p₀ p₁ r : ℝ≥0∞} {θ M₀ M₁ : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = 1)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀)
    (h₁ : HasComplexMatrixLpBound p₁ A M₁) :
    @complexMatrixLpNorm m n hn r ⟨by rw [hr]⟩ A ≤
      M₀ ^ (1 - θ) * M₁ ^ θ := by
  letI hrFact : Fact (1 ≤ r) := ⟨by rw [hr]⟩
  simpa using
    isComplexMatrixLpNormValue_le_rieszThorin_strict_eq_one
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀) (M₁ := M₁)
      (N := complexMatrixLpNorm hn r A) (A := A)
      hp₀ hp₁ hθ hθ0 hθ1 hr h₀ h₁
      (complexMatrixLpNorm_isComplexMatrixLpNormValue (m := m) (n := n) hn r A)

/-- Concrete chosen matrix-norm strict endpoint wrapper with the geometric
    Riesz-Thorin right-hand side for `r = ∞`. -/
theorem complexMatrixLpNorm_le_rieszThorin_strict_eq_top
    {m n : ℕ} (hn : 0 < n) {p₀ p₁ r : ℝ≥0∞} {θ M₀ M₁ : ℝ}
    {A : CMatrix m n}
    (hp₀ : 1 ≤ p₀) (hp₁ : 1 ≤ p₁)
    (hθ : LpInterpolationData p₀ p₁ r θ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hr : r = ∞)
    (h₀ : HasComplexMatrixLpBound p₀ A M₀)
    (h₁ : HasComplexMatrixLpBound p₁ A M₁) :
    @complexMatrixLpNorm m n hn r ⟨by rw [hr]; exact le_top⟩ A ≤
      M₀ ^ (1 - θ) * M₁ ^ θ := by
  letI hrFact : Fact (1 ≤ r) := ⟨by rw [hr]; exact le_top⟩
  simpa using
    isComplexMatrixLpNormValue_le_rieszThorin_strict_eq_top
      (m := m) (n := n) (p₀ := p₀) (p₁ := p₁) (r := r)
      (θ := θ) (M₀ := M₀) (M₁ := M₁)
      (N := complexMatrixLpNorm hn r A) (A := A)
      hp₀ hp₁ hθ hθ0 hθ1 hr h₀ h₁
      (complexMatrixLpNorm_isComplexMatrixLpNormValue (m := m) (n := n) hn r A)

/-- Higham, 2nd ed., Chapter 6, equations (6.18)-(6.20):
    source-facing finite-real Riesz-Thorin comparison at the local
    `IsComplexMatrixLpNormValue` layer, under the analytic affine-exponent
    parameterization used by the three-lines proof. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_finite_dual_normer
    {m n : ℕ} {A : CMatrix m n}
    {p0 q0 p1 q1 scaleX leftX rightX targetX
      scaleY leftY rightY targetY M0 M1 θ N : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowX0 : (scaleX * leftX) * p0 = targetX)
    (hpowY0 : (scaleY * leftY) * q0 = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal targetX) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ := by
  haveI htargetXFact : Fact (1 ≤ ENNReal.ofReal targetX) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt htargetYX.symm.lt⟩
  haveI htargetYFact : Fact (1 ≤ ENNReal.ofReal targetY) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt htargetYX.lt⟩
  exact
    isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
      (hasComplexMatrixLpBound_of_rieszThorin_finite_dual_normer
        (A := A)
        (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1)
        (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
        (targetX := targetX)
        (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
        (targetY := targetY) (M0 := M0) (M1 := M1) (θ := θ)
        hpq0 hpq1 htargetYX
        hpowX0 hpowY0 hpowX1 hpowY1 hX hY
        hscaleX hleftX hrightX hscaleY hleftY hrightY hθ0 hθ1 hA0 hA1)

/-- Source-facing finite-real Riesz-Thorin comparison when the endpoint
    constants are themselves local least matrix `p`-norm values. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_finite_dual_normer_of_endpoint_values
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 q0 p1 q1 scaleX leftX rightX targetX
      scaleY leftY rightY targetY M0 M1 θ N : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowX0 : (scaleX * leftX) * p0 = targetX)
    (hpowY0 : (scaleY * leftY) * q0 = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA0 : IsComplexMatrixLpNormValue (ENNReal.ofReal p0) A M0)
    (hA1 : IsComplexMatrixLpNormValue (ENNReal.ofReal p1) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal targetX) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ := by
  have hB0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
      (m := m) (n := n) (p := p0) (A := A) (c := M0)
      hn (le_of_lt hpq0.lt) hA0
  have hB1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
      (m := m) (n := n) (p := p1) (A := A) (c := M1)
      hn (le_of_lt hpq1.lt) hA1
  exact
    isComplexMatrixLpNormValue_le_rieszThorin_finite_dual_normer
      (A := A)
      (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (targetY := targetY) (M0 := M0) (M1 := M1) (θ := θ) (N := N)
      hpq0 hpq1 htargetYX
      hpowX0 hpowY0 hpowX1 hpowY1 hX hY
      hscaleX hleftX hrightX hscaleY hleftY hrightY hθ0 hθ1 hB0 hB1 hN

/-- Finite-real Riesz-Thorin matrix-bound wrapper with the source exponent
    relation stated through `LpInterpolationData`.  This is the reusable
    predicate-level form behind the concrete equation (6.18) wrapper. -/
theorem hasComplexMatrixLpBound_of_rieszThorin_of_interpolationData
    {m n : ℕ} {A : CMatrix m n}
    {p0 q0 p1 q1 r q θ M0 M1 : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData
      (ENNReal.ofReal p0) (ENNReal.ofReal p1) (ENNReal.ofReal r) θ)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1) :
    HasComplexMatrixLpBound (ENNReal.ofReal r) A
      (M0 ^ (1 - θ) * M1 ^ θ) := by
  haveI htargetXFact : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.lt⟩
  haveI htargetYFact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.symm.lt⟩
  have hθq : LpInterpolationData
      (ENNReal.ofReal q0) (ENNReal.ofReal q1) (ENNReal.ofReal q) θ :=
    LpInterpolationData.conjugate
      (LpConjugateExponents.ofReal_holderConjugate hpq0)
      (LpConjugateExponents.ofReal_holderConjugate hpq1)
      (LpConjugateExponents.ofReal_holderConjugate hrq)
      hθ
  have hX : r * ((1 - θ) * p0⁻¹ + θ * p1⁻¹) = 1 :=
    LpInterpolationData.affineExponent_eq_one_ofReal
      hpq0.pos hpq1.pos hrq.pos hθ
  have hY : q * ((1 - θ) * q0⁻¹ + θ * q1⁻¹) = 1 :=
    LpInterpolationData.affineExponent_eq_one_ofReal
      hpq0.symm.pos hpq1.symm.pos hrq.symm.pos hθq
  have hpowX0 : (r * p0⁻¹) * p0 = r := by
    field_simp [ne_of_gt hpq0.pos]
  have hpowX1 : (r * p1⁻¹) * p1 = r := by
    field_simp [ne_of_gt hpq1.pos]
  have hpowY0 : (q * q0⁻¹) * q0 = q := by
    field_simp [ne_of_gt hpq0.symm.pos]
  have hpowY1 : (q * q1⁻¹) * q1 = q := by
    field_simp [ne_of_gt hpq1.symm.pos]
  exact
    hasComplexMatrixLpBound_of_rieszThorin_finite_dual_normer
      (A := A)
      (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1)
      (scaleX := r) (leftX := p0⁻¹) (rightX := p1⁻¹)
      (targetX := r)
      (scaleY := q) (leftY := q0⁻¹) (rightY := q1⁻¹)
      (targetY := q) (M0 := M0) (M1 := M1) (θ := θ)
      hpq0 hpq1 hrq.symm
      hpowX0 hpowY0 hpowX1 hpowY1 hX hY
      (le_of_lt hrq.pos)
      (inv_nonneg.mpr (le_of_lt hpq0.pos))
      (inv_nonneg.mpr (le_of_lt hpq1.pos))
      (le_of_lt hrq.symm.pos)
      (inv_nonneg.mpr (le_of_lt hpq0.symm.pos))
      (inv_nonneg.mpr (le_of_lt hpq1.symm.pos))
      hθ.theta_nonneg hθ.theta_le_one hA0 hA1

/-- Finite-real Riesz-Thorin comparison at the local least-value layer with
    the exponent relation stated through `LpInterpolationData`. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_of_interpolationData
    {m n : ℕ} {A : CMatrix m n}
    {p0 q0 p1 q1 r q θ M0 M1 N : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData
      (ENNReal.ofReal p0) (ENNReal.ofReal p1) (ENNReal.ofReal r) θ)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal r) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ :=
  isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
    (hasComplexMatrixLpBound_of_rieszThorin_of_interpolationData
      (A := A) (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1)
      (r := r) (q := q) (θ := θ) (M0 := M0) (M1 := M1)
      hpq0 hpq1 hrq hθ hA0 hA1)

/-- Finite-real Riesz-Thorin least-value wrapper when the endpoint constants
    are themselves local matrix `p`-norm values. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_of_interpolationData_endpoint_values
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 q0 p1 q1 r q θ M0 M1 N : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData
      (ENNReal.ofReal p0) (ENNReal.ofReal p1) (ENNReal.ofReal r) θ)
    (hA0 : IsComplexMatrixLpNormValue (ENNReal.ofReal p0) A M0)
    (hA1 : IsComplexMatrixLpNormValue (ENNReal.ofReal p1) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal r) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ := by
  have hB0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
      (m := m) (n := n) (p := p0) (A := A) (c := M0)
      hn (le_of_lt hpq0.lt) hA0
  have hB1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
      (m := m) (n := n) (p := p1) (A := A) (c := M1)
      hn (le_of_lt hpq1.lt) hA1
  exact
    isComplexMatrixLpNormValue_le_rieszThorin_of_interpolationData
      (A := A) (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1)
      (r := r) (q := q) (θ := θ) (M0 := M0) (M1 := M1) (N := N)
      hpq0 hpq1 hrq hθ hB0 hB1 hN

/-- Endpoint `LpInterpolationData` Riesz-Thorin comparison at the local
    least-value layer with left endpoint `p₀ = 1`, `q₀ = ∞`. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_one_top_left_of_interpolationData
    {m n : ℕ} {A : CMatrix m n}
    {p1 q1 r q θ M0 M1 N : ℝ}
    (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData 1 (ENNReal.ofReal p1) (ENNReal.ofReal r) θ)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal r) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ :=
  isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
    (hasComplexMatrixLpBound_of_rieszThorin_one_top_left_of_interpolationData
      (A := A) (p1 := p1) (q1 := q1) (r := r) (q := q)
      (θ := θ) (M0 := M0) (M1 := M1)
      hpq1 hrq hθ hA0 hA1)

/-- Endpoint `LpInterpolationData` Riesz-Thorin comparison at the local
    least-value layer with left endpoint `p₀ = ∞`, `q₀ = 1`. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_top_one_left_of_interpolationData
    {m n : ℕ} {A : CMatrix m n}
    {p1 q1 r q θ M0 M1 N : ℝ}
    (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData ∞ (ENNReal.ofReal p1) (ENNReal.ofReal r) θ)
    (hA0 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal r) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ :=
  isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
    (hasComplexMatrixLpBound_of_rieszThorin_top_one_left_of_interpolationData
      (A := A) (p1 := p1) (q1 := q1) (r := r) (q := q)
      (θ := θ) (M0 := M0) (M1 := M1)
      hpq1 hrq hθ hA0 hA1)

/-- Endpoint `LpInterpolationData` Riesz-Thorin comparison at the local
    least-value layer with right endpoint `p₁ = ∞`, `q₁ = 1`. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_finite_left_top_one_of_interpolationData
    {m n : ℕ} {A : CMatrix m n}
    {p0 q0 r q θ M0 M1 N : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData (ENNReal.ofReal p0) ∞ (ENNReal.ofReal r) θ)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal r) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ :=
  isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
    (hasComplexMatrixLpBound_of_rieszThorin_finite_left_top_one_of_interpolationData
      (A := A) (p0 := p0) (q0 := q0) (r := r) (q := q)
      (θ := θ) (M0 := M0) (M1 := M1)
      hpq0 hrq hθ hA0 hA1)

/-- Endpoint `LpInterpolationData` Riesz-Thorin comparison at the local
    least-value layer with right endpoint `p₁ = 1`, `q₁ = ∞`. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_finite_left_one_top_of_interpolationData
    {m n : ℕ} {A : CMatrix m n}
    {p0 q0 r q θ M0 M1 N : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData (ENNReal.ofReal p0) 1 (ENNReal.ofReal r) θ)
    (hA0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0)
    (hA1 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal r) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ :=
  isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hN
    (hasComplexMatrixLpBound_of_rieszThorin_finite_left_one_top_of_interpolationData
      (A := A) (p0 := p0) (q0 := q0) (r := r) (q := q)
      (θ := θ) (M0 := M0) (M1 := M1)
      hpq0 hrq hθ hA0 hA1)

/-- Endpoint `LpInterpolationData` Riesz-Thorin least-value wrapper when the
    endpoint constants are themselves local matrix norm values, with left
    endpoint `p₀ = 1`, `q₀ = ∞`. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_one_top_left_of_interpolationData_endpoint_values
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p1 q1 r q θ M0 M1 N : ℝ}
    (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData 1 (ENNReal.ofReal p1) (ENNReal.ofReal r) θ)
    (hA0 : IsComplexMatrixLpNormValue (ENNReal.ofReal (1 : ℝ)) A M0)
    (hA1 : IsComplexMatrixLpNormValue (ENNReal.ofReal p1) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal r) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ := by
  have hB0 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M0 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
      (m := m) (n := n) (p := (1 : ℝ)) (A := A) (c := M0)
      hn (le_rfl : (1 : ℝ) ≤ 1) hA0
  have hB1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
      (m := m) (n := n) (p := p1) (A := A) (c := M1)
      hn (le_of_lt hpq1.lt) hA1
  exact
    isComplexMatrixLpNormValue_le_rieszThorin_one_top_left_of_interpolationData
      (A := A) (p1 := p1) (q1 := q1) (r := r) (q := q)
      (θ := θ) (M0 := M0) (M1 := M1) (N := N)
      hpq1 hrq hθ hB0 hB1 hN

/-- Endpoint `LpInterpolationData` Riesz-Thorin least-value wrapper when the
    endpoint constants are themselves local matrix norm values, with left
    endpoint `p₀ = ∞`, `q₀ = 1`. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_top_one_left_of_interpolationData_endpoint_values
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p1 q1 r q θ M0 M1 N : ℝ}
    (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData ∞ (ENNReal.ofReal p1) (ENNReal.ofReal r) θ)
    (hA0 : IsComplexMatrixLpNormValue (∞ : ℝ≥0∞) A M0)
    (hA1 : IsComplexMatrixLpNormValue (ENNReal.ofReal p1) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal r) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ := by
  haveI htopFact : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  have hB0 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M0 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_nonempty
      (m := m) (n := n) hn hA0
  have hB1 : HasComplexMatrixLpBound (ENNReal.ofReal p1) A M1 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
      (m := m) (n := n) (p := p1) (A := A) (c := M1)
      hn (le_of_lt hpq1.lt) hA1
  exact
    isComplexMatrixLpNormValue_le_rieszThorin_top_one_left_of_interpolationData
      (A := A) (p1 := p1) (q1 := q1) (r := r) (q := q)
      (θ := θ) (M0 := M0) (M1 := M1) (N := N)
      hpq1 hrq hθ hB0 hB1 hN

/-- Endpoint `LpInterpolationData` Riesz-Thorin least-value wrapper when the
    endpoint constants are themselves local matrix norm values, with right
    endpoint `p₁ = ∞`, `q₁ = 1`. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_finite_left_top_one_of_interpolationData_endpoint_values
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 q0 r q θ M0 M1 N : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData (ENNReal.ofReal p0) ∞ (ENNReal.ofReal r) θ)
    (hA0 : IsComplexMatrixLpNormValue (ENNReal.ofReal p0) A M0)
    (hA1 : IsComplexMatrixLpNormValue (∞ : ℝ≥0∞) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal r) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ := by
  haveI htopFact : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  have hB0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
      (m := m) (n := n) (p := p0) (A := A) (c := M0)
      hn (le_of_lt hpq0.lt) hA0
  have hB1 : HasComplexMatrixLpBound (∞ : ℝ≥0∞) A M1 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_nonempty
      (m := m) (n := n) hn hA1
  exact
    isComplexMatrixLpNormValue_le_rieszThorin_finite_left_top_one_of_interpolationData
      (A := A) (p0 := p0) (q0 := q0) (r := r) (q := q)
      (θ := θ) (M0 := M0) (M1 := M1) (N := N)
      hpq0 hrq hθ hB0 hB1 hN

/-- Endpoint `LpInterpolationData` Riesz-Thorin least-value wrapper when the
    endpoint constants are themselves local matrix norm values, with right
    endpoint `p₁ = 1`, `q₁ = ∞`. -/
theorem isComplexMatrixLpNormValue_le_rieszThorin_finite_left_one_top_of_interpolationData_endpoint_values
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 q0 r q θ M0 M1 N : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData (ENNReal.ofReal p0) 1 (ENNReal.ofReal r) θ)
    (hA0 : IsComplexMatrixLpNormValue (ENNReal.ofReal p0) A M0)
    (hA1 : IsComplexMatrixLpNormValue (ENNReal.ofReal (1 : ℝ)) A M1)
    (hN : IsComplexMatrixLpNormValue (ENNReal.ofReal r) A N) :
    N ≤ M0 ^ (1 - θ) * M1 ^ θ := by
  have hB0 : HasComplexMatrixLpBound (ENNReal.ofReal p0) A M0 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
      (m := m) (n := n) (p := p0) (A := A) (c := M0)
      hn (le_of_lt hpq0.lt) hA0
  have hB1 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A M1 :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
      (m := m) (n := n) (p := (1 : ℝ)) (A := A) (c := M1)
      hn (le_rfl : (1 : ℝ) ≤ 1) hA1
  exact
    isComplexMatrixLpNormValue_le_rieszThorin_finite_left_one_top_of_interpolationData
      (A := A) (p0 := p0) (q0 := q0) (r := r) (q := q)
      (θ := θ) (M0 := M0) (M1 := M1) (N := N)
      hpq0 hrq hθ hB0 hB1 hN

/-- Concrete endpoint Riesz-Thorin wrapper with left endpoint `p₀ = 1`,
    `q₀ = ∞`, stated through `LpInterpolationData`. -/
theorem complexMatrixLpNormOfReal_le_rieszThorin_one_top_left_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p1 q1 r q θ : ℝ}
    (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData 1 (ENNReal.ofReal p1) (ENNReal.ofReal r) θ) :
    complexMatrixLpNormOfReal hn r (le_of_lt hrq.lt) A ≤
      (complexMatrixLpNormOfReal hn 1 (le_rfl : (1 : ℝ) ≤ 1) A) ^ (1 - θ) *
        (complexMatrixLpNormOfReal hn p1 (le_of_lt hpq1.lt) A) ^ θ := by
  exact
    isComplexMatrixLpNormValue_le_rieszThorin_one_top_left_of_interpolationData_endpoint_values
      (m := m) (n := n) (A := A) hn
      (p1 := p1) (q1 := q1) (r := r) (q := q) (θ := θ)
      (M0 := complexMatrixLpNormOfReal hn 1 (le_rfl : (1 : ℝ) ≤ 1) A)
      (M1 := complexMatrixLpNormOfReal hn p1 (le_of_lt hpq1.lt) A)
      (N := complexMatrixLpNormOfReal hn r (le_of_lt hrq.lt) A)
      hpq1 hrq hθ
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn 1 (le_rfl : (1 : ℝ) ≤ 1) A)
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn p1 (le_of_lt hpq1.lt) A)
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn r (le_of_lt hrq.lt) A)

/-- Concrete endpoint Riesz-Thorin wrapper with left endpoint `p₀ = ∞`,
    `q₀ = 1`, stated through `LpInterpolationData`. -/
theorem complexMatrixLpNormOfReal_le_rieszThorin_top_one_left_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p1 q1 r q θ : ℝ}
    (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData ∞ (ENNReal.ofReal p1) (ENNReal.ofReal r) θ) :
    complexMatrixLpNormOfReal hn r (le_of_lt hrq.lt) A ≤
      (complexMatrixLpNorm hn (∞ : ℝ≥0∞) A) ^ (1 - θ) *
        (complexMatrixLpNormOfReal hn p1 (le_of_lt hpq1.lt) A) ^ θ := by
  haveI htopFact : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  exact
    isComplexMatrixLpNormValue_le_rieszThorin_top_one_left_of_interpolationData_endpoint_values
      (m := m) (n := n) (A := A) hn
      (p1 := p1) (q1 := q1) (r := r) (q := q) (θ := θ)
      (M0 := complexMatrixLpNorm hn (∞ : ℝ≥0∞) A)
      (M1 := complexMatrixLpNormOfReal hn p1 (le_of_lt hpq1.lt) A)
      (N := complexMatrixLpNormOfReal hn r (le_of_lt hrq.lt) A)
      hpq1 hrq hθ
      (complexMatrixLpNorm_isComplexMatrixLpNormValue
        (m := m) (n := n) hn (∞ : ℝ≥0∞) A)
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn p1 (le_of_lt hpq1.lt) A)
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn r (le_of_lt hrq.lt) A)

/-- Concrete endpoint Riesz-Thorin wrapper with right endpoint `p₁ = ∞`,
    `q₁ = 1`, stated through `LpInterpolationData`. -/
theorem complexMatrixLpNormOfReal_le_rieszThorin_finite_left_top_one_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 q0 r q θ : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData (ENNReal.ofReal p0) ∞ (ENNReal.ofReal r) θ) :
    complexMatrixLpNormOfReal hn r (le_of_lt hrq.lt) A ≤
      (complexMatrixLpNormOfReal hn p0 (le_of_lt hpq0.lt) A) ^ (1 - θ) *
        (complexMatrixLpNorm hn (∞ : ℝ≥0∞) A) ^ θ := by
  haveI htopFact : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  exact
    isComplexMatrixLpNormValue_le_rieszThorin_finite_left_top_one_of_interpolationData_endpoint_values
      (m := m) (n := n) (A := A) hn
      (p0 := p0) (q0 := q0) (r := r) (q := q) (θ := θ)
      (M0 := complexMatrixLpNormOfReal hn p0 (le_of_lt hpq0.lt) A)
      (M1 := complexMatrixLpNorm hn (∞ : ℝ≥0∞) A)
      (N := complexMatrixLpNormOfReal hn r (le_of_lt hrq.lt) A)
      hpq0 hrq hθ
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn p0 (le_of_lt hpq0.lt) A)
      (complexMatrixLpNorm_isComplexMatrixLpNormValue
        (m := m) (n := n) hn (∞ : ℝ≥0∞) A)
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn r (le_of_lt hrq.lt) A)

/-- Concrete endpoint Riesz-Thorin wrapper with right endpoint `p₁ = 1`,
    `q₁ = ∞`, stated through `LpInterpolationData`. -/
theorem complexMatrixLpNormOfReal_le_rieszThorin_finite_left_one_top_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 q0 r q θ : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData (ENNReal.ofReal p0) 1 (ENNReal.ofReal r) θ) :
    complexMatrixLpNormOfReal hn r (le_of_lt hrq.lt) A ≤
      (complexMatrixLpNormOfReal hn p0 (le_of_lt hpq0.lt) A) ^ (1 - θ) *
        (complexMatrixLpNormOfReal hn 1 (le_rfl : (1 : ℝ) ≤ 1) A) ^ θ := by
  exact
    isComplexMatrixLpNormValue_le_rieszThorin_finite_left_one_top_of_interpolationData_endpoint_values
      (m := m) (n := n) (A := A) hn
      (p0 := p0) (q0 := q0) (r := r) (q := q) (θ := θ)
      (M0 := complexMatrixLpNormOfReal hn p0 (le_of_lt hpq0.lt) A)
      (M1 := complexMatrixLpNormOfReal hn 1 (le_rfl : (1 : ℝ) ≤ 1) A)
      (N := complexMatrixLpNormOfReal hn r (le_of_lt hrq.lt) A)
      hpq0 hrq hθ
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn p0 (le_of_lt hpq0.lt) A)
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn 1 (le_rfl : (1 : ℝ) ≤ 1) A)
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn r (le_of_lt hrq.lt) A)

/-- Endpoint-aware concrete Riesz-Thorin wrapper with left endpoint `p₀ = 1`,
    `q₀ = ∞`, stated directly with `complexMatrixLpNorm`. -/
theorem complexMatrixLpNorm_le_rieszThorin_one_top_left_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p1 q1 r q θ : ℝ}
    (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData 1 (ENNReal.ofReal p1) (ENNReal.ofReal r) θ) :
    @complexMatrixLpNorm m n hn (ENNReal.ofReal r)
        ⟨by rw [ENNReal.one_le_ofReal]; exact le_of_lt hrq.lt⟩ A ≤
      (@complexMatrixLpNorm m n hn (ENNReal.ofReal (1 : ℝ))
          ⟨by rw [ENNReal.one_le_ofReal]⟩ A) ^ (1 - θ) *
        (@complexMatrixLpNorm m n hn (ENNReal.ofReal p1)
          ⟨by rw [ENNReal.one_le_ofReal]; exact le_of_lt hpq1.lt⟩ A) ^ θ := by
  haveI h1Fact : Fact (1 ≤ ENNReal.ofReal (1 : ℝ)) := ⟨by
    rw [ENNReal.one_le_ofReal]⟩
  haveI hp1Fact : Fact (1 ≤ ENNReal.ofReal p1) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq1.lt⟩
  haveI hrFact : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.lt⟩
  simpa [complexMatrixLpNormOfReal] using
    (complexMatrixLpNormOfReal_le_rieszThorin_one_top_left_of_interpolationData
      (m := m) (n := n) (A := A) hn hpq1 hrq hθ)

/-- Endpoint-aware concrete Riesz-Thorin wrapper with left endpoint `p₀ = ∞`,
    `q₀ = 1`, stated directly with `complexMatrixLpNorm`. -/
theorem complexMatrixLpNorm_le_rieszThorin_top_one_left_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p1 q1 r q θ : ℝ}
    (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData ∞ (ENNReal.ofReal p1) (ENNReal.ofReal r) θ) :
    @complexMatrixLpNorm m n hn (ENNReal.ofReal r)
        ⟨by rw [ENNReal.one_le_ofReal]; exact le_of_lt hrq.lt⟩ A ≤
      (@complexMatrixLpNorm m n hn (∞ : ℝ≥0∞) ⟨by simp⟩ A) ^ (1 - θ) *
        (@complexMatrixLpNorm m n hn (ENNReal.ofReal p1)
          ⟨by rw [ENNReal.one_le_ofReal]; exact le_of_lt hpq1.lt⟩ A) ^ θ := by
  haveI htopFact : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  haveI hp1Fact : Fact (1 ≤ ENNReal.ofReal p1) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq1.lt⟩
  haveI hrFact : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.lt⟩
  simpa [complexMatrixLpNormOfReal] using
    (complexMatrixLpNormOfReal_le_rieszThorin_top_one_left_of_interpolationData
      (m := m) (n := n) (A := A) hn hpq1 hrq hθ)

/-- Endpoint-aware concrete Riesz-Thorin wrapper with right endpoint `p₁ = ∞`,
    `q₁ = 1`, stated directly with `complexMatrixLpNorm`. -/
theorem complexMatrixLpNorm_le_rieszThorin_finite_left_top_one_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 q0 r q θ : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData (ENNReal.ofReal p0) ∞ (ENNReal.ofReal r) θ) :
    @complexMatrixLpNorm m n hn (ENNReal.ofReal r)
        ⟨by rw [ENNReal.one_le_ofReal]; exact le_of_lt hrq.lt⟩ A ≤
      (@complexMatrixLpNorm m n hn (ENNReal.ofReal p0)
          ⟨by rw [ENNReal.one_le_ofReal]; exact le_of_lt hpq0.lt⟩ A) ^ (1 - θ) *
        (@complexMatrixLpNorm m n hn (∞ : ℝ≥0∞) ⟨by simp⟩ A) ^ θ := by
  haveI hp0Fact : Fact (1 ≤ ENNReal.ofReal p0) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq0.lt⟩
  haveI htopFact : Fact (1 ≤ (∞ : ℝ≥0∞)) := ⟨by simp⟩
  haveI hrFact : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.lt⟩
  simpa [complexMatrixLpNormOfReal] using
    (complexMatrixLpNormOfReal_le_rieszThorin_finite_left_top_one_of_interpolationData
      (m := m) (n := n) (A := A) hn hpq0 hrq hθ)

/-- Endpoint-aware concrete Riesz-Thorin wrapper with right endpoint `p₁ = 1`,
    `q₁ = ∞`, stated directly with `complexMatrixLpNorm`. -/
theorem complexMatrixLpNorm_le_rieszThorin_finite_left_one_top_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 q0 r q θ : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData (ENNReal.ofReal p0) 1 (ENNReal.ofReal r) θ) :
    @complexMatrixLpNorm m n hn (ENNReal.ofReal r)
        ⟨by rw [ENNReal.one_le_ofReal]; exact le_of_lt hrq.lt⟩ A ≤
      (@complexMatrixLpNorm m n hn (ENNReal.ofReal p0)
          ⟨by rw [ENNReal.one_le_ofReal]; exact le_of_lt hpq0.lt⟩ A) ^ (1 - θ) *
        (@complexMatrixLpNorm m n hn (ENNReal.ofReal (1 : ℝ))
          ⟨by rw [ENNReal.one_le_ofReal]⟩ A) ^ θ := by
  haveI hp0Fact : Fact (1 ≤ ENNReal.ofReal p0) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq0.lt⟩
  haveI h1Fact : Fact (1 ≤ ENNReal.ofReal (1 : ℝ)) := ⟨by
    rw [ENNReal.one_le_ofReal]⟩
  haveI hrFact : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.lt⟩
  simpa [complexMatrixLpNormOfReal] using
    (complexMatrixLpNormOfReal_le_rieszThorin_finite_left_one_top_of_interpolationData
      (m := m) (n := n) (A := A) hn hpq0 hrq hθ)

/-- Concrete finite-real function wrapper for the local Riesz-Thorin
    comparison: the constructed matrix `targetX`-norm is bounded by the
    geometric interpolation of the constructed endpoint matrix norms. -/
theorem complexMatrixLpNormOfReal_le_rieszThorin_finite_dual_normer
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 q0 p1 q1 scaleX leftX rightX targetX
      scaleY leftY rightY targetY θ : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (htargetYX : targetY.HolderConjugate targetX)
    (hpowX0 : (scaleX * leftX) * p0 = targetX)
    (hpowY0 : (scaleY * leftY) * q0 = targetY)
    (hpowX1 : (scaleX * rightX) * p1 = targetX)
    (hpowY1 : (scaleY * rightY) * q1 = targetY)
    (hX : scaleX * ((1 - θ) * leftX + θ * rightX) = 1)
    (hY : scaleY * ((1 - θ) * leftY + θ * rightY) = 1)
    (hscaleX : 0 ≤ scaleX) (hleftX : 0 ≤ leftX) (hrightX : 0 ≤ rightX)
    (hscaleY : 0 ≤ scaleY) (hleftY : 0 ≤ leftY) (hrightY : 0 ≤ rightY)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    complexMatrixLpNormOfReal hn targetX (le_of_lt htargetYX.symm.lt) A ≤
      (complexMatrixLpNormOfReal hn p0 (le_of_lt hpq0.lt) A) ^ (1 - θ) *
        (complexMatrixLpNormOfReal hn p1 (le_of_lt hpq1.lt) A) ^ θ := by
  exact
    isComplexMatrixLpNormValue_le_rieszThorin_finite_dual_normer_of_endpoint_values
      (m := m) (n := n) (A := A)
      (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1)
      (scaleX := scaleX) (leftX := leftX) (rightX := rightX)
      (targetX := targetX)
      (scaleY := scaleY) (leftY := leftY) (rightY := rightY)
      (targetY := targetY)
      (M0 := complexMatrixLpNormOfReal hn p0 (le_of_lt hpq0.lt) A)
      (M1 := complexMatrixLpNormOfReal hn p1 (le_of_lt hpq1.lt) A)
      (θ := θ)
      (N := complexMatrixLpNormOfReal hn targetX (le_of_lt htargetYX.symm.lt) A)
      hn hpq0 hpq1 htargetYX
      hpowX0 hpowY0 hpowX1 hpowY1 hX hY
      hscaleX hleftX hrightX hscaleY hleftY hrightY hθ0 hθ1
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn p0 (le_of_lt hpq0.lt) A)
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn p1 (le_of_lt hpq1.lt) A)
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn targetX (le_of_lt htargetYX.symm.lt) A)

/-- Higham, 2nd ed., Chapter 6, equation (6.18):
    finite-real Riesz-Thorin interpolation for the concrete local matrix
    p-norm, with the exponent relation stated through `LpInterpolationData`.
    This packages the strict finite source theorem while endpoint/infinity
    source specializations remain separate. -/
theorem complexMatrixLpNormOfReal_le_rieszThorin_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 q0 p1 q1 r q θ : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData
      (ENNReal.ofReal p0) (ENNReal.ofReal p1) (ENNReal.ofReal r) θ) :
    complexMatrixLpNormOfReal hn r (le_of_lt hrq.lt) A ≤
      (complexMatrixLpNormOfReal hn p0 (le_of_lt hpq0.lt) A) ^ (1 - θ) *
        (complexMatrixLpNormOfReal hn p1 (le_of_lt hpq1.lt) A) ^ θ := by
  have hθq : LpInterpolationData
      (ENNReal.ofReal q0) (ENNReal.ofReal q1) (ENNReal.ofReal q) θ :=
    LpInterpolationData.conjugate
      (LpConjugateExponents.ofReal_holderConjugate hpq0)
      (LpConjugateExponents.ofReal_holderConjugate hpq1)
      (LpConjugateExponents.ofReal_holderConjugate hrq)
      hθ
  have hX : r * ((1 - θ) * p0⁻¹ + θ * p1⁻¹) = 1 :=
    LpInterpolationData.affineExponent_eq_one_ofReal
      hpq0.pos hpq1.pos hrq.pos hθ
  have hY : q * ((1 - θ) * q0⁻¹ + θ * q1⁻¹) = 1 :=
    LpInterpolationData.affineExponent_eq_one_ofReal
      hpq0.symm.pos hpq1.symm.pos hrq.symm.pos hθq
  have hpowX0 : (r * p0⁻¹) * p0 = r := by
    field_simp [ne_of_gt hpq0.pos]
  have hpowX1 : (r * p1⁻¹) * p1 = r := by
    field_simp [ne_of_gt hpq1.pos]
  have hpowY0 : (q * q0⁻¹) * q0 = q := by
    field_simp [ne_of_gt hpq0.symm.pos]
  have hpowY1 : (q * q1⁻¹) * q1 = q := by
    field_simp [ne_of_gt hpq1.symm.pos]
  exact
    complexMatrixLpNormOfReal_le_rieszThorin_finite_dual_normer
      (m := m) (n := n) (A := A) (hn := hn)
      (p0 := p0) (q0 := q0) (p1 := p1) (q1 := q1)
      (scaleX := r) (leftX := p0⁻¹) (rightX := p1⁻¹)
      (targetX := r)
      (scaleY := q) (leftY := q0⁻¹) (rightY := q1⁻¹)
      (targetY := q) (θ := θ)
      hpq0 hpq1 hrq.symm
      hpowX0 hpowY0 hpowX1 hpowY1 hX hY
      (le_of_lt hrq.pos)
      (inv_nonneg.mpr (le_of_lt hpq0.pos))
      (inv_nonneg.mpr (le_of_lt hpq1.pos))
      (le_of_lt hrq.symm.pos)
      (inv_nonneg.mpr (le_of_lt hpq0.symm.pos))
      (inv_nonneg.mpr (le_of_lt hpq1.symm.pos))
      hθ.theta_nonneg hθ.theta_le_one

/-- Endpoint-aware concrete finite-real Riesz-Thorin wrapper stated directly
    with `complexMatrixLpNorm`. -/
theorem complexMatrixLpNorm_le_rieszThorin_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 q0 p1 q1 r q θ : ℝ}
    (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
    (hrq : r.HolderConjugate q)
    (hθ : LpInterpolationData
      (ENNReal.ofReal p0) (ENNReal.ofReal p1) (ENNReal.ofReal r) θ) :
    @complexMatrixLpNorm m n hn (ENNReal.ofReal r)
        ⟨by rw [ENNReal.one_le_ofReal]; exact le_of_lt hrq.lt⟩ A ≤
      (@complexMatrixLpNorm m n hn (ENNReal.ofReal p0)
          ⟨by rw [ENNReal.one_le_ofReal]; exact le_of_lt hpq0.lt⟩ A) ^ (1 - θ) *
        (@complexMatrixLpNorm m n hn (ENNReal.ofReal p1)
          ⟨by rw [ENNReal.one_le_ofReal]; exact le_of_lt hpq1.lt⟩ A) ^ θ := by
  haveI hp0Fact : Fact (1 ≤ ENNReal.ofReal p0) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq0.lt⟩
  haveI hp1Fact : Fact (1 ≤ ENNReal.ofReal p1) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq1.lt⟩
  haveI hrFact : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hrq.lt⟩
  simpa [complexMatrixLpNormOfReal] using
    (complexMatrixLpNormOfReal_le_rieszThorin_of_interpolationData
      (m := m) (n := n) (A := A) hn hpq0 hpq1 hrq hθ)

/-- Higham, 2nd ed., Chapter 6, equation (6.19), mixed-bound form:
    the finite matrix `p`-norm is bounded by the logarithmic interpolation
    between the concrete column-sum `1`-norm and row-sum infinity norm.  This
    Schur-test proof is the endpoint specialization not covered by the strict
    finite-endpoint Riesz-Thorin wrapper above. -/
theorem complexMatrixLpNorm_one_inf_interpolation_mixedSubordinateMatrixBound
    {m n : ℕ} {p : ℝ} (hp : 1 ≤ p) (A : CMatrix m n) :
    MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A
      (complexMatrixOneNorm A ^ p⁻¹ *
        complexMatrixInfNorm A ^ (1 - p⁻¹)) := by
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hexp_nonneg : 0 ≤ p - 1 := sub_nonneg.mpr hp
  let C : ℝ := complexMatrixOneNorm A
  let R : ℝ := complexMatrixInfNorm A
  let K : ℝ := C ^ p⁻¹ * R ^ (1 - p⁻¹)
  have hC_nonneg : 0 ≤ C := by simpa [C] using complexMatrixOneNorm_nonneg A
  have hR_nonneg : 0 ≤ R := by simpa [R] using complexMatrixInfNorm_nonneg A
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (Real.rpow_nonneg hC_nonneg p⁻¹)
      (Real.rpow_nonneg hR_nonneg (1 - p⁻¹))
  have hKpow : K ^ p = C * R ^ (p - 1) := by
    dsimp [K]
    calc
      (C ^ p⁻¹ * R ^ (1 - p⁻¹)) ^ p =
          (C ^ p⁻¹) ^ p * (R ^ (1 - p⁻¹)) ^ p := by
            rw [Real.mul_rpow
              (Real.rpow_nonneg hC_nonneg p⁻¹)
              (Real.rpow_nonneg hR_nonneg (1 - p⁻¹))]
      _ = C * R ^ ((1 - p⁻¹) * p) := by
            rw [← Real.rpow_mul hC_nonneg p⁻¹ p]
            rw [← Real.rpow_mul hR_nonneg (1 - p⁻¹) p]
            have hinv_mul : p⁻¹ * p = 1 := by
              field_simp [hp_pos.ne']
            rw [hinv_mul, Real.rpow_one]
      _ = C * R ^ (p - 1) := by
            have hmul : (1 - p⁻¹) * p = p - 1 := by
              field_simp [hp_pos.ne']
            rw [hmul]
  intro x
  let SAx : ℝ := ∑ i : Fin m, ‖complexMatrixVecMul A x i‖ ^ p
  let Sx : ℝ := ∑ j : Fin n, ‖x j‖ ^ p
  have hSAx_nonneg : 0 ≤ SAx := by
    dsimp [SAx]
    exact Finset.sum_nonneg (fun i _hi =>
      Real.rpow_nonneg (norm_nonneg (complexMatrixVecMul A x i)) p)
  have hSx_nonneg : 0 ≤ Sx := by
    dsimp [Sx]
    exact Finset.sum_nonneg (fun j _hj =>
      Real.rpow_nonneg (norm_nonneg (x j)) p)
  have hrow_power : ∀ i : Fin m,
      ‖complexMatrixVecMul A x i‖ ^ p ≤
        R ^ (p - 1) * (∑ j : Fin n, ‖A i j‖ * ‖x j‖ ^ p) := by
    intro i
    let rowSum : ℝ := ∑ j : Fin n, ‖A i j‖
    let rowPow : ℝ := ∑ j : Fin n, ‖A i j‖ * ‖x j‖ ^ p
    let rowLin : ℝ := ∑ j : Fin n, ‖A i j‖ * ‖x j‖
    have hrowSum_nonneg : 0 ≤ rowSum := by
      dsimp [rowSum]
      exact Finset.sum_nonneg (fun j _hj => norm_nonneg (A i j))
    have hrowPow_nonneg : 0 ≤ rowPow := by
      dsimp [rowPow]
      exact Finset.sum_nonneg (fun j _hj =>
        mul_nonneg (norm_nonneg (A i j))
          (Real.rpow_nonneg (norm_nonneg (x j)) p))
    have htri : ‖complexMatrixVecMul A x i‖ ≤ rowLin := by
      calc
        ‖complexMatrixVecMul A x i‖
            = ‖∑ j : Fin n, A i j * x j‖ := rfl
        _ ≤ ∑ j : Fin n, ‖A i j * x j‖ := norm_sum_le _ _
        _ = rowLin := by
              dsimp [rowLin]
              apply Finset.sum_congr rfl
              intro j _hj
              exact norm_mul (A i j) (x j)
    have hschur :
        rowLin ^ p ≤ rowSum ^ (p - 1) * rowPow := by
      simpa [rowLin, rowSum, rowPow] using
        weighted_sum_mul_rpow_le_sum_weight_rpow_mul_sum_weight_mul_rpow
          (s := Finset.univ) (p := p) hp
          (w := fun j : Fin n => ‖A i j‖)
          (f := fun j : Fin n => ‖x j‖)
          (fun j => norm_nonneg (A i j))
          (fun j => norm_nonneg (x j))
    have hrowSum_le_R : rowSum ≤ R := by
      simpa [rowSum, R] using complexMatrixInfNorm_row_sum_le A i
    have hrowFactor_le :
        rowSum ^ (p - 1) ≤ R ^ (p - 1) :=
      Real.rpow_le_rpow hrowSum_nonneg hrowSum_le_R hexp_nonneg
    calc
      ‖complexMatrixVecMul A x i‖ ^ p ≤ rowLin ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) htri hp_nonneg
      _ ≤ rowSum ^ (p - 1) * rowPow := hschur
      _ ≤ R ^ (p - 1) * rowPow :=
        mul_le_mul_of_nonneg_right hrowFactor_le hrowPow_nonneg
      _ = R ^ (p - 1) * (∑ j : Fin n, ‖A i j‖ * ‖x j‖ ^ p) := by
        rfl
  have hSAx_le_core :
      SAx ≤ (C * R ^ (p - 1)) * Sx := by
    calc
      SAx ≤ ∑ i : Fin m,
          R ^ (p - 1) * (∑ j : Fin n, ‖A i j‖ * ‖x j‖ ^ p) := by
            dsimp [SAx]
            exact Finset.sum_le_sum (fun i _hi => hrow_power i)
      _ = R ^ (p - 1) *
          (∑ i : Fin m, ∑ j : Fin n, ‖A i j‖ * ‖x j‖ ^ p) := by
            rw [Finset.mul_sum]
      _ = R ^ (p - 1) *
          (∑ j : Fin n, ∑ i : Fin m, ‖A i j‖ * ‖x j‖ ^ p) := by
            rw [Finset.sum_comm]
      _ ≤ R ^ (p - 1) *
          (∑ j : Fin n, C * ‖x j‖ ^ p) := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum
              intro j _hj
              calc
                (∑ i : Fin m, ‖A i j‖ * ‖x j‖ ^ p)
                    = (∑ i : Fin m, ‖A i j‖) * ‖x j‖ ^ p := by
                        rw [Finset.sum_mul]
                _ ≤ C * ‖x j‖ ^ p :=
                    mul_le_mul_of_nonneg_right
                      (by simpa [C] using complexMatrixOneNorm_col_sum_le A j)
                      (Real.rpow_nonneg (norm_nonneg (x j)) p)
            · exact Real.rpow_nonneg hR_nonneg (p - 1)
      _ = (C * R ^ (p - 1)) * Sx := by
            dsimp [Sx]
            rw [← Finset.mul_sum]
            ring
  have hSAx_le : SAx ≤ K ^ p * Sx := by
    rw [hKpow]
    exact hSAx_le_core
  have hLpAx :
      complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A x) =
        SAx ^ p⁻¹ := by
    simpa [SAx] using
      complexVecLpNorm_ofReal_eq_sum_rpow hp_pos (complexMatrixVecMul A x)
  have hLpx :
      complexVecLpNorm (ENNReal.ofReal p) x = Sx ^ p⁻¹ := by
    simpa [Sx] using complexVecLpNorm_ofReal_eq_sum_rpow hp_pos x
  have hroot :
      SAx ^ p⁻¹ ≤ (K ^ p * Sx) ^ p⁻¹ :=
    Real.rpow_le_rpow hSAx_nonneg hSAx_le (inv_nonneg.mpr hp_nonneg)
  have hfactor : (K ^ p * Sx) ^ p⁻¹ = K * Sx ^ p⁻¹ := by
    calc
      (K ^ p * Sx) ^ p⁻¹ =
          (K ^ p) ^ p⁻¹ * Sx ^ p⁻¹ := by
            rw [Real.mul_rpow (Real.rpow_nonneg hK_nonneg p) hSx_nonneg]
      _ = K * Sx ^ p⁻¹ := by
            rw [Real.rpow_rpow_inv hK_nonneg hp_pos.ne']
  calc
    complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A x)
        = SAx ^ p⁻¹ := hLpAx
    _ ≤ (K ^ p * Sx) ^ p⁻¹ := hroot
    _ = K * Sx ^ p⁻¹ := hfactor
    _ = (complexMatrixOneNorm A ^ p⁻¹ *
        complexMatrixInfNorm A ^ (1 - p⁻¹)) *
        complexVecLpNorm (ENNReal.ofReal p) x := by
          rw [hLpx]

/-- Has-bound wrapper for Higham equation (6.19)'s Schur/Riesz-Thorin
    endpoint specialization. -/
theorem complexMatrixLpNorm_one_inf_interpolation_hasComplexMatrixLpBound
    {m n : ℕ} {p : ℝ} (hp : 1 ≤ p) (A : CMatrix m n) :
    HasComplexMatrixLpBound (ENNReal.ofReal p) A
      (complexMatrixOneNorm A ^ p⁻¹ *
        complexMatrixInfNorm A ^ (1 - p⁻¹)) := by
  refine ⟨?_, complexMatrixLpNorm_one_inf_interpolation_mixedSubordinateMatrixBound
    (m := m) (n := n) (p := p) hp A⟩
  exact mul_nonneg
    (Real.rpow_nonneg (complexMatrixOneNorm_nonneg A) p⁻¹)
    (Real.rpow_nonneg (complexMatrixInfNorm_nonneg A) (1 - p⁻¹))

/-- Higham, 2nd ed., Chapter 6, equation (6.19), concrete finite-real wrapper:
    `||A||_p <= ||A||_1^(1/p) ||A||_∞^(1-1/p)`. -/
theorem complexMatrixLpNormOfReal_rieszThorin_one_top
    {m n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p) (A : CMatrix m n) :
    complexMatrixLpNormOfReal hn p hp A ≤
      complexMatrixOneNorm A ^ p⁻¹ *
        complexMatrixInfNorm A ^ (1 - p⁻¹) := by
  exact
    isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn p hp A)
      (complexMatrixLpNorm_one_inf_interpolation_hasComplexMatrixLpBound
        (m := m) (n := n) (p := p) hp A)
end NumStability
