/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.QR.Higham19Sensitivity
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Norms
import NumStability.Analysis.HighamChapter7
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

namespace NumStability

open scoped BigOperators

/-!
# Higham Problem 19.9: two-column angle and condition number

The chapter uses this problem to turn the angle between two columns into a
lower bound for the spectral condition number.  The proof below uses the
literal two-column matrix, its actual least singular value, and the projection
residual from the Appendix-A proof.
-/

/-- Matrix having `a₁` and `a₂` as its two columns. -/
def higham19Problem19_9Matrix {m : ℕ}
    (a₁ a₂ : Fin m → ℝ) : Fin m → Fin 2 → ℝ :=
  fun i j => if j = 0 then a₁ i else a₂ i

/-- Actual smallest singular value of a real matrix with two columns. -/
noncomputable def higham19Problem19_9SigmaMin {m : ℕ}
    (A : Fin m → Fin 2 → ℝ) : ℝ :=
  complexMatrixSingularValue (realRectToCMatrix A) (Fin.last 1)

/-- Spectral condition number in maximum-gain/minimum-gain form. -/
noncomputable def higham19Problem19_9Kappa2 {m : ℕ}
    (A : Fin m → Fin 2 → ℝ) : ℝ :=
  rectOpNorm2 A / higham19Problem19_9SigmaMin A

theorem higham19_problem19_9_sigmaMin_nonneg {m : ℕ}
    (A : Fin m → Fin 2 → ℝ) :
    0 ≤ higham19Problem19_9SigmaMin A := by
  exact complexMatrixSingularValue_nonneg (realRectToCMatrix A) (Fin.last 1)

/-- Full column rank makes the actual least singular value strictly
positive; this discharges the only denominator condition in the source
condition number. -/
theorem higham19_problem19_9_sigmaMin_pos_of_fullColumnRank {m : ℕ}
    (A : Fin m → Fin 2 → ℝ)
    (hinj : Function.Injective (rectMatMulVec A)) :
    0 < higham19Problem19_9SigmaMin A := by
  by_contra hnot
  have hsigma_zero : higham19Problem19_9SigmaMin A = 0 :=
    le_antisymm (le_of_not_gt hnot) (higham19_problem19_9_sigmaMin_nonneg A)
  obtain ⟨x, hx_ne, hsq⟩ :=
    realRectToCMatrix_last_singularValue_exists_real_attaining_vector_sq A
  have hsing_zero :
      complexMatrixSingularValue (realRectToCMatrix A) (Fin.last 1) = 0 := by
    simpa [higham19Problem19_9SigmaMin] using hsigma_zero
  have hx_action_zero : rectMatMulVec A x = 0 := by
    apply funext
    apply (vecNorm2_eq_zero_iff (rectMatMulVec A x)).1
    apply (sq_eq_zero_iff).1
    rw [vecNorm2_sq, hsq, hsing_zero]
    ring
  have hx_zero : x = 0 := by
    have h0 : rectMatMulVec A x = rectMatMulVec A (fun _j => 0) := by
      rw [hx_action_zero]
      ext i
      simp [rectMatMulVec]
    exact hinj h0
  exact hx_ne hx_zero

/-- The actual least singular value supplies the lower action bound. -/
theorem higham19_problem19_9_sigmaMin_mul_vecNorm2_le {m : ℕ}
    (A : Fin m → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    higham19Problem19_9SigmaMin A * vecNorm2 x ≤
      vecNorm2 (rectMatMulVec A x) := by
  have h :=
    complexMatrixSingularValue_last_mul_norm_le_norm_euclideanLin
      (realRectToCMatrix A) (realVecToEuclidean x)
  rw [realVecToEuclidean_norm] at h
  rw [realRectToCMatrix_euclideanLin_realVecToEuclidean_norm] at h
  simpa [higham19Problem19_9SigmaMin] using h

/-- Squared norm of the residual after projecting `a` onto `b`. -/
theorem higham19_problem19_9_projection_residual_sq {m : ℕ}
    (a b : Fin m → ℝ) (hb : vecNorm2 b ≠ 0) :
    vecNorm2Sq (fun i =>
        a i - (dotProduct a b / vecNorm2 b ^ 2) * b i) =
      vecNorm2 a ^ 2 - dotProduct a b ^ 2 / vecNorm2 b ^ 2 := by
  let α := dotProduct a b / vecNorm2 b ^ 2
  have hb2 : vecNorm2 b ^ 2 ≠ 0 := pow_ne_zero 2 hb
  have hsum :
      vecNorm2Sq (fun i => a i - α * b i) =
        vecNorm2Sq a - 2 * α * dotProduct a b + α ^ 2 * vecNorm2Sq b := by
    unfold vecNorm2Sq dotProduct
    calc
      (∑ i : Fin m, (a i - α * b i) ^ 2) =
          ∑ i : Fin m,
            (a i ^ 2 - 2 * α * (a i * b i) + α ^ 2 * b i ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : Fin m, a i ^ 2) -
          2 * α * (∑ i : Fin m, a i * b i) +
            α ^ 2 * (∑ i : Fin m, b i ^ 2) := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                ← Finset.mul_sum]
  rw [show (fun i => a i - (dotProduct a b / vecNorm2 b ^ 2) * b i) =
      (fun i => a i - α * b i) by rfl]
  rw [hsum, ← vecNorm2_sq a, ← vecNorm2_sq b]
  dsimp [α]
  field_simp [hb2]
  ring

/-- Testing the least-gain inequality on the projection coefficient vector
shows that `sigma_min` is at most the projection residual norm. -/
theorem higham19_problem19_9_sigmaMin_le_projection_residual {m : ℕ}
    (a b : Fin m → ℝ) :
    higham19Problem19_9SigmaMin (higham19Problem19_9Matrix a b) ≤
      vecNorm2 (fun i =>
        a i - (dotProduct a b / vecNorm2 b ^ 2) * b i) := by
  let α := dotProduct a b / vecNorm2 b ^ 2
  let x : Fin 2 → ℝ := fun j => if j = 0 then 1 else -α
  have hxnormSq : vecNorm2Sq x = 1 + α ^ 2 := by
    simp [x, vecNorm2Sq, Fin.sum_univ_two]
  have hxnorm : 1 ≤ vecNorm2 x := by
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (1 + α ^ 2) := by
      rw [Real.le_sqrt (by norm_num) (by nlinarith [sq_nonneg α])]
      nlinarith [sq_nonneg α]
    simpa [vecNorm2, hxnormSq] using hsqrt
  have haction :
      rectMatMulVec (higham19Problem19_9Matrix a b) x =
        fun i => a i - α * b i := by
    ext i
    simp [rectMatMulVec, higham19Problem19_9Matrix, x, Fin.sum_univ_two]
    ring
  have hlower := higham19_problem19_9_sigmaMin_mul_vecNorm2_le
    (higham19Problem19_9Matrix a b) x
  have hsigma0 := higham19_problem19_9_sigmaMin_nonneg
    (higham19Problem19_9Matrix a b)
  have hsigma_le_prod :
      higham19Problem19_9SigmaMin (higham19Problem19_9Matrix a b) ≤
        higham19Problem19_9SigmaMin (higham19Problem19_9Matrix a b) *
          vecNorm2 x := by
    nlinarith
  rw [haction] at hlower
  change _ ≤ vecNorm2 (fun i => a i - α * b i)
  exact hsigma_le_prod.trans hlower

/-- Symmetric projection test, retaining the original `[a,b]` column order
while projecting the second column onto the first. -/
theorem higham19_problem19_9_sigmaMin_le_second_projection_residual {m : ℕ}
    (a b : Fin m → ℝ) :
    higham19Problem19_9SigmaMin (higham19Problem19_9Matrix a b) ≤
      vecNorm2 (fun i =>
        b i - (dotProduct b a / vecNorm2 a ^ 2) * a i) := by
  let α := dotProduct b a / vecNorm2 a ^ 2
  let x : Fin 2 → ℝ := fun j => if j = 0 then -α else 1
  have hxnormSq : vecNorm2Sq x = 1 + α ^ 2 := by
    simp [x, vecNorm2Sq, Fin.sum_univ_two]
    ring
  have hxnorm : 1 ≤ vecNorm2 x := by
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (1 + α ^ 2) := by
      rw [Real.le_sqrt (by norm_num) (by nlinarith [sq_nonneg α])]
      nlinarith [sq_nonneg α]
    simpa [vecNorm2, hxnormSq] using hsqrt
  have haction :
      rectMatMulVec (higham19Problem19_9Matrix a b) x =
        fun i => b i - α * a i := by
    ext i
    simp [rectMatMulVec, higham19Problem19_9Matrix, x, Fin.sum_univ_two]
    ring
  have hlower := higham19_problem19_9_sigmaMin_mul_vecNorm2_le
    (higham19Problem19_9Matrix a b) x
  have hsigma0 := higham19_problem19_9_sigmaMin_nonneg
    (higham19Problem19_9Matrix a b)
  have hsigma_le_prod :
      higham19Problem19_9SigmaMin (higham19Problem19_9Matrix a b) ≤
        higham19Problem19_9SigmaMin (higham19Problem19_9Matrix a b) *
          vecNorm2 x := by
    nlinarith
  rw [haction] at hlower
  change _ ≤ vecNorm2 (fun i => b i - α * a i)
  exact hsigma_le_prod.trans hlower

/-- The projection residual has exactly length `‖a‖₂ sin θ` when `θ` is the
acute angle specified in Problem 19.9. -/
theorem higham19_problem19_9_projection_residual_eq_sin {m : ℕ}
    (a b : Fin m → ℝ) (θ : ℝ)
    (ha : 0 < vecNorm2 a) (hb : 0 < vecNorm2 b)
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hcos : Real.cos θ =
      |dotProduct a b| / (vecNorm2 a * vecNorm2 b)) :
    vecNorm2 (fun i =>
        a i - (dotProduct a b / vecNorm2 b ^ 2) * b i) =
      vecNorm2 a * Real.sin θ := by
  let r : Fin m → ℝ := fun i =>
    a i - (dotProduct a b / vecNorm2 b ^ 2) * b i
  have ha_ne : vecNorm2 a ≠ 0 := ne_of_gt ha
  have hb_ne : vecNorm2 b ≠ 0 := ne_of_gt hb
  have hden : vecNorm2 a * vecNorm2 b ≠ 0 := mul_ne_zero ha_ne hb_ne
  have habs : |dotProduct a b| =
      Real.cos θ * (vecNorm2 a * vecNorm2 b) := by
    exact ((eq_div_iff hden).mp hcos).symm
  have hdotSq : dotProduct a b ^ 2 =
      Real.cos θ ^ 2 * vecNorm2 a ^ 2 * vecNorm2 b ^ 2 := by
    calc
      dotProduct a b ^ 2 = |dotProduct a b| ^ 2 := by rw [sq_abs]
      _ = _ := by rw [habs]; ring
  have hrsq := higham19_problem19_9_projection_residual_sq a b hb_ne
  have hrsq' : vecNorm2Sq r =
      vecNorm2 a ^ 2 * Real.sin θ ^ 2 := by
    change vecNorm2Sq r = _ at hrsq ⊢
    rw [hrsq, hdotSq]
    field_simp [pow_ne_zero 2 hb_ne]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθpi
  apply (sq_eq_sq₀ (vecNorm2_nonneg r) (mul_nonneg ha.le hsin0)).mp
  rw [vecNorm2_sq, hrsq']
  ring

/-- Full Problem 19.9.  For a full-rank two-column matrix, its spectral
condition number is bounded below by the column-norm ratio times `cot θ`. -/
theorem higham19_problem19_9_condition_ge_scaled_cot {m : ℕ}
    (a₁ a₂ : Fin m → ℝ) (θ : ℝ)
    (ha₁ : 0 < vecNorm2 a₁) (ha₂ : 0 < vecNorm2 a₂)
    (hθ0 : 0 < θ) (hθhalf : θ ≤ Real.pi / 2)
    (hcos : Real.cos θ =
      |dotProduct a₁ a₂| / (vecNorm2 a₁ * vecNorm2 a₂))
    (hsigma : 0 < higham19Problem19_9SigmaMin
      (higham19Problem19_9Matrix a₁ a₂)) :
    max (vecNorm2 a₁) (vecNorm2 a₂) /
        min (vecNorm2 a₁) (vecNorm2 a₂) * Real.cot θ ≤
      higham19Problem19_9Kappa2 (higham19Problem19_9Matrix a₁ a₂) := by
  let A := higham19Problem19_9Matrix a₁ a₂
  let σ := higham19Problem19_9SigmaMin A
  let op := rectOpNorm2 A
  have hθpi : θ < Real.pi := by
    have hp : 0 < Real.pi := Real.pi_pos
    linarith
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hθhalf
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hop1 : vecNorm2 a₁ ≤ op := by
    simpa [A, higham19Problem19_9Matrix, ch7RectColumnNorm2] using
      (eq_7_20_column_norm_le_of_rectOpNorm2Le A
        (rectOpNorm2Le_rectOpNorm2 A) (0 : Fin 2))
  have hop2 : vecNorm2 a₂ ≤ op := by
    simpa [A, higham19Problem19_9Matrix, ch7RectColumnNorm2] using
      (eq_7_20_column_norm_le_of_rectOpNorm2Le A
        (rectOpNorm2Le_rectOpNorm2 A) (1 : Fin 2))
  by_cases hle : vecNorm2 a₁ ≤ vecNorm2 a₂
  · have hsigmaProj :=
      higham19_problem19_9_sigmaMin_le_projection_residual a₁ a₂
    have hres := higham19_problem19_9_projection_residual_eq_sin
      a₁ a₂ θ ha₁ ha₂ hθ0.le (le_trans hθhalf (by linarith [Real.pi_pos])) hcos
    have hσbound : σ ≤ vecNorm2 a₁ * Real.sin θ := by
      simpa [A, σ, hres] using hsigmaProj
    have hratio :
        vecNorm2 a₂ / (vecNorm2 a₁ * Real.sin θ) ≤ op / σ := by
      exact div_le_div₀ (rectOpNorm2_nonneg A) hop2 hsigma hσbound
    rw [max_eq_right hle, min_eq_left hle, higham19Problem19_9Kappa2]
    rw [Real.cot_eq_cos_div_sin]
    dsimp [A, σ, op] at hratio ⊢
    calc
      vecNorm2 a₂ / vecNorm2 a₁ * (Real.cos θ / Real.sin θ) ≤
          vecNorm2 a₂ / (vecNorm2 a₁ * Real.sin θ) := by
            field_simp [ne_of_gt ha₁, ne_of_gt hsin]
            nlinarith [mul_nonneg ha₂.le hcos0]
      _ ≤ _ := hratio
  · have hle' : vecNorm2 a₂ ≤ vecNorm2 a₁ := le_of_not_ge hle
    have hsigmaProj :=
      higham19_problem19_9_sigmaMin_le_second_projection_residual a₁ a₂
    have hcos' : Real.cos θ =
        |dotProduct a₂ a₁| / (vecNorm2 a₂ * vecNorm2 a₁) := by
      simpa [dotProduct_comm, mul_comm] using hcos
    have hres := higham19_problem19_9_projection_residual_eq_sin
      a₂ a₁ θ ha₂ ha₁ hθ0.le (le_trans hθhalf (by linarith [Real.pi_pos])) hcos'
    have hσbound : σ ≤ vecNorm2 a₂ * Real.sin θ := by
      simpa [A, σ, hres] using hsigmaProj
    have hratio :
        vecNorm2 a₁ / (vecNorm2 a₂ * Real.sin θ) ≤ op / σ := by
      exact div_le_div₀ (rectOpNorm2_nonneg A) hop1 hsigma hσbound
    rw [max_eq_left hle', min_eq_right hle', higham19Problem19_9Kappa2]
    rw [Real.cot_eq_cos_div_sin]
    dsimp [A, σ, op] at hratio ⊢
    calc
      vecNorm2 a₁ / vecNorm2 a₂ * (Real.cos θ / Real.sin θ) ≤
          vecNorm2 a₁ / (vecNorm2 a₂ * Real.sin θ) := by
            field_simp [ne_of_gt ha₂, ne_of_gt hsin]
            nlinarith [mul_nonneg ha₁.le hcos0]
      _ ≤ _ := hratio

/-- Source-facing full-column-rank form of Problem 19.9. -/
theorem higham19_problem19_9_condition_ge_scaled_cot_of_fullColumnRank {m : ℕ}
    (a₁ a₂ : Fin m → ℝ) (θ : ℝ)
    (ha₁ : 0 < vecNorm2 a₁) (ha₂ : 0 < vecNorm2 a₂)
    (hθ0 : 0 < θ) (hθhalf : θ ≤ Real.pi / 2)
    (hcos : Real.cos θ =
      |dotProduct a₁ a₂| / (vecNorm2 a₁ * vecNorm2 a₂))
    (hfull : Function.Injective
      (rectMatMulVec (higham19Problem19_9Matrix a₁ a₂))) :
    max (vecNorm2 a₁) (vecNorm2 a₂) /
        min (vecNorm2 a₁) (vecNorm2 a₂) * Real.cot θ ≤
      higham19Problem19_9Kappa2 (higham19Problem19_9Matrix a₁ a₂) := by
  exact higham19_problem19_9_condition_ge_scaled_cot
    a₁ a₂ θ ha₁ ha₂ hθ0 hθhalf hcos
    (higham19_problem19_9_sigmaMin_pos_of_fullColumnRank _ hfull)

end NumStability
