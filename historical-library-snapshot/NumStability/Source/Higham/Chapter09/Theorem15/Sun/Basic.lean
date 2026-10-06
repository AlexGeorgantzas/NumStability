import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem01
import NumStability.Source.Higham.Chapter07.Corollary06.Equilibration.Basic
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# Chapter09 Theorem15 Sun Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapters1To9SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators
open scoped Topology
open scoped Matrix.Norms.Operator

namespace NumStability

/-- Sun's mixed-inverse comparison kernel. The two mixed residuals satisfy
genuine one-sided resolvent inequalities, so this proof does not use the
unavailable nonlinear self-majorant route. -/
theorem higham9_15_sun_mixed_resolvent_normalized_bounds
    {n : ℕ}
    (G X Y P Q Z T R : Matrix (Fin n) (Fin n) ℝ)
    (hZsplit : Z = X + Q)
    (hZres : Z = G + G * Q)
    (hTsplit : T = P + Y)
    (hTres : T = G + P * G)
    (hX : ∀ i j : Fin n, i.val ≤ j.val → X i j = 0)
    (hY : ∀ i j : Fin n, j.val < i.val → Y i j = 0)
    (hP : ∀ i j : Fin n, i.val ≤ j.val → P i j = 0)
    (hQ : ∀ i j : Fin n, j.val < i.val → Q i j = 0)
    (hR : ch7NonnegativeResolvent n (absMatrix n G) R) :
    (∀ i j : Fin n,
      |X i j| ≤
        higham9_15_strilPart
          (rectMatMul R (absMatrix n G)) i j) ∧
      (∀ i j : Fin n,
        |Y i j| ≤
          higham9_15_triuPart
            (rectMatMul (absMatrix n G) R) i j) := by
  let C : Matrix (Fin n) (Fin n) ℝ := absMatrix n G
  let WZ : Matrix (Fin n) (Fin n) ℝ := absMatrix n Z
  let WT : Matrix (Fin n) (Fin n) ℝ := absMatrix n T
  have hstrilZ : higham9_15_strilPart Z = X := by
    rw [hZsplit]
    exact higham9_15_strilPart_add_strictLower_upper X Q hX hQ
  have htriuZ : higham9_15_triuPart Z = Q := by
    rw [hZsplit]
    exact higham9_15_triuPart_add_strictLower_upper X Q hX hQ
  have hstrilT : higham9_15_strilPart T = P := by
    rw [hTsplit]
    exact higham9_15_strilPart_add_strictLower_upper P Y hP hY
  have htriuT : higham9_15_triuPart T = Y := by
    rw [hTsplit]
    exact higham9_15_triuPart_add_strictLower_upper P Y hP hY
  have hQabs : ∀ i j : Fin n, |Q i j| ≤ |Z i j| := by
    intro i j
    rw [← htriuZ]
    unfold higham9_15_triuPart
    by_cases hij : i.val ≤ j.val
    · simp [hij]
    · simp [hij, abs_nonneg]
  have hPabs : ∀ i j : Fin n, |P i j| ≤ |T i j| := by
    intro i j
    rw [← hstrilT]
    unfold higham9_15_strilPart
    by_cases hji : j.val < i.val
    · simp [hji]
    · simp [hji, abs_nonneg]
  have hZineq : ∀ i j : Fin n,
      WZ i j ≤ C i j + rectMatMul C WZ i j := by
    intro i j
    calc
      WZ i j = |G i j + (G * Q) i j| := by
        simp only [WZ, absMatrix]
        rw [hZres]
        rfl
      _ ≤ |G i j| + |(G * Q) i j| := abs_add_le _ _
      _ ≤ |G i j| +
          rectMatMul (absMatrix n G) (absMatrix n Q) i j :=
        add_le_add_right
          (higham9_15_abs_matrix_mul_le_abs_mul_abs G Q i j) _
      _ ≤ C i j + rectMatMul C WZ i j := by
        simp only [C, WZ, absMatrix, rectMatMul]
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hQabs k j) (abs_nonneg (G i k))
  have hTineq : ∀ i j : Fin n,
      WT i j ≤ C i j + rectMatMul WT C i j := by
    intro i j
    calc
      WT i j = |G i j + (P * G) i j| := by
        simp only [WT, absMatrix]
        rw [hTres]
        rfl
      _ ≤ |G i j| + |(P * G) i j| := abs_add_le _ _
      _ ≤ |G i j| +
          rectMatMul (absMatrix n P) (absMatrix n G) i j :=
        add_le_add_right
          (higham9_15_abs_matrix_mul_le_abs_mul_abs P G i j) _
      _ ≤ C i j + rectMatMul WT C i j := by
        simp only [C, WT, absMatrix, rectMatMul]
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hPabs i k) (abs_nonneg (G k j))
  have hZmajor : ∀ i j : Fin n,
      WZ i j ≤ rectMatMul R C i j :=
    higham9_15_resolvent_matrix_majorant_of_componentwise_inequality
      C R C WZ (by simpa [C] using hR) hZineq
  have hTmajor : ∀ i j : Fin n,
      WT i j ≤ rectMatMul C R i j :=
    higham9_15_resolvent_matrix_majorant_right_of_componentwise_inequality
      C R C WT (by simpa [C] using hR) hTineq
  have hRCnonneg : ∀ i j : Fin n,
      0 ≤ rectMatMul R C i j := by
    intro i j
    unfold rectMatMul C
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (hR.1 i k) (abs_nonneg (G k j))
  have hCRnonneg : ∀ i j : Fin n,
      0 ≤ rectMatMul C R i j := by
    intro i j
    unfold rectMatMul C
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (abs_nonneg (G i k)) (hR.1 k j)
  constructor
  · intro i j
    calc
      |X i j| = |higham9_15_strilPart Z i j| := by rw [hstrilZ]
      _ ≤ higham9_15_strilPart (rectMatMul R C) i j :=
        higham9_15_abs_strilPart_le_strilPart_of_abs_le
          Z (rectMatMul R C) hRCnonneg
          (by
            intro r c
            simpa [WZ] using hZmajor r c) i j
      _ = higham9_15_strilPart
          (rectMatMul R (absMatrix n G)) i j := by rfl
  · intro i j
    calc
      |Y i j| = |higham9_15_triuPart T i j| := by rw [htriuT]
      _ ≤ higham9_15_triuPart (rectMatMul C R) i j :=
        higham9_15_abs_triuPart_le_triuPart_of_abs_le
          T (rectMatMul C R) hCRnonneg
          (by
            intro r c
            simpa [WT] using hTmajor r c) i j
      _ = higham9_15_triuPart
          (rectMatMul (absMatrix n G) R) i j := by rfl

/-- Source-factor form of Sun's mixed-inverse argument. The additional
inverse witnesses belong to the unperturbed factors `Lhat - ΔL` and
`Uhat - ΔU`; they are structural and do not encode either bound. -/
theorem higham9_15_sun_componentwise_source_bounds_of_resolvent
    {n : ℕ}
    (A Lhat Uhat LhatInv UhatInv LbaseInv UbaseInv ΔA ΔL ΔU R :
      Matrix (Fin n) (Fin n) ℝ)
    (hA : (Lhat - ΔL) * (Uhat - ΔU) = A)
    (hPert : Lhat * Uhat = A + ΔA)
    (hLhatLeft : LhatInv * Lhat = 1)
    (hLhatRight : Lhat * LhatInv = 1)
    (hUhatRight : Uhat * UhatInv = 1)
    (hUhatLeft : UhatInv * Uhat = 1)
    (hLbaseLeft : LbaseInv * (Lhat - ΔL) = 1)
    (hUbaseRight : (Uhat - ΔU) * UbaseInv = 1)
    (hLhatInv_lower :
      ∀ i j : Fin n, i.val < j.val → LhatInv i j = 0)
    (hUhatInv_upper :
      ∀ i j : Fin n, j.val < i.val → UhatInv i j = 0)
    (hLbaseInv_lower :
      ∀ i j : Fin n, i.val < j.val → LbaseInv i j = 0)
    (hUbaseInv_upper :
      ∀ i j : Fin n, j.val < i.val → UbaseInv i j = 0)
    (hΔL_strict :
      ∀ i j : Fin n, i.val ≤ j.val → ΔL i j = 0)
    (hΔU_upper :
      ∀ i j : Fin n, j.val < i.val → ΔU i j = 0)
    (hR : ch7NonnegativeResolvent n
      (absMatrix n (higham9_27_GMatrix LhatInv ΔA UhatInv)) R) :
    (∀ i j : Fin n, |ΔL i j| ≤
        rectMatMul (absMatrix n Lhat)
          (higham9_15_strilPart
            (rectMatMul R
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv)))) i j) ∧
      (∀ i j : Fin n, |ΔU i j| ≤
        rectMatMul
          (higham9_15_triuPart
            (rectMatMul
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv)) R))
          (absMatrix n Uhat) i j) := by
  let G : Matrix (Fin n) (Fin n) ℝ := LhatInv * ΔA * UhatInv
  let X : Matrix (Fin n) (Fin n) ℝ := LhatInv * ΔL
  let Y : Matrix (Fin n) (Fin n) ℝ := ΔU * UhatInv
  let P : Matrix (Fin n) (Fin n) ℝ := LbaseInv * ΔL
  let Q : Matrix (Fin n) (Fin n) ℝ := ΔU * UbaseInv
  let Z : Matrix (Fin n) (Fin n) ℝ := LhatInv * ΔA * UbaseInv
  let T : Matrix (Fin n) (Fin n) ℝ := LbaseInv * ΔA * UhatInv
  have hΔA_lower :
      ΔA = Lhat * ΔU + ΔL * (Uhat - ΔU) := by
    calc
      ΔA = (A + ΔA) - A := by abel
      _ = Lhat * Uhat - (Lhat - ΔL) * (Uhat - ΔU) := by
        rw [hPert, hA]
      _ = Lhat * ΔU + ΔL * (Uhat - ΔU) := by noncomm_ring
  have hΔA_upper :
      ΔA = (Lhat - ΔL) * ΔU + ΔL * Uhat := by
    calc
      ΔA = (A + ΔA) - A := by abel
      _ = Lhat * Uhat - (Lhat - ΔL) * (Uhat - ΔU) := by
        rw [hPert, hA]
      _ = (Lhat - ΔL) * ΔU + ΔL * Uhat := by noncomm_ring
  have hZsplit : Z = X + Q := by
    dsimp [Z, X, Q]
    rw [hΔA_lower]
    calc
      LhatInv * (Lhat * ΔU + ΔL * (Uhat - ΔU)) * UbaseInv =
          (LhatInv * Lhat) * ΔU * UbaseInv +
            LhatInv * ΔL * ((Uhat - ΔU) * UbaseInv) := by
        noncomm_ring
      _ = LhatInv * ΔL + ΔU * UbaseInv := by
        rw [hLhatLeft, hUbaseRight]
        noncomm_ring
  have hZres : Z = G + G * Q := by
    dsimp [Z, G, Q]
    calc
      LhatInv * ΔA * UbaseInv =
          (LhatInv * ΔA * UhatInv) * Uhat * UbaseInv := by
        symm
        calc
          (LhatInv * ΔA * UhatInv) * Uhat * UbaseInv =
              LhatInv * ΔA * (UhatInv * Uhat) * UbaseInv := by
            simp only [mul_assoc]
          _ = LhatInv * ΔA * UbaseInv := by
            rw [hUhatLeft]
            simp
      _ = (LhatInv * ΔA * UhatInv) *
          (((Uhat - ΔU) * UbaseInv) + ΔU * UbaseInv) := by
        noncomm_ring
      _ = LhatInv * ΔA * UhatInv +
          (LhatInv * ΔA * UhatInv) * (ΔU * UbaseInv) := by
        rw [hUbaseRight]
        noncomm_ring
  have hTsplit : T = P + Y := by
    dsimp [T, P, Y]
    rw [hΔA_upper]
    calc
      LbaseInv * ((Lhat - ΔL) * ΔU + ΔL * Uhat) * UhatInv =
          (LbaseInv * (Lhat - ΔL)) * ΔU * UhatInv +
            LbaseInv * ΔL * (Uhat * UhatInv) := by
        noncomm_ring
      _ = LbaseInv * ΔL + ΔU * UhatInv := by
        rw [hLbaseLeft, hUhatRight]
        noncomm_ring
  have hTres : T = G + P * G := by
    dsimp [T, G, P]
    calc
      LbaseInv * ΔA * UhatInv =
          LbaseInv * Lhat * (LhatInv * ΔA * UhatInv) := by
        symm
        calc
          LbaseInv * Lhat * (LhatInv * ΔA * UhatInv) =
              LbaseInv * (Lhat * LhatInv) * ΔA * UhatInv := by
            simp only [mul_assoc]
          _ = LbaseInv * ΔA * UhatInv := by
            rw [hLhatRight]
            simp
      _ = ((LbaseInv * (Lhat - ΔL)) + LbaseInv * ΔL) *
          (LhatInv * ΔA * UhatInv) := by
        noncomm_ring
      _ = LhatInv * ΔA * UhatInv +
          (LbaseInv * ΔL) * (LhatInv * ΔA * UhatInv) := by
        rw [hLbaseLeft]
        noncomm_ring
  have hX : ∀ i j : Fin n, i.val ≤ j.val → X i j = 0 := by
    simpa [X, rectMatMul, Matrix.mul_apply] using
      higham9_15_rectMatMul_lower_strictLower_is_strictLower
        LhatInv ΔL hLhatInv_lower hΔL_strict
  have hY : ∀ i j : Fin n, j.val < i.val → Y i j = 0 := by
    simpa [Y, rectMatMul, Matrix.mul_apply] using
      higham9_15_rectMatMul_upper_upper_is_upper
        ΔU UhatInv hΔU_upper hUhatInv_upper
  have hP : ∀ i j : Fin n, i.val ≤ j.val → P i j = 0 := by
    simpa [P, rectMatMul, Matrix.mul_apply] using
      higham9_15_rectMatMul_lower_strictLower_is_strictLower
        LbaseInv ΔL hLbaseInv_lower hΔL_strict
  have hQ : ∀ i j : Fin n, j.val < i.val → Q i j = 0 := by
    simpa [Q, rectMatMul, Matrix.mul_apply] using
      higham9_15_rectMatMul_upper_upper_is_upper
        ΔU UbaseInv hΔU_upper hUbaseInv_upper
  have hGsource :
      G = higham9_27_GMatrix LhatInv ΔA UhatInv := by
    ext i j
    simp [G, higham9_27_GMatrix, rectMatMul, Matrix.mul_apply]
  have hnorm :=
    higham9_15_sun_mixed_resolvent_normalized_bounds
      G X Y P Q Z T R hZsplit hZres hTsplit hTres hX hY hP hQ
      (by simpa [hGsource] using hR)
  constructor
  · intro i j
    have hΔLeq : ΔL = Lhat * X := by
      dsimp [X]
      calc
        ΔL = 1 * ΔL := by simp
        _ = (Lhat * LhatInv) * ΔL := by rw [hLhatRight]
        _ = Lhat * (LhatInv * ΔL) := by rw [mul_assoc]
    calc
      |ΔL i j| = |(Lhat * X) i j| := by rw [hΔLeq]
      _ ≤ rectMatMul (absMatrix n Lhat) (absMatrix n X) i j :=
        higham9_15_abs_matrix_mul_le_abs_mul_abs Lhat X i j
      _ ≤ rectMatMul (absMatrix n Lhat)
          (higham9_15_strilPart
            (rectMatMul R (absMatrix n G))) i j := by
        unfold rectMatMul absMatrix
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hnorm.1 k j) (abs_nonneg (Lhat i k))
      _ = rectMatMul (absMatrix n Lhat)
          (higham9_15_strilPart
            (rectMatMul R
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv)))) i j := by
        rw [hGsource]
  · intro i j
    have hΔUeq : ΔU = Y * Uhat := by
      dsimp [Y]
      calc
        ΔU = ΔU * 1 := by simp
        _ = ΔU * (UhatInv * Uhat) := by rw [hUhatLeft]
        _ = (ΔU * UhatInv) * Uhat := by rw [mul_assoc]
    calc
      |ΔU i j| = |(Y * Uhat) i j| := by rw [hΔUeq]
      _ ≤ rectMatMul (absMatrix n Y) (absMatrix n Uhat) i j :=
        higham9_15_abs_matrix_mul_le_abs_mul_abs Y Uhat i j
      _ ≤ rectMatMul
          (higham9_15_triuPart
            (rectMatMul (absMatrix n G) R))
          (absMatrix n Uhat) i j := by
        unfold rectMatMul absMatrix
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hnorm.2 i k) (abs_nonneg (Uhat k j))
      _ = rectMatMul
          (higham9_15_triuPart
            (rectMatMul
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv)) R))
          (absMatrix n Uhat) i j := by
        rw [hGsource]

/-- Higham Theorem 9.15's printed componentwise endpoint, with Sun's two
mixed-inverse comparisons replacing the previously assumed nonlinear
self-majorant. -/
theorem higham9_15_sun_componentwise_source_bounds_of_spectralRadius_lt_one
    {n : ℕ} (hn : 0 < n)
    (A Lhat Uhat LhatInv UhatInv LbaseInv UbaseInv ΔA ΔL ΔU :
      Matrix (Fin n) (Fin n) ℝ)
    (hA : (Lhat - ΔL) * (Uhat - ΔU) = A)
    (hPert : Lhat * Uhat = A + ΔA)
    (hLhatLeft : LhatInv * Lhat = 1)
    (hLhatRight : Lhat * LhatInv = 1)
    (hUhatRight : Uhat * UhatInv = 1)
    (hUhatLeft : UhatInv * Uhat = 1)
    (hLbaseLeft : LbaseInv * (Lhat - ΔL) = 1)
    (hUbaseRight : (Uhat - ΔU) * UbaseInv = 1)
    (hLhatInv_lower :
      ∀ i j : Fin n, i.val < j.val → LhatInv i j = 0)
    (hUhatInv_upper :
      ∀ i j : Fin n, j.val < i.val → UhatInv i j = 0)
    (hLbaseInv_lower :
      ∀ i j : Fin n, i.val < j.val → LbaseInv i j = 0)
    (hUbaseInv_upper :
      ∀ i j : Fin n, j.val < i.val → UbaseInv i j = 0)
    (hΔL_strict :
      ∀ i j : Fin n, i.val ≤ j.val → ΔL i j = 0)
    (hΔU_upper :
      ∀ i j : Fin n, j.val < i.val → ΔU i j = 0)
    (hrho :
      spectralRadius ℂ
          (Matrix.toLin'
            (show Matrix (Fin n) (Fin n) ℂ from
              realRectToCMatrix
                (absMatrix n
                  (higham9_27_GMatrix LhatInv ΔA UhatInv)))) < 1) :
    (∀ i j : Fin n, |ΔL i j| ≤
        rectMatMul (absMatrix n Lhat)
          (higham9_15_strilPart
            (rectMatMul
              (nonsingInv n
                (matSub_id n
                  (absMatrix n
                    (higham9_27_GMatrix LhatInv ΔA UhatInv))))
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv)))) i j) ∧
      (∀ i j : Fin n, |ΔU i j| ≤
        rectMatMul
          (higham9_15_triuPart
            (rectMatMul
              (absMatrix n
                (higham9_27_GMatrix LhatInv ΔA UhatInv))
              (nonsingInv n
                (matSub_id n
                  (absMatrix n
                    (higham9_27_GMatrix LhatInv ΔA UhatInv))))))
          (absMatrix n Uhat) i j) := by
  let Gabs : Matrix (Fin n) (Fin n) ℝ :=
    absMatrix n (higham9_27_GMatrix LhatInv ΔA UhatInv)
  let R : Matrix (Fin n) (Fin n) ℝ :=
    nonsingInv n (matSub_id n Gabs)
  have hGabs_nonneg : ∀ i j : Fin n, 0 ≤ Gabs i j := by
    intro i j
    simp [Gabs, absMatrix]
  have hR : ch7NonnegativeResolvent n Gabs R := by
    exact
      higham9_15_nonnegative_resolvent_nonsingInv_of_spectralRadius_lt_one
        hn Gabs hGabs_nonneg (by simpa [Gabs] using hrho)
  simpa [Gabs, R] using
    higham9_15_sun_componentwise_source_bounds_of_resolvent
      A Lhat Uhat LhatInv UhatInv LbaseInv UbaseInv ΔA ΔL ΔU R
      hA hPert hLhatLeft hLhatRight hUhatRight hUhatLeft
      hLbaseLeft hUbaseRight hLhatInv_lower hUhatInv_upper
      hLbaseInv_lower hUbaseInv_upper hΔL_strict hΔU_upper
      (by simpa [Gabs] using hR)

end NumStability
