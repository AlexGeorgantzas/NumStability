import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Algorithms.NormEstimation.OneNorm.LAPACK.Basic
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter15.Algorithm04.LAPACKNormEstimator.Basic

/-!
# Chapter15 Equation06 LAPACKCounterexample Basic

Canonical destination for material split out of
`NumStability.Algorithms.Chapter15CondEst` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Higham15

open scoped BigOperators

/-- A nonzero direction orthogonal to the three vectors sampled by the
    four-dimensional instance of Algorithm 15.4: `e`, `e₁`, and the
    alternating vector `b`. -/
def H15_eq15_6_v : Fin 4 → ℝ := fun i =>
  if i = 0 then 0 else if i = 1 then 11 else if i = 2 then -2 else -9

/-- The rank-one orthogonal projector used in the concrete instance of
    Higham's equation (15.6).  Its denominator is
    `vᵀv = 11² + 2² + 9² = 206`. -/
noncomputable def H15_eq15_6_P : Fin 4 → Fin 4 → ℝ :=
  fun i j => H15_eq15_6_v i * H15_eq15_6_v j / 206

/-- The counterexample family `A(θ) = I + θP` from equation (15.6). -/
noncomputable def H15_eq15_6_A (θ : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => (if i = j then 1 else 0) + θ * H15_eq15_6_P i j

theorem H15_eq15_6_P_symmetric :
    ∀ i j, H15_eq15_6_P i j = H15_eq15_6_P j i := by
  intro i j
  simp only [H15_eq15_6_P]
  ring

/-- `Pe = 0`, the first annihilation relation printed in (15.6). -/
theorem H15_eq15_6_P_mul_e (i : Fin 4) :
    ∑ j : Fin 4, H15_eq15_6_P i j = 0 := by
  fin_cases i <;> simp [Fin.sum_univ_four, H15_eq15_6_P, H15_eq15_6_v] <;>
    norm_num

/-- `Pe₁ = 0`, the second annihilation relation printed in (15.6). -/
theorem H15_eq15_6_P_mul_e1 (i : Fin 4) :
    ∑ j : Fin 4, H15_eq15_6_P i j * basisVec (0 : Fin 4) j = 0 := by
  fin_cases i <;>
    simp [Fin.sum_univ_four, H15_eq15_6_P, H15_eq15_6_v, basisVec] <;>
    norm_num

/-- `Pb = 0`, where `b` is Algorithm 15.4's alternating vector. -/
theorem H15_eq15_6_P_mul_b (i : Fin 4) :
    ∑ j : Fin 4, H15_eq15_6_P i j * lapackAltVec (by omega : 1 < 4) j = 0 := by
  fin_cases i <;>
    simp [Fin.sum_univ_four, H15_eq15_6_P, H15_eq15_6_v, lapackAltVec,
      even_iff_two_dvd] <;>
    norm_num

/-- The exact family fixes the uniform starting vector used by Algorithm 15.4. -/
theorem H15_eq15_6_A_mul_uniform (θ : ℝ) (i : Fin 4) :
    (∑ j : Fin 4, H15_eq15_6_A θ i j * ((1 : ℝ) / 4)) = 1 / 4 := by
  fin_cases i <;>
    simp [Fin.sum_univ_four, H15_eq15_6_A, H15_eq15_6_P, H15_eq15_6_v] <;>
    ring

/-- Symmetry and `Pe=0` imply `A(θ)ᵀe=e`, so the first power-method
    iteration satisfies its stopping test exactly. -/
theorem H15_eq15_6_AT_mul_e (θ : ℝ) (j : Fin 4) :
    ∑ i : Fin 4, H15_eq15_6_A θ i j = 1 := by
  fin_cases j <;>
    simp [Fin.sum_univ_four, H15_eq15_6_A, H15_eq15_6_P, H15_eq15_6_v] <;>
    ring

/-- The alternative vector sampled at the end of Algorithm 15.4 is also fixed. -/
theorem H15_eq15_6_A_mul_b (θ : ℝ) (i : Fin 4) :
    (∑ j : Fin 4, H15_eq15_6_A θ i j * lapackAltVec (by omega : 1 < 4) j) =
      lapackAltVec (by omega : 1 < 4) i := by
  fin_cases i <;>
    simp [Fin.sum_univ_four, H15_eq15_6_A, H15_eq15_6_P, H15_eq15_6_v,
      lapackAltVec, even_iff_two_dvd] <;>
    ring

/-- Equation (15.6), executable conclusion: the repository's bounded
    Algorithm 15.4 returns the estimate `1` on every member of the family. -/
theorem H15_eq15_6_lapackNormEstimator (θ : ℝ) :
    H15_Algorithm15_4_gamma (by omega : 0 < 4) (H15_eq15_6_A θ) = 1 := by
  have hstart : oneNormPowerMethod (by omega : 0 < 4) (H15_eq15_6_A θ) 0 =
      ⟨(fun _ => (1 : ℝ) / 4), 1⟩ := by
    have hvals :
        (fun i : Fin 4 => ∑ j : Fin 4, H15_eq15_6_A θ i j * ((1 : ℝ) / 4)) =
          (fun _ => (1 : ℝ) / 4) := by
      funext i
      exact H15_eq15_6_A_mul_uniform θ i
    have hgamma : oneNormVec
        (fun i : Fin 4 => ∑ j : Fin 4,
          H15_eq15_6_A θ i j * ((1 : ℝ) / 4)) = 1 := by
      rw [hvals]
      simp [oneNormVec, Fin.sum_univ_four]
    change (⟨(fun _ : Fin 4 => (1 : ℝ) / 4),
      oneNormVec (fun i : Fin 4 => ∑ j : Fin 4,
        H15_eq15_6_A θ i j * ((1 : ℝ) / 4))⟩ : OneNormState 4) = _
    rw [hgamma]
  have hstep : oneNormStep (by omega : 0 < 4) (H15_eq15_6_A θ)
      ⟨(fun _ => (1 : ℝ) / 4), 1⟩ =
      (⟨(fun _ => (1 : ℝ) / 4), 1⟩, true) := by
    simp only [oneNormStep]
    simp_rw [H15_eq15_6_A_mul_uniform]
    simp [signVec, infNormVec, H15_eq15_6_AT_mul_e, oneNormVec]
  have hpower : oneNormPowerMethod (by omega : 0 < 4) (H15_eq15_6_A θ) 5 =
      ⟨(fun _ => (1 : ℝ) / 4), 1⟩ := by
    have hall : ∀ fuel : ℕ,
        oneNormPowerMethod (by omega : 0 < 4) (H15_eq15_6_A θ) fuel =
          ⟨(fun _ => (1 : ℝ) / 4), 1⟩ := by
      intro fuel
      induction fuel with
      | zero => exact hstart
      | succ fuel ih =>
          simp only [oneNormPowerMethod]
          rw [ih, hstep]
          rfl
    exact hall 5
  unfold H15_Algorithm15_4_gamma lapackNormEstimator
  simp only [hpower]
  have hb : oneNormVec (lapackAltVec (by omega : 1 < 4)) = 6 := by
    have hthree : (3 : ℝ)⁻¹ * 3 = 1 := inv_mul_cancel₀ (by norm_num)
    have h0 : lapackAltVec (by omega : 1 < 4) (0 : Fin 4) = 1 := by
      norm_num [lapackAltVec, even_iff_two_dvd]
    have h1 : lapackAltVec (by omega : 1 < 4) (1 : Fin 4) = -(4 / 3 : ℝ) := by
      norm_num [lapackAltVec, even_iff_two_dvd] <;>
        simp only [div_eq_mul_inv] <;> nlinarith [hthree]
    have h2 : lapackAltVec (by omega : 1 < 4) (2 : Fin 4) = 5 / 3 := by
      norm_num [lapackAltVec, even_iff_two_dvd] <;>
        simp only [div_eq_mul_inv] <;> nlinarith [hthree]
    have h3 : lapackAltVec (by omega : 1 < 4) (3 : Fin 4) = -2 := by
      norm_num [lapackAltVec, even_iff_two_dvd] <;>
        simp only [div_eq_mul_inv] <;> nlinarith [hthree]
    simp only [oneNormVec, Fin.sum_univ_four, h0, h1, h2, h3, abs_neg]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 / 3),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 5 / 3)]
    ring
  have hAb : oneNormVec (fun i => ∑ j : Fin 4,
      H15_eq15_6_A θ i j * lapackAltVec (by omega : 1 < 4) j) = 6 := by
    simp_rw [H15_eq15_6_A_mul_b]
    exact hb
  simp [hAb, hb]

/-- The true one-norm grows linearly along the counterexample family.  Thus
    the estimate-to-norm ratio can be made arbitrarily small. -/
theorem H15_eq15_6_oneNorm_lower (θ : ℝ) (hθ : 0 ≤ θ) :
    1 + (121 / 103 : ℝ) * θ ≤ oneNorm (H15_eq15_6_A θ) := by
  have hcol := col_sum_le_oneNorm (H15_eq15_6_A θ) (1 : Fin 4)
  rw [Fin.sum_univ_four] at hcol
  simp [H15_eq15_6_A, H15_eq15_6_P, H15_eq15_6_v] at hcol
  have hmain : 0 ≤ 1 + θ * ((11 : ℝ) * 11 / 206) := by positivity
  have habsθ : |θ| = θ := abs_of_nonneg hθ
  rw [abs_of_nonneg hmain, habsθ] at hcol
  norm_num at hcol ⊢
  linarith

end Higham15
end NumStability
