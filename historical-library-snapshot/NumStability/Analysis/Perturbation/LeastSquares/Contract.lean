import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

/-!
# Contract

Canonical reusable module extracted without change from Higham20Theorem20_7, Higham20Theorem20_7QdR.
-/

namespace Theorem20_7

noncomputable def rowScaleCounterA : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, _ => 0
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 1 / 2
theorem rowScaleCounter_pivot0 :
    householderActiveMaxPivotColumn (0 : Fin 2) (0 : Fin 2)
      rowScaleCounterA = 0 := by
  let q := householderActiveMaxPivotColumn (0 : Fin 2) (0 : Fin 2)
    rowScaleCounterA
  have hmax := householderActiveMaxPivotColumn_pivot_max
    (0 : Fin 2) (0 : Fin 2) rowScaleCounterA (0 : Fin 2) (by norm_num)
  change q = 0
  have hqv : q.val = 0 := by
    by_contra hne
    have hq1 : q.val = 1 := by omega
    have hqeq : q = (1 : Fin 2) := Fin.ext hq1
    change householderTrailingColumnNorm2Sq (0 : Fin 2) rowScaleCounterA 0 ≤
      householderTrailingColumnNorm2Sq (0 : Fin 2) rowScaleCounterA q at hmax
    rw [hqeq] at hmax
    norm_num [householderTrailingColumnNorm2Sq,
      householderTrailingNorm2Sq, rowScaleCounterA,
      householderTrailingPart, vecNorm2Sq] at hmax
  exact Fin.ext hqv
/-- Literal source row maximum for the two-column counterexample. -/
noncomputable def rowScaleCounterRowMax (i : Fin 2) : ℝ :=
  max |rowScaleCounterA i (0 : Fin 2)| |rowScaleCounterA i (1 : Fin 2)|
theorem rowScaleCounter_rowMax0 :
    rowScaleCounterRowMax (0 : Fin 2) = 0 := by
  simp [rowScaleCounterRowMax, rowScaleCounterA]
/-- Scaled form of the Cox--Higham multiplier estimate.

The usual lemma has `‖w‖₂ ≤ |sigma|` and conclusion `≤ sqrt 2`.  A triangular
correction column has instead `‖w‖₂ ≤ eta |sigma|`; keeping the scale outside
gives the form needed below. -/
theorem householder_multiplier_le_sqrt_two_mul {m : ℕ}
    (v w : Fin m → ℝ) (sigma beta eta : ℝ)
    (hsigma : 0 < |sigma|) (heta : 0 ≤ eta)
    (hvnorm : Real.sqrt 2 * |sigma| ≤ vecNorm2 v)
    (hw : vecNorm2 w ≤ eta * |sigma|)
    (hbeta : beta * vecNorm2 v ^ 2 = 2) :
    |beta * (∑ i : Fin m, v i * w i)| ≤ Real.sqrt 2 * eta := by
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hvpos : 0 < vecNorm2 v := by
    have : 0 < Real.sqrt 2 * |sigma| := mul_pos hsqrt_pos hsigma
    linarith
  have hvsq_pos : 0 < vecNorm2 v ^ 2 := by positivity
  have hbeta_val : beta = 2 / vecNorm2 v ^ 2 := by
    apply (eq_div_iff (ne_of_gt hvsq_pos)).2
    simpa [mul_comm] using hbeta
  have hbeta_nonneg : 0 ≤ beta := by
    rw [hbeta_val]
    positivity
  have hcs : |∑ i : Fin m, v i * w i| ≤ vecNorm2 v * vecNorm2 w :=
    abs_vecInnerProduct_le_vecNorm2_mul v w
  have hstep :
      |beta * (∑ i : Fin m, v i * w i)| ≤
        beta * (vecNorm2 v * vecNorm2 w) := by
    rw [abs_mul, abs_of_nonneg hbeta_nonneg]
    exact mul_le_mul_of_nonneg_left hcs hbeta_nonneg
  have heq : beta * (vecNorm2 v * vecNorm2 w) =
      2 * vecNorm2 w / vecNorm2 v := by
    rw [hbeta_val]
    field_simp [ne_of_gt hvpos]
  have hsqrt_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hkey : 2 * vecNorm2 w ≤
      (Real.sqrt 2 * eta) * vecNorm2 v := by
    have h1 :
        (Real.sqrt 2 * eta) * (Real.sqrt 2 * |sigma|) ≤
          (Real.sqrt 2 * eta) * vecNorm2 v :=
      mul_le_mul_of_nonneg_left hvnorm
        (mul_nonneg (Real.sqrt_nonneg _) heta)
    have h2 :
        (Real.sqrt 2 * eta) * (Real.sqrt 2 * |sigma|) =
          2 * (eta * |sigma|) := by
      rw [show (Real.sqrt 2 * eta) * (Real.sqrt 2 * |sigma|) =
          (Real.sqrt 2 * Real.sqrt 2) * (eta * |sigma|) by ring,
        hsqrt_sq]
    have h3 : 2 * vecNorm2 w ≤ 2 * (eta * |sigma|) := by linarith
    linarith
  have hfrac : 2 * vecNorm2 w / vecNorm2 v ≤ Real.sqrt 2 * eta := by
    rw [div_le_iff₀ hvpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hkey
  exact hstep.trans (heq ▸ hfrac)

end Theorem20_7

end NumStability
