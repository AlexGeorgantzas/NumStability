import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Algorithms.NormEstimation.OneNorm.LAPACK.Basic
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation
import NumStability.Analysis.MatrixAlgebra

/-!
# CondEstimation (reusable retained core)

This source-neutral condition-estimation core remains canonical in place. Most
declarations moved unchanged to narrower reusable modules imported above;
existing imports of `NumStability.Algorithms.CondEstimation` keep resolving.

The declarations still defined below are private declarations and their users.
Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. All imports and retained declarations are reusable;
book-specific correspondence lives under `NumStability.Source.Higham`.
-/

namespace NumStability

open scoped BigOperators

/-- γ from oneNormStep is always oneNormVec of A·x, regardless of convergence. -/
private lemma oneNormStep_gamma_eq {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (st : OneNormState n) :
    (oneNormStep hn A st).1.γ =
    oneNormVec (fun i => ∑ j : Fin n, A i j * st.x j) := by
  simp [oneNormStep]
  split_ifs <;> rfl

private lemma oneNormStep_gamma_le {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (st : OneNormState n)
    (hx : oneNormVec st.x ≤ 1) :
    (oneNormStep hn A st).1.γ ≤ oneNorm A := by
  rw [oneNormStep_gamma_eq hn A st]
  calc oneNormVec _ ≤ oneNorm A * oneNormVec st.x :=
        oneNormVec_matVec_le hn A st.x
    _ ≤ oneNorm A * 1 := mul_le_mul_of_nonneg_left hx (oneNorm_nonneg A)
    _ = oneNorm A := mul_one _

/-- oneNormStep output x satisfies ‖x‖₁ ≤ 1. -/
private lemma oneNormStep_x_le {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (st : OneNormState n)
    (hx : oneNormVec st.x ≤ 1) :
    oneNormVec (oneNormStep hn A st).1.x ≤ 1 := by
  simp only [oneNormStep]
  split_ifs
  · exact hx
  · exact le_of_eq (oneNormVec_basisVec _)

/-- The algorithm maintains ‖x‖₁ ≤ 1 and γ ≤ ‖A‖₁ as joint invariant. -/
private lemma oneNormPowerMethod_invariant {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    oneNormVec (oneNormPowerMethod hn A fuel).x ≤ 1 ∧
    (oneNormPowerMethod hn A fuel).γ ≤ oneNorm A := by
  induction fuel with
  | zero =>
    constructor
    · simp only [oneNormPowerMethod]
      exact le_of_eq (initial_vec_oneNorm hn)
    · simp only [oneNormPowerMethod]
      have h1 := oneNormVec_matVec_le hn A (fun _ => (1 : ℝ) / ↑n)
      rw [initial_vec_oneNorm hn, mul_one] at h1
      exact h1
  | succ fuel ih =>
    simp only [oneNormPowerMethod]
    have hprev_x := ih.1
    have hprev_γ := ih.2
    -- Result is: if (oneNormStep ...).2 then prev else (oneNormStep ...).1
    -- We need to handle both cases
    set prev := oneNormPowerMethod hn A fuel with hprev_def
    set step := oneNormStep hn A prev with hstep_def
    have hstep_γ := oneNormStep_gamma_le hn A prev hprev_x
    have hstep_x := oneNormStep_x_le hn A prev hprev_x
    rw [show (let prev := oneNormPowerMethod hn A fuel;
             let x := oneNormStep hn A prev;
             if x.2 = true then prev else x.1) =
            if step.2 = true then prev else step.1 from rfl]
    split_ifs
    · exact ⟨hprev_x, hprev_γ⟩
    · exact ⟨hstep_x, hstep_γ⟩

/-- **Lower bound guarantee for Algorithm 14.3** (Higham §14.3).

    At each iteration, γ = ‖Ax‖₁ for some x with ‖x‖₁ ≤ 1,
    so γ ≤ ‖A‖₁ · ‖x‖₁ ≤ ‖A‖₁. -/
theorem oneNormPowerMethod_lower_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    (oneNormPowerMethod hn A fuel).γ ≤ oneNorm A :=
  (oneNormPowerMethod_invariant hn A fuel).2

/-- **Lower bound for LAPACK estimator** (Algorithm 14.4).

    The power method component satisfies γ ≤ ‖A‖₁ by
    `oneNormPowerMethod_lower_bound`. The alternating vector component
    satisfies ‖Ab‖₁/‖b‖₁ ≤ ‖A‖₁ by submultiplicativity.
    The max of two lower bounds is also a lower bound. -/
theorem lapackNormEstimator_lower_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    lapackNormEstimator hn A ≤ oneNorm A := by
  unfold lapackNormEstimator
  split_ifs with h1n
  · apply max_le
    · exact oneNormPowerMethod_lower_bound hn A 5
    · -- ‖Ab‖₁ / ‖b‖₁ ≤ ‖A‖₁
      by_cases hb : oneNormVec (lapackAltVec h1n) = 0
      · simp [hb]; exact oneNorm_nonneg A
      · have hbpos : 0 < oneNormVec (lapackAltVec h1n) :=
          lt_of_le_of_ne (oneNormVec_nonneg _) (Ne.symm hb)
        rw [div_le_iff₀ hbpos]
        exact oneNormVec_matVec_le hn A _
  · exact oneNormPowerMethod_lower_bound hn A 5

end NumStability
