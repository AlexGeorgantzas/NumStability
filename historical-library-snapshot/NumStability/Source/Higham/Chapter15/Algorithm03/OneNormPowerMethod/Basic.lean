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
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation
import NumStability.Analysis.MatrixAlgebra

/-!
# Chapter15 Algorithm03 OneNormPowerMethod Basic

Canonical destination for material split out of
`NumStability.Algorithms.Chapter15CondEst` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Higham15

open scoped BigOperators

/-- The final iterate `x` produced by the Chapter-15 1-norm power method
    (Higham §15.3, Algorithm 15.3), obtained by running the repository's
    `oneNormPowerMethod` for `fuel` iterations and reading off its iterate.

    This is exactly the vector at which the returned scalar estimate is the
    1-norm of `Ax` (see `H15_Algorithm15_3_gamma`). -/
noncomputable def H15_Algorithm15_3_x {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) : Fin n → ℝ :=
  (oneNormPowerMethod hn A fuel).x

/-- The scalar estimate γ returned by Algorithm 15.3 (Higham §15.3, p. 292):
    γ = ‖A x‖₁ for the final iterate `x`. -/
noncomputable def H15_Algorithm15_3_gamma {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) : ℝ :=
  oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j)

/-- **Exact-normalization invariant** for the iterates of Algorithm 15.3.

    Every iterate produced by `oneNormPowerMethod` has 1-norm exactly `1`:
    the start vector is `n⁻¹e` (Higham §15.3: `x = n⁻¹e`), and every subsequent
    iterate is a unit basis vector `eⱼ` (`x = eⱼ`), both of 1-norm `1`; the
    converged branch merely re-returns the previous iterate.  This upgrades the
    `≤ 1` invariant used by the existing lower-bound proof to an *equality*,
    which is what the printed `‖Ax‖₁ = γ‖x‖₁` relation needs. -/
theorem H15_Algorithm15_3_x_oneNorm_eq_one {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    oneNormVec (H15_Algorithm15_3_x hn A fuel) = 1 := by
  unfold H15_Algorithm15_3_x
  -- One step maps a unit-1-norm iterate to a unit-1-norm iterate (start `n⁻¹e`
  -- or a basis vertex `eⱼ`; the converged branch re-returns the input).
  have hstep_eq : ∀ st : OneNormState n, oneNormVec st.x = 1 →
      oneNormVec (oneNormStep hn A st).1.x = 1 := by
    intro st hst
    simp only [oneNormStep]
    split_ifs
    · exact hst
    · exact oneNormVec_basisVec _
  induction fuel with
  | zero =>
    simp only [oneNormPowerMethod]
    exact initial_vec_oneNorm hn
  | succ fuel ih =>
    simp only [oneNormPowerMethod]
    set prev := oneNormPowerMethod hn A fuel with hprev
    -- Rewrite the `let`-bindings into a plain `if` on the step's Bool flag.
    rw [show (let prev := oneNormPowerMethod hn A fuel;
              let x := oneNormStep hn A prev;
              if x.2 = true then prev else x.1) =
             if (oneNormStep hn A prev).2 = true then prev
             else (oneNormStep hn A prev).1 from rfl]
    split_ifs with hconv
    · -- converged: returns the previous iterate, 1-norm 1 by IH
      exact ih
    · -- not converged: returns the step output, which has 1-norm 1 by hstep_eq
      exact hstep_eq prev ih

/-- **Algorithm 15.3 — lower-bound guarantee** (Higham §15.3, p. 292):
      `γ ≤ ‖A‖₁`.

    Since the reported iterate `x` has `‖x‖₁ = 1`, submultiplicativity of the
    1-norm gives `γ = ‖Ax‖₁ ≤ ‖A‖₁·‖x‖₁ = ‖A‖₁`.  (Reuses
    `oneNormVec_matVec_le` from the existing module; no reproof of the norm
    algebra.) -/
theorem H15_Algorithm15_3_lower_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    H15_Algorithm15_3_gamma hn A fuel ≤ oneNorm A := by
  unfold H15_Algorithm15_3_gamma
  have hx := H15_Algorithm15_3_x_oneNorm_eq_one hn A fuel
  calc oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j)
      ≤ oneNorm A * oneNormVec (H15_Algorithm15_3_x hn A fuel) :=
        oneNormVec_matVec_le hn A _
    _ = oneNorm A * 1 := by rw [hx]
    _ = oneNorm A := mul_one _

/-- **Algorithm 15.3 — norm-equality guarantee** (Higham §15.3, p. 292):
      `‖Ax‖₁ = γ‖x‖₁`.

    By construction `γ = ‖Ax‖₁` and `‖x‖₁ = 1`, so `γ‖x‖₁ = γ = ‖Ax‖₁`.
    This is the equality the existing "Chapter-14" lower-bound lemmas do not
    state; it is discharged here for the genuine final iterate, no hypothesis
    added. -/
theorem H15_Algorithm15_3_norm_eq {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j) =
      H15_Algorithm15_3_gamma hn A fuel *
        oneNormVec (H15_Algorithm15_3_x hn A fuel) := by
  rw [H15_Algorithm15_3_x_oneNorm_eq_one hn A fuel, mul_one]
  rfl

/-- **Algorithm 15.3 — full printed guarantee** (Higham §15.3, Algorithm 15.3,
    p. 292), bundling both printed conclusions for the computed pair `(γ, x)`:

      `γ ≤ ‖A‖₁`   and   `‖Ax‖₁ = γ‖x‖₁`. -/
theorem H15_Algorithm15_3_spec {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    H15_Algorithm15_3_gamma hn A fuel ≤ oneNorm A ∧
    oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j) =
      H15_Algorithm15_3_gamma hn A fuel *
        oneNormVec (H15_Algorithm15_3_x hn A fuel) :=
  ⟨H15_Algorithm15_3_lower_bound hn A fuel,
   H15_Algorithm15_3_norm_eq hn A fuel⟩

/-- The scalar stored by the bounded implementation of Algorithm 15.3 is
    always the 1-norm of `A w` for some normalized iterate `w`.

    On a nonconverged step the state stores the norm computed at the previous
    iterate while replacing its `x` field by a basis vector.  Consequently the
    witness need not be the final stored `x`; this theorem records exactly the
    provenance needed by Algorithm 15.4 when it selects the power-method arm. -/
theorem H15_Algorithm15_3_stored_gamma_realized {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    ∃ w : Fin n → ℝ,
      oneNormVec w = 1 ∧
      oneNormVec (fun i => ∑ j : Fin n, A i j * w j) =
        (oneNormPowerMethod hn A fuel).γ := by
  induction fuel with
  | zero =>
    refine ⟨fun _ => (1 : ℝ) / n, initial_vec_oneNorm hn, ?_⟩
    rfl
  | succ fuel ih =>
    simp only [oneNormPowerMethod]
    set prev := oneNormPowerMethod hn A fuel with hprev
    rw [show (let prev := oneNormPowerMethod hn A fuel;
              let next := oneNormStep hn A prev;
              if next.2 = true then prev else next.1) =
             if (oneNormStep hn A prev).2 = true then prev
             else (oneNormStep hn A prev).1 from rfl]
    split_ifs with hconv
    · exact ih
    · refine ⟨prev.x, ?_, ?_⟩
      · simpa [prev, H15_Algorithm15_3_x] using
          H15_Algorithm15_3_x_oneNorm_eq_one hn A fuel
      · have hstep :
            (oneNormStep hn A prev).1.γ =
              oneNormVec (fun i => ∑ j : Fin n, A i j * prev.x j) := by
          simp only [oneNormStep]
          split_ifs <;> rfl
        exact hstep.symm

end Higham15
end NumStability
