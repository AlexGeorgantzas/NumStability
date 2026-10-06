import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11

/-!
# Chapter10 Theorem08 ComponentwisePerturbation Resolvent

Canonical destination for material split out of
`NumStability.Algorithms.Ch10Theorem108Componentwise` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

noncomputable section

namespace NumStability

/-- The normalized perturbation matrix printed in Theorem 10.8:
`Gtilde = Rhat⁻ᵀ DeltaA Rhat⁻¹`. -/
noncomputable def higham10_8_Gtilde {n : ℕ}
    (RhatInv DeltaA : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  rectMatMul (finiteTranspose RhatInv) (rectMatMul DeltaA RhatInv)

/-- The matrix appearing before `|Rhat|` in the printed componentwise bound. -/
noncomputable def higham10_8_componentwiseEnvelope {n : ℕ}
    (Gtilde : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  higham9_15_triuPart
    (rectMatMul (absMatrix n Gtilde)
      (nonsingInv n (matSub_id n (absMatrix n Gtilde))))

/-- Congruence by an arbitrary real matrix preserves symmetry. -/
theorem higham10_8_Gtilde_symmetric {n : ℕ}
    (RhatInv DeltaA : Fin n → Fin n → ℝ)
    (hDeltaSym : IsSymmetricFiniteMatrix DeltaA) :
    IsSymmetricFiniteMatrix (higham10_8_Gtilde RhatInv DeltaA) := by
  intro i j
  unfold higham10_8_Gtilde rectMatMul finiteTranspose
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hDeltaSym l k]
  ring

end NumStability

end
