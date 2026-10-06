import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Duality ConvergenceStatements

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15ConvergenceProse` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Set

open scoped Topology BigOperators

lemma normalize2_eq_self_of_unit {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : vecNorm2 x = 1) :
    normalize2 hn x = x := by
  have hxne : x ≠ 0 := by
    intro h
    subst x
    have hzero : vecNorm2 (0 : Fin n → ℝ) = 0 := by
      simpa using (vecNorm2_zero (n := n))
    rw [hzero] at hx
    norm_num at hx
  unfold normalize2
  rw [if_neg hxne]
  funext i
  simp [hx]

/-- Pairing a nonzero scalar multiple of `v` with its Euclidean normalized
dual has magnitude `‖v‖₂`.  This is the small algebraic fact behind the
rank-one two-step calculation. -/
lemma abs_dot_normalize2_smul {n : ℕ} (hn : 0 < n)
    (v : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    |∑ i : Fin n, v i * normalize2 hn (fun j => c * v j) i| = vecNorm2 v := by
  let w : Fin n → ℝ := fun j => c * v j
  let d : Fin n → ℝ := normalize2 hn w
  have hattain : (∑ i : Fin n, d i * w i) = vecNorm2 w := by
    simpa [d] using normalize2_attains hn w
  have hscale : vecNorm2 w = |c| * vecNorm2 v := by
    simpa [w] using vecNorm2_smul c v
  have hrel : c * (∑ i : Fin n, v i * d i) = vecNorm2 w := by
    calc
      c * (∑ i : Fin n, v i * d i) = ∑ i : Fin n, d i * w i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp [w]
        ring
      _ = vecNorm2 w := hattain
  have habs := congrArg abs hrel
  rw [abs_mul, abs_of_nonneg (vecNorm2_nonneg w), hscale] at habs
  have hcpos : 0 < |c| := abs_pos.mpr hc
  nlinarith

/-- The exact Euclidean operator norm of a real rank-one matrix `u vᵀ`. -/
theorem opNorm2_rankOne_eq {n : ℕ} (hn : 0 < n)
    (u v : Fin n → ℝ) :
    opNorm2 (fun i j => u i * v j) = vecNorm2 u * vecNorm2 v := by
  let A : Fin n → Fin n → ℝ := fun i j => u i * v j
  have haction (x : Fin n → ℝ) :
      matMulVec n A x = fun i => (∑ j : Fin n, v j * x j) * u i := by
    funext i
    simp only [matMulVec, A]
    calc
      (∑ j : Fin n, u i * v j * x j) =
          u i * (∑ j : Fin n, v j * x j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = (∑ j : Fin n, v j * x j) * u i := by ring
  apply le_antisymm
  · apply opNorm2_le_of_unit_vecNorm2_bound A
      (mul_nonneg (vecNorm2_nonneg u) (vecNorm2_nonneg v))
    intro x hx
    rw [haction x, vecNorm2_smul]
    have hdot := abs_vecInnerProduct_le_vecNorm2_mul v x
    rw [hx, mul_one] at hdot
    have hmul := mul_le_mul_of_nonneg_right hdot (vecNorm2_nonneg u)
    nlinarith
  · let x : Fin n → ℝ := normalize2 hn v
    have hx : vecNorm2 x = 1 := normalize2_unit hn v
    have hdot : (∑ j : Fin n, v j * x j) = vecNorm2 v := by
      simpa [x, mul_comm] using normalize2_attains hn v
    have hop := opNorm2Le_opNorm2 A x
    rw [haction x, hdot, vecNorm2_smul,
      abs_of_nonneg (vecNorm2_nonneg v), hx, mul_one] at hop
    simpa [A, mul_comm] using hop

end Ch15
end NumStability
