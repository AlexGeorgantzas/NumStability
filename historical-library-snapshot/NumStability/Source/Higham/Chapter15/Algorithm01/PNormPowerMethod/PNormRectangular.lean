import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# Chapter15 Algorithm01 PNormPowerMethod PNormRectangular

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethodRect` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

open Ch15

namespace RectPNormPair

variable {m n : ℕ} (P : RectPNormPair m n)

/-- Relational terminal of Algorithm 15.1: the trace stops at iteration `k`
and returns the estimate attached to that iterate.  This represents the source
`repeat ... quit` without claiming termination for general `p`. -/
def AlgorithmResult (x0 : Fin n → ℝ) (k : ℕ) (γ : ℝ)
    (x : Fin n → ℝ) : Prop :=
  x = P.xseq x0 k ∧ P.StopsAt x ∧ γ = P.pOut (P.yof x)

/-- Literal rectangular Algorithm 15.1 output specification. -/
theorem higham15_algorithm15_1_rectangular_result
    (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1)
    {k : ℕ} {γ : ℝ} {x : Fin n → ℝ}
    (hresult : P.AlgorithmResult x0 k γ x) :
    γ ≤ P.opP ∧ P.pOut (P.yof x) = γ * P.pIn x := by
  rcases hresult with ⟨rfl, _hstop, rfl⟩
  have hx := P.xseq_punit x0 hx0 k
  refine ⟨P.gammaSeq_le_opP x0 hx0 k, ?_⟩
  rw [hx, mul_one]

/-- The Boolean loop body is the source stopping test and preserves unit input
norm in either branch. -/
theorem higham15_algorithm15_1_rectangular_step
    (st : State (n := n)) (hx : P.pIn st.x = 1) :
    ((P.powerStep st).2 = true ↔ P.StopsAt st.x) ∧
      P.pIn (P.powerStep st).1.x = 1 ∧
      (P.powerStep st).1.γ ≤ P.opP := by
  have hbound : P.pOut (P.yof st.x) ≤ P.opP := by
    have h := P.op_bound st.x
    rw [hx, mul_one] at h
    exact h
  unfold powerStep StopsAt
  dsimp only
  split_ifs with hstop
  · exact ⟨Iff.intro (fun _ => hstop) (fun _ => rfl), hx, hbound⟩
  · refine ⟨Iff.intro (fun h => h.elim) (fun h => hstop h), ?_, hbound⟩
    · exact P.dqIn_punit _

end RectPNormPair
end NumStability
