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
import NumStability.Algorithms.NormEstimation.PNorm.Duality.ConvergenceStatements
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Equation03.GradientQuotient.PNormPowerMethod
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormPowerMethod

/-!
# Chapter15 Equation03 GradientQuotient ConvergenceStatements

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

namespace PNormPair

variable {n : ℕ} (P : PNormPair n)

end PNormPair

/-- A unit fixed point of the Euclidean power update satisfies the zero
gradient equation for Higham's quotient (15.3). -/
theorem eq15_3_gradient_two_eq_zero_of_fixed {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (hx : vecNorm2 x = 1)
    (hfixed : (pNormPair_two hn A).xnext x = x) :
    eq15_3_gradient_two hn A x = 0 := by
  let P := pNormPair_two hn A
  let z := P.zof x
  let γ := vecNorm2 (P.yof x)
  have hfixed' : normalize2 hn z = x := by
    change normalize2 hn (P.zof x) = x at hfixed
    simpa [z] using hfixed
  have hzgamma : vecNorm2 z = γ := by
    calc
      vecNorm2 z = ∑ i : Fin n, normalize2 hn z i * z i :=
        (normalize2_attains hn z).symm
      _ = ∑ i : Fin n, z i * x i := by
        rw [← hfixed']
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = γ := by
        simpa [P, z, γ] using P.lemma152a x
  have hnormx : normalize2 hn x = x := normalize2_eq_self_of_unit hn x hx
  have hkkt : z = fun i => γ * normalize2 hn x i := by
    by_cases hz : z = 0
    · have hzero : vecNorm2 (0 : Fin n → ℝ) = 0 := by
        simpa using (vecNorm2_zero (n := n))
      have hγ : γ = 0 := by
        rw [hz, hzero] at hzgamma
        exact hzgamma.symm
      rw [hz, hγ]
      funext i
      simp
    · have hznorm : vecNorm2 z ≠ 0 := ne_of_gt (vecNorm2_pos_of_ne z hz)
      have hrecover : z = fun i => vecNorm2 z * normalize2 hn z i := by
        funext i
        unfold normalize2
        rw [if_neg hz]
        field_simp [hznorm]
      rw [hrecover, hzgamma, hfixed', hnormx]
  funext i
  change P.zof x i / vecNorm2 x -
      (vecNorm2 (P.yof x) / vecNorm2 x ^ 2) * normalize2 hn x i = 0
  rw [hx]
  simp only [div_one, one_pow]
  change z i - γ * normalize2 hn x i = 0
  rw [hkkt]
  ring

end Ch15
end NumStability
