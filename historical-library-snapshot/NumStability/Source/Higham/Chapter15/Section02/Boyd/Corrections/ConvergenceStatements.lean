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
import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Duality.ConvergenceStatements
import NumStability.Algorithms.NormEstimation.PNorm.Duality.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormPowerMethod

/-!
# Chapter15 Section02 Boyd Corrections ConvergenceStatements

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

/-- **Qualified rank-one convergence statement.**  Let `A = u vᵀ`, with
`u ≠ 0`, and suppose the initial vector is not annihilated by the row
factor (`vᵀx₀ ≠ 0`).  Then the first updated iterate already attains
`γ₁ = ‖A‖₂ = ‖u‖₂‖v‖₂`, and the following test succeeds.  Thus, with Higham's
iteration count, the concrete `p=2` algorithm converges on its second step.

The non-annihilation premise is essential for a total implementation of
`dualp(0)`; the counterexample below shows why the printed "whatever `x₀`"
sentence is not valid uniformly over the allowed choice at zero. -/
theorem rankOne_two_converges_second_step_of_pairing_ne_zero {n : ℕ}
    (hn : 0 < n) (u v x0 : Fin n → ℝ)
    (hu : u ≠ 0)
    (hpair : (∑ j : Fin n, v j * x0 j) ≠ 0) :
    let A : Fin n → Fin n → ℝ := fun i j => u i * v j
    let P := pNormPair_two hn A
    P.gammaSeq x0 1 = opNorm2 A ∧
      P.gammaSeq x0 1 = vecNorm2 u * vecNorm2 v ∧
      P.qN (P.zof (P.xseq x0 1)) ≤ P.pN (P.yof (P.xseq x0 1)) := by
  let A : Fin n → Fin n → ℝ := fun i j => u i * v j
  let P := pNormPair_two hn A
  let c : ℝ := ∑ j : Fin n, v j * x0 j
  let d : Fin n → ℝ := normalize2 hn (fun i => c * u i)
  let a : ℝ := ∑ i : Fin n, u i * d i
  have hy0 : P.yof x0 = fun i => c * u i := by
    funext i
    change (∑ j : Fin n, (u i * v j) * x0 j) = c * u i
    dsimp [c]
    calc
      (∑ j : Fin n, u i * v j * x0 j) =
          u i * (∑ j : Fin n, v j * x0 j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = (∑ j : Fin n, v j * x0 j) * u i := by ring
  have haabs : |a| = vecNorm2 u := by
    simpa [a, d] using abs_dot_normalize2_smul hn u c hpair
  have hupos : 0 < vecNorm2 u := vecNorm2_pos_of_ne u hu
  have hane : a ≠ 0 := by
    intro ha
    rw [ha, abs_zero] at haabs
    linarith
  have hz0 : P.zof x0 = fun j => a * v j := by
    funext j
    change (∑ i : Fin n, (u i * v j) * normalize2 hn (P.yof x0) i) = a * v j
    rw [hy0]
    dsimp [a, d]
    calc
      (∑ i : Fin n, u i * v j * normalize2 hn (fun i => c * u i) i) =
          v j * (∑ i : Fin n, u i * normalize2 hn (fun i => c * u i) i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (∑ i : Fin n, u i * normalize2 hn (fun i => c * u i) i) * v j := by
        ring
  have hx1 : P.xseq x0 1 = normalize2 hn (fun j => a * v j) := by
    change normalize2 hn (P.zof x0) = _
    rw [hz0]
  let b : ℝ := ∑ j : Fin n, v j * normalize2 hn (fun r => a * v r) j
  have hbabs : |b| = vecNorm2 v := by
    simpa [b] using abs_dot_normalize2_smul hn v a hane
  have hy1 : P.yof (P.xseq x0 1) = fun i => b * u i := by
    funext i
    change (∑ j : Fin n, (u i * v j) * P.xseq x0 1 j) = b * u i
    rw [hx1]
    dsimp [b]
    calc
      (∑ j : Fin n, u i * v j * normalize2 hn (fun j => a * v j) j) =
          u i * (∑ j : Fin n, v j * normalize2 hn (fun r => a * v r) j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
      _ = (∑ j : Fin n, v j * normalize2 hn (fun r => a * v r) j) * u i := by
        ring
  have hgamma : P.gammaSeq x0 1 = vecNorm2 u * vecNorm2 v := by
    change vecNorm2 (P.yof (P.xseq x0 1)) = _
    rw [hy1, vecNorm2_smul, hbabs]
    ring
  have hop : opNorm2 A = vecNorm2 u * vecNorm2 v :=
    opNorm2_rankOne_eq hn u v
  have hunit : P.pN (P.xseq x0 1) = 1 := by
    simpa [P] using P.dq_punit (P.zof x0)
  have hchain := P.lemma152b (P.xseq x0 1) hunit
  have htest : P.qN (P.zof (P.xseq x0 1)) ≤
      P.pN (P.yof (P.xseq x0 1)) := by
    calc
      P.qN (P.zof (P.xseq x0 1))
          ≤ P.pN (P.yof (P.xnext (P.xseq x0 1))) := hchain.2.1
      _ ≤ P.opP := hchain.2.2
      _ = P.pN (P.yof (P.xseq x0 1)) := by
        change opNorm2 A = P.gammaSeq x0 1
        rw [hop, hgamma]
  exact ⟨hgamma.trans hop.symm, hgamma, htest⟩

/-- Rank-one factors for the zero-start discrepancy in dimension two. -/
noncomputable def rankOneZeroStartFactor : Fin 2 → ℝ := basisVec (1 : Fin 2)

/-- The rank-one matrix `e₁e₁ᵀ` used to audit the printed "whatever `x₀`"
claim. -/
noncomputable def rankOneZeroStartMatrix : Fin 2 → Fin 2 → ℝ :=
  fun i j => rankOneZeroStartFactor i * rankOneZeroStartFactor j

/-- Initial vector `e₀`, annihilated by `e₁e₁ᵀ`. -/
noncomputable def rankOneZeroStartX : Fin 2 → ℝ := basisVec (0 : Fin 2)

lemma rankOneZeroStart_y_eq_zero :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).yof
      rankOneZeroStartX = 0 := by
  funext i
  fin_cases i <;>
    simp [PNormPair.yof, pNormPair_two, rankOneZeroStartMatrix,
      rankOneZeroStartFactor, rankOneZeroStartX, basisVec]

lemma rankOneZeroStart_z_eq_zero :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).zof
      rankOneZeroStartX = 0 := by
  funext j
  change (∑ i : Fin 2, rankOneZeroStartMatrix i j *
    normalize2 (by omega : 0 < 2)
      ((pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).yof
        rankOneZeroStartX) i) = 0
  rw [rankOneZeroStart_y_eq_zero]
  fin_cases j <;>
    simp [normalize2, e0Vec, rankOneZeroStartMatrix,
      rankOneZeroStartFactor, basisVec]

lemma rankOneZeroStart_xnext_fixed :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).xnext
      rankOneZeroStartX = rankOneZeroStartX := by
  change normalize2 (by omega : 0 < 2)
    ((pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).zof
      rankOneZeroStartX) = rankOneZeroStartX
  rw [rankOneZeroStart_z_eq_zero]
  funext i
  fin_cases i <;> simp [normalize2, e0Vec, rankOneZeroStartX, basisVec]

lemma rankOneZeroStart_xseq_fixed (k : ℕ) :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).xseq
      rankOneZeroStartX k = rankOneZeroStartX := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [PNormPair.xseq, ih]
      exact rankOneZeroStart_xnext_fixed

lemma rankOneZeroStart_gamma_eq_zero (k : ℕ) :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).gammaSeq
      rankOneZeroStartX k = 0 := by
  rw [PNormPair.gammaSeq, rankOneZeroStart_xseq_fixed]
  simp [PNormPair.yof, pNormPair_two, rankOneZeroStartMatrix,
    rankOneZeroStartFactor, rankOneZeroStartX, basisVec, vecNorm2, vecNorm2Sq]

lemma rankOneZeroStart_factor_norm_product :
    vecNorm2 rankOneZeroStartFactor * vecNorm2 rankOneZeroStartFactor = 1 := by
  norm_num [rankOneZeroStartFactor, basisVec, vecNorm2, vecNorm2Sq]

/-- **Source discrepancy, Higham p. 291.**  With the repository's valid
choice `dualp(0)=e₀`, the rank-one matrix `e₁e₁ᵀ` and start `x₀=e₀` remain
stuck at estimate zero.  Hence the unqualified printed claim that rank-one
matrices converge on the second step "whatever `x₀`" is false for the stated
set-valued dual convention. -/
theorem rankOne_second_step_whatever_x0_false :
    (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).gammaSeq
        rankOneZeroStartX 1 ≠
      vecNorm2 rankOneZeroStartFactor * vecNorm2 rankOneZeroStartFactor := by
  rw [rankOneZeroStart_gamma_eq_zero, rankOneZeroStart_factor_norm_product]
  norm_num

/-- Audit-grade package for the rank-one source discrepancy.  The concrete
start is in Algorithm 15.1's unit-sphere domain, the displayed factor is
nonzero (so its outer product is genuinely rank one), and the first updated
estimate is not the exact operator norm. -/
theorem rankOne_second_step_whatever_x0_unit_opNorm_counterexample :
    vecNorm2 rankOneZeroStartX = 1 ∧
      rankOneZeroStartFactor ≠ 0 ∧
      (pNormPair_two (by omega : 0 < 2) rankOneZeroStartMatrix).gammaSeq
          rankOneZeroStartX 1 ≠ opNorm2 rankOneZeroStartMatrix := by
  constructor
  · norm_num [rankOneZeroStartX, basisVec, vecNorm2, vecNorm2Sq]
  constructor
  · intro hzero
    have hcoord := congrFun hzero (1 : Fin 2)
    norm_num [rankOneZeroStartFactor, basisVec] at hcoord
  · have hop :
        opNorm2 rankOneZeroStartMatrix =
          vecNorm2 rankOneZeroStartFactor *
            vecNorm2 rankOneZeroStartFactor := by
      simpa [rankOneZeroStartMatrix] using
        (opNorm2_rankOne_eq (by omega : 0 < 2)
          rankOneZeroStartFactor rankOneZeroStartFactor)
    rw [hop]
    exact rankOne_second_step_whatever_x0_false

end Ch15
end NumStability
