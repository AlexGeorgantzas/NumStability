-- NumStability/Source/Higham/Chapter01/Section12/InstabilityWithoutCancellation/PivotingExample.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Analysis.InstabilityWithoutCancellation`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter01.FloatingPointArithmetic.InstabilityWithoutCancellation

/-!
# PivotingExample

Relocated from `NumStability.Analysis.InstabilityWithoutCancellation` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Instability without cancellation (compatibility module)

Compatibility facade retained so existing imports of
`NumStability.Analysis.InstabilityWithoutCancellation`
keep resolving. Most declarations moved unchanged to the canonical Higham
Chapter 1 module imported above. Six declarations remain here because their
dependency on a shared module requires the original module boundary. The
module's original imports are re-stated so consumers reaching identifiers
transitively through this path retain the same surface.
-/

namespace NumStability

open scoped BigOperators

/-- The partial-pivoting row interchange is a permutation of the two rows. -/
theorem noPivotPartialPivotSwap_bijective :
    IsPermutation 2 noPivotPartialPivotSwap := by
  constructor
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp [noPivotPartialPivotSwap] at h ⊢
  · intro b
    fin_cases b
    · exact ⟨1, by simp [noPivotPartialPivotSwap]⟩
    · exact ⟨0, by simp [noPivotPartialPivotSwap]⟩
/-- After swapping rows, Higham §1.12.1's matrix has the exact pivoted
factorization `P*A = L*U`. -/
theorem noPivotPartialPivotLUFactSpec (ε : ℝ) :
    PermutedLUFactSpec 2 (noPivotExampleA ε)
      (noPivotPartialPivotL ε) (noPivotPartialPivotU ε)
      noPivotPartialPivotSwap := by
  refine ⟨noPivotPartialPivotSwap_bijective, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [noPivotPartialPivotL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [noPivotPartialPivotL] at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [noPivotPartialPivotU] at hij ⊢
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [noPivotPartialPivotL, noPivotPartialPivotU, noPivotExampleA,
        noPivotPartialPivotSwap]
/-- The exact partial-pivoting branch for Higham §1.12.1 also satisfies the
pivoted LU backward-error surface with zero perturbation.  This is the
backward-error certificate for the exact pivoted factors; a primitive rounded
operation trace remains a separate obligation. -/
theorem noPivotPartialPivotLUBackwardError_zero (ε : ℝ) :
    PermutedLUBackwardError 2 (noPivotExampleA ε)
      (noPivotPartialPivotL ε) (noPivotPartialPivotU ε)
      noPivotPartialPivotSwap 0 := by
  have hspec := noPivotPartialPivotLUFactSpec ε
  refine
    { perm := hspec.perm
      L_diag := hspec.L_diag
      L_upper_zero := hspec.L_upper_zero
      U_lower_zero := hspec.U_lower_zero
      backward_bound := ?_ }
  intro i j
  have hprod := hspec.product_eq i j
  rw [hprod]
  simp
/-- General rounded-pivot bridge for Higham §1.12.1.  If the pivoted primitive
trace has rounded the final update to `U_22 = -1`, then for every `ε >= 0`
the resulting rounded pivoted factors satisfy the componentwise pivoted
LU backward-error certificate with radius `ε`. -/
theorem noPivotPartialPivotRoundedLUBackwardError {ε : ℝ}
    (hεnonneg : 0 ≤ ε) :
    PermutedLUBackwardError 2 (noPivotExampleA ε)
      (noPivotPartialPivotL ε) noPivotPartialPivotRoundedU
      noPivotPartialPivotSwap ε := by
  refine
    { perm := noPivotPartialPivotSwap_bijective
      L_diag := ?_
      L_upper_zero := ?_
      U_lower_zero := ?_
      backward_bound := ?_ }
  · intro i
    fin_cases i <;> simp [noPivotPartialPivotL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [noPivotPartialPivotL] at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [noPivotPartialPivotRoundedU] at hij ⊢
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [noPivotExampleA, noPivotPartialPivotL, noPivotPartialPivotRoundedU,
        noPivotPartialPivotSwap, Fin.sum_univ_two]
    all_goals
      first
      | exact hεnonneg
      | exact mul_nonneg hεnonneg (abs_nonneg ε)
      | rw [abs_of_nonneg hεnonneg]
        nlinarith [hεnonneg]
/-- The abstract primitive pivoted trace inherits the same backward-error
certificate once its three primitive rounded-operation facts are supplied. -/
theorem noPivotPartialPivotPrimitiveRoundedLUBackwardError_of_rounds
    (fp : FPModel) {ε : ℝ} (hεnonneg : 0 ≤ ε)
    (hdiv : fp.fl_div ε 1 = ε)
    (hmul : fp.fl_mul ε 1 = ε)
    (hsub : fp.fl_sub (-1) ε = -1) :
    PermutedLUBackwardError 2 (noPivotExampleA ε)
      (noPivotPartialPivotL ε)
      (noPivotPartialPivotPrimitiveRoundedU fp ε)
      noPivotPartialPivotSwap ε := by
  rw [noPivotPartialPivotPrimitiveRoundedU_eq_roundedU_of_rounds fp hdiv hmul hsub]
  exact noPivotPartialPivotRoundedLUBackwardError hεnonneg
/-- The actual concrete IEEE-single pivoted factors produced by the primitive
rounded trace for `ε = 2^{-24}` satisfy the pivoted LU backward-error surface
with componentwise radius `ε`.  Unlike the exact pivoted factors, these rounded
factors use `U_22 = -1`, because `fl((-1)-ε) = -1`. -/
theorem noPivotIeeeSinglePartialPivotRoundedLUBackwardError :
    PermutedLUBackwardError 2
      (noPivotExampleA noPivotIeeeSingleSmallEpsilon)
      (noPivotPartialPivotL noPivotIeeeSingleSmallEpsilon)
      noPivotPartialPivotIeeeSingleRoundedU
      noPivotPartialPivotSwap
      noPivotIeeeSingleSmallEpsilon := by
  refine
    { perm := noPivotPartialPivotSwap_bijective
      L_diag := ?_
      L_upper_zero := ?_
      U_lower_zero := ?_
      backward_bound := ?_ }
  · intro i
    fin_cases i <;> simp [noPivotPartialPivotL]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [noPivotPartialPivotL] at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [noPivotPartialPivotIeeeSingleRoundedU] at hij ⊢
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [noPivotExampleA, noPivotPartialPivotL,
        noPivotPartialPivotIeeeSingleRoundedU, noPivotPartialPivotSwap,
        noPivotIeeeSingleSmallEpsilon]
    all_goals
      exact (by norm_num : |(0 : ℝ)| ≤ (1 : ℝ) / 16777216)

end NumStability
