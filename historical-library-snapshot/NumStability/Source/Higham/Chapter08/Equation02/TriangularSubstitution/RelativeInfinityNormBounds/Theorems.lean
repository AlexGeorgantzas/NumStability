-- NumStability/Source/Higham/Chapter08/Equation02/TriangularSubstitution/RelativeInfinityNormBounds/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Split component of a mixed/multi-destination owner.
-- Historical owner: `NumStability.Algorithms.HighamChapter8`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Interval.Finset.Fin
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.Triangular
import NumStability.Algorithms.MMatrix
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.ArbitraryOrder
import NumStability.Source.Higham.Chapter08.Equation15.GlobalEnvelopeCounterexample.All
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ForwardErrorKernels
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem05
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem09Exact
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem04
import NumStability.Source.Higham.Chapter08.Equation14.FanInExecutor.Executor
import NumStability.Source.Higham.Chapter08.Lemma08.CorrectedCondition.RowDominance
import NumStability.Source.Higham.Chapter08.Lemma08.Entrywise.Basic
import NumStability.Source.Higham.Chapter08.Problem01.NoGuardSubstitution.Aliases
import NumStability.Source.Higham.Chapter08.Problem02.ComparisonMatrixWitness.RatioWitness
import NumStability.Source.Higham.Chapter08.Problem03.UnitTriangularSubstitution.Bound
import NumStability.Source.Higham.Chapter08.Problem04.MMatrixSubstitution.Comparison
import NumStability.Source.Higham.Chapter08.Problem05.InverseNormBounds.ZInverse
import NumStability.Source.Higham.Chapter08.Problem06.ComparisonInverseBounds.VectorBounds
import NumStability.Source.Higham.Chapter08.Problem07.DiagonalScaling.Bounds
import NumStability.Source.Higham.Chapter08.Problem08.SingleEntrySingularity.RankOne
import NumStability.Source.Higham.Chapter08.Problem09.KahanSingularValues.KahanMatrix
import NumStability.Source.Higham.Chapter08.Section01.BackwardErrorAnalysis.Core
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBounds
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBoundsPrelude
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.NormBounds
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsLower
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsPrelude
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsUpper
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.AllOrdersEnvelope
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.Factors
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.ResidualForwardBounds

/-!
# Theorems

Relocated from `NumStability.Algorithms.HighamChapter8` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


-- Algorithms/HighamChapter8.lean
--
-- Source-facing entry points for Higham Chapter 8, "Triangular Systems".
-- The detailed proofs remain in the focused triangular-system modules; this
-- file provides stable chapter labels and light wrappers around those results.















namespace NumStability

open scoped BigOperators

/-! ## §8.1 Backward Error Analysis -/

















































































































/-! ## §8.2 Forward Error Analysis -/

/-- Internal `(8.2)` transfer: a componentwise backward-error certificate with
no right-hand-side perturbation yields the Chapter 7 relative `∞`-norm forward
bound with `cond(T, x)` and `cond(T)`. -/
private theorem higham8_relative_infNorm_bound_of_componentwise_backward_error
    (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x x_hat b : Fin n → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hback : ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i))
    (hLeft : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hεcond : ε * condSkeel n hn A A_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      ε / (1 - ε * condSkeel n hn A A_inv) *
        ch7SkeelCondAtSolutionInf n hn A A_inv x := by
  rcases hback with ⟨ΔA, hΔA, hPerturbed⟩
  have hM :
      ∀ i, ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|) ≤
        condSkeel n hn A A_inv := by
    intro i
    unfold condSkeel
    exact
      Finset.le_sup'
        (fun i' => ∑ j : Fin n, |A_inv i' j| * ∑ k : Fin n, |A j k|)
        (Finset.mem_univ i)
  have hmain :=
    componentwise_forward_error_exact_relative_infNorm n hn A A_inv x x_hat b
      ΔA (fun _ => 0) (fun i j => |A i j|) (fun _ => 0) ε hε hΔA
      (by intro i; simp)
      (by intro i j; exact abs_nonneg _)
      (by intro i; simp)
      hLeft hAx (by simpa using hPerturbed)
      (condSkeel n hn A A_inv) hM hεcond hx
  simpa [ch7SkeelCondAtSolutionInf] using hmain


/-- **Equation (8.2)** for the repository back-substitution routine:
relative `∞`-norm forward error bounded by
`cond(T,x) γ_n / (1 - cond(T) γ_n)`. -/
theorem higham8_2_backSub_relative_infNorm_bound (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hU_diag : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hInv : IsInverse n U U_inv)
    (hUx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hγ : gammaValid fp n)
    (hγcond : gamma fp n * condSkeel n hn U U_inv < 1)
    (hx : 0 < infNormVec x) :
    let x_hat := fl_backSub fp n U b
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      gamma fp n / (1 - gamma fp n * condSkeel n hn U U_inv) *
        ch7SkeelCondAtSolutionInf n hn U U_inv x := by
  dsimp
  apply higham8_relative_infNorm_bound_of_componentwise_backward_error
    n hn U U_inv x (fl_backSub fp n U b) b
  · exact gamma_nonneg fp hγ
  · rcases higham8_5_backSub_backward_error fp n U b hU_diag hUT hγ with
      ⟨ΔU, hΔU, hPerturbed⟩
    refine ⟨ΔU, ?_, ?_⟩
    · intro i j
      simpa using hΔU i j
    · simpa using hPerturbed
  · exact hInv.1
  · exact hUx
  · exact hγcond
  · exact hx


/-- **Equation (8.2)** for the repository forward-substitution routine:
relative `∞`-norm forward error bounded by
`cond(T,x) γ_n / (1 - cond(T) γ_n)`. -/
theorem higham8_2_forwardSub_relative_infNorm_bound (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (L L_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ)
    (hL_diag : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsInverse n L L_inv)
    (hLx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hγ : gammaValid fp n)
    (hγcond : gamma fp n * condSkeel n hn L L_inv < 1)
    (hx : 0 < infNormVec x) :
    let x_hat := fl_forwardSub fp n L b
    infNormVec (fun i => x i - x_hat i) / infNormVec x ≤
      gamma fp n / (1 - gamma fp n * condSkeel n hn L L_inv) *
        ch7SkeelCondAtSolutionInf n hn L L_inv x := by
  dsimp
  apply higham8_relative_infNorm_bound_of_componentwise_backward_error
    n hn L L_inv x (fl_forwardSub fp n L b) b
  · exact gamma_nonneg fp hγ
  · rcases higham8_5_forwardSub_backward_error fp n L b hL_diag hLT hγ with
      ⟨ΔL, hΔL, hPerturbed⟩
    refine ⟨ΔL, ?_, ?_⟩
    · intro i j
      simpa using hΔL i j
    · simpa using hPerturbed
  · exact hInv.1
  · exact hLx
  · exact hγcond
  · exact hx


/-- **Equation (8.2)** for upper-triangular substitution with arbitrary row
evaluation orders. -/
theorem higham8_2_backSub_anyOrder_relative_infNorm_bound (fp : FPModel)
    (n : ℕ) (hn : 0 < n)
    (U U_inv : Fin n → Fin n → ℝ)
    (x b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree ((n - i.val - 1) + 1))
    (hU_diag : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hInv : IsInverse n U U_inv)
    (hUx : ∀ i, ∑ j : Fin n, U i j * x j = b i)
    (hγ : gammaValid fp n)
    (hrow : BackSubAnyOrderSpec fp n U b xhat rowTree)
    (hγcond : gamma fp n * condSkeel n hn U U_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - xhat i) / infNormVec x ≤
      gamma fp n / (1 - gamma fp n * condSkeel n hn U U_inv) *
        ch7SkeelCondAtSolutionInf n hn U U_inv x := by
  apply higham8_relative_infNorm_bound_of_componentwise_backward_error
    n hn U U_inv x xhat b
  · exact gamma_nonneg fp hγ
  · rcases higham8_5_backSub_anyOrder_backward_error fp n U b xhat rowTree
      hU_diag hUT hγ hrow with
      ⟨ΔU, hΔU, hPerturbed⟩
    refine ⟨ΔU, ?_, ?_⟩
    · intro i j
      simpa using hΔU i j
    · simpa using hPerturbed
  · exact hInv.1
  · exact hUx
  · exact hγcond
  · exact hx


/-- **Equation (8.2)** for lower-triangular substitution with arbitrary row
evaluation orders. -/
theorem higham8_2_forwardSub_anyOrder_relative_infNorm_bound (fp : FPModel)
    (n : ℕ) (hn : 0 < n)
    (L L_inv : Fin n → Fin n → ℝ)
    (x b xhat : Fin n → ℝ)
    (rowTree : (i : Fin n) → SumTree (i.val + 1))
    (hL_diag : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hInv : IsInverse n L L_inv)
    (hLx : ∀ i, ∑ j : Fin n, L i j * x j = b i)
    (hγ : gammaValid fp n)
    (hrow : ForwardSubAnyOrderSpec fp n L b xhat rowTree)
    (hγcond : gamma fp n * condSkeel n hn L L_inv < 1)
    (hx : 0 < infNormVec x) :
    infNormVec (fun i => x i - xhat i) / infNormVec x ≤
      gamma fp n / (1 - gamma fp n * condSkeel n hn L L_inv) *
        ch7SkeelCondAtSolutionInf n hn L L_inv x := by
  apply higham8_relative_infNorm_bound_of_componentwise_backward_error
    n hn L L_inv x xhat b
  · exact gamma_nonneg fp hγ
  · rcases higham8_5_forwardSub_anyOrder_backward_error fp n L b xhat rowTree
      hL_diag hLT hγ hrow with
      ⟨ΔL, hΔL, hPerturbed⟩
    refine ⟨ΔL, ?_, ?_⟩
    · intro i j
      simpa using hΔL i j
    · simpa using hPerturbed
  · exact hInv.1
  · exact hLx
  · exact hγcond
  · exact hx

end NumStability
