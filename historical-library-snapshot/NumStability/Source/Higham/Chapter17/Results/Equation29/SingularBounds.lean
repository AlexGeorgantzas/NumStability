import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Convergence.Singular.FixedSubspaces
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Forward.ComplementDecomposition
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Local.OneStep
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Residual.Identities
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Execution.Computed.Model
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Projectors.Drazin.Algebra
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Recurrences.Affine.Unrolling
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Core.Definitions
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Scaling.Diagonal
import NumStability.Analysis.Conditioning.LinearSystems.SubordinatePerturbation
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter17.Equation01.ComputedIteration.Results
import NumStability.Source.Higham.Chapter17.Equation02.LocalError.Results
import NumStability.Source.Higham.Chapter17.Equation03.ComputedRecurrence.Results
import NumStability.Source.Higham.Chapter17.Equation04.FixedPoint.Results
import NumStability.Source.Higham.Chapter17.Equation05.ErrorExpansion.Results
import NumStability.Source.Higham.Chapter17.Equation06.ComponentwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation07.NormwiseGrowth.Results
import NumStability.Source.Higham.Chapter17.Equation08.NormwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation09.ComponentwiseGrowth.Results
import NumStability.Source.Higham.Chapter17.Equation10.LocalErrorSimplification.Results
import NumStability.Source.Higham.Chapter17.Equation12.PartialSumBound.Results
import NumStability.Source.Higham.Chapter17.Equation13.ComponentwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation15.NormwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation16.Jacobi.Results
import NumStability.Source.Higham.Chapter17.Equation17.SOR.Results
import NumStability.Source.Higham.Chapter17.Equation18.ResidualRecurrence.Results
import NumStability.Source.Higham.Chapter17.Equation19.ResidualBound.Results
import NumStability.Source.Higham.Chapter17.Equation20.ResidualSigma.Results
import NumStability.Source.Higham.Chapter17.Equation21.SingularIteration.Results
import NumStability.Source.Higham.Chapter17.Equation27.SingularErrorSplit.Results
import NumStability.Source.Higham.Chapter17.Equation28.SingularErrorSplit.Results
import NumStability.Source.Higham.Chapter17.Equation29.SingularSource.Results
import NumStability.Source.Higham.Chapter17.Equation33.StoppingTests.Results
import NumStability.Source.Higham.Chapter17.Section02.ScaleIndependence.Results
import NumStability.Source.Higham.Chapter17.Section04.PrintedConclusions.Results

/-!
# Higham Chapter 17, Equation 17.29: singular source-term bounds

Canonical normwise and componentwise bounds for the singular-system source
term in stationary iteration.
-/

namespace NumStability

open scoped BigOperators

/-- The action defining `S_m` is the matrix product
    `(G^k E M⁻¹) ξ_{m-k}` term by term. -/
private theorem singularErrorSourceTerm_term_eq (n : ℕ)
    (G E M_inv : Fin n → Fin n → ℝ) (ξ : ℕ → Fin n → ℝ)
    (m k : ℕ) :
    matMulVec n (matPow n G k)
        (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) =
      matMulVec n (matMul n (matMul n (matPow n G k) E) M_inv)
        (ξ (m - k)) := by
  ext i
  calc
    matMulVec n (matPow n G k)
        (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i =
      matMulVec n (matMul n (matPow n G k) E)
        (matMulVec n M_inv (ξ (m - k))) i := by
        rw [← matMulVec_matMul]
    _ = matMulVec n (matMul n (matMul n (matPow n G k) E) M_inv)
        (ξ (m - k)) i := by
        rw [← matMulVec_matMul]

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), finite
    normwise surface: a uniform local-error norm bound `||ξ_t||∞ ≤ μ` bounds
    `||S_m||∞` by `μ sum ||G^k E M⁻¹||∞`.  The source's displayed
    `c_n u(1+gamma_x)(||M||∞+||N||∞)||x||∞` is obtained by instantiating `μ`
    with the normwise local-error estimate. -/
theorem singularErrorSourceTerm_norm_bound (n : ℕ) (hn : 0 < n)
    (G E M_inv : Fin n → Fin n → ℝ) (ξ : ℕ → Fin n → ℝ)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hξ : ∀ t : ℕ, infNormVec (ξ t) ≤ μ) (m : ℕ) :
    infNormVec (singularErrorSourceTerm n G E M_inv ξ m) ≤
      μ * singularErrorSourceNormSum n G E M_inv m := by
  apply infNormVec_le_of_abs_le
  · intro i
    calc
      |singularErrorSourceTerm n G E M_inv ξ m i|
          = |∑ k ∈ Finset.range (m + 1),
              matMulVec n (matPow n G k)
                (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| := by
              rfl
      _ ≤ ∑ k ∈ Finset.range (m + 1),
            |matMulVec n (matPow n G k)
              (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (m + 1),
            infNorm (matMul n (matMul n (matPow n G k) E) M_inv) * μ := by
            apply Finset.sum_le_sum
            intro k _hk
            let P := matMul n (matMul n (matPow n G k) E) M_inv
            have hterm :=
              congrFun (singularErrorSourceTerm_term_eq n G E M_inv ξ m k) i
            calc
              |matMulVec n (matPow n G k)
                  (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i|
                  = |matMulVec n P (ξ (m - k)) i| := by
                    rw [hterm]
              _ ≤ infNormVec (matMulVec n P (ξ (m - k))) :=
                    abs_le_infNormVec _ i
              _ ≤ infNorm P * infNormVec (ξ (m - k)) :=
                    infNormVec_matMulVec_le hn P (ξ (m - k))
              _ ≤ infNorm P * μ := by
                    exact mul_le_mul_of_nonneg_left (hξ (m - k)) (infNorm_nonneg P)
      _ = μ * singularErrorSourceNormSum n G E M_inv m := by
            unfold singularErrorSourceNormSum
            rw [← Finset.sum_mul]
            ring
  · unfold singularErrorSourceNormSum
    exact mul_nonneg hμ
      (Finset.sum_nonneg (fun k _hk => infNorm_nonneg _))

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), finite
    componentwise surface: if the local errors satisfy the already-simplified
    componentwise source bound, then the singular source term `S_m` is bounded
    by `c_n u(1+theta_x) sum |G^k E M⁻¹|(|M|+|N|)|x|`. -/
theorem singularErrorSourceTerm_componentwise_bound (n : ℕ)
    (G E M_inv M N : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (ξ : ℕ → Fin n → ℝ) (cn_u theta_x : ℝ)
    (hξ : ∀ (t : ℕ) (j : Fin n),
      |ξ t j| ≤ cn_u * (1 + theta_x) *
        stationaryLocalErrorSourceVector n M N x j)
    (m : ℕ) :
    ∀ i, |singularErrorSourceTerm n G E M_inv ξ m i| ≤
      singularErrorSourceComponentBound n G E M_inv M N x cn_u theta_x m i := by
  intro i
  let coeff := cn_u * (1 + theta_x)
  calc
    |singularErrorSourceTerm n G E M_inv ξ m i|
        = |∑ k ∈ Finset.range (m + 1),
            matMulVec n (matPow n G k)
              (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| := by
            rfl
    _ ≤ ∑ k ∈ Finset.range (m + 1),
          |matMulVec n (matPow n G k)
            (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1),
          coeff *
            matMulVec n
              (absMatrix n (matMul n (matMul n (matPow n G k) E) M_inv))
              (stationaryLocalErrorSourceVector n M N x) i := by
          apply Finset.sum_le_sum
          intro k _hk
          let P := matMul n (matMul n (matPow n G k) E) M_inv
          have hterm :=
            congrFun (singularErrorSourceTerm_term_eq n G E M_inv ξ m k) i
          calc
            |matMulVec n (matPow n G k)
                (matMulVec n E (matMulVec n M_inv (ξ (m - k)))) i|
                = |matMulVec n P (ξ (m - k)) i| := by
                  rw [hterm]
            _ ≤ ∑ j : Fin n, |P i j| * |ξ (m - k) j| :=
                  abs_matMulVec_le n P (ξ (m - k)) i
            _ ≤ ∑ j : Fin n, |P i j| *
                  (coeff * stationaryLocalErrorSourceVector n M N x j) := by
                  apply Finset.sum_le_sum
                  intro j _hj
                  exact mul_le_mul_of_nonneg_left
                    (by simpa [coeff] using hξ (m - k) j) (abs_nonneg _)
            _ = coeff *
                  matMulVec n (absMatrix n P)
                    (stationaryLocalErrorSourceVector n M N x) i := by
                  unfold matMulVec absMatrix
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl (fun j _hj => by ring)
    _ = singularErrorSourceComponentBound n G E M_inv M N x cn_u theta_x m i := by
          unfold singularErrorSourceComponentBound
          rw [← Finset.mul_sum]

-- ============================================================
-- §17.2  Componentwise forward bound (eq 17.6)
-- ============================================================







































-- ============================================================
-- §17.2  Iterate-growth constants (eqs 17.7, 17.9)
-- ============================================================
































































































-- ============================================================
-- §17.2  Local error bound and simplification (eqs 17.2, 17.10)
-- ============================================================



























































































































































































/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), normwise
    surface instantiated from the source local-error model (17.2) and
    `gamma_x` iterate-growth hypothesis (17.7). -/
theorem singularErrorSourceTerm_norm_bound_of_local_error (n : ℕ) (hn : 0 < n)
    (G E M_inv M N : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i)
    (x_hat ξ : ℕ → Fin n → ℝ) (cn_u gamma_x : ℝ)
    (hcn : 0 ≤ cn_u) (hgamma : 0 ≤ gamma_x)
    (hx_bound : NormwiseIterateGrowthBound n x x_hat gamma_x)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u)
    (m : ℕ) :
    infNormVec (singularErrorSourceTerm n G E M_inv ξ m) ≤
      cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x *
        singularErrorSourceNormSum n G E M_inv m := by
  let μ := cn_u * (1 + gamma_x) * (infNorm M + infNorm N) * infNormVec x
  have hμ : 0 ≤ μ := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hcn (by linarith))
        (add_nonneg (infNorm_nonneg M) (infNorm_nonneg N)))
      (infNormVec_nonneg x)
  have hξ :
      ∀ t : ℕ, infNormVec (ξ t) ≤ μ := by
    simpa [μ] using
      local_error_normwise_simplified n M N b x hAx x_hat ξ
        cn_u gamma_x hcn hgamma hx_bound hLocal
  simpa [μ] using
    singularErrorSourceTerm_norm_bound n hn G E M_inv ξ μ hμ hξ m

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equation (17.29), instantiated
    componentwise surface: the displayed bound for `S_m` follows from the
    source local-error model (17.2), the exact equation `Mx-Nx=b`, and the
    componentwise iterate-growth hypothesis from (17.9). -/
theorem singularErrorSourceTerm_componentwise_bound_of_local_error (n : ℕ)
    (G E M_inv M N : Fin n → Fin n → ℝ)
    (b x : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, (M i j - N i j) * x j = b i)
    (x_hat ξ : ℕ → Fin n → ℝ) (cn_u theta_x : ℝ)
    (hcn : 0 ≤ cn_u) (hθ : 0 ≤ theta_x)
    (hx_bound : ComponentwiseIterateGrowthBound n x x_hat theta_x)
    (hLocal : LocalErrorBound n M N b x_hat ξ cn_u)
    (m : ℕ) :
    ∀ i, |singularErrorSourceTerm n G E M_inv ξ m i| ≤
      singularErrorSourceComponentBound n G E M_inv M N x cn_u theta_x m i := by
  have hξ :
      ∀ (t : ℕ) (j : Fin n),
        |ξ t j| ≤ cn_u * (1 + theta_x) *
          stationaryLocalErrorSourceVector n M N x j := by
    intro t j
    simpa [stationaryLocalErrorSourceVector] using
      local_error_simplified n M N b x hAx x_hat ξ cn_u theta_x
        hcn hθ hx_bound hLocal t j
  exact singularErrorSourceTerm_componentwise_bound
    n G E M_inv M N x ξ cn_u theta_x hξ m

end NumStability
