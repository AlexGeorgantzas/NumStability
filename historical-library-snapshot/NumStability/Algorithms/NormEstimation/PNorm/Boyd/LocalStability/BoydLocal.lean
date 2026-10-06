import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd LocalStability BoydLocal

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydSourceLocal` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- Powers commute with transport by a continuous linear equivalence. -/
theorem continuousLinearEquiv_conj_pow
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (L : F →L[ℝ] F) (N : ℕ) :
    L ^ N = e.toContinuousLinearMap.comp
      (((e.symm.toContinuousLinearMap.comp
        (L.comp e.toContinuousLinearMap)) ^ N).comp
          e.symm.toContinuousLinearMap) := by
  induction N with
  | zero =>
      ext x
      simp
  | succ N ih =>
      ext x
      simp only [pow_succ, ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.comp_apply, ih]
      simp

/-- A strict contraction after any equivalent change of norm yields a finite
strict power certificate in the original norm. -/
theorem exists_pos_power_bound_of_equivalent_contraction
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (L : F →L[ℝ] F) {c K : NNReal}
    (hcK : c < K)
    (hconj : ‖e.symm.toContinuousLinearMap.comp
      (L.comp e.toContinuousLinearMap)‖ ≤ (c : ℝ)) :
    ∃ N : ℕ, 0 < N ∧ ‖L ^ N‖ ≤ (K : ℝ) ^ N := by
  let S : E →L[ℝ] E := e.symm.toContinuousLinearMap.comp
    (L.comp e.toContinuousLinearMap)
  let M : ℝ := ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖
  have hc0 : 0 ≤ (c : ℝ) := NNReal.coe_nonneg c
  have hcK' : (c : ℝ) < (K : ℝ) := by exact_mod_cast hcK
  have hlittle : (fun N : ℕ => M * (c : ℝ) ^ N) =o[atTop]
      (fun N : ℕ => (K : ℝ) ^ N) :=
    (isLittleO_pow_pow_of_lt_left hc0 hcK').const_mul_left M
  have hev : ∀ᶠ N : ℕ in atTop,
      M * (c : ℝ) ^ N ≤ (K : ℝ) ^ N := by
    filter_upwards [hlittle.eventuallyLE] with N hN
    have hM : 0 ≤ M := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    simpa [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hM,
      abs_of_nonneg hc0, abs_of_nonneg (NNReal.coe_nonneg K)] using hN
  obtain ⟨N, hbound, hN⟩ :=
    (hev.and (eventually_ge_atTop (1 : ℕ))).exists
  refine ⟨N, hN, ?_⟩
  rw [continuousLinearEquiv_conj_pow e L N]
  calc
    ‖e.toContinuousLinearMap.comp
        ((S ^ N).comp e.symm.toContinuousLinearMap)‖
        ≤ ‖e.toContinuousLinearMap‖ *
          ‖(S ^ N).comp e.symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖e.toContinuousLinearMap‖ *
        (‖S ^ N‖ * ‖e.symm.toContinuousLinearMap‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ M * (c : ℝ) ^ N := by
      have hSN : ‖S ^ N‖ ≤ (c : ℝ) ^ N := by
        calc
          ‖S ^ N‖ ≤ ‖S‖ ^ N := norm_pow_le' S hN
          _ ≤ (c : ℝ) ^ N := pow_le_pow_left₀ (norm_nonneg S)
            (by simpa [S] using hconj) N
      dsimp [M]
      calc
        ‖e.toContinuousLinearMap‖ *
            (‖S ^ N‖ * ‖e.symm.toContinuousLinearMap‖) =
            (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) *
              ‖S ^ N‖ := by ring
        _ ≤ (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) *
              (c : ℝ) ^ N := mul_le_mul_of_nonneg_left hSN
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ *
              (c : ℝ) ^ N := rfl
    _ ≤ (K : ℝ) ^ N := hbound

end Ch15
end NumStability
