import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
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
# NumStability Algorithms NormEstimation PNorm Boyd LocalStability BoydInterface

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydBridges` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- A local contraction-to-a-fixed-point certificate on a closed metric
ball.  This is a sufficient local-dynamics hypothesis, not a reformulation of
the conclusion that the iterates converge. -/
def IsLocalContractionTo {α : Type*} [PseudoMetricSpace α]
    (T : α → α) (xbar : α) (K : NNReal) (δ : ℝ) : Prop :=
  K < 1 ∧ 0 ≤ δ ∧ T xbar = xbar ∧
    ∀ x, dist x xbar ≤ δ → dist (T x) xbar ≤ (K : ℝ) * dist x xbar

/-- Iterates satisfying a local contraction certificate never leave its
closed ball and obey the exact geometric error estimate. -/
theorem iterate_dist_le_geometric_of_isLocalContractionTo
    {α : Type*} [PseudoMetricSpace α]
    {T : α → α} {xbar x0 : α} {K : NNReal} {δ : ℝ}
    (hlocal : IsLocalContractionTo T xbar K δ)
    (hx0 : dist x0 xbar ≤ δ) :
    ∀ k : ℕ,
      dist (T^[k] x0) xbar ≤ (K : ℝ) ^ k * dist x0 xbar ∧
      dist (T^[k] x0) xbar ≤ δ := by
  intro k
  induction k with
  | zero => simpa using And.intro (le_refl (dist x0 xbar)) hx0
  | succ k ih =>
      have hstep := hlocal.2.2.2 (T^[k] x0) ih.2
      have hKle : (K : ℝ) ≤ 1 := le_of_lt (by exact_mod_cast hlocal.1)
      constructor
      · rw [iterate_succ_apply']
        calc
          dist (T (T^[k] x0)) xbar
              ≤ (K : ℝ) * dist (T^[k] x0) xbar := hstep
          _ ≤ (K : ℝ) * ((K : ℝ) ^ k * dist x0 xbar) :=
            mul_le_mul_of_nonneg_left ih.1 K.coe_nonneg
          _ = (K : ℝ) ^ (k + 1) * dist x0 xbar := by ring
      · rw [iterate_succ_apply']
        calc
          dist (T (T^[k] x0)) xbar
              ≤ (K : ℝ) * dist (T^[k] x0) xbar := hstep
          _ ≤ 1 * dist (T^[k] x0) xbar :=
            mul_le_mul_of_nonneg_right hKle dist_nonneg
          _ ≤ δ := by simpa using ih.2

/-- The geometric estimate supplied by a local contraction certificate implies
topological convergence to the certified fixed point. -/
theorem tendsto_iterate_of_isLocalContractionTo
    {α : Type*} [PseudoMetricSpace α]
    {T : α → α} {xbar x0 : α} {K : NNReal} {δ : ℝ}
    (hlocal : IsLocalContractionTo T xbar K δ)
    (hx0 : dist x0 xbar ≤ δ) :
    Tendsto (fun k : ℕ => T^[k] x0) atTop (𝓝 xbar) := by
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero (fun _ => dist_nonneg)
  · intro k
    exact (iterate_dist_le_geometric_of_isLocalContractionTo hlocal hx0 k).1
  · simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one K.coe_nonneg
      (by exact_mod_cast hlocal.1)).mul_const (dist x0 xbar))

/-- A Frechet derivative with operator norm below one gives a genuine local
radial contraction about a fixed point.  The radius is constructed from the
little-o remainder in the definition of the derivative. -/
theorem exists_isLocalContractionTo_of_hasFDerivAt_norm_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : E → E} {xbar : E} {L : E →L[ℝ] E} {K : NNReal}
    (hfixed : T xbar = xbar)
    (hderiv : HasFDerivAt T L xbar)
    (hLK : ‖L‖ < (K : ℝ)) (hK : K < 1) :
    ∃ δ : ℝ, 0 < δ ∧ IsLocalContractionTo T xbar K δ := by
  let ε : ℝ := (K : ℝ) - ‖L‖
  have hε : 0 < ε := sub_pos.mpr hLK
  have hrem : ∀ᶠ x in nhds xbar,
      ‖T x - T xbar - L (x - xbar)‖ ≤ ε * ‖x - xbar‖ :=
    hderiv.isLittleO.def hε
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 hrem
  refine ⟨r / 2, half_pos hr, hK, (half_pos hr).le, hfixed, ?_⟩
  intro x hx
  have hxball : x ∈ Metric.ball xbar r := by
    rw [Metric.mem_ball]
    exact hx.trans_lt (half_lt_self hr)
  have hremainder := hrsub hxball
  rw [hfixed] at hremainder
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖T x - xbar‖
        = ‖(T x - xbar - L (x - xbar)) + L (x - xbar)‖ := by
            congr 1
            abel
    _ ≤ ‖T x - xbar - L (x - xbar)‖ + ‖L (x - xbar)‖ :=
      norm_add_le _ _
    _ ≤ ε * ‖x - xbar‖ + ‖L‖ * ‖x - xbar‖ :=
      add_le_add hremainder (L.le_opNorm (x - xbar))
    _ = (K : ℝ) * ‖x - xbar‖ := by
      dsimp [ε]
      ring

end Ch15
end NumStability
