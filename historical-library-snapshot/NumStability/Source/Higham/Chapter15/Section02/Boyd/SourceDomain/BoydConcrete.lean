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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydLocalStability
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.SecondVariation.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Convergence.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Section02.Boyd.SourceDomain.BoydLocal

/-!
# Chapter15 Section02 Boyd SourceDomain BoydConcrete

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydConcreteLemma3` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- Uniform local-linear theorem for the literal rectangular Boyd update.
The fixed-point equation and the Fréchet derivative are derived from raw
stationarity; nondegenerate constrained curvature supplies the stable power.
The only additional regularity assumptions are precisely the nonzero
coordinates used by the current smooth-domain Lemma 2. -/
theorem rect_general_boyd_concrete_local_linear_uniform
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hstat : IsBoydConcreteStationary p A x)
    (hnondeg : IsBoydConcreteNondegenerate p A x) :
    ∃ N : ℕ, 0 < N ∧ ∃ c K : NNReal,
      0 < c ∧ c < K ∧ K < 1 ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ x0 : Fin n → ℝ,
          powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
              (x0 - x) ≤ δ →
            (∀ k : ℕ,
              powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                  ((RectPNormPair.general hn hpq A).xseq x0 k - x) ≤
                (K : ℝ) ^ k *
                  powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                    (x0 - x)) ∧
            Tendsto ((RectPNormPair.general hn hpq A).xseq x0)
              atTop (nhds x) := by
  have hstat' := hstat
  obtain ⟨hunit, hS, hstationary⟩ := hstat
  have hfixed := rect_general_xnext_eq_of_stationarity
    hm hn hpq A x hxcoord hycoord hunit hstationary
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hS hstationary
  have hderiv := rect_general_xnext_hasFDerivAt_boyd
    hm hn hpq A x hycoord hzcoord
  have hL : boydSmoothRectDerivative (p := p) (q := q) A x =
      boydConcreteFullDerivative p A x := by
    ext h j
    rw [boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B
      hpq A x h hxcoord hycoord hunit hS hstationary]
    rw [boydConcreteFullDerivative_eq_normalized_projected
      p A x h hxcoord hstat']
  rw [hL] at hderiv
  obtain ⟨N, hN, c, hc0, hc1, hpow⟩ :=
    boydConcreteFullDerivative_power_stable
      hpq.lt A x hxcoord hunit hS hnondeg
  let K : NNReal := (c + 1) / 2
  have hcK : c < K := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (lt_div_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c * 2 = c + c := by ring
      _ < c + 1 := by simpa [add_comm] using add_lt_add_left hc1 c
  have hK1 : K < 1 := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (div_lt_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c + 1 < 1 + 1 := by simpa [add_comm] using add_lt_add_right hc1 1
      _ = 1 * 2 := by ring
  obtain ⟨δ, hδ, hlocal⟩ :=
    exists_local_powerAdaptedSeminormContraction
      hN hc0 hcK hK1 hpow hfixed hderiv
  refine ⟨N, hN, c, K, hc0, hcK, hK1, δ, hδ, ?_⟩
  intro x0 hx0
  have hgeom :=
    iterate_seminorm_le_geometric_of_localSeminormContraction hlocal hx0
  have hconv := tendsto_iterate_of_localSeminormContraction
    (fun y => norm_le_powerAdaptedSeminorm
      (boydConcreteFullDerivative p A x) c hN y) hlocal hx0
  constructor
  · intro k
    rw [rectPNormPair_xseq_eq_iterate]
    exact (hgeom k).1
  · rw [show (RectPNormPair.general hn hpq A).xseq x0 =
        (fun k : ℕ =>
          (RectPNormPair.general hn hpq A).xnext^[k] x0) by
      funext k
      exact rectPNormPair_xseq_eq_iterate _ _ _]
    exact hconv

/-- Fixed-start specialization of the preceding uniform neighborhood
theorem. -/
theorem rect_general_boyd_concrete_local_linear
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x0 x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hstat : IsBoydConcreteStationary p A x)
    (hnondeg : IsBoydConcreteNondegenerate p A x) :
    ∃ N : ℕ, 0 < N ∧ ∃ c K : NNReal,
      0 < c ∧ c < K ∧ K < 1 ∧ ∃ δ : ℝ, 0 < δ ∧
        (powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
            (x0 - x) ≤ δ →
          (∀ k : ℕ,
            powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                ((RectPNormPair.general hn hpq A).xseq x0 k - x) ≤
              (K : ℝ) ^ k *
                powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                  (x0 - x)) ∧
          Tendsto ((RectPNormPair.general hn hpq A).xseq x0)
            atTop (nhds x)) := by
  obtain ⟨N, hN, c, K, hc0, hcK, hK1, δ, hδ, hlocal⟩ :=
    rect_general_boyd_concrete_local_linear_uniform
      hm hn hpq A x hxcoord hycoord hstat hnondeg
  exact ⟨N, hN, c, K, hc0, hcK, hK1, δ, hδ, hlocal x0⟩

/-- Higham's source-facing implication: if the corrected nondegenerate
stationary point is a subsequential limit of the literal trace, then some
sampled entry point lies in the uniform adapted neighborhood.  The ensuing
tail has an explicit one-step geometric rate, and deleting the finite prefix
gives convergence of the full original trace.  No local-start assumption is
present. -/
theorem rect_general_boyd_concrete_linear_of_subsequential_limit
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x0 x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hstat : IsBoydConcreteStationary p A x)
    (hnondeg : IsBoydConcreteNondegenerate p A x)
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (hcluster : Tendsto
      (fun s => (RectPNormPair.general hn hpq A).xseq x0 (φ s))
      atTop (nhds x)) :
    ∃ r N : ℕ, 0 < N ∧ ∃ c K : NNReal,
      0 < c ∧ c < K ∧ K < 1 ∧
        (∀ k : ℕ,
          powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
              ((RectPNormPair.general hn hpq A).xseq x0 (φ r + k) - x) ≤
            (K : ℝ) ^ k *
              powerAdaptedSeminorm (boydConcreteFullDerivative p A x) c N
                ((RectPNormPair.general hn hpq A).xseq x0 (φ r) - x)) ∧
        Tendsto ((RectPNormPair.general hn hpq A).xseq x0)
          atTop (nhds x) := by
  obtain ⟨N, hN, c, K, hc0, hcK, hK1, δ, hδ, hlocal⟩ :=
    rect_general_boyd_concrete_local_linear_uniform
      hm hn hpq A x hxcoord hycoord hstat hnondeg
  obtain ⟨r, hr⟩ := exists_subsequence_in_powerAdapted_ball
    (RectPNormPair.general hn hpq A) x0 x
    (boydConcreteFullDerivative p A x) c N φ hδ hcluster
  obtain ⟨hgeomTail, hconvTail⟩ :=
    hlocal ((RectPNormPair.general hn hpq A).xseq x0 (φ r)) hr
  refine ⟨r, N, hN, c, K, hc0, hcK, hK1, ?_, ?_⟩
  · intro k
    simpa only [rectPNormPair_xseq_shift_add] using hgeomTail k
  · exact tendsto_rectPNormPair_xseq_of_tail
      (RectPNormPair.general hn hpq A) x0 x (φ r) hconvTail

end Ch15
end NumStability
