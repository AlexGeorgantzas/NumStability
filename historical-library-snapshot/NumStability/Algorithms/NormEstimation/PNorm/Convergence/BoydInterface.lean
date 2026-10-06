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
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Convergence BoydInterface

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

/-- The rectangular estimate sequence is bounded above by the induced
operator norm. -/
theorem rect_gammaSeq_bddAbove {m n : ℕ} (P : RectPNormPair m n)
    (x0 : Fin n → ℝ) (hx0 : P.pIn x0 = 1) :
    BddAbove (Set.range (P.gammaSeq x0)) := by
  refine ⟨P.opP, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact P.gammaSeq_le_opP x0 hx0 k

/-- A continuous self-map of a compact invariant set converges to its unique
fixed point when it admits a continuous Lyapunov function whose failure to
increase forces a fixed point. -/
theorem tendsto_iterate_of_compact_strictLyapunov_unique_fixed
    {α : Type*} [MetricSpace α]
    (s : Set α) (hs : IsCompact s)
    {T : α → α} {x0 xbar : α}
    (hx0 : x0 ∈ s) (hmap : MapsTo T s s)
    (hT : ContinuousOn T s) (g : α → ℝ) (hg : Continuous g)
    (hmono : ∀ x ∈ s, g x ≤ g (T x))
    (hfixed_of_back : ∀ x ∈ s, g (T x) ≤ g x → T x = x)
    (hunique : ∀ x ∈ s, T x = x → x = xbar) :
    Tendsto (fun k : ℕ => T^[k] x0) atTop (nhds xbar) := by
  let u : ℕ → α := fun k => T^[k] x0
  have hu_mem : ∀ k, u k ∈ s := by
    intro k
    induction k with
    | zero => exact hx0
    | succ k ih =>
        rw [show u (k + 1) = T (u k) by
          simp [u, iterate_succ_apply']]
        exact hmap ih
  let a : ℕ → ℝ := fun k => g (u k)
  have ha_mono : Monotone a := by
    apply monotone_nat_of_le_succ
    intro k
    change g (u k) ≤ g (u (k + 1))
    rw [show u (k + 1) = T (u k) by
      simp [u, iterate_succ_apply']]
    exact hmono (u k) (hu_mem k)
  have ha_bdd : BddAbove (Set.range a) := by
    apply (hs.bddAbove_image hg.continuousOn).mono
    rintro _ ⟨k, rfl⟩
    exact ⟨u k, hu_mem k, rfl⟩
  let ell : ℝ := ⨆ k : ℕ, a k
  have ha_lim : Tendsto a atTop (nhds ell) := by
    simpa [ell] using tendsto_atTop_ciSup ha_mono ha_bdd
  change Tendsto u atTop (nhds xbar)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨y, hy, phi, hphi, hsub⟩ :=
    hs.tendsto_subseq (fun k => hu_mem (ns k))
  refine ⟨phi, ?_⟩
  have hindex : Tendsto (fun k => ns (phi k)) atTop atTop :=
    hns.comp hphi.tendsto_atTop
  have ha_sub : Tendsto (fun k => a (ns (phi k))) atTop (nhds ell) :=
    ha_lim.comp hindex
  have hgy_sub : Tendsto (fun k => g (u (ns (phi k)))) atTop (nhds (g y)) := by
    exact hg.continuousAt.tendsto.comp (by simpa [Function.comp_def] using hsub)
  have hgy : g y = ell := tendsto_nhds_unique hgy_sub ha_sub
  have hshift : Tendsto (fun k => ns (phi k) + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hindex
  have ha_shift : Tendsto (fun k => a (ns (phi k) + 1)) atTop (nhds ell) :=
    ha_lim.comp hshift
  have hgTy_sub : Tendsto (fun k => g (T (u (ns (phi k))))) atTop
      (nhds (g (T y))) := by
    have hsub_nhds : Tendsto (fun k => u (ns (phi k))) atTop (nhds y) := by
      simpa [Function.comp_def] using hsub
    have hsub_mem : ∀ᶠ k in atTop, u (ns (phi k)) ∈ s :=
      Eventually.of_forall fun k => hu_mem (ns (phi k))
    have hsub_within : Tendsto (fun k => u (ns (phi k))) atTop
        (nhdsWithin y s) :=
      tendsto_nhdsWithin_iff.mpr ⟨hsub_nhds, hsub_mem⟩
    exact hg.continuousAt.tendsto.comp
      ((hT y hy).tendsto.comp hsub_within)
  have hgT_shift : Tendsto (fun k => g (T (u (ns (phi k))))) atTop
      (nhds ell) := by
    simpa [a, u, iterate_succ_apply'] using ha_shift
  have hgTy : g (T y) = ell := tendsto_nhds_unique hgTy_sub hgT_shift
  have hyfixed : T y = y := hfixed_of_back y hy (by rw [hgTy, hgy])
  have hybar : y = xbar := hunique y hy hyfixed
  simpa [Function.comp_def, hybar] using hsub

end Ch15
end NumStability
