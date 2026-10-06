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
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Convergence ConvergenceStatements

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

/-- **Higham p. 291, convergent subsequence.**  Whenever the unit sphere of
the selected finite-dimensional norm is compact, the unit iterates of
Algorithm 15.1 have a convergent subsequence whose limit is again unit.

Compactness is explicit because the abstract `PNormPair` interface records
only the algebraic duality facts used by Lemma 15.2; it does not assume that
its arbitrary real-valued functional induces the ambient topology. -/
theorem xseq_has_convergent_subsequence
    (x0 : Fin n → ℝ) (hx0 : P.pN x0 = 1)
    (hcompact : IsCompact {x : Fin n → ℝ | P.pN x = 1}) :
    ∃ xbar : Fin n → ℝ, P.pN xbar = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (P.xseq x0 ∘ φ) atTop (𝓝 xbar) := by
  simpa only [Set.mem_setOf_eq] using
    hcompact.tendsto_subseq (fun k => P.xseq_punit x0 hx0 k)

/-- A convergent functional iteration has a fixed-point limit whenever its
update map is continuous at that limit.  This is the topological bridge used
in the stationary-limit audit below. -/
theorem xseq_limit_is_fixed_of_continuousAt
    (x0 xbar : Fin n → ℝ)
    (hlim : Tendsto (P.xseq x0) atTop (𝓝 xbar))
    (hcont : ContinuousAt P.xnext xbar) :
    P.xnext xbar = xbar := by
  have hnext : Tendsto (P.xnext ∘ P.xseq x0) atTop (𝓝 (P.xnext xbar)) :=
    hcont.tendsto.comp hlim
  have hshift : Tendsto (fun k => P.xseq x0 (k + 1)) atTop (𝓝 xbar) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have heq : (fun k => P.xseq x0 (k + 1)) = P.xnext ∘ P.xseq x0 := by
    funext k
    rfl
  rw [heq] at hshift
  exact tendsto_nhds_unique hnext hshift

end PNormPair
end Ch15
end NumStability
