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
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.PNormPowerMethod
import NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Square
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormPowerMethod

/-!
# Chapter15 Section02 Boyd EndpointTermination ConvergenceStatements

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

/-- **Higham p. 291, finite endpoint termination for `p=1`.**  Among the
first `n+1` tests (indices `0,…,n`), at least one satisfies the convergence
test.  Equivalently, the concrete extreme-point implementation cannot make
more than `n` strict improvements before termination. -/
theorem pNormPair_one_terminates_by_n_plus_one {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x0 : Fin n → ℝ)
    (hx0 : oneNormVec x0 = 1) :
    ∃ k : ℕ, k ≤ n ∧
      (pNormPair_one hn A).qN
          ((pNormPair_one hn A).zof
            ((pNormPair_one hn A).xseq x0 k)) ≤
        (pNormPair_one hn A).pN
          ((pNormPair_one hn A).yof
            ((pNormPair_one hn A).xseq x0 k)) := by
  let P := pNormPair_one hn A
  let label : ℕ → Fin n := fun k => argmaxAbs hn (P.zof (P.xseq x0 k))
  let value : Fin n → ℝ := oneColumnValue A
  obtain ⟨r, hrn, hrnoninc⟩ :=
    exists_nonincreasing_step_of_fin_labels label value
  by_cases htest : P.qN (P.zof (P.xseq x0 (r + 1))) ≤
      P.pN (P.yof (P.xseq x0 (r + 1)))
  · exact ⟨r + 1, by omega, htest⟩
  · have hstrict : P.gammaSeq x0 (r + 1) < P.gammaSeq x0 (r + 2) := by
      have hfirst : P.pN (P.yof (P.xseq x0 (r + 1))) <
          P.qN (P.zof (P.xseq x0 (r + 1))) :=
        (lemma152b_strict P (P.xseq x0 (r + 1))).mp htest
      have hunit : P.pN (P.xseq x0 (r + 1)) = 1 :=
        P.xseq_punit x0 hx0 (r + 1)
      have hsecond := (P.lemma152b (P.xseq x0 (r + 1)) hunit).2.1
      exact lt_of_lt_of_le hfirst (by simpa [PNormPair.gammaSeq, PNormPair.xseq] using hsecond)
    have hcol1 : P.gammaSeq x0 (r + 1) = value (label r) := by
      simpa [P, label, value] using gammaSeq_one_succ_eq_column hn A x0 r
    have hcol2 : P.gammaSeq x0 (r + 2) = value (label (r + 1)) := by
      simpa [P, label, value, Nat.add_assoc] using
        gammaSeq_one_succ_eq_column hn A x0 (r + 1)
    rw [hcol1, hcol2] at hstrict
    exact (not_lt_of_ge hrnoninc hstrict).elim

/-- **Higham p. 291, finite endpoint termination for `p=∞` (square case).**
Among tests `0,…,n`, one succeeds.  The proof follows Higham's row-vertex
argument: off convergence, the 1-norms of successively selected rows strictly
increase, which cannot happen for `n+1` labels drawn from `n` rows.

The source introduces Algorithm 15.1 for `A : ℝ^{m×n}` but later says `n+1`
for both endpoints.  For rectangular `p=∞` the same argument counts the `m`
codomain vertices and gives `m+1`; the repository's `PNormPair` is square, so
the displayed `n+1` statement is literally valid here. -/
theorem pNormPair_inf_terminates_by_n_plus_one {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x0 : Fin n → ℝ)
    (hx0 : infNormVec x0 = 1) :
    ∃ k : ℕ, k ≤ n ∧
      (pNormPair_inf hn A).qN
          ((pNormPair_inf hn A).zof
            ((pNormPair_inf hn A).xseq x0 k)) ≤
        (pNormPair_inf hn A).pN
          ((pNormPair_inf hn A).yof
            ((pNormPair_inf hn A).xseq x0 k)) := by
  let P := pNormPair_inf hn A
  let label : ℕ → Fin n := fun k =>
    argmaxAbs hn (P.yof (P.xseq x0 k))
  let value : Fin n → ℝ := infRowValue A
  obtain ⟨r, hrn, hrnoninc⟩ :=
    exists_nonincreasing_step_of_fin_labels label value
  by_cases htest0 : P.qN (P.zof (P.xseq x0 r)) ≤
      P.pN (P.yof (P.xseq x0 r))
  · exact ⟨r, by omega, htest0⟩
  by_cases htest1 : P.qN (P.zof (P.xseq x0 (r + 1))) ≤
      P.pN (P.yof (P.xseq x0 (r + 1)))
  · exact ⟨r + 1, by omega, htest1⟩
  · have hunit : P.pN (P.xseq x0 r) = 1 := P.xseq_punit x0 hx0 r
    have hmiddle := (P.lemma152b (P.xseq x0 r) hunit).2.1
    have hstrict1 : P.pN (P.yof (P.xseq x0 (r + 1))) <
        P.qN (P.zof (P.xseq x0 (r + 1))) :=
      (lemma152b_strict P (P.xseq x0 (r + 1))).mp htest1
    have hvalues : value (label r) < value (label (r + 1)) := by
      have hrow0 : P.qN (P.zof (P.xseq x0 r)) = value (label r) := by
        have hraw := qNorm_zof_inf_eq_row hn A (P.xseq x0 r)
        change P.qN (P.zof (P.xseq x0 r)) =
          infRowValue A (argmaxAbs hn (P.yof (P.xseq x0 r))) at hraw
        simpa [label, value] using hraw
      have hrow1 : P.qN (P.zof (P.xseq x0 (r + 1))) =
          value (label (r + 1)) := by
        have hraw := qNorm_zof_inf_eq_row hn A (P.xseq x0 (r + 1))
        change P.qN (P.zof (P.xseq x0 (r + 1))) =
          infRowValue A (argmaxAbs hn (P.yof (P.xseq x0 (r + 1)))) at hraw
        simpa [label, value] using hraw
      rw [← hrow0, ← hrow1]
      exact lt_of_le_of_lt
        (by simpa [PNormPair.xseq] using hmiddle) hstrict1
    exact (not_lt_of_ge hrnoninc hvalues).elim

end Ch15
end NumStability
