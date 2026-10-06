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
import NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Rectangular
import NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Square
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.RectangularTermination
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification
import NumStability.Source.Higham.Chapter15.Lemma02.PNormPowerMethod.PNormRectangular

/-!
# Chapter15 Section02 Boyd EndpointTermination RectangularTermination

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15RectTermination` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

open Ch15

namespace RectPNormPair

/-- **Higham p. 291, rectangular finite termination for `p = 1`.**
Among the first `n+1` tests, one succeeds.  The bound depends on the domain
dimension because the updates visit signed coordinate vectors in `R^n`. -/
theorem one_terminates_by_n_plus_one_rect {m n : Nat} (hn : 0 < n)
    (A : Fin m -> Fin n -> Real) (x0 : Fin n -> Real)
    (hx0 : oneNormVec x0 = 1) :
    exists k : Nat, k <= n /\ (one hn A).StopsAt ((one hn A).xseq x0 k) := by
  let P := one hn A
  let label : Nat -> Fin n := fun k => argmaxAbs hn (P.zof (P.xseq x0 k))
  let value : Fin n -> Real := oneColumnValueRect A
  obtain ⟨r, hrn, hrnoninc⟩ :=
    Ch15.exists_nonincreasing_step_of_fin_labels label value
  by_cases htest : P.StopsAt (P.xseq x0 (r + 1))
  · exact ⟨r + 1, by omega, htest⟩
  · have hstrict : P.gammaSeq x0 (r + 1) < P.gammaSeq x0 (r + 2) := by
      have hfirst : P.pOut (P.yof (P.xseq x0 (r + 1))) <
          P.qIn (P.zof (P.xseq x0 (r + 1))) :=
        (P.higham15_lemma15_2_rectangular_strict
          (P.xseq x0 (r + 1))).mp htest
      have hunit : P.pIn (P.xseq x0 (r + 1)) = 1 :=
        P.xseq_punit x0 hx0 (r + 1)
      have hsecond :=
        (P.higham15_lemma15_2b_rectangular (P.xseq x0 (r + 1)) hunit).2.1
      exact lt_of_lt_of_le hfirst
        (by simpa [RectPNormPair.gammaSeq, RectPNormPair.xseq] using hsecond)
    have hcol1 : P.gammaSeq x0 (r + 1) = value (label r) := by
      simpa [P, label, value] using gammaSeq_one_succ_eq_column_rect hn A x0 r
    have hcol2 : P.gammaSeq x0 (r + 2) = value (label (r + 1)) := by
      simpa [P, label, value, Nat.add_assoc] using
        gammaSeq_one_succ_eq_column_rect hn A x0 (r + 1)
    rw [hcol1, hcol2] at hstrict
    exact (not_lt_of_ge hrnoninc hstrict).elim

/-- **Corrected rectangular endpoint theorem.**  At `p = infinity`, among
the first `m+1` tests one succeeds.  The count is `m+1`, not `n+1`, because
the extreme dual choices and the strictly increasing row objectives live in
the output space `R^m`. -/
theorem infinity_terminates_by_m_plus_one_rect {m n : Nat}
    (hm : 0 < m) (hn : 0 < n)
    (A : Fin m -> Fin n -> Real) (x0 : Fin n -> Real)
    (hx0 : infNormVec x0 = 1) :
    exists k : Nat, k <= m /\
      (infinity hm hn A).StopsAt ((infinity hm hn A).xseq x0 k) := by
  let P := infinity hm hn A
  let label : Nat -> Fin m := fun k => argmaxAbs hm (P.yof (P.xseq x0 k))
  let value : Fin m -> Real := infRowValueRect A
  obtain ⟨r, hrm, hrnoninc⟩ :=
    Ch15.exists_nonincreasing_step_of_fin_labels label value
  by_cases htest0 : P.StopsAt (P.xseq x0 r)
  · exact ⟨r, by omega, htest0⟩
  by_cases htest1 : P.StopsAt (P.xseq x0 (r + 1))
  · exact ⟨r + 1, by omega, htest1⟩
  · have hunit : P.pIn (P.xseq x0 r) = 1 := P.xseq_punit x0 hx0 r
    have hmiddle :=
      (P.higham15_lemma15_2b_rectangular (P.xseq x0 r) hunit).2.1
    have hstrict1 : P.pOut (P.yof (P.xseq x0 (r + 1))) <
        P.qIn (P.zof (P.xseq x0 (r + 1))) :=
      (P.higham15_lemma15_2_rectangular_strict
        (P.xseq x0 (r + 1))).mp htest1
    have hvalues : value (label r) < value (label (r + 1)) := by
      have hrow0 : P.qIn (P.zof (P.xseq x0 r)) = value (label r) := by
        have hraw := qIn_zof_infinity_eq_row_rect hm hn A (P.xseq x0 r)
        change P.qIn (P.zof (P.xseq x0 r)) =
          infRowValueRect A (argmaxAbs hm (P.yof (P.xseq x0 r))) at hraw
        simpa [label, value] using hraw
      have hrow1 : P.qIn (P.zof (P.xseq x0 (r + 1))) =
          value (label (r + 1)) := by
        have hraw := qIn_zof_infinity_eq_row_rect hm hn A (P.xseq x0 (r + 1))
        change P.qIn (P.zof (P.xseq x0 (r + 1))) =
          infRowValueRect A
            (argmaxAbs hm (P.yof (P.xseq x0 (r + 1))) ) at hraw
        simpa [label, value] using hraw
      rw [<- hrow0, <- hrow1]
      exact lt_of_le_of_lt
        (by simpa [RectPNormPair.xseq] using hmiddle) hstrict1
    exact (not_lt_of_ge hrnoninc hvalues).elim

/-- A `5 x 3` matrix whose infinity-endpoint trace makes four strict
improvements before stopping. -/
def infinityNPlusOneCounterexampleA : Fin 5 -> Fin 3 -> Real :=
  ![![-14, 1, 1],
    ![-9, 9, -12],
    ![1, -16, 18],
    ![-3, -16, -6],
    ![-16, -14, 1]]

/-- Unit-infinity-norm start of the rectangular discrepancy trace. -/
noncomputable def infinityNPlusOneCounterexampleX0 : Fin 3 -> Real := ![-1, 1 / 5, 1]

/-- The displayed counterexample starts from a unit infinity-norm vector. -/
theorem infinityNPlusOneCounterexample_unit :
    infNormVec infinityNPlusOneCounterexampleX0 = 1 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      fin_cases i <;> norm_num [infinityNPlusOneCounterexampleX0]
    · norm_num
  · have h := abs_le_infNormVec infinityNPlusOneCounterexampleX0 (0 : Fin 3)
    norm_num [infinityNPlusOneCounterexampleX0] at h
    exact h

end RectPNormPair
end NumStability
