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
import NumStability.Algorithms.NormEstimation.PNorm.Rectangular.PNormRectangular
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Rectangular RectangularTermination

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

/-- The column objective visited by rectangular Algorithm 15.1 at `p = 1`. -/
noncomputable def oneColumnValueRect {m n : Nat}
    (A : Fin m -> Fin n -> Real) (j : Fin n) : Real :=
  oneNormVec (fun i => A i j)

/-- After a rectangular `p = 1` update, the next estimate is the 1-norm of
the selected column. -/
theorem gammaSeq_one_succ_eq_column_rect {m n : Nat} (hn : 0 < n)
    (A : Fin m -> Fin n -> Real) (x0 : Fin n -> Real) (k : Nat) :
    (one hn A).gammaSeq x0 (k + 1) =
      oneColumnValueRect A
        (argmaxAbs hn ((one hn A).zof ((one hn A).xseq x0 k))) := by
  let P := one hn A
  let z := P.zof (P.xseq x0 k)
  let J := argmaxAbs hn z
  let s := signVec z J
  have hs : |s| = 1 := by
    simpa [s] using abs_signVec z J
  change oneNormVec (P.yof (P.xnext (P.xseq x0 k))) =
    oneNormVec (fun i => A i J)
  have hxnext : P.xnext (P.xseq x0 k) =
      fun j => s * basisVec J j := by
    rfl
  rw [hxnext]
  unfold RectPNormPair.yof oneNormVec
  apply Finset.sum_congr rfl
  intro i _hi
  change |Finset.univ.sum (fun j : Fin n => A i j * (s * basisVec J j))| =
    |A i J|
  have hsum :
      Finset.univ.sum (fun j : Fin n => A i j * (s * basisVec J j)) =
        s * A i J := by
    simp only [basisVec]
    rw [show Finset.univ.sum
        (fun j : Fin n => A i j * (s * if j = J then 1 else 0)) =
          Finset.univ.sum (fun j : Fin n => if j = J then s * A i J else 0) by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hj : j = J
      · subst j
        simp
        ring
      · simp [hj]]
    simp
  rw [hsum, abs_mul, hs, one_mul]

/-- The row objective visited by rectangular Algorithm 15.1 at `p = infinity`. -/
noncomputable def infRowValueRect {m n : Nat}
    (A : Fin m -> Fin n -> Real) (i : Fin m) : Real :=
  oneNormVec (fun j => A i j)

/-- The full `z` vector at the rectangular infinity endpoint is the selected
row, multiplied by the sign of the attaining output coordinate. -/
theorem zof_infinity_eq_signed_selected_row_rect {m n : Nat}
    (hm : 0 < m) (hn : 0 < n)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) :
    (infinity hm hn A).zof x = fun j =>
      signVec ((infinity hm hn A).yof x)
          (argmaxAbs hm ((infinity hm hn A).yof x)) *
        A (argmaxAbs hm ((infinity hm hn A).yof x)) j := by
  let P := infinity hm hn A
  let y := P.yof x
  let J := argmaxAbs hm y
  let s := signVec y J
  funext j
  change Finset.univ.sum (fun i : Fin m => A i j * (s * basisVec J i)) =
    s * A J j
  simp only [basisVec]
  rw [show Finset.univ.sum
      (fun i : Fin m => A i j * (s * if i = J then 1 else 0)) =
        Finset.univ.sum (fun i : Fin m => if i = J then s * A J j else 0) by
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : i = J
    · subst i
      simp
      ring
    · simp [hi]]
  simp

/-- At `p = infinity`, the dual vector selects an output row, and the
1-norm of `z` is exactly the 1-norm of that selected row. -/
theorem qIn_zof_infinity_eq_row_rect {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) :
    (infinity hm hn A).qIn ((infinity hm hn A).zof x) =
      infRowValueRect A
        (argmaxAbs hm ((infinity hm hn A).yof x)) := by
  let P := infinity hm hn A
  let y := P.yof x
  let J := argmaxAbs hm y
  let s := signVec y J
  have hs : |s| = 1 := by
    simpa [s] using abs_signVec y J
  change oneNormVec (P.zof x) = oneNormVec (fun j => A J j)
  have hz : P.zof x = fun j => s * A J j := by
    funext j
    change Finset.univ.sum (fun i : Fin m => A i j * (s * basisVec J i)) =
      s * A J j
    simp only [basisVec]
    rw [show Finset.univ.sum
        (fun i : Fin m => A i j * (s * if i = J then 1 else 0)) =
          Finset.univ.sum (fun i : Fin m => if i = J then s * A J j else 0) by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi : i = J
      · subst i
        simp
        ring
      · simp [hi]]
    simp
  rw [hz]
  unfold oneNormVec
  apply Finset.sum_congr rfl
  intro j _hj
  rw [abs_mul, hs, one_mul]

end RectPNormPair
end NumStability
