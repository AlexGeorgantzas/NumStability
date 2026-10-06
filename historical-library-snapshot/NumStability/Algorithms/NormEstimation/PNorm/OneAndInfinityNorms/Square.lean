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
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# Square

Canonical destination for the frozen declaration block of
`NumStability.Algorithms.NormEstimation.PNorm.Endpoints.ConvergenceStatements`, routed by wave R02 of the August 2026 repository reorganization
completion phase. Declaration names, kinds, visibilities, signatures and
proofs are unchanged; only the module they live in has changed. Private
declarations keep their logical names and are re-mangled against this module,
exactly as recorded in the reviewed private normalization.
-/

/-!
# NumStability Algorithms NormEstimation PNorm Endpoints ConvergenceStatements

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

/-- Pigeonhole core of the endpoint termination argument: a process labelled
by only `n` vertices cannot strictly increase a real-valued vertex objective
on each of its first `n` transitions. -/
theorem exists_nonincreasing_step_of_fin_labels {n : ℕ}
    (label : ℕ → Fin n) (value : Fin n → ℝ) :
    ∃ k : ℕ, k < n ∧ value (label (k + 1)) ≤ value (label k) := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  let f : Fin (n + 1) → ℝ := fun i => value (label i.1)
  have hf : StrictMono f := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact h i.1 i.2
  let labels : Fin (n + 1) → Fin n := fun i => label i.1
  have hinj : Function.Injective labels := by
    intro i j hij
    apply hf.injective
    exact congrArg value hij
  have hcard := Fintype.card_le_of_injective labels hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- The column objective visited by the concrete `p=1` power method. -/
noncomputable def oneColumnValue {n : ℕ}
    (A : Fin n → Fin n → ℝ) (j : Fin n) : ℝ :=
  oneNormVec (fun i => A i j)

/-- After a `p=1` update, the next scalar estimate is the 1-norm of the
selected column.  The sign of the extreme point disappears under the norm. -/
theorem gammaSeq_one_succ_eq_column {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x0 : Fin n → ℝ) (k : ℕ) :
    (pNormPair_one hn A).gammaSeq x0 (k + 1) =
      oneColumnValue A
        (argmaxAbs hn ((pNormPair_one hn A).zof
          ((pNormPair_one hn A).xseq x0 k))) := by
  let P := pNormPair_one hn A
  let z := P.zof (P.xseq x0 k)
  let J := argmaxAbs hn z
  let s := signVec z J
  have hs : |s| = 1 := by
    simpa [s] using abs_signVec z J
  change oneNormVec (P.yof (P.xnext (P.xseq x0 k))) =
    oneNormVec (fun i => A i J)
  have hxnext : P.xnext (P.xseq x0 k) = fun j => s * basisVec J j := by
    rfl
  rw [hxnext]
  unfold PNormPair.yof oneNormVec
  apply Finset.sum_congr rfl
  intro i _hi
  change |∑ j : Fin n, A i j * (s * basisVec J j)| = |A i J|
  have hsum : (∑ j : Fin n, A i j * (s * basisVec J j)) = s * A i J := by
    simp only [basisVec]
    rw [show (∑ j : Fin n, A i j * (s * if j = J then 1 else 0)) =
        ∑ j : Fin n, if j = J then s * A i J else 0 by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hj : j = J
      · subst j
        simp
        ring
      · simp [hj]]
    simp
  rw [hsum, abs_mul, hs, one_mul]

/-- The sign vector has infinity norm exactly one in positive dimension. -/
lemma sign_infNorm_eq_one {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    infNormVec (signVec v) = 1 := by
  apply le_antisymm
  · exact sign_qunit_one v
  · have hcoord := abs_le_infNormVec (signVec v) (⟨0, hn⟩ : Fin n)
    rwa [abs_signVec] at hcoord

/-- Hölder's inequality for the endpoint pair `p=∞`, `q=1`. -/
lemma holder_inf {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i : Fin n, u i * v i) ≤ oneNormVec u * infNormVec v := by
  calc
    (∑ i : Fin n, u i * v i)
        ≤ ∑ i : Fin n, |u i * v i| :=
          Finset.sum_le_sum (fun i _hi => le_abs_self (u i * v i))
    _ = ∑ i : Fin n, |u i| * |v i| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul]
    _ ≤ ∑ i : Fin n, |u i| * infNormVec v := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_left (abs_le_infNormVec v i) (abs_nonneg _)
    _ = oneNormVec u * infNormVec v := by
      unfold oneNormVec
      rw [Finset.sum_mul]

/-- The concrete `p=∞`, `q=1` specialization of Algorithm 15.1.  Both dual
maps choose extreme points: `dualp(y)=±e_J` and `dualq(z)=sign(z)`. -/
noncomputable def pNormPair_inf {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : PNormPair n where
  A := A
  pN := infNormVec
  qN := oneNormVec
  opP := infNorm A
  dp := dualq_one hn
  dq := signVec
  pN_nonneg := infNormVec_nonneg
  dp_attains := dualq_one_attains hn
  dp_qunit := fun v => le_of_eq (dualq_one_punit hn v)
  dq_attains := sign_attains_one
  dq_punit := sign_infNorm_eq_one hn
  holder := holder_inf
  op_bound := fun v => by
    simpa [PNormPair.yof, matMulVec] using infNormVec_matMulVec_le hn A v

/-- The row objective used in the `p=∞` endpoint pigeonhole argument. -/
noncomputable def infRowValue {n : ℕ}
    (A : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  oneNormVec (fun j => A i j)

/-- For `p=∞`, `z=Aᵀdualp(y)` has 1-norm equal to the 1-norm of the row
selected by the extreme dual vector `dualp(y)=±e_J`. -/
theorem qNorm_zof_inf_eq_row {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    (pNormPair_inf hn A).qN ((pNormPair_inf hn A).zof x) =
      infRowValue A
        (argmaxAbs hn ((pNormPair_inf hn A).yof x)) := by
  let P := pNormPair_inf hn A
  let y := P.yof x
  let J := argmaxAbs hn y
  let s := signVec y J
  have hs : |s| = 1 := by
    simpa [s] using abs_signVec y J
  change oneNormVec (P.zof x) = oneNormVec (fun j => A J j)
  have hz : P.zof x = fun j => s * A J j := by
    funext j
    change (∑ i : Fin n, A i j * (s * basisVec J i)) = s * A J j
    simp only [basisVec]
    rw [show (∑ i : Fin n, A i j * (s * if i = J then 1 else 0)) =
        ∑ i : Fin n, if i = J then s * A J j else 0 by
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

end Ch15
end NumStability
