import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.OneNorm.FiniteIndex.Basic
import NumStability.Algorithms.NormEstimation.OneNorm.PowerMethod.CondEstimation
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Algorithms NormEstimation OneNorm PowerMethod PNormPowerMethod

Canonical destination for material split out of
`NumStability.Algorithms.PNormPowerMethod` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open scoped BigOperators

namespace PNormPair

variable {n : ℕ} (P : PNormPair n)

end PNormPair

/-- `dualp` for `p = 1` is the sign vector (unit ∞-norm, attaining `‖·‖₁`).
    Reuses `signVec` from `Algorithms/CondEstimation`. -/
lemma sign_attains_one {n : ℕ} (v : Fin n → ℝ) :
    (∑ i : Fin n, signVec v i * v i) = oneNormVec v := by
  unfold oneNormVec
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]; exact mul_signVec_eq_abs v i

lemma sign_qunit_one {n : ℕ} (v : Fin n → ℝ) : infNormVec (signVec v) ≤ 1 := by
  apply infNormVec_le_of_abs_le
  · intro i; rw [abs_signVec]
  · exact zero_le_one

/-- `dualq` for `p = 1`: `sign(w_J) · e_J` where `J` is the (smallest) index
    with `|w_J| = ‖w‖_∞`.  This is Higham's `x = ±e_j` extreme-point choice
    (Algorithm 15.1, `dualq(z)` for `p = 1`); the sign makes it attain `‖w‖_∞`
    rather than merely `|w_J|`, and it has unit 1-norm. -/
noncomputable def dualq_one {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => signVec w (argmaxAbs hn w) * basisVec (argmaxAbs hn w) i

lemma dualq_one_punit {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) :
    oneNormVec (dualq_one hn w) = 1 := by
  unfold oneNormVec dualq_one
  have hs : |signVec w (argmaxAbs hn w)| = 1 := abs_signVec w _
  calc (∑ i : Fin n, |signVec w (argmaxAbs hn w) * basisVec (argmaxAbs hn w) i|)
      = ∑ i : Fin n, |basisVec (argmaxAbs hn w) i| := by
        apply Finset.sum_congr rfl; intro i _
        rw [abs_mul, hs, one_mul]
    _ = oneNormVec (basisVec (argmaxAbs hn w)) := rfl
    _ = 1 := oneNormVec_basisVec _

lemma dualq_one_attains {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) :
    (∑ i : Fin n, dualq_one hn w i * w i) = infNormVec w := by
  unfold dualq_one
  set J := argmaxAbs hn w with hJdef
  have hstep : (∑ i : Fin n, signVec w J * basisVec J i * w i)
      = signVec w J * w J := by
    rw [show (∑ i : Fin n, signVec w J * basisVec J i * w i)
          = ∑ i : Fin n, signVec w J * (basisVec J i * w i) from
        Finset.sum_congr rfl (fun i _ => by ring)]
    rw [← Finset.mul_sum]
    congr 1
    unfold basisVec
    rw [show (∑ i : Fin n, (if i = J then (1:ℝ) else 0) * w i)
          = ∑ i : Fin n, (if i = J then w i else 0) from
        Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)]
    rw [Finset.sum_ite_eq' Finset.univ J w]
    simp
  rw [hstep, mul_comm, mul_signVec_eq_abs]
  -- |w J| = ‖w‖_∞ since J is the argmax of |·|
  apply le_antisymm
  · exact abs_le_infNormVec w J
  · apply infNormVec_le_of_abs_le
    · intro i; exact argmaxAbs_spec hn w i
    · exact abs_nonneg _

/-- Hölder for `p = 1`, `q = ∞`: `uᵀ v ≤ ‖u‖_∞ ‖v‖₁`. -/
lemma holder_one {n : ℕ} (u v : Fin n → ℝ) :
    (∑ i : Fin n, u i * v i) ≤ infNormVec u * oneNormVec v := by
  calc (∑ i : Fin n, u i * v i)
      ≤ ∑ i : Fin n, |u i * v i| := Finset.sum_le_sum (fun i _ => le_abs_self _)
    _ = ∑ i : Fin n, |u i| * |v i| := by
        apply Finset.sum_congr rfl; intro i _; exact abs_mul _ _
    _ ≤ ∑ i : Fin n, infNormVec u * |v i| := by
        apply Finset.sum_le_sum; intro i _
        exact mul_le_mul_of_nonneg_right (abs_le_infNormVec u i) (abs_nonneg _)
    _ = infNormVec u * oneNormVec v := by
        unfold oneNormVec; rw [Finset.mul_sum]

/-- **The 1-norm power method as a `PNormPair`** (Higham §15.2, `p = 1`).

    For `p = 1` the dual is `q = ∞`; here `‖·‖_p = oneNormVec`,
    `‖·‖_q = infNormVec`, `‖A‖_p = oneNorm A` (max column sum), `dualp = signVec`
    and `dualq(z) = ±e_j` at the largest-magnitude entry.  All hypotheses are
    discharged from `CondEstimation`/`MatrixAlgebra` lemmas (the operator bound
    is `oneNormVec_matVec_le`), so Lemma 15.2 and the lower bound
    `gammaSeq_le_opP` hold for this concrete instance too. -/
noncomputable def pNormPair_one {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : PNormPair n where
  A := A
  pN := oneNormVec
  qN := infNormVec
  opP := oneNorm A
  dp := signVec
  dq := dualq_one hn
  pN_nonneg := oneNormVec_nonneg
  dp_attains := sign_attains_one
  dp_qunit := sign_qunit_one
  dq_attains := dualq_one_attains hn
  dq_punit := dualq_one_punit hn
  holder := holder_one
  op_bound := fun v => oneNormVec_matVec_le hn A v

end Ch15
end NumStability
