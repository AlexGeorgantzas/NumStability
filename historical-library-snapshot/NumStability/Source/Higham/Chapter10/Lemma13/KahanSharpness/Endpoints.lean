import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.RoundedFactorization.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound

/-!
# Chapter10 Lemma13 KahanSharpness Endpoints

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter10` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Equation (10.13)**: complete-pivoting inequality for the displayed
Cholesky factor, written with zero-based finite indices. -/
def higham10_13_completePivotingInequality (n r : ℕ)
    (R : Fin n → Fin n → ℝ) : Prop :=
  ∀ k j : Fin n, k.val < r → k.val < j.val →
    R k k ^ 2 ≥
      ∑ i : Fin n,
        if k.val ≤ i.val ∧ i.val ≤ j.val ∧ i.val < r then R i j ^ 2 else 0

/-- **The display-(10.18) matrix** (Higham p. 204, square-block
    instance `k = n − k`): `A = [[αI, I], [I, α⁻¹I]]`, the positive
    semidefinite matrix on which Lemma 10.12's inequality is an
    equality and `‖W‖₂ = α⁻¹` is arbitrarily large. -/
noncomputable def higham10_18_matrix (k : ℕ) (α : ℝ) :
    Fin (k + k) → Fin (k + k) → ℝ :=
  fun i j =>
    if i.val = j.val then (if i.val < k then α else α⁻¹)
    else if i.val + k = j.val ∨ j.val + k = i.val then 1 else 0

/-- **Lemma 10.13 / equation (10.19)**: complete-pivoting bound on
`‖W‖_F²` with Higham's `(n−r)(4^r−1)/3` constant, in honest form: for
an `r × r` upper-triangular block `U` with positive diagonal whose rows
are pivot-dominated on and right of the diagonal — exactly what
complete pivoting guarantees via the (10.13) column-tail invariant
(`tail_invariant_entry_le` applied to the factor from
`psd_pivoted_cholesky_exists_tail`) — the solution `W` of `U W = B`
with pivot-dominated right-hand columns `B` (the border block `R₁₂`)
satisfies `∑_{i,j} W i j ² ≤ m (4^r − 1)/3`, `m = n − r` border
columns. -/
theorem higham10_13_complete_pivoting_w_bound {r m : ℕ}
    (U : Fin r → Fin r → ℝ) (B W : Fin r → Fin m → ℝ)
    (hupper : ∀ i j : Fin r, j.val < i.val → U i j = 0)
    (hdiag_pos : ∀ i : Fin r, 0 < U i i)
    (hentry : ∀ i j : Fin r, i.val ≤ j.val → |U i j| ≤ U i i)
    (hB : ∀ (i : Fin r) (j : Fin m), |B i j| ≤ U i i)
    (hsolve : ∀ (i : Fin r) (j : Fin m),
      ∑ k : Fin r, U i k * W k j = B i j) :
    ∑ j : Fin m, ∑ i : Fin r, W i j ^ 2 ≤
      (m : ℝ) * (((4 : ℝ) ^ r - 1) / 3) :=
  complete_pivoting_w_bound U B W hupper hdiag_pos hentry hB hsolve

/-- **Lemma 10.13 instantiated on the complete-pivoting factor**: for any
    pivoted Cholesky factor `R` satisfying the (10.13) column-tail
    invariant (as produced by `psd_pivoted_cholesky_exists_tail`), the
    implicit matrix `W = R₁₁⁻¹ R₁₂` exists — each border column of `R₁₂`
    is solved exactly against the leading `r × r` block — and satisfies
    Higham's bound `‖W‖_F² ≤ (n − r)(4^r − 1)/3`. -/
theorem higham10_13_pivoted_w_frobenius_bound {n : ℕ}
    {A R : Fin n → Fin n → ℝ} {σ : Fin n → Fin n} {r : ℕ}
    (spec : PivotedCholeskySpec n A R σ r) (hr : r ≤ n)
    (htail : ∀ k j : Fin n, k.val ≤ j.val →
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
        R i j ^ 2) ≤ R k k ^ 2) :
    ∃ W : Fin r → Fin (n - r) → ℝ,
      (∀ (i : Fin r) (j : Fin (n - r)),
        ∑ k : Fin r, R (Fin.castLE hr i) (Fin.castLE hr k) * W k j =
          R (Fin.castLE hr i) ⟨r + j.val, by omega⟩) ∧
      ∑ j : Fin (n - r), ∑ i : Fin r, W i j ^ 2 ≤
        ((n - r : ℕ) : ℝ) * (((4 : ℝ) ^ r - 1) / 3) := by
  have hdiag_nonneg : ∀ i : Fin n, 0 ≤ R i i := by
    intro i
    rcases Nat.lt_or_ge i.val r with hlt | hge
    · exact (spec.R_diag_pos i hlt).le
    · rw [spec.R_rank_zero i i hge]
  have hdom := tail_invariant_entry_le hdiag_nonneg htail
  set U : Fin r → Fin r → ℝ :=
    fun i k => R (Fin.castLE hr i) (Fin.castLE hr k) with hU
  set B : Fin r → Fin (n - r) → ℝ :=
    fun i j => R (Fin.castLE hr i) ⟨r + j.val, by omega⟩ with hB
  have hupper : ∀ i j : Fin r, j.val < i.val → U i j = 0 :=
    fun i j hij => spec.R_upper _ _ hij
  have hdiag_pos : ∀ i : Fin r, 0 < U i i :=
    fun i => spec.R_diag_pos _ i.isLt
  have hentry : ∀ i j : Fin r, i.val ≤ j.val → |U i j| ≤ U i i :=
    fun i j hij => hdom _ _ hij
  have hBdom : ∀ (i : Fin r) (j : Fin (n - r)), |B i j| ≤ U i i :=
    fun i j => hdom _ _ (by
      show i.val ≤ r + j.val
      exact le_trans i.isLt.le (Nat.le_add_right r j.val))
  have hsol : ∀ j : Fin (n - r), ∃ y : Fin r → ℝ,
      ∀ i : Fin r, ∑ k : Fin r, U i k * y k = B i j :=
    fun j => upperTriangular_solve_exists r U hupper
      (fun i => (hdiag_pos i).ne') (fun i => B i j)
  choose Wcol hWcol using hsol
  refine ⟨fun i j => Wcol j i, fun i j => hWcol j i, ?_⟩
  exact complete_pivoting_w_bound U B (fun i j => Wcol j i)
    hupper hdiag_pos hentry hBdom (fun i j => hWcol j i)

end NumStability
