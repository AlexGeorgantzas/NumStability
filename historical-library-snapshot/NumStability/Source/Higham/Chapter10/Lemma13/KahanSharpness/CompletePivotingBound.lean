import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound

/-!
# Chapter10 Lemma13 KahanSharpness CompletePivotingBound

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyPSD` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Squared-sum of the growth bounds**: entries bounded by `2^{r-1-i}`
    have squared sum at most `(4^r − 1)/3` (geometric sum, Higham
    §10.3, proof of Lemma 10.13). -/
lemma sq_sum_pow_two_bound {r : ℕ} (w : Fin r → ℝ)
    (h : ∀ i : Fin r, |w i| ≤ 2 ^ (r - 1 - i.val)) :
    ∑ i : Fin r, w i ^ 2 ≤ ((4 : ℝ) ^ r - 1) / 3 := by
  have hterm : ∀ i : Fin r, w i ^ 2 ≤ (4 : ℝ) ^ (r - 1 - i.val) := by
    intro i
    obtain ⟨hlo, hhi⟩ := abs_le.mp (h i)
    have hsq : w i ^ 2 ≤ ((2 : ℝ) ^ (r - 1 - i.val)) ^ 2 :=
      sq_le_sq' hlo hhi
    calc w i ^ 2 ≤ ((2 : ℝ) ^ (r - 1 - i.val)) ^ 2 := hsq
      _ = ((2 : ℝ) ^ 2) ^ (r - 1 - i.val) := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = (4 : ℝ) ^ (r - 1 - i.val) := by norm_num
  have hrev : ∑ i : Fin r, (4 : ℝ) ^ (r - 1 - i.val) =
      ∑ i : Fin r, (4 : ℝ) ^ i.val := by
    apply Fintype.sum_bijective (Fin.rev) (Fin.rev_involutive.bijective)
    intro i
    rw [Fin.val_rev]
    congr 1
    omega
  have hgeom : ∑ i : Fin r, (4 : ℝ) ^ i.val = ((4 : ℝ) ^ r - 1) / 3 := by
    rw [Fin.sum_univ_eq_sum_range (fun t => (4 : ℝ) ^ t) r,
      geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1) r,
      show (4 : ℝ) - 1 = 3 by norm_num]
  calc ∑ i : Fin r, w i ^ 2
      ≤ ∑ i : Fin r, (4 : ℝ) ^ (r - 1 - i.val) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ((4 : ℝ) ^ r - 1) / 3 := by rw [hrev, hgeom]

/-- **Complete-pivoting bound on ‖W‖_F²** (Higham §10.3, Lemma 10.13,
    display (10.19)): if the `r × r` upper-triangular block `U` has
    positive diagonal and every row pivot-dominated on and right of the
    diagonal (as `tail_invariant_entry_le` extracts from the (10.13)
    column-tail invariant of complete pivoting), and `W` solves
    `U W = B` column-by-column with `|B i j| ≤ U i i`, then
    `‖W‖_F² ≤ m (4^r − 1)/3` — Higham's `(n − r)(4^r − 1)/3` with
    `m = n − r` border columns. -/
theorem complete_pivoting_w_bound {r m : ℕ} (U : Fin r → Fin r → ℝ)
    (B W : Fin r → Fin m → ℝ)
    (hupper : ∀ i j : Fin r, j.val < i.val → U i j = 0)
    (hdiag_pos : ∀ i : Fin r, 0 < U i i)
    (hentry : ∀ i j : Fin r, i.val ≤ j.val → |U i j| ≤ U i i)
    (hB : ∀ (i : Fin r) (j : Fin m), |B i j| ≤ U i i)
    (hsolve : ∀ (i : Fin r) (j : Fin m),
      ∑ k : Fin r, U i k * W k j = B i j) :
    ∑ j : Fin m, ∑ i : Fin r, W i j ^ 2 ≤
      (m : ℝ) * (((4 : ℝ) ^ r - 1) / 3) := by
  have hcol : ∀ j : Fin m, ∑ i : Fin r, W i j ^ 2 ≤
      ((4 : ℝ) ^ r - 1) / 3 := fun j =>
    sq_sum_pow_two_bound (fun i => W i j)
      (normalized_solve_growth U (fun i => B i j) (fun i => W i j)
        hupper hdiag_pos hentry (fun i => hB i j) (fun i => hsolve i j))
  calc ∑ j : Fin m, ∑ i : Fin r, W i j ^ 2
      ≤ ∑ _j : Fin m, ((4 : ℝ) ^ r - 1) / 3 :=
        Finset.sum_le_sum fun j _ => hcol j
    _ = (m : ℝ) * (((4 : ℝ) ^ r - 1) / 3) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end NumStability
