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

/-!
# Chapter10 Section03 PositiveSemidefinite WNormBound

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyPSD` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Abstract W-norm bound interface** (Higham §10.3, Lemma 10.12). -/
theorem w_norm_bound_from_cond
    (W_norm κ_A11 : ℝ) (_hκ : 0 ≤ κ_A11)
    (hW : W_norm ^ 2 ≤ κ_A11) :
    W_norm ^ 2 ≤ κ_A11 :=
  hW

/-- **Abstract back-substitution growth** (Lemma 10.13 engine): if each
    `|w i|` is bounded by `1` plus the sum of the later `|w j|` — the
    pivot-normalized form of the triangular solve under the (10.13)
    bounds — then `|w i| ≤ 2^{r-1-i}`, by downward induction with the
    geometric sum `1 + (2^t − 1) = 2^t`. -/
lemma backsub_growth {r : ℕ} (w : Fin r → ℝ)
    (hrec : ∀ i : Fin r, |w i| ≤ 1 +
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val), |w j|) :
    ∀ i : Fin r, |w i| ≤ 2 ^ (r - 1 - i.val) := by
  have H : ∀ (t : ℕ) (i : Fin r), r - 1 - i.val = t →
      |w i| ≤ 2 ^ t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t IH =>
      intro i hit
      have himg : (Finset.univ.filter
          (fun j : Fin r => i.val < j.val)).image
          (fun j : Fin r => r - 1 - j.val) = Finset.range t := by
        ext k
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_range]
        constructor
        · rintro ⟨j, hj, rfl⟩
          have := j.isLt
          omega
        · intro hk
          refine ⟨⟨r - 1 - k, by omega⟩, by simp; omega, by simp; omega⟩
      have hinj : ∀ a ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val),
          ∀ b ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val),
          r - 1 - a.val = r - 1 - b.val → a = b := by
        intro a ha b hb hab
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        have := a.isLt
        have := b.isLt
        exact Fin.ext (by omega)
      have hsum_exp : ∑ j ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val), (2:ℝ) ^ (r - 1 - j.val) =
          ∑ k ∈ Finset.range t, (2:ℝ) ^ k := by
        rw [← himg, Finset.sum_image hinj]
      calc |w i| ≤ 1 + ∑ j ∈ Finset.univ.filter
            (fun j : Fin r => i.val < j.val), |w j| := hrec i
        _ ≤ 1 + ∑ j ∈ Finset.univ.filter
            (fun j : Fin r => i.val < j.val),
            (2:ℝ) ^ (r - 1 - j.val) := by
            gcongr with j hj
            simp only [Finset.mem_filter, Finset.mem_univ,
              true_and] at hj
            exact IH (r - 1 - j.val) (by have := j.isLt; omega) j rfl
        _ = 1 + ∑ k ∈ Finset.range t, (2:ℝ) ^ k := by rw [hsum_exp]
        _ = 2 ^ t := by
            rw [geom_sum_eq (by norm_num : (2:ℝ) ≠ 1) t]
            ring
  intro i
  exact H (r - 1 - i.val) i rfl

/-- **Entry domination from the column-tail invariant** (Lemma 10.13
    wiring): under the (10.13) invariant, every entry on or right of the
    diagonal is dominated in absolute value by its row pivot. -/
lemma tail_invariant_entry_le {n : ℕ} {R : Fin n → Fin n → ℝ}
    (hdiag_nonneg : ∀ i : Fin n, 0 ≤ R i i)
    (htail : ∀ k j : Fin n, k.val ≤ j.val →
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
        R i j ^ 2) ≤ R k k ^ 2)
    (k j : Fin n) (hkj : k.val ≤ j.val) :
    |R k j| ≤ R k k := by
  have hmem : k ∈ Finset.univ.filter
      (fun i : Fin n => k.val ≤ i.val) := by
    simp
  have hsingle : R k j ^ 2 ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
        R i j ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (R i j)) hmem
  have hsq : R k j ^ 2 ≤ R k k ^ 2 :=
    le_trans hsingle (htail k j hkj)
  nlinarith [abs_nonneg (R k j), sq_abs (R k j), hdiag_nonneg k]

/-- **Normalized triangular-solve growth** (Lemma 10.13 core): a solve
    `Uw = b` against an upper-triangular matrix whose every row is
    pivot-dominated (`|U i j| ≤ U i i`, `|b i| ≤ U i i` — supplied by the
    (10.13) invariant through `tail_invariant_entry_le`) has solution
    entries bounded by `2^{r-1-i}`. -/
theorem normalized_solve_growth {r : ℕ} (U : Fin r → Fin r → ℝ)
    (b w : Fin r → ℝ)
    (hupper : ∀ i j : Fin r, j.val < i.val → U i j = 0)
    (hdiag_pos : ∀ i : Fin r, 0 < U i i)
    (hentry : ∀ i j : Fin r, i.val ≤ j.val → |U i j| ≤ U i i)
    (hb : ∀ i : Fin r, |b i| ≤ U i i)
    (hsolve : ∀ i : Fin r, ∑ j : Fin r, U i j * w j = b i) :
    ∀ i : Fin r, |w i| ≤ 2 ^ (r - 1 - i.val) := by
  apply backsub_growth
  intro i
  have hpos := hdiag_pos i
  -- split the solve row at the diagonal: below-diagonal entries vanish
  have hle_part : ∑ j ∈ Finset.univ.filter
      (fun j : Fin r => ¬ i.val < j.val), U i j * w j =
      U i i * w i := by
    refine Finset.sum_eq_single_of_mem i (by simp) ?_
    intro j hj hji
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.not_lt] at hj
    have hjlt : j.val < i.val := by
      rcases Nat.lt_or_eq_of_le hj with h' | h'
      · exact h'
      · exact absurd (Fin.ext h') hji
    rw [hupper i j hjlt, zero_mul]
  have hsplit : U i i * w i +
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val),
        U i j * w j = b i := by
    have h := hsolve i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin r => i.val < j.val) (fun j => U i j * w j),
      hle_part] at h
    linarith [h]
  -- bound the absolute tail sum by pivot-scaled solution magnitudes
  have hsum_abs : |∑ j ∈ Finset.univ.filter
      (fun j : Fin r => i.val < j.val), U i j * w j| ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val),
        U i i * |w j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum ?_)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hentry i j hj.le) (abs_nonneg _)
  -- triangle inequality on the rearranged pivot equation
  have htri : |U i i * w i| ≤ |b i| + |∑ j ∈ Finset.univ.filter
      (fun j : Fin r => i.val < j.val), U i j * w j| := by
    have heq : U i i * w i = b i - ∑ j ∈ Finset.univ.filter
        (fun j : Fin r => i.val < j.val), U i j * w j := by
      linarith [hsplit]
    rw [heq]
    have h1 := abs_add_le (b i) (-(∑ j ∈ Finset.univ.filter
      (fun j : Fin r => i.val < j.val), U i j * w j))
    rw [abs_neg, ← sub_eq_add_neg] at h1
    exact h1
  -- assemble and divide by the positive pivot
  have hwi : U i i * |w i| ≤ U i i * (1 +
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => i.val < j.val),
        |w j|) := by
    have habs : U i i * |w i| = |U i i * w i| := by
      rw [abs_mul, abs_of_pos hpos]
    rw [habs, mul_add, mul_one, Finset.mul_sum]
    calc |U i i * w i|
        ≤ |b i| + |∑ j ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val), U i j * w j| := htri
      _ ≤ U i i + ∑ j ∈ Finset.univ.filter
          (fun j : Fin r => i.val < j.val), U i i * |w j| :=
          add_le_add (hb i) hsum_abs
  exact le_of_mul_le_mul_left hwi hpos

end NumStability
