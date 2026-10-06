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
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis

/-!
# Results

Canonical destination for 4 declaration(s) relocated from
`NumStability.Algorithms.Cholesky.CholeskyPSD` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- Two-point evaluation of the quadratic form: for `x` supported on
    `{i, j}` with `i ≠ j`, `xᵀAx = t²·a_ii + ts·(a_ij + a_ji) + s²·a_jj`. -/
private lemma quadForm_two_point {n : ℕ} (A : Fin n → Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (t s : ℝ) :
    ∑ k : Fin n, ∑ l : Fin n,
      (if k = i then t else if k = j then s else 0) * A k l *
      (if l = i then t else if l = j then s else 0) =
    t ^ 2 * A i i + t * s * (A i j + A j i) + s ^ 2 * A j j := by
  have hrow : ∀ k : Fin n,
      ∑ l : Fin n, (if k = i then t else if k = j then s else 0) * A k l *
        (if l = i then t else if l = j then s else 0) =
      (if k = i then t else if k = j then s else 0) *
        (A k i * t + A k j * s) := by
    intro k
    rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i)
      (Finset.mem_univ j) hij ?_]
    · rw [if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
      ring
    · intro l _ hl
      rcases hl with ⟨hli, hlj⟩
      simp [hli, hlj]
  rw [Finset.sum_congr rfl fun k _ => hrow k]
  rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i)
    (Finset.mem_univ j) hij ?_]
  · rw [if_pos rfl, if_neg (Ne.symm hij), if_pos rfl]
    ring
  · intro k _ hk
    rcases hk with ⟨hki, hkj⟩
    simp [hki, hkj]

/-- **All diagonal entries zero forces the zero matrix** for PSD matrices
    (Theorem 10.9(b) recursion, termination case): with every `a_ii = 0`,
    the two-point quadratic form reduces to `2ts·a_ij ≥ 0` for all
    `t, s`, so every entry vanishes. -/
lemma psd_all_diag_zero {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (hdiag : ∀ i, A i i = 0) :
    ∀ i j : Fin n, A i j = 0 := by
  intro i j
  by_cases hij : i = j
  · rw [hij]; exact hdiag j
  · have hpos := hPSD.2
      (fun k => if k = i then (1:ℝ) else if k = j then 1 else 0)
    have hneg := hPSD.2
      (fun k => if k = i then (1:ℝ) else if k = j then (-1) else 0)
    rw [quadForm_two_point A i j hij 1 1] at hpos
    rw [quadForm_two_point A i j hij 1 (-1)] at hneg
    have hsym := hPSD.1 i j
    rw [hdiag i, hdiag j] at hpos hneg
    nlinarith [hpos, hneg, hsym]

/-- **PSD off-diagonal domination, non-strict form** (Problem 10.1 in
    PSD strength): `|a_ij| ≤ √(a_ii) √(a_jj)`. -/
lemma psd_abs_entry_le_sqrt_diag {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (i j : Fin n) :
    |A i j| ≤ Real.sqrt (A i i) * Real.sqrt (A j j) := by
  have hdi := isPosSemiDef_diag_nonneg A hPSD i
  have hdj := isPosSemiDef_diag_nonneg A hPSD j
  rcases eq_or_ne i j with rfl | hij
  · rw [abs_of_nonneg hdi]
    exact (Real.mul_self_sqrt hdi).ge
  · set u : ℝ := Real.sqrt (A i i) with hu
    set w : ℝ := Real.sqrt (A j j) with hw
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hw0 : 0 ≤ w := Real.sqrt_nonneg _
    have hu2 : u ^ 2 = A i i := Real.sq_sqrt hdi
    have hw2 : w ^ 2 = A j j := Real.sq_sqrt hdj
    have hsym := hPSD.1 i j
    have hqf : ∀ t s : ℝ, 0 ≤ t ^ 2 * A i i + t * s * (2 * A i j) +
        s ^ 2 * A j j := by
      intro t s
      have h := hPSD.2 (fun k => if k = i then t else
        if k = j then s else 0)
      rw [quadForm_two_point A i j hij t s] at h
      have h2 : A i j + A j i = 2 * A i j := by rw [← hsym]; ring
      rw [h2] at h
      linarith [h]
    -- zero-diagonal cases force a zero entry
    by_cases hzi : A i i = 0
    · have hAij : A i j = 0 := by
        by_contra hne
        have h := hqf (-(A j j + 1) / (2 * A i j)) 1
        rw [hzi] at h
        have h2 : (-(A j j + 1) / (2 * A i j)) * 1 * (2 * A i j) =
            -(A j j + 1) := by
          field_simp [hne]
        nlinarith [h, h2]
      rw [hAij, abs_zero]
      positivity
    by_cases hzj : A j j = 0
    · have hAij : A i j = 0 := by
        by_contra hne
        have h := hqf 1 (-(A i i + 1) / (2 * A i j))
        rw [hzj] at h
        have h2 : (1 : ℝ) * (-(A i i + 1) / (2 * A i j)) *
            (2 * A i j) = -(A i i + 1) := by
          field_simp [hne]
        nlinarith [h, h2]
      rw [hAij, abs_zero]
      positivity
    -- positive-diagonal case: evaluate at (w, ±u)
    have hupos : 0 < u := Real.sqrt_pos.mpr (lt_of_le_of_ne hdi
      (Ne.symm hzi))
    have hwpos : 0 < w := Real.sqrt_pos.mpr (lt_of_le_of_ne hdj
      (Ne.symm hzj))
    have hq1 := hqf w u
    have hq2 := hqf w (-u)
    rw [abs_le]
    constructor
    · nlinarith [hq1, hu2, hw2, mul_pos hupos hwpos]
    · nlinarith [hq2, hu2, hw2, mul_pos hupos hwpos]

/-- **PSD entries are dominated by the largest diagonal entry**
    (Higham §10.3, the (10.23)/(10.24) termination engine): if every
    diagonal entry of a PSD matrix is at most `d`, every entry is at
    most `d` in absolute value. Applied to the exact trailing Schur
    complement at termination, this converts the pivoted algorithm's
    stopping test `max diag ≤ tol` into the entrywise trailing residual
    bound. -/
lemma psd_abs_entry_le_maxdiag {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (d : ℝ)
    (hd : ∀ i : Fin n, A i i ≤ d) (i j : Fin n) :
    |A i j| ≤ d := by
  have hdi := isPosSemiDef_diag_nonneg A hPSD i
  have hd0 : 0 ≤ d := le_trans hdi (hd i)
  calc |A i j| ≤ Real.sqrt (A i i) * Real.sqrt (A j j) :=
        psd_abs_entry_le_sqrt_diag A hPSD i j
    _ ≤ Real.sqrt d * Real.sqrt d :=
        mul_le_mul (Real.sqrt_le_sqrt (hd i))
          (Real.sqrt_le_sqrt (hd j)) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = d := Real.mul_self_sqrt hd0

end NumStability
