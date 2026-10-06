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
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter10 Section03 PositiveSemidefinite Existence

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyPSD` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Schur complement of PSD is PSD** (Higham §10.3, Lemma 10.11).

    If A is positive semidefinite with A₀₀ > 0, then the Schur complement
    S = A₂₂ − A₂₁ A₁₁⁻¹ A₁₂ is also positive semidefinite.

    Proof: y^T S y = x^T A x where x₀ = −(a^T y)/a₁₁, x_{i+1} = yᵢ.
    Since A is PSD, x^T A x ≥ 0, so y^T S y ≥ 0 for all y. -/
lemma schur_psd {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hPSD : IsPosSemiDef (m + 1) A) (ha₁₁ : 0 < A 0 0) :
    IsPosSemiDef m (fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) := by
  have ha_ne : A 0 0 ≠ 0 := ne_of_gt ha₁₁
  constructor
  · intro i j; show A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0 =
      A j.succ i.succ - A 0 j.succ * A 0 i.succ / A 0 0
    rw [hPSD.1 i.succ j.succ, hPSD.1 0 i.succ, hPSD.1 0 j.succ]; ring
  · intro y
    set t := ∑ j : Fin m, A 0 j.succ * y j
    set Q := ∑ i : Fin m, ∑ j : Fin m, y i * A i.succ j.succ * y j
    set x : Fin (m + 1) → ℝ := Fin.cons (-t / A 0 0) y
    have hpsd_x := hPSD.2 x
    suffices heq :
        ∑ i : Fin m, ∑ j : Fin m, y i *
          (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
        ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * A i j * x j by linarith
    have ht' : ∑ i : Fin m, y i * A 0 i.succ = t := by
      show ∑ i, y i * A 0 i.succ = ∑ j, A 0 j.succ * y j; congr 1; ext i; ring
    -- LHS = Q - t²/A₀₀
    have lhs_eq : ∑ i : Fin m, ∑ j : Fin m, y i *
        (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
        Q - t * t / A 0 0 := by
      simp_rw [show ∀ (i j : Fin m), y i *
          (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
          y i * A i.succ j.succ * y j -
          (y i * A 0 i.succ) * (A 0 j.succ * y j) / A 0 0
          from fun i j => by ring]
      simp_rw [Finset.sum_sub_distrib]
      congr 1
      simp_rw [← Finset.sum_div]
      congr 1
      simp_rw [← Finset.mul_sum]
      simp_rw [← Finset.sum_mul]
      rw [ht']
    -- RHS = Q - t²/A₀₀
    have rhs_eq : ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * A i j * x j =
        Q - t * t / A 0 0 := by
      rw [Fin.sum_univ_succ]
      simp only [x, Fin.cons_zero, Fin.cons_succ]
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      simp_rw [show ∀ j : Fin m, (-t / A 0 0) * A 0 j.succ * y j =
          (-t / A 0 0) * (A 0 j.succ * y j) from fun j => by ring]
      rw [← Finset.mul_sum]
      simp_rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ,
        show ∀ i : Fin m, A i.succ 0 = A 0 i.succ from fun i => hPSD.1 i.succ 0]
      simp_rw [Finset.sum_add_distrib]
      rw [← Finset.sum_mul, ht']
      field_simp; ring
    rw [lhs_eq, rhs_eq]

/-- **Schur diagonal domination** (equation (10.13) foundation): each
    Schur-complement diagonal entry is at most the corresponding original
    diagonal entry, hence — under the complete-pivoting choice — at most
    the current pivot.  This is the monotonicity that propagates the
    per-stage maximality into the (10.13) display. -/
lemma schur_diag_le_pivot {m : ℕ} (B : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hB00 : 0 < B 0 0)
    (hmax : ∀ i : Fin (m + 1), B i i ≤ B 0 0) (i : Fin m) :
    B i.succ i.succ - B 0 i.succ * B 0 i.succ / B 0 0 ≤ B 0 0 := by
  have hsub : 0 ≤ B 0 i.succ * B 0 i.succ / B 0 0 :=
    div_nonneg (mul_self_nonneg _) hB00.le
  linarith [hmax i.succ]

/-- **Column-tail identity for the pivoted factor** (equation (10.13)
    foundation, spec level): the tail of a squared column of `R` from row
    `k` down equals the permuted diagonal entry minus the head — i.e. the
    stage-`k` Schur diagonal in factored form.  Combined with the
    stage-domination invariant this yields the display (10.13). -/
lemma pivoted_spec_column_split {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (k j : Fin n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
      R i j ^ 2) =
    A (σ j) (σ j) -
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val),
        R i j ^ 2 := by
  have hprod := hspec.product_eq j j
  have hsq : ∑ i : Fin n, R i j * R i j = ∑ i : Fin n, R i j ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hsq] at hprod
  have hsplit : ∑ i : Fin n, R i j ^ 2 =
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k.val),
        R i j ^ 2) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
        R i j ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin n => i.val < k.val) (fun i => R i j ^ 2)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp
  linarith [hprod, hsplit]

/-- The leading diagonal entry of a pivoted factor squares to the
    permuted leading diagonal of `A` (product equation at `(0,0)` with
    upper triangularity). -/
lemma pivoted_spec_head_sq {m : ℕ} {A R : Fin (m + 1) → Fin (m + 1) → ℝ}
    {σ : Fin (m + 1) → Fin (m + 1)} {r : ℕ}
    (hspec : PivotedCholeskySpec (m + 1) A R σ r) :
    R 0 0 * R 0 0 = A (σ 0) (σ 0) := by
  have h := hspec.product_eq 0 0
  rw [Fin.sum_univ_succ] at h
  rw [show ∑ i : Fin m, R i.succ 0 * R i.succ 0 = 0 from
    Finset.sum_eq_zero fun i _ => by
      rw [hspec.R_upper i.succ 0 (by simp), zero_mul]] at h
  linarith

/-- Diagonal entries of a pivoted factor are nonnegative. -/
lemma pivoted_spec_diag_nonneg {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (i : Fin n) :
    0 ≤ R i i := by
  rcases Nat.lt_or_ge i.val r with h | h
  · exact (hspec.R_diag_pos i h).le
  · rw [hspec.R_rank_zero i i h]

/-- **Rank invariance of the pivoted certificate** (Theorem 10.9(b),
    `r = rank` bridge, part 1): the matrix rank of `A` equals the rank of
    the pivoted factor `R` — `rank A = rank(ΠᵀAΠ) = rank(RᵀR) = rank R`.
    The remaining identification `rank R = r` (triangular rank count) is
    a separate row. -/
theorem pivoted_spec_rank_eq {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) :
    (Matrix.of A).rank = (Matrix.of R).rank := by
  let eσ : Fin n ≃ Fin n := Equiv.ofBijective σ hspec.perm
  have hsub : (Matrix.of A).submatrix ⇑eσ ⇑eσ =
      (Matrix.of R).transpose * Matrix.of R := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply]
    show A (σ i) (σ j) = ∑ k : Fin n, R k i * R k j
    rw [← hspec.product_eq i j]
  calc (Matrix.of A).rank
      = ((Matrix.of A).submatrix ⇑eσ ⇑eσ).rank :=
        (Matrix.rank_submatrix (Matrix.of A) eσ eσ).symm
    _ = ((Matrix.of R).transpose * Matrix.of R).rank := by rw [hsub]
    _ = (Matrix.of R).rank :=
        Matrix.rank_transpose_mul_self (Matrix.of R)

/-- **The leading `r × r` block of a pivoted factor is a determinant
    unit** (Theorem 10.9(b), `rank R = r` bridge, `≥` side): upper
    triangular with positive diagonal, so its determinant is the product
    of the positive pivots. -/
theorem pivoted_leading_block_isUnit_det {n : ℕ}
    {A R : Fin n → Fin n → ℝ} {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (hr : r ≤ n) :
    IsUnit (Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).det := by
  have hBT : (Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).BlockTriangular id := by
    intro i j hij
    exact hspec.R_upper _ _ hij
  rw [Matrix.det_of_upperTriangular hBT]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (hspec.R_diag_pos ⟨i.val, by omega⟩ i.isLt).ne'

/-- **Triangular rank count** (Theorem 10.9(b), `r = rank` bridge,
    part 2): the pivoted factor has matrix rank exactly `r` — the zero
    rows give `≤` and the unit leading block gives `≥`, both through
    selection-matrix factorizations and `rank_mul_le`. -/
theorem pivoted_spec_rank_R {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (hr : r ≤ n) :
    (Matrix.of R).rank = r := by
  set Rtop : Matrix (Fin r) (Fin n) ℝ :=
    Matrix.of (fun k j => R ⟨k.val, by omega⟩ j) with hRtop
  set E : Matrix (Fin n) (Fin r) ℝ :=
    Matrix.of (fun i k => if i.val = k.val then (1:ℝ) else 0) with hE
  set E' : Matrix (Fin r) (Fin n) ℝ :=
    Matrix.of (fun k i => if k.val = i.val then (1:ℝ) else 0) with hE'
  set F : Matrix (Fin n) (Fin r) ℝ :=
    Matrix.of (fun j k => if j.val = k.val then (1:ℝ) else 0) with hF
  have hfac1 : Matrix.of R = E * Rtop := by
    ext i j
    show R i j = ∑ k : Fin r,
      (if i.val = k.val then (1:ℝ) else 0) * R ⟨k.val, by omega⟩ j
    by_cases hi : i.val < r
    · rw [Finset.sum_eq_single (⟨i.val, hi⟩ : Fin r)]
      · rw [if_pos rfl, one_mul]
      · intro b _ hb
        rw [if_neg (fun hbe => hb (Fin.ext hbe.symm)), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hspec.R_rank_zero i j (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (by omega), zero_mul]
  have hfac2 : Rtop = E' * Matrix.of R := by
    ext k j
    show R ⟨k.val, by omega⟩ j = ∑ i : Fin n,
      (if k.val = i.val then (1:ℝ) else 0) * R i j
    rw [Finset.sum_eq_single (⟨k.val, by omega⟩ : Fin n)]
    · rw [if_pos rfl, one_mul]
    · intro b _ hb
      rw [if_neg (fun hbe => hb (Fin.ext hbe.symm)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfac3 : Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) = Rtop * F := by
    ext k k'
    show R ⟨k.val, by omega⟩ ⟨k'.val, by omega⟩ = ∑ j : Fin n,
      R ⟨k.val, by omega⟩ j * (if j.val = k'.val then (1:ℝ) else 0)
    rw [Finset.sum_eq_single (⟨k'.val, by omega⟩ : Fin n)]
    · rw [if_pos rfl, mul_one]
    · intro b _ hb
      rw [if_neg (fun hbe => hb (Fin.ext hbe)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hMrank : (Matrix.of (fun i j : Fin r =>
      R ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).rank = r := by
    rw [Matrix.rank_of_isUnit _
      ((Matrix.isUnit_iff_isUnit_det _).mpr
        (pivoted_leading_block_isUnit_det hspec hr))]
    simp
  have h1 : (Matrix.of R).rank ≤ Rtop.rank := by
    rw [hfac1]
    exact Matrix.rank_mul_le_right E Rtop
  have h2 : Rtop.rank ≤ (Matrix.of R).rank := by
    rw [hfac2]
    exact Matrix.rank_mul_le_right E' (Matrix.of R)
  have h3 : r ≤ Rtop.rank := by
    have hle := Matrix.rank_mul_le_left Rtop F
    rw [← hfac3, hMrank] at hle
    exact hle
  have h4 : Rtop.rank ≤ r := by
    have := Matrix.rank_le_card_height Rtop
    simpa using this
  omega

/-- **Theorem 10.9(b), rank identification**: for any pivoted certificate
    with `r ≤ n`, the parameter `r` is the matrix rank of `A` — closing
    the "positive semidefinite of rank r" reading of the source row. -/
theorem pivoted_spec_rank_eq_r {n : ℕ} {A R : Fin n → Fin n → ℝ}
    {σ : Fin n → Fin n} {r : ℕ}
    (hspec : PivotedCholeskySpec n A R σ r) (hr : r ≤ n) :
    (Matrix.of A).rank = r := by
  rw [pivoted_spec_rank_eq hspec, pivoted_spec_rank_R hspec hr]

end NumStability
