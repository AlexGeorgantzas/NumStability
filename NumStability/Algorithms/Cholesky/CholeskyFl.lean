-- Algorithms/Cholesky/CholeskyFl.lean
--
-- Concrete floating-point Cholesky foundations (Higham §10.1, 2nd ed.,
-- Algorithm 10.2 / Theorem 10.3, pp. 197-199).
--
-- Algorithm 10.2 computes, for each entry of the upper factor,
--   off-diagonal:  r̂_ij = fl((a_ij − ∑_{k<i} r̂_ki r̂_kj) / r̂_ii)
--   diagonal:      r̂_jj = fl(√(a_jj − ∑_{k<j} r̂_kj²))
-- This file proves the per-entry rounding specifications of these two scalar
-- steps over the standard model, generically in the previously computed
-- entries.  They are the local facts from which the Theorem 10.3 backward
-- error certificate (`CholeskyBackwardError`) is assembled by recursion.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Algorithms.Cholesky.CholeskyDemmel

namespace NumStability

open scoped BigOperators

/-- **Cholesky partial-pivot fold** (Higham §10.1, Algorithm 10.2).

    The sequentially rounded evaluation of `c − ∑_k x k * y k`:
    the common inner expression of both Cholesky entry recurrences, with
    `c` an entry of `A` and `x`, `y` previously computed factor columns. -/
noncomputable def fl_cholSubFold (fp : FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (c : ℝ) : ℝ :=
  Fin.foldl m (fun acc k => fp.fl_sub acc (fp.fl_mul (x k) (y k))) c

/-- **Cholesky partial-pivot fold error** (Higham §10.1, Algorithm 10.2 inner
    expression; standard-model expansion in the style of §8.1, Lemma 8.4).

    The rounded fold equals `c (1 + Θ) − ∑ x k y k (1 + θ k)` with
    `|Θ| ≤ γ_m` and `|θ k| ≤ γ_{m+1}`: each product term absorbs its
    multiplication rounding plus the suffix of subtraction roundings. -/
theorem fl_cholSubFold_error (fp : FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (c : ℝ) (hm1 : gammaValid fp (m + 1)) :
    ∃ (Θ : ℝ) (θ : Fin m → ℝ),
      |Θ| ≤ gamma fp m ∧ (∀ k, |θ k| ≤ gamma fp (m + 1)) ∧
      fl_cholSubFold fp m x y c =
        c * (1 + Θ) - ∑ k : Fin m, x k * y k * (1 + θ k) := by
  have hm : gammaValid fp m := gammaValid_mono fp (Nat.le_succ m) hm1
  have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hm1
  have h1m : gammaValid fp (1 + m) := by rw [Nat.add_comm]; exact hm1
  obtain ⟨Θ, θsub, hΘ, hθsub, hfold⟩ :=
    fl_sub_sum_error_init fp m (fun k => fp.fl_mul (x k) (y k)) c hm
  have hcomb : ∀ k : Fin m, ∃ η : ℝ, |η| ≤ gamma fp (1 + m) ∧
      fp.fl_mul (x k) (y k) * (1 + θsub k) = x k * y k * (1 + η) := by
    intro k
    obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x k) (y k)
    have hδ1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos h1valid)
    obtain ⟨η, hη, heq⟩ := gamma_mul fp 1 m δ (θsub k) hδ1 (hθsub k) h1m
    exact ⟨η, hη, by rw [hmul, mul_assoc, heq]⟩
  choose η hη hηeq using hcomb
  refine ⟨Θ, η, hΘ, ?_, ?_⟩
  · intro k
    have := hη k
    rwa [Nat.add_comm] at this
  · unfold fl_cholSubFold
    rw [hfold]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hηeq k

/-- **Cholesky off-diagonal entry specification** (Higham §10.1,
    Algorithm 10.2 / Theorem 10.3 off-diagonal step).

    The computed entry `r̂ = fl((c − ∑ x k y k)/d)` satisfies
    `d r̂ = (c (1 + Θ) − ∑ x k y k (1 + θ k)) (1 + ρ)` with `|Θ| ≤ γ_m`,
    `|θ k| ≤ γ_{m+1}`, `|ρ| ≤ u`: the entry of `A` is recovered by the
    computed inner product up to the per-operation rounding factors that
    Theorem 10.3 compresses into the `γ_{n+1}` certificate. -/
theorem fl_chol_offdiag_step_error (fp : FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (c d : ℝ) (hd : d ≠ 0)
    (hm1 : gammaValid fp (m + 1)) :
    ∃ (Θ : ℝ) (θ : Fin m → ℝ) (ρ : ℝ),
      |Θ| ≤ gamma fp m ∧ (∀ k, |θ k| ≤ gamma fp (m + 1)) ∧ |ρ| ≤ fp.u ∧
      d * fp.fl_div (fl_cholSubFold fp m x y c) d =
        (c * (1 + Θ) - ∑ k : Fin m, x k * y k * (1 + θ k)) * (1 + ρ) := by
  obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ := fl_cholSubFold_error fp m x y c hm1
  obtain ⟨ρ, hρ, hdiv⟩ := fp.model_div (fl_cholSubFold fp m x y c) d hd
  refine ⟨Θ, θ, ρ, hΘ, hθ, hρ, ?_⟩
  rw [hdiv, ← hfold]
  field_simp

/-- **Cholesky diagonal entry specification** (Higham §10.1,
    Algorithm 10.2 / Theorem 10.3 diagonal step).

    When the rounded partial pivot is nonnegative (the success case governed
    by Theorem 10.7), the computed diagonal entry `r̂ = fl(√(c − ∑ x k²))`
    satisfies `r̂² = (c (1 + Θ) − ∑ x k² (1 + θ k)) (1 + η)` with
    `|Θ| ≤ γ_m`, `|θ k| ≤ γ_{m+1}`, `|η| ≤ 2u + u²`. -/
theorem fl_chol_diag_step_error (fp : FPModel) (m : ℕ)
    (x : Fin m → ℝ) (c : ℝ)
    (hs : 0 ≤ fl_cholSubFold fp m x x c)
    (hm1 : gammaValid fp (m + 1)) :
    ∃ (Θ : ℝ) (θ : Fin m → ℝ) (η : ℝ),
      |Θ| ≤ gamma fp m ∧ (∀ k, |θ k| ≤ gamma fp (m + 1)) ∧
      |η| ≤ 2 * fp.u + fp.u ^ 2 ∧
      (fp.fl_sqrt (fl_cholSubFold fp m x x c)) ^ 2 =
        (c * (1 + Θ) - ∑ k : Fin m, x k * x k * (1 + θ k)) * (1 + η) := by
  obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ := fl_cholSubFold_error fp m x x c hm1
  obtain ⟨η, hη, hsq⟩ := fl_sqrt_sq_backward_error fp _ hs
  exact ⟨Θ, θ, η, hΘ, hθ, hη, by rw [hsq, hfold]⟩

set_option linter.unusedVariables false in
/-- **Algorithm 10.2** (Higham §10.1), entry recursion over `ℕ` indices.

    Column-major evaluation of the upper Cholesky factor:
    `r̂_ij = fl((a_ij − ∑_{k<i} r̂_ki r̂_kj) / r̂_ii)` for `i < j` and
    `r̂_jj = fl(√(a_jj − ∑_{k<j} r̂_kj²))`, with junk value `0` below the
    diagonal and outside the matrix range.  Recursion is well-founded in the
    lexicographic order on (column, row). -/
noncomputable def fl_cholEntry (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : ℕ → ℕ → ℝ
  | i, j =>
    if h : i < n ∧ j < n then
      if hij : i < j then
        fp.fl_div
          (fl_cholSubFold fp i
            (fun k => fl_cholEntry fp n A k.val i)
            (fun k => fl_cholEntry fp n A k.val j)
            (A ⟨i, h.1⟩ ⟨j, h.2⟩))
          (fl_cholEntry fp n A i i)
      else if hji : i = j then
        fp.fl_sqrt
          (fl_cholSubFold fp i
            (fun k => fl_cholEntry fp n A k.val i)
            (fun k => fl_cholEntry fp n A k.val i)
            (A ⟨i, h.1⟩ ⟨i, h.1⟩))
      else 0
    else 0
  termination_by i j => (j, i)
  decreasing_by
  all_goals
    first
      | exact Prod.Lex.left _ _ hij
      | exact Prod.Lex.right _ k.isLt
      | (subst hji; exact Prod.Lex.right _ k.isLt)

/-- **Algorithm 10.2** (Higham §10.1): the computed floating-point Cholesky
    factor `R̂` as a `Fin n` matrix. -/
noncomputable def fl_cholesky (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => fl_cholEntry fp n A i.val j.val

/-- The computed factor is upper triangular: entries strictly below the
    diagonal are the algorithm's junk value `0`. -/
theorem fl_cholesky_strict_lower (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (i j : Fin n) (h : j.val < i.val) :
    fl_cholesky fp n A i j = 0 := by
  unfold fl_cholesky
  rw [fl_cholEntry.eq_1]
  have h1 : ¬ i.val < j.val := by omega
  have h2 : ¬ i.val = j.val := by omega
  simp [i.isLt, j.isLt, h1, h2]

/-- **Algorithm 10.2 off-diagonal recurrence, matrix form**:
    `R̂ i j = fl((A i j − ∑_{k<i} R̂ k i · R̂ k j) / R̂ i i)` for `i < j`. -/
theorem fl_cholesky_offdiag_eq (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (i j : Fin n) (hij : i.val < j.val) :
    fl_cholesky fp n A i j =
      fp.fl_div
        (fl_cholSubFold fp i.val
          (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ i)
          (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ j)
          (A i j))
        (fl_cholesky fp n A i i) := by
  show fl_cholEntry fp n A i.val j.val = _
  rw [fl_cholEntry.eq_1]
  rw [dif_pos (⟨i.isLt, j.isLt⟩ : i.val < n ∧ j.val < n), dif_pos hij]
  rfl

/-- **Algorithm 10.2 diagonal recurrence, matrix form**:
    `R̂ j j = fl(√(A j j − ∑_{k<j} (R̂ k j)²))`. -/
theorem fl_cholesky_diag_eq (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (j : Fin n) :
    fl_cholesky fp n A j j =
      fp.fl_sqrt
        (fl_cholSubFold fp j.val
          (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩ j)
          (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩ j)
          (A j j)) := by
  show fl_cholEntry fp n A j.val j.val = _
  rw [fl_cholEntry.eq_1]
  rw [dif_pos (⟨j.isLt, j.isLt⟩ : j.val < n ∧ j.val < n),
      dif_neg (lt_irrefl j.val), dif_pos rfl]
  rfl

/-- **Factor-level subtraction-fold expansion** (Higham §3.1/§3.4 bookkeeping
    for Algorithm 10.2, uncompressed form).

    Unlike `fl_sub_sum_error_init`, which compresses rounding factors into
    `γ` witnesses, this exposes the actual local subtraction factors:
    the initial accumulator passes through every subtraction, while term `k`
    passes through only the suffix of subtractions from its insertion step.
    This uncompressed form is required for the sharp `γ_{n+1}` constant of
    Theorem 10.3: the factors shared between the accumulator product and each
    term's suffix product cancel when the recurrence is solved for `A i j`. -/
theorem fl_sub_fold_local_factors (fp : FPModel) (m : ℕ)
    (t : Fin m → ℝ) (c : ℝ) :
    ∃ δ : Fin m → ℝ, (∀ s, |δ s| ≤ fp.u) ∧
      Fin.foldl m (fun acc k => fp.fl_sub acc (t k)) c =
        c * ∏ s : Fin m, (1 + δ s) -
          ∑ k : Fin m, t k * sumSuffixErrorProduct m δ k := by
  induction m with
  | zero =>
      exact ⟨fun s => s.elim0, fun s => s.elim0, by simp⟩
  | succ m ih =>
      obtain ⟨δ', hδ', hfold⟩ := ih (fun k => t k.castSucc)
      obtain ⟨δl, hδl, hsub⟩ := fp.model_sub
        (Fin.foldl m (fun acc k => fp.fl_sub acc (t k.castSucc)) c)
        (t (Fin.last m))
      refine ⟨(Fin.snoc δ' δl : Fin (m + 1) → ℝ), ?_, ?_⟩
      · intro s
        refine Fin.lastCases ?_ ?_ s
        · rw [Fin.snoc_last]; exact hδl
        · intro s; rw [Fin.snoc_castSucc]; exact hδ' s
      · have hsuffix_cast : ∀ k : Fin m,
            sumSuffixErrorProduct (m + 1) (Fin.snoc δ' δl) k.castSucc =
              sumSuffixErrorProduct m δ' k * (1 + δl) := by
          intro k
          rw [sumSuffixErrorProduct_eq_prod_if, sumSuffixErrorProduct_eq_prod_if,
              Fin.prod_univ_castSucc]
          congr 1
          · apply Finset.prod_congr rfl
            intro j _
            simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last, Nat.le_of_lt k.isLt]
        have hsuffix_last :
            sumSuffixErrorProduct (m + 1) (Fin.snoc δ' δl) (Fin.last m) =
              1 + δl := by
          rw [sumSuffixErrorProduct_eq_prod_if, Fin.prod_univ_castSucc]
          have h1 : ∀ j : Fin m,
              (if (Fin.last m).val ≤ (j.castSucc).val
                then 1 + (Fin.snoc δ' δl : Fin (m + 1) → ℝ) j.castSucc
                else 1) = 1 := by
            intro j
            rw [if_neg]
            simp only [Fin.val_last, Fin.val_castSucc]
            exact Nat.not_le.mpr j.isLt
          rw [Finset.prod_congr rfl (fun j _ => h1 j)]
          simp [Fin.snoc_last]
        rw [Fin.foldl_succ_last, hsub, hfold,
            Fin.prod_univ_castSucc, Fin.sum_univ_castSucc, hsuffix_last]
        simp only [hsuffix_cast, Fin.snoc_castSucc, Fin.snoc_last]
        have hsum : ∑ k : Fin m,
              t k.castSucc * (sumSuffixErrorProduct m δ' k * (1 + δl)) =
            (∑ k : Fin m, t k.castSucc * sumSuffixErrorProduct m δ' k) *
              (1 + δl) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
        rw [hsum]
        ring

/-- **Algorithm 10.2 locality**: entries of the computed factor with both
    indices below `k` depend only on the leading `k × k` block of `A`.
    This is the formal content of "consider Algorithm 10.2 with `n`
    replaced by `k`" in the Theorem 10.7 induction (Higham p. 200). -/
theorem fl_cholEntry_leading_principal (fp : FPModel) {n k : ℕ}
    (hk : k ≤ n) (A : Fin n → Fin n → ℝ) :
    ∀ i j : ℕ, i < k → j < k →
      fl_cholEntry fp n A i j =
        fl_cholEntry fp k
          (fun i' j' => A ⟨i'.val, by omega⟩ ⟨j'.val, by omega⟩) i j := by
  intro i j
  induction i, j using fl_cholEntry.induct (n := n) with
  | case1 i j h hij ihx ihy ihd =>
      intro hi hj
      have hx : (fun k' : Fin i => fl_cholEntry fp n A k'.val i) =
          (fun k' : Fin i => fl_cholEntry fp k
            (fun i' j' => A ⟨i'.val, by omega⟩ ⟨j'.val, by omega⟩)
            k'.val i) :=
        funext fun k' => ihx k' (Nat.lt_trans k'.isLt hi) hi
      have hy : (fun k' : Fin i => fl_cholEntry fp n A k'.val j) =
          (fun k' : Fin i => fl_cholEntry fp k
            (fun i' j' => A ⟨i'.val, by omega⟩ ⟨j'.val, by omega⟩)
            k'.val j) :=
        funext fun k' => ihy k' (Nat.lt_trans k'.isLt hi) hj
      have hd := ihd hi hi
      conv_lhs => rw [fl_cholEntry.eq_1]
      conv_rhs => rw [fl_cholEntry.eq_1]
      simp only [dif_pos h, dif_pos (⟨hi, hj⟩ : i < k ∧ j < k),
        dif_pos hij]
      simp only [hx, hy, hd]
  | case2 j h hjj ih =>
      intro hj _
      have hx : (fun k' : Fin j => fl_cholEntry fp n A k'.val j) =
          (fun k' : Fin j => fl_cholEntry fp k
            (fun i' j' => A ⟨i'.val, by omega⟩ ⟨j'.val, by omega⟩)
            k'.val j) :=
        funext fun k' => ih k' (Nat.lt_trans k'.isLt hj) hj
      conv_lhs => rw [fl_cholEntry.eq_1]
      conv_rhs => rw [fl_cholEntry.eq_1]
      simp only [dif_pos h, dif_pos (⟨hj, hj⟩ : j < k ∧ j < k),
        dif_neg hjj]
      simp only [hx]
  | case3 i j h hij hji =>
      intro hi hj
      conv_lhs => rw [fl_cholEntry.eq_1]
      conv_rhs => rw [fl_cholEntry.eq_1]
      simp only [dif_pos h, dif_pos (⟨hi, hj⟩ : i < k ∧ j < k),
        dif_neg hij, dif_neg hji]
  | case4 i j h =>
      intro hi hj
      exact absurd ⟨by omega, by omega⟩ h

/-- **Algorithm 10.2 locality, matrix form**: the computed factor of the
    leading principal block is the leading principal block of the computed
    factor. -/
theorem fl_cholesky_leading_principal (fp : FPModel) {n k : ℕ}
    (hk : k ≤ n) (A : Fin n → Fin n → ℝ) (i j : Fin k) :
    fl_cholesky fp k
      (fun i' j' => A ⟨i'.val, by omega⟩ ⟨j'.val, by omega⟩) i j =
    fl_cholesky fp n A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ :=
  (fl_cholEntry_leading_principal fp hk A i.val j.val i.isLt j.isLt).symm

/-- **Diagonal pivot lower bound** (Theorem 10.7 induction, real-model
    form of the "stage `k` can be completed" step): the rounded partial
    pivot is at least the exact partial pivot minus the accumulated
    rounding mass `γ_{m+1}(|c| + ∑ x_k²)`.  When the exact pivot exceeds
    that mass — which the `λ_min` threshold guarantees — the rounded pivot
    is positive and the stage's square root is real. -/
theorem fl_cholSubFold_pivot_lower (fp : FPModel) (m : ℕ)
    (x : Fin m → ℝ) (c : ℝ) (hm1 : gammaValid fp (m + 1)) :
    c - (∑ k : Fin m, x k ^ 2) -
      gamma fp (m + 1) * (|c| + ∑ k : Fin m, x k ^ 2) ≤
    fl_cholSubFold fp m x x c := by
  obtain ⟨Θ, θ, hΘ, hθ, heq⟩ := fl_cholSubFold_error fp m x x c hm1
  rw [heq]
  have hγnn : 0 ≤ gamma fp (m + 1) := gamma_nonneg fp hm1
  have hγm : gamma fp m ≤ gamma fp (m + 1) :=
    gamma_mono fp (Nat.le_succ m) hm1
  have h1 : c - |c| * gamma fp (m + 1) ≤ c * (1 + Θ) := by
    have habs : |c * Θ| ≤ |c| * gamma fp (m + 1) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (le_trans hΘ hγm) (abs_nonneg c)
    have h := (abs_le.mp habs).1
    nlinarith
  have h2 : ∑ k : Fin m, x k * x k * (1 + θ k) ≤
      (∑ k : Fin m, x k ^ 2) + gamma fp (m + 1) * ∑ k : Fin m, x k ^ 2 := by
    calc ∑ k : Fin m, x k * x k * (1 + θ k)
        ≤ ∑ k : Fin m, x k ^ 2 * (1 + gamma fp (m + 1)) := by
          apply Finset.sum_le_sum
          intro k _
          have hθk := (abs_le.mp (hθ k)).2
          nlinarith [sq_nonneg (x k)]
      _ = (∑ k : Fin m, x k ^ 2) +
          gamma fp (m + 1) * ∑ k : Fin m, x k ^ 2 := by
          rw [← Finset.sum_mul, Finset.sum_mul]
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun k _ => by ring
  nlinarith [h1, h2]

/-- A rounded square root of a positive number is positive (`u < 1`). -/
theorem fl_sqrt_pos (fp : FPModel) (hu : fp.u < 1) (s : ℝ) (hs : 0 < s) :
    0 < fp.fl_sqrt s := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_sqrt s hs.le
  rw [heq]
  have h1 : 0 < 1 + δ := by
    have := (abs_le.mp hδ).1
    linarith
  exact mul_pos (Real.sqrt_pos_of_pos hs) h1

/-- **Exact upper-triangular solvability** (Theorem 10.7 induction,
    "producing a nonsingular R̂" step): an upper-triangular matrix with
    nonzero diagonal solves every right-hand side, via the determinant of
    a block-triangular matrix. -/
theorem upperTriangular_solve_exists (k : ℕ) (U : Fin k → Fin k → ℝ)
    (hupper : ∀ i j : Fin k, j.val < i.val → U i j = 0)
    (hdiag : ∀ i, U i i ≠ 0) (b : Fin k → ℝ) :
    ∃ y : Fin k → ℝ, ∀ i : Fin k, ∑ j : Fin k, U i j * y j = b i := by
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of U
  have hBT : M.BlockTriangular id := fun i j hij => hupper i j hij
  have hdet_unit : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular hBT]
    exact isUnit_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i)
  refine ⟨M⁻¹.mulVec b, ?_⟩
  intro i
  have hsolve : M.mulVec (M⁻¹.mulVec b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet_unit,
      Matrix.one_mulVec]
  calc ∑ j : Fin k, U i j * (M⁻¹.mulVec b) j
      = M.mulVec (M⁻¹.mulVec b) i := rfl
    _ = b i := congrFun hsolve i

/-- **Bordered Gram expansion** (Theorem 10.7 induction): expanding
    `∑_p ((Uy)_p + c_p)²` in the bordered-block quadratic form.  With `y`
    solving `Uy = −c` the left side vanishes, so the computed Gram form of
    the test vector `z = (y, 1)` collapses to zero. -/
theorem bordered_gram_expand (m : ℕ) (U : Fin m → Fin m → ℝ)
    (c : Fin m → ℝ) (y : Fin m → ℝ) :
    ∑ p : Fin m, ((∑ i : Fin m, U p i * y i) + c p) ^ 2 =
      (∑ i : Fin m, ∑ l : Fin m,
        y i * (∑ p : Fin m, U p i * U p l) * y l) +
      2 * (∑ i : Fin m, y i * ∑ p : Fin m, U p i * c p) +
      ∑ p : Fin m, c p ^ 2 := by
  have hexp : ∀ p : Fin m,
      ((∑ i : Fin m, U p i * y i) + c p) ^ 2 =
      (∑ i : Fin m, U p i * y i) * (∑ l : Fin m, U p l * y l) +
        2 * ((∑ i : Fin m, U p i * y i) * c p) + c p ^ 2 := by
    intro p; ring
  rw [Finset.sum_congr rfl fun p _ => hexp p]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · congr 1
    · -- ∑_p (∑_i U pi y i)(∑_l U pl y l) = ∑_i ∑_l y i (∑_p U pi U pl) y l
      have h1 : ∀ p : Fin m,
          (∑ i : Fin m, U p i * y i) * (∑ l : Fin m, U p l * y l) =
          ∑ i : Fin m, ∑ l : Fin m, y i * (U p i * U p l) * y l := by
        intro p
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      rw [Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum, Finset.sum_mul]
    · -- ∑_p 2 (∑_i U pi y i) c p = 2 ∑_i y i ∑_p U pi c p
      rw [Finset.mul_sum]
      rw [show ∑ p : Fin m, 2 * ((∑ i : Fin m, U p i * y i) * c p) =
          ∑ p : Fin m, ∑ i : Fin m, 2 * (y i * (U p i * c p)) from
        Finset.sum_congr rfl fun p _ => by
          rw [Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum, Finset.mul_sum]

/-- **Bordered Gram vanishing**: if `y` solves `Uy = −c` exactly, the
    computed Gram quadratic form of the test vector `(y, 1)` is zero. -/
theorem bordered_gram_zero (m : ℕ) (U : Fin m → Fin m → ℝ)
    (c : Fin m → ℝ) (y : Fin m → ℝ)
    (hy : ∀ p : Fin m, ∑ i : Fin m, U p i * y i = -(c p)) :
    (∑ i : Fin m, ∑ l : Fin m,
      y i * (∑ p : Fin m, U p i * U p l) * y l) +
    2 * (∑ i : Fin m, y i * ∑ p : Fin m, U p i * c p) +
    ∑ p : Fin m, c p ^ 2 = 0 := by
  rw [← bordered_gram_expand m U c y]
  apply Finset.sum_eq_zero
  intro p _
  rw [hy p]
  ring

-- ============================================================
-- §10.1  Sharp solve forms for the Algorithm 10.2 recurrences
--        (Higham Theorem 10.3 per-entry equations, Stewart counters)
-- ============================================================

private lemma one_add_pos_of_abs_le_u {fp : FPModel} {δ : ℝ}
    (h : |δ| ≤ fp.u) (hu : fp.u < 1) : (0 : ℝ) < 1 + δ := by
  have := abs_le.mp h
  linarith [this.1]

private lemma u_lt_one_of_gammaValid_succ {fp : FPModel} {m : ℕ}
    (hm1 : gammaValid fp (m + 1)) : fp.u < 1 := by
  unfold gammaValid at hm1
  push_cast at hm1
  nlinarith [mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ)) fp.u_nonneg]

private lemma counter_one (fp : FPModel) {δ : ℝ} (hδ : |δ| ≤ fp.u) :
    relErrorCounter fp 1 (1 + δ) :=
  ⟨fun _ => δ, fun _ => false, fun _ => hδ, by simp⟩

private lemma counter_plain_prod (fp : FPModel) (m : ℕ) (δ : Fin m → ℝ)
    (hδ : ∀ s, |δ s| ≤ fp.u) :
    relErrorCounter fp m (∏ s : Fin m, (1 + δ s)) :=
  ⟨δ, fun _ => false, hδ, by simp⟩

/-- Prefix product of subtraction factors strictly before insertion step `k`.
    Complements `sumSuffixErrorProduct`: their product is the full factor
    product, which is the cancellation behind the sharp Theorem 10.3
    constant. -/
private lemma suffix_mul_prefix_eq_prod (m : ℕ) (δ : Fin m → ℝ) (k : Fin m) :
    sumSuffixErrorProduct m δ k *
      (∏ j : Fin m, if j.val < k.val then 1 + δ j else 1) =
    ∏ s : Fin m, (1 + δ s) := by
  rw [sumSuffixErrorProduct_eq_prod_if, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rcases Nat.lt_or_ge j.val k.val with h | h
  · rw [if_neg (Nat.not_le.mpr h), if_pos h, one_mul]
  · rw [if_pos h, if_neg (Nat.not_lt.mpr h), mul_one]

/-- The Cholesky per-term local factor `(1 + μ)/(prefix product)` is a
    Stewart counter of `m + 1` factors, hence within `γ_{m+1}` of `1`. -/
private lemma chol_term_factor_bound (fp : FPModel) (m : ℕ)
    (δ : Fin m → ℝ) (μk : ℝ) (k : Fin m)
    (hδ : ∀ s, |δ s| ≤ fp.u) (hμ : |μk| ≤ fp.u)
    (hm1 : gammaValid fp (m + 1)) :
    |(1 + μk) / (∏ j : Fin m, if j.val < k.val then 1 + δ j else 1) - 1| ≤
      gamma fp (m + 1) := by
  have hu : fp.u < 1 := u_lt_one_of_gammaValid_succ hm1
  have hQcnt : relErrorCounter fp m
      (∏ j : Fin m, if j.val < k.val then 1 + δ j else 1) := by
    refine ⟨fun j => if j.val < k.val then δ j else 0, fun _ => false, ?_, ?_⟩
    · intro j
      by_cases h : j.val < k.val
      · simpa [h] using hδ j
      · simpa [h] using fp.u_nonneg
    · simp only [Bool.false_eq_true, if_false]
      apply Finset.prod_congr rfl
      intro j _
      by_cases h : j.val < k.val <;> simp [h]
  have hcnt : relErrorCounter fp (1 + m)
      ((1 + μk) * (1 / ∏ j : Fin m, if j.val < k.val then 1 + δ j else 1)) :=
    relErrorCounter_mul fp 1 m _ _ (counter_one fp hμ)
      (relErrorCounter_inv fp m _ hQcnt hu)
  rw [Nat.add_comm 1 m] at hcnt
  have := relErrorCounter_abs_sub_one_le_gamma fp (m + 1) _ hcnt hm1
  rwa [mul_one_div] at this

/-- **Algorithm 10.2 off-diagonal solve form** (Higham §10.1, Theorem 10.3
    off-diagonal equation, sharp constants).

    The computed entry `r̂ = fl((c − ∑ x k y k)/d)` satisfies
    `d r̂ φ₀ = c − ∑ x k y k φ k` where every local factor is within
    `γ_{m+1}` of `1`.  The sharp constant comes from the factor-level fold
    expansion: each term's suffix factors cancel against the accumulator
    product, leaving at most `m + 1` signed factors per term. -/
theorem fl_chol_offdiag_solve_form (fp : FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (c d : ℝ) (hd : d ≠ 0)
    (hm1 : gammaValid fp (m + 1)) :
    ∃ (φ₀ : ℝ) (φ : Fin m → ℝ),
      |φ₀ - 1| ≤ gamma fp (m + 1) ∧
      (∀ k, |φ k - 1| ≤ gamma fp (m + 1)) ∧
      d * fp.fl_div (fl_cholSubFold fp m x y c) d * φ₀ =
        c - ∑ k : Fin m, x k * y k * φ k := by
  have hu : fp.u < 1 := u_lt_one_of_gammaValid_succ hm1
  obtain ⟨δ, hδ, hfold⟩ := fl_sub_fold_local_factors fp m
    (fun k => fp.fl_mul (x k) (y k)) c
  choose μ hμ hμeq using fun k : Fin m => fp.model_mul (x k) (y k)
  obtain ⟨ρ, hρ, hdiv⟩ := fp.model_div (fl_cholSubFold fp m x y c) d hd
  have hfac : ∀ s : Fin m, (0:ℝ) < 1 + δ s :=
    fun s => one_add_pos_of_abs_le_u (hδ s) hu
  have hρpos : (0:ℝ) < 1 + ρ := one_add_pos_of_abs_le_u hρ hu
  have hP : (0:ℝ) < ∏ s : Fin m, (1 + δ s) :=
    Finset.prod_pos fun s _ => hfac s
  have hQ : ∀ k : Fin m,
      (0:ℝ) < ∏ j : Fin m, (if j.val < k.val then 1 + δ j else 1) := by
    intro k
    apply Finset.prod_pos
    intro j _
    by_cases h : j.val < k.val <;> simp [h, hfac j]
  -- φ₀ bound
  have hφ₀cnt : relErrorCounter fp (m + 1)
      (1 / ((∏ s : Fin m, (1 + δ s)) * (1 + ρ))) :=
    relErrorCounter_inv fp (m + 1) _
      (relErrorCounter_mul fp m 1 _ _
        (counter_plain_prod fp m δ hδ) (counter_one fp hρ)) hu
  have hφ₀ : |1 / ((∏ s : Fin m, (1 + δ s)) * (1 + ρ)) - 1| ≤
      gamma fp (m + 1) :=
    relErrorCounter_abs_sub_one_le_gamma fp (m + 1) _ hφ₀cnt hm1
  refine ⟨1 / ((∏ s : Fin m, (1 + δ s)) * (1 + ρ)),
    fun k => (1 + μ k) /
      (∏ j : Fin m, if j.val < k.val then 1 + δ j else 1),
    hφ₀, fun k => chol_term_factor_bound fp m δ (μ k) k hδ (hμ k) hm1, ?_⟩
  have hfold' : fl_cholSubFold fp m x y c =
      c * ∏ s : Fin m, (1 + δ s) -
        ∑ k : Fin m, x k * y k * (1 + μ k) * sumSuffixErrorProduct m δ k := by
    have h0 : fl_cholSubFold fp m x y c =
        c * ∏ s : Fin m, (1 + δ s) -
          ∑ k : Fin m, fp.fl_mul (x k) (y k) * sumSuffixErrorProduct m δ k :=
      hfold
    rw [h0]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hμeq k]
  rw [hdiv]
  have hLHS : d * (fl_cholSubFold fp m x y c / d * (1 + ρ)) *
      (1 / ((∏ s : Fin m, (1 + δ s)) * (1 + ρ))) =
      fl_cholSubFold fp m x y c / (∏ s : Fin m, (1 + δ s)) := by
    field_simp
  rw [hLHS, hfold', sub_div]
  congr 1
  · field_simp
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    have hSP := suffix_mul_prefix_eq_prod m δ k
    show x k * y k * (1 + μ k) * sumSuffixErrorProduct m δ k /
        (∏ s : Fin m, (1 + δ s)) =
      x k * y k *
        ((1 + μ k) / ∏ j : Fin m, if j.val < k.val then 1 + δ j else 1)
    rw [← mul_div_assoc, div_eq_div_iff hP.ne' (hQ k).ne']
    linear_combination (x k * y k * (1 + μ k)) * hSP

/-- **Algorithm 10.2 diagonal solve form** (Higham §10.1, Theorem 10.3
    diagonal equation, sharp constants).

    When the rounded partial pivot is nonnegative, the computed diagonal
    entry `r̂ = fl(√(c − ∑ x k²))` satisfies `r̂² φ₀ = c − ∑ x k² φ k` with
    `|φ₀ − 1| ≤ γ_{m+2}` (the two square-root factors join the accumulator
    product) and `|φ k − 1| ≤ γ_{m+1}`. -/
theorem fl_chol_diag_solve_form (fp : FPModel) (m : ℕ)
    (x : Fin m → ℝ) (c : ℝ)
    (hs : 0 ≤ fl_cholSubFold fp m x x c)
    (hm2 : gammaValid fp (m + 2)) :
    ∃ (φ₀ : ℝ) (φ : Fin m → ℝ),
      |φ₀ - 1| ≤ gamma fp (m + 2) ∧
      (∀ k, |φ k - 1| ≤ gamma fp (m + 1)) ∧
      (fp.fl_sqrt (fl_cholSubFold fp m x x c)) ^ 2 * φ₀ =
        c - ∑ k : Fin m, x k * x k * φ k := by
  have hm1 : gammaValid fp (m + 1) :=
    gammaValid_mono fp (by omega) hm2
  have hu : fp.u < 1 := u_lt_one_of_gammaValid_succ hm1
  obtain ⟨δ, hδ, hfold⟩ := fl_sub_fold_local_factors fp m
    (fun k => fp.fl_mul (x k) (x k)) c
  choose μ hμ hμeq using fun k : Fin m => fp.model_mul (x k) (x k)
  obtain ⟨σ, hσ, hsqrt⟩ := fp.model_sqrt (fl_cholSubFold fp m x x c) hs
  have hfac : ∀ s : Fin m, (0:ℝ) < 1 + δ s :=
    fun s => one_add_pos_of_abs_le_u (hδ s) hu
  have hσpos : (0:ℝ) < 1 + σ := one_add_pos_of_abs_le_u hσ hu
  have hP : (0:ℝ) < ∏ s : Fin m, (1 + δ s) :=
    Finset.prod_pos fun s _ => hfac s
  have hQ : ∀ k : Fin m,
      (0:ℝ) < ∏ j : Fin m, (if j.val < k.val then 1 + δ j else 1) := by
    intro k
    apply Finset.prod_pos
    intro j _
    by_cases h : j.val < k.val <;> simp [h, hfac j]
  -- φ₀ bound: m subtraction factors plus two square-root factors
  have hφ₀cnt : relErrorCounter fp (m + 2)
      (1 / ((∏ s : Fin m, (1 + δ s)) * (1 + σ) * (1 + σ))) :=
    relErrorCounter_inv fp (m + 2) _
      (relErrorCounter_mul fp (m + 1) 1 _ _
        (relErrorCounter_mul fp m 1 _ _
          (counter_plain_prod fp m δ hδ) (counter_one fp hσ))
        (counter_one fp hσ)) hu
  have hφ₀ : |1 / ((∏ s : Fin m, (1 + δ s)) * (1 + σ) * (1 + σ)) - 1| ≤
      gamma fp (m + 2) :=
    relErrorCounter_abs_sub_one_le_gamma fp (m + 2) _ hφ₀cnt hm2
  refine ⟨1 / ((∏ s : Fin m, (1 + δ s)) * (1 + σ) * (1 + σ)),
    fun k => (1 + μ k) /
      (∏ j : Fin m, if j.val < k.val then 1 + δ j else 1),
    hφ₀, fun k => chol_term_factor_bound fp m δ (μ k) k hδ (hμ k) hm1, ?_⟩
  have hfold' : fl_cholSubFold fp m x x c =
      c * ∏ s : Fin m, (1 + δ s) -
        ∑ k : Fin m, x k * x k * (1 + μ k) * sumSuffixErrorProduct m δ k := by
    have h0 : fl_cholSubFold fp m x x c =
        c * ∏ s : Fin m, (1 + δ s) -
          ∑ k : Fin m, fp.fl_mul (x k) (x k) * sumSuffixErrorProduct m δ k :=
      hfold
    rw [h0]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hμeq k]
  have hsq : (fp.fl_sqrt (fl_cholSubFold fp m x x c)) ^ 2 =
      fl_cholSubFold fp m x x c * (1 + σ) ^ 2 := by
    rw [hsqrt, mul_pow, Real.sq_sqrt hs]
  rw [hsq]
  have hLHS : fl_cholSubFold fp m x x c * (1 + σ) ^ 2 *
      (1 / ((∏ s : Fin m, (1 + δ s)) * (1 + σ) * (1 + σ))) =
      fl_cholSubFold fp m x x c / (∏ s : Fin m, (1 + δ s)) := by
    field_simp
  rw [hLHS, hfold', sub_div]
  congr 1
  · field_simp
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    have hSP := suffix_mul_prefix_eq_prod m δ k
    show x k * x k * (1 + μ k) * sumSuffixErrorProduct m δ k /
        (∏ s : Fin m, (1 + δ s)) =
      x k * x k *
        ((1 + μ k) / ∏ j : Fin m, if j.val < k.val then 1 + δ j else 1)
    rw [← mul_div_assoc, div_eq_div_iff hP.ne' (hQ k).ne']
    linear_combination (x k * x k * (1 + μ k)) * hSP

-- ============================================================
-- §10.1  Theorem 10.3: backward-error certificate for Algorithm 10.2
-- ============================================================

/-- **Algorithm 10.2 diagonal partial pivot** for column `j`: the rounded
    value whose square root becomes the computed diagonal entry `R̂ j j`.
    Nonnegativity of every pivot is the "algorithm runs to completion"
    premise of Theorem 10.3 (governed by Theorem 10.7). -/
noncomputable def fl_cholPivot (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (j : Fin n) : ℝ :=
  fl_cholSubFold fp j.val
    (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩ j)
    (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt j.isLt⟩ j)
    (A j j)

lemma sum_fin_eq_sum_filter_lt' {n k : ℕ} (hk : k ≤ n)
    (f : Fin n → ℝ) :
    (∑ t : Fin k, f ⟨t.val, by omega⟩) =
    Finset.sum (Finset.filter (fun j : Fin n => j.val < k) Finset.univ) f := by
  have hinj : ∀ a : Fin k, a ∈ Finset.univ →
      ∀ b : Fin k, b ∈ Finset.univ →
      (⟨a.val, by omega⟩ : Fin n) = ⟨b.val, by omega⟩ → a = b :=
    fun a _ b _ hab => Fin.ext (by simp only [Fin.mk.injEq] at hab; exact hab)
  have himg : Finset.image (fun (t : Fin k) => (⟨t.val, by omega⟩ : Fin n))
      Finset.univ = Finset.filter (fun j : Fin n => j.val < k) Finset.univ := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩; simp
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext (by simp)⟩
  rw [← himg, Finset.sum_image hinj]

/-- Truncate a full-index sum at row `i` when the summand vanishes strictly
    below the diagonal of the `i`-th column. -/
private lemma sum_truncate_at (n : ℕ) (i : Fin n) (f : Fin n → ℝ)
    (hf : ∀ k : Fin n, i.val < k.val → f k = 0) :
    ∑ k : Fin n, f k =
      (∑ k : Fin i.val, f ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩) + f i := by
  rw [sum_fin_eq_sum_filter_lt' (Nat.le_of_lt i.isLt) f]
  have h1 : ∑ k : Fin n, f k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val ≤ i.val), f k := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.not_le] at hk
    exact hf k hk
  rw [h1]
  have h2 : Finset.univ.filter (fun k : Fin n => k.val ≤ i.val) =
      insert i (Finset.univ.filter (fun k : Fin n => k.val < i.val)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hk
      rcases Nat.lt_or_eq_of_le hk with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | hk)
      · exact le_rfl
      · exact Nat.le_of_lt hk
  rw [h2, Finset.sum_insert (by simp)]
  ring

/-- Shared certificate core: a solved recurrence with local factors within
    `γ` of `1` yields the componentwise Theorem 10.3 bound for one entry. -/
private lemma chol_cert_core (m : ℕ) (a d r : ℝ) (x y : Fin m → ℝ)
    (φ₀ : ℝ) (φ : Fin m → ℝ) (γ : ℝ)
    (hφ₀ : |φ₀ - 1| ≤ γ) (hφ : ∀ k, |φ k - 1| ≤ γ)
    (heqn : d * r * φ₀ = a - ∑ k : Fin m, x k * y k * φ k) :
    |(∑ k : Fin m, x k * y k) + d * r - a| ≤
      γ * ((∑ k : Fin m, |x k| * |y k|) + |d| * |r|) := by
  have hs : ∑ k : Fin m, x k * y k * (φ k - 1) =
      (∑ k : Fin m, x k * y k * φ k) - ∑ k : Fin m, x k * y k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h1 : (∑ k : Fin m, x k * y k) + d * r - a =
      -(d * r * (φ₀ - 1) + ∑ k : Fin m, x k * y k * (φ k - 1)) := by
    rw [hs]
    linear_combination heqn
  rw [h1, abs_neg]
  calc |d * r * (φ₀ - 1) + ∑ k : Fin m, x k * y k * (φ k - 1)|
      ≤ |d * r * (φ₀ - 1)| + |∑ k : Fin m, x k * y k * (φ k - 1)| :=
        abs_add_le _ _
    _ ≤ |d| * |r| * γ + ∑ k : Fin m, |x k| * |y k| * γ := by
        apply add_le_add
        · rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left hφ₀
            (mul_nonneg (abs_nonneg d) (abs_nonneg r))
        · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hφ k)
            (mul_nonneg (abs_nonneg (x k)) (abs_nonneg (y k)))
    _ = γ * ((∑ k : Fin m, |x k| * |y k|) + |d| * |r|) := by
        rw [← Finset.sum_mul]
        ring

/-- **Theorem 10.3, per-entry stage-local form** (Theorem 10.7 induction):
    the componentwise certificate for entry `(i, j)` with `i ≤ j` needs
    only the `i`-th diagonal nonzero (off-diagonal case) or the `i`-th
    pivot nonnegative (diagonal case) — hypotheses available inductively
    at each stage before any later pivot exists. -/
theorem fl_cholesky_entry_bound_stage (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (i j : Fin n) (hij : i.val ≤ j.val)
    (hdz_i : i.val < j.val → fl_cholesky fp n A i i ≠ 0)
    (hpiv_i : i = j → 0 ≤ fl_cholPivot fp n A i) :
    |∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j - A i j| ≤
      gamma fp (n + 1) *
        ∑ k : Fin n, |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j| := by
  have htrunc : ∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j =
      (∑ k : Fin i.val,
        fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ i *
        fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ j) +
      fl_cholesky fp n A i i * fl_cholesky fp n A i j := by
    apply sum_truncate_at n i
    intro k hk
    rw [fl_cholesky_strict_lower fp n A k i hk, zero_mul]
  have htrunc_abs : ∑ k : Fin n,
      |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j| =
      (∑ k : Fin i.val,
        |fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ i| *
        |fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ j|) +
      |fl_cholesky fp n A i i| * |fl_cholesky fp n A i j| := by
    apply sum_truncate_at n i
    intro k hk
    rw [fl_cholesky_strict_lower fp n A k i hk, abs_zero, zero_mul]
  rw [htrunc, htrunc_abs]
  rcases Nat.lt_or_eq_of_le hij with hlt | heq
  · have hm1 : gammaValid fp (i.val + 1) := gammaValid_mono fp (by omega) hn1
    obtain ⟨φ₀, φ, hφ₀, hφ, heqn⟩ := fl_chol_offdiag_solve_form fp i.val
      (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ i)
      (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ j)
      (A i j) (fl_cholesky fp n A i i) (hdz_i hlt) hm1
    rw [← fl_cholesky_offdiag_eq fp n A i j hlt] at heqn
    have hmono : gamma fp (i.val + 1) ≤ gamma fp (n + 1) :=
      gamma_mono fp (by omega) hn1
    exact chol_cert_core i.val (A i j)
      (fl_cholesky fp n A i i) (fl_cholesky fp n A i j) _ _ φ₀ φ
      (gamma fp (n + 1))
      (le_trans hφ₀ hmono) (fun k => le_trans (hφ k) hmono) heqn
  · have hieqj : i = j := Fin.ext heq
    have hpiv := hpiv_i hieqj
    subst hieqj
    have hm2 : gammaValid fp (i.val + 2) := gammaValid_mono fp (by omega) hn1
    obtain ⟨φ₀, φ, hφ₀, hφ, heqn⟩ := fl_chol_diag_solve_form fp i.val
      (fun k => fl_cholesky fp n A ⟨k.val, Nat.lt_trans k.isLt i.isLt⟩ i)
      (A i i) hpiv hm2
    rw [← fl_cholesky_diag_eq fp n A i, pow_two] at heqn
    have hmono1 : gamma fp (i.val + 1) ≤ gamma fp (n + 1) :=
      gamma_mono fp (by omega) hn1
    have hmono2 : gamma fp (i.val + 2) ≤ gamma fp (n + 1) :=
      gamma_mono fp (by omega) hn1
    exact chol_cert_core i.val (A i i)
      (fl_cholesky fp n A i i) (fl_cholesky fp n A i i) _ _ φ₀ φ
      (gamma fp (n + 1))
      (le_trans hφ₀ hmono2) (fun k => le_trans (hφ k) hmono1) heqn

private lemma fl_cholesky_entry_bound (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n A j)
    (hdz : ∀ j : Fin n, fl_cholesky fp n A j j ≠ 0)
    (i j : Fin n) (hij : i.val ≤ j.val) :
    |∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j - A i j| ≤
      gamma fp (n + 1) *
        ∑ k : Fin n, |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j| :=
  fl_cholesky_entry_bound_stage fp n A hn1 i j hij
    (fun _ => hdz i) (fun h => h ▸ hpiv i)

/-- **Gram-sum truncation to a leading block** (Theorem 10.7 induction):
    for column indices below `m`, the full certificate sum runs only over
    the first `m` rows, since the computed factor is upper triangular. -/
theorem gram_sum_truncate (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (m : ℕ) (hm : m ≤ n) (i l : Fin n) (hi : i.val < m) :
    ∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k l =
    ∑ p : Fin m, fl_cholesky fp n A ⟨p.val, by omega⟩ i *
      fl_cholesky fp n A ⟨p.val, by omega⟩ l := by
  have hzero : ∀ k : Fin n,
      k ∉ Finset.univ.filter (fun k : Fin n => k.val < m) →
      fl_cholesky fp n A k i * fl_cholesky fp n A k l = 0 := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.not_lt] at hk
    rw [fl_cholesky_strict_lower fp n A k i (by omega), zero_mul]
  calc ∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k l
      = ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < m),
          fl_cholesky fp n A k i * fl_cholesky fp n A k l :=
        (Finset.sum_subset (Finset.filter_subset _ _)
          (fun k _ hk => hzero k hk)).symm
    _ = ∑ p : Fin m, fl_cholesky fp n A ⟨p.val, by omega⟩ i *
          fl_cholesky fp n A ⟨p.val, by omega⟩ l :=
        (sum_fin_eq_sum_filter_lt' hm _).symm

/-- **Stage-local column-norm control** (Theorem 10.7 induction): once the
    `i`-th pivot is known nonnegative, the certificate at `(i, i)` bounds
    the computed column's squared norm by `(1 − γ_{n+1})⁻¹ a_ii`. -/
theorem fl_cholesky_colNormSq_le_stage (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hn1 : gammaValid fp (n + 1)) (i : Fin n)
    (hpiv_i : 0 ≤ fl_cholPivot fp n A i) :
    (1 - gamma fp (n + 1)) *
      ∑ k : Fin n, fl_cholesky fp n A k i ^ 2 ≤ A i i := by
  have h := fl_cholesky_entry_bound_stage fp n A hn1 i i le_rfl
    (fun h => absurd h (lt_irrefl _)) (fun _ => hpiv_i)
  rw [show ∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k i =
      ∑ k : Fin n, fl_cholesky fp n A k i ^ 2 from
      Finset.sum_congr rfl fun k _ => by ring,
    show ∑ k : Fin n,
        |fl_cholesky fp n A k i| * |fl_cholesky fp n A k i| =
      ∑ k : Fin n, fl_cholesky fp n A k i ^ 2 from
      Finset.sum_congr rfl fun k _ => by
        rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]; ring] at h
  have := abs_le.mp h
  linarith [this.1]

/-- **Theorem 10.3 (Higham §10.1, equations (10.4)–(10.5))**: the concrete
    floating-point Cholesky factorization of Algorithm 10.2, when it runs to
    completion (every rounded pivot nonnegative, every computed diagonal
    entry nonzero), produces a computed factor `R̂` satisfying the
    componentwise backward-error certificate
    `|R̂ᵀR̂ − A| ≤ γ_{n+1} |R̂ᵀ||R̂|`.

    This discharges the `CholeskyBackwardError` hypothesis consumed by the
    Theorem 10.3–10.5 wrappers downstream
    (`higham10_3_cholesky_backward_error`,
    `higham10_4_cholesky_solve_backward_error`,
    `cholesky_demmel_bound_colNorm`) with the concrete algorithm rather
    than an assumed certificate. -/
theorem fl_cholesky_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hn1 : gammaValid fp (n + 1))
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n A j)
    (hdz : ∀ j : Fin n, fl_cholesky fp n A j j ≠ 0) :
    CholeskyBackwardError n A (fl_cholesky fp n A) (gamma fp (n + 1)) := by
  refine ⟨fun i j h => fl_cholesky_strict_lower fp n A i j h, ?_⟩
  intro i j
  rcases Nat.lt_or_ge j.val i.val with hji | hij
  swap
  · exact fl_cholesky_entry_bound fp n A hn1 hpiv hdz i j hij
  · have h := fl_cholesky_entry_bound fp n A hn1 hpiv hdz j i
      (Nat.le_of_lt hji)
    have h1 : ∑ k : Fin n,
        fl_cholesky fp n A k i * fl_cholesky fp n A k j =
        ∑ k : Fin n, fl_cholesky fp n A k j * fl_cholesky fp n A k i :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    have h2 : ∑ k : Fin n,
        |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j| =
        ∑ k : Fin n, |fl_cholesky fp n A k j| * |fl_cholesky fp n A k i| :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [h1, h2, hsym i j]
    exact h

/-- **Truncated certificate bound** (Theorem 10.7 induction, sub-increment
    ii, generalized): at stage `j` with `m := j.val`, for any row `i < m`
    and any column `w` with `i ≤ w`, the certificate entry bound holds with
    all sums truncated to the first `m` rows —
    `|Gram_iw − a_iw| ≤ γ_{n+1} ‖U_col i‖ ‖col w ↾ m‖`.  With `w` interior
    (`w < m`) this bounds the bordered block's interior perturbation; with
    `w = j` it bounds the border column, and no junk value from the
    not-yet-established stage-`j` square root enters. -/
theorem fl_cholesky_truncated_bound (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hn1 : gammaValid fp (n + 1))
    (j : Fin n) (i : Fin j.val) (w : Fin n) (hiw : i.val ≤ w.val)
    (hdz_i : i.val < w.val →
      fl_cholesky fp n A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ ≠ 0)
    (hpiv_i : (⟨i.val, by omega⟩ : Fin n) = w →
      0 ≤ fl_cholPivot fp n A ⟨i.val, by omega⟩) :
    |(∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ w) -
      A ⟨i.val, by omega⟩ w| ≤
      gamma fp (n + 1) *
        (Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
         Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ w ^ 2)) := by
  set ihat : Fin n := ⟨i.val, by omega⟩ with hihat
  have h1 := fl_cholesky_entry_bound_stage fp n A hn1 ihat w hiw
    hdz_i hpiv_i
  rw [gram_sum_truncate fp n A j.val j.isLt.le ihat w i.isLt] at h1
  have habs_trunc : ∑ k : Fin n,
      |fl_cholesky fp n A k ihat| * |fl_cholesky fp n A k w| =
      ∑ p : Fin j.val,
        |fl_cholesky fp n A ⟨p.val, by omega⟩ ihat| *
        |fl_cholesky fp n A ⟨p.val, by omega⟩ w| := by
    have hzero : ∀ k : Fin n,
        k ∉ Finset.univ.filter (fun k : Fin n => k.val < j.val) →
        |fl_cholesky fp n A k ihat| * |fl_cholesky fp n A k w| = 0 := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Nat.not_lt] at hk
      rw [fl_cholesky_strict_lower fp n A k ihat (by
        simp only [hihat]; omega), abs_zero, zero_mul]
    calc ∑ k : Fin n,
        |fl_cholesky fp n A k ihat| * |fl_cholesky fp n A k w|
        = ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < j.val),
            |fl_cholesky fp n A k ihat| * |fl_cholesky fp n A k w| :=
          (Finset.sum_subset (Finset.filter_subset _ _)
            (fun k _ hk => hzero k hk)).symm
      _ = ∑ p : Fin j.val,
            |fl_cholesky fp n A ⟨p.val, by omega⟩ ihat| *
            |fl_cholesky fp n A ⟨p.val, by omega⟩ w| :=
          (sum_fin_eq_sum_filter_lt' j.isLt.le _).symm
  rw [habs_trunc] at h1
  refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ (gamma_nonneg fp hn1))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin j.val))
    (fun p => |fl_cholesky fp n A ⟨p.val, by omega⟩ ihat|)
    (fun p => |fl_cholesky fp n A ⟨p.val, by omega⟩ w|)
  have hsq1 : ∑ p : Fin j.val,
      |fl_cholesky fp n A ⟨p.val, by omega⟩ ihat| ^ 2 =
      ∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ihat ^ 2 :=
    Finset.sum_congr rfl fun p _ => sq_abs _
  have hsq2 : ∑ p : Fin j.val,
      |fl_cholesky fp n A ⟨p.val, by omega⟩ w| ^ 2 =
      ∑ p : Fin j.val, fl_cholesky fp n A ⟨p.val, by omega⟩ w ^ 2 :=
    Finset.sum_congr rfl fun p _ => sq_abs _
  rw [hsq1, hsq2] at hcs
  have hnn : 0 ≤ ∑ p : Fin j.val,
      |fl_cholesky fp n A ⟨p.val, by omega⟩ ihat| *
      |fl_cholesky fp n A ⟨p.val, by omega⟩ w| :=
    Finset.sum_nonneg fun p _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc ∑ p : Fin j.val,
      |fl_cholesky fp n A ⟨p.val, by omega⟩ ihat| *
      |fl_cholesky fp n A ⟨p.val, by omega⟩ w|
      = Real.sqrt ((∑ p : Fin j.val,
          |fl_cholesky fp n A ⟨p.val, by omega⟩ ihat| *
          |fl_cholesky fp n A ⟨p.val, by omega⟩ w|) ^ 2) := by
        rw [Real.sqrt_sq hnn]
    _ ≤ Real.sqrt ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ihat ^ 2) *
        ∑ p : Fin j.val, fl_cholesky fp n A ⟨p.val, by omega⟩ w ^ 2) :=
        Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ihat ^ 2) *
        Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ w ^ 2) := by
        rw [Real.sqrt_mul (Finset.sum_nonneg fun p _ => sq_nonneg _)]

/-- **Demmel-form certificate for the computed block of a truncated run**
    (Theorem 10.14 leading block, display (10.22) engine): if the first
    `r` stages of Algorithm 10.2 ran to completion (nonzero computed
    pivot diagonals, nonnegative rounded pivots), then every Gram entry
    of the computed factor over columns `i, j < r` is Demmel-stable:
    `|R̂ᵀR̂ − A|_{ij} ≤ γ_{n+1}/(1−γ_{n+1}) √(a_ii a_jj)` — no hypothesis
    on stages `≥ r`, so this survives early termination of the PSD
    pivoted algorithm. -/
theorem fl_cholesky_truncated_demmel (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hn1 : gammaValid fp (n + 1))
    (hγlt : gamma fp (n + 1) < 1)
    (hsymm : ∀ i j : Fin n, A i j = A j i) (r : ℕ)
    (hdz : ∀ i : Fin n, i.val < r → fl_cholesky fp n A i i ≠ 0)
    (hpiv : ∀ i : Fin n, i.val < r → 0 ≤ fl_cholPivot fp n A i) :
    ∀ i j : Fin n, i.val < r → j.val < r →
      |∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j -
        A i j| ≤
      gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A i i) * Real.sqrt (A j j)) := by
  have hγ0 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  have h1γ : 0 < 1 - gamma fp (n + 1) := by linarith
  -- the ordered case i ≤ j
  have haux : ∀ i j : Fin n, i.val < r → i.val ≤ j.val →
      0 ≤ fl_cholPivot fp n A j →
      |∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j -
        A i j| ≤
      gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A i i) * Real.sqrt (A j j)) := by
    intro i j hir hij hpivj
    have hstage := fl_cholesky_entry_bound_stage fp n A hn1 i j hij
      (fun _ => hdz i hir) (fun _ => hpiv i hir)
    have hcs := colNorm_cauchy_schwarz n (fl_cholesky fp n A) i j
    -- column-norm control for both columns
    have hcol : ∀ w : Fin n, 0 ≤ fl_cholPivot fp n A w →
        colNorm n (fl_cholesky fp n A) w ≤
          Real.sqrt (A w w / (1 - gamma fp (n + 1))) := by
      intro w hw
      have h := fl_cholesky_colNormSq_le_stage fp n A hn1 w hw
      have hsq : colNormSq n (fl_cholesky fp n A) w ≤
          A w w / (1 - gamma fp (n + 1)) := by
        rw [le_div_iff₀ h1γ, mul_comm]
        exact h
      exact Real.sqrt_le_sqrt hsq
    have hAii : 0 ≤ A i i := by
      have h := fl_cholesky_colNormSq_le_stage fp n A hn1 i (hpiv i hir)
      have hnn : 0 ≤ ∑ k : Fin n, fl_cholesky fp n A k i ^ 2 :=
        Finset.sum_nonneg fun k _ => sq_nonneg _
      nlinarith
    have hAjj : 0 ≤ A j j := by
      have h := fl_cholesky_colNormSq_le_stage fp n A hn1 j hpivj
      have hnn : 0 ≤ ∑ k : Fin n, fl_cholesky fp n A k j ^ 2 :=
        Finset.sum_nonneg fun k _ => sq_nonneg _
      nlinarith
    have hprod : colNorm n (fl_cholesky fp n A) i *
        colNorm n (fl_cholesky fp n A) j ≤
        Real.sqrt (A i i) * Real.sqrt (A j j) /
          (1 - gamma fp (n + 1)) := by
      have hmul := mul_le_mul (hcol i (hpiv i hir)) (hcol j hpivj)
        (colNorm_nonneg n _ j) (Real.sqrt_nonneg _)
      calc colNorm n (fl_cholesky fp n A) i *
          colNorm n (fl_cholesky fp n A) j
          ≤ Real.sqrt (A i i / (1 - gamma fp (n + 1))) *
            Real.sqrt (A j j / (1 - gamma fp (n + 1))) := hmul
        _ = Real.sqrt (A i i) * Real.sqrt (A j j) /
              (1 - gamma fp (n + 1)) := by
            rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤
              A i i / (1 - gamma fp (n + 1)))]
            rw [show A i i / (1 - gamma fp (n + 1)) *
                (A j j / (1 - gamma fp (n + 1))) =
                A i i * A j j / (1 - gamma fp (n + 1)) ^ 2 by
              field_simp]
            have h2 : (Real.sqrt (A i i) * Real.sqrt (A j j) /
                (1 - gamma fp (n + 1))) ^ 2 =
                A i i * A j j / (1 - gamma fp (n + 1)) ^ 2 := by
              rw [div_pow, mul_pow, Real.sq_sqrt hAii,
                Real.sq_sqrt hAjj]
            rw [← h2, Real.sqrt_sq (by positivity)]
    calc |∑ k : Fin n, fl_cholesky fp n A k i *
          fl_cholesky fp n A k j - A i j|
        ≤ gamma fp (n + 1) * ∑ k : Fin n,
            |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j| := hstage
      _ ≤ gamma fp (n + 1) * (colNorm n (fl_cholesky fp n A) i *
            colNorm n (fl_cholesky fp n A) j) :=
          mul_le_mul_of_nonneg_left hcs hγ0
      _ ≤ gamma fp (n + 1) * (Real.sqrt (A i i) * Real.sqrt (A j j) /
            (1 - gamma fp (n + 1))) :=
          mul_le_mul_of_nonneg_left hprod hγ0
      _ = gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
            (Real.sqrt (A i i) * Real.sqrt (A j j)) := by ring
  intro i j hir hjr
  rcases le_total i.val j.val with hij | hji
  · exact haux i j hir hij (hpiv j hjr)
  · have h := haux j i hjr hji (hpiv i hir)
    have hgram : ∑ k : Fin n, fl_cholesky fp n A k i *
        fl_cholesky fp n A k j =
        ∑ k : Fin n, fl_cholesky fp n A k j *
          fl_cholesky fp n A k i :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hgram, hsymm i j]
    calc |∑ k : Fin n, fl_cholesky fp n A k j *
          fl_cholesky fp n A k i - A j i|
        ≤ gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
            (Real.sqrt (A j j) * Real.sqrt (A i i)) := h
      _ = gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
            (Real.sqrt (A i i) * Real.sqrt (A j j)) := by ring

/-- **Border-block certificate for a truncated run under computed-pivot
    domination** (Theorem 10.14 border block): for `i < r ≤ j`, if the
    computed border entries are dominated by their row pivots up to a
    factor `c` (the computed-factor form of the complete-pivoting
    invariant (10.13)), the Gram defect is bounded by
    `γ_{n+1} c/(1−γ_{n+1}) √(a_ii) √(∑_{k<r} a_kk)` — trace-controlled,
    matching the row-sum shape of display (10.22). -/
theorem fl_cholesky_truncated_border_demmel (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hn1 : gammaValid fp (n + 1))
    (hγlt : gamma fp (n + 1) < 1) (r : ℕ)
    (hdz : ∀ i : Fin n, i.val < r → fl_cholesky fp n A i i ≠ 0)
    (hpiv : ∀ i : Fin n, i.val < r → 0 ≤ fl_cholPivot fp n A i)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ j : Fin n, r ≤ j.val → ∀ k : Fin n, k.val < r →
      |fl_cholesky fp n A k j| ≤ c * |fl_cholesky fp n A k k|) :
    ∀ i j : Fin n, i.val < r → r ≤ j.val →
      |∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j -
        A i j| ≤
      gamma fp (n + 1) * c / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A i i) *
          Real.sqrt (∑ k ∈ Finset.univ.filter
            (fun k : Fin n => k.val < r), A k k)) := by
  intro i j hir hjr
  have hγ0 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  have h1γ : 0 < 1 - gamma fp (n + 1) := by linarith
  have hij : i.val ≤ j.val := le_trans (Nat.le_of_lt hir) hjr
  have hstage := fl_cholesky_entry_bound_stage fp n A hn1 i j hij
    (fun _ => hdz i hir) (fun _ => hpiv i hir)
  -- diagonal nonnegativity on computed stages
  have hAkk : ∀ k : Fin n, k.val < r → 0 ≤ A k k := by
    intro k hk
    have h := fl_cholesky_colNormSq_le_stage fp n A hn1 k (hpiv k hk)
    have hnn : 0 ≤ ∑ p : Fin n, fl_cholesky fp n A p k ^ 2 :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    nlinarith
  have hAii : 0 ≤ A i i := hAkk i hir
  -- step 1: dominate the border factors by pivot entries
  have hsum1 : ∑ k : Fin n,
      |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j| ≤
      c * ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
        |fl_cholesky fp n A k i| * |fl_cholesky fp n A k k| := by
    rw [Finset.mul_sum]
    rw [show (∑ k : Fin n,
        |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j|) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
          |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j| from
      (Finset.sum_subset (Finset.filter_subset _ _) fun k _ hk => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Nat.not_lt] at hk
        rw [fl_cholesky_strict_lower fp n A k i
          (lt_of_lt_of_le hir hk), abs_zero, zero_mul]).symm]
    refine Finset.sum_le_sum fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [show c * (|fl_cholesky fp n A k i| *
        |fl_cholesky fp n A k k|) =
        |fl_cholesky fp n A k i| *
          (c * |fl_cholesky fp n A k k|) by ring]
    exact mul_le_mul_of_nonneg_left (hdom j hjr k hk) (abs_nonneg _)
  -- step 2: Cauchy–Schwarz over the computed rows
  have hcs : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
      |fl_cholesky fp n A k i| * |fl_cholesky fp n A k k| ≤
      Real.sqrt (∑ k ∈ Finset.univ.filter
          (fun k : Fin n => k.val < r), fl_cholesky fp n A k i ^ 2) *
      Real.sqrt (∑ k ∈ Finset.univ.filter
          (fun k : Fin n => k.val < r), fl_cholesky fp n A k k ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ.filter (fun k : Fin n => k.val < r))
      (fun k => |fl_cholesky fp n A k i|)
      (fun k => |fl_cholesky fp n A k k|)
    have hL : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
        |fl_cholesky fp n A k i| ^ 2 =
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
          fl_cholesky fp n A k i ^ 2 :=
      Finset.sum_congr rfl fun k _ => sq_abs _
    have hR : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
        |fl_cholesky fp n A k k| ^ 2 =
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
          fl_cholesky fp n A k k ^ 2 :=
      Finset.sum_congr rfl fun k _ => sq_abs _
    rw [hL, hR] at h
    have hnn : 0 ≤ ∑ k ∈ Finset.univ.filter
        (fun k : Fin n => k.val < r),
        |fl_cholesky fp n A k i| * |fl_cholesky fp n A k k| :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
        |fl_cholesky fp n A k i| * |fl_cholesky fp n A k k|
        = Real.sqrt ((∑ k ∈ Finset.univ.filter
            (fun k : Fin n => k.val < r),
            |fl_cholesky fp n A k i| * |fl_cholesky fp n A k k|) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((∑ k ∈ Finset.univ.filter
            (fun k : Fin n => k.val < r),
            fl_cholesky fp n A k i ^ 2) *
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
            fl_cholesky fp n A k k ^ 2) := Real.sqrt_le_sqrt h
      _ = _ := Real.sqrt_mul (Finset.sum_nonneg fun k _ =>
            sq_nonneg _) _
  -- step 3: column-i partial sum ≤ full column sum ≤ a_ii/(1−γ)
  have hcolI : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
      fl_cholesky fp n A k i ^ 2 ≤ A i i / (1 - gamma fp (n + 1)) := by
    have hfull := fl_cholesky_colNormSq_le_stage fp n A hn1 i
      (hpiv i hir)
    have hsub : ∑ k ∈ Finset.univ.filter
        (fun k : Fin n => k.val < r), fl_cholesky fp n A k i ^ 2 ≤
        ∑ k : Fin n, fl_cholesky fp n A k i ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) fun k _ _ => sq_nonneg _
    rw [le_div_iff₀ h1γ]
    nlinarith
  -- step 4: pivot squares dominated by column sums, then by trace
  have hdiagS : ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
      fl_cholesky fp n A k k ^ 2 ≤
      (∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r), A k k) /
        (1 - gamma fp (n + 1)) := by
    rw [le_div_iff₀ h1γ, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    have hcol := fl_cholesky_colNormSq_le_stage fp n A hn1 k
      (hpiv k hk)
    have hsingle : fl_cholesky fp n A k k ^ 2 ≤
        ∑ p : Fin n, fl_cholesky fp n A p k ^ 2 :=
      Finset.single_le_sum
        (f := fun p => fl_cholesky fp n A p k ^ 2)
        (fun p _ => sq_nonneg _) (Finset.mem_univ k)
    nlinarith
  -- assemble
  have htr0 : 0 ≤ ∑ k ∈ Finset.univ.filter
      (fun k : Fin n => k.val < r), A k k :=
    Finset.sum_nonneg fun k hk => hAkk k (by
      simpa using (Finset.mem_filter.mp hk).2)
  calc |∑ k : Fin n, fl_cholesky fp n A k i *
        fl_cholesky fp n A k j - A i j|
      ≤ gamma fp (n + 1) * ∑ k : Fin n,
          |fl_cholesky fp n A k i| * |fl_cholesky fp n A k j| := hstage
    _ ≤ gamma fp (n + 1) * (c * ∑ k ∈ Finset.univ.filter
          (fun k : Fin n => k.val < r),
          |fl_cholesky fp n A k i| * |fl_cholesky fp n A k k|) :=
        mul_le_mul_of_nonneg_left hsum1 hγ0
    _ ≤ gamma fp (n + 1) * (c *
          (Real.sqrt (∑ k ∈ Finset.univ.filter
            (fun k : Fin n => k.val < r),
            fl_cholesky fp n A k i ^ 2) *
           Real.sqrt (∑ k ∈ Finset.univ.filter
            (fun k : Fin n => k.val < r),
            fl_cholesky fp n A k k ^ 2))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcs hc) hγ0
    _ ≤ gamma fp (n + 1) * (c *
          (Real.sqrt (A i i / (1 - gamma fp (n + 1))) *
           Real.sqrt ((∑ k ∈ Finset.univ.filter
              (fun k : Fin n => k.val < r), A k k) /
            (1 - gamma fp (n + 1))))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul (Real.sqrt_le_sqrt hcolI)
            (Real.sqrt_le_sqrt hdiagS) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)) hc) hγ0
    _ = gamma fp (n + 1) * c / (1 - gamma fp (n + 1)) *
          (Real.sqrt (A i i) *
           Real.sqrt (∑ k ∈ Finset.univ.filter
            (fun k : Fin n => k.val < r), A k k)) := by
        rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤
            A i i / (1 - gamma fp (n + 1)))]
        rw [show A i i / (1 - gamma fp (n + 1)) *
            ((∑ k ∈ Finset.univ.filter
              (fun k : Fin n => k.val < r), A k k) /
              (1 - gamma fp (n + 1))) =
            A i i * (∑ k ∈ Finset.univ.filter
              (fun k : Fin n => k.val < r), A k k) /
              (1 - gamma fp (n + 1)) ^ 2 by field_simp]
        have h2 : (Real.sqrt (A i i) *
            Real.sqrt (∑ k ∈ Finset.univ.filter
              (fun k : Fin n => k.val < r), A k k) /
            (1 - gamma fp (n + 1))) ^ 2 =
            A i i * (∑ k ∈ Finset.univ.filter
              (fun k : Fin n => k.val < r), A k k) /
              (1 - gamma fp (n + 1)) ^ 2 := by
          rw [div_pow, mul_pow, Real.sq_sqrt hAii, Real.sq_sqrt htr0]
        rw [← h2, Real.sqrt_sq (by positivity)]
        ring

/-- **The r-row truncated computed factor**: rows `≥ r` zeroed — the
    factor actually produced when the pivoted PSD algorithm terminates
    after `r` stages (Higham §10.3, Theorem 10.14). -/
noncomputable def fl_choleskyTrunc (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (r : ℕ) : Fin n → Fin n → ℝ :=
  fun k j => if k.val < r then fl_cholesky fp n A k j else 0

/-- The truncated Gram is the row-filtered Gram of the full recursion. -/
lemma fl_choleskyTrunc_gram (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (r : ℕ) (i j : Fin n) :
    ∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
      fl_choleskyTrunc fp n A r k j =
    ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
      fl_cholesky fp n A k i * fl_cholesky fp n A k j := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold fl_choleskyTrunc
  by_cases hk : k.val < r
  · simp [hk]
  · simp [hk]

/-- For a computed column (`i < r`), the truncated Gram equals the full
    Gram: rows `≥ r` never meet column `i` (strict lower zeros). -/
lemma fl_choleskyTrunc_gram_computed (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (r : ℕ) (i j : Fin n) (hi : i.val < r) :
    ∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
      fl_choleskyTrunc fp n A r k j =
    ∑ k : Fin n, fl_cholesky fp n A k i * fl_cholesky fp n A k j := by
  rw [fl_choleskyTrunc_gram]
  refine Finset.sum_subset (Finset.filter_subset _ _)
    fun k _ hk => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.not_lt] at hk
  rw [fl_cholesky_strict_lower fp n A k i (lt_of_lt_of_le hi hk),
    zero_mul]

/-- **Theorem 10.14, three-block backward-error certificate for the
    truncated computed factor** (display (10.22) shape): after `r`
    completed stages of Algorithm 10.2,
    * the computed `r × r` block is Demmel-stable,
    * the border block is trace-controlled under the computed-pivot
      domination `c` (the computed form of the (10.13) invariant),
    * the trailing block carries the terminal Schur residual `η`
      (what the termination criterion (10.24)/(10.25) certifies),
    all stated for the truncated factor `R̃ = fl_choleskyTrunc`. -/
theorem fl_choleskyTrunc_backward_error (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hn1 : gammaValid fp (n + 1))
    (hγlt : gamma fp (n + 1) < 1)
    (hsymm : ∀ i j : Fin n, A i j = A j i) (r : ℕ)
    (hdz : ∀ i : Fin n, i.val < r → fl_cholesky fp n A i i ≠ 0)
    (hpiv : ∀ i : Fin n, i.val < r → 0 ≤ fl_cholPivot fp n A i)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ j : Fin n, r ≤ j.val → ∀ k : Fin n, k.val < r →
      |fl_cholesky fp n A k j| ≤ c * |fl_cholesky fp n A k k|)
    (η : ℝ)
    (htrail : ∀ i j : Fin n, r ≤ i.val → r ≤ j.val →
      |∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < r),
        fl_cholesky fp n A k i * fl_cholesky fp n A k j - A i j| ≤ η) :
    (∀ i j : Fin n, i.val < r → j.val < r →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A i i) * Real.sqrt (A j j))) ∧
    (∀ i j : Fin n, i.val < r → r ≤ j.val →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) * c / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A i i) *
         Real.sqrt (∑ k ∈ Finset.univ.filter
          (fun k : Fin n => k.val < r), A k k))) ∧
    (∀ i j : Fin n, r ≤ i.val → j.val < r →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤
      gamma fp (n + 1) * c / (1 - gamma fp (n + 1)) *
        (Real.sqrt (A j j) *
         Real.sqrt (∑ k ∈ Finset.univ.filter
          (fun k : Fin n => k.val < r), A k k))) ∧
    (∀ i j : Fin n, r ≤ i.val → r ≤ j.val →
      |∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j - A i j| ≤ η) := by
  refine ⟨fun i j hi hj => ?_, fun i j hi hj => ?_,
    fun i j hi hj => ?_, fun i j hi hj => ?_⟩
  · rw [fl_choleskyTrunc_gram_computed fp n A r i j hi]
    exact fl_cholesky_truncated_demmel fp n A hn1 hγlt hsymm r
      hdz hpiv i j hi hj
  · rw [fl_choleskyTrunc_gram_computed fp n A r i j hi]
    exact fl_cholesky_truncated_border_demmel fp n A hn1 hγlt r
      hdz hpiv c hc hdom i j hi hj
  · -- transpose of the border case
    have hgram : ∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j =
        ∑ k : Fin n, fl_choleskyTrunc fp n A r k j *
          fl_choleskyTrunc fp n A r k i :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hgram, hsymm i j, fl_choleskyTrunc_gram_computed fp n A r j i hj]
    exact fl_cholesky_truncated_border_demmel fp n A hn1 hγlt r
      hdz hpiv c hc hdom j i hj hi
  · rw [fl_choleskyTrunc_gram]
    exact htrail i j hi hj

/-- **Normwise bordered perturbation floor** (Theorem 10.7 constant
    sharpening route): when the interior and border perturbation masses
    are controlled *normwise* — `|yᵀΔy| ≤ ε·W` and
    `|2yᵀδ| ≤ ε(t + W)` directly, as the (10.7) operator-norm
    certificates provide — the exact pivot floor loses the dimension
    factor: `lam·a_jj + (lam − ε)W − εt ≤ a_jj − t` replaces the
    componentwise route's `lam − 2εm` weight. This is the engine for a
    stage step with the source's `n`-shaped threshold. -/
theorem bordered_perturbation_floor_normwise (m : ℕ)
    (Gint : Fin m → Fin m → ℝ) (gb : Fin m → ℝ)
    (Bint : Fin m → Fin m → ℝ) (bb : Fin m → ℝ)
    (a : Fin m → ℝ) (ajj t : ℝ) (y : Fin m → ℝ) (ε lam : ℝ)
    (hε0 : 0 ≤ ε) (ht0 : 0 ≤ t)
    (hgram : (∑ i : Fin m, ∑ l : Fin m, y i * Gint i l * y l) +
      2 * (∑ i : Fin m, y i * gb i) + t = 0)
    (hint : |∑ i : Fin m, ∑ l : Fin m,
      y i * (Gint i l - Bint i l) * y l| ≤
      ε * (∑ i : Fin m, a i * y i ^ 2))
    (hbord : |2 * ∑ i : Fin m, y i * (gb i - bb i)| ≤
      ε * (t + ∑ i : Fin m, a i * y i ^ 2))
    (hfloor : lam * ((∑ i : Fin m, a i * y i ^ 2) + ajj) ≤
      (∑ i : Fin m, ∑ l : Fin m, y i * Bint i l * y l) +
      2 * (∑ i : Fin m, y i * bb i) + ajj) :
    lam * ajj + (lam - 2 * ε) * (∑ i : Fin m, a i * y i ^ 2) -
      ε * t ≤ ajj - t := by
  set W : ℝ := ∑ i : Fin m, a i * y i ^ 2 with hW
  have hdecomp : (∑ i : Fin m, ∑ l : Fin m, y i * Bint i l * y l) +
      2 * (∑ i : Fin m, y i * bb i) + ajj =
      -(∑ i : Fin m, ∑ l : Fin m,
        y i * (Gint i l - Bint i l) * y l) -
      2 * (∑ i : Fin m, y i * (gb i - bb i)) + (ajj - t) := by
    have hsplitI : ∑ i : Fin m, ∑ l : Fin m,
        y i * (Gint i l - Bint i l) * y l =
        (∑ i : Fin m, ∑ l : Fin m, y i * Gint i l * y l) -
        ∑ i : Fin m, ∑ l : Fin m, y i * Bint i l * y l := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hsplitB : ∑ i : Fin m, y i * (gb i - bb i) =
        (∑ i : Fin m, y i * gb i) - ∑ i : Fin m, y i * bb i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplitI, hsplitB]
    linarith [hgram]
  have hfloor2 := hfloor
  rw [hdecomp] at hfloor2
  have h1 := abs_le.mp hint
  have h2 := abs_le.mp hbord
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Normwise stage endgame** (Theorem 10.7 sharpened threshold,
    scalar core): combining the normwise perturbation floor, the
    rounded-pivot lower bound, and a breakdown assumption yields a
    contradiction whenever `lam > ε + 2γ` (and `lam ≥ 2ε`,
    `lam ≤ 1`) — the source-shaped threshold whose leading term is the
    normwise certificate `ε` (which carries the dimension), replacing
    the componentwise route's `2εm` weight. -/
theorem normwise_stage_endgame (ajj t W lam ε γ s : ℝ)
    (hAj : 0 < ajj) (ht0 : 0 ≤ t) (hW0 : 0 ≤ W)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hfloor : lam * ajj + (lam - 2 * ε) * W - ε * t ≤ ajj - t)
    (hlow : ajj - t - γ * (ajj + t) ≤ s)
    (hs : s ≤ 0)
    (hlam2ε : 2 * ε ≤ lam)
    (hthresh : ε + 2 * γ < lam) :
    False := by
  -- breakdown converts the pivot lower bound into a t-floor
  have hkey2 : (1 - γ) * ajj ≤ (1 + γ) * t := by nlinarith
  -- the W-term is nonnegative, so the floor gives a t-ceiling
  have hWnn : 0 ≤ (lam - 2 * ε) * W :=
    mul_nonneg (by linarith) hW0
  have hkey1 : lam * ajj - ε * t ≤ ajj - t := by nlinarith
  -- combine: (1−γ)(1−ε)·ajj ≤ (1+γ)(1−lam)·ajj forces lam ≤ ε + 2γ
  have ht_ceil : t * (1 - ε) ≤ ajj * (1 - lam) := by nlinarith
  have h1ε : (0:ℝ) < 1 - ε := by linarith
  have h1γ : (0:ℝ) < 1 + γ := by linarith
  -- chain the two t-bounds through the positive weights
  have hA : (1 - γ) * (1 - ε) * ajj ≤
      (1 + γ) * (ajj * (1 - lam)) := by
    calc (1 - γ) * (1 - ε) * ajj
        = (1 - ε) * ((1 - γ) * ajj) := by ring
      _ ≤ (1 - ε) * ((1 + γ) * t) :=
          mul_le_mul_of_nonneg_left hkey2 h1ε.le
      _ = (1 + γ) * (t * (1 - ε)) := by ring
      _ ≤ (1 + γ) * (ajj * (1 - lam)) :=
          mul_le_mul_of_nonneg_left ht_ceil h1γ.le
  -- the threshold forces the reverse strict inequality
  have hceil : (1 + γ) * (1 - lam) < (1 - γ) * (1 - ε) := by
    have h1 := mul_lt_mul_of_pos_right hthresh h1γ
    nlinarith [mul_nonneg hγ0 hε0, sq_nonneg γ]
  have hfinal := mul_lt_mul_of_pos_right hceil hAj
  nlinarith [hA, hfinal]

/-- **Theorem 10.7 stage step with the source-shaped threshold**: if the
    stage-`j` interior and border Gram defects carry *normwise* mass
    bounds `ε` against the `A`-diagonal weights (as the (10.7)
    operator-norm certificates provide, with `ε` carrying the
    dimension), the `j`-th rounded pivot is positive whenever
    `λ > ε + 2γ_{n+1}` (and `λ ≥ 2ε`) — Higham's `n`-shaped threshold,
    replacing the componentwise `(2n+3)γ/(1−γ)`. -/
theorem fl_cholesky_pivot_pos_step_sharp (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (j : Fin n)
    (IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l)
    (lam ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hfloor : ∀ y : Fin j.val → ℝ,
      lam * ((∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j) ≤
        (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j)
    (hmassI : ∀ y : Fin j.val → ℝ,
      |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
        ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
          A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * y l| ≤
      ε * ∑ i : Fin j.val,
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2)
    (hmassB : ∀ y : Fin j.val → ℝ,
      |2 * ∑ i : Fin j.val, y i *
        ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
          A ⟨i.val, by omega⟩ j)| ≤
      ε * ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) +
        ∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2))
    (hlam2ε : 2 * ε ≤ lam)
    (hthresh : ε + 2 * gamma fp (n + 1) < lam) :
    0 < fl_cholPivot fp n A j := by
  by_contra hs
  push_neg at hs
  have hγ0 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  set γ : ℝ := gamma fp (n + 1) with hγdef
  have hu : fp.u < 1 := u_lt_one_of_gammaValid_succ hn1
  -- stage data
  have hdiag_pos : ∀ i : Fin j.val,
      0 < fl_cholesky fp n A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ := by
    intro i
    rw [fl_cholesky_diag_eq fp n A ⟨i.val, by omega⟩]
    exact fl_sqrt_pos fp hu _ (IH ⟨i.val, by omega⟩ i.isLt)
  set U : Fin j.val → Fin j.val → ℝ := fun p i =>
    fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ with hUdef
  set c : Fin j.val → ℝ := fun p =>
    fl_cholesky fp n A ⟨p.val, by omega⟩ j with hcdef
  obtain ⟨y, hy⟩ := upperTriangular_solve_exists j.val U
    (fun p i hpi => fl_cholesky_strict_lower fp n A _ _ hpi)
    (fun i => (hdiag_pos i).ne') (fun p => -(c p))
  have hgram := bordered_gram_zero j.val U c y hy
  set t : ℝ := ∑ p : Fin j.val, c p ^ 2 with htdef
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun p _ => sq_nonneg _
  set W : ℝ := ∑ i : Fin j.val,
    A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hAdiag _).le (sq_nonneg _)
  -- the normwise perturbation floor at the solve vector
  have hfloorN := bordered_perturbation_floor_normwise j.val
    (fun i l => ∑ p : Fin j.val, U p i * U p l)
    (fun i => ∑ p : Fin j.val, U p i * c p)
    (fun i l => A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩)
    (fun i => A ⟨i.val, by omega⟩ j)
    (fun i => A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
    (A j j) t y ε lam hε0 ht0 hgram (hmassI y) (hmassB y) (hfloor y)
  -- the rounded-pivot lower bound
  have hm1' : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hlow := fl_cholSubFold_pivot_lower fp j.val c (A j j) hm1'
  have hpiv_eq : fl_cholPivot fp n A j =
      fl_cholSubFold fp j.val c c (A j j) := rfl
  have hγm : gamma fp (j.val + 1) ≤ γ :=
    gamma_mono fp (by omega) hn1
  have hAj := hAdiag j
  have habsAj : |A j j| = A j j := abs_of_pos hAj
  have hlow2 : A j j - t - γ * (A j j + t) ≤ fl_cholPivot fp n A j := by
    rw [hpiv_eq]
    have hmass : gamma fp (j.val + 1) * (|A j j| + t) ≤
        γ * (A j j + t) := by
      rw [habsAj]
      exact mul_le_mul_of_nonneg_right hγm (by linarith)
    calc A j j - t - γ * (A j j + t)
        ≤ A j j - t - gamma fp (j.val + 1) * (|A j j| + t) := by
          linarith
      _ ≤ fl_cholSubFold fp j.val c c (A j j) := hlow
  -- contradiction via the source-shaped scalar endgame
  exact normwise_stage_endgame (A j j) t W lam ε γ
    (fl_cholPivot fp n A j) hAj ht0 hW0 hγ0 hγ1 hε0 hε1
    hfloorN hlow2 hs hlam2ε hthresh

/-- **All rounded pivots positive at the source-shaped threshold**: the
    whole-run induction over `fl_cholesky_pivot_pos_step_sharp` — every
    pivot is positive whenever `λ > ε + 2γ_{n+1}` with per-stage
    normwise mass certificates. -/
theorem fl_cholesky_pivots_pos_sharp (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (lam ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hfloor : ∀ j : Fin n, ∀ y : Fin j.val → ℝ,
      lam * ((∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j) ≤
        (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j)
    (hmassI : ∀ j : Fin n, ∀ y : Fin j.val → ℝ,
      |∑ i : Fin j.val, ∑ l : Fin j.val, y i *
        ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨l.val, by omega⟩) -
          A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩) * y l| ≤
      ε * ∑ i : Fin j.val,
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2)
    (hmassB : ∀ j : Fin n, ∀ y : Fin j.val → ℝ,
      |2 * ∑ i : Fin j.val, y i *
        ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
          fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
          A ⟨i.val, by omega⟩ j)| ≤
      ε * ((∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2) +
        ∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2))
    (hlam2ε : 2 * ε ≤ lam)
    (hthresh : ε + 2 * gamma fp (n + 1) < lam) :
    ∀ j : Fin n, 0 < fl_cholPivot fp n A j := by
  have H : ∀ k : ℕ, ∀ j : Fin n, j.val = k →
      0 < fl_cholPivot fp n A j := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IHk =>
      intro j hj
      refine fl_cholesky_pivot_pos_step_sharp fp A hAdiag hn1 hγ1 j
        (fun l hl => IHk l.val (hj ▸ hl) l rfl) lam ε hε0 hε1
        (hfloor j) (hmassI j) (hmassB j) hlam2ε hthresh
  exact fun j => H j.val j rfl

/-- Leading-column Gram sums truncate to the stage square
    (strict-lower zeros kill rows at and beyond the stage). -/
lemma gram_sum_stage_trunc (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (j : Fin n) (x w : Fin n)
    (hx : x.val < j.val) :
    ∑ p : Fin n, fl_cholesky fp n A p x * fl_cholesky fp n A p w =
    ∑ p : Fin j.val, fl_cholesky fp n A ⟨p.val, by omega⟩ x *
      fl_cholesky fp n A ⟨p.val, by omega⟩ w := by
  rw [sum_fin_eq_sum_filter_lt' j.isLt.le
    (fun p => fl_cholesky fp n A p x * fl_cholesky fp n A p w)]
  refine (Finset.sum_subset (Finset.filter_subset _ _)
    fun p _ hp => ?_).symm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.not_lt] at hp
  rw [fl_cholesky_strict_lower fp n A p x (lt_of_lt_of_le hx hp),
    zero_mul]

/-- **Border-column entry bound**: the `w = j` instance of
    `fl_cholesky_truncated_bound`. -/
theorem fl_cholesky_border_bound (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (hn1 : gammaValid fp (n + 1))
    (j : Fin n) (i : Fin j.val)
    (hdz_i : fl_cholesky fp n A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ ≠ 0) :
    |(∑ p : Fin j.val,
        fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ *
        fl_cholesky fp n A ⟨p.val, by omega⟩ j) -
      A ⟨i.val, by omega⟩ j| ≤
      gamma fp (n + 1) *
        (Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ ^ 2) *
         Real.sqrt (∑ p : Fin j.val,
          fl_cholesky fp n A ⟨p.val, by omega⟩ j ^ 2)) :=
  fl_cholesky_truncated_bound fp A hn1 j i j (i.isLt).le
    (fun _ => hdz_i)
    (fun h => absurd (congrArg Fin.val h) (by simp; omega))

/-- **Pivot locality**: the `l`-th pivot of the algorithm run on a leading
    `m × m` block equals the `l`-th pivot of the full run, `l < m ≤ n`. -/
theorem fl_cholPivot_leading_principal (fp : FPModel) {n m : ℕ}
    (hm : m ≤ n) (A : Fin n → Fin n → ℝ) (l : Fin m) :
    fl_cholPivot fp m
      (fun i' j' => A ⟨i'.val, by omega⟩ ⟨j'.val, by omega⟩) l =
    fl_cholPivot fp n A ⟨l.val, by omega⟩ := by
  unfold fl_cholPivot
  congr 1
  · funext k
    exact fl_cholesky_leading_principal fp hm A
      ⟨k.val, Nat.lt_trans k.isLt l.isLt⟩ l
  · funext k
    exact fl_cholesky_leading_principal fp hm A
      ⟨k.val, Nat.lt_trans k.isLt l.isLt⟩ l

/-- **Stage-`m` block certificate** (Theorem 10.7 induction): once every
    pivot below `m` is positive, the leading `m × m` block of `A` satisfies
    the full Theorem 10.3 certificate at level `γ_{m+1}`, via Algorithm 10.2
    locality. -/
theorem fl_cholesky_block_certificate (fp : FPModel) {n m : ℕ}
    (hm : m ≤ n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hu : fp.u < 1)
    (hm1 : gammaValid fp (m + 1))
    (IH : ∀ l : Fin n, l.val < m → 0 < fl_cholPivot fp n A l) :
    CholeskyBackwardError m
      (fun i' j' => A ⟨i'.val, by omega⟩ ⟨j'.val, by omega⟩)
      (fl_cholesky fp m
        (fun i' j' => A ⟨i'.val, by omega⟩ ⟨j'.val, by omega⟩))
      (gamma fp (m + 1)) := by
  apply fl_cholesky_backward_error fp m _
    (fun i j => hsym _ _) hm1
  · intro l
    rw [fl_cholPivot_leading_principal fp hm A l]
    exact (IH ⟨l.val, by omega⟩ l.isLt).le
  · intro l
    rw [show fl_cholesky fp m
        (fun i' j' => A ⟨i'.val, by omega⟩ ⟨j'.val, by omega⟩) l l =
      fl_cholesky fp n A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩ from
      fl_cholesky_leading_principal fp hm A l l]
    rw [fl_cholesky_diag_eq fp n A ⟨l.val, by omega⟩]
    exact (fl_sqrt_pos fp hu _ (IH ⟨l.val, by omega⟩ l.isLt)).ne'


/-- **Bordered perturbation floor** (Theorem 10.7 induction, abstract
    scalar core): if the computed Gram form of the test vector vanishes,
    the interior and border perturbations are `ε`-small against the
    `D`-weights, and the bordered `A`-form has Rayleigh floor `lam`, then
    the exact pivot `a_jj − t` is floored by
    `lam·a_jj + (lam − 2εm)W − εt`.  All Cauchy–Schwarz and AM–GM steps
    happen here, divorced from the algorithm. -/
theorem bordered_perturbation_floor (m : ℕ)
    (Gint : Fin m → Fin m → ℝ) (gb : Fin m → ℝ)
    (Bint : Fin m → Fin m → ℝ) (bb : Fin m → ℝ)
    (a : Fin m → ℝ) (ajj t : ℝ) (y : Fin m → ℝ) (ε lam : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hε0 : 0 ≤ ε) (ht0 : 0 ≤ t)
    (hgram : (∑ i : Fin m, ∑ l : Fin m, y i * Gint i l * y l) +
      2 * (∑ i : Fin m, y i * gb i) + t = 0)
    (hint : ∀ i l : Fin m, |Gint i l - Bint i l| ≤
      ε * (Real.sqrt (a i) * Real.sqrt (a l)))
    (hbord : ∀ i : Fin m, |gb i - bb i| ≤
      ε * (Real.sqrt (a i) * Real.sqrt t))
    (hfloor : lam * ((∑ i : Fin m, a i * y i ^ 2) + ajj) ≤
      (∑ i : Fin m, ∑ l : Fin m, y i * Bint i l * y l) +
      2 * (∑ i : Fin m, y i * bb i) + ajj) :
    lam * ajj + lam * (∑ i : Fin m, a i * y i ^ 2) -
      2 * ε * m * (∑ i : Fin m, a i * y i ^ 2) - ε * t ≤ ajj - t := by
  set W : ℝ := ∑ i : Fin m, a i * y i ^ 2 with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ =>
    mul_nonneg (ha i) (sq_nonneg _)
  set Q : ℝ := ∑ i : Fin m, |y i| * Real.sqrt (a i) with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun i _ =>
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  -- Q² ≤ m·W by Cauchy–Schwarz with the ones vector
  have hQsq : Q ^ 2 ≤ m * W := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin m))
      (fun _ => (1:ℝ)) (fun i => |y i| * Real.sqrt (a i))
    have h1 : ∑ i : Fin m, (1:ℝ) * (|y i| * Real.sqrt (a i)) = Q :=
      Finset.sum_congr rfl fun i _ => one_mul _
    have h2 : ∑ _i : Fin m, ((1:ℝ)) ^ 2 = (m : ℝ) := by simp
    have h3 : ∑ i : Fin m, (|y i| * Real.sqrt (a i)) ^ 2 = W := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, sq_abs, Real.sq_sqrt (ha i)]
      ring
    rw [h1, h2, h3] at h
    exact h
  -- interior mass
  have hImass : |∑ i : Fin m, ∑ l : Fin m,
      y i * (Gint i l - Bint i l) * y l| ≤ ε * Q ^ 2 := by
    calc |∑ i : Fin m, ∑ l : Fin m, y i * (Gint i l - Bint i l) * y l|
        ≤ ∑ i : Fin m, |∑ l : Fin m, y i * (Gint i l - Bint i l) * y l| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin m, ∑ l : Fin m,
            |y i| * |Gint i l - Bint i l| * |y l| := by
          apply Finset.sum_le_sum
          intro i _
          calc |∑ l : Fin m, y i * (Gint i l - Bint i l) * y l|
              ≤ ∑ l : Fin m, |y i * (Gint i l - Bint i l) * y l| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = ∑ l : Fin m, |y i| * |Gint i l - Bint i l| * |y l| := by
                apply Finset.sum_congr rfl
                intro l _
                rw [abs_mul, abs_mul]
      _ ≤ ∑ i : Fin m, ∑ l : Fin m,
            |y i| * (ε * (Real.sqrt (a i) * Real.sqrt (a l))) * |y l| := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro l _
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left (hint i l) (abs_nonneg _)
      _ = ε * Q ^ 2 := by
          rw [hQ, sq, Finset.sum_mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
  -- border mass, with AM–GM
  have hBmass : |2 * ∑ i : Fin m, y i * (gb i - bb i)| ≤ ε * (t + Q ^ 2) := by
    have h1 : |∑ i : Fin m, y i * (gb i - bb i)| ≤
        ε * Real.sqrt t * Q := by
      calc |∑ i : Fin m, y i * (gb i - bb i)|
          ≤ ∑ i : Fin m, |y i * (gb i - bb i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i : Fin m, |y i| * |gb i - bb i| := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul]
        _ ≤ ∑ i : Fin m, |y i| *
              (ε * (Real.sqrt (a i) * Real.sqrt t)) := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left (hbord i) (abs_nonneg _)
        _ = ε * Real.sqrt t * Q := by
            rw [hQ, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    have hamgm : 2 * (Real.sqrt t * Q) ≤ t + Q ^ 2 := by
      have hsq := sq_nonneg (Real.sqrt t - Q)
      have hts : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
      nlinarith
    calc |2 * ∑ i : Fin m, y i * (gb i - bb i)|
        = 2 * |∑ i : Fin m, y i * (gb i - bb i)| := by
          rw [abs_mul]
          norm_num
      _ ≤ 2 * (ε * Real.sqrt t * Q) := by linarith [h1]
      _ = ε * (2 * (Real.sqrt t * Q)) := by ring
      _ ≤ ε * (t + Q ^ 2) := mul_le_mul_of_nonneg_left hamgm hε0
  -- assemble: S_B = −ΔI − 2ΔM + (ajj − t)
  have hdecomp : (∑ i : Fin m, ∑ l : Fin m, y i * Bint i l * y l) +
      2 * (∑ i : Fin m, y i * bb i) + ajj =
      -(∑ i : Fin m, ∑ l : Fin m, y i * (Gint i l - Bint i l) * y l) -
      2 * (∑ i : Fin m, y i * (gb i - bb i)) + (ajj - t) := by
    have hsplitI : ∑ i : Fin m, ∑ l : Fin m,
        y i * (Gint i l - Bint i l) * y l =
        (∑ i : Fin m, ∑ l : Fin m, y i * Gint i l * y l) -
        ∑ i : Fin m, ∑ l : Fin m, y i * Bint i l * y l := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hsplitB : ∑ i : Fin m, y i * (gb i - bb i) =
        (∑ i : Fin m, y i * gb i) - ∑ i : Fin m, y i * bb i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplitI, hsplitB]
    linarith [hgram]
  have hfloor2 := hfloor
  rw [hdecomp] at hfloor2
  have habs1 := abs_le.mp hImass
  have habs2 := abs_le.mp hBmass
  have hQW := hQsq
  nlinarith [habs1.1, habs1.2, habs2.1, habs2.2, hε0, hQ0, hW0]

set_option maxHeartbeats 1600000 in
/-- **Theorem 10.7, success direction for the concrete algorithm — stage
    step** (Higham p. 200, real-model form): if every pivot below stage `j`
    is positive and the bordered leading block of `A` has Rayleigh floor
    `lam > (2n+3)·γ_{n+1}/(1−γ_{n+1})` in `D²`-weighted split form, then
    the `j`-th rounded pivot is positive.  Test vector `z = (y, 1)` with
    `Uy = −c`; the computed Gram form vanishes (`bordered_gram_zero`), the
    perturbation mass is controlled by `bordered_perturbation_floor` fed
    with the truncated certificate bounds, and `fl_cholSubFold_pivot_lower`
    converts exact positivity into floating-point positivity.  The
    threshold constant is coarser than the source display
    `n γ_{n+1}/(1−γ_{n+1})`; sharpening is left open. -/
theorem fl_cholesky_pivot_pos_step (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (j : Fin n)
    (IH : ∀ l : Fin n, l.val < j.val → 0 < fl_cholPivot fp n A l)
    (lam : ℝ)
    (hfloor : ∀ y : Fin j.val → ℝ,
      lam * ((∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j) ≤
        (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j)
    (hthresh : (2 * (n : ℝ) + 3) *
      (gamma fp (n + 1) / (1 - gamma fp (n + 1))) < lam) :
    0 < fl_cholPivot fp n A j := by
  by_contra hs
  push_neg at hs
  have hγ0 : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  have h1γ : (0:ℝ) < 1 - gamma fp (n + 1) := by linarith
  set γ : ℝ := gamma fp (n + 1) with hγdef
  set ε : ℝ := γ / (1 - γ) with hεdef
  have hε0 : 0 ≤ ε := div_nonneg hγ0 h1γ.le
  have hεγ : ε * (1 - γ) = γ := div_mul_cancel₀ γ h1γ.ne'
  have hγε : γ ≤ ε := by nlinarith
  have hu : fp.u < 1 := u_lt_one_of_gammaValid_succ hn1
  have hcast : (j.val : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (j.isLt).le
  have hlam3 : 3 * ε < lam := by
    nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ)), hε0]
  -- lam ≤ 1 from the floor at y = 0
  have hlam1 : lam ≤ 1 := by
    have h0 := hfloor (fun _ => 0)
    simp at h0
    nlinarith [hAdiag j, h0]
  have hεsmall : ε < 1 / 3 := by nlinarith
  -- stage data
  have hdiag_pos : ∀ i : Fin j.val,
      0 < fl_cholesky fp n A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ := by
    intro i
    rw [fl_cholesky_diag_eq fp n A ⟨i.val, by omega⟩]
    exact fl_sqrt_pos fp hu _ (IH ⟨i.val, by omega⟩ i.isLt)
  set U : Fin j.val → Fin j.val → ℝ := fun p i =>
    fl_cholesky fp n A ⟨p.val, by omega⟩ ⟨i.val, by omega⟩ with hUdef
  set c : Fin j.val → ℝ := fun p =>
    fl_cholesky fp n A ⟨p.val, by omega⟩ j with hcdef
  obtain ⟨y, hy⟩ := upperTriangular_solve_exists j.val U
    (fun p i hpi => fl_cholesky_strict_lower fp n A _ _ hpi)
    (fun i => (hdiag_pos i).ne') (fun p => -(c p))
  have hgram := bordered_gram_zero j.val U c y hy
  set t : ℝ := ∑ p : Fin j.val, c p ^ 2 with htdef
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun p _ => sq_nonneg _
  -- column-norm control and √-forms
  have hcolsq : ∀ i : Fin j.val,
      ∑ p : Fin j.val, U p i ^ 2 ≤
        A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ / (1 - γ) := by
    intro i
    have h1 := fl_cholesky_colNormSq_le_stage fp n A hn1
      ⟨i.val, by omega⟩ (IH ⟨i.val, by omega⟩ i.isLt).le
    have htr : ∑ k : Fin n,
        fl_cholesky fp n A k ⟨i.val, by omega⟩ ^ 2 =
        ∑ p : Fin j.val, U p i ^ 2 := by
      rw [show ∑ k : Fin n,
          fl_cholesky fp n A k ⟨i.val, by omega⟩ ^ 2 =
        ∑ k : Fin n, fl_cholesky fp n A k ⟨i.val, by omega⟩ *
          fl_cholesky fp n A k ⟨i.val, by omega⟩ from
        Finset.sum_congr rfl fun k _ => by ring]
      rw [gram_sum_truncate fp n A j.val j.isLt.le ⟨i.val, by omega⟩
        ⟨i.val, by omega⟩ i.isLt]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [htr] at h1
    rw [le_div_iff₀ h1γ]
    linarith
  have hsqrt1γ : Real.sqrt (1 - γ) * Real.sqrt (1 - γ) = 1 - γ :=
    Real.mul_self_sqrt h1γ.le
  have hsqrt1γ_pos : 0 < Real.sqrt (1 - γ) := Real.sqrt_pos.mpr h1γ
  have hsqrt1γ_ge : 1 - γ ≤ Real.sqrt (1 - γ) := by
    have hle1 : Real.sqrt (1 - γ) ≤ 1 :=
      Real.sqrt_le_one.mpr (by linarith)
    nlinarith [hle1, hsqrt1γ_pos.le, hsqrt1γ]
  have hγ'' : γ / Real.sqrt (1 - γ) ≤ ε := by
    rw [hεdef]
    exact div_le_div_of_nonneg_left hγ0 h1γ hsqrt1γ_ge
  have hsqrt_col : ∀ i : Fin j.val,
      Real.sqrt (∑ p : Fin j.val, U p i ^ 2) ≤
      Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) /
        Real.sqrt (1 - γ) := by
    intro i
    rw [show Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) /
        Real.sqrt (1 - γ) =
      Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ / (1 - γ)) from
      (Real.sqrt_div (hAdiag _).le _).symm]
    exact Real.sqrt_le_sqrt (hcolsq i)
  -- interior perturbation bound in ε-form
  have hint : ∀ i l : Fin j.val,
      |(∑ p : Fin j.val, U p i * U p l) -
        A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩| ≤
      ε * (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
        Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩)) := by
    have hkey : ∀ i l : Fin j.val, i.val ≤ l.val →
        |(∑ p : Fin j.val, U p i * U p l) -
          A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩| ≤
        ε * (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
          Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩)) := by
      intro i l hil
      have h1 := fl_cholesky_truncated_bound fp A hn1 j i
        ⟨l.val, by omega⟩ hil
        (fun _ => (hdiag_pos i).ne')
        (fun _ => (IH ⟨i.val, by omega⟩ i.isLt).le)
      refine le_trans h1 ?_
      have hsl := hsqrt_col i
      have hsr := hsqrt_col l
      have hprod : Real.sqrt (∑ p : Fin j.val, U p i ^ 2) *
          Real.sqrt (∑ p : Fin j.val, U p l ^ 2) ≤
          (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) /
            Real.sqrt (1 - γ)) *
          (Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩) /
            Real.sqrt (1 - γ)) :=
        mul_le_mul hsl hsr (Real.sqrt_nonneg _)
          (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      calc γ * (Real.sqrt (∑ p : Fin j.val, U p i ^ 2) *
            Real.sqrt (∑ p : Fin j.val, U p l ^ 2))
          ≤ γ * ((Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) /
              Real.sqrt (1 - γ)) *
            (Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩) /
              Real.sqrt (1 - γ))) :=
            mul_le_mul_of_nonneg_left hprod hγ0
        _ = ε * (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
            Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩)) := by
            rw [hεdef]
            field_simp
            linear_combination (-(γ *
              Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
              Real.sqrt (A ⟨l.val, by omega⟩ ⟨l.val, by omega⟩))) *
              (Real.sq_sqrt h1γ.le)
    intro i l
    rcases le_or_gt i.val l.val with hil | hli
    · exact hkey i l hil
    · have hswap1 : (∑ p : Fin j.val, U p i * U p l) =
          ∑ p : Fin j.val, U p l * U p i :=
        Finset.sum_congr rfl fun p _ => mul_comm _ _
      have hswap2 : A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ =
          A ⟨l.val, by omega⟩ ⟨i.val, by omega⟩ := hsym _ _
      rw [hswap1, hswap2, mul_comm (Real.sqrt _)]
      exact hkey l i hli.le
  -- border perturbation bound in ε-form
  have hbord : ∀ i : Fin j.val,
      |(∑ p : Fin j.val, U p i * c p) - A ⟨i.val, by omega⟩ j| ≤
      ε * (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
        Real.sqrt t) := by
    intro i
    have h1 := fl_cholesky_border_bound fp A hn1 j i (hdiag_pos i).ne'
    refine le_trans h1 ?_
    have hsl := hsqrt_col i
    calc γ * (Real.sqrt (∑ p : Fin j.val, U p i ^ 2) * Real.sqrt t)
        ≤ γ * ((Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) /
            Real.sqrt (1 - γ)) * Real.sqrt t) := by
          apply mul_le_mul_of_nonneg_left _ hγ0
          exact mul_le_mul_of_nonneg_right hsl (Real.sqrt_nonneg _)
      _ = (γ / Real.sqrt (1 - γ)) *
          (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
            Real.sqrt t) := by ring
      _ ≤ ε * (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
            Real.sqrt t) :=
          mul_le_mul_of_nonneg_right hγ''
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  -- the perturbation floor
  have hmain := bordered_perturbation_floor j.val
    (fun i l => ∑ p : Fin j.val, U p i * U p l)
    (fun i => ∑ p : Fin j.val, U p i * c p)
    (fun i l => A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩)
    (fun i => A ⟨i.val, by omega⟩ j)
    (fun i => A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩)
    (A j j) t y ε lam
    (fun i => (hAdiag _).le) hε0 ht0 hgram hint hbord (hfloor y)
  set W : ℝ := ∑ i : Fin j.val,
    A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2 with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hAdiag _).le (sq_nonneg _)
  -- rounded pivot lower bound
  have hm1' : gammaValid fp (j.val + 1) :=
    gammaValid_mono fp (by omega) hn1
  have hlow := fl_cholSubFold_pivot_lower fp j.val c (A j j) hm1'
  have hpiv_eq : fl_cholPivot fp n A j =
      fl_cholSubFold fp j.val c c (A j j) := rfl
  have hγm : gamma fp (j.val + 1) ≤ γ :=
    gamma_mono fp (by omega) hn1
  have hAj := hAdiag j
  have habsAj : |A j j| = A j j := abs_of_pos hAj
  -- s ≥ (A jj − t) − γ (A jj + t)
  have hlow2 : A j j - t - γ * (A j j + t) ≤ fl_cholPivot fp n A j := by
    rw [hpiv_eq]
    have hmass : gamma fp (j.val + 1) * (|A j j| + t) ≤
        γ * (A j j + t) := by
      rw [habsAj]
      exact mul_le_mul_of_nonneg_right hγm (by linarith)
    calc A j j - t - γ * (A j j + t)
        ≤ A j j - t - gamma fp (j.val + 1) * (|A j j| + t) := by
          linarith
      _ ≤ fl_cholSubFold fp j.val c c (A j j) := hlow
  -- scalar end-game
  have hthresh_m : 2 * ε * (j.val : ℝ) + 3 * ε < lam := by
    nlinarith
  have hWterm : (2 * ε * (j.val : ℝ) + 3 * ε) * W ≤ lam * W :=
    mul_le_mul_of_nonneg_right hthresh_m.le hW0
  -- from the floor: lam·ajj ≤ ajj − t(1−ε) (after absorbing W-terms)
  have hkey1 : lam * A j j ≤ A j j - t * (1 - ε) := by nlinarith
  -- from the pivot bound and hs: (1−γ)ajj ≤ (1+γ)t
  have hkey2 : (1 - γ) * A j j ≤ (1 + γ) * t := by nlinarith
  -- contradiction
  nlinarith [hkey1, hkey2, hεγ, hAj, ht0, hγ0, hεsmall, hlam3, hγε,
    mul_pos hAj (by linarith : (0:ℝ) < 1 - ε)]

/-- **Theorem 10.7, success direction for the concrete algorithm**
    (Higham p. 200): if every bordered leading block of `A` has Rayleigh
    floor `lam > (2n+3)·γ_{n+1}/(1−γ_{n+1})` in `D²`-weighted split form,
    then Algorithm 10.2 runs to completion — every rounded pivot is
    positive, hence every computed diagonal entry is real and positive. -/
theorem fl_cholesky_pivots_pos (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (lam : ℝ)
    (hfloor : ∀ j : Fin n, ∀ y : Fin j.val → ℝ,
      lam * ((∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j) ≤
        (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j)
    (hthresh : (2 * (n : ℝ) + 3) *
      (gamma fp (n + 1) / (1 - gamma fp (n + 1))) < lam) :
    ∀ j : Fin n, 0 < fl_cholPivot fp n A j := by
  have H : ∀ k : ℕ, ∀ j : Fin n, j.val = k → 0 < fl_cholPivot fp n A j := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k IHk =>
      intro j hj
      apply fl_cholesky_pivot_pos_step fp A hsym hAdiag hn1 hγ1 j _
        lam (hfloor j) hthresh
      intro l hl
      exact IHk l.val (hj ▸ hl) l rfl
  exact fun j => H j.val j rfl

/-- **Run-to-completion, diagonal form**: under the same floor, every
    computed diagonal entry of the factor is positive — the algorithm never
    encounters a nonpositive pivot and all square roots are real. -/
theorem fl_cholesky_diag_pos_of_floor (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hn1 : gammaValid fp (n + 1))
    (hγ1 : gamma fp (n + 1) < 1)
    (lam : ℝ)
    (hfloor : ∀ j : Fin n, ∀ y : Fin j.val → ℝ,
      lam * ((∑ i : Fin j.val,
          A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩ * y i ^ 2) + A j j) ≤
        (∑ i : Fin j.val, ∑ l : Fin j.val,
          y i * A ⟨i.val, by omega⟩ ⟨l.val, by omega⟩ * y l) +
        2 * (∑ i : Fin j.val, y i * A ⟨i.val, by omega⟩ j) + A j j)
    (hthresh : (2 * (n : ℝ) + 3) *
      (gamma fp (n + 1) / (1 - gamma fp (n + 1))) < lam) :
    ∀ j : Fin n, 0 < fl_cholesky fp n A j j := by
  intro j
  rw [fl_cholesky_diag_eq fp n A j]
  exact fl_sqrt_pos fp (u_lt_one_of_gammaValid_succ hn1) _
    (fl_cholesky_pivots_pos fp A hsym hAdiag hn1 hγ1 lam hfloor hthresh j)

end NumStability
