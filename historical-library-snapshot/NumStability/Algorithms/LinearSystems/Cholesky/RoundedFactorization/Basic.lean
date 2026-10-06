import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Demmel
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms LinearSystems Cholesky RoundedFactorization Basic

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyFl` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

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

end NumStability
