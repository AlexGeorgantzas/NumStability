import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskyDemmel
import NumStability.Algorithms.LinearSystems.Cholesky.RoundedFactorization.Basic
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model

/-!
# CholeskyFl (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Cholesky.CholeskyFl`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

namespace NumStability

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
