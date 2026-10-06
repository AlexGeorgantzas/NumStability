-- Algorithms/Summation/Recursive/Core.lean

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import NumStability.Analysis.Error
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.Summation.ErrorBounds

/-!
# Recursive summation core

Source-independent definitions and error analysis for left-to-right recursive
summation, including higher-precision composition and running-error bounds.
The numbered Higham Problem 4.3 correspondence lives in
`NumStability.Source.Higham.Chapter04.Problem03`.
-/

namespace NumStability

open scoped BigOperators

/-- Floating-point recursive summation of `n` values.

    Computes `fl_add(... fl_add(fl_add(0, v 0), v 1) ..., v (n-1))`,
    left-to-right starting from the accumulator 0.

    This formalises the standard loop from Higham §4.1:
    ```
    s = 0
    for i = 1:n
      s = s + xᵢ
    end
    ``` -/
noncomputable def fl_recursiveSum (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0

/-- Under exact arithmetic, recursive summation returns the exact source sum. -/
theorem fl_recursiveSum_exactWithUnitRoundoff (u0 : ℝ) (hu0 : 0 ≤ u0) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      fl_recursiveSum (FPModel.exactWithUnitRoundoff u0 hu0) n v =
        ∑ i : Fin n, v i
  | 0, _v => by
      simp [fl_recursiveSum]
  | n + 1, v => by
      let fp := FPModel.exactWithUnitRoundoff u0 hu0
      have hfold :
          fl_recursiveSum fp (n + 1) v =
            fp.fl_add
              (fl_recursiveSum fp n (fun i : Fin n => v i.castSucc))
              (v (Fin.last n)) :=
        Fin.foldl_succ_last _ _
      rw [hfold, fl_recursiveSum_exactWithUnitRoundoff u0 hu0 n
        (fun i : Fin n => v i.castSucc)]
      simp [fp, FPModel.exactWithUnitRoundoff, Fin.sum_univ_castSucc,
        add_comm]

/-! ## Higher-precision recursive summation trace -/

/-- Source-level trace for Higham Chapter 4's advice to compute a recursive
sum in a higher precision and then round the result to the working precision.
The final working-precision rounding is supplied explicitly as `roundWorking`,
because the abstract `FPModel` records binary operations rather than a general
unary format-rounding operator. -/
structure HigherPrecisionRecursiveSumTrace where
  highSum : ℝ
  roundedSum : ℝ

/-- Recursive summation in `highFp`, followed by a supplied working-precision
rounding map. -/
noncomputable def higherPrecisionRecursiveSumTrace
    (highFp : FPModel) (roundWorking : ℝ → ℝ)
    (n : ℕ) (v : Fin n → ℝ) : HigherPrecisionRecursiveSumTrace :=
  let highSum := fl_recursiveSum highFp n v
  let roundedSum := roundWorking highSum
  { highSum := highSum, roundedSum := roundedSum }

/-- The higher-precision stage is ordinary recursive summation under
`highFp`. -/
theorem higherPrecisionRecursiveSumTrace_highSum
    (highFp : FPModel) (roundWorking : ℝ → ℝ)
    (n : ℕ) (v : Fin n → ℝ) :
    (higherPrecisionRecursiveSumTrace highFp roundWorking n v).highSum =
      fl_recursiveSum highFp n v := by
  rfl

/-- The final stage rounds the higher-precision recursive sum to working
precision by the supplied map. -/
theorem higherPrecisionRecursiveSumTrace_roundedSum
    (highFp : FPModel) (roundWorking : ℝ → ℝ)
    (n : ℕ) (v : Fin n → ℝ) :
    (higherPrecisionRecursiveSumTrace highFp roundWorking n v).roundedSum =
      roundWorking
        (higherPrecisionRecursiveSumTrace highFp roundWorking n v).highSum := by
  rfl

/-- Returned value of the higher-precision recursive-sum-then-round trace. -/
noncomputable def fl_higherPrecisionRecursiveSum
    (highFp : FPModel) (roundWorking : ℝ → ℝ)
    (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  (higherPrecisionRecursiveSumTrace highFp roundWorking n v).roundedSum

/-- The returned value is the rounded high-precision recursive sum. -/
theorem fl_higherPrecisionRecursiveSum_eq_round_highSum
    (highFp : FPModel) (roundWorking : ℝ → ℝ)
    (n : ℕ) (v : Fin n → ℝ) :
    fl_higherPrecisionRecursiveSum highFp roundWorking n v =
      roundWorking (fl_recursiveSum highFp n v) := by
  rfl

/-- Under exact high-precision arithmetic and identity final rounding, the
higher-precision recursive-sum trace returns the exact source sum. -/
theorem fl_higherPrecisionRecursiveSum_exactWithUnitRoundoff_id
    (u0 : ℝ) (hu0 : 0 ≤ u0) (n : ℕ) (v : Fin n → ℝ) :
    fl_higherPrecisionRecursiveSum
        (FPModel.exactWithUnitRoundoff u0 hu0) id n v =
      ∑ i : Fin n, v i := by
  rw [fl_higherPrecisionRecursiveSum_eq_round_highSum]
  simpa using fl_recursiveSum_exactWithUnitRoundoff u0 hu0 n v

/-- Mixed-precision error composition for a high-precision recursive sum
followed by one working-precision rounding.

If the final rounding map has local relative error at most `u`, and the
high-precision recursive stage has absolute error at most
`ε * sum |xᵢ|`, then the final result has the displayed two-term bound. -/
theorem fl_higherPrecisionRecursiveSum_abs_error_le_of_high_bound
    (highFp : FPModel) (roundWorking : ℝ → ℝ)
    (n : ℕ) (v : Fin n → ℝ) {u ε : ℝ}
    (hround : ∀ y : ℝ, |roundWorking y - y| ≤ u * |y|)
    (hhigh : |fl_recursiveSum highFp n v - ∑ i : Fin n, v i| ≤
      ε * ∑ i : Fin n, |v i|) :
    |(∑ i : Fin n, v i) -
        fl_higherPrecisionRecursiveSum highFp roundWorking n v| ≤
      u * |fl_recursiveSum highFp n v| + ε * ∑ i : Fin n, |v i| := by
  rw [fl_higherPrecisionRecursiveSum_eq_round_highSum]
  let high := fl_recursiveSum highFp n v
  let exact := ∑ i : Fin n, v i
  have hdecomp :
      exact - roundWorking high =
        (exact - high) + (high - roundWorking high) := by
    ring
  calc
    |exact - roundWorking high|
        = |(exact - high) + (high - roundWorking high)| := by
          rw [hdecomp]
    _ ≤ |exact - high| + |high - roundWorking high| := abs_add_le _ _
    _ = |high - exact| + |roundWorking high - high| := by
          rw [abs_sub_comm exact high,
            abs_sub_comm high (roundWorking high)]
    _ ≤ ε * ∑ i : Fin n, |v i| + u * |high| :=
          add_le_add hhigh (hround high)
    _ = u * |high| + ε * ∑ i : Fin n, |v i| := by ring

/-- Chapter 4's displayed mixed-precision `n*u^2` form as a composition
theorem: once the high-precision recursive stage has the advertised
`n*u^2 * sum |xᵢ|` bound, one final working-precision rounding gives the
two-term mixed-precision error bound. -/
theorem fl_higherPrecisionRecursiveSum_abs_error_le_nu_sq
    (highFp : FPModel) (roundWorking : ℝ → ℝ)
    (n : ℕ) (v : Fin n → ℝ) {u : ℝ}
    (hround : ∀ y : ℝ, |roundWorking y - y| ≤ u * |y|)
    (hhigh : |fl_recursiveSum highFp n v - ∑ i : Fin n, v i| ≤
      (n : ℝ) * u ^ 2 * ∑ i : Fin n, |v i|) :
    |(∑ i : Fin n, v i) -
        fl_higherPrecisionRecursiveSum highFp roundWorking n v| ≤
      u * |fl_recursiveSum highFp n v| +
        (n : ℝ) * u ^ 2 * ∑ i : Fin n, |v i| :=
  fl_higherPrecisionRecursiveSum_abs_error_le_of_high_bound
    highFp roundWorking n v hround hhigh

/-- **Recursive summation backward error** (Higham §4.2, eq. 4.4).

    The computed recursive sum satisfies:
      `fl_recursiveSum fp n v = ∑ i, v i * (1 + θ i)`
    where each `|θ i| ≤ γ(n - 1)`.

    Backward result: the computed sum is the *exact* sum of perturbed
    inputs `vᵢ * (1 + θᵢ)`.  The bound γ(n-1) is tight: no number xᵢ
    participates in more than n - 1 additions (Higham §4.2).  The first
    step `fl_add 0 (v 0) = v 0` is exact by `fl_add_zero`, leaving only
    n - 1 rounding steps; this is captured via `fl_sum_error_tight`. -/
theorem recursiveSum_backward_error (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : gammaValid fp (n - 1)) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ gamma fp (n - 1)) ∧
      fl_recursiveSum fp n v = ∑ i : Fin n, v i * (1 + θ i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨Fin.elim0, fun i => i.elim0, by simp [fl_recursiveSum]⟩
  · exact fl_sum_error_tight fp n hpos v hn

/-- **Exact error decomposition** (Higham §4.2, eq. 4.2 — per-input form).

    Given backward error witnesses `θ` certifying
      `fl_recursiveSum fp n v = ∑ i, v i * (1 + θ i)`,
    the absolute error decomposes as:
      `fl_recursiveSum fp n v - ∑ i, v i = ∑ i, v i * θ i`

    This is the per-input counterpart of Higham's eq. (4.2), which writes the
    error as a sum of local contributions `δᵢ T̂ᵢ`.  It is the stepping stone
    from the backward error representation to the forward bound (4.4). -/
lemma recursiveSum_error_decomp (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (θ : Fin n → ℝ)
    (hfl : fl_recursiveSum fp n v = ∑ i : Fin n, v i * (1 + θ i)) :
    fl_recursiveSum fp n v - ∑ i : Fin n, v i = ∑ i : Fin n, v i * θ i := by
  rw [hfl, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

/-- **Recursive summation forward error bound** (Higham §4.2, equation 4.4).

    The absolute error of recursive summation satisfies:
      `|fl_recursiveSum fp n v - ∑ i, v i| ≤ γ(n - 1) * ∑ i, |v i|`

    This matches Higham's eq. (4.4) exactly: the constant is n - 1, not n,
    because the initial `fl_add 0 (v 0)` is exact (see `recursiveSum_backward_error`).

    Proof: from the backward form `∑ vᵢ(1+θᵢ)`, apply `recursiveSum_error_decomp`
    to get the error equals `∑ vᵢθᵢ`; triangle inequality + `|θᵢ| ≤ γ(n-1)` close. -/
theorem recursiveSum_forward_error_bound (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : gammaValid fp (n - 1)) :
    |fl_recursiveSum fp n v - ∑ i : Fin n, v i| ≤
      gamma fp (n - 1) * ∑ i : Fin n, |v i| := by
  obtain ⟨θ, hθ, hfold⟩ := recursiveSum_backward_error fp n v hn
  rw [recursiveSum_error_decomp fp n v θ hfold]
  calc |∑ i : Fin n, v i * θ i|
      ≤ ∑ i : Fin n, |v i * θ i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |v i| * |θ i| := by
          apply Finset.sum_congr rfl; intro i _; rw [abs_mul]
    _ ≤ ∑ i : Fin n, |v i| * gamma fp (n - 1) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hθ i) (abs_nonneg _)
    _ = gamma fp (n - 1) * ∑ i : Fin n, |v i| := by
          rw [← Finset.sum_mul, mul_comm]

/-- Absolute magnitude bound for recursive summation, obtained from the
source-shaped backward-error representation. -/
theorem recursiveSum_abs_le_one_add_gamma_mul_sum_abs
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hn : gammaValid fp (n - 1)) :
    |fl_recursiveSum fp n v| ≤
      (1 + gamma fp (n - 1)) * ∑ i : Fin n, |v i| := by
  obtain ⟨θ, hθ, hfold⟩ := recursiveSum_backward_error fp n v hn
  rw [hfold]
  calc
    |∑ i : Fin n, v i * (1 + θ i)|
        ≤ ∑ i : Fin n, |v i * (1 + θ i)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |v i| * |1 + θ i| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul]
    _ ≤ ∑ i : Fin n, |v i| * (1 + gamma fp (n - 1)) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hone :
          |1 + θ i| ≤ 1 + gamma fp (n - 1) := by
        calc
          |1 + θ i| ≤ |(1 : ℝ)| + |θ i| := abs_add_le _ _
          _ = 1 + |θ i| := by norm_num
          _ ≤ 1 + gamma fp (n - 1) := by
            linarith [hθ i]
      exact mul_le_mul_of_nonneg_left hone (abs_nonneg _)
    _ = (1 + gamma fp (n - 1)) * ∑ i : Fin n, |v i| := by
      rw [← Finset.sum_mul]
      ring

/-! ## Weighted absolute-value exchange -/

/-- Assigning the larger weight to the smaller magnitude cannot increase a
two-term weighted absolute-value bound. -/
theorem weighted_abs_pair_exchange_le {wa wb a b : ℝ}
    (hweight : wb ≤ wa) (hab : |a| ≤ |b|) :
    wa * |a| + wb * |b| ≤ wa * |b| + wb * |a| := by
  have hdiff : 0 ≤ wa - wb := sub_nonneg.mpr hweight
  calc
    wa * |a| + wb * |b| =
        wb * (|a| + |b|) + (wa - wb) * |a| := by ring
    _ ≤ wb * (|a| + |b|) + (wa - wb) * |b| := by
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hab hdiff)
    _ = wa * |b| + wb * |a| := by ring

/-- Gamma-form mixed-precision bound derived from the repository's recursive
summation analysis for the high-precision stage. -/
theorem fl_higherPrecisionRecursiveSum_abs_error_le_gamma
    (highFp : FPModel) (roundWorking : ℝ → ℝ)
    (n : ℕ) (v : Fin n → ℝ) {u : ℝ}
    (hround : ∀ y : ℝ, |roundWorking y - y| ≤ u * |y|)
    (hvalid : gammaValid highFp (n - 1)) :
    |(∑ i : Fin n, v i) -
        fl_higherPrecisionRecursiveSum highFp roundWorking n v| ≤
      u * |fl_recursiveSum highFp n v| +
        gamma highFp (n - 1) * ∑ i : Fin n, |v i| :=
  fl_higherPrecisionRecursiveSum_abs_error_le_of_high_bound
    highFp roundWorking n v hround
    (recursiveSum_forward_error_bound highFp n v hvalid)

/-- One-signed relative-error consequence of the higher-precision
recursive-sum-then-round composition theorem.

If the high-precision recursive stage has absolute error at most
`ε * sum |xᵢ|`, then on one-signed nonzero data the final rounded result has
relative error at most `u * (1 + ε) + ε`. -/
theorem fl_higherPrecisionRecursiveSum_relError_le_of_high_bound_oneSigned
    (highFp : FPModel) (roundWorking : ℝ → ℝ)
    (n : ℕ) (v : Fin n → ℝ) {u ε : ℝ}
    (hu : 0 ≤ u)
    (hround : ∀ y : ℝ, |roundWorking y - y| ≤ u * |y|)
    (hhigh : |fl_recursiveSum highFp n v - ∑ i : Fin n, v i| ≤
      ε * ∑ i : Fin n, |v i|)
    (hv : OneSigned v) (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_higherPrecisionRecursiveSum highFp roundWorking n v)
        (∑ i : Fin n, v i) ≤
      u * (1 + ε) + ε := by
  let high := fl_recursiveSum highFp n v
  let exact := ∑ i : Fin n, v i
  have hden : 0 < |exact| := abs_pos.mpr hsum
  have hsumAbs : (∑ i : Fin n, |v i|) = |exact| := by
    simpa [exact] using sum_abs_eq_abs_sum_of_oneSigned v hv
  have hhigh_one : |high - exact| ≤ ε * |exact| := by
    simpa [high, exact, hsumAbs] using hhigh
  have hhigh_abs : |high| ≤ (1 + ε) * |exact| := by
    calc
      |high| = |(high - exact) + exact| := by ring_nf
      _ ≤ |high - exact| + |exact| := abs_add_le _ _
      _ ≤ ε * |exact| + |exact| := add_le_add hhigh_one (le_refl _)
      _ = (1 + ε) * |exact| := by ring
  have habs :=
    fl_higherPrecisionRecursiveSum_abs_error_le_of_high_bound
      highFp roundWorking n v hround hhigh
  have hbound :
      |fl_higherPrecisionRecursiveSum highFp roundWorking n v - exact| ≤
        (u * (1 + ε) + ε) * |exact| := by
    calc
      |fl_higherPrecisionRecursiveSum highFp roundWorking n v - exact|
          = |exact -
              fl_higherPrecisionRecursiveSum highFp roundWorking n v| := by
              rw [abs_sub_comm]
      _ ≤ u * |high| + ε * ∑ i : Fin n, |v i| := by
            simpa [high, exact] using habs
      _ = u * |high| + ε * |exact| := by rw [hsumAbs]
      _ ≤ u * ((1 + ε) * |exact|) + ε * |exact| := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hhigh_abs hu) (le_refl _)
      _ = (u * (1 + ε) + ε) * |exact| := by ring
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound

/-- Gamma-form one-signed relative-error corollary for the higher-precision
recursive-sum-then-round trace. -/
theorem fl_higherPrecisionRecursiveSum_relError_le_gamma_oneSigned
    (highFp : FPModel) (roundWorking : ℝ → ℝ)
    (n : ℕ) (v : Fin n → ℝ) {u : ℝ}
    (hu : 0 ≤ u)
    (hround : ∀ y : ℝ, |roundWorking y - y| ≤ u * |y|)
    (hvalid : gammaValid highFp (n - 1))
    (hv : OneSigned v) (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_higherPrecisionRecursiveSum highFp roundWorking n v)
        (∑ i : Fin n, v i) ≤
      u * (1 + gamma highFp (n - 1)) + gamma highFp (n - 1) :=
  fl_higherPrecisionRecursiveSum_relError_le_of_high_bound_oneSigned
    highFp roundWorking n v hu hround
    (recursiveSum_forward_error_bound highFp n v hvalid) hv hsum

/-- Recursive summation has a relative-form forward bound for one-signed data:
the absolute error is at most `gamma (n-1)` times the magnitude of the exact
sum. -/
theorem recursiveSum_forward_error_bound_oneSigned (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (hn : gammaValid fp (n - 1)) (hv : OneSigned v) :
    |fl_recursiveSum fp n v - ∑ i : Fin n, v i| ≤
      gamma fp (n - 1) * |∑ i : Fin n, v i| := by
  have hbound := recursiveSum_forward_error_bound fp n v hn
  simpa [sum_abs_eq_abs_sum_of_oneSigned v hv] using hbound

/-- Recursive summation relative-error corollary for one-signed data.  The
nonzero exact-sum hypothesis is the standard domain condition for Higham's
relative error. -/
theorem recursiveSum_relError_le_gamma_of_oneSigned (fp : FPModel) (n : ℕ)
    (v : Fin n → ℝ) (hn : gammaValid fp (n - 1)) (hv : OneSigned v)
    (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_recursiveSum fp n v) (∑ i : Fin n, v i) ≤
      gamma fp (n - 1) := by
  have hden : 0 < |∑ i : Fin n, v i| := abs_pos.mpr hsum
  have hbound := recursiveSum_forward_error_bound_oneSigned fp n v hn hv
  unfold relError
  rw [div_le_iff₀ hden]
  exact hbound

/-- Source-shaped `nu` corollary for recursive summation on one-signed data.

This specializes the generic Algorithm 4.1 `n*u` corollary to the recursive
chain. -/
theorem recursiveSum_relError_le_n_mul_u_of_oneSigned (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n) (hvalid : gammaValid fp (n - 1))
    (hsmall : (n : ℝ) * (((n - 1 : ℕ) : ℝ) * fp.u) ≤ 1)
    (v : Fin n → ℝ) (hv : OneSigned v)
    (hsum : (∑ i : Fin n, v i) ≠ 0) :
    relError (fl_recursiveSum fp n v) (∑ i : Fin n, v i) ≤
      (n : ℝ) * fp.u := by
  exact le_trans
    (recursiveSum_relError_le_gamma_of_oneSigned fp n v hvalid hv hsum)
    (gamma_pred_le_n_mul_u_of_n_mul_pred_u_le_one fp hn_pos hvalid hsmall)

-- ============================================================
-- Running error bound (Higham §4.2, equation 4.3)
-- ============================================================

/-- The sequence of pre-rounding pairwise sums during recursive summation.
    At step `i`, this is `fl_recursiveSum fp i.val (v ∘ castSucc...) + v i`,
    i.e., the exact sum of the accumulated result and the new element,
    before rounding. This matches the `ŝₖ` quantities in Higham eq. (4.3). -/
noncomputable def fl_partialSums (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fl_recursiveSum fp i.val (fun j => v ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) + v i

/-- Reindex a prefix over `Fin k` as the corresponding filtered sum over
`Fin n`. -/
private lemma sum_fin_eq_sum_filter_lt {n k : ℕ} (hk : k ≤ n)
    (f : Fin n → ℝ) :
    (∑ t : Fin k, f ⟨t.val, by omega⟩) =
      Finset.sum (Finset.filter (fun j : Fin n => j.val < k) Finset.univ) f := by
  classical
  have hinj : ∀ a : Fin k, a ∈ Finset.univ →
      ∀ b : Fin k, b ∈ Finset.univ →
      (⟨a.val, by omega⟩ : Fin n) = ⟨b.val, by omega⟩ → a = b :=
    fun a _ b _ hab => Fin.ext (by simp only [Fin.mk.injEq] at hab; exact hab)
  have himg : Finset.image (fun (t : Fin k) => (⟨t.val, by omega⟩ : Fin n))
      Finset.univ = Finset.filter (fun j : Fin n => j.val < k) Finset.univ := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩
      simp
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext (by simp)⟩
  rw [← himg, Finset.sum_image hinj]

/-- A prefix absolute sum together with the current entry is bounded by the
full input absolute sum. -/
private lemma prefix_abs_sum_add_current_le_total_abs {n : ℕ}
    (v : Fin n → ℝ) (i : Fin n) :
    (∑ t : Fin i.val, |v ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩|) +
        |v i| ≤
      ∑ j : Fin n, |v j| := by
  classical
  have hprefix :
      (∑ t : Fin i.val, |v ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩|) =
        Finset.sum
          (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)
          (fun j => |v j|) := by
    simpa using
      (sum_fin_eq_sum_filter_lt (n := n) (k := i.val)
        (Nat.le_of_lt i.isLt) (fun j : Fin n => |v j|))
  have hi_mem :
      i ∈ Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ := by
    simp
  have herase :
      (Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ).erase i =
        Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hne : j.val ≠ i.val := by
        intro hv
        exact h.1 (Fin.ext hv)
      exact Nat.lt_of_le_of_ne h.2 hne
    · intro hlt
      exact ⟨by
        intro hji
        have hv : j.val = i.val := by rw [hji]
        omega, le_of_lt hlt⟩
  have hfilter_decomp :
      |v i| +
          Finset.sum
            (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)
            (fun j => |v j|) =
        Finset.sum
          (Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ)
          (fun j => |v j|) := by
    have hadd :=
      (Finset.add_sum_erase
        (Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ)
        (fun j : Fin n => |v j|) hi_mem)
    rw [herase] at hadd
    exact hadd
  have hfilter_le :
      Finset.sum
          (Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ)
          (fun j => |v j|) ≤
        ∑ j : Fin n, |v j| := by
    exact
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun j : Fin n => j.val ≤ i.val) Finset.univ)
        (by
          intro j _hj _hnot
          exact abs_nonneg (v j))
  rw [hprefix]
  have hleft :
      Finset.sum
          (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)
          (fun j => |v j|) + |v i| =
        Finset.sum
          (Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ)
          (fun j => |v j|) := by
    linarith [hfilter_decomp]
  rw [hleft]
  exact hfilter_le

/-- Each recursive-summation pre-rounding partial sum is bounded by the full
input absolute sum, up to the uniform `(1 + gamma(n-1))` factor. -/
theorem fl_partialSums_abs_le_one_add_gamma_mul_total_abs
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ)
    (hgamma : gammaValid fp (n - 1)) (i : Fin n) :
    |fl_partialSums fp v i| ≤
      (1 + gamma fp (n - 1)) * ∑ j : Fin n, |v j| := by
  let pref : Fin i.val → ℝ :=
    fun j => v ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
  let prefixAbs : ℝ := ∑ j : Fin i.val, |pref j|
  have hvalid_i : gammaValid fp (i.val - 1) :=
    gammaValid_mono fp (by omega) hgamma
  have hprefix_bound :
      |fl_recursiveSum fp i.val pref| ≤
        (1 + gamma fp (i.val - 1)) * prefixAbs := by
    simpa [prefixAbs, pref] using
      recursiveSum_abs_le_one_add_gamma_mul_sum_abs fp i.val pref hvalid_i
  have hgamma_le : gamma fp (i.val - 1) ≤ gamma fp (n - 1) :=
    gamma_mono fp (by omega) hgamma
  have hprefixAbs_nonneg : 0 ≤ prefixAbs := by
    exact Finset.sum_nonneg fun j _hj => abs_nonneg (pref j)
  have hprefix_uniform :
      |fl_recursiveSum fp i.val pref| ≤
        (1 + gamma fp (n - 1)) * prefixAbs := by
    exact le_trans hprefix_bound
      (mul_le_mul_of_nonneg_right (by linarith) hprefixAbs_nonneg)
  have hfactor_nonneg : 0 ≤ 1 + gamma fp (n - 1) := by
    nlinarith [gamma_nonneg fp hgamma]
  have hfactor_ge_one : 1 ≤ 1 + gamma fp (n - 1) := by
    nlinarith [gamma_nonneg fp hgamma]
  have hpartial :
      |fl_partialSums fp v i| ≤
        |fl_recursiveSum fp i.val pref| + |v i| := by
    simpa [fl_partialSums, pref] using
      abs_add_le (fl_recursiveSum fp i.val pref) (v i)
  calc
    |fl_partialSums fp v i|
        ≤ |fl_recursiveSum fp i.val pref| + |v i| := hpartial
    _ ≤ (1 + gamma fp (n - 1)) * prefixAbs + |v i| := by
      exact add_le_add hprefix_uniform (le_refl |v i|)
    _ ≤ (1 + gamma fp (n - 1)) * prefixAbs +
          (1 + gamma fp (n - 1)) * |v i| := by
      exact add_le_add (le_refl ((1 + gamma fp (n - 1)) * prefixAbs))
        (by
          simpa [one_mul] using
            mul_le_mul_of_nonneg_right hfactor_ge_one (abs_nonneg (v i)))
    _ = (1 + gamma fp (n - 1)) * (prefixAbs + |v i|) := by ring
    _ ≤ (1 + gamma fp (n - 1)) * ∑ j : Fin n, |v j| := by
      exact mul_le_mul_of_nonneg_left
        (by
          simpa [prefixAbs, pref] using
            prefix_abs_sum_add_current_le_total_abs v i)
        hfactor_nonneg

/-- Summed version of `fl_partialSums_abs_le_one_add_gamma_mul_total_abs`. -/
theorem fl_partialSums_abs_sum_le_n_mul_one_add_gamma_mul_sum_abs
    (fp : FPModel) (n : ℕ) (v : Fin n → ℝ)
    (hgamma : gammaValid fp (n - 1)) :
    ∑ i : Fin n, |fl_partialSums fp v i| ≤
      ((n : ℝ) * (1 + gamma fp (n - 1))) *
        ∑ j : Fin n, |v j| := by
  calc
    ∑ i : Fin n, |fl_partialSums fp v i|
        ≤ ∑ i : Fin n,
            (1 + gamma fp (n - 1)) * ∑ j : Fin n, |v j| := by
      apply Finset.sum_le_sum
      intro i _hi
      exact fl_partialSums_abs_le_one_add_gamma_mul_total_abs fp v hgamma i
    _ = ((n : ℝ) * (1 + gamma fp (n - 1))) *
          ∑ j : Fin n, |v j| := by
      rw [Finset.sum_const]
      simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- **Recursive summation running error bound** (Higham §4.2, equation 4.3).

    The absolute error is bounded by `u` times the sum of absolute values of
    the pre-rounding pairwise sums at each step:
      `|fl_recursiveSum fp n v − ∑ i, v i| ≤ u * ∑ i, |fl_partialSums fp v i|`

    Here `fl_partialSums fp v i` is the exact sum `Ŝᵢ + vᵢ` just before
    rounding at step `i`, corresponding to Higham (4.3).

    Proof sketch: induction on n, peeling the last step.  At each step the
    error splits as `E_{n+1} = E_n + δ * (Ŝₙ + vₙ)` where `|δ| ≤ u` and
    `Ŝₙ + vₙ = fl_partialSums fp v (Fin.last n)`. -/
theorem recursiveSum_running_error_bound (fp : FPModel) (n : ℕ) (v : Fin n → ℝ) :
    |fl_recursiveSum fp n v - ∑ i : Fin n, v i| ≤
      fp.u * ∑ i : Fin n, |fl_partialSums fp v i| := by
  induction n with
  | zero => simp [fl_recursiveSum, fl_partialSums]
  | succ n ih =>
    -- Peel the last fold step
    have hfold : fl_recursiveSum fp (n + 1) v =
        fp.fl_add (fl_recursiveSum fp n (fun i => v i.castSucc)) (v (Fin.last n)) :=
      Fin.foldl_succ_last _ _
    -- Extract rounding error δ from the last fl_add
    obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (fl_recursiveSum fp n (fun i => v i.castSucc)) (v (Fin.last n))
    -- Abbreviations
    set Sn := fl_recursiveSum fp n (fun i => v i.castSucc)
    set vn := v (Fin.last n)
    -- Helper: two fl_recursiveSum calls with pointwise-equal functions are equal
    have reindex : ∀ (m : ℕ) (w₁ w₂ : Fin m → ℝ),
        (∀ j : Fin m, w₁ j = w₂ j) →
        fl_recursiveSum fp m w₁ = fl_recursiveSum fp m w₂ :=
      fun m w₁ w₂ h => by congr 1; funext j; exact h j
    -- The last pre-rounding pairwise sum equals Sn + vn
    have hlast : fl_partialSums fp v (Fin.last n) = Sn + vn := by
      unfold fl_partialSums
      -- (Fin.last n).val = n, and the fn arg equals (fun i => v i.castSucc)
      have hfn : fl_recursiveSum fp (Fin.last n).val
                   (fun j => v ⟨j.val, Nat.lt_trans j.isLt (Fin.last n).isLt⟩) = Sn :=
        reindex n _ _ (fun j => by congr 1)
      have hvn : v (Fin.last n) = vn := rfl
      rw [hfn, hvn]
    -- Compatibility: fl_partialSums fp v i.castSucc = fl_partialSums fp (v ∘ castSucc) i
    have hcompat : ∀ i : Fin n,
        fl_partialSums fp v i.castSucc = fl_partialSums fp (fun j => v j.castSucc) i := by
      intro i
      unfold fl_partialSums
      -- The recursive sum arguments are pointwise equal
      have hfn : fl_recursiveSum fp (Fin.castSucc i).val
                   (fun j => v ⟨j.val, Nat.lt_trans j.isLt (Fin.castSucc i).isLt⟩) =
                 fl_recursiveSum fp i.val
                   (fun j => (fun k : Fin n => v k.castSucc) ⟨j.val,
                     Nat.lt_trans j.isLt i.isLt⟩) := by
        simp only [Fin.val_castSucc]
        apply reindex
        intro j
        congr 1
      have hvn : v (Fin.castSucc i) = (fun k : Fin n => v k.castSucc) i := rfl
      rw [hfn, hvn]
    -- Error decomposition: E_{n+1} = E_n + δ * (Sn + vn)
    have herr : fl_recursiveSum fp (n + 1) v - ∑ i : Fin (n + 1), v i =
        (Sn - ∑ i : Fin n, v i.castSucc) + δ * (Sn + vn) := by
      rw [hfold, hfl, Fin.sum_univ_castSucc]; ring
    -- IH specialised to (v ∘ castSucc)
    have ih' := ih (fun i => v i.castSucc)
    -- Split the sum of partial sums
    have hpsum : ∑ i : Fin (n + 1), |fl_partialSums fp v i| =
        ∑ i : Fin n, |fl_partialSums fp (fun j => v j.castSucc) i| +
        |fl_partialSums fp v (Fin.last n)| := by
      rw [Fin.sum_univ_castSucc]
      congr 1
    -- Triangle inequality (using abs_le + linarith instead of unavailable abs_add)
    have htri : |(Sn - ∑ i : Fin n, v i.castSucc) + δ * (Sn + vn)| ≤
        |Sn - ∑ i : Fin n, v i.castSucc| + |δ * (Sn + vn)| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Sn - ∑ i : Fin n, v i.castSucc),
                  neg_abs_le (δ * (Sn + vn))]
      · linarith [le_abs_self (Sn - ∑ i : Fin n, v i.castSucc),
                  le_abs_self (δ * (Sn + vn))]
    -- Bound |δ * (Sn + vn)| ≤ fp.u * |fl_partialSums fp v (Fin.last n)|
    have hbound_last : |δ * (Sn + vn)| ≤ fp.u * |fl_partialSums fp v (Fin.last n)| := by
      rw [hlast, abs_mul]
      exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
    rw [herr, hpsum]
    calc |(Sn - ∑ i : Fin n, v i.castSucc) + δ * (Sn + vn)|
        ≤ |Sn - ∑ i : Fin n, v i.castSucc| + |δ * (Sn + vn)| := htri
      _ ≤ fp.u * ∑ i : Fin n, |fl_partialSums fp (fun j => v j.castSucc) i| +
            fp.u * |fl_partialSums fp v (Fin.last n)| := by linarith [ih', hbound_last]
      _ = fp.u * (∑ i : Fin n, |fl_partialSums fp (fun j => v j.castSucc) i| +
            |fl_partialSums fp v (Fin.last n)|) := by ring

end NumStability
