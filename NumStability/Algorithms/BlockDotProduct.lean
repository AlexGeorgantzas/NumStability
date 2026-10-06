-- Algorithms/BlockDotProduct.lean

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct

namespace NumStability

open scoped BigOperators

/-!
# Block dot products

This file formalizes the Chapter 3 observation that splitting an inner product
into `k` equal-length pieces, forming each partial dot product, and then adding
the partial sums changes the error radius from `gamma n` to
`gamma (n / k + k - 1)` in the equal-block case.
-/

/-- Dot product evaluated in `q + 1` equal blocks of length `b`.

The first block is used as the initial accumulator, so the outer stage performs
exactly `q` rounded additions.  Thus `q + 1` is the source's number of pieces
`k`, and the final radius below is `gamma (b + q) = gamma (b + k - 1)`. -/
noncomputable def fl_blockDotProduct (fp : FPModel) (q b : ℕ)
    (x y : Fin (q + 1) → Fin b → ℝ) : ℝ :=
  Fin.foldl q
    (fun acc r => fp.fl_add acc (fl_dotProduct fp b (x r.succ) (y r.succ)))
    (fl_dotProduct fp b (x 0) (y 0))

/-- **Block dot-product backward error**.

For `q + 1` blocks of length `b`, every term in the block algorithm carries a
single componentwise perturbation bounded by `gamma (b + q)`.  Written with
`k = q + 1` and `n = b * k`, this is Higham's
`gamma (n / k + k - 1)` bound. -/
theorem blockDotProduct_backward_error (fp : FPModel) (q b : ℕ)
    (x y : Fin (q + 1) → Fin b → ℝ)
    (hγ : gammaValid fp (b + q)) :
    ∃ η : Fin (q + 1) → Fin b → ℝ,
      (∀ r l, |η r l| ≤ gamma fp (b + q)) ∧
      fl_blockDotProduct fp q b x y =
        ∑ r : Fin (q + 1), ∑ l : Fin b,
          x r l * y r l * (1 + η r l) := by
  have hγb : gammaValid fp b := gammaValid_mono fp (by omega) hγ
  have hγq : gammaValid fp q := gammaValid_mono fp (by omega) hγ
  let ηInner : Fin (q + 1) → Fin b → ℝ :=
    fun r => Classical.choose (dotProduct_backward_error fp b (x r) (y r) hγb)
  have hηInner :
      ∀ r,
        (∀ l, |ηInner r l| ≤ gamma fp b) ∧
          fl_dotProduct fp b (x r) (y r) =
            ∑ l : Fin b, x r l * y r l * (1 + ηInner r l) := by
    intro r
    exact Classical.choose_spec (dotProduct_backward_error fp b (x r) (y r) hγb)
  obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ :=
    fl_sum_error_init fp q
      (fun r => fl_dotProduct fp b (x r.succ) (y r.succ))
      (fl_dotProduct fp b (x 0) (y 0)) hγq
  let η : Fin (q + 1) → Fin b → ℝ :=
    Fin.cases
      (fun l =>
        Classical.choose
          (gamma_mul fp b q (ηInner 0 l) Θ ((hηInner 0).1 l) hΘ hγ))
      (fun r l =>
        Classical.choose
          (gamma_mul fp b q (ηInner r.succ l) (θ r)
            ((hηInner r.succ).1 l) (hθ r) hγ))
  have hη : ∀ r l, |η r l| ≤ gamma fp (b + q) := by
    intro r
    refine Fin.cases ?_ ?_ r
    · intro l
      simp only [η, Fin.cases_zero]
      exact
        (Classical.choose_spec
          (gamma_mul fp b q (ηInner 0 l) Θ ((hηInner 0).1 l) hΘ hγ)).1
    · intro r l
      simp only [η, Fin.cases_succ]
      exact
        (Classical.choose_spec
          (gamma_mul fp b q (ηInner r.succ l) (θ r)
            ((hηInner r.succ).1 l) (hθ r) hγ)).1
  refine ⟨η, hη, ?_⟩
  have hmain :
      fl_blockDotProduct fp q b x y =
        (∑ l : Fin b, x 0 l * y 0 l * (1 + ηInner 0 l)) * (1 + Θ) +
          ∑ r : Fin q,
            (∑ l : Fin b, x r.succ l * y r.succ l *
              (1 + ηInner r.succ l)) * (1 + θ r) := by
    rw [fl_blockDotProduct, hfold, (hηInner 0).2]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [(hηInner r.succ).2]
  rw [hmain, Fin.sum_univ_succ]
  congr 1
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    have hcomb :
        (1 + ηInner 0 l) * (1 + Θ) = 1 + η 0 l := by
      simp only [η, Fin.cases_zero]
      exact
        (Classical.choose_spec
          (gamma_mul fp b q (ηInner 0 l) Θ ((hηInner 0).1 l) hΘ hγ)).2
    calc
      x 0 l * y 0 l * (1 + ηInner 0 l) * (1 + Θ) =
          x 0 l * y 0 l * ((1 + ηInner 0 l) * (1 + Θ)) := by ring
      _ = x 0 l * y 0 l * (1 + η 0 l) := by rw [hcomb]
  · apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    have hcomb :
        (1 + ηInner r.succ l) * (1 + θ r) = 1 + η r.succ l := by
      simp only [η, Fin.cases_succ]
      exact
        (Classical.choose_spec
          (gamma_mul fp b q (ηInner r.succ l) (θ r)
            ((hηInner r.succ).1 l) (hθ r) hγ)).2
    calc
      x r.succ l * y r.succ l * (1 + ηInner r.succ l) * (1 + θ r) =
          x r.succ l * y r.succ l *
            ((1 + ηInner r.succ l) * (1 + θ r)) := by ring
      _ = x r.succ l * y r.succ l * (1 + η r.succ l) := by rw [hcomb]

/-- **Block dot-product forward error bound**.

The forward form follows directly from the componentwise backward error:
the exact double sum is perturbed termwise by at most `gamma (b + q)`. -/
theorem blockDotProduct_error_bound (fp : FPModel) (q b : ℕ)
    (x y : Fin (q + 1) → Fin b → ℝ)
    (hγ : gammaValid fp (b + q)) :
    |fl_blockDotProduct fp q b x y -
        ∑ r : Fin (q + 1), ∑ l : Fin b, x r l * y r l| ≤
      gamma fp (b + q) *
        ∑ r : Fin (q + 1), ∑ l : Fin b, |x r l| * |y r l| := by
  obtain ⟨η, hη, hfl⟩ := blockDotProduct_backward_error fp q b x y hγ
  have herr :
      fl_blockDotProduct fp q b x y -
          ∑ r : Fin (q + 1), ∑ l : Fin b, x r l * y r l =
        ∑ r : Fin (q + 1), ∑ l : Fin b, x r l * y r l * η r l := by
    rw [hfl, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [herr]
  calc
    |∑ r : Fin (q + 1), ∑ l : Fin b, x r l * y r l * η r l|
        ≤ ∑ r : Fin (q + 1), |∑ l : Fin b, x r l * y r l * η r l| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin (q + 1), ∑ l : Fin b, |x r l * y r l * η r l| := by
          apply Finset.sum_le_sum
          intro r _
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r : Fin (q + 1), ∑ l : Fin b,
            |x r l| * |y r l| * |η r l| := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro l _
          rw [abs_mul, abs_mul]
    _ ≤ ∑ r : Fin (q + 1), ∑ l : Fin b,
            |x r l| * |y r l| * gamma fp (b + q) := by
          apply Finset.sum_le_sum
          intro r _
          apply Finset.sum_le_sum
          intro l _
          exact mul_le_mul_of_nonneg_left (hη r l)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = gamma fp (b + q) *
          ∑ r : Fin (q + 1), ∑ l : Fin b, |x r l| * |y r l| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring

/-- Two equal pieces give the displayed `gamma (b + 1)` radius. -/
theorem twoPieceDotProduct_error_bound (fp : FPModel) (b : ℕ)
    (x y : Fin 2 → Fin b → ℝ)
    (hγ : gammaValid fp (b + 1)) :
    |fl_blockDotProduct fp 1 b x y -
        ∑ r : Fin 2, ∑ l : Fin b, x r l * y r l| ≤
      gamma fp (b + 1) *
        ∑ r : Fin 2, ∑ l : Fin b, |x r l| * |y r l| := by
  simpa using blockDotProduct_error_bound fp 1 b x y hγ

/-- Continuous relaxation of the block-count work index.

For fixed positive problem size `n`, the real-valued expression
`n / k + k - 1` decomposes as a nonnegative square term plus
`2 * sqrt n - 1`, so the source's balancing rule `k ≈ sqrt n` is exactly the
continuous optimum. -/
theorem blockDotProduct_real_index_decomposition {n k : ℝ}
    (hn : 0 ≤ n) (hk : k ≠ 0) :
    n / k + k - 1 =
      2 * Real.sqrt n - 1 + (k - Real.sqrt n) ^ 2 / k := by
  have hsqr : (Real.sqrt n) ^ 2 = n := by
    simpa [sq] using Real.sq_sqrt hn
  field_simp [hk]
  nlinarith [hsqr]

/-- The continuous block-count index is minimized at `sqrt n`. -/
theorem blockDotProduct_real_index_ge_optimum {n k : ℝ}
    (hn : 0 ≤ n) (hk : 0 < k) :
    2 * Real.sqrt n - 1 ≤ n / k + k - 1 := by
  rw [blockDotProduct_real_index_decomposition hn (ne_of_gt hk)]
  have hsq_nonneg : 0 ≤ (k - Real.sqrt n) ^ 2 := sq_nonneg _
  have hdiv_nonneg : 0 ≤ (k - Real.sqrt n) ^ 2 / k :=
    div_nonneg hsq_nonneg (le_of_lt hk)
  linarith

/-- At the continuous optimum `k = sqrt n`, the index is `2 * sqrt n - 1`. -/
theorem blockDotProduct_real_index_at_sqrt {n : ℝ} (hn : 0 < n) :
    n / Real.sqrt n + Real.sqrt n - 1 = 2 * Real.sqrt n - 1 := by
  have hsqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  rw [blockDotProduct_real_index_decomposition (le_of_lt hn) hsqrt_ne]
  ring

end NumStability
