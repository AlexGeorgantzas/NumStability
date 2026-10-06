-- Algorithms/LU/Doolittle.lean
--
-- Doolittle's method for LU factorization (Higham §9.2, Algorithm 9.2)
-- and its backward error analysis.
--
-- Doolittle's method computes L (unit lower triangular) and U (upper triangular)
-- column by column / row by row using inner-product formulations:
--   u_kj = a_kj - ∑_{s<k} l_ks * u_sj   for j ≥ k
--   l_ik = (a_ik - ∑_{s<k} l_is * u_sk) / u_kk   for i > k
--
-- The backward error is |L̂Û - A| ≤ γ(n)|L̂||Û| componentwise (Theorem 9.3).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.LUSolve

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §9.2  Doolittle's method specification
-- ============================================================

/-- **Doolittle's method specification** (Higham §9.2, Algorithm 9.2).

    Doolittle's method computes L and U by the recurrences:
    For k = 0, ..., n-1:
      u_kj = fl(a_kj - ∑_{s<k} l_ks u_sj)   for j ≥ k
      l_ik = fl((a_ik - ∑_{s<k} l_is u_sk) / u_kk)   for i > k

    This is mathematically equivalent to Gaussian elimination but
    organized as a "kji" or "right-looking" variant.

    This structure captures the key property: the computed factors
    satisfy `LUBackwardError` with ε = γ(n). -/
structure DoolittleLU (n : ℕ) (A L_hat U_hat : Fin n → Fin n → ℝ)
    (fp : FPModel) : Prop where
  /-- L̂ is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L_hat i i = 1
  /-- L̂ is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0
  /-- Û is upper triangular. -/
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0
  /-- U row computation: u_kj involves inner product of at most k terms.
      Each inner product is computed in floating-point with at most n
      multiply-add operations. -/
  U_computed : ∀ k j : Fin n, k.val ≤ j.val →
    ∃ θ : ℝ, |θ| ≤ gamma fp n ∧
      U_hat k j * (1 + θ) =
        A k j - ∑ s : Fin n, (if s.val < k.val then L_hat k s * U_hat s j else 0)
  /-- L column computation: l_ik = fl((a_ik - ∑ l_is u_sk) / u_kk). -/
  L_computed : ∀ i k : Fin n, k.val < i.val →
    ∃ θ : ℝ, |θ| ≤ gamma fp n ∧
      L_hat i k * U_hat k k * (1 + θ) =
        A i k - ∑ s : Fin n, (if s.val < k.val then L_hat i s * U_hat s k else 0)

/-- Literal floating-point row update used by dense Doolittle for an upper
entry.  This is the executable fold shape: start from `A k j` and subtract the
already available products `L k s * U s j`, each product and subtraction
rounded by `fp`. -/
noncomputable def flDoolittleUEntry (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (k j : Fin n) : ℝ :=
  Fin.foldl k.val
    (fun acc (s : Fin k.val) =>
      fp.fl_sub acc
        (fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ j)))
    (A k j)

/-- Literal floating-point numerator fold used by dense Doolittle for a lower
entry before division by the computed pivot. -/
noncomputable def flDoolittleLNumerator (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  Fin.foldl k.val
    (fun acc (s : Fin k.val) =>
      fp.fl_sub acc
        (fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ k)))
    (A i k)

/-- Literal floating-point lower-entry update used by dense Doolittle after
forming the rounded numerator. -/
noncomputable def flDoolittleLEntry (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  fp.fl_div (flDoolittleLNumerator fp n A L_hat U_hat i k) (U_hat k k)

/-- A masked prefix sum over `Fin n` is the same as the corresponding sum over
`Fin k.val`.  This is the small reindexing bridge between the literal
Doolittle folds and the compact recurrence certificate. -/
theorem finMaskedPrefixSum_eq_finSum {n : ℕ} (k : Fin n)
    (f : Fin n → ℝ) :
    (∑ s : Fin n, (if s.val < k.val then f s else 0)) =
      ∑ s : Fin k.val, f ⟨s.val, Nat.lt_trans s.isLt k.isLt⟩ := by
  let g : ℕ → ℝ := fun i =>
    if h : i < k.val then f ⟨i, Nat.lt_trans h k.isLt⟩ else 0
  have hleft :
      (∑ s : Fin n, (if s.val < k.val then f s else 0)) =
        ∑ i ∈ Finset.range n, g i := by
    calc
      (∑ s : Fin n, (if s.val < k.val then f s else 0))
          = ∑ s : Fin n, g s.val := by
            apply Finset.sum_congr rfl
            intro s _
            by_cases hs : s.val < k.val
            · have hfin :
                  (⟨s.val, Nat.lt_trans hs k.isLt⟩ : Fin n) = s := by
                ext
                rfl
              simp [g, hs, hfin]
            · simp [g, hs]
      _ = ∑ i ∈ Finset.range n, g i :=
          Fin.sum_univ_eq_sum_range g n
  have hright :
      (∑ s : Fin k.val, f ⟨s.val, Nat.lt_trans s.isLt k.isLt⟩) =
        ∑ i ∈ Finset.range k.val, g i := by
    calc
      (∑ s : Fin k.val, f ⟨s.val, Nat.lt_trans s.isLt k.isLt⟩)
          = ∑ s : Fin k.val, g s.val := by
            apply Finset.sum_congr rfl
            intro s _
            simp [g, s.isLt]
      _ = ∑ i ∈ Finset.range k.val, g i :=
          Fin.sum_univ_eq_sum_range g k.val
  have hfilter :
      (Finset.range n).filter (fun i => i < k.val) = Finset.range k.val := by
    ext i
    constructor
    · intro hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_trans (Finset.mem_range.mp hi) k.isLt),
          Finset.mem_range.mp hi⟩
  have hrange :
      ∑ i ∈ Finset.range n, g i = ∑ i ∈ Finset.range k.val, g i := by
    calc
      ∑ i ∈ Finset.range n, g i =
          ∑ i ∈ Finset.range n, (if i < k.val then g i else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i < k.val
            · simp [hi]
            · simp [g, hi]
      _ = ∑ i ∈ (Finset.range n).filter (fun i => i < k.val), g i := by
            rw [Finset.sum_filter]
      _ = ∑ i ∈ Finset.range k.val, g i := by
            rw [hfilter]
  rw [hleft, hright, hrange]

/-- Absolute residual budget for the literal upper-entry Doolittle subtraction
fold, measured against the exact subtraction of the rounded products that the
fold actually receives. -/
theorem flDoolittleUEntry_rounded_residual_abs_le (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (k j : Fin n)
    (hk : gammaValid fp k.val) :
    |(A k j -
      ∑ s : Fin k.val,
        fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ j)) -
        flDoolittleUEntry fp n A L_hat U_hat k j| ≤
      gamma fp k.val *
        (|A k j| +
          ∑ s : Fin k.val,
            |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
              (U_hat ⟨s.val, by omega⟩ j)|) := by
  simpa [flDoolittleUEntry] using
    fl_sub_sum_error_init_abs_residual_le fp k.val
      (fun s : Fin k.val =>
        fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ j))
      (A k j) hk

/-- Absolute residual budget for the literal lower-entry Doolittle numerator
subtraction fold, measured against the exact subtraction of the rounded products
that the fold actually receives. -/
theorem flDoolittleLNumerator_rounded_residual_abs_le (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n)
    (hk : gammaValid fp k.val) :
    |(A i k -
      ∑ s : Fin k.val,
        fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ k)) -
        flDoolittleLNumerator fp n A L_hat U_hat i k| ≤
      gamma fp k.val *
        (|A i k| +
          ∑ s : Fin k.val,
            |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
              (U_hat ⟨s.val, by omega⟩ k)|) := by
  simpa [flDoolittleLNumerator] using
    fl_sub_sum_error_init_abs_residual_le fp k.val
      (fun s : Fin k.val =>
        fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ k))
      (A i k) hk

/-- Primitive multiplication roundoff as an absolute product-error bound. -/
theorem fl_mul_abs_sub_mul_le (fp : FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  have hdiff : fp.fl_mul x y - x * y = (x * y) * δ := by
    rw [hfl]
    ring
  calc
    |fp.fl_mul x y - x * y| = |(x * y) * δ| := by rw [hdiff]
    _ = |x * y| * |δ| := by rw [abs_mul]
    _ ≤ |x * y| * fp.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = fp.u * |x * y| := by ring

/-- Primitive multiplication roundoff as a one-sided absolute product-growth
bound.  This is useful for source no-cancellation margins stated with exact
products while the implemented Doolittle fold subtracts rounded products. -/
theorem fl_mul_abs_le_one_add_u_mul_abs_mul (fp : FPModel) (x y : ℝ) :
    |fp.fl_mul x y| ≤ (1 + fp.u) * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  have hδ_bounds := abs_le.mp hδ
  have hδ_upper : δ ≤ fp.u := hδ_bounds.2
  have hδ_lower : -fp.u ≤ δ := hδ_bounds.1
  have h_upper : 1 + δ ≤ 1 + fp.u := by linarith
  have h_lower : -(1 + fp.u) ≤ 1 + δ := by linarith [hδ_lower, fp.u_nonneg]
  have h_abs : |1 + δ| ≤ 1 + fp.u := abs_le.mpr ⟨h_lower, h_upper⟩
  calc
    |fp.fl_mul x y| = |(x * y) * (1 + δ)| := by rw [hfl]
    _ = |x * y| * |1 + δ| := by rw [abs_mul]
    _ ≤ |x * y| * (1 + fp.u) :=
        mul_le_mul_of_nonneg_left h_abs (abs_nonneg _)
    _ = (1 + fp.u) * |x * y| := by ring

/-- Absolute residual budget for the literal upper-entry Doolittle subtraction
fold, now measured against the exact products rather than the rounded products
fed to the subtraction fold. -/
theorem flDoolittleUEntry_exact_product_residual_abs_le (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (k j : Fin n)
    (hk : gammaValid fp k.val) :
    |(A k j -
      ∑ s : Fin k.val,
        L_hat k ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ j) -
        flDoolittleUEntry fp n A L_hat U_hat k j| ≤
      gamma fp k.val *
        (|A k j| +
          ∑ s : Fin k.val,
            |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
              (U_hat ⟨s.val, by omega⟩ j)|) +
        fp.u *
          ∑ s : Fin k.val,
            |L_hat k ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ j| := by
  let rounded : Fin k.val → ℝ := fun s =>
    fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
      (U_hat ⟨s.val, by omega⟩ j)
  let exact : Fin k.val → ℝ := fun s =>
    L_hat k ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ j
  have hfold :
      |(A k j - ∑ s : Fin k.val, rounded s) -
          flDoolittleUEntry fp n A L_hat U_hat k j| ≤
        gamma fp k.val *
          (|A k j| + ∑ s : Fin k.val, |rounded s|) := by
    simpa [rounded] using
      flDoolittleUEntry_rounded_residual_abs_le fp n A L_hat U_hat k j hk
  have hprod :
      |(∑ s : Fin k.val, rounded s) - ∑ s : Fin k.val, exact s| ≤
        fp.u * ∑ s : Fin k.val, |exact s| := by
    calc
      |(∑ s : Fin k.val, rounded s) - ∑ s : Fin k.val, exact s|
          = |∑ s : Fin k.val, (rounded s - exact s)| := by
            rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ s : Fin k.val, |rounded s - exact s| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s : Fin k.val, fp.u * |exact s| := by
          exact Finset.sum_le_sum (fun s _ => by
            simpa [rounded, exact] using
              fl_mul_abs_sub_mul_le fp
                (L_hat k ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ j))
      _ = fp.u * ∑ s : Fin k.val, |exact s| := by
          rw [Finset.mul_sum]
  have htri :
      |(A k j - ∑ s : Fin k.val, exact s) -
          flDoolittleUEntry fp n A L_hat U_hat k j| ≤
        |(A k j - ∑ s : Fin k.val, rounded s) -
          flDoolittleUEntry fp n A L_hat U_hat k j| +
        |(∑ s : Fin k.val, rounded s) - ∑ s : Fin k.val, exact s| := by
    have hdecomp :
        (A k j - ∑ s : Fin k.val, exact s) -
            flDoolittleUEntry fp n A L_hat U_hat k j =
          ((A k j - ∑ s : Fin k.val, rounded s) -
              flDoolittleUEntry fp n A L_hat U_hat k j) +
            ((∑ s : Fin k.val, rounded s) - ∑ s : Fin k.val, exact s) := by
      ring
    rw [hdecomp]
    exact abs_add_le _ _
  have hmain :
      |(A k j - ∑ s : Fin k.val, exact s) -
          flDoolittleUEntry fp n A L_hat U_hat k j| ≤
        gamma fp k.val *
          (|A k j| + ∑ s : Fin k.val, |rounded s|) +
        fp.u * ∑ s : Fin k.val, |exact s| :=
    calc
      |(A k j - ∑ s : Fin k.val, exact s) -
          flDoolittleUEntry fp n A L_hat U_hat k j|
          ≤ |(A k j - ∑ s : Fin k.val, rounded s) -
              flDoolittleUEntry fp n A L_hat U_hat k j| +
            |(∑ s : Fin k.val, rounded s) -
              ∑ s : Fin k.val, exact s| := htri
      _ ≤ gamma fp k.val *
            (|A k j| + ∑ s : Fin k.val, |rounded s|) +
          fp.u * ∑ s : Fin k.val, |exact s| :=
            add_le_add hfold hprod
  simpa [rounded, exact] using hmain

/-- Absolute residual budget for the literal lower-entry Doolittle numerator
subtraction fold, now measured against the exact products rather than the
rounded products fed to the subtraction fold. -/
theorem flDoolittleLNumerator_exact_product_residual_abs_le (fp : FPModel)
    (n : ℕ) (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n)
    (hk : gammaValid fp k.val) :
    |(A i k -
      ∑ s : Fin k.val,
        L_hat i ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ k) -
        flDoolittleLNumerator fp n A L_hat U_hat i k| ≤
      gamma fp k.val *
        (|A i k| +
          ∑ s : Fin k.val,
            |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
              (U_hat ⟨s.val, by omega⟩ k)|) +
        fp.u *
          ∑ s : Fin k.val,
            |L_hat i ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ k| := by
  let rounded : Fin k.val → ℝ := fun s =>
    fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
      (U_hat ⟨s.val, by omega⟩ k)
  let exact : Fin k.val → ℝ := fun s =>
    L_hat i ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ k
  have hfold :
      |(A i k - ∑ s : Fin k.val, rounded s) -
          flDoolittleLNumerator fp n A L_hat U_hat i k| ≤
        gamma fp k.val *
          (|A i k| + ∑ s : Fin k.val, |rounded s|) := by
    simpa [rounded] using
      flDoolittleLNumerator_rounded_residual_abs_le fp n A L_hat U_hat i k hk
  have hprod :
      |(∑ s : Fin k.val, rounded s) - ∑ s : Fin k.val, exact s| ≤
        fp.u * ∑ s : Fin k.val, |exact s| := by
    calc
      |(∑ s : Fin k.val, rounded s) - ∑ s : Fin k.val, exact s|
          = |∑ s : Fin k.val, (rounded s - exact s)| := by
            rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ s : Fin k.val, |rounded s - exact s| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s : Fin k.val, fp.u * |exact s| := by
          exact Finset.sum_le_sum (fun s _ => by
            simpa [rounded, exact] using
              fl_mul_abs_sub_mul_le fp
                (L_hat i ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ k))
      _ = fp.u * ∑ s : Fin k.val, |exact s| := by
          rw [Finset.mul_sum]
  have htri :
      |(A i k - ∑ s : Fin k.val, exact s) -
          flDoolittleLNumerator fp n A L_hat U_hat i k| ≤
        |(A i k - ∑ s : Fin k.val, rounded s) -
          flDoolittleLNumerator fp n A L_hat U_hat i k| +
        |(∑ s : Fin k.val, rounded s) - ∑ s : Fin k.val, exact s| := by
    have hdecomp :
        (A i k - ∑ s : Fin k.val, exact s) -
            flDoolittleLNumerator fp n A L_hat U_hat i k =
          ((A i k - ∑ s : Fin k.val, rounded s) -
              flDoolittleLNumerator fp n A L_hat U_hat i k) +
            ((∑ s : Fin k.val, rounded s) - ∑ s : Fin k.val, exact s) := by
      ring
    rw [hdecomp]
    exact abs_add_le _ _
  have hmain :
      |(A i k - ∑ s : Fin k.val, exact s) -
          flDoolittleLNumerator fp n A L_hat U_hat i k| ≤
        gamma fp k.val *
          (|A i k| + ∑ s : Fin k.val, |rounded s|) +
        fp.u * ∑ s : Fin k.val, |exact s| :=
    calc
      |(A i k - ∑ s : Fin k.val, exact s) -
          flDoolittleLNumerator fp n A L_hat U_hat i k|
          ≤ |(A i k - ∑ s : Fin k.val, rounded s) -
              flDoolittleLNumerator fp n A L_hat U_hat i k| +
            |(∑ s : Fin k.val, rounded s) -
              ∑ s : Fin k.val, exact s| := htri
      _ ≤ gamma fp k.val *
            (|A i k| + ∑ s : Fin k.val, |rounded s|) +
          fp.u * ∑ s : Fin k.val, |exact s| :=
            add_le_add hfold hprod
  simpa [rounded, exact] using hmain

/-- Exact-product upper-entry residual in the masked `Fin n` shape used by the
compact Doolittle recurrence certificate. -/
theorem flDoolittleUEntry_masked_exact_product_residual_abs_le (fp : FPModel)
    (n : ℕ) (A L_hat U_hat : Fin n → Fin n → ℝ) (k j : Fin n)
    (hk : gammaValid fp k.val) :
    |(A k j -
      ∑ s : Fin n,
        (if s.val < k.val then L_hat k s * U_hat s j else 0)) -
        flDoolittleUEntry fp n A L_hat U_hat k j| ≤
      gamma fp k.val *
        (|A k j| +
          ∑ s : Fin k.val,
            |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
              (U_hat ⟨s.val, by omega⟩ j)|) +
        fp.u *
          ∑ s : Fin k.val,
            |L_hat k ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ j| := by
  have hsum :=
    finMaskedPrefixSum_eq_finSum k (fun s : Fin n => L_hat k s * U_hat s j)
  rw [hsum]
  exact
    flDoolittleUEntry_exact_product_residual_abs_le fp n A L_hat U_hat k j hk

/-- Exact-product lower-numerator residual in the masked `Fin n` shape used by
the compact Doolittle recurrence certificate. -/
theorem flDoolittleLNumerator_masked_exact_product_residual_abs_le (fp : FPModel)
    (n : ℕ) (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n)
    (hk : gammaValid fp k.val) :
    |(A i k -
      ∑ s : Fin n,
        (if s.val < k.val then L_hat i s * U_hat s k else 0)) -
        flDoolittleLNumerator fp n A L_hat U_hat i k| ≤
      gamma fp k.val *
        (|A i k| +
          ∑ s : Fin k.val,
            |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
              (U_hat ⟨s.val, by omega⟩ k)|) +
        fp.u *
          ∑ s : Fin k.val,
            |L_hat i ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ k| := by
  have hsum :=
    finMaskedPrefixSum_eq_finSum k (fun s : Fin n => L_hat i s * U_hat s k)
  rw [hsum]
  exact
    flDoolittleLNumerator_exact_product_residual_abs_le
      fp n A L_hat U_hat i k hk

/-- Rounded division by the computed Doolittle pivot gives a visible absolute
residual after multiplying the stored lower entry by that pivot. -/
theorem flDoolittleLEntry_mul_pivot_sub_numerator_abs_le (fp : FPModel)
    (n : ℕ) (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n)
    (hU : U_hat k k ≠ 0) :
    |flDoolittleLNumerator fp n A L_hat U_hat i k -
        flDoolittleLEntry fp n A L_hat U_hat i k * U_hat k k| ≤
      fp.u * |flDoolittleLNumerator fp n A L_hat U_hat i k| := by
  let num := flDoolittleLNumerator fp n A L_hat U_hat i k
  let piv := U_hat k k
  have hpiv : piv ≠ 0 := by
    simpa [piv] using hU
  obtain ⟨δ, hδ, hfl⟩ := fp.model_div num piv hpiv
  have hentry :
      flDoolittleLEntry fp n A L_hat U_hat i k =
        (num / piv) * (1 + δ) := by
    simpa [flDoolittleLEntry, num, piv] using hfl
  have hmul :
      flDoolittleLEntry fp n A L_hat U_hat i k * U_hat k k =
        num * (1 + δ) := by
    calc
      flDoolittleLEntry fp n A L_hat U_hat i k * U_hat k k
          = ((num / piv) * (1 + δ)) * piv := by
              simp [hentry, piv]
      _ = num * (1 + δ) := by
              field_simp [hpiv]
  calc
    |flDoolittleLNumerator fp n A L_hat U_hat i k -
        flDoolittleLEntry fp n A L_hat U_hat i k * U_hat k k|
        = |num - num * (1 + δ)| := by
            simp [num, hmul]
    _ = |-(num * δ)| := by
            ring_nf
    _ = |num| * |δ| := by
            rw [abs_neg, abs_mul]
    _ ≤ |num| * fp.u :=
            mul_le_mul_of_nonneg_left hδ (abs_nonneg num)
    _ = fp.u * |flDoolittleLNumerator fp n A L_hat U_hat i k| := by
            ring

/-- Masked exact-product lower-entry residual after rounded division and
multiplication by the computed pivot. -/
theorem flDoolittleLEntry_masked_exact_product_residual_abs_le (fp : FPModel)
    (n : ℕ) (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n)
    (hk : gammaValid fp k.val) (hU : U_hat k k ≠ 0)
    (hentry : L_hat i k = flDoolittleLEntry fp n A L_hat U_hat i k) :
    |(A i k -
      ∑ s : Fin n,
        (if s.val < k.val then L_hat i s * U_hat s k else 0)) -
        L_hat i k * U_hat k k| ≤
      (gamma fp k.val *
        (|A i k| +
          ∑ s : Fin k.val,
            |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
              (U_hat ⟨s.val, by omega⟩ k)|) +
        fp.u *
          ∑ s : Fin k.val,
            |L_hat i ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ k|) +
      fp.u * |flDoolittleLNumerator fp n A L_hat U_hat i k| := by
  let target :=
    A i k -
      ∑ s : Fin n,
        (if s.val < k.val then L_hat i s * U_hat s k else 0)
  let num := flDoolittleLNumerator fp n A L_hat U_hat i k
  let lentry := flDoolittleLEntry fp n A L_hat U_hat i k
  have hnum :
      |target - num| ≤
        gamma fp k.val *
          (|A i k| +
            ∑ s : Fin k.val,
              |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ k)|) +
          fp.u *
            ∑ s : Fin k.val,
              |L_hat i ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ k| := by
    simpa [target, num] using
      flDoolittleLNumerator_masked_exact_product_residual_abs_le
        fp n A L_hat U_hat i k hk
  have hdiv :
      |num - lentry * U_hat k k| ≤ fp.u * |num| := by
    simpa [num, lentry] using
      flDoolittleLEntry_mul_pivot_sub_numerator_abs_le
        fp n A L_hat U_hat i k hU
  have htri :
      |target - L_hat i k * U_hat k k| ≤
        |target - num| + |num - lentry * U_hat k k| := by
    have hdecomp :
        target - L_hat i k * U_hat k k =
          (target - num) + (num - lentry * U_hat k k) := by
      simp [lentry, hentry]
    rw [hdecomp]
    exact abs_add_le _ _
  calc
    |(A i k -
      ∑ s : Fin n,
        (if s.val < k.val then L_hat i s * U_hat s k else 0)) -
        L_hat i k * U_hat k k|
        = |target - L_hat i k * U_hat k k| := by
            rfl
    _ ≤ |target - num| + |num - lentry * U_hat k k| := htri
    _ ≤ (gamma fp k.val *
          (|A i k| +
            ∑ s : Fin k.val,
              |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ k)|) +
          fp.u *
            ∑ s : Fin k.val,
              |L_hat i ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ k|) +
        fp.u * |flDoolittleLNumerator fp n A L_hat U_hat i k| := by
          simpa [num] using add_le_add hnum hdiv

/-- Concrete upper-entry absolute budget supplied by the literal rounded
Doolittle fold analysis. -/
noncomputable def doolittleUAbsBudget (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (k j : Fin n) : ℝ :=
  gamma fp k.val *
    (|A k j| +
      ∑ s : Fin k.val,
        |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ j)|) +
    fp.u *
      ∑ s : Fin k.val,
        |L_hat k ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ j|

/-- Concrete lower-entry absolute budget supplied by the literal rounded
Doolittle fold, division, and computed-pivot analysis. -/
noncomputable def doolittleLAbsBudget (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  (gamma fp k.val *
    (|A i k| +
      ∑ s : Fin k.val,
        |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ k)|) +
    fp.u *
      ∑ s : Fin k.val,
        |L_hat i ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ k|) +
    fp.u * |flDoolittleLNumerator fp n A L_hat U_hat i k|

/-- Absolute work term multiplying `gamma fp k` in the upper literal
Doolittle budget. -/
noncomputable def doolittleUWorkAbs (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (k j : Fin n) : ℝ :=
  |A k j| +
    ∑ s : Fin k.val,
      |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
        (U_hat ⟨s.val, by omega⟩ j)|

/-- Absolute exact-product term multiplying `fp.u` in the upper literal
Doolittle budget. -/
noncomputable def doolittleUProductAbs (_fp : FPModel) (n : ℕ)
    (_A L_hat U_hat : Fin n → Fin n → ℝ) (k j : Fin n) : ℝ :=
  ∑ s : Fin k.val,
    |L_hat k ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ j|

/-- Absolute work term multiplying `gamma fp k` in the lower literal
Doolittle budget. -/
noncomputable def doolittleLWorkAbs (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  |A i k| +
    ∑ s : Fin k.val,
      |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
        (U_hat ⟨s.val, by omega⟩ k)|

/-- Absolute exact-product term multiplying `fp.u` in the lower literal
Doolittle budget. -/
noncomputable def doolittleLProductAbs (_fp : FPModel) (n : ℕ)
    (_A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  ∑ s : Fin k.val,
    |L_hat i ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ k|

/-- Absolute lower numerator term multiplying `fp.u` in the lower literal
Doolittle budget. -/
noncomputable def doolittleLNumeratorAbs (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  |flDoolittleLNumerator fp n A L_hat U_hat i k|

/-- Exact upper-entry target before floating-point subtraction in the literal
Doolittle row fold. -/
noncomputable def doolittleUExactTarget (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (k j : Fin n) : ℝ :=
  A k j -
    ∑ s : Fin k.val,
      L_hat k ⟨s.val, by omega⟩ *
        U_hat ⟨s.val, by omega⟩ j

/-- Exact lower numerator target before floating-point subtraction and division
in the literal Doolittle column fold. -/
noncomputable def doolittleLExactTarget (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  A i k -
    ∑ s : Fin k.val,
      L_hat i ⟨s.val, by omega⟩ *
        U_hat ⟨s.val, by omega⟩ k

/-- Explicit exact-product residual budget for the upper exact target after the
literal rounded Doolittle row fold has computed the stored upper entry. -/
noncomputable def doolittleUExactTargetResidualBudget (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (k j : Fin n) : ℝ :=
  gamma fp k.val *
      (|A k j| + (1 + fp.u) *
        doolittleUProductAbs fp n A L_hat U_hat k j) +
    fp.u * doolittleUProductAbs fp n A L_hat U_hat k j

/-- Explicit exact-product residual budget for the lower exact target after the
literal rounded Doolittle numerator fold. -/
noncomputable def doolittleLExactTargetNumeratorResidualBudget
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  gamma fp k.val *
      (|A i k| + (1 + fp.u) *
        doolittleLProductAbs fp n A L_hat U_hat i k) +
    fp.u * doolittleLProductAbs fp n A L_hat U_hat i k

/-- Explicit exact-product residual budget for the lower exact target after the
literal rounded numerator is divided by the computed pivot and multiplied back
by that pivot. -/
noncomputable def doolittleLExactTargetEntryResidualBudget
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  doolittleLExactTargetNumeratorResidualBudget fp n A L_hat U_hat i k +
    fp.u * |flDoolittleLNumerator fp n A L_hat U_hat i k|

/-- Rounded products in the literal upper Doolittle fold are dominated by the
exact-product sum with the primitive `(1+u_fp)` factor. -/
theorem doolittleURoundedProductAbsSum_le_one_add_u_productAbs {n : ℕ}
    (fp : FPModel) (A L_hat U_hat : Fin n → Fin n → ℝ)
    (k j : Fin n) :
    (∑ s : Fin k.val,
      |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
        (U_hat ⟨s.val, by omega⟩ j)|) ≤
      (1 + fp.u) *
        doolittleUProductAbs fp n A L_hat U_hat k j := by
  calc
    (∑ s : Fin k.val,
      |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
        (U_hat ⟨s.val, by omega⟩ j)|)
        ≤ ∑ s : Fin k.val,
            (1 + fp.u) *
              |L_hat k ⟨s.val, by omega⟩ *
                U_hat ⟨s.val, by omega⟩ j| := by
          exact Finset.sum_le_sum (fun s _ =>
            fl_mul_abs_le_one_add_u_mul_abs_mul fp
              (L_hat k ⟨s.val, by omega⟩)
              (U_hat ⟨s.val, by omega⟩ j))
    _ = (1 + fp.u) *
          ∑ s : Fin k.val,
            |L_hat k ⟨s.val, by omega⟩ *
              U_hat ⟨s.val, by omega⟩ j| := by
          symm
          rw [Finset.mul_sum]
    _ = (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j := by
          simp [doolittleUProductAbs]

/-- Rounded products in the literal lower Doolittle numerator fold are
dominated by the exact-product sum with the primitive `(1+u_fp)` factor. -/
theorem doolittleLRoundedProductAbsSum_le_one_add_u_productAbs {n : ℕ}
    (fp : FPModel) (A L_hat U_hat : Fin n → Fin n → ℝ)
    (i k : Fin n) :
    (∑ s : Fin k.val,
      |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
        (U_hat ⟨s.val, by omega⟩ k)|) ≤
      (1 + fp.u) *
        doolittleLProductAbs fp n A L_hat U_hat i k := by
  calc
    (∑ s : Fin k.val,
      |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
        (U_hat ⟨s.val, by omega⟩ k)|)
        ≤ ∑ s : Fin k.val,
            (1 + fp.u) *
              |L_hat i ⟨s.val, by omega⟩ *
                U_hat ⟨s.val, by omega⟩ k| := by
          exact Finset.sum_le_sum (fun s _ =>
            fl_mul_abs_le_one_add_u_mul_abs_mul fp
              (L_hat i ⟨s.val, by omega⟩)
              (U_hat ⟨s.val, by omega⟩ k))
    _ = (1 + fp.u) *
          ∑ s : Fin k.val,
            |L_hat i ⟨s.val, by omega⟩ *
              U_hat ⟨s.val, by omega⟩ k| := by
          symm
          rw [Finset.mul_sum]
    _ = (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k := by
          simp [doolittleLProductAbs]

/-- Literal rounded upper Doolittle arithmetic is within the explicit
exact-target residual budget. -/
theorem doolittleUExactTarget_residual_abs_le_of_literal {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {k j : Fin n} (hk : gammaValid fp k.val)
    (hentry : U_hat k j = flDoolittleUEntry fp n A L_hat U_hat k j) :
    |doolittleUExactTarget n A L_hat U_hat k j - U_hat k j| ≤
      doolittleUExactTargetResidualBudget fp n A L_hat U_hat k j := by
  have hraw :
      |doolittleUExactTarget n A L_hat U_hat k j -
          flDoolittleUEntry fp n A L_hat U_hat k j| ≤
        gamma fp k.val *
          (|A k j| +
            ∑ s : Fin k.val,
              |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ j)|) +
          fp.u * doolittleUProductAbs fp n A L_hat U_hat k j := by
    simpa [doolittleUExactTarget, doolittleUProductAbs] using
      flDoolittleUEntry_exact_product_residual_abs_le
        fp n A L_hat U_hat k j hk
  have hround :=
    doolittleURoundedProductAbsSum_le_one_add_u_productAbs
      fp A L_hat U_hat k j
  have hwork :
      |A k j| +
          ∑ s : Fin k.val,
            |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
              (U_hat ⟨s.val, by omega⟩ j)| ≤
        |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j :=
    add_le_add le_rfl hround
  have hg : 0 ≤ gamma fp k.val := gamma_nonneg fp hk
  have hbudget :
      gamma fp k.val *
          (|A k j| +
            ∑ s : Fin k.val,
              |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ j)|) +
          fp.u * doolittleUProductAbs fp n A L_hat U_hat k j ≤
        doolittleUExactTargetResidualBudget fp n A L_hat U_hat k j := by
    exact add_le_add (mul_le_mul_of_nonneg_left hwork hg) le_rfl
  simpa [hentry] using le_trans hraw hbudget

/-- Literal rounded lower Doolittle arithmetic is within the explicit
exact-target numerator residual budget before division by the computed pivot. -/
theorem doolittleLExactTarget_numerator_residual_abs_le_of_literal {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n} (hk : gammaValid fp k.val) :
    |doolittleLExactTarget n A L_hat U_hat i k -
        flDoolittleLNumerator fp n A L_hat U_hat i k| ≤
      doolittleLExactTargetNumeratorResidualBudget fp n A L_hat U_hat i k := by
  have hraw :
      |doolittleLExactTarget n A L_hat U_hat i k -
          flDoolittleLNumerator fp n A L_hat U_hat i k| ≤
        gamma fp k.val *
          (|A i k| +
            ∑ s : Fin k.val,
              |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ k)|) +
          fp.u * doolittleLProductAbs fp n A L_hat U_hat i k := by
    simpa [doolittleLExactTarget, doolittleLProductAbs] using
      flDoolittleLNumerator_exact_product_residual_abs_le
        fp n A L_hat U_hat i k hk
  have hround :=
    doolittleLRoundedProductAbsSum_le_one_add_u_productAbs
      fp A L_hat U_hat i k
  have hwork :
      |A i k| +
          ∑ s : Fin k.val,
            |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
              (U_hat ⟨s.val, by omega⟩ k)| ≤
        |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k :=
    add_le_add le_rfl hround
  have hg : 0 ≤ gamma fp k.val := gamma_nonneg fp hk
  have hbudget :
      gamma fp k.val *
          (|A i k| +
            ∑ s : Fin k.val,
              |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ k)|) +
          fp.u * doolittleLProductAbs fp n A L_hat U_hat i k ≤
        doolittleLExactTargetNumeratorResidualBudget
          fp n A L_hat U_hat i k := by
    exact add_le_add (mul_le_mul_of_nonneg_left hwork hg) le_rfl
  exact le_trans hraw hbudget

/-- Literal rounded lower Doolittle arithmetic is within the explicit
exact-target entry residual budget after division by the computed pivot and
multiplication back by that pivot. -/
theorem doolittleLExactTarget_entry_residual_abs_le_of_literal {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n} (hk : gammaValid fp k.val)
    (hU : U_hat k k ≠ 0)
    (hentry : L_hat i k = flDoolittleLEntry fp n A L_hat U_hat i k) :
    |doolittleLExactTarget n A L_hat U_hat i k -
        L_hat i k * U_hat k k| ≤
      doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k := by
  let target := doolittleLExactTarget n A L_hat U_hat i k
  let num := flDoolittleLNumerator fp n A L_hat U_hat i k
  let lentry := flDoolittleLEntry fp n A L_hat U_hat i k
  have hnum :
      |target - num| ≤
        doolittleLExactTargetNumeratorResidualBudget
          fp n A L_hat U_hat i k := by
    simpa [target, num] using
      doolittleLExactTarget_numerator_residual_abs_le_of_literal
        (n := n) (fp := fp) (A := A) (L_hat := L_hat)
        (U_hat := U_hat) (i := i) (k := k) hk
  have hdiv :
      |num - lentry * U_hat k k| ≤ fp.u * |num| := by
    simpa [num, lentry] using
      flDoolittleLEntry_mul_pivot_sub_numerator_abs_le
        fp n A L_hat U_hat i k hU
  have htri :
      |target - lentry * U_hat k k| ≤
        |target - num| + |num - lentry * U_hat k k| := by
    have hdecomp :
        target - lentry * U_hat k k =
          (target - num) + (num - lentry * U_hat k k) := by
      ring
    rw [hdecomp]
    exact abs_add_le _ _
  have hsum :
      |target - lentry * U_hat k k| ≤
        doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k := by
    calc
      |target - lentry * U_hat k k|
          ≤ |target - num| + |num - lentry * U_hat k k| := htri
      _ ≤ doolittleLExactTargetNumeratorResidualBudget
            fp n A L_hat U_hat i k + fp.u * |num| :=
          add_le_add hnum hdiv
      _ = doolittleLExactTargetEntryResidualBudget
            fp n A L_hat U_hat i k := by
          simp [doolittleLExactTargetEntryResidualBudget, num]
  simpa [target, lentry, hentry] using hsum

private lemma le_abs_rounded_of_gap
    {exact rounded lhs eta : ℝ}
    (hgap : lhs + eta ≤ |exact|)
    (hres : |exact - rounded| ≤ eta) :
    lhs ≤ |rounded| := by
  have htri : |exact| ≤ |rounded| + eta := by
    calc
      |exact| = |rounded + (exact - rounded)| := by
          congr 1
          ring
      _ ≤ |rounded| + |exact - rounded| := abs_add_le _ _
      _ ≤ |rounded| + eta := add_le_add le_rfl hres
  linarith

/-- A source-facing exact-target gap for an upper entry yields the
exact-product no-cancellation margin against the stored upper entry. -/
theorem doolittleUExactProductMargin_of_exactTarget_gap {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {k j : Fin n} (hk : gammaValid fp k.val)
    (hentry : U_hat k j = flDoolittleUEntry fp n A L_hat U_hat k j)
    (hgap :
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j +
        doolittleUExactTargetResidualBudget fp n A L_hat U_hat k j ≤
        |doolittleUExactTarget n A L_hat U_hat k j|) :
    |A k j| + (1 + fp.u) *
        doolittleUProductAbs fp n A L_hat U_hat k j ≤ |U_hat k j| := by
  exact le_abs_rounded_of_gap hgap
    (doolittleUExactTarget_residual_abs_le_of_literal hk hentry)

/-- A source-facing exact-target gap for a lower entry yields the
exact-product no-cancellation margin against the stored lower pivot product. -/
theorem doolittleLExactProductMargin_of_exactTarget_gap {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n} (hk : gammaValid fp k.val)
    (hU : U_hat k k ≠ 0)
    (hentry : L_hat i k = flDoolittleLEntry fp n A L_hat U_hat i k)
    (hgap :
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k +
        doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|) :
    |A i k| + (1 + fp.u) *
        doolittleLProductAbs fp n A L_hat U_hat i k ≤
      |L_hat i k * U_hat k k| := by
  exact le_abs_rounded_of_gap hgap
    (doolittleLExactTarget_entry_residual_abs_le_of_literal hk hU hentry)

/-- A stronger source-facing exact-target gap yields the lower exact-product
numerator margin needed to dominate the rounded numerator itself. -/
theorem doolittleLExactProductNumeratorMargin_of_exactTarget_gap {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n} (hk : gammaValid fp k.val)
    (hU : U_hat k k ≠ 0)
    (hentry : L_hat i k = flDoolittleLEntry fp n A L_hat U_hat i k)
    (hgap :
      ((|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
        doolittleLExactTargetNumeratorResidualBudget
          fp n A L_hat U_hat i k) +
        doolittleLExactTargetEntryResidualBudget
          fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|) :
    (|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
      doolittleLExactTargetNumeratorResidualBudget
        fp n A L_hat U_hat i k ≤
      |L_hat i k * U_hat k k| := by
  exact le_abs_rounded_of_gap hgap
    (doolittleLExactTarget_entry_residual_abs_le_of_literal hk hU hentry)

/-- The exact upper Doolittle target cannot exceed the source entry plus the
absolute exact-product sum.  This triangle audit is useful for detecting when
an exact-target gap hypothesis is too strong to be supplied by an ordinary
no-cancellation argument. -/
theorem doolittleUExactTarget_abs_le_source_plus_productAbs {n : ℕ}
    (fp : FPModel) (A L_hat U_hat : Fin n → Fin n → ℝ)
    (k j : Fin n) :
    |doolittleUExactTarget n A L_hat U_hat k j| ≤
      |A k j| + doolittleUProductAbs fp n A L_hat U_hat k j := by
  have hsum :
      |∑ s : Fin k.val,
          L_hat k ⟨s.val, by omega⟩ *
            U_hat ⟨s.val, by omega⟩ j| ≤
        ∑ s : Fin k.val,
          |L_hat k ⟨s.val, by omega⟩ *
            U_hat ⟨s.val, by omega⟩ j| :=
    Finset.abs_sum_le_sum_abs _ _
  calc
    |doolittleUExactTarget n A L_hat U_hat k j|
        = |A k j -
            ∑ s : Fin k.val,
              L_hat k ⟨s.val, by omega⟩ *
                U_hat ⟨s.val, by omega⟩ j| := by
            simp [doolittleUExactTarget]
    _ ≤ |A k j| +
          |∑ s : Fin k.val,
            L_hat k ⟨s.val, by omega⟩ *
              U_hat ⟨s.val, by omega⟩ j| :=
        by
          simpa using
            (abs_sub_le (A k j) 0
              (∑ s : Fin k.val,
                L_hat k ⟨s.val, by omega⟩ *
                  U_hat ⟨s.val, by omega⟩ j))
    _ ≤ |A k j| +
          ∑ s : Fin k.val,
            |L_hat k ⟨s.val, by omega⟩ *
              U_hat ⟨s.val, by omega⟩ j| :=
        add_le_add le_rfl hsum
    _ = |A k j| + doolittleUProductAbs fp n A L_hat U_hat k j := by
        simp [doolittleUProductAbs]

/-- The exact lower Doolittle target cannot exceed the source entry plus the
absolute exact-product sum. -/
theorem doolittleLExactTarget_abs_le_source_plus_productAbs {n : ℕ}
    (fp : FPModel) (A L_hat U_hat : Fin n → Fin n → ℝ)
    (i k : Fin n) :
    |doolittleLExactTarget n A L_hat U_hat i k| ≤
      |A i k| + doolittleLProductAbs fp n A L_hat U_hat i k := by
  have hsum :
      |∑ s : Fin k.val,
          L_hat i ⟨s.val, by omega⟩ *
            U_hat ⟨s.val, by omega⟩ k| ≤
        ∑ s : Fin k.val,
          |L_hat i ⟨s.val, by omega⟩ *
            U_hat ⟨s.val, by omega⟩ k| :=
    Finset.abs_sum_le_sum_abs _ _
  calc
    |doolittleLExactTarget n A L_hat U_hat i k|
        = |A i k -
            ∑ s : Fin k.val,
              L_hat i ⟨s.val, by omega⟩ *
                U_hat ⟨s.val, by omega⟩ k| := by
            simp [doolittleLExactTarget]
    _ ≤ |A i k| +
          |∑ s : Fin k.val,
            L_hat i ⟨s.val, by omega⟩ *
              U_hat ⟨s.val, by omega⟩ k| :=
        by
          simpa using
            (abs_sub_le (A i k) 0
              (∑ s : Fin k.val,
                L_hat i ⟨s.val, by omega⟩ *
                  U_hat ⟨s.val, by omega⟩ k))
    _ ≤ |A i k| +
          ∑ s : Fin k.val,
            |L_hat i ⟨s.val, by omega⟩ *
              U_hat ⟨s.val, by omega⟩ k| :=
        add_le_add le_rfl hsum
    _ = |A i k| + doolittleLProductAbs fp n A L_hat U_hat i k := by
        simp [doolittleLProductAbs]

/-- If the upper exact-target gap used by
`doolittleUExactProductMargin_of_exactTarget_gap` holds, then its extra
roundoff/residual excess must be nonpositive.  Thus any genuinely positive
excess rules out that gap route. -/
theorem doolittleUExactTarget_gap_excess_nonpos {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {k j : Fin n}
    (hgap :
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j +
        doolittleUExactTargetResidualBudget fp n A L_hat U_hat k j ≤
        |doolittleUExactTarget n A L_hat U_hat k j|) :
    fp.u * doolittleUProductAbs fp n A L_hat U_hat k j +
      doolittleUExactTargetResidualBudget fp n A L_hat U_hat k j ≤ 0 := by
  have htri :=
    doolittleUExactTarget_abs_le_source_plus_productAbs
      fp A L_hat U_hat k j
  have hchain :
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j +
        doolittleUExactTargetResidualBudget fp n A L_hat U_hat k j ≤
      |A k j| + doolittleUProductAbs fp n A L_hat U_hat k j :=
    le_trans hgap htri
  linarith

/-- A positive upper exact-target excess contradicts the LR.1bp exact-target
gap. -/
theorem doolittleUExactTarget_gap_false_of_positive_excess {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {k j : Fin n}
    (hpos :
      0 < fp.u * doolittleUProductAbs fp n A L_hat U_hat k j +
        doolittleUExactTargetResidualBudget fp n A L_hat U_hat k j)
    (hgap :
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j +
        doolittleUExactTargetResidualBudget fp n A L_hat U_hat k j ≤
        |doolittleUExactTarget n A L_hat U_hat k j|) :
    False := by
  have hnonpos :=
    doolittleUExactTarget_gap_excess_nonpos
      (n := n) (fp := fp) (A := A) (L_hat := L_hat)
      (U_hat := U_hat) (k := k) (j := j) hgap
  linarith

/-- If the lower exact-target entry gap used by
`doolittleLExactProductMargin_of_exactTarget_gap` holds, then its extra
roundoff/residual excess must be nonpositive. -/
theorem doolittleLExactTarget_gap_excess_nonpos {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n}
    (hgap :
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k +
        doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|) :
    fp.u * doolittleLProductAbs fp n A L_hat U_hat i k +
      doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k ≤ 0 := by
  have htri :=
    doolittleLExactTarget_abs_le_source_plus_productAbs
      fp A L_hat U_hat i k
  have hchain :
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k +
        doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k ≤
      |A i k| + doolittleLProductAbs fp n A L_hat U_hat i k :=
    le_trans hgap htri
  linarith

/-- A positive lower exact-target entry excess contradicts the LR.1bp
exact-target gap. -/
theorem doolittleLExactTarget_gap_false_of_positive_excess {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n}
    (hpos :
      0 < fp.u * doolittleLProductAbs fp n A L_hat U_hat i k +
        doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k)
    (hgap :
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k +
        doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|) :
    False := by
  have hnonpos :=
    doolittleLExactTarget_gap_excess_nonpos
      (n := n) (fp := fp) (A := A) (L_hat := L_hat)
      (U_hat := U_hat) (i := i) (k := k) hgap
  linarith

/-- The stronger lower numerator exact-target gap likewise forces its
roundoff/residual excess to be nonpositive. -/
theorem doolittleLExactTarget_numerator_gap_excess_nonpos {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n}
    (hgap :
      ((|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
        doolittleLExactTargetNumeratorResidualBudget
          fp n A L_hat U_hat i k) +
        doolittleLExactTargetEntryResidualBudget
          fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|) :
    doolittleLExactTargetNumeratorResidualBudget fp n A L_hat U_hat i k +
      doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k ≤ 0 := by
  have htri :=
    doolittleLExactTarget_abs_le_source_plus_productAbs
      fp A L_hat U_hat i k
  have hchain :
      ((|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
        doolittleLExactTargetNumeratorResidualBudget
          fp n A L_hat U_hat i k) +
        doolittleLExactTargetEntryResidualBudget
          fp n A L_hat U_hat i k ≤
      |A i k| + doolittleLProductAbs fp n A L_hat U_hat i k :=
    le_trans hgap htri
  linarith

/-- A positive lower numerator exact-target excess contradicts the stronger
LR.1bp numerator gap. -/
theorem doolittleLExactTarget_numerator_gap_false_of_positive_excess {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n}
    (hpos :
      0 < doolittleLExactTargetNumeratorResidualBudget fp n A L_hat U_hat i k +
        doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k)
    (hgap :
      ((|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
        doolittleLExactTargetNumeratorResidualBudget
          fp n A L_hat U_hat i k) +
        doolittleLExactTargetEntryResidualBudget
          fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|) :
    False := by
  have hnonpos :=
    doolittleLExactTarget_numerator_gap_excess_nonpos
      (n := n) (fp := fp) (A := A) (L_hat := L_hat)
      (U_hat := U_hat) (i := i) (k := k) hgap
  linarith

/-- An exact-product no-cancellation margin for an upper entry dominates the
rounded-product work term used by the literal Doolittle budget. -/
theorem doolittleUWorkAbs_le_of_exact_product_margin {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {k j : Fin n}
    (hmargin :
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j ≤ |U_hat k j|) :
    doolittleUWorkAbs fp n A L_hat U_hat k j ≤ |U_hat k j| := by
  have hsum :
      (∑ s : Fin k.val,
        |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ j)|) ≤
        (1 + fp.u) *
          ∑ s : Fin k.val,
            |L_hat k ⟨s.val, by omega⟩ *
              U_hat ⟨s.val, by omega⟩ j| := by
    calc
      (∑ s : Fin k.val,
        |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ j)|)
          ≤ ∑ s : Fin k.val,
              (1 + fp.u) *
                |L_hat k ⟨s.val, by omega⟩ *
                  U_hat ⟨s.val, by omega⟩ j| := by
            exact Finset.sum_le_sum (fun s _ =>
              fl_mul_abs_le_one_add_u_mul_abs_mul fp
                (L_hat k ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ j))
      _ = (1 + fp.u) *
            ∑ s : Fin k.val,
              |L_hat k ⟨s.val, by omega⟩ *
                U_hat ⟨s.val, by omega⟩ j| := by
            symm
            rw [Finset.mul_sum]
  calc
    doolittleUWorkAbs fp n A L_hat U_hat k j
        = |A k j| +
            ∑ s : Fin k.val,
              |fp.fl_mul (L_hat k ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ j)| := by
            simp [doolittleUWorkAbs]
    _ ≤ |A k j| + (1 + fp.u) *
          ∑ s : Fin k.val,
            |L_hat k ⟨s.val, by omega⟩ *
              U_hat ⟨s.val, by omega⟩ j| :=
        add_le_add le_rfl hsum
    _ = |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j := by
        simp [doolittleUProductAbs]
    _ ≤ |U_hat k j| := hmargin

/-- The same exact-product no-cancellation margin also dominates the upper
exact-product term itself. -/
theorem doolittleUProductAbs_le_of_exact_product_margin {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {k j : Fin n}
    (hmargin :
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j ≤ |U_hat k j|) :
    doolittleUProductAbs fp n A L_hat U_hat k j ≤ |U_hat k j| := by
  have hprod_nonneg :
      0 ≤ doolittleUProductAbs fp n A L_hat U_hat k j := by
    unfold doolittleUProductAbs
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hcoef : 1 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have hprod_scaled :
      doolittleUProductAbs fp n A L_hat U_hat k j ≤
        (1 + fp.u) * doolittleUProductAbs fp n A L_hat U_hat k j := by
    calc
      doolittleUProductAbs fp n A L_hat U_hat k j
          = 1 * doolittleUProductAbs fp n A L_hat U_hat k j := by ring
      _ ≤ (1 + fp.u) * doolittleUProductAbs fp n A L_hat U_hat k j :=
          mul_le_mul_of_nonneg_right hcoef hprod_nonneg
  have hscaled_le :
      (1 + fp.u) * doolittleUProductAbs fp n A L_hat U_hat k j ≤
        |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j :=
    le_add_of_nonneg_left (abs_nonneg _)
  exact le_trans hprod_scaled (le_trans hscaled_le hmargin)

/-- An exact-product no-cancellation margin for a lower entry dominates the
rounded-product work term used by the literal Doolittle budget. -/
theorem doolittleLWorkAbs_le_of_exact_product_margin {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n}
    (hmargin :
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|) :
    doolittleLWorkAbs fp n A L_hat U_hat i k ≤
      |L_hat i k * U_hat k k| := by
  have hsum :
      (∑ s : Fin k.val,
        |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ k)|) ≤
        (1 + fp.u) *
          ∑ s : Fin k.val,
            |L_hat i ⟨s.val, by omega⟩ *
              U_hat ⟨s.val, by omega⟩ k| := by
    calc
      (∑ s : Fin k.val,
        |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
          (U_hat ⟨s.val, by omega⟩ k)|)
          ≤ ∑ s : Fin k.val,
              (1 + fp.u) *
                |L_hat i ⟨s.val, by omega⟩ *
                  U_hat ⟨s.val, by omega⟩ k| := by
            exact Finset.sum_le_sum (fun s _ =>
              fl_mul_abs_le_one_add_u_mul_abs_mul fp
                (L_hat i ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ k))
      _ = (1 + fp.u) *
            ∑ s : Fin k.val,
              |L_hat i ⟨s.val, by omega⟩ *
                U_hat ⟨s.val, by omega⟩ k| := by
            symm
            rw [Finset.mul_sum]
  calc
    doolittleLWorkAbs fp n A L_hat U_hat i k
        = |A i k| +
            ∑ s : Fin k.val,
              |fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
                (U_hat ⟨s.val, by omega⟩ k)| := by
            simp [doolittleLWorkAbs]
    _ ≤ |A i k| + (1 + fp.u) *
          ∑ s : Fin k.val,
            |L_hat i ⟨s.val, by omega⟩ *
              U_hat ⟨s.val, by omega⟩ k| :=
        add_le_add le_rfl hsum
    _ = |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k := by
        simp [doolittleLProductAbs]
    _ ≤ |L_hat i k * U_hat k k| := hmargin

/-- The same exact-product no-cancellation margin also dominates the lower
exact-product term itself. -/
theorem doolittleLProductAbs_le_of_exact_product_margin {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n}
    (hmargin :
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|) :
    doolittleLProductAbs fp n A L_hat U_hat i k ≤
      |L_hat i k * U_hat k k| := by
  have hprod_nonneg :
      0 ≤ doolittleLProductAbs fp n A L_hat U_hat i k := by
    unfold doolittleLProductAbs
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hcoef : 1 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have hprod_scaled :
      doolittleLProductAbs fp n A L_hat U_hat i k ≤
        (1 + fp.u) * doolittleLProductAbs fp n A L_hat U_hat i k := by
    calc
      doolittleLProductAbs fp n A L_hat U_hat i k
          = 1 * doolittleLProductAbs fp n A L_hat U_hat i k := by ring
      _ ≤ (1 + fp.u) * doolittleLProductAbs fp n A L_hat U_hat i k :=
          mul_le_mul_of_nonneg_right hcoef hprod_nonneg
  have hscaled_le :
      (1 + fp.u) * doolittleLProductAbs fp n A L_hat U_hat i k ≤
        |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k :=
    le_add_of_nonneg_left (abs_nonneg _)
  exact le_trans hprod_scaled (le_trans hscaled_le hmargin)

/-- A stronger lower exact-product numerator margin dominates the rounded
lower numerator itself.  This is the remaining component in the lower
no-cancellation route: the proof pays the exact-product subtraction-fold radius
and the `(1+u_fp)` rounded-product growth bound. -/
theorem doolittleLNumeratorAbs_le_of_exact_product_numerator_margin {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n} (hk : gammaValid fp k.val)
    (hmargin :
      (|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
        (gamma fp k.val *
            (|A i k| + (1 + fp.u) *
              doolittleLProductAbs fp n A L_hat U_hat i k) +
          fp.u * doolittleLProductAbs fp n A L_hat U_hat i k) ≤
        |L_hat i k * U_hat k k|) :
    doolittleLNumeratorAbs fp n A L_hat U_hat i k ≤
      |L_hat i k * U_hat k k| := by
  let exact : Fin k.val → ℝ := fun s =>
    L_hat i ⟨s.val, by omega⟩ * U_hat ⟨s.val, by omega⟩ k
  let rounded : Fin k.val → ℝ := fun s =>
    fp.fl_mul (L_hat i ⟨s.val, by omega⟩)
      (U_hat ⟨s.val, by omega⟩ k)
  let target : ℝ := A i k - ∑ s : Fin k.val, exact s
  let num : ℝ := flDoolittleLNumerator fp n A L_hat U_hat i k
  have hround :
      (∑ s : Fin k.val, |rounded s|) ≤
        (1 + fp.u) * doolittleLProductAbs fp n A L_hat U_hat i k := by
    calc
      (∑ s : Fin k.val, |rounded s|)
          ≤ ∑ s : Fin k.val, (1 + fp.u) * |exact s| := by
            exact Finset.sum_le_sum (fun s _ => by
              simpa [rounded, exact] using
                fl_mul_abs_le_one_add_u_mul_abs_mul fp
                  (L_hat i ⟨s.val, by omega⟩)
                  (U_hat ⟨s.val, by omega⟩ k))
      _ = (1 + fp.u) * ∑ s : Fin k.val, |exact s| := by
            symm
            rw [Finset.mul_sum]
      _ = (1 + fp.u) *
            doolittleLProductAbs fp n A L_hat U_hat i k := by
            simp [doolittleLProductAbs, exact]
  have htarget :
      |target| ≤ |A i k| + doolittleLProductAbs fp n A L_hat U_hat i k := by
    calc
      |target| = |A i k - ∑ s : Fin k.val, exact s| := by rfl
      _ ≤ |A i k - 0| + |0 - ∑ s : Fin k.val, exact s| :=
          abs_sub_le (A i k) 0 (∑ s : Fin k.val, exact s)
      _ = |A i k| + |∑ s : Fin k.val, exact s| := by simp
      _ ≤ |A i k| + ∑ s : Fin k.val, |exact s| :=
          add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
      _ = |A i k| + doolittleLProductAbs fp n A L_hat U_hat i k := by
          simp [doolittleLProductAbs, exact]
  have hres0 :
      |target - num| ≤
        gamma fp k.val * (|A i k| + ∑ s : Fin k.val, |rounded s|) +
          fp.u * doolittleLProductAbs fp n A L_hat U_hat i k := by
    simpa [target, num, exact, rounded, doolittleLProductAbs] using
      flDoolittleLNumerator_exact_product_residual_abs_le
        fp n A L_hat U_hat i k hk
  have hwork :
      |A i k| + ∑ s : Fin k.val, |rounded s| ≤
        |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k :=
    add_le_add le_rfl hround
  have hg : 0 ≤ gamma fp k.val := gamma_nonneg fp hk
  have hres :
      |target - num| ≤
        gamma fp k.val *
            (|A i k| + (1 + fp.u) *
              doolittleLProductAbs fp n A L_hat U_hat i k) +
          fp.u * doolittleLProductAbs fp n A L_hat U_hat i k :=
    le_trans hres0
      (add_le_add (mul_le_mul_of_nonneg_left hwork hg) le_rfl)
  have htri :
      |target - (target - num)| ≤ |target| + |target - num| := by
    calc
      |target - (target - num)|
          ≤ |target - 0| + |0 - (target - num)| :=
          abs_sub_le target 0 (target - num)
      _ = |target| + |target - num| := by
          have hzero : 0 - (target - num) = num - target := by ring
          rw [sub_zero, hzero, abs_sub_comm num target]
  have hnum_abs :
      |num| ≤
        (|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
          (gamma fp k.val *
              (|A i k| + (1 + fp.u) *
                doolittleLProductAbs fp n A L_hat U_hat i k) +
            fp.u * doolittleLProductAbs fp n A L_hat U_hat i k) := by
    calc
      |num| = |target - (target - num)| := by
          congr 1
          ring
      _ ≤ |target| + |target - num| := htri
      _ ≤ (|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
            (gamma fp k.val *
                (|A i k| + (1 + fp.u) *
                  doolittleLProductAbs fp n A L_hat U_hat i k) +
              fp.u * doolittleLProductAbs fp n A L_hat U_hat i k) :=
          add_le_add htarget hres
  exact le_trans hnum_abs hmargin

/-- A componentwise no-cancellation regime for the two upper non-probability
work terms is sufficient to dominate the concrete upper Doolittle budget by
the relative compression radius. -/
theorem doolittleUAbsBudget_le_compression_of_component_dominance {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {k j : Fin n} (hn : gammaValid fp n) (_hkj : k.val ≤ j.val)
    (hwork :
      doolittleUWorkAbs fp n A L_hat U_hat k j ≤ |U_hat k j|)
    (hprod :
      doolittleUProductAbs fp n A L_hat U_hat k j ≤ |U_hat k j|) :
    doolittleUAbsBudget fp n A L_hat U_hat k j ≤
      gamma fp n * |U_hat k j| := by
  have hk1_le : k.val + 1 ≤ n := by
    omega
  have hk_valid : gammaValid fp k.val :=
    gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
  have hk1_valid : gammaValid fp (k.val + 1) :=
    gammaValid_mono fp hk1_le hn
  have hgk_nonneg : 0 ≤ gamma fp k.val := gamma_nonneg fp hk_valid
  have hscale_nonneg : 0 ≤ |U_hat k j| := abs_nonneg _
  have hwork' :
      gamma fp k.val * doolittleUWorkAbs fp n A L_hat U_hat k j ≤
        gamma fp k.val * |U_hat k j| :=
    mul_le_mul_of_nonneg_left hwork hgk_nonneg
  have hprod' :
      fp.u * doolittleUProductAbs fp n A L_hat U_hat k j ≤
        fp.u * |U_hat k j| :=
    mul_le_mul_of_nonneg_left hprod fp.u_nonneg
  have hbudget :
      doolittleUAbsBudget fp n A L_hat U_hat k j ≤
        (gamma fp k.val + fp.u) * |U_hat k j| := by
    calc
      doolittleUAbsBudget fp n A L_hat U_hat k j
          = gamma fp k.val *
              doolittleUWorkAbs fp n A L_hat U_hat k j +
            fp.u * doolittleUProductAbs fp n A L_hat U_hat k j := by
              simp [doolittleUAbsBudget, doolittleUWorkAbs,
                doolittleUProductAbs]
      _ ≤ gamma fp k.val * |U_hat k j| + fp.u * |U_hat k j| :=
            add_le_add hwork' hprod'
      _ = (gamma fp k.val + fp.u) * |U_hat k j| := by ring
  have hcoef :
      gamma fp k.val + fp.u ≤ gamma fp n :=
    le_trans (gamma_add_u_le fp k.val hk1_valid)
      (gamma_mono fp hk1_le hn)
  exact le_trans hbudget (mul_le_mul_of_nonneg_right hcoef hscale_nonneg)

/-- A componentwise no-cancellation regime for the three lower
non-probability work terms is sufficient to dominate the concrete lower
Doolittle budget by the relative compression radius after multiplication by
the computed pivot. -/
theorem doolittleLAbsBudget_le_compression_of_component_dominance {n : ℕ}
    {fp : FPModel} {A L_hat U_hat : Fin n → Fin n → ℝ}
    {i k : Fin n} (hn : gammaValid fp n) (hki : k.val < i.val)
    (hwork :
      doolittleLWorkAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hprod :
      doolittleLProductAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hnum :
      doolittleLNumeratorAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|) :
    doolittleLAbsBudget fp n A L_hat U_hat i k ≤
      gamma fp n * |L_hat i k * U_hat k k| := by
  have hk2_le : k.val + 2 ≤ n := by
    omega
  have hk_valid : gammaValid fp k.val :=
    gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
  have hk1_valid : gammaValid fp (k.val + 1) :=
    gammaValid_mono fp (by omega) hn
  have hk2_valid : gammaValid fp (k.val + 2) :=
    gammaValid_mono fp hk2_le hn
  have hgk_nonneg : 0 ≤ gamma fp k.val := gamma_nonneg fp hk_valid
  have hscale_nonneg : 0 ≤ |L_hat i k * U_hat k k| := abs_nonneg _
  have hwork' :
      gamma fp k.val * doolittleLWorkAbs fp n A L_hat U_hat i k ≤
        gamma fp k.val * |L_hat i k * U_hat k k| :=
    mul_le_mul_of_nonneg_left hwork hgk_nonneg
  have hprod' :
      fp.u * doolittleLProductAbs fp n A L_hat U_hat i k ≤
        fp.u * |L_hat i k * U_hat k k| :=
    mul_le_mul_of_nonneg_left hprod fp.u_nonneg
  have hnum' :
      fp.u * doolittleLNumeratorAbs fp n A L_hat U_hat i k ≤
        fp.u * |L_hat i k * U_hat k k| :=
    mul_le_mul_of_nonneg_left hnum fp.u_nonneg
  have hbudget :
      doolittleLAbsBudget fp n A L_hat U_hat i k ≤
        (gamma fp k.val + fp.u + fp.u) * |L_hat i k * U_hat k k| := by
    calc
      doolittleLAbsBudget fp n A L_hat U_hat i k
          = (gamma fp k.val *
              doolittleLWorkAbs fp n A L_hat U_hat i k +
            fp.u * doolittleLProductAbs fp n A L_hat U_hat i k) +
            fp.u * doolittleLNumeratorAbs fp n A L_hat U_hat i k := by
              simp [doolittleLAbsBudget, doolittleLWorkAbs,
                doolittleLProductAbs, doolittleLNumeratorAbs]
      _ ≤ (gamma fp k.val * |L_hat i k * U_hat k k| +
            fp.u * |L_hat i k * U_hat k k|) +
            fp.u * |L_hat i k * U_hat k k| :=
            add_le_add (add_le_add hwork' hprod') hnum'
      _ = (gamma fp k.val + fp.u + fp.u) * |L_hat i k * U_hat k k| := by
            ring
  have hcoef1 :
      gamma fp k.val + fp.u ≤ gamma fp (k.val + 1) :=
    gamma_add_u_le fp k.val hk1_valid
  have hcoef2 :
      gamma fp (k.val + 1) + fp.u ≤ gamma fp (k.val + 2) :=
    gamma_add_u_le fp (k.val + 1) hk2_valid
  have hcoef :
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n := by
    have hstep :
        gamma fp k.val + fp.u + fp.u ≤ gamma fp (k.val + 1) + fp.u :=
      by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right hcoef1 fp.u
    exact le_trans hstep
      (le_trans hcoef2 (gamma_mono fp hk2_le hn))
  exact le_trans hbudget (mul_le_mul_of_nonneg_right hcoef hscale_nonneg)

/-- Dense-Doolittle executable-loop certificate.

The first two recurrence fields record that the stored factors are produced by
the literal floating-point folds above.  The residual-compression fields are
the extra implementation-facing hypotheses needed to compress those literal
rounded folds into the compact `DoolittleLU` relative-error contract.  This
keeps the no-cancellation/pivot-quality obligation visible instead of silently
assuming that a fold-level absolute error is already relative to the stored
entry. -/
structure DoolittleDenseLoopCertificate (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (fp : FPModel) : Prop where
  /-- L̂ is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L_hat i i = 1
  /-- L̂ is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0
  /-- Û is upper triangular. -/
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0
  /-- Upper entries agree with the literal rounded Doolittle row fold. -/
  U_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
    U_hat k j = flDoolittleUEntry fp n A L_hat U_hat k j
  /-- Lower entries agree with the literal rounded Doolittle numerator fold
  followed by rounded division by the computed pivot. -/
  L_entry_eq : ∀ i k : Fin n, k.val < i.val →
    L_hat i k = flDoolittleLEntry fp n A L_hat U_hat i k
  /-- Visible compression budget for upper entries. -/
  U_residual_compression : ∀ k j : Fin n, k.val ≤ j.val →
    |(A k j -
      ∑ s : Fin n, (if s.val < k.val then L_hat k s * U_hat s j else 0)) -
        U_hat k j| ≤ gamma fp n * |U_hat k j|
  /-- Visible compression budget for lower entries after multiplication by the
  computed pivot. -/
  L_residual_compression : ∀ i k : Fin n, k.val < i.val →
    |(A i k -
      ∑ s : Fin n, (if s.val < k.val then L_hat i s * U_hat s k else 0)) -
        L_hat i k * U_hat k k| ≤ gamma fp n * |L_hat i k * U_hat k k|

/-- Dense-Doolittle absolute-budget certificate.

This is the next implementation-facing layer below
`DoolittleDenseLoopCertificate`: a routine may first prove ordinary absolute
residual budgets `BU` and `BL` for the literal rounded folds, then discharge
the noncancellation/pivot-quality work by proving those budgets are dominated
by the relative quantities required by `DoolittleDenseLoopCertificate`. -/
structure DoolittleDenseLoopAbsBudgetCertificate (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ) (fp : FPModel)
    (BU BL : Fin n → Fin n → ℝ) : Prop where
  /-- L̂ is unit lower triangular. -/
  L_diag : ∀ i : Fin n, L_hat i i = 1
  /-- L̂ is lower triangular. -/
  L_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0
  /-- Û is upper triangular. -/
  U_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0
  /-- Upper entries agree with the literal rounded Doolittle row fold. -/
  U_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
    U_hat k j = flDoolittleUEntry fp n A L_hat U_hat k j
  /-- Lower entries agree with the literal rounded Doolittle numerator fold
  followed by rounded division by the computed pivot. -/
  L_entry_eq : ∀ i k : Fin n, k.val < i.val →
    L_hat i k = flDoolittleLEntry fp n A L_hat U_hat i k
  /-- Absolute residual budget for upper entries. -/
  U_abs_residual : ∀ k j : Fin n, k.val ≤ j.val →
    |(A k j -
      ∑ s : Fin n, (if s.val < k.val then L_hat k s * U_hat s j else 0)) -
        U_hat k j| ≤ BU k j
  /-- Dominance turning the upper absolute budget into the relative
  compression budget. -/
  U_budget_le_compression : ∀ k j : Fin n, k.val ≤ j.val →
    BU k j ≤ gamma fp n * |U_hat k j|
  /-- Absolute residual budget for lower entries after multiplication by the
  computed pivot. -/
  L_abs_residual : ∀ i k : Fin n, k.val < i.val →
    |(A i k -
      ∑ s : Fin n, (if s.val < k.val then L_hat i s * U_hat s k else 0)) -
        L_hat i k * U_hat k k| ≤ BL i k
  /-- Dominance turning the lower absolute budget into the relative
  compression budget. -/
  L_budget_le_compression : ∀ i k : Fin n, k.val < i.val →
    BL i k ≤ gamma fp n * |L_hat i k * U_hat k k|

namespace DoolittleDenseLoopAbsBudgetCertificate

/-- Absolute residual budgets plus visible dominance inequalities produce the
relative residual-compression certificate consumed by the dense-loop
Doolittle-to-`DoolittleLU` handoff. -/
theorem to_denseLoopCertificate {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    {BU BL : Fin n → Fin n → ℝ}
    (hC : DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp BU BL) :
    DoolittleDenseLoopCertificate n A L_hat U_hat fp where
  L_diag := hC.L_diag
  L_upper_zero := hC.L_upper_zero
  U_lower_zero := hC.U_lower_zero
  U_entry_eq := hC.U_entry_eq
  L_entry_eq := hC.L_entry_eq
  U_residual_compression := by
    intro k j hkj
    exact le_trans (hC.U_abs_residual k j hkj)
      (hC.U_budget_le_compression k j hkj)
  L_residual_compression := by
    intro i k hki
    exact le_trans (hC.L_abs_residual i k hki)
      (hC.L_budget_le_compression i k hki)

/-- Literal Doolittle source budgets plus visible dominance inequalities
produce the absolute-budget certificate consumed by the dense-loop handoff. -/
theorem of_literal_doolittle_source_budgets {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      doolittleUAbsBudget fp n A L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLAbsBudget fp n A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp
      (doolittleUAbsBudget fp n A L_hat U_hat)
      (doolittleLAbsBudget fp n A L_hat U_hat) where
  L_diag := hL_diag
  L_upper_zero := hL_upper_zero
  U_lower_zero := hU_lower_zero
  U_entry_eq := hU_entry_eq
  L_entry_eq := hL_entry_eq
  U_abs_residual := by
    intro k j hkj
    have hk : gammaValid fp k.val :=
      gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
    rw [hU_entry_eq k j hkj]
    simpa [doolittleUAbsBudget] using
      flDoolittleUEntry_masked_exact_product_residual_abs_le
        fp n A L_hat U_hat k j hk
  U_budget_le_compression := hU_budget_le
  L_abs_residual := by
    intro i k hki
    have hk : gammaValid fp k.val :=
      gammaValid_mono fp (Nat.le_of_lt k.isLt) hn
    simpa [doolittleLAbsBudget] using
      flDoolittleLEntry_masked_exact_product_residual_abs_le
        fp n A L_hat U_hat i k hk (hU_diag k) (hL_entry_eq i k hki)
  L_budget_le_compression := hL_budget_le

/-- Componentwise work/product/numerator dominance is a concrete
no-cancellation route to the literal Doolittle absolute-budget certificate. -/
theorem of_literal_doolittle_component_dominance {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_work_le : ∀ k j : Fin n, k.val ≤ j.val →
      doolittleUWorkAbs fp n A L_hat U_hat k j ≤ |U_hat k j|)
    (hU_prod_le : ∀ k j : Fin n, k.val ≤ j.val →
      doolittleUProductAbs fp n A L_hat U_hat k j ≤ |U_hat k j|)
    (hL_work_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLWorkAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_prod_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLProductAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLNumeratorAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|) :
    DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp
      (doolittleUAbsBudget fp n A L_hat U_hat)
      (doolittleLAbsBudget fp n A L_hat U_hat) :=
  of_literal_doolittle_source_budgets
    hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag hn
    (by
      intro k j hkj
      exact doolittleUAbsBudget_le_compression_of_component_dominance
        hn hkj (hU_work_le k j hkj) (hU_prod_le k j hkj))
    (by
      intro i k hki
      exact doolittleLAbsBudget_le_compression_of_component_dominance
        hn hki (hL_work_le i k hki) (hL_prod_le i k hki) (hL_num_le i k hki))

/-- Exact-product no-cancellation margins, plus the lower rounded-numerator
dominance condition, produce the literal dense-Doolittle absolute-budget
certificate.  This source-shaped variant accounts for the fact that the
implemented fold subtracts rounded products by paying the explicit
`(1+u_fp)` product-growth factor. -/
theorem of_literal_doolittle_exact_product_margins {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j ≤ |U_hat k j|)
    (hL_margin : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLNumeratorAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|) :
    DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp
      (doolittleUAbsBudget fp n A L_hat U_hat)
      (doolittleLAbsBudget fp n A L_hat U_hat) :=
  of_literal_doolittle_component_dominance
    hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag hn
    (fun k j hkj =>
      doolittleUWorkAbs_le_of_exact_product_margin
        (hU_margin k j hkj))
    (fun k j hkj =>
      doolittleUProductAbs_le_of_exact_product_margin
        (hU_margin k j hkj))
    (fun i k hki =>
      doolittleLWorkAbs_le_of_exact_product_margin
        (hL_margin i k hki))
    (fun i k hki =>
      doolittleLProductAbs_le_of_exact_product_margin
        (hL_margin i k hki))
    hL_num_le

/-- Exact-product work margins plus an explicit lower numerator margin produce
the literal dense-Doolittle absolute-budget certificate.  Compared with
`of_literal_doolittle_exact_product_margins`, this constructor derives the
lower rounded-numerator dominance internally from the exact-product numerator
margin and `gammaValid`. -/
theorem of_literal_doolittle_exact_product_numerator_margins {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j ≤ |U_hat k j|)
    (hL_margin : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_margin : ∀ i k : Fin n, k.val < i.val →
      (|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
        (gamma fp k.val *
            (|A i k| + (1 + fp.u) *
              doolittleLProductAbs fp n A L_hat U_hat i k) +
          fp.u * doolittleLProductAbs fp n A L_hat U_hat i k) ≤
        |L_hat i k * U_hat k k|) :
    DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp
      (doolittleUAbsBudget fp n A L_hat U_hat)
      (doolittleLAbsBudget fp n A L_hat U_hat) :=
  of_literal_doolittle_exact_product_margins
    hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag hn
    hU_margin hL_margin
    (fun i k hki =>
      doolittleLNumeratorAbs_le_of_exact_product_numerator_margin
        (gammaValid_mono fp (Nat.le_of_lt k.isLt) hn)
        (hL_num_margin i k hki))

/-- Exact-target source gaps for the literal Doolittle arithmetic produce the
dense-loop absolute-budget certificate.

This is one layer closer to a concrete implementation than
`of_literal_doolittle_exact_product_numerator_margins`: the assumptions are
gaps for the exact pre-rounded upper and lower Doolittle targets.  The theorem
uses the literal rounded-fold residual budgets above to transfer those gaps to
the stored entries and pivot products. -/
theorem of_literal_doolittle_exact_target_gaps {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A k j| + (1 + fp.u) *
          doolittleUProductAbs fp n A L_hat U_hat k j +
        doolittleUExactTargetResidualBudget fp n A L_hat U_hat k j ≤
        |doolittleUExactTarget n A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          doolittleLProductAbs fp n A L_hat U_hat i k +
        doolittleLExactTargetEntryResidualBudget fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + doolittleLProductAbs fp n A L_hat U_hat i k) +
        doolittleLExactTargetNumeratorResidualBudget
          fp n A L_hat U_hat i k) +
        doolittleLExactTargetEntryResidualBudget
          fp n A L_hat U_hat i k ≤
        |doolittleLExactTarget n A L_hat U_hat i k|) :
    DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp
      (doolittleUAbsBudget fp n A L_hat U_hat)
      (doolittleLAbsBudget fp n A L_hat U_hat) :=
  of_literal_doolittle_exact_product_numerator_margins
    hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag hn
    (fun k j hkj =>
      doolittleUExactProductMargin_of_exactTarget_gap
        (gammaValid_mono fp (Nat.le_of_lt k.isLt) hn)
        (hU_entry_eq k j hkj)
        (hU_gap k j hkj))
    (fun i k hki =>
      doolittleLExactProductMargin_of_exactTarget_gap
        (gammaValid_mono fp (Nat.le_of_lt k.isLt) hn)
        (hU_diag k)
        (hL_entry_eq i k hki)
        (hL_gap i k hki))
    (fun i k hki => by
      simpa [doolittleLExactTargetNumeratorResidualBudget] using
        doolittleLExactProductNumeratorMargin_of_exactTarget_gap
          (gammaValid_mono fp (Nat.le_of_lt k.isLt) hn)
          (hU_diag k)
          (hL_entry_eq i k hki)
          (hL_num_gap i k hki))

end DoolittleDenseLoopAbsBudgetCertificate

/-- Convert a visible relative residual budget into the existential
`theta`-form used by compact Higham-style recurrence certificates. -/
private lemma exists_relative_error_of_abs_sub_le_mul_abs
    (target rounded γ : ℝ) (hγ : 0 ≤ γ)
    (h : |target - rounded| ≤ γ * |rounded|) :
    ∃ θ : ℝ, |θ| ≤ γ ∧ rounded * (1 + θ) = target := by
  by_cases hrounded : rounded = 0
  · subst rounded
    have htarget_abs : |target| ≤ 0 := by simpa using h
    have htarget_abs_eq : |target| = 0 :=
      le_antisymm htarget_abs (abs_nonneg target)
    have htarget : target = 0 := abs_eq_zero.mp htarget_abs_eq
    subst target
    exact ⟨0, by simpa using hγ, by ring⟩
  · refine ⟨(target - rounded) / rounded, ?_, ?_⟩
    · have hpos : 0 < |rounded| := abs_pos.mpr hrounded
      have hdiv :
          |target - rounded| / |rounded| ≤ γ := by
        rw [div_le_iff₀ hpos]
        simpa [mul_comm] using h
      simpa [abs_div] using hdiv
    · field_simp [hrounded]
      ring

namespace DoolittleDenseLoopCertificate

/-- A dense-Doolittle loop certificate with visible residual-compression
budgets produces the compact `DoolittleLU` recurrence certificate. -/
theorem to_DoolittleLU {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hC : DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hγ : 0 ≤ gamma fp n) :
    DoolittleLU n A L_hat U_hat fp where
  L_diag := hC.L_diag
  L_upper_zero := hC.L_upper_zero
  U_lower_zero := hC.U_lower_zero
  U_computed := by
    intro k j hkj
    exact exists_relative_error_of_abs_sub_le_mul_abs
      (A k j -
        ∑ s : Fin n, (if s.val < k.val then L_hat k s * U_hat s j else 0))
      (U_hat k j) (gamma fp n) hγ
      (hC.U_residual_compression k j hkj)
  L_computed := by
    intro i k hki
    exact exists_relative_error_of_abs_sub_le_mul_abs
      (A i k -
        ∑ s : Fin n, (if s.val < k.val then L_hat i s * U_hat s k else 0))
      (L_hat i k * U_hat k k) (gamma fp n) hγ
      (hC.L_residual_compression i k hki)

end DoolittleDenseLoopCertificate

/-- Product split used by Doolittle's row recurrence.  In row `i` and a column
`j` with `i <= j`, all terms after `i` vanish by lower-triangularity of `L`,
and the diagonal entry of `L` contributes the single `U i j` term. -/
private lemma doolittle_product_eq_U {n : ℕ}
    (A L_hat U_hat : Fin n → Fin n → ℝ) (fp : FPModel)
    (hD : DoolittleLU n A L_hat U_hat fp)
    (i j : Fin n) :
    ∑ k : Fin n, L_hat i k * U_hat k j =
      ∑ k : Fin n, (if k.val < i.val then L_hat i k * U_hat k j else 0) +
        U_hat i j := by
  have hsingle :
      (∑ k : Fin n, if k = i then U_hat i j else 0) = U_hat i j := by
    simp
  rw [← hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hklt : k.val < i.val
  · have hki : k ≠ i := Fin.ne_of_val_ne (by omega)
    simp [hklt, hki]
  · by_cases hki : k = i
    · subst k
      simp [hD.L_diag]
    · have hik : i.val < k.val := by omega
      rw [hD.L_upper_zero i k hik, zero_mul]
      simp [hklt, hki]

/-- Product split used by Doolittle's column recurrence.  In row `i` and
column `j` with `j < i`, all terms after `j` vanish by upper-triangularity of
`U`, and the `j`th term contributes `L i j * U j j`. -/
private lemma doolittle_product_eq_L {n : ℕ}
    (A L_hat U_hat : Fin n → Fin n → ℝ) (fp : FPModel)
    (hD : DoolittleLU n A L_hat U_hat fp)
    (i j : Fin n) :
    ∑ k : Fin n, L_hat i k * U_hat k j =
      ∑ k : Fin n, (if k.val < j.val then L_hat i k * U_hat k j else 0) +
        L_hat i j * U_hat j j := by
  have hsingle :
      (∑ k : Fin n, if k = j then L_hat i j * U_hat j j else 0) =
        L_hat i j * U_hat j j := by
    simp
  rw [← hsingle, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hklt : k.val < j.val
  · have hkj : k ≠ j := Fin.ne_of_val_ne (by omega)
    simp [hklt, hkj]
  · by_cases hkj : k = j
    · subst k
      simp
    · have hjk : j.val < k.val := by omega
      rw [hD.U_lower_zero k j hjk, mul_zero]
      simp [hklt, hkj]

/-- A Doolittle recurrence certificate produces the standard componentwise LU
backward-error certificate.  The proof splits each entry into the row-recurrence
case `i <= j` and the column-recurrence case `j < i`; in either case the
residual is one rounded term, bounded by the corresponding term of
`|L_hat||U_hat|`. -/
theorem DoolittleLU.to_LUBackwardError (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hD : DoolittleLU n A L_hat U_hat fp) :
    LUBackwardError n A L_hat U_hat (gamma fp n) where
  L_diag := hD.L_diag
  L_upper_zero := hD.L_upper_zero
  U_lower_zero := hD.U_lower_zero
  backward_bound := by
    intro i j
    let W := ∑ k : Fin n, |L_hat i k| * |U_hat k j|
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    by_cases hij : i.val ≤ j.val
    · rcases hD.U_computed i j hij with ⟨θ, hθ, hrec⟩
      let S := ∑ k : Fin n,
        (if k.val < i.val then L_hat i k * U_hat k j else 0)
      have hprod :
          ∑ k : Fin n, L_hat i k * U_hat k j = S + U_hat i j := by
        simpa [S] using doolittle_product_eq_U A L_hat U_hat fp hD i j
      have hA : A i j = U_hat i j * (1 + θ) + S := by
        linarith [hrec]
      have hdiff :
          ∑ k : Fin n, L_hat i k * U_hat k j - A i j =
            -(θ * U_hat i j) := by
        rw [hprod, hA]
        ring
      have hterm :
          |U_hat i j| ≤ W := by
        have hterm_eq : |U_hat i j| = |L_hat i i| * |U_hat i j| := by
          rw [hD.L_diag i, abs_one, one_mul]
        rw [hterm_eq]
        change |L_hat i i| * |U_hat i j| ≤
          ∑ k : Fin n, |L_hat i k| * |U_hat k j|
        exact Finset.single_le_sum
          (s := Finset.univ)
          (a := i)
          (f := fun k : Fin n => |L_hat i k| * |U_hat k j|)
          (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (Finset.mem_univ i)
      calc
        |∑ k : Fin n, L_hat i k * U_hat k j - A i j|
            = |θ| * |U_hat i j| := by
              rw [hdiff, abs_neg, abs_mul, mul_comm]
        _ ≤ gamma fp n * |U_hat i j| :=
            mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
        _ ≤ gamma fp n * W :=
            mul_le_mul_of_nonneg_left hterm hγ
    · have hji : j.val < i.val := by omega
      rcases hD.L_computed i j hji with ⟨θ, hθ, hrec⟩
      let S := ∑ k : Fin n,
        (if k.val < j.val then L_hat i k * U_hat k j else 0)
      have hprod :
          ∑ k : Fin n, L_hat i k * U_hat k j =
            S + L_hat i j * U_hat j j := by
        simpa [S] using doolittle_product_eq_L A L_hat U_hat fp hD i j
      have hA : A i j = L_hat i j * U_hat j j * (1 + θ) + S := by
        linarith [hrec]
      have hdiff :
          ∑ k : Fin n, L_hat i k * U_hat k j - A i j =
            -(θ * (L_hat i j * U_hat j j)) := by
        rw [hprod, hA]
        ring
      have hterm :
          |L_hat i j| * |U_hat j j| ≤ W := by
        change |L_hat i j| * |U_hat j j| ≤
          ∑ k : Fin n, |L_hat i k| * |U_hat k j|
        exact Finset.single_le_sum
          (s := Finset.univ)
          (a := j)
          (f := fun k : Fin n => |L_hat i k| * |U_hat k j|)
          (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (Finset.mem_univ j)
      calc
        |∑ k : Fin n, L_hat i k * U_hat k j - A i j|
            = |θ| * (|L_hat i j| * |U_hat j j|) := by
              rw [hdiff, abs_neg, abs_mul, abs_mul]
        _ ≤ gamma fp n * (|L_hat i j| * |U_hat j j|) :=
            mul_le_mul_of_nonneg_right hθ
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ ≤ gamma fp n * W :=
            mul_le_mul_of_nonneg_left hterm hγ

/-- The executable-loop certificate feeds the standard LU backward-error
surface once the visible compression budgets have been supplied. -/
theorem DoolittleDenseLoopCertificate.to_LUBackwardError {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hC : DoolittleDenseLoopCertificate n A L_hat U_hat fp)
    (hn : gammaValid fp n) :
    LUBackwardError n A L_hat U_hat (gamma fp n) :=
  DoolittleLU.to_LUBackwardError n fp A L_hat U_hat hn
    (hC.to_DoolittleLU (gamma_nonneg fp hn))

namespace DoolittleDenseLoopAbsBudgetCertificate

/-- Absolute residual budgets plus visible dominance inequalities produce the
compact Doolittle recurrence certificate. -/
theorem to_DoolittleLU {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    {BU BL : Fin n → Fin n → ℝ}
    (hC : DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp BU BL)
    (hγ : 0 ≤ gamma fp n) :
    DoolittleLU n A L_hat U_hat fp :=
  hC.to_denseLoopCertificate.to_DoolittleLU hγ

/-- Absolute residual budgets plus visible dominance inequalities feed the
standard LU backward-error surface. -/
theorem to_LUBackwardError {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    {BU BL : Fin n → Fin n → ℝ}
    (hC : DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp BU BL)
    (hn : gammaValid fp n) :
    LUBackwardError n A L_hat U_hat (gamma fp n) :=
  hC.to_denseLoopCertificate.to_LUBackwardError hn

end DoolittleDenseLoopAbsBudgetCertificate

/-- **Doolittle backward error** (Higham §9.3, Theorem 9.3).

    Doolittle's method (Algorithm 9.2) satisfies the same backward error
    as general Gaussian elimination:
      |L̂Û - A| ≤ γ(n) · |L̂| · |Û|  componentwise

    This is because Doolittle computes the same mathematical operations
    as GE, just organized differently. The inner products have at most n
    terms, giving the γ(n) factor.

    This theorem shows that `DoolittleLU` implies `LUBackwardError`. -/
theorem doolittle_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hD : DoolittleLU n A L_hat U_hat fp) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  lu_backward_error_perturbation n A L_hat U_hat
    (gamma fp n) (gamma_nonneg fp hn)
    (DoolittleLU.to_LUBackwardError n fp A L_hat U_hat hn hD)

/-- **Doolittle full solve** (Higham §9.4, combining Algorithm 9.2 + Theorem 9.4).

    Computing x̂ via Doolittle's LU + triangular solves gives:
      (A + ΔA)x̂ = b  with  |ΔA| ≤ γ(3n) · |L̂||Û|

    This is equivalent to the general LU solve backward error. -/
theorem doolittle_solve_backward_error (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * n) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  lu_solve_backward_error_tight fp n A L_hat U_hat b hL_diag hU_diag hLU hn hn3

end NumStability
