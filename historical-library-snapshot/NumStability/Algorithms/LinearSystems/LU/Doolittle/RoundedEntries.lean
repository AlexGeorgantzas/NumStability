import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.LUSolve
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.FloatingPoint.Model

/-!
# RoundedEntries

Retained R03 owner (reusable): every declaration stays at this exact path
under the frozen B0005 route; wave R03 adds this module docstring only.
-/


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














namespace NumStability

open scoped BigOperators

-- ============================================================
-- §9.2  Doolittle's method specification
-- ============================================================


































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













































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































namespace DoolittleDenseLoopAbsBudgetCertificate






























































































































































































































































end DoolittleDenseLoopAbsBudgetCertificate

























namespace DoolittleDenseLoopCertificate


























end DoolittleDenseLoopCertificate























































































































































namespace DoolittleDenseLoopAbsBudgetCertificate





















end DoolittleDenseLoopAbsBudgetCertificate














































end NumStability
