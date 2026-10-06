import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.LU.Doolittle.RoundedEntries
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.FloatingPoint.Model

/-!
# Budgets

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
















































































namespace DoolittleDenseLoopAbsBudgetCertificate






























































































































































































































































end DoolittleDenseLoopAbsBudgetCertificate

























namespace DoolittleDenseLoopCertificate


























end DoolittleDenseLoopCertificate























































































































































namespace DoolittleDenseLoopAbsBudgetCertificate





















end DoolittleDenseLoopAbsBudgetCertificate














































end NumStability
