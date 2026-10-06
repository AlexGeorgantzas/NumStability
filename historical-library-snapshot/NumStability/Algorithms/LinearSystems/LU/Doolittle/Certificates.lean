import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Budgets
import NumStability.Algorithms.LinearSystems.LU.Doolittle.RoundedEntries
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.FloatingPoint.Model

/-!
# Certificates

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





























































end DoolittleDenseLoopAbsBudgetCertificate

























namespace DoolittleDenseLoopCertificate


























end DoolittleDenseLoopCertificate























































































































































namespace DoolittleDenseLoopAbsBudgetCertificate





















end DoolittleDenseLoopAbsBudgetCertificate














































end NumStability
