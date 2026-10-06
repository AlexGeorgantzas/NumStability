import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LU.SpecialMatrices
import NumStability.Algorithms.LU.Tridiagonal
import NumStability.Algorithms.LU.TridiagonalCond
import NumStability.Algorithms.LU.TridiagonalRecurrence
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Budgets
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02

/-!
# Higham Chapter 9: Section03

Canonical source-correspondence owner from Chapter 9 destination-DAG layer 3.
-/

namespace NumStability

open scoped BigOperators
open ComplexConjugate
open Matrix

/-- **Theorem 9.3**, dense executable-loop certificate form: the literal dense
Doolittle loop certificate feeds the standard componentwise backward-error
theorem.  The remaining compression hypotheses are exactly the visible fields
of `higham9_2_DoolittleDenseLoopCertificate`; they are not hidden inside this
wrapper. -/
theorem higham9_3_denseLoopCertificate_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopCertificate n A L_hat U_hat fp) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_3_doolittle_backward_error n fp A L_hat U_hat hn
    (higham9_2_denseLoopCertificate_to_DoolittleLU hC hn)

/-- **Theorem 9.3**, absolute-budget executable-loop form: absolute residual
budgets for the literal Doolittle folds, once dominated by the source relative
budgets, feed the standard componentwise backward-error theorem. -/
theorem higham9_3_absBudgetCertificate_backward_error (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_DoolittleDenseLoopAbsBudgetCertificate n A L_hat U_hat fp BU BL) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_3_doolittle_backward_error n fp A L_hat U_hat hn
    (higham9_2_absBudgetCertificate_to_DoolittleLU hC hn)

/-- **Theorem 9.3**, square literal-source-budget form. -/
theorem higham9_3_literalDoolittle_source_budgets_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_flDoolittleLEntry fp n A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      doolittleUAbsBudget fp n A L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      doolittleLAbsBudget fp n A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_3_absBudgetCertificate_backward_error n fp A L_hat U_hat
    (doolittleUAbsBudget fp n A L_hat U_hat)
    (doolittleLAbsBudget fp n A L_hat U_hat) hn
    (higham9_2_absBudgetCertificate_of_literal_doolittle_source_budgets
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hU_budget_le hL_budget_le)

/-- **Theorem 9.3**, square literal component-dominance form. -/
theorem higham9_3_literalDoolittle_componentDominance_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_flDoolittleLEntry fp n A L_hat U_hat i k)
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
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_3_absBudgetCertificate_backward_error n fp A L_hat U_hat
    (doolittleUAbsBudget fp n A L_hat U_hat)
    (doolittleLAbsBudget fp n A L_hat U_hat) hn
    (higham9_2_absBudgetCertificate_of_literal_doolittle_component_dominance
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hU_work_le hU_prod_le hL_work_le hL_prod_le hL_num_le)

/-- **Theorem 9.3**, square literal exact-product margin form. -/
theorem higham9_3_literalDoolittle_exactProductMargins_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_flDoolittleLEntry fp n A L_hat U_hat i k)
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
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_3_absBudgetCertificate_backward_error n fp A L_hat U_hat
    (doolittleUAbsBudget fp n A L_hat U_hat)
    (doolittleLAbsBudget fp n A L_hat U_hat) hn
    (higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_margins
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hU_margin hL_margin hL_num_le)

/-- **Theorem 9.3**, square literal exact-product numerator-margin form. -/
theorem higham9_3_literalDoolittle_exactProductNumeratorMargins_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_flDoolittleLEntry fp n A L_hat U_hat i k)
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
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_3_absBudgetCertificate_backward_error n fp A L_hat U_hat
    (doolittleUAbsBudget fp n A L_hat U_hat)
    (doolittleLAbsBudget fp n A L_hat U_hat) hn
    (higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hU_margin hL_margin hL_num_margin)

/-- **Theorem 9.3**, square literal exact-target gap form. -/
theorem higham9_3_literalDoolittle_exactTargetGaps_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_flDoolittleUEntry fp n A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_flDoolittleLEntry fp n A L_hat U_hat i k)
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
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_3_absBudgetCertificate_backward_error n fp A L_hat U_hat
    (doolittleUAbsBudget fp n A L_hat U_hat)
    (doolittleLAbsBudget fp n A L_hat U_hat) hn
    (higham9_2_absBudgetCertificate_of_literal_doolittle_exact_target_gaps
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hU_gap hL_gap hL_num_gap)

/-- **Theorem 9.3**, square-specialized rectangular dense-loop form.  A
rectangular Algorithm 9.2 certificate at `m = n` feeds the same componentwise
backward-error theorem as the square dense-loop certificate. -/
theorem higham9_3_rectDenseLoopCertificate_square_backward_error
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      (Nat.le_refl n) A L_hat U_hat fp) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_3_denseLoopCertificate_backward_error n fp A L_hat U_hat hn
    (higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate hC)

/-- **Theorem 9.3**, square-specialized rectangular absolute-budget form.
Absolute residual budgets proved in the rectangular `m x n` source notation,
when specialized to `m = n`, feed the established square Doolittle
backward-error theorem. -/
theorem higham9_3_rectAbsBudgetCertificate_square_backward_error
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (BU BL : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      (Nat.le_refl n) A L_hat U_hat fp BU BL) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  higham9_3_absBudgetCertificate_backward_error n fp A L_hat U_hat BU BL hn
    (higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate hC)

/-- **Theorem 9.3**, square-specialized rectangular literal-source-budget
form.  The literal rounded rectangular Doolittle folds, explicit computed
pivot nonzero hypotheses, and visible absolute-budget dominance hypotheses
give the standard square componentwise backward-error result when `m = n`. -/
theorem higham9_3_rectLiteralDoolittle_source_budgets_square_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k =
        higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  exact
    higham9_3_rectAbsBudgetCertificate_square_backward_error n fp A L_hat U_hat
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L_hat U_hat)
      (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat) hn
      (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_source_budgets
        (hmn := Nat.le_refl n) (A := A) (L := L_hat) (U := U_hat)
        (by
          intro k
          simpa [higham9_2_rectRow] using hL_diag k)
        hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag hn
        hU_budget_le hL_budget_le)

/-- **Theorem 9.3**, square-specialized rectangular literal
component-dominance form.  This exposes the rectangular Algorithm 9.2
component-dominance source conditions directly at `m = n`, with the usual
square componentwise backward-error conclusion. -/
theorem higham9_3_rectLiteralDoolittle_componentDominance_square_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k =
        higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_work_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUWorkAbs fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ |U_hat k j|)
    (hU_prod_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
          A L_hat U_hat k j ≤ |U_hat k j|)
    (hL_work_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLWorkAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_prod_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLNumeratorAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  exact
    higham9_3_rectAbsBudgetCertificate_square_backward_error n fp A L_hat U_hat
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L_hat U_hat)
      (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat) hn
      (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_component_dominance
        (hmn := Nat.le_refl n) (A := A) (L := L_hat) (U := U_hat)
        (by
          intro k
          simpa [higham9_2_rectRow] using hL_diag k)
        hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag hn
        hL_coeff hU_work_le hU_prod_le hL_work_le hL_prod_le hL_num_le)

/-- **Theorem 9.3**, square-specialized rectangular literal exact-product
margin form. -/
theorem higham9_3_rectLiteralDoolittle_exactProductMargins_square_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k =
        higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |A k j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j ≤
        |U_hat k j|)
    (hL_margin : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLNumeratorAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  exact
    higham9_3_rectAbsBudgetCertificate_square_backward_error n fp A L_hat U_hat
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L_hat U_hat)
      (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat) hn
      (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_margins
        (hmn := Nat.le_refl n) (A := A) (L := L_hat) (U := U_hat)
        (by
          intro k
          simpa [higham9_2_rectRow] using hL_diag k)
        hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag hn
        hL_coeff
        (by
          intro k j hkj
          simpa [higham9_2_rectRow] using hU_margin k j hkj)
        hL_margin hL_num_le)

/-- **Theorem 9.3**, square-specialized rectangular literal exact-product
numerator-margin form. -/
theorem higham9_3_rectLiteralDoolittle_exactProductNumeratorMargins_square_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k =
        higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |A k j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j ≤
        |U_hat k j|)
    (hL_margin : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_margin : ∀ i k : Fin n, k.val < i.val →
      (|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        (gamma fp k.val *
            (|A i k| + (1 + fp.u) *
              higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
          fp.u * higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) ≤
        |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  exact
    higham9_3_rectAbsBudgetCertificate_square_backward_error n fp A L_hat U_hat
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L_hat U_hat)
      (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat) hn
      (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins
        (hmn := Nat.le_refl n) (A := A) (L := L_hat) (U := U_hat)
        (by
          intro k
          simpa [higham9_2_rectRow] using hL_diag k)
        hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag hn
        hL_coeff
        (by
          intro k j hkj
          simpa [higham9_2_rectRow] using hU_margin k j hkj)
        hL_margin hL_num_margin)

/-- **Theorem 9.3**, square-specialized rectangular literal exact-target gap
form. -/
theorem higham9_3_rectLiteralDoolittle_exactTargetGaps_square_backward_error
    {n : ℕ} {fp : FPModel}
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L_hat i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A L_hat U_hat k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L_hat i k =
        higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A k j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp (Nat.le_refl n)
            A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp (Nat.le_refl n)
          A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget (Nat.le_refl n)
          A L_hat U_hat k j|)
    (hL_gap : ∀ i k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) := by
  exact
    higham9_3_rectAbsBudgetCertificate_square_backward_error n fp A L_hat U_hat
      (higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L_hat U_hat)
      (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat) hn
      (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps
        (hmn := Nat.le_refl n) (A := A) (L := L_hat) (U := U_hat)
        (by
          intro k
          simpa [higham9_2_rectRow] using hL_diag k)
        hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag hn
        hL_coeff
        (by
          intro k j hkj
          simpa [higham9_2_rectRow] using hU_gap k j hkj)
        hL_gap hL_num_gap)

/-- **Theorem 9.3**, rectangular dense-loop certificate form.

The rectangular `m x n`, `m >= n` Algorithm 9.2 certificate gives the same
componentwise product backward-error shape as the square Doolittle theorem,
but with `L_hat * U_hat` interpreted as a rectangular product. This closes the
certificate-to-error handoff for the rectangular source notation; constructing
the certificate from a concrete executable schedule remains a separate task. -/
theorem higham9_3_rectDenseLoopCertificate_backward_error
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A L_hat : Fin m → Fin n → ℝ) (U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopCertificate
      hmn A L_hat U_hat fp) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, rectMatMul L_hat U_hat i j = A i j + ΔA i j) := by
  refine ⟨fun i j => rectMatMul L_hat U_hat i j - A i j, ?_, ?_⟩
  · intro i j
    have hγ : 0 ≤ gamma fp n := gamma_nonneg fp hn
    by_cases hij : i.val ≤ j.val
    · let k : Fin n := ⟨i.val, lt_of_le_of_lt hij j.isLt⟩
      have hi_row : higham9_2_rectRow hmn k = i := by
        ext
        rfl
      have hkj : k.val ≤ j.val := by
        simpa [k] using hij
      have hprod :=
        higham9_2_rectMatMul_eq_prefix_add_upper
          (hmn := hmn) (U := U_hat) hC.L_diag hC.L_upper_zero k j hkj
      have hentry :=
        higham9_2_abs_upper_entry_le_rectMatMul_abs_sum
          (hmn := hmn) (U := U_hat) hC.L_diag k j
      have hcomp := hC.U_residual_compression k j hkj
      calc
        |(fun i j => rectMatMul L_hat U_hat i j - A i j) i j|
            = |rectMatMul L_hat U_hat (higham9_2_rectRow hmn k) j -
                A (higham9_2_rectRow hmn k) j| := by
                rw [hi_row]
        _ = |(higham9_2_rectPrefixDot L_hat U_hat
                (higham9_2_rectRow hmn k) j k + U_hat k j) -
                A (higham9_2_rectRow hmn k) j| := by
                rw [hprod]
        _ = |(A (higham9_2_rectRow hmn k) j -
                higham9_2_rectPrefixDot L_hat U_hat
                  (higham9_2_rectRow hmn k) j k) -
                U_hat k j| := by
                have hneg :
                    (higham9_2_rectPrefixDot L_hat U_hat
                        (higham9_2_rectRow hmn k) j k + U_hat k j) -
                        A (higham9_2_rectRow hmn k) j =
                      -((A (higham9_2_rectRow hmn k) j -
                          higham9_2_rectPrefixDot L_hat U_hat
                            (higham9_2_rectRow hmn k) j k) -
                          U_hat k j) := by
                  ring
                rw [hneg, abs_neg]
        _ ≤ gamma fp n * |U_hat k j| := hcomp
        _ ≤ gamma fp n *
              ∑ s : Fin n,
                |L_hat (higham9_2_rectRow hmn k) s| * |U_hat s j| :=
              mul_le_mul_of_nonneg_left hentry hγ
        _ = gamma fp n * ∑ s : Fin n, |L_hat i s| * |U_hat s j| := by
              rw [hi_row]
    · have hji : j.val < i.val := lt_of_not_ge hij
      have hprod :=
        higham9_2_rectMatMul_eq_prefix_add_lower
          (L := L_hat) hC.U_lower_zero i j
      have hentry :=
        higham9_2_abs_lower_entry_mul_pivot_le_rectMatMul_abs_sum
          L_hat U_hat i j
      have hcomp := hC.L_residual_compression i j hji
      calc
        |(fun i j => rectMatMul L_hat U_hat i j - A i j) i j|
            = |rectMatMul L_hat U_hat i j - A i j| := rfl
        _ = |(higham9_2_rectPrefixDot L_hat U_hat i j j +
                L_hat i j * U_hat j j) - A i j| := by
                rw [hprod]
        _ = |(A i j - higham9_2_rectPrefixDot L_hat U_hat i j j) -
                L_hat i j * U_hat j j| := by
                have hneg :
                    (higham9_2_rectPrefixDot L_hat U_hat i j j +
                        L_hat i j * U_hat j j) - A i j =
                      -((A i j - higham9_2_rectPrefixDot L_hat U_hat i j j) -
                        L_hat i j * U_hat j j) := by
                  ring
                rw [hneg, abs_neg]
        _ ≤ gamma fp n * |L_hat i j * U_hat j j| := hcomp
        _ ≤ gamma fp n * ∑ s : Fin n, |L_hat i s| * |U_hat s j| :=
              mul_le_mul_of_nonneg_left hentry hγ
  · intro i j
    ring

/-- **Theorem 9.3**, rectangular absolute-budget certificate form. -/
theorem higham9_3_rectAbsBudgetCertificate_backward_error
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    (A L_hat : Fin m → Fin n → ℝ) (U_hat : Fin n → Fin n → ℝ)
    (BU : Fin n → Fin n → ℝ) (BL : Fin m → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hC : higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate
      hmn A L_hat U_hat fp BU BL) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, rectMatMul L_hat U_hat i j = A i j + ΔA i j) :=
  higham9_3_rectDenseLoopCertificate_backward_error A L_hat U_hat hn
    (higham9_2_rectAbsBudgetCertificate_to_rectDenseLoopCertificate hC)

/-- **Theorem 9.3**, rectangular rounded-stage trace form.  A scheduled
rectangular rounded Doolittle trace plus visible absolute-budget dominance
feeds the rectangular componentwise backward-error theorem directly. -/
theorem higham9_3_rectRoundedStageTrace_backward_error
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L_hat : Fin m → Fin n → ℝ} {U_hat : Fin n → Fin n → ℝ}
    (hT : higham9_2_RectDoolittleRoundedStageTrace hmn A L_hat U_hat fp)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, rectMatMul L_hat U_hat i j = A i j + ΔA i j) :=
  higham9_3_rectAbsBudgetCertificate_backward_error A L_hat U_hat
    (higham9_2_rectDoolittleUAbsBudget fp hmn A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat) hn
    (higham9_2_rectRoundedStageTrace_to_rectAbsBudgetCertificate
      hT hU_diag hn hU_budget_le hL_budget_le)

/-- **Theorem 9.3**, executable rectangular rounded-loop form.  The concrete
Algorithm 9.2 loop supplies the rounded-stage trace, so only nonzero computed
pivots and visible budget dominance remain as hypotheses. -/
theorem higham9_3_rectRoundedLoop_backward_error {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m) (A : Fin m → Fin n → ℝ)
    (hU_diag : ∀ k : Fin n, higham9_2_rectRoundedLoopU fp hmn A k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) k j ≤
        gamma fp n * |higham9_2_rectRoundedLoopU fp hmn A k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp hmn A i k *
            higham9_2_rectRoundedLoopU fp hmn A k k|) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp hmn A i k| *
            |higham9_2_rectRoundedLoopU fp hmn A k j|) ∧
      (∀ i j,
        rectMatMul (higham9_2_rectRoundedLoopL fp hmn A)
          (higham9_2_rectRoundedLoopU fp hmn A) i j = A i j + ΔA i j) :=
  higham9_3_rectRoundedStageTrace_backward_error
    (higham9_2_rectRoundedLoopStageTrace fp hmn A)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Theorem 9.3**, completed rectangular rounded-prefix trace form.  A
rectangular Doolittle prefix trace at horizon `n` feeds the same componentwise
backward-error theorem as the full rounded-stage trace. -/
theorem higham9_3_rectRoundedPrefixTrace_complete_backward_error
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L_hat : Fin m → Fin n → ℝ} {U_hat : Fin n → Fin n → ℝ}
    (hT : higham9_2_RectDoolittleRoundedPrefixTrace hmn A L_hat U_hat fp n)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, rectMatMul L_hat U_hat i j = A i j + ΔA i j) :=
  higham9_3_rectRoundedStageTrace_backward_error
    (higham9_2_rectRoundedPrefixTrace_complete_to_stageTrace hT)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Theorem 9.3**, rectangular natural-stage obligation form.  Per-stage
Algorithm 9.2 obligations, nonzero computed pivots, and visible budget
dominance feed the rectangular componentwise backward-error theorem. -/
theorem higham9_3_rectStageObligations_backward_error
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L_hat : Fin m → Fin n → ℝ} {U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ (t : ℕ) (ht : t < n),
      L_hat (higham9_2_rectRow hmn ⟨t, ht⟩) ⟨t, ht⟩ = 1)
    (hL_upper_zero_stage : ∀ (t : ℕ) (ht : t < n),
      ∀ i : Fin m, i.val < t → L_hat i ⟨t, ht⟩ = 0)
    (hU_lower_zero_stage : ∀ (t : ℕ) (ht : t < n),
      ∀ j : Fin n, j.val < t → U_hat ⟨t, ht⟩ j = 0)
    (hU_stage_eq : ∀ (t : ℕ) (ht : t < n),
      ∀ j : Fin n, t ≤ j.val →
        U_hat ⟨t, ht⟩ j =
          higham9_2_rectFlDoolittleUEntry fp hmn A L_hat U_hat ⟨t, ht⟩ j)
    (hL_stage_eq : ∀ (t : ℕ) (ht : t < n),
      ∀ i : Fin m, t < i.val →
        L_hat i ⟨t, ht⟩ =
          higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i ⟨t, ht⟩)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, rectMatMul L_hat U_hat i j = A i j + ΔA i j) :=
  higham9_3_rectRoundedStageTrace_backward_error
    (higham9_2_rectRoundedStageTrace_of_stage_obligations
      hL_diag hL_upper_zero_stage hU_lower_zero_stage hU_stage_eq hL_stage_eq)
    hU_diag hn hU_budget_le hL_budget_le

/-- **Theorem 9.3**, rectangular literal-source-budget form.  Literal rounded
rectangular Doolittle folds, nonzero computed pivots, and visible
absolute-budget dominance hypotheses produce a rectangular componentwise
backward-error theorem directly in the source `m x n` notation. -/
theorem higham9_3_rectLiteralDoolittle_source_budgets_backward_error
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L_hat : Fin m → Fin n → ℝ} {U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_rectFlDoolittleUEntry fp hmn A L_hat U_hat k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp hmn A L_hat U_hat k j ≤
        gamma fp n * |U_hat k j|)
    (hL_budget_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat i k ≤
        gamma fp n * |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, rectMatMul L_hat U_hat i j = A i j + ΔA i j) :=
  higham9_3_rectAbsBudgetCertificate_backward_error A L_hat U_hat
    (higham9_2_rectDoolittleUAbsBudget fp hmn A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat) hn
    (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_source_budgets
      (hmn := hmn) (A := A) (L := L_hat) (U := U_hat)
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hU_budget_le hL_budget_le)

/-- **Theorem 9.3**, rectangular literal component-dominance form. -/
theorem higham9_3_rectLiteralDoolittle_componentDominance_backward_error
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L_hat : Fin m → Fin n → ℝ} {U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_rectFlDoolittleUEntry fp hmn A L_hat U_hat k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_work_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUWorkAbs fp hmn A L_hat U_hat k j ≤ |U_hat k j|)
    (hU_prod_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUProductAbs fp hmn A L_hat U_hat k j ≤ |U_hat k j|)
    (hL_work_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLWorkAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_prod_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLNumeratorAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, rectMatMul L_hat U_hat i j = A i j + ΔA i j) :=
  higham9_3_rectAbsBudgetCertificate_backward_error A L_hat U_hat
    (higham9_2_rectDoolittleUAbsBudget fp hmn A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat) hn
    (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_component_dominance
      (hmn := hmn) (A := A) (L := L_hat) (U := U_hat)
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff hU_work_le hU_prod_le hL_work_le hL_prod_le hL_num_le)

/-- **Theorem 9.3**, rectangular literal exact-product margin form. -/
theorem higham9_3_rectLiteralDoolittle_exactProductMargins_backward_error
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L_hat : Fin m → Fin n → ℝ} {U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_rectFlDoolittleUEntry fp hmn A L_hat U_hat k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow hmn k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp hmn A L_hat U_hat k j ≤
        |U_hat k j|)
    (hL_margin : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_le : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLNumeratorAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, rectMatMul L_hat U_hat i j = A i j + ΔA i j) :=
  higham9_3_rectAbsBudgetCertificate_backward_error A L_hat U_hat
    (higham9_2_rectDoolittleUAbsBudget fp hmn A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat) hn
    (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_margins
      (hmn := hmn) (A := A) (L := L_hat) (U := U_hat)
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff hU_margin hL_margin hL_num_le)

/-- **Theorem 9.3**, rectangular literal exact-product numerator-margin form. -/
theorem higham9_3_rectLiteralDoolittle_exactProductNumeratorMargins_backward_error
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L_hat : Fin m → Fin n → ℝ} {U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_rectFlDoolittleUEntry fp hmn A L_hat U_hat k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_margin : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow hmn k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp hmn A L_hat U_hat k j ≤
        |U_hat k j|)
    (hL_margin : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k ≤
        |L_hat i k * U_hat k k|)
    (hL_num_margin : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      (|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        (gamma fp k.val *
            (|A i k| + (1 + fp.u) *
              higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
          fp.u * higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) ≤
        |L_hat i k * U_hat k k|) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, rectMatMul L_hat U_hat i j = A i j + ΔA i j) :=
  higham9_3_rectAbsBudgetCertificate_backward_error A L_hat U_hat
    (higham9_2_rectDoolittleUAbsBudget fp hmn A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat) hn
    (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins
      (hmn := hmn) (A := A) (L := L_hat) (U := U_hat)
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff hU_margin hL_margin hL_num_margin)

/-- **Theorem 9.3**, rectangular literal exact-target gap form. -/
theorem higham9_3_rectLiteralDoolittle_exactTargetGaps_backward_error
    {m n : ℕ} {fp : FPModel} {hmn : n ≤ m}
    {A L_hat : Fin m → Fin n → ℝ} {U_hat : Fin n → Fin n → ℝ}
    (hL_diag : ∀ k : Fin n, L_hat (higham9_2_rectRow hmn k) k = 1)
    (hL_upper_zero : ∀ i : Fin m, ∀ j : Fin n, i.val < j.val → L_hat i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U_hat k j = higham9_2_rectFlDoolittleUEntry fp hmn A L_hat U_hat k j)
    (hL_entry_eq : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      L_hat i k = higham9_2_rectFlDoolittleLEntry fp A L_hat U_hat i k)
    (hU_diag : ∀ k : Fin n, U_hat k k ≠ 0)
    (hn : gammaValid fp n)
    (hL_coeff : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      gamma fp k.val + fp.u + fp.u ≤ gamma fp n)
    (hU_gap : ∀ k j : Fin n, k.val ≤ j.val →
      |A (higham9_2_rectRow hmn k) j| + (1 + fp.u) *
          higham9_2_rectDoolittleUProductAbs fp hmn A L_hat U_hat k j +
        higham9_2_rectDoolittleUExactTargetResidualBudget fp hmn A L_hat U_hat k j ≤
        |higham9_2_rectDoolittleUExactTarget hmn A L_hat U_hat k j|)
    (hL_gap : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      |A i k| + (1 + fp.u) *
          higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|)
    (hL_num_gap : ∀ i : Fin m, ∀ k : Fin n, k.val < i.val →
      ((|A i k| + higham9_2_rectDoolittleLProductAbs fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget
          fp A L_hat U_hat i k) +
        higham9_2_rectDoolittleLExactTargetEntryResidualBudget
          fp A L_hat U_hat i k ≤
        |higham9_2_rectDoolittleLExactTarget A L_hat U_hat i k|) :
    ∃ ΔA : Fin m → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, rectMatMul L_hat U_hat i j = A i j + ΔA i j) :=
  higham9_3_rectAbsBudgetCertificate_backward_error A L_hat U_hat
    (higham9_2_rectDoolittleUAbsBudget fp hmn A L_hat U_hat)
    (higham9_2_rectDoolittleLAbsBudget fp A L_hat U_hat) hn
    (higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps
      (hmn := hmn) (A := A) (L := L_hat) (U := U_hat)
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq
      hU_diag hn hL_coeff hU_gap hL_gap hL_num_gap)

/-- **Theorem 9.3**, generic LU backward-error-certificate form. -/
theorem higham9_3_lu_backward_error_gamma (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (hn : gammaValid fp n)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n)) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, L_hat i k * U_hat k j = A i j + ΔA i j) :=
  lu_backward_error_gamma fp n A L_hat U_hat hn hLU

/-- **Algorithm 9.2 / Theorem 9.3**, exact Doolittle recurrences as a zero
`LUBackwardError` certificate.  Exact upper/lower recurrence equations, shape
hypotheses, unit lower diagonal, and nonzero pivots first produce an exact
`LUFactSpec`, hence a zero componentwise backward-error certificate.  This is
an exact-arithmetic handoff and does not construct the rounded executable loop. -/
theorem higham9_3_exactDoolittle_recurrences_to_LUBackwardError_zero {n : ℕ}
    {A L U : Fin n → Fin n → ℝ}
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectDoolittleUUpdate (Nat.le_refl n) A L U k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L i k = higham9_2_rectDoolittleLUpdate A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0) :
    LUBackwardError n A L U 0 :=
  LUFactSpec.to_LUBackwardError_zero
    (higham9_2_exactDoolittle_recurrences_to_LUFactSpec
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag)

/-- Monotonicity of an LU backward-error certificate in its scalar error
coefficient.  The triangular structure is unchanged; only the componentwise
residual bound is weakened. -/
theorem higham9_LUBackwardError_mono {n : ℕ}
    {A L_hat U_hat : Fin n → Fin n → ℝ} {ε η : ℝ}
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hεη : ε ≤ η) :
    LUBackwardError n A L_hat U_hat η where
  L_diag := hLU.L_diag
  L_upper_zero := hLU.L_upper_zero
  U_lower_zero := hLU.U_lower_zero
  backward_bound := by
    intro i j
    have hW_nonneg :
        0 ≤ ∑ k : Fin n, |L_hat i k| * |U_hat k j| := by
      exact Finset.sum_nonneg
        (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact (hLU.backward_bound i j).trans
      (mul_le_mul_of_nonneg_right hεη hW_nonneg)

/-- Exact LU certificates also satisfy Higham's public `γ_n`
backward-error interface. -/
theorem higham9_LUFactSpec_to_LUBackwardError_gamma (fp : FPModel) (n : ℕ)
    {A L_hat U_hat : Fin n → Fin n → ℝ}
    (hn : gammaValid fp n)
    (hLU : LUFactSpec n A L_hat U_hat) :
    LUBackwardError n A L_hat U_hat (gamma fp n) :=
  higham9_LUBackwardError_mono
    (LUFactSpec.to_LUBackwardError_zero hLU) (gamma_nonneg fp hn)

/-- **Algorithm 9.2 / Theorem 9.3**, exact Doolittle recurrences weakened to
Higham's `γ_n` backward-error certificate.  The residual is still exactly zero;
`γ_n` only matches the public Theorem 9.3 API. -/
theorem higham9_3_exactDoolittle_recurrences_to_LUBackwardError_gamma
    {n : ℕ} {fp : FPModel} {A L U : Fin n → Fin n → ℝ}
    (hn : gammaValid fp n)
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectDoolittleUUpdate (Nat.le_refl n) A L U k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L i k = higham9_2_rectDoolittleLUpdate A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0) :
    LUBackwardError n A L U (gamma fp n) where
  L_diag := hL_diag
  L_upper_zero := hL_upper_zero
  U_lower_zero := hU_lower_zero
  backward_bound := by
    intro i j
    let hLU := higham9_2_exactDoolittle_recurrences_to_LUFactSpec
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag
    have hzero :
        |∑ k : Fin n, L i k * U k j - A i j| = 0 := by
      rw [hLU.product_eq i j]
      simp
    rw [hzero]
    exact mul_nonneg (gamma_nonneg fp hn)
      (Finset.sum_nonneg
        (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))

/-- **Algorithm 9.2 / Theorem 9.3**, exact Doolittle recurrence handoff to the
standard componentwise backward-error perturbation surface.  This closes the
exact recurrence-to-`ΔA` adapter; the rounded executable schedule that proves
these recurrence hypotheses for computed factors remains open. -/
theorem higham9_3_exactDoolittle_recurrences_backward_error_gamma
    {n : ℕ} {fp : FPModel} {A L U : Fin n → Fin n → ℝ}
    (hn : gammaValid fp n)
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectDoolittleUUpdate (Nat.le_refl n) A L U k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L i k = higham9_2_rectDoolittleLUpdate A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ k : Fin n, |L i k| * |U k j|) ∧
      (∀ i j, ∑ k : Fin n, L i k * U k j = A i j + ΔA i j) :=
  higham9_3_lu_backward_error_gamma fp n A L U hn
    (higham9_3_exactDoolittle_recurrences_to_LUBackwardError_gamma hn
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag)

/-- **Theorem 9.4**: LU factorization plus two triangular solves, with
Higham's absorbed `γ_{3n}` componentwise bound. -/
theorem higham9_4_lu_solve_backward_error (fp : FPModel) (n : ℕ)
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

/-- **Algorithm 9.2 / Theorem 9.4**, exact Doolittle recurrence handoff to the
LU-solve backward-error surface.  Exact recurrences give the factorization
backward-error certificate; the triangular solves remain the modeled floating-
point solves in `higham9_4_lu_solve_backward_error`. -/
theorem higham9_4_exactDoolittle_recurrences_lu_solve_backward_error
    {n : ℕ} {fp : FPModel} {A L U : Fin n → Fin n → ℝ}
    (b : Fin n → ℝ)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hL_upper_zero : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hU_lower_zero : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hU_entry_eq : ∀ k j : Fin n, k.val ≤ j.val →
      U k j = higham9_2_rectDoolittleUUpdate (Nat.le_refl n) A L U k j)
    (hL_entry_eq : ∀ i k : Fin n, k.val < i.val →
      L i k = higham9_2_rectDoolittleLUpdate A L U i k)
    (hU_diag : ∀ k : Fin n, U k k ≠ 0) :
    let y_hat := fl_forwardSub fp n L b
    let x_hat := fl_backSub fp n U y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * n) *
        ∑ k : Fin n, |L i k| * |U k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  higham9_4_lu_solve_backward_error fp n A L U b
    (by
      intro i
      rw [hL_diag i]
      norm_num)
    hU_diag
    (higham9_3_exactDoolittle_recurrences_to_LUBackwardError_gamma hn
      hL_diag hL_upper_zero hU_lower_zero hU_entry_eq hL_entry_eq hU_diag)
    hn hn3

/-- **Algorithm 9.2 / Theorem 9.4**, square executable rectangular rounded-loop
handoff to the LU-solve backward-error surface.  The loop supplies the
`DoolittleLU` recurrence certificate; triangular solves and the explicit
nonzero-pivot/budget hypotheses remain visible. -/
theorem higham9_4_rectRoundedLoop_square_lu_solve_backward_error {n : ℕ}
    (fp : FPModel) (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) k j ≤
        gamma fp n * |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|)
    (hL_budget_le : ∀ i : Fin n, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k|) :
    let y_hat := fl_forwardSub fp n
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A) b
    let x_hat := fl_backSub fp n
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A) y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ gamma fp (3 * n) *
        ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let L := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
  let U := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
  have hL_diag_ne : ∀ i : Fin n, L i i ≠ 0 := by
    intro i
    have hdiag : L i i = 1 := by
      simpa [L, higham9_2_rectRow] using
        (higham9_2_rectRoundedLoopL_diag fp (Nat.le_refl n) A i)
    rw [hdiag]
    norm_num
  have hU_diag' : ∀ i : Fin n, U i i ≠ 0 := by
    intro i
    simpa [U] using hU_diag i
  have hU_budget_le' : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n) A L U k j ≤
        gamma fp n * |U k j| := by
    intro k j hkj
    simpa [L, U] using hU_budget_le k j hkj
  have hL_budget_le' : ∀ i : Fin n, ∀ k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp A L U i k ≤
        gamma fp n * |L i k * U k k| := by
    intro i k hki
    simpa [L, U] using hL_budget_le i k hki
  have hD : higham9_2_DoolittleLU n A L U fp := by
    simpa [L, U] using
      (higham9_2_rectRoundedLoop_square_to_DoolittleLU fp A
        hU_diag hn hU_budget_le hL_budget_le)
  have hBE : LUBackwardError n A L U (gamma fp n) :=
    DoolittleLU.to_LUBackwardError n fp A L U hn hD
  simpa [L, U] using
    (higham9_4_lu_solve_backward_error fp n A L U b
      hL_diag_ne hU_diag' hBE hn hn3)

/-- **Problem 9.4**, row-pivoted analogue of Theorem 9.4.

If the LU backward-error certificate is for `P A`, the triangular solves use
the permuted right-hand side `P b`.  Unpermuting the perturbation rows gives a
backward error for the original system `A x = b`, with the componentwise bound
recorded in source pivoted-row coordinates. -/
theorem higham_problem9_4_permuted_lu_solve_backward_error
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA (sigma i) j| ≤ gamma fp (3 * n) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  classical
  let bP : Fin n → ℝ := fun i => b (sigma i)
  let Aperm : Fin n → Fin n → ℝ := higham9_2_rowPermutedMatrix A sigma
  obtain ⟨ΔPA, hΔPA_bound, hΔPA_eq⟩ :=
    lu_solve_backward_error_tight fp n Aperm L_hat U_hat bP
      hL_diag hU_diag
      (higham9_2_permutedLUBackwardError_to_LUBackwardError hLU) hn hn3
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hLU.perm
  let ΔA : Fin n → Fin n → ℝ := fun i j => ΔPA (eSigma.symm i) j
  refine ⟨ΔA, ?_, ?_⟩
  · intro i j
    simpa [ΔA, eSigma] using hΔPA_bound i j
  · intro i
    have hrow := hΔPA_eq (eSigma.symm i)
    have hsigma_symm : sigma (eSigma.symm i) = i := by
      change eSigma (eSigma.symm i) = i
      exact Equiv.apply_symm_apply eSigma i
    calc
      ∑ j : Fin n, (A i j + ΔA i j) *
          (fl_backSub fp n U_hat (fl_forwardSub fp n L_hat bP)) j
          = ∑ j : Fin n, (Aperm (eSigma.symm i) j + ΔPA (eSigma.symm i) j) *
              (fl_backSub fp n U_hat (fl_forwardSub fp n L_hat bP)) j := by
            apply Finset.sum_congr rfl
            intro j _
            simp [Aperm, higham9_2_rowPermutedMatrix, ΔA, hsigma_symm]
      _ = bP (eSigma.symm i) := hrow
      _ = b i := by simp [bP, hsigma_symm]

/-- **Problem 9.4**, complete-pivoted analogue of Theorem 9.4.

For a complete-pivoting certificate `P A Q`, the triangular solves compute the
permuted unknown `z`; the returned original-order vector is
`x_j = z_(Q^{-1} j)`.  The perturbation is unpermuted in both rows and columns,
while the componentwise bound is recorded in the source `P A Q` coordinates. -/
theorem higham_problem9_4_complete_permuted_lu_solve_backward_error
    (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (sigma tau : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau
      (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let z_hat := fl_backSub fp n U_hat y_hat
    let x_hat : Fin n → ℝ :=
      fun j => z_hat ((Equiv.ofBijective tau hLU.1).symm j)
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA (sigma i) (tau j)| ≤ gamma fp (3 * n) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  classical
  let bP : Fin n → ℝ := fun i => b (sigma i)
  let B : Fin n → Fin n → ℝ := higham9_2_rowColPermutedMatrix A sigma tau
  obtain ⟨ΔB, hΔB_bound, hΔB_eq⟩ :=
    lu_solve_backward_error_tight fp n B L_hat U_hat bP
      hL_diag hU_diag
      (higham9_2_completePermutedLUBackwardError_to_LUBackwardError hLU) hn hn3
  let eSigma : Fin n ≃ Fin n := Equiv.ofBijective sigma hLU.2.perm
  let eTau : Fin n ≃ Fin n := Equiv.ofBijective tau hLU.1
  let z_hat := fl_backSub fp n U_hat (fl_forwardSub fp n L_hat bP)
  let x_hat : Fin n → ℝ := fun j => z_hat (eTau.symm j)
  let ΔA : Fin n → Fin n → ℝ := fun i j => ΔB (eSigma.symm i) (eTau.symm j)
  refine ⟨ΔA, ?_, ?_⟩
  · intro i j
    simpa [ΔA, eSigma, eTau] using hΔB_bound i j
  · intro i
    have hrow := hΔB_eq (eSigma.symm i)
    have hsigma_symm : sigma (eSigma.symm i) = i := by
      change eSigma (eSigma.symm i) = i
      exact Equiv.apply_symm_apply eSigma i
    let f : Fin n → ℝ := fun j => (A i j + ΔA i j) * x_hat j
    calc
      ∑ j : Fin n, (A i j + ΔA i j) * x_hat j
          = ∑ j : Fin n, f (eTau j) := by
              simpa [f] using (Equiv.sum_comp eTau f).symm
      _ = ∑ j : Fin n, (B (eSigma.symm i) j + ΔB (eSigma.symm i) j) *
            z_hat j := by
          apply Finset.sum_congr rfl
          intro j _
          simp [f, B, higham9_2_rowColPermutedMatrix,
            higham9_2_rowPermutedMatrix, higham9_2_colPermutedMatrix,
            ΔA, x_hat, z_hat, eTau, hsigma_symm]
      _ = bP (eSigma.symm i) := hrow
      _ = b i := by simp [bP, hsigma_symm]

/-- **Problem 9.4 / Algorithm 9.2**, executable row-pivoted rectangular
rounded-loop solve handoff.

The concrete rectangular rounded Doolittle loop is run on the row-permuted
matrix `PA`; the triangular solve uses the permuted right-hand side `Pb`.
The remaining side conditions are exactly the local nonzero computed pivots
and visible rectangular budget dominance hypotheses. -/
theorem higham_problem9_4_permuted_rectRoundedLoop_lu_solve_backward_error
    {n : ℕ} (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (sigma : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hsigma : IsPermutation n sigma)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma) k k ≠ 0)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowPermutedMatrix A sigma)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowPermutedMatrix A sigma) k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
      (higham9_2_rowPermutedMatrix A sigma)
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
      (higham9_2_rowPermutedMatrix A sigma)
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA (sigma i) j| ≤ gamma fp (3 * n) *
        ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma) i k| *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowPermutedMatrix A sigma) k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let PA := higham9_2_rowPermutedMatrix A sigma
  let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) PA
  let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) PA
  have hL_diag : ∀ i : Fin n, L_hat i i ≠ 0 := by
    intro i
    have hdiag : L_hat i i = 1 := by
      simpa [L_hat, PA, higham9_2_rectRow] using
        (higham9_2_rectRoundedLoopL_diag fp (Nat.le_refl n) PA i)
    rw [hdiag]
    norm_num
  have hU_diag' : ∀ i : Fin n, U_hat i i ≠ 0 := by
    intro i
    simpa [U_hat, PA] using hU_diag i
  have hBE :
      higham9_2_PermutedLUBackwardError n A L_hat U_hat sigma (gamma fp n) := by
    simpa [L_hat, U_hat, PA] using
      (higham9_2_permutedRectRoundedLoop_to_PermutedLUBackwardError
        fp A sigma hsigma hU_diag hn hU_budget_le hL_budget_le)
  simpa [L_hat, U_hat, PA] using
    (higham_problem9_4_permuted_lu_solve_backward_error
      fp n A L_hat U_hat sigma b hL_diag hU_diag' hBE hn hn3)

/-- **Problem 9.4 / Algorithm 9.2**, executable complete-pivoted rectangular
rounded-loop solve handoff.

The concrete rectangular rounded Doolittle loop is run on `PAQ`; the returned
solution is unpermuted by `Q^{-1}` as in the complete-pivoted solve wrapper. -/
theorem higham_problem9_4_complete_permuted_rectRoundedLoop_lu_solve_backward_error
    {n : ℕ} (fp : FPModel)
    (A : Fin n → Fin n → ℝ) (sigma tau : Fin n → Fin n)
    (b : Fin n → ℝ)
    (hsigma : IsPermutation n sigma)
    (htau : IsPermutation n tau)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau) k k ≠ 0)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hU_budget_le : ∀ k j : Fin n, k.val ≤ j.val →
      higham9_2_rectDoolittleUAbsBudget fp (Nat.le_refl n)
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) k j ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau) k j|)
    (hL_budget_le : ∀ i k : Fin n, k.val < i.val →
      higham9_2_rectDoolittleLAbsBudget fp
          (higham9_2_rowColPermutedMatrix A sigma tau)
          (higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau))
          (higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau)) i k ≤
        gamma fp n *
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) i k *
            higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
              (higham9_2_rowColPermutedMatrix A sigma tau) k k|) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
      (higham9_2_rowColPermutedMatrix A sigma tau)
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
      (higham9_2_rowColPermutedMatrix A sigma tau)
    let bP : Fin n → ℝ := fun i => b (sigma i)
    let y_hat := fl_forwardSub fp n L_hat bP
    let z_hat := fl_backSub fp n U_hat y_hat
    let x_hat : Fin n → ℝ :=
      fun j => z_hat ((Equiv.ofBijective tau htau).symm j)
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA (sigma i) (tau j)| ≤ gamma fp (3 * n) *
        ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau) i k| *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n)
            (higham9_2_rowColPermutedMatrix A sigma tau) k j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  let PAQ := higham9_2_rowColPermutedMatrix A sigma tau
  let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) PAQ
  let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) PAQ
  have hL_diag : ∀ i : Fin n, L_hat i i ≠ 0 := by
    intro i
    have hdiag : L_hat i i = 1 := by
      simpa [L_hat, PAQ, higham9_2_rectRow] using
        (higham9_2_rectRoundedLoopL_diag fp (Nat.le_refl n) PAQ i)
    rw [hdiag]
    norm_num
  have hU_diag' : ∀ i : Fin n, U_hat i i ≠ 0 := by
    intro i
    simpa [U_hat, PAQ] using hU_diag i
  have hBE :
      higham9_2_CompletePermutedLUBackwardError n A L_hat U_hat sigma tau
        (gamma fp n) := by
    simpa [L_hat, U_hat, PAQ] using
      (higham9_2_completePermutedRectRoundedLoop_to_CompletePermutedLUBackwardError
        fp A sigma tau hsigma htau hU_diag hn hU_budget_le hL_budget_le)
  simpa [L_hat, U_hat, PAQ] using
    (higham_problem9_4_complete_permuted_lu_solve_backward_error
      fp n A L_hat U_hat sigma tau b hL_diag hU_diag' hBE hn hn3)

/-- **Equation (9.8)**: nonnegative computed factors give
`|L_hat||U_hat| ≤ |A|/(1-ε)`. -/
theorem higham9_8_nonneg_factor_bound (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε_lt : ε < 1) (hε_nn : 0 ≤ ε)
    (hLU : LUBackwardError n A L_hat U_hat ε)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |L_hat i k| * |U_hat k j| ≤ |A i j| / (1 - ε) :=
  nonneg_factor_bound n A L_hat U_hat ε hε_lt hε_nn hLU hL_nn hU_nn

/-- **Equation (9.9)**: LU solve bound specialized by the nonnegative-factor
correction from (9.8), giving `γ_{3n}/(1-γ_n)` times `|A|`. -/
theorem higham9_9_nonneg_lu_solve_backward_error (fp : FPModel) (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hγ_lt : gamma fp n < 1)
    (hL_nn : ∀ i k : Fin n, 0 ≤ L_hat i k)
    (hU_nn : ∀ k j : Fin n, 0 ≤ U_hat k j) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤
        (gamma fp (3 * n) / (1 - gamma fp n)) * |A i j|) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) := by
  intro y_hat x_hat
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    lu_solve_backward_error_tight fp n A L_hat U_hat b
      hL_diag hU_diag hLU hn hn3
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hW :=
    nonneg_factor_bound n A L_hat U_hat (gamma fp n) hγ_lt
      (gamma_nonneg fp hn) hLU hL_nn hU_nn i j
  have hγ3 : 0 ≤ gamma fp (3 * n) := gamma_nonneg fp hn3
  calc
    |ΔA i j| ≤ gamma fp (3 * n) *
        ∑ k : Fin n, |L_hat i k| * |U_hat k j| := hΔA_bound i j
    _ ≤ gamma fp (3 * n) * (|A i j| / (1 - gamma fp n)) :=
        mul_le_mul_of_nonneg_left hW hγ3
    _ = (gamma fp (3 * n) / (1 - gamma fp n)) * |A i j| := by
        ring

/-- **Theorem 9.5**, repository `∞`-norm Wilkinson form:
`‖ΔA‖∞ ≤ γ_{3n} n ‖U_hat‖∞`. -/
theorem higham9_5_wilkinson_normwise_infNorm_tight (fp : FPModel) (n : ℕ)
    (hn_pos : 0 < n)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L_hat i i ≠ 0)
    (hU_diag : ∀ i : Fin n, U_hat i i ≠ 0)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n))
    (hL_bound : ∀ i j : Fin n, |L_hat i j| ≤ 1) :
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    ∃ ΔA : Fin n → Fin n → ℝ,
      (infNorm ΔA ≤ gamma fp (3 * n) * ↑n * infNorm U_hat) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * x_hat j = b i) :=
  wilkinson_normwise_infNorm_tight fp n hn_pos A L_hat U_hat b
    hL_diag hU_diag hLU hn hn3 hL_bound

end NumStability
