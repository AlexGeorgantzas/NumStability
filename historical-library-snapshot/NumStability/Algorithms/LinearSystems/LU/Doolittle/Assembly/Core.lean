-- NumStability/Algorithms/LinearSystems/LU/Doolittle/Assembly/Core.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Algorithms.LU.Doolittle`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.LU.Doolittle.BackwardError
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Budgets
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates
import NumStability.Algorithms.LinearSystems.LU.Doolittle.RoundedEntries
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.FloatingPoint.Model

/-!
# Core

Relocated from `NumStability.Algorithms.LU.Doolittle` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
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
















































































































































































































































































































































































































































































































































































































































































































namespace DoolittleDenseLoopAbsBudgetCertificate


































































































































































































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























end NumStability
