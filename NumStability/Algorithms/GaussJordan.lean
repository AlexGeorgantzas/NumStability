-- Algorithms/GaussJordan.lean
--
-- Higham Chapter 14, §14.4: Gauss–Jordan Elimination.
--
-- The second stage of GJE reduces the upper triangular factor U from
-- Gaussian elimination to diagonal form via matrices N_k.
-- This file proves the algebraic composition from explicitly supplied
-- second-stage contracts to the overall GJE residual and forward-error
-- bounds.  The local recurrence/second-stage bounds are exposed as abstract
-- interfaces rather than derived here from a concrete GJE loop.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.ForwardError
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.HighamChapter9

namespace NumStability

open Finset BigOperators

-- ══════════════════════════════════════════════════════════════════════
-- §14.4  GJE second-stage cumulative error constant
-- ══════════════════════════════════════════════════════════════════════

/-- **GJE second-stage cumulative error constant** (Higham §14.4).

    The accumulation of n−1 elimination steps, each introducing error γ₃
    with (1+γ₃) amplification per subsequent step, gives the cumulative
    bound (n−1)γ₃(1+γ₃)^{n−2}. -/
noncomputable def gje_c₃ (fp : FPModel) (n : ℕ) : ℝ :=
  ((n : ℝ) - 1) * gamma fp 3 * (1 + gamma fp 3) ^ (n - 2)

/-- Higham, 2nd ed., Chapter 14, Theorem 14.5 support:
    specialize the generic `gamma` first-order split to the `gamma_3`
    correction term used by the GJE second-stage constant. -/
theorem gamma_three_sub_linear_eq_quadratic_remainder
    (fp : FPModel) (h3 : gammaValid fp 3) :
    gamma fp 3 - 3 * fp.u =
      (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) := by
  rw [gamma_eq_linear_plus_quadratic_remainder fp 3 h3]
  ring

/-- Higham, 2nd ed., Chapter 14, Theorem 14.5 support:
    exact scalar split of the GJE cumulative coefficient into the displayed
    first-order term `3 (n - 1) u` plus explicit higher-order factors. -/
theorem gje_c3_eq_linear_plus_explicit_remainder
    (fp : FPModel) (n : ℕ) :
    gje_c₃ fp n =
      3 * ((n : ℝ) - 1) * fp.u +
        ((n : ℝ) - 1) *
          ((gamma fp 3 - 3 * fp.u) * (1 + gamma fp 3) ^ (n - 2) +
            3 * fp.u * ((1 + gamma fp 3) ^ (n - 2) - 1)) := by
  unfold gje_c₃
  ring

/-- Higham, 2nd ed., Chapter 14, Theorem 14.5 support:
    the preceding split with the `gamma_3 - 3u` term expanded using the
    standard quadratic-and-higher `gamma` remainder. -/
theorem gje_c3_eq_linear_plus_quadratic_remainder
    (fp : FPModel) (n : ℕ) (h3 : gammaValid fp 3) :
    gje_c₃ fp n =
      3 * ((n : ℝ) - 1) * fp.u +
        ((n : ℝ) - 1) *
          (((((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u)) *
              (1 + gamma fp 3) ^ (n - 2) +
            3 * fp.u * ((1 + gamma fp 3) ^ (n - 2) - 1)) := by
  rw [gje_c3_eq_linear_plus_explicit_remainder,
    gamma_three_sub_linear_eq_quadratic_remainder fp h3]

/-- Explicit higher-order term in the Chapter 14 first-order split of
    the GJE cumulative coefficient. -/
noncomputable def gje_c3_quadratic_remainder (fp : FPModel) (n : ℕ) : ℝ :=
  ((n : ℝ) - 1) *
    (((((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u)) *
        (1 + gamma fp 3) ^ (n - 2) +
      3 * fp.u * ((1 + gamma fp 3) ^ (n - 2) - 1))

/-- Named form of the `gje_c₃` first-order split, using
    `gje_c3_quadratic_remainder` for the higher-order contribution. -/
theorem gje_c3_eq_linear_plus_quadratic_remainder_term
    (fp : FPModel) (n : ℕ) (h3 : gammaValid fp 3) :
    gje_c₃ fp n =
      3 * ((n : ℝ) - 1) * fp.u + gje_c3_quadratic_remainder fp n := by
  simpa [gje_c3_quadratic_remainder] using
    gje_c3_eq_linear_plus_quadratic_remainder fp n h3

/-- Theorem 14.5 scalar support: the GJE `c₃` coefficient is bounded by the
    source-facing `3 n u` first-order term plus the existing explicit
    higher-order remainder. -/
theorem gje_c3_le_three_n_u_plus_quadratic_remainder
    (fp : FPModel) (n : ℕ) (h3 : gammaValid fp 3) :
    gje_c₃ fp n ≤
      3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n := by
  rw [gje_c3_eq_linear_plus_quadratic_remainder_term fp n h3]
  nlinarith [fp.u_nonneg]

/-- Higham, 2nd ed., Chapter 14, Theorem 14.5 support:
    the GJE cumulative coefficient `c₃ = (n-1) γ₃ (1+γ₃)^(n-2)` is
    nonnegative under the usual dimension and gamma-validity side conditions. -/
theorem gje_c3_nonneg (fp : FPModel) (n : ℕ)
    (hn : 1 ≤ n) (h3 : gammaValid fp 3) :
    0 ≤ gje_c₃ fp n := by
  have hgamma : 0 ≤ gamma fp 3 := gamma_nonneg fp h3
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hnminus : 0 ≤ (n : ℝ) - 1 := by
    rw [← hcast]
    exact Nat.cast_nonneg _
  have hbase : 0 ≤ 1 + gamma fp 3 := by linarith
  have hpow : 0 ≤ (1 + gamma fp 3) ^ (n - 2) := pow_nonneg hbase _
  unfold gje_c₃
  exact mul_nonneg (mul_nonneg hnminus hgamma) hpow

/-- Elementary scalar growth bound used to connect the exact constant
    product envelope `(1 + c)^steps - 1` to Higham's `c₃`-style coefficient. -/
theorem gje_one_add_pow_sub_one_le_nat_mul_pred {c : ℝ} (hc : 0 ≤ c) :
    ∀ steps : ℕ,
      (1 + c) ^ steps - 1 ≤ (steps : ℝ) * c * (1 + c) ^ (steps - 1) := by
  intro steps
  induction steps with
  | zero =>
      simp
  | succ k ih =>
      cases k with
      | zero =>
          ring_nf
          exact le_rfl
      | succ m =>
          have hbase_nonneg : 0 ≤ 1 + c := by linarith
          have hbase_one : (1 : ℝ) ≤ 1 + c := by linarith
          have hpow_ge_one : (1 : ℝ) ≤ (1 + c) ^ (m + 1) :=
            one_le_pow₀ hbase_one
          have hmul := mul_le_mul_of_nonneg_right ih hbase_nonneg
          have hc_le : c ≤ c * (1 + c) ^ (m + 1) := by
            calc
              c = c * 1 := by ring
              _ ≤ c * (1 + c) ^ (m + 1) :=
                mul_le_mul_of_nonneg_left hpow_ge_one hc
          calc
            (1 + c) ^ (Nat.succ (Nat.succ m)) - 1 =
                (1 + c) ^ (m + 1) * (1 + c) - 1 := by
              rw [show Nat.succ (Nat.succ m) = (m + 1) + 1 by omega, pow_succ]
            _ = ((1 + c) ^ (m + 1) - 1) * (1 + c) + c := by
              ring
            _ ≤ ((m + 1 : ℕ) : ℝ) * c * (1 + c) ^ ((m + 1) - 1) *
                  (1 + c) + c := by
              exact add_le_add hmul (le_refl c)
            _ = ((m + 1 : ℕ) : ℝ) * c * ((1 + c) ^ m * (1 + c)) + c := by
              rw [show (m + 1 : ℕ) - 1 = m by omega]
              ring
            _ = ((m + 1 : ℕ) : ℝ) * c * (1 + c) ^ (m + 1) + c := by
              rw [pow_succ]
            _ ≤ ((m + 1 : ℕ) : ℝ) * c * (1 + c) ^ (m + 1) +
                  c * (1 + c) ^ (m + 1) := by
              exact add_le_add (le_refl _) hc_le
            _ = ((Nat.succ (Nat.succ m) : ℕ) : ℝ) * c *
                  (1 + c) ^ (Nat.succ (Nat.succ m) - 1) := by
              rw [show Nat.succ (Nat.succ m) - 1 = m + 1 by omega]
              norm_num [Nat.cast_add, Nat.cast_one]
              ring

/-- Chapter 14 scalar bridge: the constant GJE product envelope with
    `eta = gamma fp 3` is bounded by the file's `gje_c₃ fp n` coefficient. -/
theorem gje_one_add_gamma_three_pow_sub_one_le_c3 (fp : FPModel) (n : ℕ)
    (hn : 1 ≤ n) (hvalid : gammaValid fp 3) :
    (1 + gamma fp 3) ^ (n - 1) - 1 ≤ gje_c₃ fp n := by
  have hgamma : 0 ≤ gamma fp 3 := gamma_nonneg fp hvalid
  have h := gje_one_add_pow_sub_one_le_nat_mul_pred hgamma (n - 1)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hexp : (n - 1) - 1 = n - 2 := by omega
  simpa [gje_c₃, hcast, hexp] using h

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.1  GJE Second Stage: Specification
-- ══════════════════════════════════════════════════════════════════════

/-- **GJE second-stage Nₖ matrix specification**.

    The second stage of GJE applies matrices N₂, N₃, …, Nₙ to reduce
    the upper triangular factor U to diagonal form.
    Each Nₖ has the form Nₖ = I − nₖeₖᵀ where nₖ has zeros
    in positions k through n (i.e., the entries below the diagonal). -/
structure GJEStage2Spec (n : ℕ) (U : Fin n → Fin n → ℝ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) : Prop where
  /-- Each N̂ₖ has the Nₖ-structure: N̂ₖ = I − n̂ₖeₖᵀ. -/
  N_form : ∀ k : Fin n, ∀ i j : Fin n,
    N_hat k i j = (if i = j then 1 else 0) -
      (if j = k then N_hat k i k else 0)
  /-- The diagonal of N̂ₖ at position k is 1 (since (Nₖ)ₖₖ = 1 − nₖₖ and
      nₖₖ = 0 for the second stage). -/
  diag_one : ∀ k : Fin n, N_hat k k k = 1
  /-- Entries at or below k in column k are zero (nₖᵢ = 0 for i ≥ k). -/
  lower_zero : ∀ k : Fin n, ∀ i : Fin n,
    i.val ≥ k.val → i ≠ k → N_hat k i k = 0

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.2  Error Recurrences (eqs. 14.25–14.26)
-- ══════════════════════════════════════════════════════════════════════

/-- **Abstract Eq. 14.25a interface**: matrix recurrence error bound for
    the GJE second stage.

    At each step k, the computed upper triangular factor satisfies:
      Û_{k+1} = N̂ₖÛₖ + Δₖ  with  |Δₖ| ≤ γ₃|N̂ₖ||Ûₖ|.

    The γ₃ constant arises because each element of N̂ₖÛₖ involves
    at most 3 arithmetic operations (multiply, add, subtract).  The hypothesis
    `hComp` supplies that local rounded-computation analysis. -/
theorem gje_stage2_matrix_recurrence (n : ℕ) (fp : FPModel)
    (U_k N_k U_next : Fin n → Fin n → ℝ)
    (_hn : gammaValid fp 3)
    -- N̂ₖÛₖ is computed with rounding errors bounded by γ₃
    (hComp : ∀ i j : Fin n,
      |U_next i j - ∑ l : Fin n, N_k i l * U_k l j| ≤
      gamma fp 3 * ∑ l : Fin n, |N_k i l| * |U_k l j|) :
    ∀ i j : Fin n,
      |U_next i j - ∑ l : Fin n, N_k i l * U_k l j| ≤
      gamma fp 3 * ∑ l : Fin n, |N_k i l| * |U_k l j| :=
  hComp

/-- **Abstract Eq. 14.26 interface**: RHS recurrence error bound for the
    GJE second stage.

    The computed right-hand side satisfies:
      x̂_{k+1} = N̂ₖx̂ₖ + fₖ  with  |fₖ| ≤ γ₃|N̂ₖ||x̂ₖ|.

    Same γ₃ constant as the matrix recurrence.  The hypothesis `hComp`
    supplies the local rounded-computation analysis. -/
theorem gje_stage2_rhs_recurrence (n : ℕ) (fp : FPModel)
    (x_k : Fin n → ℝ) (N_k : Fin n → Fin n → ℝ)
    (x_next : Fin n → ℝ)
    (_hn : gammaValid fp 3)
    (hComp : ∀ i : Fin n,
      |x_next i - ∑ l : Fin n, N_k i l * x_k l| ≤
      gamma fp 3 * ∑ l : Fin n, |N_k i l| * |x_k l|) :
    ∀ i : Fin n,
      |x_next i - ∑ l : Fin n, N_k i l * x_k l| ≤
      gamma fp 3 * ∑ l : Fin n, |N_k i l| * |x_k l| :=
  hComp

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.3  Cumulative Product (eqs. 14.27–14.28)
-- ══════════════════════════════════════════════════════════════════════

/-- **Cumulative product of N̂ matrices** for the GJE second stage.

    gje_cumulative_product n N̂ start finish = N̂_{finish-1} · ⋯ · N̂_{start},
    or I if finish ≤ start.

    This represents the product of N̂ₖ matrices applied in the second stage
    of Gauss–Jordan elimination. -/
noncomputable def gje_cumulative_product (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ)
    (start finish_ : ℕ) : Fin n → Fin n → ℝ :=
  if finish_ ≤ start then fun i j => if i = j then 1 else 0
  else if h : finish_ - 1 < n then
    let prev := gje_cumulative_product n N_hat start (finish_ - 1)
    fun i j => ∑ k : Fin n, N_hat ⟨finish_ - 1, h⟩ i k * prev k j
  else fun i j => if i = j then 1 else 0
termination_by finish_ - start

/-- Equation (14.27) base case for the GJE cumulative product:
    an empty stage range is the identity. -/
theorem gje_cumulative_product_base (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) {start finish_ : ℕ}
    (hfinish : finish_ ≤ start) :
    gje_cumulative_product n N_hat start finish_ = idMatrix n := by
  conv_lhs => unfold gje_cumulative_product
  ext i j
  simp [hfinish, idMatrix]

/-- Equation (14.27) step case for the GJE cumulative product:
    when the stage index `finish - 1` is valid, the product is obtained by
    multiplying that stage on the left of the previous cumulative product. -/
theorem gje_cumulative_product_step (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) {start finish_ : ℕ}
    (hstep : start < finish_) (hidx : finish_ - 1 < n) :
    gje_cumulative_product n N_hat start finish_ =
      matMul n (N_hat ⟨finish_ - 1, hidx⟩)
        (gje_cumulative_product n N_hat start (finish_ - 1)) := by
  conv_lhs => unfold gje_cumulative_product
  ext i j
  simp [not_le_of_gt hstep, hidx, matMul]

/-- Out-of-range guard for the cumulative product: if the requested stage
    `finish - 1` is not a valid `Fin n` index, the definition returns the
    identity.  This keeps the total function honest outside the source range. -/
theorem gje_cumulative_product_oob (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) {start finish_ : ℕ}
    (hstep : start < finish_) (hidx : ¬ finish_ - 1 < n) :
    gje_cumulative_product n N_hat start finish_ = idMatrix n := by
  conv_lhs => unfold gje_cumulative_product
  ext i j
  simp [not_le_of_gt hstep, hidx, idMatrix]

/-- Entrywise nonnegative stage matrices have entrywise nonnegative GJE
    cumulative products.  This is the basic monotonicity fact needed before
    turning (14.27)--(14.28) into componentwise absolute-value bounds. -/
theorem gje_cumulative_product_nonneg (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ)
    (hN : ∀ k i j : Fin n, 0 ≤ N_hat k i j) :
    ∀ start finish_ : ℕ, ∀ i j : Fin n,
      0 ≤ gje_cumulative_product n N_hat start finish_ i j := by
  intro start finish_
  induction finish_ using Nat.strong_induction_on generalizing start with
  | h finish_ ih =>
      intro i j
      by_cases hfinish : finish_ ≤ start
      · rw [gje_cumulative_product_base n N_hat hfinish]
        simp [idMatrix]
        split <;> norm_num
      · by_cases hidx : finish_ - 1 < n
        · have hstep : start < finish_ := lt_of_not_ge hfinish
          have hfinish_ne : finish_ ≠ 0 :=
            Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le start) hstep)
          rw [gje_cumulative_product_step n N_hat hstep hidx]
          simp [matMul]
          exact Finset.sum_nonneg fun k _ =>
            mul_nonneg (hN ⟨finish_ - 1, hidx⟩ i k)
              (ih (finish_ - 1) (Nat.sub_one_lt hfinish_ne) start k j)
        · have hstep : start < finish_ := lt_of_not_ge hfinish
          rw [gje_cumulative_product_oob n N_hat hstep hidx]
          simp [idMatrix]
          split <;> norm_num

/-- The absolute-value stage matrices used in the GJE error bounds have
    nonnegative cumulative products. -/
theorem gje_cumulative_product_abs_nonneg (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ) :
    ∀ start finish_ : ℕ, ∀ i j : Fin n,
      0 ≤ gje_cumulative_product n
        (fun k i j => |N_hat k i j|) start finish_ i j :=
  gje_cumulative_product_nonneg n
    (fun k i j => |N_hat k i j|)
    (fun _ _ _ => abs_nonneg _)

/-- The GJE cumulative product over a valid `steps`-long range is the generic
    matrix sequence product of the same stages in reverse order.  This bridge
    lets the generic product-perturbation lemmas in `MatrixAlgebra` feed the
    source-shaped GJE cumulative product used in (14.27)--(14.30). -/
theorem gje_cumulative_product_eq_matSeqProd_rev (n : Nat)
    (N_hat : Fin n -> Fin n -> Fin n -> Real)
    (start steps : Nat)
    (hidx : forall r : Fin steps, start + (steps - 1 - r.val) < n) :
    gje_cumulative_product n N_hat start (start + steps) =
      matSeqProd n steps (fun r : Fin steps =>
        let k : Fin n := Fin.mk (start + (steps - 1 - r.val)) (hidx r);
        N_hat k) := by
  induction steps with
  | zero =>
      rw [Nat.add_zero]
      rw [gje_cumulative_product_base n N_hat (le_refl start)]
      simp [matSeqProd]
  | succ m ih =>
      have htop : start + m < n := by
        simpa using hidx 0
      have hstep : start < start + (m + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos m)
      have hfinish_idx : start + (m + 1) - 1 < n := by
        simpa [Nat.add_assoc] using htop
      have hprev_idx : forall r : Fin m, start + (m - 1 - r.val) < n := by
        intro r
        have hr := hidx r.succ
        have heq : m - (r.val + 1) = m - 1 - r.val := by
          rw [Nat.sub_sub, Nat.add_comm]
        simpa [Nat.succ_eq_add_one, heq] using hr
      have hfin : (Fin.mk (start + (m + 1) - 1) hfinish_idx : Fin n) =
          Fin.mk (start + m) htop := by
        apply Fin.ext
        simp
      have hcp_prev :
          gje_cumulative_product n N_hat start (start + (m + 1) - 1) =
            gje_cumulative_product n N_hat start (start + m) := by
        simp
      rw [gje_cumulative_product_step n N_hat hstep hfinish_idx]
      rw [hfin, hcp_prev]
      rw [ih hprev_idx]
      simp [matSeqProd, Nat.sub_sub, Nat.add_comm]

/-- Componentwise perturbation bound for GJE cumulative products, obtained by
    transporting the generic `matSeqProd_componentwise_perturbation_bound`
    through `gje_cumulative_product_eq_matSeqProd_rev`. -/
theorem gje_cumulative_product_componentwise_perturbation_bound (n : Nat)
    (N_hat DeltaN : Fin n -> Fin n -> Fin n -> Real)
    (start steps : Nat) (delta : Fin steps -> Real)
    (hidx : forall r : Fin steps, start + (steps - 1 - r.val) < n)
    (hdelta : forall r : Fin steps, 0 <= delta r)
    (hDelta : forall r : Fin steps, forall i j : Fin n,
      |DeltaN (Fin.mk (start + (steps - 1 - r.val)) (hidx r)) i j| <=
        delta r * |N_hat (Fin.mk (start + (steps - 1 - r.val)) (hidx r)) i j|)
    (i j : Fin n) :
    |gje_cumulative_product n (fun k i j => N_hat k i j + DeltaN k i j)
        start (start + steps) i j -
      gje_cumulative_product n N_hat start (start + steps) i j| <=
      ((scalarSeqProd steps fun r => 1 + delta r) - 1) *
        gje_cumulative_product n (fun k i j => |N_hat k i j|)
          start (start + steps) i j := by
  let X : Fin steps -> Fin n -> Fin n -> Real := fun r =>
    N_hat (Fin.mk (start + (steps - 1 - r.val)) (hidx r))
  let DX : Fin steps -> Fin n -> Fin n -> Real := fun r =>
    DeltaN (Fin.mk (start + (steps - 1 - r.val)) (hidx r))
  have hDelta' : forall r : Fin steps, forall i j : Fin n,
      |DX r i j| <= delta r * |X r i j| := by
    intro r i j
    simpa [X, DX] using hDelta r i j
  have hbound :=
    matSeqProd_componentwise_perturbation_bound n steps X DX delta
      hdelta hDelta' i j
  have hpert := gje_cumulative_product_eq_matSeqProd_rev n
    (fun k i j => N_hat k i j + DeltaN k i j) start steps hidx
  have hbase := gje_cumulative_product_eq_matSeqProd_rev n N_hat start steps hidx
  have habs := gje_cumulative_product_eq_matSeqProd_rev n
    (fun k i j => |N_hat k i j|) start steps hidx
  rw [hpert, hbase, habs]
  simpa [X, DX, absMatrix] using hbound

/-- Constant per-stage scalar product for the GJE product-error envelope. -/
theorem gje_scalarSeqProd_const (steps : Nat) (eta : Real) :
    scalarSeqProd steps (fun _ : Fin steps => 1 + eta) =
      (1 + eta) ^ steps := by
  induction steps with
  | zero =>
      simp [scalarSeqProd]
  | succ m ih =>
      simp [scalarSeqProd, ih, pow_succ, mul_comm]

/-- Constant-error specialization of
    `gje_cumulative_product_componentwise_perturbation_bound`, with the
    scalar envelope in the source-shaped form `(1 + eta)^steps - 1`. -/
theorem gje_cumulative_product_componentwise_perturbation_bound_const (n : Nat)
    (N_hat DeltaN : Fin n -> Fin n -> Fin n -> Real)
    (start steps : Nat) (eta : Real)
    (hidx : forall r : Fin steps, start + (steps - 1 - r.val) < n)
    (heta : 0 <= eta)
    (hDelta : forall r : Fin steps, forall i j : Fin n,
      |DeltaN (Fin.mk (start + (steps - 1 - r.val)) (hidx r)) i j| <=
        eta * |N_hat (Fin.mk (start + (steps - 1 - r.val)) (hidx r)) i j|)
    (i j : Fin n) :
    |gje_cumulative_product n (fun k i j => N_hat k i j + DeltaN k i j)
        start (start + steps) i j -
      gje_cumulative_product n N_hat start (start + steps) i j| <=
      ((1 + eta) ^ steps - 1) *
        gje_cumulative_product n (fun k i j => |N_hat k i j|)
          start (start + steps) i j := by
  have h := gje_cumulative_product_componentwise_perturbation_bound n
    N_hat DeltaN start steps (fun _ : Fin steps => eta) hidx
    (fun _ => heta) hDelta i j
  simpa [gje_scalarSeqProd_const] using h

/-- Source-shaped constant-error GJE product perturbation bound with the
    accumulated scalar envelope absorbed into `gje_c₃ fp n`. -/
theorem gje_cumulative_product_componentwise_perturbation_bound_gamma_c3
    (n : Nat) (fp : FPModel)
    (N_hat DeltaN : Fin n -> Fin n -> Fin n -> Real)
    (start : Nat)
    (hn : 1 <= n) (hvalid : gammaValid fp 3)
    (hidx : forall r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : forall r : Fin (n - 1), forall i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| <=
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (i j : Fin n) :
    |gje_cumulative_product n (fun k i j => N_hat k i j + DeltaN k i j)
        start (start + (n - 1)) i j -
      gje_cumulative_product n N_hat start (start + (n - 1)) i j| <=
      gje_c₃ fp n *
        gje_cumulative_product n (fun k i j => |N_hat k i j|)
          start (start + (n - 1)) i j := by
  have hconst :=
    gje_cumulative_product_componentwise_perturbation_bound_const n
      N_hat DeltaN start (n - 1) (gamma fp 3) hidx
      (gamma_nonneg fp hvalid) hDelta i j
  have hscalar := gje_one_add_gamma_three_pow_sub_one_le_c3 fp n hn hvalid
  have hprod_nonneg :
      0 <= gje_cumulative_product n (fun k i j => |N_hat k i j|)
        start (start + (n - 1)) i j :=
    gje_cumulative_product_abs_nonneg n N_hat start (start + (n - 1)) i j
  exact le_trans hconst (mul_le_mul_of_nonneg_right hscalar hprod_nonneg)

/-- Vector-applied form of the Chapter 14 GJE cumulative-product perturbation
    bound.  This is the matrix-vector bridge needed by the right-hand-side
    accumulation in the route to equation (14.29): the existing entrywise
    product perturbation theorem is pushed through multiplication by a fixed
    right-hand side. -/
theorem gje_cumulative_product_matMulVec_componentwise_perturbation_bound_gamma_c3
    (n : Nat) (fp : FPModel)
    (N_hat DeltaN : Fin n -> Fin n -> Fin n -> Real)
    (start : Nat) (rhs : Fin n -> Real)
    (hn : 1 <= n) (hvalid : gammaValid fp 3)
    (hidx : forall r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : forall r : Fin (n - 1), forall i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| <=
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (i : Fin n) :
    |matMulVec n
        (gje_cumulative_product n (fun k a b => N_hat k a b + DeltaN k a b)
          start (start + (n - 1))) rhs i -
      matMulVec n
        (gje_cumulative_product n N_hat start (start + (n - 1))) rhs i| <=
      gje_c₃ fp n *
        ∑ j : Fin n,
          gje_cumulative_product n (fun k a b => |N_hat k a b|)
            start (start + (n - 1)) i j * |rhs j| := by
  let Pδ : Fin n -> Fin n -> Real :=
    gje_cumulative_product n (fun k a b => N_hat k a b + DeltaN k a b)
      start (start + (n - 1))
  let P : Fin n -> Fin n -> Real :=
    gje_cumulative_product n N_hat start (start + (n - 1))
  let Pabs : Fin n -> Fin n -> Real :=
    gje_cumulative_product n (fun k a b => |N_hat k a b|)
      start (start + (n - 1))
  have hentry : forall j : Fin n,
      |Pδ i j - P i j| <= gje_c₃ fp n * Pabs i j := by
    intro j
    simpa [Pδ, P, Pabs] using
      gje_cumulative_product_componentwise_perturbation_bound_gamma_c3
        n fp N_hat DeltaN start hn hvalid hidx hDelta i j
  change |matMulVec n Pδ rhs i - matMulVec n P rhs i| <=
    gje_c₃ fp n * ∑ j : Fin n, Pabs i j * |rhs j|
  change |(∑ j : Fin n, Pδ i j * rhs j) -
      (∑ j : Fin n, P i j * rhs j)| <=
    gje_c₃ fp n * ∑ j : Fin n, Pabs i j * |rhs j|
  have hdiff :
      (∑ j : Fin n, Pδ i j * rhs j) -
          (∑ j : Fin n, P i j * rhs j) =
        ∑ j : Fin n, (Pδ i j - P i j) * rhs j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdiff]
  calc
    |∑ j : Fin n, (Pδ i j - P i j) * rhs j|
        <= ∑ j : Fin n, |(Pδ i j - P i j) * rhs j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |Pδ i j - P i j| * |rhs j| := by
          apply Finset.sum_congr rfl
          intro j _
          exact abs_mul _ _
    _ <= ∑ j : Fin n, (gje_c₃ fp n * Pabs i j) * |rhs j| := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hentry j) (abs_nonneg _)
    _ = gje_c₃ fp n * ∑ j : Fin n, Pabs i j * |rhs j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- Matrix-applied form of the Chapter 14 GJE cumulative-product perturbation
    bound.  This is the fixed-right-matrix bridge needed by the matrix side of
    equation (14.30): the entrywise product perturbation theorem is pushed
    through multiplication by the current upper-triangular factor. -/
theorem gje_cumulative_product_matMul_componentwise_perturbation_bound_gamma_c3
    (n : Nat) (fp : FPModel)
    (N_hat DeltaN : Fin n -> Fin n -> Fin n -> Real)
    (start : Nat) (rhs : Fin n -> Fin n -> Real)
    (hn : 1 <= n) (hvalid : gammaValid fp 3)
    (hidx : forall r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : forall r : Fin (n - 1), forall i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| <=
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (i j : Fin n) :
    |matMul n
        (gje_cumulative_product n (fun k a b => N_hat k a b + DeltaN k a b)
          start (start + (n - 1))) rhs i j -
      matMul n
        (gje_cumulative_product n N_hat start (start + (n - 1))) rhs i j| <=
      gje_c₃ fp n *
        ∑ k : Fin n,
          gje_cumulative_product n (fun s a b => |N_hat s a b|)
            start (start + (n - 1)) i k * |rhs k j| := by
  let Pdelta : Fin n -> Fin n -> Real :=
    gje_cumulative_product n (fun k a b => N_hat k a b + DeltaN k a b)
      start (start + (n - 1))
  let P : Fin n -> Fin n -> Real :=
    gje_cumulative_product n N_hat start (start + (n - 1))
  let Pabs : Fin n -> Fin n -> Real :=
    gje_cumulative_product n (fun k a b => |N_hat k a b|)
      start (start + (n - 1))
  have hentry : forall k : Fin n,
      |Pdelta i k - P i k| <= gje_c₃ fp n * Pabs i k := by
    intro k
    simpa [Pdelta, P, Pabs] using
      gje_cumulative_product_componentwise_perturbation_bound_gamma_c3
        n fp N_hat DeltaN start hn hvalid hidx hDelta i k
  change |matMul n Pdelta rhs i j - matMul n P rhs i j| <=
    gje_c₃ fp n * ∑ k : Fin n, Pabs i k * |rhs k j|
  change |(∑ k : Fin n, Pdelta i k * rhs k j) -
      (∑ k : Fin n, P i k * rhs k j)| <=
    gje_c₃ fp n * ∑ k : Fin n, Pabs i k * |rhs k j|
  have hdiff :
      (∑ k : Fin n, Pdelta i k * rhs k j) -
          (∑ k : Fin n, P i k * rhs k j) =
        ∑ k : Fin n, (Pdelta i k - P i k) * rhs k j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hdiff]
  calc
    |∑ k : Fin n, (Pdelta i k - P i k) * rhs k j|
        <= ∑ k : Fin n, |(Pdelta i k - P i k) * rhs k j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |Pdelta i k - P i k| * |rhs k j| := by
          apply Finset.sum_congr rfl
          intro k _
          exact abs_mul _ _
    _ <= ∑ k : Fin n, (gje_c₃ fp n * Pabs i k) * |rhs k j| := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_right (hentry k) (abs_nonneg _)
    _ = gje_c₃ fp n * ∑ k : Fin n, Pabs i k * |rhs k j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring

/-- Equation (14.27) accumulation algebra for the GJE second-stage matrix
    recurrence.  If the exact stage matrices obey
    `U_{start+t+1} = N_{start+t} U_{start+t}` for `steps` valid stages, then
    the last stage is the cumulative product times the initial stage. -/
theorem gje_cumulative_product_matrix_accumulation (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ)
    (U_stage : ℕ → Fin n → Fin n → ℝ)
    (start steps : ℕ)
    (hidx : ∀ t : ℕ, t < steps → start + t < n)
    (hrec : ∀ t : ℕ, (ht : t < steps) →
      U_stage (start + (t + 1)) =
        matMul n (N_hat ⟨start + t, hidx t ht⟩) (U_stage (start + t))) :
    U_stage (start + steps) =
      matMul n (gje_cumulative_product n N_hat start (start + steps))
        (U_stage start) := by
  induction steps with
  | zero =>
      simp
      rw [gje_cumulative_product_base n N_hat (le_refl start), matMul_id_left]
  | succ steps ih =>
      have hidx_prev : ∀ t : ℕ, t < steps → start + t < n := by
        intro t ht
        exact hidx t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have hrec_prev : ∀ t : ℕ, (ht : t < steps) →
          U_stage (start + (t + 1)) =
            matMul n (N_hat ⟨start + t, hidx_prev t ht⟩)
              (U_stage (start + t)) := by
        intro t ht
        simpa [hidx_prev] using hrec t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have ih' := ih hidx_prev hrec_prev
      have hstage := hrec steps (Nat.lt_succ_self steps)
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfinish_eq : start + (steps + 1) - 1 = start + steps := by
        simp
      have hfinish_idx : start + (steps + 1) - 1 < n := by
        simpa [hfinish_eq] using hidx steps (Nat.lt_succ_self steps)
      have hfin : (⟨start + (steps + 1) - 1, hfinish_idx⟩ : Fin n) =
          ⟨start + steps, hidx steps (Nat.lt_succ_self steps)⟩ := by
        apply Fin.ext
        simp
      have hcp_prev :
          gje_cumulative_product n N_hat start (start + (steps + 1) - 1) =
            gje_cumulative_product n N_hat start (start + steps) := by
        rw [hfinish_eq]
      have hcp := gje_cumulative_product_step n N_hat hstep hfinish_idx
      rw [hstage, ih', hcp, hfin, hcp_prev, matMul_assoc]

/-- Equation (14.28) accumulation algebra for the GJE second-stage right-hand
    side recurrence.  If the exact stage vectors obey
    `x_{start+t+1} = N_{start+t} x_{start+t}` for `steps` valid stages, then
    the last vector is the cumulative product applied to the initial vector. -/
theorem gje_cumulative_product_rhs_accumulation (n : ℕ)
    (N_hat : Fin n → Fin n → Fin n → ℝ)
    (x_stage : ℕ → Fin n → ℝ)
    (start steps : ℕ)
    (hidx : ∀ t : ℕ, t < steps → start + t < n)
    (hrec : ∀ t : ℕ, (ht : t < steps) →
      x_stage (start + (t + 1)) =
        matMulVec n (N_hat ⟨start + t, hidx t ht⟩) (x_stage (start + t))) :
    x_stage (start + steps) =
      matMulVec n (gje_cumulative_product n N_hat start (start + steps))
        (x_stage start) := by
  induction steps with
  | zero =>
      simp
      rw [gje_cumulative_product_base n N_hat (le_refl start), matMulVec_id]
  | succ steps ih =>
      have hidx_prev : ∀ t : ℕ, t < steps → start + t < n := by
        intro t ht
        exact hidx t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have hrec_prev : ∀ t : ℕ, (ht : t < steps) →
          x_stage (start + (t + 1)) =
            matMulVec n (N_hat ⟨start + t, hidx_prev t ht⟩)
              (x_stage (start + t)) := by
        intro t ht
        simpa [hidx_prev] using hrec t (Nat.lt_trans ht (Nat.lt_succ_self steps))
      have ih' := ih hidx_prev hrec_prev
      have hstage := hrec steps (Nat.lt_succ_self steps)
      have hstep : start < start + (steps + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos steps)
      have hfinish_eq : start + (steps + 1) - 1 = start + steps := by
        simp
      have hfinish_idx : start + (steps + 1) - 1 < n := by
        simpa [hfinish_eq] using hidx steps (Nat.lt_succ_self steps)
      have hfin : (⟨start + (steps + 1) - 1, hfinish_idx⟩ : Fin n) =
          ⟨start + steps, hidx steps (Nat.lt_succ_self steps)⟩ := by
        apply Fin.ext
        simp
      have hcp_prev :
          gje_cumulative_product n N_hat start (start + (steps + 1) - 1) =
            gje_cumulative_product n N_hat start (start + steps) := by
        rw [hfinish_eq]
      have hcp := gje_cumulative_product_step n N_hat hstep hfinish_idx
      rw [hstage, ih', hcp, hfin, hcp_prev]
      ext i
      exact (matMulVec_matMul n
        (N_hat ⟨start + steps, hidx steps (Nat.lt_succ_self steps)⟩)
        (gje_cumulative_product n N_hat start (start + steps))
        (x_stage start) i).symm

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.4  Forward Error (eq. 14.29)
-- ══════════════════════════════════════════════════════════════════════

/-- **Abstract Eq. 14.29 interface**: forward error bound for the GJE
    second stage.

    The componentwise forward error for the second stage satisfies:
      |x − x̂| ≤ (n−1)γ₃(1+γ₃)^{n−2} · |X̂| · (|U||x| + |y|)

    where X̂ = |N̂ₙ|···|N̂₂| is the absolute cumulative product of N̂ matrices
    and y is the first-stage output.  The hypothesis `hErr` supplies the
    second-stage accumulation proof. -/
theorem gje_stage2_forward_error_bound (n : ℕ) (fp : FPModel)
    (U : Fin n → Fin n → ℝ) (y x x_hat : Fin n → ℝ)
    (X_abs : Fin n → Fin n → ℝ)
    (_hn3 : gammaValid fp 3)
    -- U is upper triangular with nonzero diagonal
    (_hU_diag : ∀ i : Fin n, U i i ≠ 0)
    -- x is the exact solution of Ux = y
    (_hExact : ∀ i : Fin n, ∑ j : Fin n, U i j * x j = y i)
    -- x̂ is the GJE-computed solution with total second-stage error
    (hErr : ∀ i : Fin n,
      |x i - x_hat i| ≤
      gje_c₃ fp n *
        ∑ j : Fin n, |X_abs i j| * (∑ k : Fin n, |U j k| * |x k| + |y j|)) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      gje_c₃ fp n *
        ∑ j : Fin n, |X_abs i j| * (∑ k : Fin n, |U j k| * |x k| + |y j|) :=
  hErr

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.5  Backward Error (eq. 14.30)
-- ══════════════════════════════════════════════════════════════════════

/-- **Abstract Eq. 14.30 interface**: GJE second-stage backward error.

    The computed solution x̂ of Ux = y satisfies:
      (U + ΔU)x̂ = y + Δy
    with componentwise bounds (eqs. 14.30b–c):
      |ΔU| ≤ (n−1)γ₃(1+γ₃)^{n−2} · |X̂| · |U|
      |Δy| ≤ (n−1)γ₃(1+γ₃)^{n−2} · |X̂| · |y|

    where X̂ = |N̂ₙ|···|N̂₂| is the absolute cumulative product.  The
    existential hypothesis `hBackward` supplies the second-stage backward
    analysis used by the overall GJE theorem below. -/
theorem gje_stage2_backward_error (n : ℕ) (fp : FPModel)
    (U : Fin n → Fin n → ℝ) (y x_hat : Fin n → ℝ)
    (X_abs : Fin n → Fin n → ℝ)
    (_hn : gammaValid fp 3)
    (_hU_diag : ∀ i : Fin n, U i i ≠ 0)
    -- Backward error hypothesis: there exist ΔU, Δy such that
    -- (U + ΔU)x̂ = y + Δy with the stated bounds
    (hBackward : ∃ (ΔU : Fin n → Fin n → ℝ) (Δy : Fin n → ℝ),
      (∀ i : Fin n, ∑ j : Fin n, (U i j + ΔU i j) * x_hat j = y i + Δy i) ∧
      (∀ i j : Fin n, |ΔU i j| ≤
        gje_c₃ fp n * ∑ k : Fin n, |X_abs i k| * |U k j|) ∧
      (∀ i : Fin n, |Δy i| ≤
        gje_c₃ fp n * ∑ j : Fin n, |X_abs i j| * |y j|)) :
    ∃ (ΔU : Fin n → Fin n → ℝ) (Δy : Fin n → ℝ),
      (∀ i : Fin n, ∑ j : Fin n, (U i j + ΔU i j) * x_hat j = y i + Δy i) ∧
      (∀ i j : Fin n, |ΔU i j| ≤
        gje_c₃ fp n * ∑ k : Fin n, |X_abs i k| * |U k j|) ∧
      (∀ i : Fin n, |Δy i| ≤
        gje_c₃ fp n * ∑ j : Fin n, |X_abs i j| * |y j|) :=
  hBackward

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.6  Theorem 14.5: Overall GJE Error (eqs. 14.31–14.32)
-- ══════════════════════════════════════════════════════════════════════

/-- **Equation 14.30, cumulative-product certificate route.**

    This source-facing wrapper removes the final componentwise bound
    hypotheses from `gje_stage2_backward_error`: once the per-stage
    perturbations of the GJE second-stage matrices are bounded by `γ₃`, the
    cumulative-product matrix and right-hand-side perturbation bridges provide
    the componentwise bounds (14.30b)--(14.30c).  The exact backward equation
    (14.30a) remains an explicit recurrence-instantiation hypothesis. -/
theorem gje_stage2_backward_error_of_cumulative_product_certificates
    (n : ℕ) (fp : FPModel)
    (U : Fin n → Fin n → ℝ) (y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hn : 1 ≤ n) (hvalid : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1))) U i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∃ (DeltaU : Fin n → Fin n → ℝ) (Deltay : Fin n → ℝ),
      (∀ i : Fin n, ∑ j : Fin n, (U i j + DeltaU i j) * x_hat j =
        y i + Deltay i) ∧
      (∀ i j : Fin n, |DeltaU i j| ≤
        gje_c₃ fp n * ∑ k : Fin n,
          |gje_cumulative_product n (fun s a b => |N_hat s a b|)
            start (start + (n - 1)) i k| * |U k j|) ∧
      (∀ i : Fin n, |Deltay i| ≤
        gje_c₃ fp n * ∑ j : Fin n,
          |gje_cumulative_product n (fun s a b => |N_hat s a b|)
            start (start + (n - 1)) i j| * |y j|) := by
  let Pdelta : Fin n → Fin n → ℝ :=
    gje_cumulative_product n
      (fun k a b => N_hat k a b + DeltaN k a b)
      start (start + (n - 1))
  let P : Fin n → Fin n → ℝ :=
    gje_cumulative_product n N_hat start (start + (n - 1))
  let Pabs : Fin n → Fin n → ℝ :=
    gje_cumulative_product n (fun s a b => |N_hat s a b|)
      start (start + (n - 1))
  let DeltaU : Fin n → Fin n → ℝ := fun i j =>
    matMul n Pdelta U i j - matMul n P U i j
  let Deltay : Fin n → ℝ := fun i =>
    matMulVec n Pdelta y i - matMulVec n P y i
  refine ⟨DeltaU, Deltay, ?_, ?_, ?_⟩
  · intro i
    simpa [DeltaU, Deltay, Pdelta, P] using hBackwardEq i
  · intro i j
    change |DeltaU i j| ≤
      gje_c₃ fp n * ∑ k : Fin n, |Pabs i k| * |U k j|
    have hPabs_nonneg : ∀ a b : Fin n, 0 ≤ Pabs a b := by
      intro a b
      simpa [Pabs] using
        gje_cumulative_product_abs_nonneg n N_hat start (start + (n - 1)) a b
    have hBridge : |DeltaU i j| ≤
        gje_c₃ fp n * ∑ k : Fin n, Pabs i k * |U k j| := by
      simpa [DeltaU, Pdelta, P, Pabs] using
        gje_cumulative_product_matMul_componentwise_perturbation_bound_gamma_c3
          n fp N_hat DeltaN start U hn hvalid hidx hDelta i j
    have hsum :
        (∑ k : Fin n, Pabs i k * |U k j|) =
          ∑ k : Fin n, |Pabs i k| * |U k j| := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_of_nonneg (hPabs_nonneg i k)]
    simpa [hsum] using hBridge
  · intro i
    change |Deltay i| ≤
      gje_c₃ fp n * ∑ j : Fin n, |Pabs i j| * |y j|
    have hPabs_nonneg : ∀ a b : Fin n, 0 ≤ Pabs a b := by
      intro a b
      simpa [Pabs] using
        gje_cumulative_product_abs_nonneg n N_hat start (start + (n - 1)) a b
    have hBridge : |Deltay i| ≤
        gje_c₃ fp n * ∑ j : Fin n, Pabs i j * |y j| := by
      simpa [Deltay, Pdelta, P, Pabs] using
        gje_cumulative_product_matMulVec_componentwise_perturbation_bound_gamma_c3
          n fp N_hat DeltaN start y hn hvalid hidx hDelta i
    have hsum :
        (∑ j : Fin n, Pabs i j * |y j|) =
          ∑ j : Fin n, |Pabs i j| * |y j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_of_nonneg (hPabs_nonneg i j)]
    simpa [hsum] using hBridge

/-- **Theorem 14.5, eq. 14.31**: Overall GJE residual bound.

    Combining the first-stage error (GE: A + ΔA = L̂Û with |ΔA| ≤ γₙ|L̂||Û|)
    with the second-stage backward error (eq. 14.30), the residual satisfies:
      |b − Ax̂| ≤ γₙ|L̂||Û||x̂| + c₃|L̂||X̂|(|Û||x̂| + |y|)

    where X̂ = |N̂ₙ|···|N̂₂| and c₃ = (n−1)γ₃(1+γ₃)^{n−2}.

    The proof decomposes b − Ax̂ = L̂(ΔU·x̂ − Δy) + (L̂Û − A)x̂
    using the first-stage equation L̂ŷ = b and the second-stage
    backward error (Û + ΔU)x̂ = ŷ + Δy. -/
theorem gje_overall_residual (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (X_abs : Fin n → Fin n → ℝ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (_hn : gammaValid fp n)
    (_hn3 : gammaValid fp 3)
    -- First-stage equation: L̂ŷ = b
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    -- Second-stage backward error: (Û + ΔU)x̂ = ŷ + Δy with bounds
    (ΔU : Fin n → Fin n → ℝ) (Δy : Fin n → ℝ)
    (hStage2_eq : ∀ i : Fin n,
      ∑ j : Fin n, (U_hat i j + ΔU i j) * x_hat j = y i + Δy i)
    (hΔU_bound : ∀ i j : Fin n, |ΔU i j| ≤
      gje_c₃ fp n * ∑ k : Fin n, |X_abs i k| * |U_hat k j|)
    (hΔy_bound : ∀ i : Fin n, |Δy i| ≤
      gje_c₃ fp n * ∑ j : Fin n, |X_abs i j| * |y j|) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      -- First-stage contribution: |ΔA·x̂| ≤ γₙ|L̂||Û||x̂|
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
      -- Second-stage U-error: |L̂ΔU·x̂| via |X̂||Û|
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| +
      -- Second-stage y-error: |L̂Δy| via |X̂||y|
      gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |X_abs k j| * |y j|) := by
  intro i
  let T1 := gamma fp n * ∑ j : Fin n,
    (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j|
  let T2 := gje_c₃ fp n * ∑ j : Fin n,
    (∑ k₁ : Fin n, |L_hat i k₁| *
      (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
  let T3 := gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
    (∑ j : Fin n, |X_abs k j| * |y j|)
  -- From stage 2: y − Ûx̂ = ΔU·x̂ − Δy
  have hLUx : ∀ k : Fin n,
      y k - ∑ j : Fin n, U_hat k j * x_hat j =
      ∑ j : Fin n, ΔU k j * x_hat j - Δy k := by
    intro k
    have h := hStage2_eq k
    have : ∑ j : Fin n, (U_hat k j + ΔU k j) * x_hat j =
        ∑ j : Fin n, U_hat k j * x_hat j + ∑ j : Fin n, ΔU k j * x_hat j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    linarith
  have hLUerr := hLU.backward_bound
  -- Bound 1: |(L̂Û − A)x̂| ≤ T1
  have hB1 : |∑ j : Fin n, (∑ k : Fin n, L_hat i k * U_hat k j - A i j) *
      x_hat j| ≤ T1 := by
    calc _ ≤ ∑ j, |(∑ k, L_hat i k * U_hat k j - A i j) * x_hat j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |∑ k, L_hat i k * U_hat k j - A i j| * |x_hat j| := by
          apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
      _ ≤ ∑ j, (gamma fp n * ∑ k, |L_hat i k| * |U_hat k j|) * |x_hat j| := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_right (hLUerr i j) (abs_nonneg _)
      _ = T1 := by
          show _ = gamma fp n * _; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
  -- Bound 2: |L̂(ΔU·x̂ − Δy)| ≤ T2 + T3
  have hB2 : |∑ k : Fin n, L_hat i k *
      (∑ j : Fin n, ΔU k j * x_hat j - Δy k)| ≤ T2 + T3 := by
    calc _ ≤ ∑ k, |L_hat i k| * |∑ j, ΔU k j * x_hat j - Δy k| := by
          calc _ ≤ ∑ k, |L_hat i k * (∑ j, ΔU k j * x_hat j - Δy k)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ = _ := by apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
      _ ≤ ∑ k, |L_hat i k| * (∑ j, |ΔU k j| * |x_hat j| + |Δy k|) := by
          apply Finset.sum_le_sum; intro k _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc _ = |∑ j, ΔU k j * x_hat j + (-Δy k)| := by
                rw [sub_eq_add_neg]
            _ ≤ |∑ j, ΔU k j * x_hat j| + |(-Δy k)| := abs_add_le _ _
            _ = |∑ j, ΔU k j * x_hat j| + |Δy k| := by rw [abs_neg]
            _ ≤ (∑ j, |ΔU k j| * |x_hat j|) + |Δy k| := by
                linarith [show |∑ j, ΔU k j * x_hat j| ≤
                  ∑ j, |ΔU k j * x_hat j| from Finset.abs_sum_le_sum_abs _ _,
                  show ∑ j : Fin n, |ΔU k j * x_hat j| =
                    ∑ j, |ΔU k j| * |x_hat j| from
                    Finset.sum_congr rfl (fun j _ => abs_mul _ _)]
      _ ≤ ∑ k, |L_hat i k| *
          (∑ j, ((gje_c₃ fp n * ∑ k₂, |X_abs k k₂| * |U_hat k₂ j|) *
            |x_hat j|) + gje_c₃ fp n * ∑ j, |X_abs k j| * |y j|) := by
          apply Finset.sum_le_sum; intro k _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply add_le_add
          · apply Finset.sum_le_sum; intro j _
            exact mul_le_mul_of_nonneg_right (hΔU_bound k j) (abs_nonneg _)
          · exact hΔy_bound k
      _ = T2 + T3 := by
          -- Factor gje_c₃ from inner j-sum
          have h1 : ∀ k : Fin n,
              ∑ j : Fin n, (gje_c₃ fp n *
                ∑ k₂ : Fin n, |X_abs k k₂| * |U_hat k₂ j|) * |x_hat j| =
              gje_c₃ fp n *
                ∑ j : Fin n, (∑ k₂ : Fin n, |X_abs k k₂| * |U_hat k₂ j|) *
                  |x_hat j| := by
            intro k; rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j _; ring
          simp_rw [h1]
          -- Factor gje_c₃ out of each summand
          have h2 : ∀ k : Fin n,
              |L_hat i k| * (gje_c₃ fp n *
                ∑ j, (∑ k₂, |X_abs k k₂| * |U_hat k₂ j|) * |x_hat j| +
                gje_c₃ fp n * ∑ j, |X_abs k j| * |y j|) =
              gje_c₃ fp n * (|L_hat i k| *
                ∑ j, (∑ k₂, |X_abs k k₂| * |U_hat k₂ j|) * |x_hat j|) +
              gje_c₃ fp n * (|L_hat i k| * ∑ j, |X_abs k j| * |y j|) :=
            fun _ => by ring
          simp_rw [h2, Finset.sum_add_distrib, ← Finset.mul_sum]
          -- T2 needs Fubini; T3 matches directly
          congr 1
          · congr 1
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _
            simp_rw [show ∀ k : Fin n,
                |L_hat i k| * ((∑ k₂, |X_abs k k₂| * |U_hat k₂ j|) * |x_hat j|) =
                (|L_hat i k| * (∑ k₂, |X_abs k k₂| * |U_hat k₂ j|)) * |x_hat j|
              from fun _ => by ring]
            rw [← Finset.sum_mul]; congr 1
            simp_rw [Finset.mul_sum]
  -- Combine: |b − Ax̂| = |L̂(ΔU·x̂ − Δy) + (L̂Û − A)x̂| ≤ T1 + T2 + T3
  -- Algebraic decomposition
  suffices h : b i - ∑ j, A i j * x_hat j =
      ∑ k, L_hat i k * (∑ j, ΔU k j * x_hat j - Δy k) +
      ∑ j, (∑ k, L_hat i k * U_hat k j - A i j) * x_hat j by
    rw [h]
    have htri := abs_add_le
      (∑ k, L_hat i k * (∑ j, ΔU k j * x_hat j - Δy k))
      (∑ j, (∑ k, L_hat i k * U_hat k j - A i j) * x_hat j)
    linarith
  -- Prove the decomposition
  have hb : b i = ∑ k : Fin n, L_hat i k * y k := (hy i).symm
  have hyk : ∀ k : Fin n, L_hat i k * y k =
      L_hat i k * (∑ j : Fin n, U_hat k j * x_hat j) +
      L_hat i k * (∑ j : Fin n, ΔU k j * x_hat j - Δy k) := by
    intro k; rw [← mul_add]; congr 1; linarith [hLUx k]
  rw [hb]; simp_rw [hyk]; rw [Finset.sum_add_distrib]
  -- Fubini on ∑_k L̂_{ik} · ∑_j Û_{kj}x̂_j
  have hFubini : ∑ k : Fin n, L_hat i k * (∑ j : Fin n, U_hat k j * x_hat j) =
      ∑ j : Fin n, (∑ k : Fin n, L_hat i k * U_hat k j) * x_hat j := by
    simp_rw [Finset.mul_sum, ← mul_assoc]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_mul]
  linarith [show ∑ j : Fin n, (∑ k : Fin n, L_hat i k * U_hat k j) * x_hat j -
      ∑ j : Fin n, A i j * x_hat j =
      ∑ j : Fin n, (∑ k : Fin n, L_hat i k * U_hat k j - A i j) * x_hat j from by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring]

/-- **Theorem 14.5, eq. 14.31 certificate route**:
    the cumulative-product second-stage certificates from (14.30) imply the
    overall GJE residual bound, leaving only the exact rounded-recurrence
    backward equation as an explicit source-instantiation hypothesis. -/
theorem gje_overall_residual_of_cumulative_product_certificates
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) k₁ k₂| *
              |U_hat k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n,
          |gje_cumulative_product n (fun s a b => |N_hat s a b|)
            start (start + (n - 1)) k j| * |y j|) := by
  let X_abs : Fin n → Fin n → ℝ :=
    gje_cumulative_product n (fun s a b => |N_hat s a b|)
      start (start + (n - 1))
  obtain ⟨DeltaU, Deltay, hStage2_eq, hDeltaU, hDeltay⟩ :=
    gje_stage2_backward_error_of_cumulative_product_certificates
      n fp U_hat y x_hat N_hat DeltaN start hnpos hn3 hidx hDelta hBackwardEq
  simpa [X_abs] using
    gje_overall_residual n fp A L_hat U_hat b y x_hat X_abs
      hLU hn hn3 hy DeltaU Deltay hStage2_eq hDeltaU hDeltay

/-- **Theorem 14.5 scalar-split residual route**:
    the cumulative-product residual certificate route with the `gje_c₃`
    coefficient expanded into its first-order `3(n-1)u` part plus the
    explicit higher-order remainder. -/
theorem gje_overall_residual_of_cumulative_product_certificates_c3_split
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
      (3 * ((n : ℝ) - 1) * fp.u + gje_c3_quadratic_remainder fp n) *
        ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) k₁ k₂| *
              |U_hat k₂ j|)) * |x_hat j| +
      (3 * ((n : ℝ) - 1) * fp.u + gje_c3_quadratic_remainder fp n) *
        ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) k j| * |y j|) := by
  have h :=
    gje_overall_residual_of_cumulative_product_certificates
      n fp A L_hat U_hat b y x_hat N_hat DeltaN start
      hLU hn hnpos hn3 hidx hDelta hy hBackwardEq
  simpa [gje_c3_eq_linear_plus_quadratic_remainder_term fp n hn3] using h

/-- **Theorem 14.5 residual route with the source-facing `3 n u` cap**.

    This pushes `gje_c3_le_three_n_u_plus_quadratic_remainder` through the
    cumulative-product residual certificate route, replacing the exact
    second-stage coefficient by `3 n u` plus the explicit higher-order
    remainder. -/
theorem gje_overall_residual_of_cumulative_product_certificates_c3_three_n
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
      (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
        ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) k₁ k₂| *
              |U_hat k₂ j|)) * |x_hat j| +
      (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
        ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) k j| * |y j|) := by
  intro i
  let C : ℝ := 3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n
  let S2 : ℝ :=
    ∑ j : Fin n,
      (∑ k₁ : Fin n, |L_hat i k₁| *
        (∑ k₂ : Fin n,
          |gje_cumulative_product n (fun s a b => |N_hat s a b|)
            start (start + (n - 1)) k₁ k₂| *
          |U_hat k₂ j|)) * |x_hat j|
  let S3 : ℝ :=
    ∑ k : Fin n, |L_hat i k| *
      (∑ j : Fin n,
        |gje_cumulative_product n (fun s a b => |N_hat s a b|)
          start (start + (n - 1)) k j| * |y j|)
  have hBase :=
    gje_overall_residual_of_cumulative_product_certificates
      n fp A L_hat U_hat b y x_hat N_hat DeltaN start
      hLU hn hnpos hn3 hidx hDelta hy hBackwardEq
  have hC : gje_c₃ fp n ≤ C := by
    simpa [C] using gje_c3_le_three_n_u_plus_quadratic_remainder fp n hn3
  have hS2_nonneg : 0 ≤ S2 := by
    dsimp [S2]
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg
      (Finset.sum_nonneg (fun k₁ _ =>
        mul_nonneg (abs_nonneg _)
          (Finset.sum_nonneg (fun k₂ _ =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _)))))
      (abs_nonneg _)
  have hS3_nonneg : 0 ≤ S3 := by
    dsimp [S3]
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (abs_nonneg _)
      (Finset.sum_nonneg (fun j _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have h2 : gje_c₃ fp n * S2 ≤ C * S2 :=
    mul_le_mul_of_nonneg_right hC hS2_nonneg
  have h3 : gje_c₃ fp n * S3 ≤ C * S3 :=
    mul_le_mul_of_nonneg_right hC hS3_nonneg
  have hGoal :
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
      C * S2 + C * S3 := by
    calc
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
          gamma fp n * ∑ j : Fin n,
            (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
          gje_c₃ fp n * S2 + gje_c₃ fp n * S3 := by
            simpa [S2, S3] using hBase i
      _ ≤ gamma fp n * ∑ j : Fin n,
            (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
          C * S2 + C * S3 := by
            nlinarith
  simpa [C, S2, S3] using hGoal

/-- **Theorem 14.5, eq. 14.32**: Overall GJE forward error.

    The forward error satisfies:
      |x − x̂| ≤ |A⁻¹| · |b − Ax̂|.

    Combined with the residual bound (eq. 14.31), this gives:
      |x − x̂| ≤ |A⁻¹| · (γₙ|L̂||Û||x̂| + c₃|L̂||X̂|(|Û||x̂| + |y|)). -/
theorem gje_overall_forward_error (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (X_abs : Fin n → Fin n → ℝ)
    (_hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (_hn : gammaValid fp n)
    (_hn3 : gammaValid fp 3)
    -- Exact solution
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    -- Residual bound from gje_overall_residual
    (hResidual : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |X_abs k j| * |y j|)) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ k|)) * |x_hat k| +
        gje_c₃ fp n * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n, |X_abs l k| * |y k|)) := by
  intro i
  -- x − x̂ = A⁻¹(b − Ax̂) since Ax = b
  have hDiff : x i - x_hat i =
      ∑ j : Fin n, A_inv i j *
        (b j - ∑ k : Fin n, A j k * x_hat k) := by
    have hRHS_expand : ∑ j : Fin n, A_inv i j *
        (b j - ∑ k : Fin n, A j k * x_hat k) =
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x k) -
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x_hat k) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _
      rw [hExact j]; ring
    rw [hRHS_expand]
    -- ∑_j A⁻¹(i,j) · ∑_k A(j,k) · x(k) = x(i) using hAinv
    have hFirst : ∑ j : Fin n, A_inv i j *
        (∑ k : Fin n, A j k * x k) = x i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hSecond : ∑ j : Fin n, A_inv i j *
        (∑ k : Fin n, A j k * x_hat k) = x_hat i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    linarith
  rw [hDiff]
  -- |∑ A⁻¹ · r| ≤ ∑ |A⁻¹| · |r| ≤ ∑ |A⁻¹| · (bound)
  calc |∑ j : Fin n, A_inv i j *
        (b j - ∑ k : Fin n, A j k * x_hat k)|
      ≤ ∑ j : Fin n, |A_inv i j| *
        |b j - ∑ k : Fin n, A j k * x_hat k| := by
        calc _ ≤ ∑ j, |A_inv i j * (b j - ∑ k, A j k * x_hat k)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = _ := by apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
    _ ≤ ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        (gje_c₃ fp n) * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ k|)) * |x_hat k| +
        (gje_c₃ fp n) * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n, |X_abs l k| * |y k|)) := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (hResidual j) (abs_nonneg _)

/-- **Theorem 14.5, eqs. 14.31--14.32 certificate route**:
    the cumulative-product second-stage certificates imply the overall GJE
    forward error bound after composing the residual certificate route with
    the exact inverse transfer `|x - x_hat| <= |A_inv| |b - A x_hat|`.

    The exact rounded-recurrence backward equation from (14.30a) remains an
    explicit source-instantiation hypothesis. -/
theorem gje_overall_forward_error_of_cumulative_product_certificates
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) k₁ k₂| *
              |U_hat k₂ k|)) * |x_hat k| +
        gje_c₃ fp n * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) l k| * |y k|)) := by
  let X_abs : Fin n → Fin n → ℝ :=
    gje_cumulative_product n (fun s a b => |N_hat s a b|)
      start (start + (n - 1))
  have hResidual :
      ∀ i : Fin n,
        |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        gamma fp n * ∑ j : Fin n,
          (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
        gje_c₃ fp n * ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| +
        gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n, |X_abs k j| * |y j|) := by
    simpa [X_abs] using
      gje_overall_residual_of_cumulative_product_certificates
        n fp A L_hat U_hat b y x_hat N_hat DeltaN start
        hLU hn hnpos hn3 hidx hDelta hy hBackwardEq
  simpa [X_abs] using
    gje_overall_forward_error n fp A A_inv L_hat U_hat b y x x_hat X_abs
      hLU hAinv hn hn3 hExact hResidual

/-- **Theorem 14.5 scalar-split forward-error route**:
    the cumulative-product forward-error certificate route with the `gje_c₃`
    coefficient expanded into its first-order `3(n-1)u` part plus the
    explicit higher-order remainder. -/
theorem gje_overall_forward_error_of_cumulative_product_certificates_c3_split
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        (3 * ((n : ℝ) - 1) * fp.u + gje_c3_quadratic_remainder fp n) *
          ∑ k : Fin n,
            (∑ k₁ : Fin n, |L_hat j k₁| *
              (∑ k₂ : Fin n,
                |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                  start (start + (n - 1)) k₁ k₂| *
                |U_hat k₂ k|)) * |x_hat k| +
        (3 * ((n : ℝ) - 1) * fp.u + gje_c3_quadratic_remainder fp n) *
          ∑ l : Fin n, |L_hat j l| *
            (∑ k : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) l k| * |y k|)) := by
  have h :=
    gje_overall_forward_error_of_cumulative_product_certificates
      n fp A A_inv L_hat U_hat b y x x_hat N_hat DeltaN start
      hLU hAinv hn hnpos hn3 hidx hDelta hy hExact hBackwardEq
  simpa [gje_c3_eq_linear_plus_quadratic_remainder_term fp n hn3] using h

/-- **Theorem 14.5 forward-error route with the source-facing `3 n u` cap**.

    This is the forward-error companion to
    `gje_overall_residual_of_cumulative_product_certificates_c3_three_n`. -/
theorem gje_overall_forward_error_of_cumulative_product_certificates_c3_three_n
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i)) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
          ∑ k : Fin n,
            (∑ k₁ : Fin n, |L_hat j k₁| *
              (∑ k₂ : Fin n,
                |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                  start (start + (n - 1)) k₁ k₂| *
                |U_hat k₂ k|)) * |x_hat k| +
        (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
          ∑ l : Fin n, |L_hat j l| *
            (∑ k : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) l k| * |y k|)) := by
  intro i
  let C : ℝ := 3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n
  have hBase :=
    gje_overall_forward_error_of_cumulative_product_certificates
      n fp A A_inv L_hat U_hat b y x x_hat N_hat DeltaN start
      hLU hAinv hn hnpos hn3 hidx hDelta hy hExact hBackwardEq
  have hC : gje_c₃ fp n ≤ C := by
    simpa [C] using gje_c3_le_three_n_u_plus_quadratic_remainder fp n hn3
  have hTerm :
      ∀ j : Fin n,
        gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) k₁ k₂| *
              |U_hat k₂ k|)) * |x_hat k| +
        gje_c₃ fp n * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) l k| * |y k|) ≤
        gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        C * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) k₁ k₂| *
              |U_hat k₂ k|)) * |x_hat k| +
        C * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) l k| * |y k|) := by
    intro j
    let S2 : ℝ :=
      ∑ k : Fin n,
        (∑ k₁ : Fin n, |L_hat j k₁| *
          (∑ k₂ : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) k₁ k₂| *
            |U_hat k₂ k|)) * |x_hat k|
    let S3 : ℝ :=
      ∑ l : Fin n, |L_hat j l| *
        (∑ k : Fin n,
          |gje_cumulative_product n (fun s a b => |N_hat s a b|)
            start (start + (n - 1)) l k| * |y k|)
    have hS2_nonneg : 0 ≤ S2 := by
      dsimp [S2]
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg
        (Finset.sum_nonneg (fun k₁ _ =>
          mul_nonneg (abs_nonneg _)
            (Finset.sum_nonneg (fun k₂ _ =>
              mul_nonneg (abs_nonneg _) (abs_nonneg _)))))
        (abs_nonneg _)
    have hS3_nonneg : 0 ≤ S3 := by
      dsimp [S3]
      apply Finset.sum_nonneg
      intro l _
      exact mul_nonneg (abs_nonneg _)
        (Finset.sum_nonneg (fun k _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    have h2 : gje_c₃ fp n * S2 ≤ C * S2 :=
      mul_le_mul_of_nonneg_right hC hS2_nonneg
    have h3 : gje_c₃ fp n * S3 ≤ C * S3 :=
      mul_le_mul_of_nonneg_right hC hS3_nonneg
    simpa [S2, S3] using (by nlinarith : gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        gje_c₃ fp n * S2 + gje_c₃ fp n * S3 ≤
        gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        C * S2 + C * S3)
  calc
    |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) k₁ k₂| *
              |U_hat k₂ k|)) * |x_hat k| +
        gje_c₃ fp n * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) l k| * |y k|)) := by
        simpa using hBase i
    _ ≤ ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |L_hat j l| * |U_hat l k|) * |x_hat k| +
        C * ∑ k : Fin n,
          (∑ k₁ : Fin n, |L_hat j k₁| *
            (∑ k₂ : Fin n,
              |gje_cumulative_product n (fun s a b => |N_hat s a b|)
                start (start + (n - 1)) k₁ k₂| *
              |U_hat k₂ k|)) * |x_hat k| +
        C * ∑ l : Fin n, |L_hat j l| *
          (∑ k : Fin n,
            |gje_cumulative_product n (fun s a b => |N_hat s a b|)
              start (start + (n - 1)) l k| * |y k|)) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hTerm j) (abs_nonneg _)

-- ══════════════════════════════════════════════════════════════════════
-- §14.4.7  Corollary 14.6: SPD Specialization
-- ══════════════════════════════════════════════════════════════════════

/-- **Abstract Corollary 14.6 interface** (Higham p. 277): GJE for SPD matrices.

    For SPD A with Cholesky factorization A + ΔA = R̂ᵀR̂, the GJE
    residual simplifies because L̂ = R̂ᵀ, Û = R̂, and the cumulative
    product X̂ = |N̂ₙ···N̂₂| is bounded by |R̂⁻¹|.

    The componentwise residual specializes to:
      |b − Ax̂| ≤ γₙ|R̂ᵀ||R̂||x̂| + c₃|R̂ᵀ||R̂⁻¹|(|R̂||x̂| + |y|)

    which gives the normwise bound (Higham eq. 14.33):
      ‖b − Ax̂‖ / (‖A‖ · ‖x̂‖) ≤ 8n³u κ(A)^{1/2} + O(u²).

    The specialized residual is supplied as `hResidual`; the general
    composition theorem `gje_overall_residual` above is fully proved from its
    stated first- and second-stage hypotheses. -/
theorem gje_spd_residual (n : ℕ) (fp : FPModel)
    (A R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (_hSPD : IsSymPosDef n A)
    (_hn : gammaValid fp n)
    (_hn3 : gammaValid fp 3)
    -- Cholesky: A + ΔA = R̂ᵀR̂ (L̂ = R̂ᵀ, Û = R̂)
    (_hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    -- The overall residual bound specializing Theorem 14.5
    -- with L̂ = R̂ᵀ, Û = R̂, X_abs = |R̂⁻¹|
    (hResidual : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |R_hat k₁ i| *
          (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |R_hat k i| *
        (∑ j : Fin n, |R_inv k j| * |y j|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |R_hat k₁ i| *
          (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |R_hat k i| *
        (∑ j : Fin n, |R_inv k j| * |y j|) :=
  hResidual

/-- **Corollary 14.6 componentwise certificate route** (Higham p. 277).

    This specializes the proved Theorem 14.5 cumulative-product residual route
    to the SPD/GJE shape `L_hat = R_hatᵀ`, `U_hat = R_hat`.  The extra
    certificate `hRinvDom` records the source comparison that the second-stage
    absolute cumulative product is bounded entrywise by the supplied
    `R_inv` majorant.  This closes the componentwise residual transfer to the
    existing Corollary 14.6 interface; the normwise printed `κ₂(A)^{1/2}`
    endpoint remains a separate open norm/Cholesky aggregation step. -/
theorem gje_spd_residual_of_cumulative_product_certificates
    (n : ℕ) (fp : FPModel)
    (A R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j| +
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |R_hat k₁ i| *
          (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j| +
      gje_c₃ fp n * ∑ k : Fin n, |R_hat k i| *
        (∑ j : Fin n, |R_inv k j| * |y j|) := by
  let X_abs : Fin n → Fin n → ℝ :=
    gje_cumulative_product n (fun s a b => |N_hat s a b|)
      start (start + (n - 1))
  have hXdom : ∀ i j : Fin n, |X_abs i j| ≤ |R_inv i j| := by
    intro i j
    simpa [X_abs] using hRinvDom i j
  have hc3 : 0 ≤ gje_c₃ fp n := gje_c3_nonneg fp n hnpos hn3
  have hGen :
      ∀ i : Fin n,
        |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        gamma fp n * ∑ j : Fin n,
          (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j| +
        gje_c₃ fp n * ∑ j : Fin n,
          (∑ k₁ : Fin n, |R_hat k₁ i| *
            (∑ k₂ : Fin n, |X_abs k₁ k₂| * |R_hat k₂ j|)) * |x_hat j| +
        gje_c₃ fp n * ∑ k : Fin n, |R_hat k i| *
          (∑ j : Fin n, |X_abs k j| * |y j|) := by
    simpa [X_abs] using
      gje_overall_residual_of_cumulative_product_certificates
        n fp A (fun i j => R_hat j i) R_hat b y x_hat
        N_hat DeltaN start hLU hn hnpos hn3 hidx hDelta hy hBackwardEq
  have hResidual :
      ∀ i : Fin n,
        |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        gamma fp n * ∑ j : Fin n,
          (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j| +
        gje_c₃ fp n * ∑ j : Fin n,
          (∑ k₁ : Fin n, |R_hat k₁ i| *
            (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j| +
        gje_c₃ fp n * ∑ k : Fin n, |R_hat k i| *
          (∑ j : Fin n, |R_inv k j| * |y j|) := by
    intro i
    let T1 : ℝ :=
      gamma fp n * ∑ j : Fin n,
        (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j|
    let T2X : ℝ :=
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |R_hat k₁ i| *
          (∑ k₂ : Fin n, |X_abs k₁ k₂| * |R_hat k₂ j|)) * |x_hat j|
    let T2R : ℝ :=
      gje_c₃ fp n * ∑ j : Fin n,
        (∑ k₁ : Fin n, |R_hat k₁ i| *
          (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j|
    let T3X : ℝ :=
      gje_c₃ fp n * ∑ k : Fin n, |R_hat k i| *
        (∑ j : Fin n, |X_abs k j| * |y j|)
    let T3R : ℝ :=
      gje_c₃ fp n * ∑ k : Fin n, |R_hat k i| *
        (∑ j : Fin n, |R_inv k j| * |y j|)
    have hT2 : T2X ≤ T2R := by
      dsimp [T2X, T2R]
      apply mul_le_mul_of_nonneg_left _ hc3
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply Finset.sum_le_sum
      intro k₁ _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Finset.sum_le_sum
      intro k₂ _
      exact mul_le_mul_of_nonneg_right (hXdom k₁ k₂) (abs_nonneg _)
    have hT3 : T3X ≤ T3R := by
      dsimp [T3X, T3R]
      apply mul_le_mul_of_nonneg_left _ hc3
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hXdom k j) (abs_nonneg _)
    calc
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤ T1 + T2X + T3X := by
        simpa [T1, T2X, T3X] using hGen i
      _ ≤ T1 + T2R + T3X := by
        linarith
      _ ≤ T1 + T2R + T3R := by
        linarith
      _ = gamma fp n * ∑ j : Fin n,
            (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j| +
          gje_c₃ fp n * ∑ j : Fin n,
            (∑ k₁ : Fin n, |R_hat k₁ i| *
              (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j| +
          gje_c₃ fp n * ∑ k : Fin n, |R_hat k i| *
          (∑ j : Fin n, |R_inv k j| * |y j|) := by
        rfl
  exact gje_spd_residual n fp A R_hat R_inv b y x_hat hSPD hn hn3 hLU hResidual

/-- **Corollary 14.6 conditional normwise residual route**.

    Starting from the componentwise SPD/GJE cumulative-product certificate,
    this converts the residual to a relative 2-norm bound after exposing the
    three remaining Cholesky/norm aggregation facts as hypotheses.  The
    second-stage coefficient is capped by the source-facing
    `3 n u + gje_c3_quadratic_remainder fp n`; the final printed
    `kappa_2(A)^(1/2)` constants remain separate aggregation obligations. -/
theorem gje_spd_residual_relative_norm2_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (alpha beta eta : ℝ)
    (hApos : 0 < opNorm2 A)
    (hxpos : 0 < vecNorm2 x_hat)
    (hbeta : 0 ≤ beta) (heta : 0 ≤ eta)
    (hRT_R_x :
      vecNorm2 (fun i : Fin n =>
        ∑ j : Fin n,
          (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j|) ≤
        alpha * vecNorm2 x_hat)
    (hRT_Rinv_R_x :
      vecNorm2 (fun i : Fin n =>
        ∑ j : Fin n,
          (∑ k₁ : Fin n, |R_hat k₁ i| *
            (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j|) ≤
        beta * vecNorm2 x_hat)
    (hRT_Rinv_y :
      vecNorm2 (fun i : Fin n =>
        ∑ k : Fin n, |R_hat k i| *
          (∑ j : Fin n, |R_inv k j| * |y j|)) ≤
        eta * vecNorm2 x_hat) :
    vecNorm2 (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (opNorm2 A * vecNorm2 x_hat) ≤
      (gamma fp n * alpha +
          (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (beta + eta)) / opNorm2 A := by
  let r : Fin n → ℝ := fun i => b i - ∑ j : Fin n, A i j * x_hat j
  let T1 : Fin n → ℝ := fun i =>
    ∑ j : Fin n,
      (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j|
  let T2 : Fin n → ℝ := fun i =>
    ∑ j : Fin n,
      (∑ k₁ : Fin n, |R_hat k₁ i| *
        (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j|
  let T3 : Fin n → ℝ := fun i =>
    ∑ k : Fin n, |R_hat k i| *
      (∑ j : Fin n, |R_inv k j| * |y j|)
  let C : ℝ := 3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n
  have hResidual :=
    gje_spd_residual_of_cumulative_product_certificates
      n fp A R_hat R_inv b y x_hat N_hat DeltaN start
      hSPD hLU hn hnpos hn3 hidx hDelta hy hBackwardEq hRinvDom
  have hAbs : ∀ i : Fin n,
      |r i| ≤ gamma fp n * T1 i + gje_c₃ fp n * T2 i + gje_c₃ fp n * T3 i := by
    intro i
    simpa [r, T1, T2, T3] using hResidual i
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hc3 : 0 ≤ gje_c₃ fp n := gje_c3_nonneg fp n hnpos hn3
  have hC : gje_c₃ fp n ≤ C := by
    simpa [C] using gje_c3_le_three_n_u_plus_quadratic_remainder fp n hn3
  have hC_nonneg : 0 ≤ C := le_trans hc3 hC
  have hNormStart :
      vecNorm2 r ≤
        vecNorm2 (fun i : Fin n =>
          gamma fp n * T1 i + gje_c₃ fp n * T2 i + gje_c₃ fp n * T3 i) :=
    vecNorm2_le_of_abs_le r
      (fun i : Fin n =>
        gamma fp n * T1 i + gje_c₃ fp n * T2 i + gje_c₃ fp n * T3 i) hAbs
  have hTri :
      vecNorm2 (fun i : Fin n =>
          gamma fp n * T1 i + gje_c₃ fp n * T2 i + gje_c₃ fp n * T3 i) ≤
        gamma fp n * vecNorm2 T1 + gje_c₃ fp n * vecNorm2 T2 +
          gje_c₃ fp n * vecNorm2 T3 := by
    have h12 :=
      vecNorm2_add_le
        (fun i : Fin n => gamma fp n * T1 i)
        (fun i : Fin n => gje_c₃ fp n * T2 i)
    have h123 :=
      vecNorm2_add_le
        (fun i : Fin n => gamma fp n * T1 i + gje_c₃ fp n * T2 i)
        (fun i : Fin n => gje_c₃ fp n * T3 i)
    have h1 :
        vecNorm2 (fun i : Fin n => gamma fp n * T1 i) =
          gamma fp n * vecNorm2 T1 := by
      rw [vecNorm2_smul, abs_of_nonneg hgamma]
    have h2 :
        vecNorm2 (fun i : Fin n => gje_c₃ fp n * T2 i) =
          gje_c₃ fp n * vecNorm2 T2 := by
      rw [vecNorm2_smul, abs_of_nonneg hc3]
    have h3 :
        vecNorm2 (fun i : Fin n => gje_c₃ fp n * T3 i) =
          gje_c₃ fp n * vecNorm2 T3 := by
      rw [vecNorm2_smul, abs_of_nonneg hc3]
    calc
      vecNorm2 (fun i : Fin n =>
          gamma fp n * T1 i + gje_c₃ fp n * T2 i + gje_c₃ fp n * T3 i)
          ≤ vecNorm2 (fun i : Fin n =>
              gamma fp n * T1 i + gje_c₃ fp n * T2 i) +
            vecNorm2 (fun i : Fin n => gje_c₃ fp n * T3 i) := h123
      _ ≤ (vecNorm2 (fun i : Fin n => gamma fp n * T1 i) +
              vecNorm2 (fun i : Fin n => gje_c₃ fp n * T2 i)) +
            vecNorm2 (fun i : Fin n => gje_c₃ fp n * T3 i) := by
              exact add_le_add h12 (le_refl _)
      _ = gamma fp n * vecNorm2 T1 + gje_c₃ fp n * vecNorm2 T2 +
          gje_c₃ fp n * vecNorm2 T3 := by
            rw [h1, h2, h3]
  have hT1 :
      gamma fp n * vecNorm2 T1 ≤
        gamma fp n * (alpha * vecNorm2 x_hat) := by
    exact mul_le_mul_of_nonneg_left (by simpa [T1] using hRT_R_x) hgamma
  have hT2 :
      gje_c₃ fp n * vecNorm2 T2 ≤
        C * (beta * vecNorm2 x_hat) := by
    calc
      gje_c₃ fp n * vecNorm2 T2 ≤
          gje_c₃ fp n * (beta * vecNorm2 x_hat) := by
            exact mul_le_mul_of_nonneg_left (by simpa [T2] using hRT_Rinv_R_x) hc3
      _ ≤ C * (beta * vecNorm2 x_hat) := by
            exact mul_le_mul_of_nonneg_right hC
              (mul_nonneg hbeta (vecNorm2_nonneg x_hat))
  have hT3 :
      gje_c₃ fp n * vecNorm2 T3 ≤
        C * (eta * vecNorm2 x_hat) := by
    calc
      gje_c₃ fp n * vecNorm2 T3 ≤
          gje_c₃ fp n * (eta * vecNorm2 x_hat) := by
            exact mul_le_mul_of_nonneg_left (by simpa [T3] using hRT_Rinv_y) hc3
      _ ≤ C * (eta * vecNorm2 x_hat) := by
            exact mul_le_mul_of_nonneg_right hC
              (mul_nonneg heta (vecNorm2_nonneg x_hat))
  have hVec :
      vecNorm2 r ≤
        (gamma fp n * alpha + C * (beta + eta)) * vecNorm2 x_hat := by
    calc
      vecNorm2 r ≤
          gamma fp n * vecNorm2 T1 + gje_c₃ fp n * vecNorm2 T2 +
            gje_c₃ fp n * vecNorm2 T3 := le_trans hNormStart hTri
      _ ≤ gamma fp n * (alpha * vecNorm2 x_hat) +
            C * (beta * vecNorm2 x_hat) + C * (eta * vecNorm2 x_hat) := by
            nlinarith
      _ = (gamma fp n * alpha + C * (beta + eta)) * vecNorm2 x_hat := by
            ring
  have hden_pos : 0 < opNorm2 A * vecNorm2 x_hat := mul_pos hApos hxpos
  have hDiv :=
    div_le_div_of_nonneg_right hVec hden_pos.le
  calc
    vecNorm2 (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (opNorm2 A * vecNorm2 x_hat)
        = vecNorm2 r / (opNorm2 A * vecNorm2 x_hat) := by rfl
    _ ≤ ((gamma fp n * alpha + C * (beta + eta)) * vecNorm2 x_hat) /
        (opNorm2 A * vecNorm2 x_hat) := hDiv
    _ = (gamma fp n * alpha + C * (beta + eta)) / opNorm2 A := by
        field_simp [hApos.ne', hxpos.ne']

/-- Canonical finite 2-norm aggregation constant for the SPD/Corollary 14.6
    first-stage residual term. -/
noncomputable def gje_spd_firstStage_norm2AggregationConstant
    (n : ℕ) (R_hat : Fin n → Fin n → ℝ) (x_hat : Fin n → ℝ) : ℝ :=
  vecNorm2 (fun i : Fin n =>
    ∑ j : Fin n,
      (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j|) /
    vecNorm2 x_hat

/-- Canonical finite 2-norm aggregation constant for the SPD/Corollary 14.6
    second-stage `R_inv * R_hat * x_hat` residual term. -/
noncomputable def gje_spd_secondStageX_norm2AggregationConstant
    (n : ℕ) (R_hat R_inv : Fin n → Fin n → ℝ)
    (x_hat : Fin n → ℝ) : ℝ :=
  vecNorm2 (fun i : Fin n =>
    ∑ j : Fin n,
      (∑ k₁ : Fin n, |R_hat k₁ i| *
        (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j|) /
    vecNorm2 x_hat

/-- Canonical finite 2-norm aggregation constant for the SPD/Corollary 14.6
    second-stage `R_inv * y` residual term. -/
noncomputable def gje_spd_secondStageY_norm2AggregationConstant
    (n : ℕ) (R_hat R_inv : Fin n → Fin n → ℝ)
    (x_hat y : Fin n → ℝ) : ℝ :=
  vecNorm2 (fun i : Fin n =>
    ∑ k : Fin n, |R_hat k i| *
      (∑ j : Fin n, |R_inv k j| * |y j|)) /
    vecNorm2 x_hat

/-- **Corollary 14.6 conditional normwise residual route, finite aggregation
    form**.

    This wrapper discharges the arbitrary `alpha`, `beta`, and `eta`
    aggregation hypotheses in
    `gje_spd_residual_relative_norm2_of_cumulative_product_certificates_c3_cap`
    by using canonical finite 2-norm quotient constants.  It does not attempt
    the remaining source step that reduces these constants to the printed
    `kappa_2(A)^(1/2)` endpoint. -/
theorem gje_spd_residual_relative_norm2_normConstants_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (hApos : 0 < opNorm2 A)
    (hxpos : 0 < vecNorm2 x_hat) :
    vecNorm2 (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (opNorm2 A * vecNorm2 x_hat) ≤
      (gamma fp n *
          gje_spd_firstStage_norm2AggregationConstant n R_hat x_hat +
        (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
          (gje_spd_secondStageX_norm2AggregationConstant n R_hat R_inv x_hat +
            gje_spd_secondStageY_norm2AggregationConstant n R_hat R_inv x_hat y)) /
        opNorm2 A := by
  let alpha : ℝ :=
    gje_spd_firstStage_norm2AggregationConstant n R_hat x_hat
  let beta : ℝ :=
    gje_spd_secondStageX_norm2AggregationConstant n R_hat R_inv x_hat
  let eta : ℝ :=
    gje_spd_secondStageY_norm2AggregationConstant n R_hat R_inv x_hat y
  let T1 : Fin n → ℝ := fun i =>
    ∑ j : Fin n,
      (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j|
  let T2 : Fin n → ℝ := fun i =>
    ∑ j : Fin n,
      (∑ k₁ : Fin n, |R_hat k₁ i| *
        (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j|
  let T3 : Fin n → ℝ := fun i =>
    ∑ k : Fin n, |R_hat k i| *
      (∑ j : Fin n, |R_inv k j| * |y j|)
  have hbeta_nonneg : 0 ≤ beta := by
    have hdiv : 0 ≤ vecNorm2 T2 / vecNorm2 x_hat :=
      div_nonneg (vecNorm2_nonneg T2) hxpos.le
    simpa [beta, gje_spd_secondStageX_norm2AggregationConstant, T2] using hdiv
  have heta_nonneg : 0 ≤ eta := by
    have hdiv : 0 ≤ vecNorm2 T3 / vecNorm2 x_hat :=
      div_nonneg (vecNorm2_nonneg T3) hxpos.le
    simpa [eta, gje_spd_secondStageY_norm2AggregationConstant, T3] using hdiv
  have halpha_eq : alpha * vecNorm2 x_hat = vecNorm2 T1 := by
    simp [alpha, gje_spd_firstStage_norm2AggregationConstant, T1]
    field_simp [hxpos.ne']
  have hbeta_eq : beta * vecNorm2 x_hat = vecNorm2 T2 := by
    simp [beta, gje_spd_secondStageX_norm2AggregationConstant, T2]
    field_simp [hxpos.ne']
  have heta_eq : eta * vecNorm2 x_hat = vecNorm2 T3 := by
    simp [eta, gje_spd_secondStageY_norm2AggregationConstant, T3]
    field_simp [hxpos.ne']
  have hRT_R_x :
      vecNorm2 (fun i : Fin n =>
        ∑ j : Fin n,
          (∑ k : Fin n, |R_hat k i| * |R_hat k j|) * |x_hat j|) ≤
        alpha * vecNorm2 x_hat := by
    change vecNorm2 T1 ≤ alpha * vecNorm2 x_hat
    exact le_of_eq halpha_eq.symm
  have hRT_Rinv_R_x :
      vecNorm2 (fun i : Fin n =>
        ∑ j : Fin n,
          (∑ k₁ : Fin n, |R_hat k₁ i| *
            (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ j|)) * |x_hat j|) ≤
        beta * vecNorm2 x_hat := by
    change vecNorm2 T2 ≤ beta * vecNorm2 x_hat
    exact le_of_eq hbeta_eq.symm
  have hRT_Rinv_y :
      vecNorm2 (fun i : Fin n =>
        ∑ k : Fin n, |R_hat k i| *
          (∑ j : Fin n, |R_inv k j| * |y j|)) ≤
        eta * vecNorm2 x_hat := by
    change vecNorm2 T3 ≤ eta * vecNorm2 x_hat
    exact le_of_eq heta_eq.symm
  have hbase :=
    gje_spd_residual_relative_norm2_of_cumulative_product_certificates_c3_cap
      n fp A R_hat R_inv b y x_hat N_hat DeltaN start
      hSPD hLU hn hnpos hn3 hidx hDelta hy hBackwardEq hRinvDom
      alpha beta eta hApos hxpos hbeta_nonneg heta_nonneg
      hRT_R_x hRT_Rinv_R_x hRT_Rinv_y
  simpa [alpha, beta, eta] using hbase

/-- **Corollary 14.6 componentwise forward-error certificate route**.

    This is the forward-error companion to
    `gje_spd_residual_of_cumulative_product_certificates`.  It specializes the
    proved Theorem 14.5 cumulative-product forward-error route to the SPD/GJE
    shape `L_hat = R_hatᵀ`, `U_hat = R_hat`, and uses the explicit
    `hRinvDom` majorization certificate to replace the second-stage absolute
    cumulative product by the supplied `R_inv` entrywise majorant.  The
    source normwise `κ₂(A)^{1/2}` endpoint remains a separate norm/Cholesky
    aggregation step. -/
theorem gje_spd_forward_error_of_cumulative_product_certificates
    (n : ℕ) (fp : FPModel)
    (A A_inv R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (_hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|) :
    ∀ i : Fin n,
      |x i - x_hat i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |R_hat l j| * |R_hat l k|) * |x_hat k| +
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |R_hat k₁ j| *
            (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ k|)) * |x_hat k| +
        gje_c₃ fp n * ∑ l : Fin n, |R_hat l j| *
          (∑ k : Fin n, |R_inv l k| * |y k|)) := by
  let X_abs : Fin n → Fin n → ℝ :=
    gje_cumulative_product n (fun s a b => |N_hat s a b|)
      start (start + (n - 1))
  have hXdom : ∀ i j : Fin n, |X_abs i j| ≤ |R_inv i j| := by
    intro i j
    simpa [X_abs] using hRinvDom i j
  have hc3 : 0 ≤ gje_c₃ fp n := gje_c3_nonneg fp n hnpos hn3
  have hGen :
      ∀ i : Fin n,
        |x i - x_hat i| ≤
        ∑ j : Fin n, |A_inv i j| *
          (gamma fp n * ∑ k : Fin n,
            (∑ l : Fin n, |R_hat l j| * |R_hat l k|) * |x_hat k| +
          gje_c₃ fp n * ∑ k : Fin n,
            (∑ k₁ : Fin n, |R_hat k₁ j| *
              (∑ k₂ : Fin n, |X_abs k₁ k₂| * |R_hat k₂ k|)) * |x_hat k| +
          gje_c₃ fp n * ∑ l : Fin n, |R_hat l j| *
            (∑ k : Fin n, |X_abs l k| * |y k|)) := by
    simpa [X_abs] using
      gje_overall_forward_error_of_cumulative_product_certificates
        n fp A A_inv (fun i j => R_hat j i) R_hat b y x x_hat
        N_hat DeltaN start hLU hAinv hn hnpos hn3 hidx hDelta hy hExact hBackwardEq
  intro i
  calc
    |x i - x_hat i| ≤
        ∑ j : Fin n, |A_inv i j| *
          (gamma fp n * ∑ k : Fin n,
            (∑ l : Fin n, |R_hat l j| * |R_hat l k|) * |x_hat k| +
          gje_c₃ fp n * ∑ k : Fin n,
            (∑ k₁ : Fin n, |R_hat k₁ j| *
              (∑ k₂ : Fin n, |X_abs k₁ k₂| * |R_hat k₂ k|)) * |x_hat k| +
          gje_c₃ fp n * ∑ l : Fin n, |R_hat l j| *
            (∑ k : Fin n, |X_abs l k| * |y k|)) := hGen i
    _ ≤ ∑ j : Fin n, |A_inv i j| *
        (gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |R_hat l j| * |R_hat l k|) * |x_hat k| +
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |R_hat k₁ j| *
            (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ k|)) * |x_hat k| +
        gje_c₃ fp n * ∑ l : Fin n, |R_hat l j| *
          (∑ k : Fin n, |R_inv l k| * |y k|)) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      let T1 : ℝ :=
        gamma fp n * ∑ k : Fin n,
          (∑ l : Fin n, |R_hat l j| * |R_hat l k|) * |x_hat k|
      let T2X : ℝ :=
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |R_hat k₁ j| *
            (∑ k₂ : Fin n, |X_abs k₁ k₂| * |R_hat k₂ k|)) * |x_hat k|
      let T2R : ℝ :=
        gje_c₃ fp n * ∑ k : Fin n,
          (∑ k₁ : Fin n, |R_hat k₁ j| *
            (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ k|)) * |x_hat k|
      let T3X : ℝ :=
        gje_c₃ fp n * ∑ l : Fin n, |R_hat l j| *
          (∑ k : Fin n, |X_abs l k| * |y k|)
      let T3R : ℝ :=
        gje_c₃ fp n * ∑ l : Fin n, |R_hat l j| *
          (∑ k : Fin n, |R_inv l k| * |y k|)
      have hT2 : T2X ≤ T2R := by
        dsimp [T2X, T2R]
        apply mul_le_mul_of_nonneg_left _ hc3
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        apply Finset.sum_le_sum
        intro k₁ _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        intro k₂ _
        exact mul_le_mul_of_nonneg_right (hXdom k₁ k₂) (abs_nonneg _)
      have hT3 : T3X ≤ T3R := by
        dsimp [T3X, T3R]
        apply mul_le_mul_of_nonneg_left _ hc3
        apply Finset.sum_le_sum
        intro l _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hXdom l k) (abs_nonneg _)
      change T1 + T2X + T3X ≤ T1 + T2R + T3R
      linarith

/-- **Corollary 14.6 conditional normwise forward-error route**.

    This converts the componentwise SPD/GJE forward-error certificate to a
    relative 2-norm bound after exposing the remaining Cholesky norm
    aggregation facts as `alpha`, `beta`, and `eta` hypotheses and keeping
    the absolute inverse action as `opNorm2 |A_inv|`.  The second-stage
    coefficient is capped by the source-facing
    `3 n u + gje_c3_quadratic_remainder fp n`; the printed
    `kappa_2(A)^(1/2)` constants remain separate aggregation obligations. -/
theorem gje_spd_forward_error_relative_norm2_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A A_inv R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (alpha beta eta : ℝ)
    (hxpos : 0 < vecNorm2 x)
    (hbeta : 0 ≤ beta) (heta : 0 ≤ eta)
    (hRT_R_x :
      vecNorm2 (fun i : Fin n =>
        ∑ k : Fin n,
          (∑ l : Fin n, |R_hat l i| * |R_hat l k|) * |x_hat k|) ≤
        alpha * vecNorm2 x_hat)
    (hRT_Rinv_R_x :
      vecNorm2 (fun i : Fin n =>
        ∑ k : Fin n,
          (∑ k₁ : Fin n, |R_hat k₁ i| *
            (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ k|)) *
            |x_hat k|) ≤
        beta * vecNorm2 x_hat)
    (hRT_Rinv_y :
      vecNorm2 (fun i : Fin n =>
        ∑ l : Fin n, |R_hat l i| *
          (∑ k : Fin n, |R_inv l k| * |y k|)) ≤
        eta * vecNorm2 x_hat) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
      opNorm2 (fun i j : Fin n => |A_inv i j|) *
      (gamma fp n * alpha +
        (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
          (beta + eta)) *
        (vecNorm2 x_hat / vecNorm2 x) := by
  let e : Fin n → ℝ := fun i => x i - x_hat i
  let AbsAinv : Fin n → Fin n → ℝ := fun i j => |A_inv i j|
  let T1 : Fin n → ℝ := fun i =>
    ∑ k : Fin n,
      (∑ l : Fin n, |R_hat l i| * |R_hat l k|) * |x_hat k|
  let T2 : Fin n → ℝ := fun i =>
    ∑ k : Fin n,
      (∑ k₁ : Fin n, |R_hat k₁ i| *
        (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ k|)) *
        |x_hat k|
  let T3 : Fin n → ℝ := fun i =>
    ∑ l : Fin n, |R_hat l i| *
      (∑ k : Fin n, |R_inv l k| * |y k|)
  let S : Fin n → ℝ := fun i =>
    gamma fp n * T1 i + gje_c₃ fp n * T2 i + gje_c₃ fp n * T3 i
  let C : ℝ := 3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n
  have hForward :=
    gje_spd_forward_error_of_cumulative_product_certificates
      n fp A A_inv R_hat R_inv b y x x_hat N_hat DeltaN start
      hSPD hLU hAinv hn hnpos hn3 hidx hDelta hy hExact hBackwardEq hRinvDom
  have hAbs : ∀ i : Fin n,
      |e i| ≤ matMulVec n AbsAinv S i := by
    intro i
    simpa [e, AbsAinv, S, T1, T2, T3, matMulVec] using hForward i
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hc3 : 0 ≤ gje_c₃ fp n := gje_c3_nonneg fp n hnpos hn3
  have hC : gje_c₃ fp n ≤ C := by
    simpa [C] using gje_c3_le_three_n_u_plus_quadratic_remainder fp n hn3
  have hNormStart :
      vecNorm2 e ≤
        vecNorm2 (matMulVec n AbsAinv S) :=
    vecNorm2_le_of_abs_le e (matMulVec n AbsAinv S) hAbs
  have hOuter :
      vecNorm2 (matMulVec n AbsAinv S) ≤
        opNorm2 AbsAinv * vecNorm2 S :=
    opNorm2Le_opNorm2 AbsAinv S
  have hTri :
      vecNorm2 S ≤
        gamma fp n * vecNorm2 T1 + gje_c₃ fp n * vecNorm2 T2 +
          gje_c₃ fp n * vecNorm2 T3 := by
    have h12 :=
      vecNorm2_add_le
        (fun i : Fin n => gamma fp n * T1 i)
        (fun i : Fin n => gje_c₃ fp n * T2 i)
    have h123 :=
      vecNorm2_add_le
        (fun i : Fin n => gamma fp n * T1 i + gje_c₃ fp n * T2 i)
        (fun i : Fin n => gje_c₃ fp n * T3 i)
    have h1 :
        vecNorm2 (fun i : Fin n => gamma fp n * T1 i) =
          gamma fp n * vecNorm2 T1 := by
      rw [vecNorm2_smul, abs_of_nonneg hgamma]
    have h2 :
        vecNorm2 (fun i : Fin n => gje_c₃ fp n * T2 i) =
          gje_c₃ fp n * vecNorm2 T2 := by
      rw [vecNorm2_smul, abs_of_nonneg hc3]
    have h3 :
        vecNorm2 (fun i : Fin n => gje_c₃ fp n * T3 i) =
          gje_c₃ fp n * vecNorm2 T3 := by
      rw [vecNorm2_smul, abs_of_nonneg hc3]
    calc
      vecNorm2 S
          = vecNorm2 (fun i : Fin n =>
              gamma fp n * T1 i + gje_c₃ fp n * T2 i + gje_c₃ fp n * T3 i) := by rfl
      _
          ≤ vecNorm2 (fun i : Fin n =>
              gamma fp n * T1 i + gje_c₃ fp n * T2 i) +
            vecNorm2 (fun i : Fin n => gje_c₃ fp n * T3 i) := h123
      _ ≤ (vecNorm2 (fun i : Fin n => gamma fp n * T1 i) +
              vecNorm2 (fun i : Fin n => gje_c₃ fp n * T2 i)) +
            vecNorm2 (fun i : Fin n => gje_c₃ fp n * T3 i) := by
              exact add_le_add h12 (le_refl _)
      _ = gamma fp n * vecNorm2 T1 + gje_c₃ fp n * vecNorm2 T2 +
          gje_c₃ fp n * vecNorm2 T3 := by
            rw [h1, h2, h3]
  have hT1 :
      gamma fp n * vecNorm2 T1 ≤
        gamma fp n * (alpha * vecNorm2 x_hat) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [T1] using hRT_R_x) hgamma
  have hT2 :
      gje_c₃ fp n * vecNorm2 T2 ≤
        C * (beta * vecNorm2 x_hat) := by
    calc
      gje_c₃ fp n * vecNorm2 T2 ≤
          gje_c₃ fp n * (beta * vecNorm2 x_hat) := by
            exact mul_le_mul_of_nonneg_left
              (by simpa [T2] using hRT_Rinv_R_x) hc3
      _ ≤ C * (beta * vecNorm2 x_hat) := by
            exact mul_le_mul_of_nonneg_right hC
              (mul_nonneg hbeta (vecNorm2_nonneg x_hat))
  have hT3 :
      gje_c₃ fp n * vecNorm2 T3 ≤
        C * (eta * vecNorm2 x_hat) := by
    calc
      gje_c₃ fp n * vecNorm2 T3 ≤
          gje_c₃ fp n * (eta * vecNorm2 x_hat) := by
            exact mul_le_mul_of_nonneg_left
              (by simpa [T3] using hRT_Rinv_y) hc3
      _ ≤ C * (eta * vecNorm2 x_hat) := by
            exact mul_le_mul_of_nonneg_right hC
              (mul_nonneg heta (vecNorm2_nonneg x_hat))
  have hSBound :
      vecNorm2 S ≤
        (gamma fp n * alpha + C * (beta + eta)) * vecNorm2 x_hat := by
    calc
      vecNorm2 S ≤
          gamma fp n * vecNorm2 T1 + gje_c₃ fp n * vecNorm2 T2 +
            gje_c₃ fp n * vecNorm2 T3 := hTri
      _ ≤ gamma fp n * (alpha * vecNorm2 x_hat) +
            C * (beta * vecNorm2 x_hat) + C * (eta * vecNorm2 x_hat) := by
            nlinarith
      _ = (gamma fp n * alpha + C * (beta + eta)) * vecNorm2 x_hat := by
            ring
  have hVec :
      vecNorm2 e ≤
        opNorm2 AbsAinv *
          ((gamma fp n * alpha + C * (beta + eta)) * vecNorm2 x_hat) := by
    calc
      vecNorm2 e ≤ vecNorm2 (matMulVec n AbsAinv S) := hNormStart
      _ ≤ opNorm2 AbsAinv * vecNorm2 S := hOuter
      _ ≤ opNorm2 AbsAinv *
          ((gamma fp n * alpha + C * (beta + eta)) * vecNorm2 x_hat) := by
            exact mul_le_mul_of_nonneg_left hSBound (opNorm2_nonneg AbsAinv)
  have hFinal :
      vecNorm2 e / vecNorm2 x ≤
        opNorm2 AbsAinv * (gamma fp n * alpha + C * (beta + eta)) *
          (vecNorm2 x_hat / vecNorm2 x) := by
    have hDiv := div_le_div_of_nonneg_right hVec hxpos.le
    calc
      vecNorm2 e / vecNorm2 x ≤
          (opNorm2 AbsAinv *
            ((gamma fp n * alpha + C * (beta + eta)) * vecNorm2 x_hat)) /
            vecNorm2 x := hDiv
      _ = opNorm2 AbsAinv * (gamma fp n * alpha + C * (beta + eta)) *
            (vecNorm2 x_hat / vecNorm2 x) := by
          field_simp [hxpos.ne']
  simpa [e, AbsAinv, C] using hFinal

-- ═══════════════════════════════════════════════════════════════════════════════
-- §14.4.8  Corollary 14.7: Row-Diagonally-Dominant Specialization
-- ═══════════════════════════════════════════════════════════════════════════════

/-- **Corollary 14.6 conditional normwise forward-error route, finite
    aggregation form**.

    This is the forward-error companion to
    `gje_spd_residual_relative_norm2_normConstants_of_cumulative_product_certificates_c3_cap`.
    It reuses the same finite 2-norm quotient constants for the SPD/GJE
    residual aggregation and keeps the absolute inverse action
    `opNorm2 |A_inv|` explicit. -/
theorem gje_spd_forward_error_relative_norm2_normConstants_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A A_inv R_hat R_inv : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A (fun i j => R_hat j i) R_hat (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, R_hat j i * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (R_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) R_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                R_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hRinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |R_inv i j|)
    (hxpos : 0 < vecNorm2 x)
    (hxhatpos : 0 < vecNorm2 x_hat) :
    vecNorm2 (fun i : Fin n => x i - x_hat i) / vecNorm2 x ≤
      opNorm2 (fun i j : Fin n => |A_inv i j|) *
      (gamma fp n *
          gje_spd_firstStage_norm2AggregationConstant n R_hat x_hat +
        (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
          (gje_spd_secondStageX_norm2AggregationConstant n R_hat R_inv x_hat +
            gje_spd_secondStageY_norm2AggregationConstant n R_hat R_inv x_hat y)) *
        (vecNorm2 x_hat / vecNorm2 x) := by
  let alpha : ℝ :=
    gje_spd_firstStage_norm2AggregationConstant n R_hat x_hat
  let beta : ℝ :=
    gje_spd_secondStageX_norm2AggregationConstant n R_hat R_inv x_hat
  let eta : ℝ :=
    gje_spd_secondStageY_norm2AggregationConstant n R_hat R_inv x_hat y
  let T1 : Fin n → ℝ := fun i =>
    ∑ k : Fin n,
      (∑ l : Fin n, |R_hat l i| * |R_hat l k|) * |x_hat k|
  let T2 : Fin n → ℝ := fun i =>
    ∑ k : Fin n,
      (∑ k₁ : Fin n, |R_hat k₁ i| *
        (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ k|)) *
        |x_hat k|
  let T3 : Fin n → ℝ := fun i =>
    ∑ l : Fin n, |R_hat l i| *
      (∑ k : Fin n, |R_inv l k| * |y k|)
  have hbeta_nonneg : 0 ≤ beta := by
    have hdiv : 0 ≤ vecNorm2 T2 / vecNorm2 x_hat :=
      div_nonneg (vecNorm2_nonneg T2) hxhatpos.le
    simpa [beta, gje_spd_secondStageX_norm2AggregationConstant, T2] using hdiv
  have heta_nonneg : 0 ≤ eta := by
    have hdiv : 0 ≤ vecNorm2 T3 / vecNorm2 x_hat :=
      div_nonneg (vecNorm2_nonneg T3) hxhatpos.le
    simpa [eta, gje_spd_secondStageY_norm2AggregationConstant, T3] using hdiv
  have halpha_eq : alpha * vecNorm2 x_hat = vecNorm2 T1 := by
    simp [alpha, gje_spd_firstStage_norm2AggregationConstant, T1]
    field_simp [hxhatpos.ne']
  have hbeta_eq : beta * vecNorm2 x_hat = vecNorm2 T2 := by
    simp [beta, gje_spd_secondStageX_norm2AggregationConstant, T2]
    field_simp [hxhatpos.ne']
  have heta_eq : eta * vecNorm2 x_hat = vecNorm2 T3 := by
    simp [eta, gje_spd_secondStageY_norm2AggregationConstant, T3]
    field_simp [hxhatpos.ne']
  have hRT_R_x :
      vecNorm2 (fun i : Fin n =>
        ∑ k : Fin n,
          (∑ l : Fin n, |R_hat l i| * |R_hat l k|) * |x_hat k|) ≤
        alpha * vecNorm2 x_hat := by
    change vecNorm2 T1 ≤ alpha * vecNorm2 x_hat
    exact le_of_eq halpha_eq.symm
  have hRT_Rinv_R_x :
      vecNorm2 (fun i : Fin n =>
        ∑ k : Fin n,
          (∑ k₁ : Fin n, |R_hat k₁ i| *
            (∑ k₂ : Fin n, |R_inv k₁ k₂| * |R_hat k₂ k|)) *
            |x_hat k|) ≤
        beta * vecNorm2 x_hat := by
    change vecNorm2 T2 ≤ beta * vecNorm2 x_hat
    exact le_of_eq hbeta_eq.symm
  have hRT_Rinv_y :
      vecNorm2 (fun i : Fin n =>
        ∑ l : Fin n, |R_hat l i| *
          (∑ k : Fin n, |R_inv l k| * |y k|)) ≤
        eta * vecNorm2 x_hat := by
    change vecNorm2 T3 ≤ eta * vecNorm2 x_hat
    exact le_of_eq heta_eq.symm
  have hbase :=
    gje_spd_forward_error_relative_norm2_of_cumulative_product_certificates_c3_cap
      n fp A A_inv R_hat R_inv b y x x_hat N_hat DeltaN start
      hSPD hLU hAinv hn hnpos hn3 hidx hDelta hy hExact hBackwardEq hRinvDom
      alpha beta eta hxpos hbeta_nonneg heta_nonneg
      hRT_R_x hRT_Rinv_R_x hRT_Rinv_y
  simpa [alpha, beta, eta] using hbase

/-- **Corollary 14.7 conditional row-dominant certificate route**.

    For a row-diagonally-dominant upper factor, the existing Chapter 9
    Lemma-8.8 route gives the source-facing `‖|L||U|‖∞ ≤ (2n-1)‖A‖∞`
    first-stage budget.  The GJE residual side then specializes the proved
    cumulative-product certificate route by exposing the remaining source
    comparison `|N̂_n⋯N̂_2| ≤ |Û⁻¹|` as `hUinvDom`.

    This is deliberately conditional: the theorem records the row-dominant
    bridge and the componentwise residual transfer, while the preservation of
    row diagonal dominance by the computed elimination path remains a separate
    source-instantiation obligation. -/
theorem gje_rowDiagDominantUpper_residual_of_cumulative_product_certificates
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|) :
    higham9_17_rowDiagDom_absLU_bound n A L_hat U_hat ∧
      ∀ i : Fin n,
        |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        gamma fp n * ∑ j : Fin n,
          (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
        gje_c₃ fp n * ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n,
              |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| +
        gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) := by
  have hAbsLU : higham9_17_rowDiagDom_absLU_bound n A L_hat U_hat :=
    higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec
      hnpos A L_hat U_hat hLUExact hURow
  refine ⟨hAbsLU, ?_⟩
  let X_abs : Fin n → Fin n → ℝ :=
    gje_cumulative_product n (fun s a b => |N_hat s a b|)
      start (start + (n - 1))
  let U_inv : Fin n → Fin n → ℝ := nonsingInv n U_hat
  have hXdom : ∀ i j : Fin n, |X_abs i j| ≤ |U_inv i j| := by
    intro i j
    simpa [X_abs, U_inv] using hUinvDom i j
  have hc3 : 0 ≤ gje_c₃ fp n := gje_c3_nonneg fp n hnpos hn3
  have hGen :
      ∀ i : Fin n,
        |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        gamma fp n * ∑ j : Fin n,
          (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| +
        gje_c₃ fp n * ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) *
            |x_hat j| +
        gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n, |X_abs k j| * |y j|) := by
    simpa [X_abs] using
      gje_overall_residual_of_cumulative_product_certificates
        n fp A L_hat U_hat b y x_hat N_hat DeltaN start
        hLU hn hnpos hn3 hidx hDelta hy hBackwardEq
  intro i
  let T1 : ℝ :=
    gamma fp n * ∑ j : Fin n,
      (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j|
  let T2X : ℝ :=
    gje_c₃ fp n * ∑ j : Fin n,
      (∑ k₁ : Fin n, |L_hat i k₁| *
        (∑ k₂ : Fin n, |X_abs k₁ k₂| * |U_hat k₂ j|)) *
        |x_hat j|
  let T2U : ℝ :=
    gje_c₃ fp n * ∑ j : Fin n,
      (∑ k₁ : Fin n, |L_hat i k₁| *
        (∑ k₂ : Fin n, |U_inv k₁ k₂| * |U_hat k₂ j|)) *
        |x_hat j|
  let T3X : ℝ :=
    gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
      (∑ j : Fin n, |X_abs k j| * |y j|)
  let T3U : ℝ :=
    gje_c₃ fp n * ∑ k : Fin n, |L_hat i k| *
      (∑ j : Fin n, |U_inv k j| * |y j|)
  have hT2 : T2X ≤ T2U := by
    dsimp [T2X, T2U]
    apply mul_le_mul_of_nonneg_left _ hc3
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply Finset.sum_le_sum
    intro k₁ _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Finset.sum_le_sum
    intro k₂ _
    exact mul_le_mul_of_nonneg_right (hXdom k₁ k₂) (abs_nonneg _)
  have hT3 : T3X ≤ T3U := by
    dsimp [T3X, T3U]
    apply mul_le_mul_of_nonneg_left _ hc3
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (hXdom k j) (abs_nonneg _)
  have hResidual :
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤ T1 + T2U + T3U := by
    calc
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤ T1 + T2X + T3X := by
        simpa [T1, T2X, T3X] using hGen i
      _ ≤ T1 + T2U + T3X := by
        linarith
      _ ≤ T1 + T2U + T3U := by
        linarith
  simpa [T1, T2U, T3U, U_inv] using hResidual

/-- **Corollary 14.7 conditional infinity-norm residual route**.

    This normwise wrapper uses the row-dominant `|| |L| |U| ||_inf` budget
    supplied by `gje_rowDiagDominantUpper_residual_of_cumulative_product_certificates`
    for the first-stage term, caps the GJE second-stage coefficient by
    `3 n u + gje_c3_quadratic_remainder fp n`, and exposes the two remaining
    second-stage norm aggregations as `beta` and `eta` hypotheses. -/
theorem gje_rowDiagDominantUpper_residual_relative_infNorm_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|)
    (beta eta : ℝ)
    (hApos : 0 < infNorm A)
    (hxpos : 0 < infNormVec x_hat)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hSecondU_x : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| ≤
      beta * infNorm A * infNormVec x_hat)
    (hSecondU_y : ∀ i : Fin n,
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) ≤
      eta * infNorm A * infNormVec x_hat) :
    infNormVec (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (infNorm A * infNormVec x_hat) ≤
      gamma fp n * (2 * (n : ℝ) - 1) +
        (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
          (beta + eta) := by
  let r : Fin n → ℝ := fun i => b i - ∑ j : Fin n, A i j * x_hat j
  let W : Fin n → Fin n → ℝ :=
    matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let x_abs : Fin n → ℝ := absVec n x_hat
  let denom : ℝ := infNorm A * infNormVec x_hat
  let C : ℝ := 3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n
  have hLU : LUBackwardError n A L_hat U_hat (gamma fp n) :=
    higham9_LUFactSpec_to_LUBackwardError_gamma fp n hn hLUExact
  have hPack :=
    gje_rowDiagDominantUpper_residual_of_cumulative_product_certificates
      n fp A L_hat U_hat b y x_hat N_hat DeltaN start
      hLUExact hLU hURow hn hnpos hn3 hidx hDelta hy hBackwardEq hUinvDom
  have hAbsLU : higham9_17_rowDiagDom_absLU_bound n A L_hat U_hat := hPack.1
  have hResidual := hPack.2
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hc3 : 0 ≤ gje_c₃ fp n := gje_c3_nonneg fp n hnpos hn3
  have hC : gje_c₃ fp n ≤ C := by
    simpa [C] using gje_c3_le_three_n_u_plus_quadratic_remainder fp n hn3
  have hC_nonneg : 0 ≤ C := le_trans hc3 hC
  have hdenom_pos : 0 < denom := by
    exact mul_pos hApos hxpos
  have hrowCoeff_nonneg : 0 ≤ 2 * (n : ℝ) - 1 := by
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    nlinarith
  have hT1_bound : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j| ≤
        (2 * (n : ℝ) - 1) * infNorm A * infNormVec x_hat := by
    intro i
    have hsum_eq :
        (∑ j : Fin n,
          (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j|) =
          matMulVec n W x_abs i := by
      simp [W, x_abs, matMulVec, matMul, absMatrix, absVec]
    have hcomponent :
        matMulVec n W x_abs i ≤ infNorm W * infNormVec x_abs := by
      exact (le_abs_self _).trans
        ((abs_le_infNormVec (matMulVec n W x_abs) i).trans
          (infNormVec_matMulVec_le hnpos W x_abs))
    calc
      ∑ j : Fin n,
          (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j|
          = matMulVec n W x_abs i := hsum_eq
      _ ≤ infNorm W * infNormVec x_abs := hcomponent
      _ ≤ ((2 * (n : ℝ) - 1) * infNorm A) * infNormVec x_abs := by
            exact mul_le_mul_of_nonneg_right hAbsLU (infNormVec_nonneg x_abs)
      _ = (2 * (n : ℝ) - 1) * infNorm A * infNormVec x_hat := by
            rw [infNormVec_absVec hnpos x_hat]
  have hcomponent_bound : ∀ i : Fin n,
      |r i| ≤
        (gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta)) * denom := by
    intro i
    let S1 : ℝ :=
      ∑ j : Fin n,
        (∑ k : Fin n, |L_hat i k| * |U_hat k j|) * |x_hat j|
    let S2 : ℝ :=
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
    let S3 : ℝ :=
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|)
    have hS1 : S1 ≤ (2 * (n : ℝ) - 1) * denom := by
      calc
        S1 ≤ (2 * (n : ℝ) - 1) * infNorm A * infNormVec x_hat := by
          simpa [S1] using hT1_bound i
        _ = (2 * (n : ℝ) - 1) * denom := by
          simp [denom]
          ring
    have hS2 : S2 ≤ beta * denom := by
      calc
        S2 ≤ beta * infNorm A * infNormVec x_hat := by
          simpa [S2] using hSecondU_x i
        _ = beta * denom := by
          simp [denom]
          ring
    have hS3 : S3 ≤ eta * denom := by
      calc
        S3 ≤ eta * infNorm A * infNormVec x_hat := by
          simpa [S3] using hSecondU_y i
        _ = eta * denom := by
          simp [denom]
          ring
    have hS2_nonneg : 0 ≤ S2 := by
      dsimp [S2]
      apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg
        (Finset.sum_nonneg (fun k₁ _ =>
          mul_nonneg (abs_nonneg _)
            (Finset.sum_nonneg (fun k₂ _ =>
              mul_nonneg (abs_nonneg _) (abs_nonneg _)))))
        (abs_nonneg _)
    have hS3_nonneg : 0 ≤ S3 := by
      dsimp [S3]
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (abs_nonneg _)
        (Finset.sum_nonneg (fun j _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    have h1 :
        gamma fp n * S1 ≤
          gamma fp n * ((2 * (n : ℝ) - 1) * denom) :=
      mul_le_mul_of_nonneg_left hS1 hgamma
    have h2 :
        gje_c₃ fp n * S2 ≤ C * (beta * denom) := by
      calc
        gje_c₃ fp n * S2 ≤ C * S2 :=
          mul_le_mul_of_nonneg_right hC hS2_nonneg
        _ ≤ C * (beta * denom) :=
          mul_le_mul_of_nonneg_left hS2 hC_nonneg
    have h3 :
        gje_c₃ fp n * S3 ≤ C * (eta * denom) := by
      calc
        gje_c₃ fp n * S3 ≤ C * S3 :=
          mul_le_mul_of_nonneg_right hC hS3_nonneg
        _ ≤ C * (eta * denom) :=
          mul_le_mul_of_nonneg_left hS3 hC_nonneg
    calc
      |r i| ≤ gamma fp n * S1 + gje_c₃ fp n * S2 + gje_c₃ fp n * S3 := by
        simpa [r, S1, S2, S3] using hResidual i
      _ ≤ gamma fp n * ((2 * (n : ℝ) - 1) * denom) +
            C * (beta * denom) + C * (eta * denom) := by
            nlinarith
      _ = (gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta)) * denom := by
            ring
  have hscalar_nonneg :
      0 ≤ (gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta)) * denom := by
    have hsum_nonneg :
        0 ≤ gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta) :=
      add_nonneg
        (mul_nonneg hgamma hrowCoeff_nonneg)
        (mul_nonneg hC_nonneg (add_nonneg hbeta heta))
    exact mul_nonneg hsum_nonneg hdenom_pos.le
  have hVec :
      infNormVec r ≤
        (gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta)) * denom :=
    infNormVec_le_of_abs_le r hcomponent_bound hscalar_nonneg
  have hFinal :
      infNormVec r / denom ≤
        gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta) := by
    have hDiv := div_le_div_of_nonneg_right hVec hdenom_pos.le
    calc
      infNormVec r / denom ≤
          ((gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta)) * denom) /
            denom := hDiv
      _ = gamma fp n * (2 * (n : ℝ) - 1) + C * (beta + eta) := by
          field_simp [hdenom_pos.ne']
  simpa [r, denom, C] using hFinal

/-- **Corollary 14.7 conditional infinity-norm forward-error route**.

    This composes the row-dominant relative residual bridge with the exact
    inverse action `x - x_hat = A_inv (b - A x_hat)`.  The result keeps
    the same explicit `beta`/`eta` second-stage aggregation hypotheses and
    an explicit `infNorm A_inv * infNorm A` condition factor. -/
theorem gje_rowDiagDominantUpper_forward_error_relative_infNorm_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hAinv : IsLeftInverse n A A_inv)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|)
    (beta eta : ℝ)
    (hApos : 0 < infNorm A)
    (hxhatpos : 0 < infNormVec x_hat)
    (hxpos : 0 < infNormVec x)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hSecondU_x : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| ≤
      beta * infNorm A * infNormVec x_hat)
    (hSecondU_y : ∀ i : Fin n,
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) ≤
      eta * infNorm A * infNormVec x_hat) :
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x ≤
      infNorm A_inv * infNorm A *
        (gamma fp n * (2 * (n : ℝ) - 1) +
          (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (beta + eta)) *
        (infNormVec x_hat / infNormVec x) := by
  let e : Fin n → ℝ := fun i => x i - x_hat i
  let r : Fin n → ℝ := fun i => b i - ∑ j : Fin n, A i j * x_hat j
  let B : ℝ :=
    gamma fp n * (2 * (n : ℝ) - 1) +
      (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) * (beta + eta)
  let denom : ℝ := infNorm A * infNormVec x_hat
  have hResRel :=
    gje_rowDiagDominantUpper_residual_relative_infNorm_of_cumulative_product_certificates_c3_cap
      n fp A L_hat U_hat b y x_hat N_hat DeltaN start
      hLUExact hURow hn hnpos hn3 hidx hDelta hy hBackwardEq hUinvDom
      beta eta hApos hxhatpos hbeta heta hSecondU_x hSecondU_y
  have hdenom_pos : 0 < denom := mul_pos hApos hxhatpos
  have hResNorm : infNormVec r ≤ B * denom := by
    have hmul := mul_le_mul_of_nonneg_right
      (by simpa [r, denom, B] using hResRel) hdenom_pos.le
    calc
      infNormVec r = (infNormVec r / denom) * denom := by
        field_simp [hdenom_pos.ne']
      _ ≤ B * denom := by
        simpa using hmul
  have hDiff : ∀ i : Fin n, e i = ∑ j : Fin n, A_inv i j * r j := by
    intro i
    have hRHS_expand : ∑ j : Fin n, A_inv i j * r j =
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x k) -
        ∑ j : Fin n, A_inv i j * (∑ k : Fin n, A j k * x_hat k) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hExact j]
      simp [r]
      ring
    have hFirst : ∑ j : Fin n, A_inv i j *
        (∑ k : Fin n, A j k * x k) = x i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hSecond : ∑ j : Fin n, A_inv i j *
        (∑ k : Fin n, A j k * x_hat k) = x_hat i := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hAinv i]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    calc
      e i = x i - x_hat i := rfl
      _ = ∑ j : Fin n, A_inv i j * r j := by
        rw [hRHS_expand, hFirst, hSecond]
  have hForwardNorm : infNormVec e ≤ infNorm A_inv * infNormVec r := by
    apply infNormVec_le_of_abs_le
    · intro i
      calc
        |e i| = |∑ j : Fin n, A_inv i j * r j| := by rw [hDiff i]
        _ ≤ ∑ j : Fin n, |A_inv i j * r j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |A_inv i j| * |r j| := by
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_mul]
        _ ≤ ∑ j : Fin n, |A_inv i j| * infNormVec r := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_left (abs_le_infNormVec r j) (abs_nonneg _)
        _ = (∑ j : Fin n, |A_inv i j|) * infNormVec r := by
              rw [Finset.sum_mul]
        _ ≤ infNorm A_inv * infNormVec r := by
              exact mul_le_mul_of_nonneg_right
                (row_sum_le_infNorm A_inv i) (infNormVec_nonneg r)
    · exact mul_nonneg (infNorm_nonneg A_inv) (infNormVec_nonneg r)
  have hEbound :
      infNormVec e ≤ infNorm A_inv * (B * denom) := by
    calc
      infNormVec e ≤ infNorm A_inv * infNormVec r := hForwardNorm
      _ ≤ infNorm A_inv * (B * denom) :=
        mul_le_mul_of_nonneg_left hResNorm (infNorm_nonneg A_inv)
  have hFinal :
      infNormVec e / infNormVec x ≤
        infNorm A_inv * infNorm A * B *
          (infNormVec x_hat / infNormVec x) := by
    have hDiv := div_le_div_of_nonneg_right hEbound hxpos.le
    calc
      infNormVec e / infNormVec x ≤
          (infNorm A_inv * (B * denom)) / infNormVec x := hDiv
      _ = infNorm A_inv * infNorm A * B *
            (infNormVec x_hat / infNormVec x) := by
          simp [denom]
          field_simp [hxpos.ne']
  simpa [e, B] using hFinal

/-- **Corollary 14.7 conditional infinity-norm forward-error route, kappa form**.

    This is the source-facing condition-number wrapper for
    `gje_rowDiagDominantUpper_forward_error_relative_infNorm_of_cumulative_product_certificates_c3_cap`.
    It rewrites the raw `infNorm A_inv * infNorm A` amplification as
    `kappaInf n _ A A_inv`, leaving the same explicit certificate and
    aggregation hypotheses. -/
theorem gje_rowDiagDominantUpper_forward_error_relative_infNorm_kappaInf_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hAinv : IsLeftInverse n A A_inv)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|)
    (beta eta : ℝ)
    (hApos : 0 < infNorm A)
    (hxhatpos : 0 < infNormVec x_hat)
    (hxpos : 0 < infNormVec x)
    (hbeta : 0 ≤ beta)
    (heta : 0 ≤ eta)
    (hSecondU_x : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| ≤
      beta * infNorm A * infNormVec x_hat)
    (hSecondU_y : ∀ i : Fin n,
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) ≤
      eta * infNorm A * infNormVec x_hat) :
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x ≤
      kappaInf n (Nat.lt_of_lt_of_le Nat.zero_lt_one hnpos) A A_inv *
        (gamma fp n * (2 * (n : ℝ) - 1) +
          (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (beta + eta)) *
        (infNormVec x_hat / infNormVec x) := by
  have hraw :=
    gje_rowDiagDominantUpper_forward_error_relative_infNorm_of_cumulative_product_certificates_c3_cap
      n fp A A_inv L_hat U_hat b y x x_hat N_hat DeltaN start
      hLUExact hAinv hURow hn hnpos hn3 hidx hDelta hy hExact hBackwardEq hUinvDom
      beta eta hApos hxhatpos hxpos hbeta heta hSecondU_x hSecondU_y
  calc
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x ≤
        infNorm A_inv * infNorm A *
          (gamma fp n * (2 * (n : ℝ) - 1) +
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
              (beta + eta)) *
          (infNormVec x_hat / infNormVec x) := hraw
    _ =
        kappaInf n (Nat.lt_of_lt_of_le Nat.zero_lt_one hnpos) A A_inv *
          (gamma fp n * (2 * (n : ℝ) - 1) +
            (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
              (beta + eta)) *
          (infNormVec x_hat / infNormVec x) := by
        rw [kappaInf_eq_infNorm_mul_infNorm n
          (Nat.lt_of_lt_of_le Nat.zero_lt_one hnpos) A A_inv]
        ring

/-- Canonical finite row-sum constant for the first second-stage aggregation
    term in the row-dominant Corollary 14.7 forward-error route. -/
noncomputable def gje_rowDiagDominantUpper_secondStageX_rowsumConstant
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (x_hat : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n,
      (∑ k₁ : Fin n, |L_hat i k₁| *
        (∑ k₂ : Fin n,
          |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|) /
    (infNorm A * infNormVec x_hat)

/-- Canonical finite row-sum constant for the second second-stage aggregation
    term in the row-dominant Corollary 14.7 forward-error route. -/
noncomputable def gje_rowDiagDominantUpper_secondStageY_rowsumConstant
    (n : ℕ)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (x_hat y : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, ∑ k : Fin n, |L_hat i k| *
      (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|)) /
    (infNorm A * infNormVec x_hat)

/-- **Corollary 14.7 conditional infinity-norm residual route, finite
    row-sum aggregation form**.

    This wrapper discharges the explicit `beta` and `eta` aggregation
    hypotheses in the row-dominant residual theorem by using canonical finite
    row-sum constants. It is the residual-side companion to the `kappaInf`
    forward-error row-sum wrapper below. -/
theorem gje_rowDiagDominantUpper_residual_relative_infNorm_rowsum_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|)
    (hApos : 0 < infNorm A)
    (hxhatpos : 0 < infNormVec x_hat) :
    infNormVec (fun i : Fin n => b i - ∑ j : Fin n, A i j * x_hat j) /
        (infNorm A * infNormVec x_hat) ≤
      gamma fp n * (2 * (n : ℝ) - 1) +
        (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
          (gje_rowDiagDominantUpper_secondStageX_rowsumConstant
              n A L_hat U_hat x_hat +
            gje_rowDiagDominantUpper_secondStageY_rowsumConstant
              n A L_hat U_hat x_hat y) := by
  let beta : ℝ :=
    gje_rowDiagDominantUpper_secondStageX_rowsumConstant n A L_hat U_hat x_hat
  let eta : ℝ :=
    gje_rowDiagDominantUpper_secondStageY_rowsumConstant n A L_hat U_hat x_hat y
  let denom : ℝ := infNorm A * infNormVec x_hat
  let Xrow : Fin n → ℝ := fun i =>
    ∑ j : Fin n,
      (∑ k₁ : Fin n, |L_hat i k₁| *
        (∑ k₂ : Fin n,
          |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
  let Yrow : Fin n → ℝ := fun i =>
    ∑ k : Fin n, |L_hat i k| *
      (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|)
  have hdenom_pos : 0 < denom := mul_pos hApos hxhatpos
  have hXrow_nonneg : ∀ i : Fin n, 0 ≤ Xrow i := by
    intro i
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg
        (Finset.sum_nonneg (fun k₁ _ =>
          mul_nonneg (abs_nonneg _)
            (Finset.sum_nonneg (fun k₂ _ =>
              mul_nonneg (abs_nonneg _) (abs_nonneg _)))))
        (abs_nonneg _))
  have hYrow_nonneg : ∀ i : Fin n, 0 ≤ Yrow i := by
    intro i
    exact Finset.sum_nonneg (fun k _ =>
      mul_nonneg (abs_nonneg _)
        (Finset.sum_nonneg (fun j _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  have hbeta_nonneg : 0 ≤ beta := by
    have hsum : 0 ≤ ∑ i : Fin n, Xrow i :=
      Finset.sum_nonneg (fun i _ => hXrow_nonneg i)
    have hdiv : 0 ≤ (∑ i : Fin n, Xrow i) / denom :=
      div_nonneg hsum hdenom_pos.le
    simpa [beta, gje_rowDiagDominantUpper_secondStageX_rowsumConstant,
      Xrow, denom] using hdiv
  have heta_nonneg : 0 ≤ eta := by
    have hsum : 0 ≤ ∑ i : Fin n, Yrow i :=
      Finset.sum_nonneg (fun i _ => hYrow_nonneg i)
    have hdiv : 0 ≤ (∑ i : Fin n, Yrow i) / denom :=
      div_nonneg hsum hdenom_pos.le
    simpa [eta, gje_rowDiagDominantUpper_secondStageY_rowsumConstant,
      Yrow, denom] using hdiv
  have hbeta_eq :
      beta * infNorm A * infNormVec x_hat = ∑ i : Fin n, Xrow i := by
    simp [beta, gje_rowDiagDominantUpper_secondStageX_rowsumConstant,
      Xrow]
    field_simp [hdenom_pos.ne']
  have heta_eq :
      eta * infNorm A * infNormVec x_hat = ∑ i : Fin n, Yrow i := by
    simp [eta, gje_rowDiagDominantUpper_secondStageY_rowsumConstant,
      Yrow]
    field_simp [hdenom_pos.ne']
  have hSecondU_x : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| ≤
      beta * infNorm A * infNormVec x_hat := by
    intro i
    calc
      ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n,
              |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
          = Xrow i := rfl
      _ ≤ ∑ r : Fin n, Xrow r :=
          Finset.single_le_sum (fun r _ => hXrow_nonneg r) (Finset.mem_univ i)
      _ = beta * infNorm A * infNormVec x_hat := by
          rw [hbeta_eq]
  have hSecondU_y : ∀ i : Fin n,
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) ≤
      eta * infNorm A * infNormVec x_hat := by
    intro i
    calc
      ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|)
          = Yrow i := rfl
      _ ≤ ∑ r : Fin n, Yrow r :=
          Finset.single_le_sum (fun r _ => hYrow_nonneg r) (Finset.mem_univ i)
      _ = eta * infNorm A * infNormVec x_hat := by
          rw [heta_eq]
  have hbase :=
    gje_rowDiagDominantUpper_residual_relative_infNorm_of_cumulative_product_certificates_c3_cap
      n fp A L_hat U_hat b y x_hat N_hat DeltaN start
      hLUExact hURow hn hnpos hn3 hidx hDelta hy hBackwardEq hUinvDom
      beta eta hApos hxhatpos hbeta_nonneg heta_nonneg hSecondU_x hSecondU_y
  simpa [beta, eta] using hbase

/-- **Corollary 14.7 conditional infinity-norm forward-error route, finite
    row-sum aggregation form**.

    This wrapper discharges the explicit `beta` and `eta` aggregation
    hypotheses in the `kappaInf` row-dominant forward-error theorem by using
    canonical finite row-sum constants.  It still keeps the source-critical
    row-dominance, cumulative-product domination, exact backward equation, and
    rounded per-stage certificate hypotheses explicit. -/
theorem gje_rowDiagDominantUpper_forward_error_relative_infNorm_kappaInf_rowsum_of_cumulative_product_certificates_c3_cap
    (n : ℕ) (fp : FPModel)
    (A A_inv L_hat U_hat : Fin n → Fin n → ℝ)
    (b y x x_hat : Fin n → ℝ)
    (N_hat DeltaN : Fin n → Fin n → Fin n → ℝ)
    (start : ℕ)
    (hLUExact : LUFactSpec n A L_hat U_hat)
    (hAinv : IsLeftInverse n A A_inv)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hn : gammaValid fp n)
    (hnpos : 1 ≤ n)
    (hn3 : gammaValid fp 3)
    (hidx : ∀ r : Fin (n - 1),
      start + ((n - 1) - 1 - r.val) < n)
    (hDelta : ∀ r : Fin (n - 1), ∀ i j : Fin n,
      |DeltaN (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j| ≤
        gamma fp 3 *
          |N_hat (Fin.mk (start + ((n - 1) - 1 - r.val)) (hidx r)) i j|)
    (hy : ∀ i : Fin n, ∑ j : Fin n, L_hat i j * y j = b i)
    (hExact : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hBackwardEq : ∀ i : Fin n,
      ∑ j : Fin n,
          (U_hat i j +
            (matMul n
                (gje_cumulative_product n
                  (fun k a b => N_hat k a b + DeltaN k a b)
                  start (start + (n - 1))) U_hat i j -
              matMul n
                (gje_cumulative_product n N_hat start (start + (n - 1)))
                U_hat i j)) *
            x_hat j =
        y i +
          (matMulVec n
              (gje_cumulative_product n
                (fun k a b => N_hat k a b + DeltaN k a b)
                start (start + (n - 1))) y i -
            matMulVec n
              (gje_cumulative_product n N_hat start (start + (n - 1))) y i))
    (hUinvDom : ∀ i j : Fin n,
      |gje_cumulative_product n (fun s a b => |N_hat s a b|)
        start (start + (n - 1)) i j| ≤ |nonsingInv n U_hat i j|)
    (hApos : 0 < infNorm A)
    (hxhatpos : 0 < infNormVec x_hat)
    (hxpos : 0 < infNormVec x) :
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x ≤
      kappaInf n (Nat.lt_of_lt_of_le Nat.zero_lt_one hnpos) A A_inv *
        (gamma fp n * (2 * (n : ℝ) - 1) +
          (3 * (n : ℝ) * fp.u + gje_c3_quadratic_remainder fp n) *
            (gje_rowDiagDominantUpper_secondStageX_rowsumConstant
                n A L_hat U_hat x_hat +
              gje_rowDiagDominantUpper_secondStageY_rowsumConstant
                n A L_hat U_hat x_hat y)) *
        (infNormVec x_hat / infNormVec x) := by
  let beta : ℝ :=
    gje_rowDiagDominantUpper_secondStageX_rowsumConstant n A L_hat U_hat x_hat
  let eta : ℝ :=
    gje_rowDiagDominantUpper_secondStageY_rowsumConstant n A L_hat U_hat x_hat y
  let denom : ℝ := infNorm A * infNormVec x_hat
  let Xrow : Fin n → ℝ := fun i =>
    ∑ j : Fin n,
      (∑ k₁ : Fin n, |L_hat i k₁| *
        (∑ k₂ : Fin n,
          |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
  let Yrow : Fin n → ℝ := fun i =>
    ∑ k : Fin n, |L_hat i k| *
      (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|)
  have hdenom_pos : 0 < denom := mul_pos hApos hxhatpos
  have hXrow_nonneg : ∀ i : Fin n, 0 ≤ Xrow i := by
    intro i
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg
        (Finset.sum_nonneg (fun k₁ _ =>
          mul_nonneg (abs_nonneg _)
            (Finset.sum_nonneg (fun k₂ _ =>
              mul_nonneg (abs_nonneg _) (abs_nonneg _)))))
        (abs_nonneg _))
  have hYrow_nonneg : ∀ i : Fin n, 0 ≤ Yrow i := by
    intro i
    exact Finset.sum_nonneg (fun k _ =>
      mul_nonneg (abs_nonneg _)
        (Finset.sum_nonneg (fun j _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))))
  have hbeta_nonneg : 0 ≤ beta := by
    have hsum : 0 ≤ ∑ i : Fin n, Xrow i :=
      Finset.sum_nonneg (fun i _ => hXrow_nonneg i)
    have hdiv : 0 ≤ (∑ i : Fin n, Xrow i) / denom :=
      div_nonneg hsum hdenom_pos.le
    simpa [beta, gje_rowDiagDominantUpper_secondStageX_rowsumConstant,
      Xrow, denom] using hdiv
  have heta_nonneg : 0 ≤ eta := by
    have hsum : 0 ≤ ∑ i : Fin n, Yrow i :=
      Finset.sum_nonneg (fun i _ => hYrow_nonneg i)
    have hdiv : 0 ≤ (∑ i : Fin n, Yrow i) / denom :=
      div_nonneg hsum hdenom_pos.le
    simpa [eta, gje_rowDiagDominantUpper_secondStageY_rowsumConstant,
      Yrow, denom] using hdiv
  have hbeta_eq :
      beta * infNorm A * infNormVec x_hat = ∑ i : Fin n, Xrow i := by
    simp [beta, gje_rowDiagDominantUpper_secondStageX_rowsumConstant,
      Xrow]
    field_simp [hdenom_pos.ne']
  have heta_eq :
      eta * infNorm A * infNormVec x_hat = ∑ i : Fin n, Yrow i := by
    simp [eta, gje_rowDiagDominantUpper_secondStageY_rowsumConstant,
      Yrow]
    field_simp [hdenom_pos.ne']
  have hSecondU_x : ∀ i : Fin n,
      ∑ j : Fin n,
        (∑ k₁ : Fin n, |L_hat i k₁| *
          (∑ k₂ : Fin n,
            |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j| ≤
      beta * infNorm A * infNormVec x_hat := by
    intro i
    calc
      ∑ j : Fin n,
          (∑ k₁ : Fin n, |L_hat i k₁| *
            (∑ k₂ : Fin n,
              |nonsingInv n U_hat k₁ k₂| * |U_hat k₂ j|)) * |x_hat j|
          = Xrow i := rfl
      _ ≤ ∑ r : Fin n, Xrow r :=
          Finset.single_le_sum (fun r _ => hXrow_nonneg r) (Finset.mem_univ i)
      _ = beta * infNorm A * infNormVec x_hat := by
          rw [hbeta_eq]
  have hSecondU_y : ∀ i : Fin n,
      ∑ k : Fin n, |L_hat i k| *
        (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|) ≤
      eta * infNorm A * infNormVec x_hat := by
    intro i
    calc
      ∑ k : Fin n, |L_hat i k| *
          (∑ j : Fin n, |nonsingInv n U_hat k j| * |y j|)
          = Yrow i := rfl
      _ ≤ ∑ r : Fin n, Yrow r :=
          Finset.single_le_sum (fun r _ => hYrow_nonneg r) (Finset.mem_univ i)
      _ = eta * infNorm A * infNormVec x_hat := by
          rw [heta_eq]
  have hbase :=
    gje_rowDiagDominantUpper_forward_error_relative_infNorm_kappaInf_of_cumulative_product_certificates_c3_cap
      n fp A A_inv L_hat U_hat b y x x_hat N_hat DeltaN start
      hLUExact hAinv hURow hn hnpos hn3 hidx hDelta hy hExact hBackwardEq hUinvDom
      beta eta hApos hxhatpos hxpos hbeta_nonneg heta_nonneg hSecondU_x hSecondU_y
  simpa [beta, eta] using hbase

end NumStability
