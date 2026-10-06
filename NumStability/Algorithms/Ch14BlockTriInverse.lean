-- Algorithms/Ch14BlockTriInverse.lean
--
-- Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
-- Chapter 14 (Matrix Inversion), §14.2.2, Lemma 14.2, eqs. (14.10)-(14.13),
-- page 265-266.
--
-- Method 1B (block triangular inversion) right residual.  The reusable
-- certificate route in `MatrixInversion.lean`
-- (`triInv_method1B_right_residual`, `triInv_method1B_*_of_row_certificates`)
-- DERIVES the residual bound (14.10) from row-local backward-error
-- certificates, but leaves the derivation of those certificates from the
-- block loop as an open dependency.
--
-- This file DISCHARGES that dependency for the two-block partition that
-- Higham's proof uses ("It suffices to verify the inequality with j = 1",
-- p. 265): the diagonal blocks are inverted by Method 1 (forward
-- substitution, Higham eq. 14.12) and the off-diagonal block is formed by a
-- matrix multiply followed by a block forward-substitution solve (Higham eq.
-- 14.13).  The row certificates are proved from
--   * `forwardSub_backward_error`  (Higham Thm 8.5) for the diagonal solves,
--   * `dotProduct_backward_stable_x` (Higham §3.1) for the off-diagonal
--     matrix multiply,
-- so the printed constant γ (Higham's cₙ) is DERIVED from the FP model, not
-- assumed.  The assembled certificates are then fed to Codex's existing
-- residual route to close (14.10)-(14.13) and the Problem 14.2 normwise form.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.MatrixInversion

namespace NumStability.Ch14Ext

open scoped BigOperators
open NumStability

-- ============================================================
-- Block data for the two-block partition L = [[L11,0],[L21,L22]]
-- with L11 ∈ ℝ^{r×r}, L22 ∈ ℝ^{m×m}, indices Fin (r+m).
-- ============================================================

/-- (1,1) diagonal block of `L` in the `Fin (r+m)` partition. -/
def ch14ext_blk11 (r m : ℕ) (L : Fin (r + m) → Fin (r + m) → ℝ) :
    Fin r → Fin r → ℝ :=
  fun a b => L (Fin.castAdd m a) (Fin.castAdd m b)

/-- (2,2) diagonal block of `L`. -/
def ch14ext_blk22 (r m : ℕ) (L : Fin (r + m) → Fin (r + m) → ℝ) :
    Fin m → Fin m → ℝ :=
  fun a b => L (Fin.natAdd r a) (Fin.natAdd r b)

/-- (2,1) lower-left off-diagonal block of `L`. -/
def ch14ext_blk21 (r m : ℕ) (L : Fin (r + m) → Fin (r + m) → ℝ) :
    Fin m → Fin r → ℝ :=
  fun a b => L (Fin.natAdd r a) (Fin.castAdd m b)

/-- Diagonal block-1 inverse, computed by Method 1 (column-by-column forward
    substitution) on `L11`. -/
noncomputable def ch14ext_X11 (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) : Fin r → Fin r → ℝ :=
  fun c d => fl_forwardSub fp r (ch14ext_blk11 r m L)
    (fun k => if k = d then 1 else 0) c

/-- Right-hand side of the block forward substitution for the off-diagonal
    block: the computed `T = -L21 X11`, column `d`. -/
noncomputable def ch14ext_Tvec (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) (d : Fin r) : Fin m → ℝ :=
  fun a => fl_dotProduct fp r (fun b => -(ch14ext_blk21 r m L a b))
    (fun b => ch14ext_X11 fp r m L b d)

/-- Off-diagonal block, computed by solving `L22 X21 = T` by forward
    substitution. -/
noncomputable def ch14ext_X21 (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) : Fin m → Fin r → ℝ :=
  fun c d => fl_forwardSub fp m (ch14ext_blk22 r m L) (ch14ext_Tvec fp r m L d) c

/-- Diagonal block-2 inverse, computed by Method 1 on `L22`. -/
noncomputable def ch14ext_X22 (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) : Fin m → Fin m → ℝ :=
  fun c d => fl_forwardSub fp m (ch14ext_blk22 r m L)
    (fun k => if k = d then 1 else 0) c

/-- The Method 1B computed inverse for the two-block partition, assembled from
    the block computations:  diagonal blocks by Method 1, the (2,1) block by
    matmul + solve, the (1,2) block is zero (lower-triangular result). -/
noncomputable def ch14ext_method1BBlockInverse (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) : Fin (r + m) → Fin (r + m) → ℝ :=
  fun i j =>
    Fin.addCases
      (fun b : Fin r =>
        Fin.addCases (fun d : Fin r => ch14ext_X11 fp r m L b d)
          (fun _ : Fin m => (0 : ℝ)) j)
      (fun c : Fin m =>
        Fin.addCases (fun d : Fin r => ch14ext_X21 fp r m L c d)
          (fun d : Fin m => ch14ext_X22 fp r m L c d) j)
      i

-- Evaluation lemmas for the assembled inverse.

lemma ch14ext_inv_bb (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) (b d : Fin r) :
    ch14ext_method1BBlockInverse fp r m L (Fin.castAdd m b) (Fin.castAdd m d)
      = ch14ext_X11 fp r m L b d := by
  simp only [ch14ext_method1BBlockInverse, Fin.addCases_left]

lemma ch14ext_inv_bd (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) (b : Fin r) (d : Fin m) :
    ch14ext_method1BBlockInverse fp r m L (Fin.castAdd m b) (Fin.natAdd r d)
      = 0 := by
  simp only [ch14ext_method1BBlockInverse, Fin.addCases_left, Fin.addCases_right]

lemma ch14ext_inv_cb (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) (c : Fin m) (d : Fin r) :
    ch14ext_method1BBlockInverse fp r m L (Fin.natAdd r c) (Fin.castAdd m d)
      = ch14ext_X21 fp r m L c d := by
  simp only [ch14ext_method1BBlockInverse, Fin.addCases_right, Fin.addCases_left]

lemma ch14ext_inv_cd (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) (c d : Fin m) :
    ch14ext_method1BBlockInverse fp r m L (Fin.natAdd r c) (Fin.natAdd r d)
      = ch14ext_X22 fp r m L c d := by
  simp only [ch14ext_method1BBlockInverse, Fin.addCases_right]

-- ============================================================
-- A forward-substitution solution against a unit vector vanishes above the
-- diagonal (needed for the lower-triangular shape of the computed inverse).
-- ============================================================

/-- If `a` is strictly above the pivot `d` (a.val < d.val), then forward
    substitution of `L y = e_d` produces `y a = 0`.  This is the source of the
    lower-triangular structure of the Method-1 inverse. -/
theorem ch14ext_fl_forwardSub_unit_zero_below (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (hL : ∀ i, L i i ≠ 0) (hn : gammaValid fp n)
    (d : Fin n) :
    ∀ a : Fin n, a.val < d.val →
      fl_forwardSub fp n L (fun k => if k = d then (1 : ℝ) else 0) a = 0 := by
  have hspec := fl_forwardSub_satisfies_spec fp n L
    (fun k => if k = d then (1 : ℝ) else 0) hL hn
  suffices H : ∀ N : ℕ, ∀ a : Fin n, a.val = N → a.val < d.val →
      fl_forwardSub fp n L (fun k => if k = d then (1 : ℝ) else 0) a = 0 by
    exact fun a ha => H a.val a rfl ha
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a haN ha_lt
    obtain ⟨Θ, ρ, θ, _hΘ, _hρ, _hθ, heq⟩ := hspec a
    have hba : (fun k : Fin n => if k = d then (1 : ℝ) else 0) a = 0 := by
      show (if a = d then (1 : ℝ) else 0) = 0
      rw [if_neg]
      intro h; rw [h] at ha_lt; exact lt_irrefl _ ha_lt
    have hsum0 :
        (Finset.sum (Finset.filter (fun j : Fin n => j.val < a.val) Finset.univ)
          (fun j => L a j *
            fl_forwardSub fp n L (fun k => if k = d then (1 : ℝ) else 0) j *
            (1 + θ j))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hj0 : fl_forwardSub fp n L (fun k => if k = d then (1 : ℝ) else 0) j = 0 :=
        ih j.val (by omega) j rfl (by omega)
      rw [hj0]; ring
    rw [hba, hsum0] at heq
    have hzero :
        L a a * fl_forwardSub fp n L (fun k => if k = d then (1 : ℝ) else 0) a = 0 := by
      rw [heq]; ring
    exact (mul_eq_zero.mp hzero).resolve_left (hL a)

-- ============================================================
-- Block hypotheses derived from the ambient triangular hypotheses on L.
-- ============================================================

-- ============================================================
-- Lemma 14.2 / eqs. (14.11)-(14.13):  the block loop supplies the row-local
-- backward-error certificates.
-- ============================================================

/-- **Method 1B two-block row certificates** (Higham Lemma 14.2 proof,
    eqs. 14.11-14.13).

    For the two-block partition `L = [[L11,0],[L21,L22]]` with `L11 ∈ ℝ^{r×r}`,
    `L22 ∈ ℝ^{m×m}`, the assembled Method 1B inverse
    `ch14ext_method1BBlockInverse` satisfies, for every column `j` and row `i`,
    a row-local backward-error certificate
      ∑ₖ (Lᵢₖ + Δₖ) X̂ₖⱼ = δᵢⱼ,  |Δₖ| ≤ γ_{r+m} |Lᵢₖ|.

    The certificates are DERIVED from the block loop:
      * diagonal blocks (14.12): `forwardSub_backward_error` (Thm 8.5);
      * off-diagonal block (14.13): `dotProduct_backward_stable_x` for the
        matmul `T = -L21 X11`, then `forwardSub_backward_error` for the solve
        `L22 X21 = T`.
    The printed constant `γ` (Higham's `cₙ`) is obtained by `gamma_mono` from
    the block sizes `r`, `m ≤ r+m`; nothing is assumed at the certificate
    level. -/
theorem ch14ext_method1B_block_row_certificates (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ)
    (hL_diag : ∀ i : Fin (r + m), L i i ≠ 0)
    (hLT : ∀ i j : Fin (r + m), j.val > i.val → L i j = 0)
    (hn : gammaValid fp (r + m)) :
    ∀ j i : Fin (r + m), ∃ Δrow : Fin (r + m) → ℝ,
      (∀ k : Fin (r + m), |Δrow k| ≤ gamma fp (r + m) * |L i k|) ∧
      ∑ k : Fin (r + m), (L i k + Δrow k) *
        ch14ext_method1BBlockInverse fp r m L k j =
        if i = j then 1 else 0 := by
  -- Common gamma facts and block hypotheses.
  have hn_r : gammaValid fp r := gammaValid_mono fp (Nat.le_add_right r m) hn
  have hn_m : gammaValid fp m := gammaValid_mono fp (Nat.le_add_left m r) hn
  have hγr : gamma fp r ≤ gamma fp (r + m) := gamma_mono fp (Nat.le_add_right r m) hn
  have hγm : gamma fp m ≤ gamma fp (r + m) := gamma_mono fp (Nat.le_add_left m r) hn
  have hγnn : 0 ≤ gamma fp (r + m) := gamma_nonneg fp hn
  have hb11diag : ∀ a : Fin r, ch14ext_blk11 r m L a a ≠ 0 := fun a => hL_diag _
  have hb22diag : ∀ a : Fin m, ch14ext_blk22 r m L a a ≠ 0 := fun a => hL_diag _
  have hb11low : ∀ a b : Fin r, a.val < b.val → ch14ext_blk11 r m L a b = 0 := by
    intro a b h; apply hLT; simpa using h
  have hb22low : ∀ a b : Fin m, a.val < b.val → ch14ext_blk22 r m L a b = 0 := by
    intro a b h; apply hLT; simp only [Fin.val_natAdd]; omega
  intro j
  refine Fin.addCases (fun d => ?_) (fun d => ?_) j
  · -- Column j = castAdd d  (block-1 column)
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · -- Case A: row castAdd a, col castAdd d  (diagonal block 1)
      obtain ⟨ΔA, hΔA_bd, hΔA_eq⟩ := forwardSub_backward_error fp r
        (ch14ext_blk11 r m L) (fun k => if k = d then 1 else 0)
        hb11diag hb11low hn_r
      refine ⟨Fin.addCases (fun b : Fin r => ΔA a b) (fun _ : Fin m => (0 : ℝ)), ?_, ?_⟩
      · intro k
        refine Fin.addCases (fun b => ?_) (fun c => ?_) k
        · simp only [Fin.addCases_left]
          calc |ΔA a b| ≤ gamma fp r * |ch14ext_blk11 r m L a b| := hΔA_bd a b
            _ ≤ gamma fp (r + m) * |ch14ext_blk11 r m L a b| :=
                mul_le_mul_of_nonneg_right hγr (abs_nonneg _)
        · simp only [Fin.addCases_right, abs_zero]
          exact mul_nonneg hγnn (abs_nonneg _)
      · rw [Fin.sum_univ_add]
        simp only [Fin.addCases_left, Fin.addCases_right,
          ch14ext_inv_bb, ch14ext_inv_cb]
        have hfirst : ∑ b : Fin r,
            (L (Fin.castAdd m a) (Fin.castAdd m b) + ΔA a b) *
              ch14ext_X11 fp r m L b d = (if a = d then (1 : ℝ) else 0) := by
          have h := hΔA_eq a
          simpa [ch14ext_blk11, ch14ext_X11] using h
        have hsecond : ∑ c : Fin m,
            (L (Fin.castAdd m a) (Fin.natAdd r c) + (0 : ℝ)) *
              ch14ext_X21 fp r m L c d = 0 := by
          apply Finset.sum_eq_zero
          intro c _
          have hz : L (Fin.castAdd m a) (Fin.natAdd r c) = 0 := by
            apply hLT; simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
          rw [hz]; ring
        rw [hfirst, hsecond, add_zero]
        by_cases hAD : a = d
        · subst hAD; simp
        · rw [if_neg hAD, if_neg]
          intro h
          exact hAD (Fin.ext (by have h2 := congrArg Fin.val h; simpa using h2))
    · -- Case C: row natAdd a, col castAdd d  (off-diagonal block, eq. 14.13)
      obtain ⟨δA, hδA_bd, hδA_eq⟩ := dotProduct_backward_stable_x fp r
        (fun b => -(ch14ext_blk21 r m L a b))
        (fun b => ch14ext_X11 fp r m L b d) hn_r
      obtain ⟨ΔL22, hΔL22_bd, hΔL22_eq⟩ := forwardSub_backward_error fp m
        (ch14ext_blk22 r m L) (ch14ext_Tvec fp r m L d)
        hb22diag hb22low hn_m
      refine ⟨Fin.addCases (fun b : Fin r => -(δA b)) (fun c : Fin m => ΔL22 a c),
        ?_, ?_⟩
      · intro k
        refine Fin.addCases (fun b => ?_) (fun c => ?_) k
        · simp only [Fin.addCases_left, abs_neg]
          calc |δA b| ≤ gamma fp r * |(-(ch14ext_blk21 r m L a b))| := hδA_bd b
            _ = gamma fp r * |ch14ext_blk21 r m L a b| := by rw [abs_neg]
            _ ≤ gamma fp (r + m) * |ch14ext_blk21 r m L a b| :=
                mul_le_mul_of_nonneg_right hγr (abs_nonneg _)
        · simp only [Fin.addCases_right]
          calc |ΔL22 a c| ≤ gamma fp m * |ch14ext_blk22 r m L a c| := hΔL22_bd a c
            _ ≤ gamma fp (r + m) * |ch14ext_blk22 r m L a c| :=
                mul_le_mul_of_nonneg_right hγm (abs_nonneg _)
      · rw [Fin.sum_univ_add]
        simp only [Fin.addCases_left, Fin.addCases_right,
          ch14ext_inv_bb, ch14ext_inv_cb]
        have hsecond : ∑ c : Fin m,
            (L (Fin.natAdd r a) (Fin.natAdd r c) + ΔL22 a c) *
              ch14ext_X21 fp r m L c d = ch14ext_Tvec fp r m L d a := by
          have h := hΔL22_eq a
          simpa [ch14ext_blk22, ch14ext_X21] using h
        have hTvec : ch14ext_Tvec fp r m L d a =
            ∑ b : Fin r, (-(L (Fin.natAdd r a) (Fin.castAdd m b)) + δA b) *
              ch14ext_X11 fp r m L b d := by
          have h := hδA_eq
          simpa [ch14ext_Tvec, ch14ext_blk21] using h
        rw [hsecond, hTvec, ← Finset.sum_add_distrib, if_neg]
        · apply Finset.sum_eq_zero; intro b _; ring
        · intro h
          have h2 := congrArg Fin.val h
          simp only [Fin.val_natAdd, Fin.val_castAdd] at h2
          omega
  · -- Column j = natAdd d  (block-2 column)
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · -- Case B: row castAdd a, col natAdd d  (upper block, all-zero column part)
      refine ⟨fun _ => (0 : ℝ), ?_, ?_⟩
      · intro k; simp only [abs_zero]; exact mul_nonneg hγnn (abs_nonneg _)
      · rw [Fin.sum_univ_add]
        simp only [ch14ext_inv_bd, ch14ext_inv_cd, add_zero, mul_zero,
          Finset.sum_const_zero, zero_add]
        have hsecond : ∑ c : Fin m,
            L (Fin.castAdd m a) (Fin.natAdd r c) *
              ch14ext_X22 fp r m L c d = 0 := by
          apply Finset.sum_eq_zero
          intro c _
          have hz : L (Fin.castAdd m a) (Fin.natAdd r c) = 0 := by
            apply hLT; simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
          rw [hz]; ring
        rw [hsecond, if_neg]
        intro h
        have h2 := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
        omega
    · -- Case D: row natAdd a, col natAdd d  (diagonal block 2)
      obtain ⟨ΔD, hΔD_bd, hΔD_eq⟩ := forwardSub_backward_error fp m
        (ch14ext_blk22 r m L) (fun k => if k = d then 1 else 0)
        hb22diag hb22low hn_m
      refine ⟨Fin.addCases (fun _ : Fin r => (0 : ℝ)) (fun c : Fin m => ΔD a c),
        ?_, ?_⟩
      · intro k
        refine Fin.addCases (fun b => ?_) (fun c => ?_) k
        · simp only [Fin.addCases_left, abs_zero]
          exact mul_nonneg hγnn (abs_nonneg _)
        · simp only [Fin.addCases_right]
          calc |ΔD a c| ≤ gamma fp m * |ch14ext_blk22 r m L a c| := hΔD_bd a c
            _ ≤ gamma fp (r + m) * |ch14ext_blk22 r m L a c| :=
                mul_le_mul_of_nonneg_right hγm (abs_nonneg _)
      · rw [Fin.sum_univ_add]
        simp only [Fin.addCases_left, Fin.addCases_right,
          ch14ext_inv_bd, ch14ext_inv_cd]
        have hfirst : ∑ b : Fin r,
            (L (Fin.natAdd r a) (Fin.castAdd m b) + (0 : ℝ)) * (0 : ℝ) = 0 := by
          simp
        have hsecond : ∑ c : Fin m,
            (L (Fin.natAdd r a) (Fin.natAdd r c) + ΔD a c) *
              ch14ext_X22 fp r m L c d = (if a = d then (1 : ℝ) else 0) := by
          have h := hΔD_eq a
          simpa [ch14ext_blk22, ch14ext_X22] using h
        rw [hfirst, hsecond, zero_add]
        by_cases hAD : a = d
        · subst hAD; simp
        · rw [if_neg hAD, if_neg]
          intro h
          apply hAD
          have h2 := congrArg Fin.val h
          simp only [Fin.val_natAdd] at h2
          exact Fin.ext (by omega)

-- ============================================================
-- Feeding the existing Method 1B residual route (MatrixInversion.lean).
-- ============================================================

/-- The assembled Method 1B block inverse is lower triangular
    (Higham eq. 14.9: the computed inverse of a lower-triangular matrix is
    lower triangular). -/
theorem ch14ext_method1B_block_lower (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ)
    (hL_diag : ∀ i : Fin (r + m), L i i ≠ 0)
    (hn : gammaValid fp (r + m)) :
    ∀ i j : Fin (r + m), i.val < j.val →
      ch14ext_method1BBlockInverse fp r m L i j = 0 := by
  have hn_r : gammaValid fp r := gammaValid_mono fp (Nat.le_add_right r m) hn
  have hn_m : gammaValid fp m := gammaValid_mono fp (Nat.le_add_left m r) hn
  have hb11diag : ∀ a : Fin r, ch14ext_blk11 r m L a a ≠ 0 := fun a => hL_diag _
  have hb22diag : ∀ a : Fin m, ch14ext_blk22 r m L a a ≠ 0 := fun a => hL_diag _
  intro i
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · intro j
    refine Fin.addCases (fun d => ?_) (fun d => ?_) j
    · intro hlt
      rw [ch14ext_inv_bb]
      have hlt' : a.val < d.val := by
        have := hlt; simp only [Fin.val_castAdd] at this; exact this
      exact ch14ext_fl_forwardSub_unit_zero_below fp r (ch14ext_blk11 r m L)
        hb11diag hn_r d a hlt'
    · intro _; rw [ch14ext_inv_bd]
  · intro j
    refine Fin.addCases (fun d => ?_) (fun d => ?_) j
    · intro hlt
      exfalso
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hlt
      omega
    · intro hlt
      rw [ch14ext_inv_cd]
      have hlt' : a.val < d.val := by
        simp only [Fin.val_natAdd] at hlt; omega
      exact ch14ext_fl_forwardSub_unit_zero_below fp m (ch14ext_blk22 r m L)
        hb22diag hn_m d a hlt'

/-- **Lemma 14.2 (eq. 14.10), componentwise right residual** for the two-block
    Method 1B, obtained by feeding the derived row certificates through Codex's
    row→column assembler and `triInv_method1B_right_residual`. -/
theorem ch14ext_method1B_block_right_residual (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ)
    (hL_diag : ∀ i : Fin (r + m), L i i ≠ 0)
    (hLT : ∀ i j : Fin (r + m), j.val > i.val → L i j = 0)
    (hn : gammaValid fp (r + m)) :
    ∀ i j : Fin (r + m),
      |∑ k : Fin (r + m), L i k * ch14ext_method1BBlockInverse fp r m L k j -
        (if i = j then 1 else 0)| ≤
      gamma fp (r + m) *
        ∑ k : Fin (r + m), |L i k| *
          |ch14ext_method1BBlockInverse fp r m L k j| := by
  have hRows := ch14ext_method1B_block_row_certificates fp r m L hL_diag hLT hn
  have hCol : ∀ j : Fin (r + m), ∃ ΔL : Fin (r + m) → Fin (r + m) → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp (r + m) * |L i k|) ∧
      ∀ i, ∑ k : Fin (r + m), (L i k + ΔL i k) *
        ch14ext_method1BBlockInverse fp r m L k j =
        if i = j then 1 else 0 := fun j =>
    triInv_method1B_column_backward_error_of_row_certificates (r + m) fp
      L (ch14ext_method1BBlockInverse fp r m L) j (hRows j)
  exact triInv_method1B_right_residual (r + m) fp L
    (ch14ext_method1BBlockInverse fp r m L) hL_diag hLT hn hCol

/-- **Problem 14.2 / Lemma 14.2 normwise right residual** for the two-block
    Method 1B. -/
theorem ch14ext_method1B_block_right_residual_normwise (fp : FPModel) (r m : ℕ)
    (hn0 : 0 < r + m)
    (L : Fin (r + m) → Fin (r + m) → ℝ)
    (hL_diag : ∀ i : Fin (r + m), L i i ≠ 0)
    (hLT : ∀ i j : Fin (r + m), j.val > i.val → L i j = 0)
    (hn : gammaValid fp (r + m)) :
    infNorm (fun i j =>
      ∑ k : Fin (r + m), L i k * ch14ext_method1BBlockInverse fp r m L k j -
        (if i = j then 1 else 0)) ≤
      gamma fp (r + m) * infNorm L *
        infNorm (ch14ext_method1BBlockInverse fp r m L) := by
  have hRows := ch14ext_method1B_block_row_certificates fp r m L hL_diag hLT hn
  have hCol : ∀ j : Fin (r + m), ∃ ΔL : Fin (r + m) → Fin (r + m) → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp (r + m) * |L i k|) ∧
      ∀ i, ∑ k : Fin (r + m), (L i k + ΔL i k) *
        ch14ext_method1BBlockInverse fp r m L k j =
        if i = j then 1 else 0 := fun j =>
    triInv_method1B_column_backward_error_of_row_certificates (r + m) fp
      L (ch14ext_method1BBlockInverse fp r m L) j (hRows j)
  exact triInv_method1B_right_residual_normwise (r + m) hn0 fp L
    (ch14ext_method1BBlockInverse fp r m L) hL_diag hLT hn hCol

/-- **BlockMethod1BSpec** for the two-block Method 1B: block count, lower
    triangular shape, and per-column backward errors are all discharged from
    the block loop, via the row-certificate route
    `triInv_method1B_spec_of_row_certificates`. -/
theorem ch14ext_method1B_block_spec (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ)
    (hL_diag : ∀ i : Fin (r + m), L i i ≠ 0)
    (hLT : ∀ i j : Fin (r + m), j.val > i.val → L i j = 0)
    (hn : gammaValid fp (r + m))
    (hN : 2 ≤ r + m) :
    BlockMethod1BSpec fp (r + m) 2 L (ch14ext_method1BBlockInverse fp r m L) :=
  triInv_method1B_spec_of_row_certificates (r + m) 2 fp
    L (ch14ext_method1BBlockInverse fp r m L) hN
    (ch14ext_method1B_block_lower fp r m L hL_diag hn)
    (ch14ext_method1B_block_row_certificates fp r m L hL_diag hLT hn)

/-- **Lemma 14.2 (eq. 14.10)** for the two-block Method 1B via the full
    `triInv_method1B_right_residual_of_row_certificates` route named in the
    Chapter 14 ledger (block count + lower-triangular shape + derived
    certificates). -/
theorem ch14ext_method1B_block_right_residual_via_spec (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ)
    (hL_diag : ∀ i : Fin (r + m), L i i ≠ 0)
    (hLT : ∀ i j : Fin (r + m), j.val > i.val → L i j = 0)
    (hn : gammaValid fp (r + m))
    (hN : 2 ≤ r + m) :
    ∀ i j : Fin (r + m),
      |∑ k : Fin (r + m), L i k * ch14ext_method1BBlockInverse fp r m L k j -
        (if i = j then 1 else 0)| ≤
      gamma fp (r + m) *
        ∑ k : Fin (r + m), |L i k| *
          |ch14ext_method1BBlockInverse fp r m L k j| :=
  triInv_method1B_right_residual_of_row_certificates (r + m) 2 fp
    L (ch14ext_method1BBlockInverse fp r m L) hL_diag hLT hn hN
    (ch14ext_method1B_block_lower fp r m L hL_diag hn)
    (ch14ext_method1B_block_row_certificates fp r m L hL_diag hLT hn)

end NumStability.Ch14Ext
