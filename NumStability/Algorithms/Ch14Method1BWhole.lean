-- Algorithms/Ch14Method1BWhole.lean
--
-- Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
-- Chapter 14 (Matrix Inversion), §14.2.2 "Block Methods", **Lemma 14.2**
-- (eqs. (14.10)-(14.13), p. 265-266): the computed inverse `X̂` from Method 1B
-- (the block triangular-inverse variant) satisfies the RIGHT residual bound
-- `|L X̂ − I| ≤ cₙu |L| |X̂|`  (eq. (14.10)).
--
-- Method 1B (Higham p. 265):
--   for j = 1 : N
--     Xⱼⱼ = Lⱼⱼ⁻¹                                (by Method 1, forward subst.)
--     Xⱼ₊₁:N,ⱼ = −Lⱼ₊₁:N,ⱼ · Xⱼⱼ                  (block product  T = −L₂₁ X₁₁)
--     Solve Lⱼ₊₁:N,ⱼ₊₁:N · Xⱼ₊₁:N,ⱼ = Xⱼ₊₁:N,ⱼ    (by forward substitution)
--   end
--
-- WAVE 2 (`Ch14BlockTriInverse.lean`) supplied the *2-block per-step* right
-- residual (Higham's "It suffices to verify the inequality with j = 1", the
-- analogue of (14.11) for j = 1): `ch14ext_method1B_block_right_residual`, via
-- the derived row/column backward-error certificates and Codex's Method 1B
-- residual route.
--
-- THIS FILE lifts that per-step result to the WHOLE MATRIX / general N-block
-- case, by exactly the outer block induction Higham describes ("Equating block
-- columns ... it suffices to verify with j = 1"; relabel each block column as
-- the first block column of a trailing submatrix and induct on the number of
-- blocks).  It follows the SAME List-of-block-sizes induction template that
-- wave 3 used to close Lemma 14.3 whole-matrix (`Ch14Method2CWhole.lean`,
-- `ch14ext_method2C_whole_left_residual`): a concrete block-inverse recursion
-- plus a per-level residual composer that combines the leading-block residual,
-- the trailing-block residual (from the induction hypothesis), and the DERIVED
-- off-diagonal residual.  Concretely:
--   * `ch14ext_m1b_offdiag` is the Method 1B off-diagonal block (T = fl(L₂₁X₁₁)
--     by `fl_matMul`, then `X₂₁` by column-wise `fl_forwardSub` solving
--     `L₂₂X₂₁ = −T`), and `ch14ext_m1b_offdiag_residual` DERIVES (14.13),
--     `|L₂₁X̂₁₁ + L₂₂X̂₂₁| ≤ γ_b(|L₂₁||X̂₁₁|) + γ_m(|L₂₂||X̂₂₁|)`, from
--     `matMul_error_bound` (Higham §3.5) and `forwardSub_backward_error`
--     (Higham Thm 8.5) — no residual is assumed.
--   * `ch14ext_m1bBlockInverse fp b m L X₁₁ X₂₂` assembles the 2-block inverse
--     from arbitrary diagonal-block inverses `X₁₁`, `X₂₂` and the derived
--     off-diagonal, and `ch14ext_m1b_block_right_residual` is the composable
--     per-step right residual (leading residual `h11`, trailing residual `h22`,
--     off-diagonal derived), the RIGHT-residual analogue of
--     `ch14ext_method2C_block_left_residual`.
--   * `ch14ext_m1bInv fp bs L` is the block Method 1B inverse for an arbitrary
--     block partition `bs : List ℕ`, peeling the leading block (inverted by
--     Method 1, `ch14ext_X11`, i.e. (14.12)) and recursing Method 1B on the
--     trailing submatrix `ch14ext_blk22`.
--   * `ch14ext_m1bInv_right_residual` proves, by induction on the block list,
--     the full flat `Fin bs.sum` right residual, using the composer as the
--     induction STEP (leading block `h11` from the Method-1 residual
--     `ch14ext_m1b_leading_right_residual` / (14.4), trailing block `h22` from
--     the induction hypothesis, off-diagonal derived inside the step).
--   * `ch14ext_method1B_whole_right_residual` and its `_normwise` companion
--     state the closed whole-matrix Lemma 14.2 with the DERIVED constant
--     `cₙu = γ_{bs.sum}` (matching wave 2's `γ_{r+m}`).
--
-- Nothing is assumed at the residual level: every diagonal-block, off-diagonal,
-- and constant fact is discharged from the FP rounding model or from the
-- already-derived wave-1/wave-2 lemmas.  The printed `cₙu = γ_n` is DERIVED into
-- the conclusion.

import NumStability.Algorithms.Ch14BlockTriInverse
import NumStability.Algorithms.MatMul

namespace NumStability.Ch14Ext

open scoped BigOperators
open NumStability

-- ============================================================
-- §14.2.2  Method 1B block off-diagonal computation (Higham p. 265)
-- ============================================================

/-- The block product step of Method 1B: `T̂ = fl(L₂₁ · X₁₁)`.

    `L₂₁` is the `m×b` below-diagonal block `ch14ext_blk21` and `X₁₁` is the
    already-computed `b×b` leading inverse; the computed product commits the
    standard column-by-column matrix-multiply rounding errors. -/
noncomputable def ch14ext_m1b_temp (fp : FPModel) (b m : ℕ)
    (L : Fin (b + m) → Fin (b + m) → ℝ) (X11 : Fin b → Fin b → ℝ) :
    Fin m → Fin b → ℝ :=
  fl_matMul fp m b b (ch14ext_blk21 b m L) X11

/-- The forward-substitution step of Method 1B: solve `L₂₂ · X₂₁ = −T̂` for the
    off-diagonal block `X̂₂₁` (an `m×b` matrix), column by column.

    Column `d` of `X̂₂₁` solves `L₂₂ (X̂₂₁)(:,d) = −T̂(:,d)` by `fl_forwardSub`,
    since `L₂₂ = ch14ext_blk22` is lower triangular. -/
noncomputable def ch14ext_m1b_offdiag (fp : FPModel) (b m : ℕ)
    (L : Fin (b + m) → Fin (b + m) → ℝ) (X11 : Fin b → Fin b → ℝ) :
    Fin m → Fin b → ℝ :=
  fun c d => fl_forwardSub fp m (ch14ext_blk22 b m L)
    (fun a => - ch14ext_m1b_temp fp b m L X11 a d) c

-- ============================================================
-- §14.2.2  Off-diagonal RIGHT residual (14.13), DERIVED
-- ============================================================

/-- **Method 1B off-diagonal block right residual** (Higham §14.2.2, eq.
    (14.13), p. 266), DERIVED form.

    For the `2×2` block partition `L = [[L₁₁,0],[L₂₁,L₂₂]]`, Method 1B forms
    `T̂ = fl(L₂₁·X̂₁₁)` and then solves `L₂₂·X̂₂₁ = −T̂` by column-wise forward
    substitution.  This theorem derives the componentwise off-diagonal residual
    bound directly from the floating-point error models of those two steps — no
    residual bound is assumed.

    The derived (two-budget) constant is explicit:
      `|(L₂₁X̂₁₁)ᶜᵈ + (L₂₂X̂₂₁)ᶜᵈ| ≤ γ_b·(|L₂₁||X̂₁₁|)ᶜᵈ + γ_m·(|L₂₂||X̂₂₁|)ᶜᵈ`,
    where `γ_b` is the block-product coefficient (inner dimension `b`) and `γ_m`
    is the forward-substitution coefficient (`m×m` solve).  This is Higham's
    `cₙu(|L₂₁||X̂₁₁| + |L₂₂||X̂₂₁|)` with a concrete constant, coming from the
    computed identity `L₂₂X̂₂₁ + Δ(L₂₂,X̂₂₁) = −L₂₁X̂₁₁ + Δ(L₂₁,X̂₁₁)`. -/
theorem ch14ext_m1b_offdiag_residual (fp : FPModel) (b m : ℕ)
    (L : Fin (b + m) → Fin (b + m) → ℝ) (X11 : Fin b → Fin b → ℝ)
    (hb22diag : ∀ a : Fin m, ch14ext_blk22 b m L a a ≠ 0)
    (hb22lt : ∀ p q : Fin m, p.val < q.val → ch14ext_blk22 b m L p q = 0)
    (hval : gammaValid fp (b + m)) :
    ∀ (c : Fin m) (d : Fin b),
      |(∑ k : Fin b, ch14ext_blk21 b m L c k * X11 k d)
          + (∑ l : Fin m, ch14ext_blk22 b m L c l
              * ch14ext_m1b_offdiag fp b m L X11 l d)| ≤
        gamma fp b * (∑ k : Fin b, |ch14ext_blk21 b m L c k| * |X11 k d|)
        + gamma fp m * (∑ l : Fin m, |ch14ext_blk22 b m L c l|
              * |ch14ext_m1b_offdiag fp b m L X11 l d|) := by
  intro c d
  have hval_b : gammaValid fp b := gammaValid_mono fp (by omega) hval
  have hval_m : gammaValid fp m := gammaValid_mono fp (by omega) hval
  have hγm_nonneg : 0 ≤ gamma fp m := gamma_nonneg fp hval_m
  -- Abbreviations for the exact and computed pieces.
  -- (a) Block matrix-product error: T̂ = L₂₁X₁₁ + E, |E| ≤ γ_b·(|L₂₁||X₁₁|).
  have hmm : |ch14ext_m1b_temp fp b m L X11 c d
        - (∑ k : Fin b, ch14ext_blk21 b m L c k * X11 k d)|
      ≤ gamma fp b * (∑ k : Fin b, |ch14ext_blk21 b m L c k| * |X11 k d|) := by
    have h := matMul_error_bound fp m b b (ch14ext_blk21 b m L) X11 hval_b c d
    simpa [ch14ext_m1b_temp] using h
  -- (b) Column-wise forward-substitution solve, backward error on L₂₂.
  obtain ⟨ΔL22, hΔL22_bd, hΔL22_eq⟩ :=
    forwardSub_backward_error fp m (ch14ext_blk22 b m L)
      (fun a => - ch14ext_m1b_temp fp b m L X11 a d) hb22diag hb22lt hval_m
  -- The forward-substitution output is exactly the constructed X̂₂₁ column.
  have hsol : ∀ l,
      fl_forwardSub fp m (ch14ext_blk22 b m L)
        (fun a => - ch14ext_m1b_temp fp b m L X11 a d) l
        = ch14ext_m1b_offdiag fp b m L X11 l d := fun l => rfl
  -- Instantiate the solve's equation at row `c` and rewrite into X̂₂₁.
  have heqc : (∑ l : Fin m, (ch14ext_blk22 b m L c l + ΔL22 c l)
        * ch14ext_m1b_offdiag fp b m L X11 l d)
      = - ch14ext_m1b_temp fp b m L X11 c d := by
    have h := hΔL22_eq c
    simp only [hsol] at h
    exact h
  -- Split the perturbed sum.
  have hsum_split : (∑ l : Fin m, (ch14ext_blk22 b m L c l + ΔL22 c l)
        * ch14ext_m1b_offdiag fp b m L X11 l d)
      = (∑ l : Fin m, ch14ext_blk22 b m L c l
            * ch14ext_m1b_offdiag fp b m L X11 l d)
        + (∑ l : Fin m, ΔL22 c l * ch14ext_m1b_offdiag fp b m L X11 l d) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hsum_split] at heqc
  -- The residual identity:
  --   (L₂₁X̂₁₁ + L₂₂X̂₂₁)ᶜᵈ = −(T̂ − L₂₁X̂₁₁) − Σₗ ΔL₂₂ X̂₂₁.
  have hR : (∑ k : Fin b, ch14ext_blk21 b m L c k * X11 k d)
        + (∑ l : Fin m, ch14ext_blk22 b m L c l
            * ch14ext_m1b_offdiag fp b m L X11 l d)
      = -(ch14ext_m1b_temp fp b m L X11 c d
            - (∑ k : Fin b, ch14ext_blk21 b m L c k * X11 k d))
        - (∑ l : Fin m, ΔL22 c l * ch14ext_m1b_offdiag fp b m L X11 l d) := by
    have hL22 : (∑ l : Fin m, ch14ext_blk22 b m L c l
          * ch14ext_m1b_offdiag fp b m L X11 l d)
        = - ch14ext_m1b_temp fp b m L X11 c d
          - (∑ l : Fin m, ΔL22 c l * ch14ext_m1b_offdiag fp b m L X11 l d) := by
      linarith [heqc]
    rw [hL22]; ring
  rw [hR]
  -- Bound Σₗ |ΔL₂₂| |X̂₂₁| by γ_m·(|L₂₂||X̂₂₁|).
  have ht_sum : (∑ l : Fin m, |ΔL22 c l| * |ch14ext_m1b_offdiag fp b m L X11 l d|)
      ≤ gamma fp m * (∑ l : Fin m, |ch14ext_blk22 b m L c l|
            * |ch14ext_m1b_offdiag fp b m L X11 l d|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    calc |ΔL22 c l| * |ch14ext_m1b_offdiag fp b m L X11 l d|
        ≤ (gamma fp m * |ch14ext_blk22 b m L c l|)
            * |ch14ext_m1b_offdiag fp b m L X11 l d| :=
          mul_le_mul_of_nonneg_right (hΔL22_bd c l) (abs_nonneg _)
      _ = gamma fp m * (|ch14ext_blk22 b m L c l|
            * |ch14ext_m1b_offdiag fp b m L X11 l d|) := by ring
  -- Assemble via the triangle inequality.
  calc |(-(ch14ext_m1b_temp fp b m L X11 c d
            - (∑ k : Fin b, ch14ext_blk21 b m L c k * X11 k d)))
          - (∑ l : Fin m, ΔL22 c l * ch14ext_m1b_offdiag fp b m L X11 l d)|
      ≤ |ch14ext_m1b_temp fp b m L X11 c d
            - (∑ k : Fin b, ch14ext_blk21 b m L c k * X11 k d)|
        + (∑ l : Fin m, |ΔL22 c l| * |ch14ext_m1b_offdiag fp b m L X11 l d|) := by
        have h1 := abs_add_le
          (-(ch14ext_m1b_temp fp b m L X11 c d
              - (∑ k : Fin b, ch14ext_blk21 b m L c k * X11 k d)))
          (-(∑ l : Fin m, ΔL22 c l * ch14ext_m1b_offdiag fp b m L X11 l d))
        rw [abs_neg, abs_neg, ← sub_eq_add_neg] at h1
        have h2 : |∑ l : Fin m, ΔL22 c l * ch14ext_m1b_offdiag fp b m L X11 l d|
            ≤ (∑ l : Fin m, |ΔL22 c l| * |ch14ext_m1b_offdiag fp b m L X11 l d|) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          exact le_of_eq (Finset.sum_congr rfl fun l _ => by rw [abs_mul])
        linarith [h1, h2]
    _ ≤ gamma fp b * (∑ k : Fin b, |ch14ext_blk21 b m L c k| * |X11 k d|)
        + gamma fp m * (∑ l : Fin m, |ch14ext_blk22 b m L c l|
              * |ch14ext_m1b_offdiag fp b m L X11 l d|) := by
        linarith [hmm, ht_sum]

-- ============================================================
-- §14.2.2  The assembled 2-block Method 1B inverse (composable)
-- ============================================================

/-- The Method 1B computed inverse for the two-block partition, assembled from
    arbitrary diagonal block inverses `X₁₁` (leading, by Method 1) and `X₂₂`
    (trailing, by the Method 1B recursion) together with the derived
    off-diagonal block `ch14ext_m1b_offdiag` (matmul + forward substitution).
    The `(1,2)` block is zero (the computed inverse is lower triangular).

    This is the RIGHT-residual analogue of `ch14ext_method2CBlockInverse`. -/
noncomputable def ch14ext_m1bBlockInverse (fp : FPModel) (b m : ℕ)
    (L : Fin (b + m) → Fin (b + m) → ℝ)
    (X11 : Fin b → Fin b → ℝ) (X22 : Fin m → Fin m → ℝ) :
    Fin (b + m) → Fin (b + m) → ℝ :=
  fun i j =>
    Fin.addCases
      (fun p : Fin b =>
        Fin.addCases (fun q : Fin b => X11 p q) (fun _ : Fin m => (0 : ℝ)) j)
      (fun c : Fin m =>
        Fin.addCases
          (fun q : Fin b => ch14ext_m1b_offdiag fp b m L X11 c q)
          (fun q : Fin m => X22 c q) j)
      i

lemma ch14ext_m1b_inv_bb (fp : FPModel) (b m : ℕ)
    (L : Fin (b + m) → Fin (b + m) → ℝ) (X11 : Fin b → Fin b → ℝ)
    (X22 : Fin m → Fin m → ℝ) (p q : Fin b) :
    ch14ext_m1bBlockInverse fp b m L X11 X22 (Fin.castAdd m p) (Fin.castAdd m q)
      = X11 p q := by
  simp only [ch14ext_m1bBlockInverse, Fin.addCases_left]

lemma ch14ext_m1b_inv_bd (fp : FPModel) (b m : ℕ)
    (L : Fin (b + m) → Fin (b + m) → ℝ) (X11 : Fin b → Fin b → ℝ)
    (X22 : Fin m → Fin m → ℝ) (p : Fin b) (q : Fin m) :
    ch14ext_m1bBlockInverse fp b m L X11 X22 (Fin.castAdd m p) (Fin.natAdd b q)
      = 0 := by
  simp only [ch14ext_m1bBlockInverse, Fin.addCases_left, Fin.addCases_right]

lemma ch14ext_m1b_inv_cb (fp : FPModel) (b m : ℕ)
    (L : Fin (b + m) → Fin (b + m) → ℝ) (X11 : Fin b → Fin b → ℝ)
    (X22 : Fin m → Fin m → ℝ) (c : Fin m) (q : Fin b) :
    ch14ext_m1bBlockInverse fp b m L X11 X22 (Fin.natAdd b c) (Fin.castAdd m q)
      = ch14ext_m1b_offdiag fp b m L X11 c q := by
  simp only [ch14ext_m1bBlockInverse, Fin.addCases_right, Fin.addCases_left]

lemma ch14ext_m1b_inv_cd (fp : FPModel) (b m : ℕ)
    (L : Fin (b + m) → Fin (b + m) → ℝ) (X11 : Fin b → Fin b → ℝ)
    (X22 : Fin m → Fin m → ℝ) (c q : Fin m) :
    ch14ext_m1bBlockInverse fp b m L X11 X22 (Fin.natAdd b c) (Fin.natAdd b q)
      = X22 c q := by
  simp only [ch14ext_m1bBlockInverse, Fin.addCases_right]

-- Index bookkeeping for the `Fin (b + m)` block partition.

private lemma ch14ext_m1b_castAdd_eq_iff {b m : ℕ} (p q : Fin b) :
    ((Fin.castAdd m p : Fin (b + m)) = Fin.castAdd m q) ↔ (p = q) := by
  constructor
  · intro h; apply Fin.ext; have := congrArg Fin.val h; simpa using this
  · intro h; rw [h]

private lemma ch14ext_m1b_natAdd_eq_iff {b m : ℕ} (c q : Fin m) :
    ((Fin.natAdd b c : Fin (b + m)) = Fin.natAdd b q) ↔ (c = q) := by
  constructor
  · intro h; apply Fin.ext; have := congrArg Fin.val h
    simp only [Fin.val_natAdd] at this; omega
  · intro h; rw [h]

private lemma ch14ext_m1b_castAdd_ne_natAdd {b m : ℕ} (p : Fin b) (c : Fin m) :
    (Fin.castAdd m p : Fin (b + m)) ≠ Fin.natAdd b c := by
  intro hc
  have h := congrArg Fin.val hc
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h
  have := p.isLt; omega

-- ============================================================
-- §14.2.1  Leading-block Method 1 RIGHT residual (14.12) / (14.4)
-- ============================================================

/-- **Leading diagonal block right residual** (Higham eq. (14.12), from the
    Method 1 bound (14.4)).

    The leading block inverse `ch14ext_X11 fp b m L` is computed by Method 1
    (column-by-column forward substitution on `L₁₁ = ch14ext_blk11`).  From the
    forward-substitution backward error (Higham Thm 8.5) its right residual
    satisfies `|L₁₁ X̂₁₁ − I| ≤ γ_b |L₁₁| |X̂₁₁|`. -/
theorem ch14ext_m1b_leading_right_residual (fp : FPModel) (b m : ℕ)
    (L : Fin (b + m) → Fin (b + m) → ℝ)
    (hb11diag : ∀ a : Fin b, ch14ext_blk11 b m L a a ≠ 0)
    (hb11lt : ∀ p q : Fin b, p.val < q.val → ch14ext_blk11 b m L p q = 0)
    (hval_b : gammaValid fp b) :
    ∀ a d : Fin b,
      |(∑ k : Fin b, ch14ext_blk11 b m L a k * ch14ext_X11 fp b m L k d)
          - (if a = d then 1 else 0)|
        ≤ gamma fp b * (∑ k : Fin b, |ch14ext_blk11 b m L a k|
              * |ch14ext_X11 fp b m L k d|) := by
  intro a d
  obtain ⟨ΔL, hΔL_bd, hΔL_eq⟩ :=
    forwardSub_backward_error fp b (ch14ext_blk11 b m L)
      (fun k => if k = d then 1 else 0) hb11diag hb11lt hval_b
  -- ch14ext_X11 fp b m L k d = fl_forwardSub fp b L₁₁ e_d k  (definitionally).
  have hsol : ∀ k,
      fl_forwardSub fp b (ch14ext_blk11 b m L) (fun k => if k = d then 1 else 0) k
        = ch14ext_X11 fp b m L k d := fun k => rfl
  have heqa : (∑ k : Fin b, (ch14ext_blk11 b m L a k + ΔL a k)
        * ch14ext_X11 fp b m L k d) = (if a = d then (1 : ℝ) else 0) := by
    have h := hΔL_eq a
    simp only [hsol] at h
    -- (fun k => if k = d then 1 else 0) a = if a = d then 1 else 0
    simpa using h
  -- Residual identity: (L₁₁X̂₁₁ − I)ₐᵈ = −Σₖ ΔL X̂₁₁.
  have hLX : (∑ k : Fin b, ch14ext_blk11 b m L a k * ch14ext_X11 fp b m L k d)
        - (if a = d then (1 : ℝ) else 0)
      = -(∑ k : Fin b, ΔL a k * ch14ext_X11 fp b m L k d) := by
    have hsplit : (∑ k : Fin b, ch14ext_blk11 b m L a k * ch14ext_X11 fp b m L k d)
          + (∑ k : Fin b, ΔL a k * ch14ext_X11 fp b m L k d)
        = (if a = d then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Eq.trans ?_ heqa
      exact Finset.sum_congr rfl fun k _ => by ring
    linarith [hsplit]
  rw [hLX, abs_neg]
  calc |∑ k : Fin b, ΔL a k * ch14ext_X11 fp b m L k d|
      ≤ ∑ k : Fin b, |ΔL a k * ch14ext_X11 fp b m L k d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin b, |ΔL a k| * |ch14ext_X11 fp b m L k d| :=
        Finset.sum_congr rfl fun k _ => abs_mul _ _
    _ ≤ ∑ k : Fin b, (gamma fp b * |ch14ext_blk11 b m L a k|)
            * |ch14ext_X11 fp b m L k d| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔL_bd a k) (abs_nonneg _)
    _ = gamma fp b * ∑ k : Fin b, |ch14ext_blk11 b m L a k|
            * |ch14ext_X11 fp b m L k d| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring

-- ============================================================
-- §14.2.2  Composable per-step whole-block RIGHT residual
-- ============================================================

/-- **Lemma 14.2 per-step composer** (Higham §14.2.2, "verify with j = 1",
    eqs. (14.11)-(14.13)), two-block form.

    For the partition `L = [[L₁₁,0],[L₂₁,L₂₂]]` over `Fin (b+m)`, Method 1B
    inverts `L₁₁`, `L₂₂` by Method 1 / recursion (their right residuals are the
    hypotheses `h11`, `h22`, exactly Higham's use of (14.12) for the diagonal
    blocks), and forms the off-diagonal block by the matmul + forward-
    substitution step whose residual is DERIVED in
    `ch14ext_m1b_offdiag_residual` ((14.13)).

    Assembling the four block right residuals gives the componentwise right
    residual `|L X̂ − I| ≤ C·|L||X̂|`, with `C` any constant dominating the block
    coefficients `γ_b`, `γ_m` (hypotheses `hCb`, `hCm`).  This is the RIGHT-
    residual analogue of `ch14ext_method2C_block_left_residual`. -/
theorem ch14ext_m1b_block_right_residual (fp : FPModel) (b m : ℕ)
    (L : Fin (b + m) → Fin (b + m) → ℝ)
    (X11 : Fin b → Fin b → ℝ) (X22 : Fin m → Fin m → ℝ) (C : ℝ)
    (hL_diag : ∀ i : Fin (b + m), L i i ≠ 0)
    (hLT : ∀ i j : Fin (b + m), j.val > i.val → L i j = 0)
    (hval : gammaValid fp (b + m))
    (hCb : gamma fp b ≤ C) (hCm : gamma fp m ≤ C)
    (h11 : ∀ a d : Fin b,
      |(∑ k : Fin b, ch14ext_blk11 b m L a k * X11 k d) - (if a = d then 1 else 0)|
        ≤ C * (∑ k : Fin b, |ch14ext_blk11 b m L a k| * |X11 k d|))
    (h22 : ∀ c d : Fin m,
      |(∑ k : Fin m, ch14ext_blk22 b m L c k * X22 k d) - (if c = d then 1 else 0)|
        ≤ C * (∑ k : Fin m, |ch14ext_blk22 b m L c k| * |X22 k d|)) :
    ∀ i j : Fin (b + m),
      |(∑ k : Fin (b + m), L i k * ch14ext_m1bBlockInverse fp b m L X11 X22 k j)
          - (if i = j then 1 else 0)|
        ≤ C * (∑ k : Fin (b + m),
              |L i k| * |ch14ext_m1bBlockInverse fp b m L X11 X22 k j|) := by
  -- Nonnegativity of C (from `γ_b ≤ C`).
  have hγb_nonneg : 0 ≤ gamma fp b :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hval)
  have hC_nonneg : 0 ≤ C := le_trans hγb_nonneg hCb
  -- Block triangular/diagonal facts for the trailing block.
  have hb22diag : ∀ a : Fin m, ch14ext_blk22 b m L a a ≠ 0 := fun a => hL_diag _
  have hb22lt : ∀ p q : Fin m, p.val < q.val → ch14ext_blk22 b m L p q = 0 := by
    intro p q h; apply hLT; simp only [Fin.val_natAdd]; omega
  -- The derived off-diagonal block residual.
  have hoff := ch14ext_m1b_offdiag_residual fp b m L X11 hb22diag hb22lt hval
  intro i j
  refine Fin.addCases (fun p => ?_) (fun c => ?_) i <;>
    refine Fin.addCases (fun q => ?_) (fun q => ?_) j
  · -- (1,1) diagonal block: reduce to the leading-block residual `h11`.
    have hres : (∑ k : Fin (b + m),
          L (Fin.castAdd m p) k
            * ch14ext_m1bBlockInverse fp b m L X11 X22 k (Fin.castAdd m q))
        = ∑ k : Fin b, ch14ext_blk11 b m L p k * X11 k q := by
      rw [Fin.sum_univ_add]
      have h2 : (∑ k : Fin m,
          L (Fin.castAdd m p) (Fin.natAdd b k)
            * ch14ext_m1bBlockInverse fp b m L X11 X22 (Fin.natAdd b k)
                (Fin.castAdd m q)) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        have hz : L (Fin.castAdd m p) (Fin.natAdd b k) = 0 := by
          apply hLT; simp only [Fin.val_castAdd, Fin.val_natAdd]
          have := p.isLt; omega
        rw [hz, zero_mul]
      rw [h2, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ch14ext_m1b_inv_bb]; rfl
    have hbud : (∑ k : Fin (b + m),
          |L (Fin.castAdd m p) k|
            * |ch14ext_m1bBlockInverse fp b m L X11 X22 k (Fin.castAdd m q)|)
        = ∑ k : Fin b, |ch14ext_blk11 b m L p k| * |X11 k q| := by
      rw [Fin.sum_univ_add]
      have h2 : (∑ k : Fin m,
          |L (Fin.castAdd m p) (Fin.natAdd b k)|
            * |ch14ext_m1bBlockInverse fp b m L X11 X22 (Fin.natAdd b k)
                (Fin.castAdd m q)|) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        have hz : L (Fin.castAdd m p) (Fin.natAdd b k) = 0 := by
          apply hLT; simp only [Fin.val_castAdd, Fin.val_natAdd]
          have := p.isLt; omega
        rw [hz, abs_zero, zero_mul]
      rw [h2, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ch14ext_m1b_inv_bb]; rfl
    rw [hres, hbud]
    simp only [ch14ext_m1b_castAdd_eq_iff]
    exact h11 p q
  · -- (1,2) block: residual is exactly zero.
    have hres : (∑ k : Fin (b + m),
          L (Fin.castAdd m p) k
            * ch14ext_m1bBlockInverse fp b m L X11 X22 k (Fin.natAdd b q)) = 0 := by
      rw [Fin.sum_univ_add]
      have h1 : (∑ k : Fin b,
          L (Fin.castAdd m p) (Fin.castAdd m k)
            * ch14ext_m1bBlockInverse fp b m L X11 X22 (Fin.castAdd m k)
                (Fin.natAdd b q)) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        rw [ch14ext_m1b_inv_bd, mul_zero]
      have h2 : (∑ k : Fin m,
          L (Fin.castAdd m p) (Fin.natAdd b k)
            * ch14ext_m1bBlockInverse fp b m L X11 X22 (Fin.natAdd b k)
                (Fin.natAdd b q)) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        have hz : L (Fin.castAdd m p) (Fin.natAdd b k) = 0 := by
          apply hLT; simp only [Fin.val_castAdd, Fin.val_natAdd]
          have := p.isLt; omega
        rw [hz, zero_mul]
      rw [h1, h2, add_zero]
    rw [hres, if_neg (ch14ext_m1b_castAdd_ne_natAdd p q), sub_zero, abs_zero]
    exact mul_nonneg hC_nonneg
      (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · -- (2,1) off-diagonal block: the DERIVED residual.
    have hres : (∑ k : Fin (b + m),
          L (Fin.natAdd b c) k
            * ch14ext_m1bBlockInverse fp b m L X11 X22 k (Fin.castAdd m q))
        = (∑ k : Fin b, ch14ext_blk21 b m L c k * X11 k q)
          + (∑ l : Fin m, ch14ext_blk22 b m L c l
              * ch14ext_m1b_offdiag fp b m L X11 l q) := by
      rw [Fin.sum_univ_add]
      refine congrArg₂ (· + ·) ?_ ?_
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [ch14ext_m1b_inv_bb]; rfl
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [ch14ext_m1b_inv_cb]; rfl
    have hbud : (∑ k : Fin (b + m),
          |L (Fin.natAdd b c) k|
            * |ch14ext_m1bBlockInverse fp b m L X11 X22 k (Fin.castAdd m q)|)
        = (∑ k : Fin b, |ch14ext_blk21 b m L c k| * |X11 k q|)
          + (∑ l : Fin m, |ch14ext_blk22 b m L c l|
              * |ch14ext_m1b_offdiag fp b m L X11 l q|) := by
      rw [Fin.sum_univ_add]
      refine congrArg₂ (· + ·) ?_ ?_
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [ch14ext_m1b_inv_bb]; rfl
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [ch14ext_m1b_inv_cb]; rfl
    rw [hres, hbud, if_neg ((ch14ext_m1b_castAdd_ne_natAdd q c).symm), sub_zero]
    have hB1 : 0 ≤ (∑ k : Fin b, |ch14ext_blk21 b m L c k| * |X11 k q|) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hB2 : 0 ≤ (∑ l : Fin m, |ch14ext_blk22 b m L c l|
          * |ch14ext_m1b_offdiag fp b m L X11 l q|) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    refine le_trans (hoff c q) ?_
    have e1 : gamma fp b * (∑ k : Fin b, |ch14ext_blk21 b m L c k| * |X11 k q|)
        ≤ C * (∑ k : Fin b, |ch14ext_blk21 b m L c k| * |X11 k q|) :=
      mul_le_mul_of_nonneg_right hCb hB1
    have e2 : gamma fp m * (∑ l : Fin m, |ch14ext_blk22 b m L c l|
          * |ch14ext_m1b_offdiag fp b m L X11 l q|)
        ≤ C * (∑ l : Fin m, |ch14ext_blk22 b m L c l|
          * |ch14ext_m1b_offdiag fp b m L X11 l q|) :=
      mul_le_mul_of_nonneg_right hCm hB2
    calc gamma fp b * (∑ k : Fin b, |ch14ext_blk21 b m L c k| * |X11 k q|)
          + gamma fp m * (∑ l : Fin m, |ch14ext_blk22 b m L c l|
              * |ch14ext_m1b_offdiag fp b m L X11 l q|)
        ≤ C * (∑ k : Fin b, |ch14ext_blk21 b m L c k| * |X11 k q|)
          + C * (∑ l : Fin m, |ch14ext_blk22 b m L c l|
              * |ch14ext_m1b_offdiag fp b m L X11 l q|) := add_le_add e1 e2
      _ = C * ((∑ k : Fin b, |ch14ext_blk21 b m L c k| * |X11 k q|)
          + (∑ l : Fin m, |ch14ext_blk22 b m L c l|
              * |ch14ext_m1b_offdiag fp b m L X11 l q|)) := by ring
  · -- (2,2) diagonal block: reduce to the trailing-block residual `h22`.
    have hres : (∑ k : Fin (b + m),
          L (Fin.natAdd b c) k
            * ch14ext_m1bBlockInverse fp b m L X11 X22 k (Fin.natAdd b q))
        = ∑ k : Fin m, ch14ext_blk22 b m L c k * X22 k q := by
      rw [Fin.sum_univ_add]
      have h1 : (∑ k : Fin b,
          L (Fin.natAdd b c) (Fin.castAdd m k)
            * ch14ext_m1bBlockInverse fp b m L X11 X22 (Fin.castAdd m k)
                (Fin.natAdd b q)) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        rw [ch14ext_m1b_inv_bd, mul_zero]
      rw [h1, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ch14ext_m1b_inv_cd]; rfl
    have hbud : (∑ k : Fin (b + m),
          |L (Fin.natAdd b c) k|
            * |ch14ext_m1bBlockInverse fp b m L X11 X22 k (Fin.natAdd b q)|)
        = ∑ k : Fin m, |ch14ext_blk22 b m L c k| * |X22 k q| := by
      rw [Fin.sum_univ_add]
      have h1 : (∑ k : Fin b,
          |L (Fin.natAdd b c) (Fin.castAdd m k)|
            * |ch14ext_m1bBlockInverse fp b m L X11 X22 (Fin.castAdd m k)
                (Fin.natAdd b q)|) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        rw [ch14ext_m1b_inv_bd, abs_zero, mul_zero]
      rw [h1, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ch14ext_m1b_inv_cd]; rfl
    rw [hres, hbud]
    simp only [ch14ext_m1b_natAdd_eq_iff]
    exact h22 c q

-- ============================================================
-- §14.2.2  The block Method 1B inverse for a general block partition
-- ============================================================

/-- **Method 1B block triangular inverse (Higham §14.2.2), general N-block
    form.**

    `ch14ext_m1bInv fp bs L` is the matrix computed by Method 1B on the lower
    triangular `L : Fin bs.sum → Fin bs.sum → ℝ`, where `bs : List ℕ` lists the
    block sizes (`n = bs.sum`, number of blocks `bs.length`).  The recursion is
    Higham's outer block loop:

    * `[]`  (empty partition, `Fin 0`): the vacuous empty matrix.
    * `b :: rest`: peel the leading `b × b` block `L₁₁`; invert it by Method 1
      (column-wise forward substitution, `ch14ext_X11`, eq. (14.12)); recurse
      Method 1B on the trailing `(bs.sum − b)` submatrix `ch14ext_blk22`; form
      the off-diagonal `(2,1)` block by the matmul + forward-substitution step
      inside `ch14ext_m1bBlockInverse`.

    Because `(b :: rest).sum` is definitionally `b + rest.sum`, the assembled
    `Fin (b + rest.sum)` matrix has exactly the ambient index type. -/
noncomputable def ch14ext_m1bInv (fp : FPModel) :
    (bs : List ℕ) → (L : Fin bs.sum → Fin bs.sum → ℝ) → Fin bs.sum → Fin bs.sum → ℝ
  | [], L => L
  | (b :: rest), L =>
      ch14ext_m1bBlockInverse fp b rest.sum L
        (ch14ext_X11 fp b rest.sum L)
        (ch14ext_m1bInv fp rest (ch14ext_blk22 b rest.sum L))

/-- Defining equation of the block Method 1B inverse at a nonempty partition. -/
lemma ch14ext_m1bInv_cons (fp : FPModel) (b : ℕ) (rest : List ℕ)
    (L : Fin (b + rest.sum) → Fin (b + rest.sum) → ℝ) :
    ch14ext_m1bInv fp (b :: rest) L
      = ch14ext_m1bBlockInverse fp b rest.sum L
          (ch14ext_X11 fp b rest.sum L)
          (ch14ext_m1bInv fp rest (ch14ext_blk22 b rest.sum L)) := rfl

-- ============================================================
-- §14.2.2  Lemma 14.2 — whole-matrix right residual by outer block induction
-- ============================================================

/-- **Lemma 14.2 (Higham §14.2.2, p. 265-266) — whole-matrix / general N-block
    right residual for Method 1B, componentwise, uniform constant `C`.**

    For any block partition `bs : List ℕ` of `n = bs.sum` and any lower
    triangular `L` with nonzero diagonal, the block Method 1B inverse
    `ch14ext_m1bInv fp bs L` satisfies

        |L X̂ − I|_{ij} ≤ C · (|L| |X̂|)_{ij}

    for every `C` dominating `γ_N` at a bounding dimension `N ≥ bs.sum`
    (hypothesis `hCbig`).

    The proof is Higham's outer block induction ("Equating block columns ... it
    suffices to verify with j = 1"; relabel each block column as the first block
    column of a trailing submatrix and induct on the number of blocks), realised
    as a `List` induction:

    * base `bs = []`: `Fin 0` is empty, so the statement is vacuous;
    * step `bs = b :: rest`: the composer `ch14ext_m1b_block_right_residual`
      assembles
        - `h11` — the Method-1 leading-block right residual
          (`ch14ext_m1b_leading_right_residual`, eq. (14.12)), weakened to `C`;
        - `h22` — the induction hypothesis on the trailing block;
        - the off-diagonal residual, DERIVED inside the composer ((14.13)).
      The block coefficients `γ_b`, `γ_m` are bounded by `C` through `gamma`
      monotonicity since `b, m ≤ bs.sum ≤ N`.

    Because `C` is threaded unchanged, every level's constant obligation reduces
    to the single top-level `hCbig`. -/
theorem ch14ext_m1bInv_right_residual (fp : FPModel) (N : ℕ) (C : ℝ)
    (hvalN : gammaValid fp N)
    (hCbig : gamma fp N ≤ C) :
    ∀ (bs : List ℕ) (L : Fin bs.sum → Fin bs.sum → ℝ),
      bs.sum ≤ N →
      (∀ i : Fin bs.sum, L i i ≠ 0) →
      (∀ i j : Fin bs.sum, j.val > i.val → L i j = 0) →
      ∀ i j : Fin bs.sum,
        |(∑ k : Fin bs.sum, L i k * ch14ext_m1bInv fp bs L k j) -
            (if i = j then 1 else 0)|
          ≤ C * ∑ k : Fin bs.sum, |L i k| * |ch14ext_m1bInv fp bs L k j| := by
  intro bs
  induction bs with
  | nil => intro L _ _ _ i; exact i.elim0
  | cons b rest ih =>
      intro L hsum hdiag hLT i j
      set m := rest.sum with hm
      -- size facts (`(b :: rest).sum = b + m` definitionally)
      have hbmN : b + m ≤ N := hsum
      have hbN : b ≤ N := by omega
      have hmN : m ≤ N := by omega
      have hval_bm : gammaValid fp (b + m) := gammaValid_mono fp (by omega) hvalN
      have hval_b : gammaValid fp b := gammaValid_mono fp (by omega) hvalN
      -- constant bounds via monotonicity
      have hCb : gamma fp b ≤ C := le_trans (gamma_mono fp (by omega) hvalN) hCbig
      have hCm : gamma fp m ≤ C := le_trans (gamma_mono fp (by omega) hvalN) hCbig
      -- leading-block triangular/diagonal facts
      have hb11diag : ∀ a : Fin b, ch14ext_blk11 b m L a a ≠ 0 := fun a => hdiag _
      have hb11lt : ∀ p q : Fin b, p.val < q.val → ch14ext_blk11 b m L p q = 0 := by
        intro p q h; apply hLT; simpa [ch14ext_blk11, Fin.val_castAdd] using h
      -- trailing-block triangular/diagonal facts
      have hb22diag : ∀ a : Fin m, ch14ext_blk22 b m L a a ≠ 0 := fun a => hdiag _
      have hb22lt : ∀ i j : Fin m, j.val > i.val → ch14ext_blk22 b m L i j = 0 := by
        intro i' j' h; apply hLT; simp only [Fin.val_natAdd]; omega
      -- h11: leading block right residual (Method 1, γ_b), weakened to `C`
      have h11 : ∀ a d : Fin b,
          |(∑ k : Fin b, ch14ext_blk11 b m L a k * ch14ext_X11 fp b m L k d)
              - (if a = d then 1 else 0)|
            ≤ C * (∑ k : Fin b, |ch14ext_blk11 b m L a k|
                  * |ch14ext_X11 fp b m L k d|) := by
        intro a d
        have hbase := ch14ext_m1b_leading_right_residual fp b m L
          hb11diag hb11lt hval_b a d
        refine le_trans hbase ?_
        exact mul_le_mul_of_nonneg_right hCb
          (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      -- h22: trailing block by the induction hypothesis
      have h22 : ∀ c d : Fin m,
          |(∑ k : Fin m, ch14ext_blk22 b m L c k
                * ch14ext_m1bInv fp rest (ch14ext_blk22 b m L) k d)
              - (if c = d then 1 else 0)|
            ≤ C * (∑ k : Fin m, |ch14ext_blk22 b m L c k|
                  * |ch14ext_m1bInv fp rest (ch14ext_blk22 b m L) k d|) :=
        ih (ch14ext_blk22 b m L) (by omega) hb22diag hb22lt
      -- assemble the whole-block right residual via the composer
      exact ch14ext_m1b_block_right_residual fp b m L
        (ch14ext_X11 fp b m L)
        (ch14ext_m1bInv fp rest (ch14ext_blk22 b m L)) C
        hdiag hLT hval_bm hCb hCm h11 h22 i j

-- ============================================================
-- §14.2.2  Lemma 14.2, closed whole-matrix form with explicit constant
-- ============================================================

/-- **Lemma 14.2 (Higham §14.2.2, eq. (14.10), p. 265-266), closed whole-matrix
    componentwise form.**

    For any block partition `bs` of `n = bs.sum` and lower triangular `L` with
    nonzero diagonal, the block Method 1B inverse satisfies

        |L X̂ − I| ≤ cₙu · |L| |X̂|,     cₙu = γ_{bs.sum},

    the right-residual bound (14.10), with the constant DERIVED (not assumed)
    from the FP model.  This is the whole-matrix statement Higham asserts for
    Method 1B, lifting wave 2's 2-block `γ_{r+m}` to the general N-block case. -/
theorem ch14ext_method1B_whole_right_residual (fp : FPModel) (bs : List ℕ)
    (L : Fin bs.sum → Fin bs.sum → ℝ)
    (hval : gammaValid fp bs.sum)
    (hdiag : ∀ i : Fin bs.sum, L i i ≠ 0)
    (hLT : ∀ i j : Fin bs.sum, j.val > i.val → L i j = 0) :
    ∀ i j : Fin bs.sum,
      |(∑ k : Fin bs.sum, L i k * ch14ext_m1bInv fp bs L k j) -
          (if i = j then 1 else 0)|
        ≤ gamma fp bs.sum
            * ∑ k : Fin bs.sum, |L i k| * |ch14ext_m1bInv fp bs L k j| :=
  ch14ext_m1bInv_right_residual fp bs.sum (gamma fp bs.sum) hval le_rfl
    bs L le_rfl hdiag hLT

/-- **Lemma 14.2, closed whole-matrix infinity-norm form** (Problem 14.2).

        ‖L X̂ − I‖_∞ ≤ cₙu · ‖L‖_∞ ‖X̂‖_∞ .

    The normwise companion of `ch14ext_method1B_whole_right_residual`, obtained
    from the componentwise bound through the repo bridge
    `higham14_infNorm_le_of_componentwise_matmul_bound` (with `A = L`, `B = X̂`). -/
theorem ch14ext_method1B_whole_right_residual_normwise (fp : FPModel) (bs : List ℕ)
    (hn0 : 0 < bs.sum)
    (L : Fin bs.sum → Fin bs.sum → ℝ)
    (hval : gammaValid fp bs.sum)
    (hdiag : ∀ i : Fin bs.sum, L i i ≠ 0)
    (hLT : ∀ i j : Fin bs.sum, j.val > i.val → L i j = 0) :
    infNorm (fun i j =>
        (∑ k : Fin bs.sum, L i k * ch14ext_m1bInv fp bs L k j) -
          (if i = j then 1 else 0))
      ≤ gamma fp bs.sum
          * infNorm L * infNorm (ch14ext_m1bInv fp bs L) :=
  higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (gamma_nonneg fp hval)
    (ch14ext_method1B_whole_right_residual fp bs L hval hdiag hLT)

end NumStability.Ch14Ext
