-- Algorithms/Ch14Method2CWhole.lean
--
-- Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
-- Chapter 14 (Matrix Inversion), §14.2.2 "Block Methods", **Lemma 14.3**
-- (p. 266-267): the computed inverse `X̂` from Method 2C (the block
-- triangular-inverse variant used by LAPACK's xTRTRI) satisfies the left
-- residual bound  |X̂L − I| ≤ cₙu|X̂||L|.
--
-- Method 2C (Higham p. 266):
--   for j = N : −1 : 1
--     Xⱼⱼ = Lⱼⱼ⁻¹                              (by Method 2)
--     Xⱼ₊₁:N,ⱼ = Xⱼ₊₁:N,ⱼ₊₁:N · Lⱼ₊₁:N,ⱼ        (block product T = X̂₂₂·L₂₁)
--     Solve Xⱼ₊₁:N,ⱼ · Lⱼⱼ = −Xⱼ₊₁:N,ⱼ          (by back substitution)
--   end
--
-- WAVE 2 supplied the *2-block per-step* residual (Higham's "It suffices to
-- verify the inequality with j = 1", the analogue of (14.14) for Method 2C):
-- `ch14ext_method2C_block_left_residual` (Ch14Method2C.lean) assembles the four
-- block residuals of the partition `L = [[L₁₁,0],[L₂₁,L₂₂]]` into
--   |X̂L − I| ≤ C·|X̂||L|
-- from (a) a Method-2 left residual on the leading block L₁₁, (b) a left
-- residual on the trailing block L₂₂, and (c) the DERIVED (FP first-principles,
-- matmul + back-substitution) off-diagonal residual.
--
-- THIS FILE lifts that per-step result to the WHOLE MATRIX / general N-block
-- case, exactly by the outer block induction Higham describes ("relabel each
-- block column as the first block column of a trailing submatrix; induct on the
-- number of blocks").  Concretely:
--   * `ch14ext_method2CInv fp bs L` is the block Method 2C inverse for an
--     arbitrary block partition `bs : List ℕ` (block sizes, `bs.sum = n`),
--     built by peeling the leading block, inverting it by the concrete Method 2
--     loop `ch14ext_method2Inv` (Lemma 14.1, Ch14Method2Loop.lean), recursing
--     Method 2C on the trailing submatrix, and forming the off-diagonal block
--     by the wave-2 matmul + back-substitution step.
--   * `ch14ext_method2CInv_left_residual` proves, by induction on the block
--     list, the full flat `Fin bs.sum` left residual, using the wave-2 2-block
--     core `ch14ext_method2C_block_left_residual` as the induction STEP (leading
--     block `h11` from Lemma 14.1, trailing block `h22` from the induction
--     hypothesis, off-diagonal derived inside the step).
--   * `ch14ext_method2C_whole_left_residual` and its `_normwise` companion state
--     the closed whole-matrix Lemma 14.3 with an explicit, DERIVED constant
--     `cₙ = γ_{n+2} + 2γ_n + γ_n²`.
--
-- Nothing is assumed at the residual level: every diagonal-block, off-diagonal,
-- and constant fact is discharged from the FP rounding model or from the
-- already-derived wave-1/wave-2 lemmas.  The printed `cₙu` is DERIVED into the
-- conclusion.

import NumStability.Algorithms.Ch14Method2C
import NumStability.Algorithms.Ch14Method2Loop

namespace NumStability.Ch14Ext

open scoped BigOperators

-- ============================================================
-- §14.2.2  The block Method 2C inverse for a general block partition
-- ============================================================

/-- **Method 2C block triangular inverse (Higham §14.2.2), general N-block
    form.**

    `ch14ext_method2CInv fp bs L` is the matrix `X` computed by Method 2C on the
    lower triangular `L : Fin bs.sum → Fin bs.sum → ℝ`, where `bs : List ℕ` is
    the list of block sizes (so `n = bs.sum` and the number of blocks is
    `bs.length`).  The recursion is Higham's outer block loop:

    * `[]` (empty partition, `Fin 0`): the (vacuous) empty matrix.
    * `b :: rest`: peel the leading `b × b` block `L₁₁`; invert it by the
      concrete Method 2 loop `ch14ext_method2Inv` (Lemma 14.1); recurse Method 2C
      on the trailing `(bs.sum − b) × (bs.sum − b)` submatrix `ch14ext_blk22`;
      form the off-diagonal `(2,1)` block by the wave-2 matmul +
      back-substitution step inside `ch14ext_method2CBlockInverse`.

    Because `(b :: rest).sum` is definitionally `b + rest.sum`, the assembled
    `Fin (b + rest.sum)` matrix has exactly the ambient index type, so the
    recursion needs no index casts. -/
noncomputable def ch14ext_method2CInv (fp : FPModel) :
    (bs : List ℕ) → (L : Fin bs.sum → Fin bs.sum → ℝ) → Fin bs.sum → Fin bs.sum → ℝ
  | [], L => L
  | (b :: rest), L =>
      ch14ext_method2CBlockInverse fp b rest.sum L
        (ch14ext_method2Inv b fp (ch14ext_blk11 b rest.sum L))
        (ch14ext_method2CInv fp rest (ch14ext_blk22 b rest.sum L))

/-- Defining equation of the block Method 2C inverse at a nonempty partition:
    leading block by Method 2, trailing block by the Method 2C recursion, and
    the off-diagonal assembled by `ch14ext_method2CBlockInverse`. -/
lemma ch14ext_method2CInv_cons (fp : FPModel) (b : ℕ) (rest : List ℕ)
    (L : Fin (b + rest.sum) → Fin (b + rest.sum) → ℝ) :
    ch14ext_method2CInv fp (b :: rest) L
      = ch14ext_method2CBlockInverse fp b rest.sum L
          (ch14ext_method2Inv b fp (ch14ext_blk11 b rest.sum L))
          (ch14ext_method2CInv fp rest (ch14ext_blk22 b rest.sum L)) := rfl

-- ============================================================
-- Block structural facts (lower-triangular shape, nonzero diagonal) inherited
-- by the diagonal sub-blocks from the ambient matrix.
-- ============================================================

/-- The leading `(1,1)` block of a matrix with nonzero diagonal has nonzero
    diagonal. -/
lemma ch14ext_m2c_blk11_diag (b m : ℕ) (L : Fin (b + m) → Fin (b + m) → ℝ)
    (hdiag : ∀ i : Fin (b + m), L i i ≠ 0) :
    ∀ a : Fin b, ch14ext_blk11 b m L a a ≠ 0 := fun _ => hdiag _

/-- The leading `(1,1)` block of a lower triangular matrix is lower triangular. -/
lemma ch14ext_m2c_blk11_lt (b m : ℕ) (L : Fin (b + m) → Fin (b + m) → ℝ)
    (hLT : ∀ i j : Fin (b + m), j.val > i.val → L i j = 0) :
    ∀ i j : Fin b, j.val > i.val → ch14ext_blk11 b m L i j = 0 := by
  intro i j h; apply hLT; simpa [ch14ext_blk11, Fin.val_castAdd] using h

/-- The trailing `(2,2)` block of a matrix with nonzero diagonal has nonzero
    diagonal. -/
lemma ch14ext_m2c_blk22_diag (b m : ℕ) (L : Fin (b + m) → Fin (b + m) → ℝ)
    (hdiag : ∀ i : Fin (b + m), L i i ≠ 0) :
    ∀ a : Fin m, ch14ext_blk22 b m L a a ≠ 0 := fun _ => hdiag _

/-- The trailing `(2,2)` block of a lower triangular matrix is lower
    triangular. -/
lemma ch14ext_m2c_blk22_lt (b m : ℕ) (L : Fin (b + m) → Fin (b + m) → ℝ)
    (hLT : ∀ i j : Fin (b + m), j.val > i.val → L i j = 0) :
    ∀ i j : Fin m, j.val > i.val → ch14ext_blk22 b m L i j = 0 := by
  intro i j h; apply hLT; simp only [Fin.val_natAdd]; omega

-- ============================================================
-- §14.2.2  Lemma 14.3 — whole-matrix left residual by outer block induction
-- ============================================================

/-- **Lemma 14.3 (Higham §14.2.2, p. 266-267) — whole-matrix / general N-block
    left residual for Method 2C, componentwise, uniform constant `C`.**

    For any block partition `bs : List ℕ` of `n = bs.sum` and any lower
    triangular `L` with nonzero diagonal, the block Method 2C inverse
    `ch14ext_method2CInv fp bs L` satisfies

        |X̂L − I|_{ij} ≤ C · (|X̂| |L|)_{ij}

    for every `C` dominating the top-level constant
    `γ_{N+2} + 2γ_N + γ_N²` at a bounding dimension `N ≥ bs.sum` (hypothesis
    `hCbig`).

    The proof is Higham's outer block induction ("relabel each block column as
    the first block column of a trailing submatrix; induct on the number of
    blocks"), realised as a `List` induction:

    * base `bs = []`: `Fin 0` is empty, so the statement is vacuous;
    * step `bs = b :: rest`: the wave-2 2-block core
      `ch14ext_method2C_block_left_residual` assembles
        - `h11` — the Method-2 left residual (Lemma 14.1,
          `ch14ext_method2_left_residual`) on the leading block, weakened from
          `γ_{b+2}` to `C`;
        - `h22` — the induction hypothesis on the trailing block;
        - the off-diagonal residual, DERIVED inside the core from the matmul +
          back-substitution FP model.
      Its `hCoff` constant `γ_{b+1} + γ_m + γ_b + γ_b γ_m` is bounded by `C`
      through `gamma` monotonicity since `b, m ≤ bs.sum ≤ N`.

    Because `C` is threaded unchanged, every level's constant obligation reduces
    to the single top-level `hCbig`. -/
theorem ch14ext_method2CInv_left_residual (fp : FPModel) (N : ℕ) (C : ℝ)
    (hvalN : gammaValid fp (N + 2))
    (hCbig : gamma fp (N + 2) + gamma fp N + gamma fp N + gamma fp N * gamma fp N ≤ C) :
    ∀ (bs : List ℕ) (L : Fin bs.sum → Fin bs.sum → ℝ),
      bs.sum ≤ N →
      (∀ i : Fin bs.sum, L i i ≠ 0) →
      (∀ i j : Fin bs.sum, j.val > i.val → L i j = 0) →
      ∀ i j : Fin bs.sum,
        |(∑ k : Fin bs.sum, ch14ext_method2CInv fp bs L i k * L k j) -
            (if i = j then 1 else 0)|
          ≤ C * ∑ k : Fin bs.sum, |ch14ext_method2CInv fp bs L i k| * |L k j| := by
  -- gamma facts at the bounding dimension `N`
  have hvalN_N : gammaValid fp N := gammaValid_mono fp (by omega) hvalN
  have hγN_nonneg : 0 ≤ gamma fp N := gamma_nonneg fp hvalN_N
  have hγN2_nonneg : 0 ≤ gamma fp (N + 2) := gamma_nonneg fp hvalN
  intro bs
  induction bs with
  | nil => intro L _ _ _ i; exact i.elim0
  | cons b rest ih =>
      intro L hsum hdiag hLT i j
      set m := rest.sum with hm
      -- size facts (relies on `(b :: rest).sum = b + m` definitionally)
      have hbmN : b + m ≤ N := hsum
      have hbN : b ≤ N := by omega
      have hmN : m ≤ N := by omega
      -- gamma validity for the sub-blocks
      have hval_step : gammaValid fp (b + m + 1) := gammaValid_mono fp (by omega) hvalN
      have hval_b2 : gammaValid fp (b + 2) := gammaValid_mono fp (by omega) hvalN
      -- constant bounds via monotonicity
      have hγb1 : gamma fp (b + 1) ≤ gamma fp (N + 2) := gamma_mono fp (by omega) hvalN
      have hγb2 : gamma fp (b + 2) ≤ gamma fp (N + 2) := gamma_mono fp (by omega) hvalN
      have hγm : gamma fp m ≤ gamma fp N := gamma_mono fp (by omega) hvalN_N
      have hγb : gamma fp b ≤ gamma fp N := gamma_mono fp (by omega) hvalN_N
      have hγb_nonneg : 0 ≤ gamma fp b := gamma_nonneg fp (gammaValid_mono fp (by omega) hvalN)
      have hγm_nonneg : 0 ≤ gamma fp m := gamma_nonneg fp (gammaValid_mono fp (by omega) hvalN)
      have hNN : 0 ≤ gamma fp N * gamma fp N := mul_nonneg hγN_nonneg hγN_nonneg
      -- step off-diagonal constant `hCoff ≤ C`
      have hCoff : gamma fp (b + 1) + gamma fp m + gamma fp b + gamma fp b * gamma fp m ≤ C := by
        have hprod : gamma fp b * gamma fp m ≤ gamma fp N * gamma fp N :=
          mul_le_mul hγb hγm hγm_nonneg hγN_nonneg
        calc gamma fp (b + 1) + gamma fp m + gamma fp b + gamma fp b * gamma fp m
            ≤ gamma fp (N + 2) + gamma fp N + gamma fp N + gamma fp N * gamma fp N := by
              linarith
          _ ≤ C := hCbig
      -- leading-block Method-2 residual constant `γ_{b+2} ≤ C`
      have hγb2C : gamma fp (b + 2) ≤ C := le_trans hγb2 (by linarith)
      -- h11: leading block inverted by Method 2 (Lemma 14.1), weakened to `C`
      have h11 : ∀ b' d : Fin b,
          |(∑ k : Fin b, ch14ext_method2Inv b fp (ch14ext_blk11 b m L) b' k
                * ch14ext_blk11 b m L k d) - (if b' = d then 1 else 0)|
            ≤ C * (∑ k : Fin b, |ch14ext_method2Inv b fp (ch14ext_blk11 b m L) b' k|
                * |ch14ext_blk11 b m L k d|) := by
        intro b' d
        have hbase := ch14ext_method2_left_residual b fp (ch14ext_blk11 b m L)
          hval_b2 (ch14ext_m2c_blk11_lt b m L hLT) (ch14ext_m2c_blk11_diag b m L hdiag) b' d
        refine le_trans hbase ?_
        exact mul_le_mul_of_nonneg_right hγb2C
          (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      -- h22: trailing block by the induction hypothesis
      have h22 : ∀ c d : Fin m,
          |(∑ k : Fin m, ch14ext_method2CInv fp rest (ch14ext_blk22 b m L) c k
                * ch14ext_blk22 b m L k d) - (if c = d then 1 else 0)|
            ≤ C * (∑ k : Fin m, |ch14ext_method2CInv fp rest (ch14ext_blk22 b m L) c k|
                * |ch14ext_blk22 b m L k d|) :=
        ih (ch14ext_blk22 b m L) (by omega)
          (ch14ext_m2c_blk22_diag b m L hdiag) (ch14ext_m2c_blk22_lt b m L hLT)
      -- assemble the whole-matrix residual via the wave-2 2-block core
      exact ch14ext_method2C_block_left_residual fp b m L
        (ch14ext_method2Inv b fp (ch14ext_blk11 b m L))
        (ch14ext_method2CInv fp rest (ch14ext_blk22 b m L)) C
        hdiag hLT hval_step hCoff h11 h22 i j

-- ============================================================
-- §14.2.2  Lemma 14.3, closed whole-matrix form with explicit constant
-- ============================================================

/-- The explicit whole-matrix Lemma 14.3 constant `cₙ = γ_{n+2} + 2γ_n + γ_n²`
    (an order-`n` multiple of `u`, matching Higham's `cₙu`). -/
noncomputable def ch14ext_m2c_const (fp : FPModel) (n : ℕ) : ℝ :=
  gamma fp (n + 2) + gamma fp n + gamma fp n + gamma fp n * gamma fp n

lemma ch14ext_m2c_const_nonneg (fp : FPModel) (n : ℕ) (hval : gammaValid fp (n + 2)) :
    0 ≤ ch14ext_m2c_const fp n := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have h1 : 0 ≤ gamma fp (n + 2) := gamma_nonneg fp hval
  have h2 : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have := mul_nonneg h2 h2
  unfold ch14ext_m2c_const
  linarith

/-- **Lemma 14.3 (Higham §14.2.2, p. 266-267), closed whole-matrix
    componentwise form.**

    For any block partition `bs` of `n = bs.sum` and lower triangular `L` with
    nonzero diagonal, the block Method 2C inverse satisfies

        |X̂L − I| ≤ cₙu · |X̂| |L|,     cₙu = ch14ext_m2c_const fp bs.sum,

    the left-residual analogue (14.8) of the Method-1 right residual (14.4),
    with the constant DERIVED (not assumed) from the FP model.  This is the
    whole-matrix statement Higham asserts for Method 2C. -/
theorem ch14ext_method2C_whole_left_residual (fp : FPModel) (bs : List ℕ)
    (L : Fin bs.sum → Fin bs.sum → ℝ)
    (hval : gammaValid fp (bs.sum + 2))
    (hdiag : ∀ i : Fin bs.sum, L i i ≠ 0)
    (hLT : ∀ i j : Fin bs.sum, j.val > i.val → L i j = 0) :
    ∀ i j : Fin bs.sum,
      |(∑ k : Fin bs.sum, ch14ext_method2CInv fp bs L i k * L k j) -
          (if i = j then 1 else 0)|
        ≤ ch14ext_m2c_const fp bs.sum
            * ∑ k : Fin bs.sum, |ch14ext_method2CInv fp bs L i k| * |L k j| :=
  ch14ext_method2CInv_left_residual fp bs.sum (ch14ext_m2c_const fp bs.sum)
    hval (le_of_eq rfl) bs L le_rfl hdiag hLT

/-- **Lemma 14.3, closed whole-matrix infinity-norm form.**

        ‖X̂L − I‖_∞ ≤ cₙu · ‖X̂‖_∞ ‖L‖_∞ .

    The normwise companion of `ch14ext_method2C_whole_left_residual`, obtained
    from the componentwise bound through the repo bridge
    `higham14_infNorm_le_of_componentwise_matmul_bound`. -/
theorem ch14ext_method2C_whole_left_residual_normwise (fp : FPModel) (bs : List ℕ)
    (hn0 : 0 < bs.sum)
    (L : Fin bs.sum → Fin bs.sum → ℝ)
    (hval : gammaValid fp (bs.sum + 2))
    (hdiag : ∀ i : Fin bs.sum, L i i ≠ 0)
    (hLT : ∀ i j : Fin bs.sum, j.val > i.val → L i j = 0) :
    infNorm (fun i j =>
        (∑ k : Fin bs.sum, ch14ext_method2CInv fp bs L i k * L k j) -
          (if i = j then 1 else 0))
      ≤ ch14ext_m2c_const fp bs.sum
          * infNorm (ch14ext_method2CInv fp bs L) * infNorm L :=
  higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (ch14ext_m2c_const_nonneg fp bs.sum hval)
    (ch14ext_method2C_whole_left_residual fp bs L hval hdiag hLT)

end NumStability.Ch14Ext
