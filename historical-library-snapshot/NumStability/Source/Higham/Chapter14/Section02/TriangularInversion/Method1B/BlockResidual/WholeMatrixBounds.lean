import NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockTriInverse
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.Method1BWhole

/-!
# WholeMatrixBounds

Canonical destination for the Chapter14.Section02 declarations relocated from the
historical path `NumStability.Algorithms.Ch14Method1BWhole` during wave R08.
Holds 7 declaration(s): 4 public and 3 authored-private.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open scoped BigOperators
open NumStability

namespace NumStability

namespace Ch14Ext

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

end Ch14Ext
end NumStability
