import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Problem12.ConditionNumberExamples.StressAndPeiMatrices
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockTriInverse
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.Method2C

/-!
# LeftResidualBounds

Canonical destination for the Chapter14.Section02 declarations relocated from the
historical path `NumStability.Algorithms.Ch14Method2C` during wave R08.
Holds 4 declaration(s): 1 public and 3 authored-private.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

namespace Ch14Ext

private lemma ch14ext_castAdd_eq_iff {r m : ℕ} (b d : Fin r) :
    ((Fin.castAdd m b : Fin (r + m)) = Fin.castAdd m d) ↔ (b = d) := by
  constructor
  · intro h; apply Fin.ext; have := congrArg Fin.val h; simpa using this
  · intro h; rw [h]

private lemma ch14ext_natAdd_eq_iff {r m : ℕ} (c d : Fin m) :
    ((Fin.natAdd r c : Fin (r + m)) = Fin.natAdd r d) ↔ (c = d) := by
  constructor
  · intro h; apply Fin.ext; have := congrArg Fin.val h
    simp only [Fin.val_natAdd] at this; omega
  · intro h; rw [h]

private lemma ch14ext_castAdd_ne_natAdd {r m : ℕ} (b : Fin r) (d : Fin m) :
    (Fin.castAdd m b : Fin (r + m)) ≠ Fin.natAdd r d := by
  intro hc
  have h := congrArg Fin.val hc
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h
  have := b.isLt; omega

/-- **Lemma 14.3** (Higham §14.2.2, p. 266-267), two-block form.

    For the partition `L = [[L₁₁,0],[L₂₁,L₂₂]]` over `Fin (r+m)`, Method 2C
    inverts `L₁₁`, `L₂₂` by Method 2 / recursion (their left residuals are the
    hypotheses `h11`, `h22`, exactly Higham's use of (14.8) for the diagonal
    blocks), and forms the off-diagonal block by the matmul + back-substitution
    step whose residual is DERIVED in
    `ch14ext_method2C_offdiag_residual_of_spec_uniform`.

    Assembling the four block residuals gives the componentwise left residual
    `|X̂L − I| ≤ cₙu|X̂||L|`, with `cₙu = C` any constant dominating the derived
    off-diagonal constant (`hCoff`).  Only the off-diagonal piece is discharged
    from floating-point first principles here; `h11`, `h22` remain the
    Method 2 / recursion contracts. -/
theorem ch14ext_method2C_block_left_residual (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ)
    (X11 : Fin r → Fin r → ℝ) (X22 : Fin m → Fin m → ℝ) (C : ℝ)
    (hL_diag : ∀ i : Fin (r + m), L i i ≠ 0)
    (hLT : ∀ i j : Fin (r + m), j.val > i.val → L i j = 0)
    (hval : gammaValid fp (r + m + 1))
    (hCoff : gamma fp (r + 1) + gamma fp m + gamma fp r + gamma fp r * gamma fp m ≤ C)
    (h11 : ∀ b d : Fin r,
      |(∑ k : Fin r, X11 b k * ch14ext_blk11 r m L k d) - (if b = d then 1 else 0)|
        ≤ C * (∑ k : Fin r, |X11 b k| * |ch14ext_blk11 r m L k d|))
    (h22 : ∀ c d : Fin m,
      |(∑ k : Fin m, X22 c k * ch14ext_blk22 r m L k d) - (if c = d then 1 else 0)|
        ≤ C * (∑ k : Fin m, |X22 c k| * |ch14ext_blk22 r m L k d|)) :
    ∀ i j : Fin (r + m),
      |(∑ k : Fin (r + m), ch14ext_method2CBlockInverse fp r m L X11 X22 i k * L k j)
          - (if i = j then 1 else 0)|
        ≤ C * (∑ k : Fin (r + m),
              |ch14ext_method2CBlockInverse fp r m L X11 X22 i k| * |L k j|) := by
  -- Nonnegativity of the constant.
  have hγr1 : 0 ≤ gamma fp (r + 1) := gamma_nonneg fp (gammaValid_mono fp (by omega) hval)
  have hγr : 0 ≤ gamma fp r := gamma_nonneg fp (gammaValid_mono fp (by omega) hval)
  have hγm : 0 ≤ gamma fp m := gamma_nonneg fp (gammaValid_mono fp (by omega) hval)
  have hC_nonneg : 0 ≤ C :=
    le_trans (add_nonneg (add_nonneg (add_nonneg hγr1 hγm) hγr) (mul_nonneg hγr hγm)) hCoff
  -- The derived off-diagonal block residual (uniform constant).
  have hoff := ch14ext_method2C_offdiag_residual_of_spec_uniform fp r m
    (ch14ext_blk11 r m L) (ch14ext_blk21 r m L) X22
    (ch14ext_method2C_offdiag fp r m (ch14ext_blk11 r m L) X22 (ch14ext_blk21 r m L))
    (ch14ext_method2C_temp fp r m X22 (ch14ext_blk21 r m L))
    (fun a => hL_diag (Fin.castAdd m a))
    (fun p q hpq => hLT (Fin.castAdd m p) (Fin.castAdd m q) (by simpa using hpq))
    hval (fun _ _ => rfl) (fun _ => rfl)
  intro i j
  refine Fin.addCases (fun b => ?_) (fun c => ?_) i <;>
    refine Fin.addCases (fun d => ?_) (fun d => ?_) j
  · -- (1,1) diagonal block: reduce to Method 2 residual on L11.
    have hres : (∑ k : Fin (r + m),
          ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.castAdd m b) k
            * L k (Fin.castAdd m d))
        = ∑ k : Fin r, X11 b k * ch14ext_blk11 r m L k d := by
      rw [Fin.sum_univ_add]
      simp only [ch14ext_m2c_inv_bb, ch14ext_m2c_inv_bd, zero_mul,
        Finset.sum_const_zero, add_zero]
      rfl
    have hbud : (∑ k : Fin (r + m),
          |ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.castAdd m b) k|
            * |L k (Fin.castAdd m d)|)
        = ∑ k : Fin r, |X11 b k| * |ch14ext_blk11 r m L k d| := by
      rw [Fin.sum_univ_add]
      simp only [ch14ext_m2c_inv_bb, ch14ext_m2c_inv_bd, abs_zero, zero_mul,
        Finset.sum_const_zero, add_zero]
      rfl
    rw [hres, hbud]
    simp only [ch14ext_castAdd_eq_iff]
    exact h11 b d
  · -- (1,2) block: residual is exactly zero.
    have hres : (∑ k : Fin (r + m),
          ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.castAdd m b) k
            * L k (Fin.natAdd r d)) = 0 := by
      rw [Fin.sum_univ_add]
      have h1 : (∑ k : Fin r,
          ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.castAdd m b) (Fin.castAdd m k)
            * L (Fin.castAdd m k) (Fin.natAdd r d)) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        have hz : L (Fin.castAdd m k) (Fin.natAdd r d) = 0 := by
          apply hLT; simp only [Fin.val_castAdd, Fin.val_natAdd]; have := k.isLt; omega
        rw [hz, mul_zero]
      have h2 : (∑ k : Fin m,
          ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.castAdd m b) (Fin.natAdd r k)
            * L (Fin.natAdd r k) (Fin.natAdd r d)) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        rw [ch14ext_m2c_inv_bd, zero_mul]
      rw [h1, h2, add_zero]
    rw [hres, if_neg (ch14ext_castAdd_ne_natAdd b d), sub_zero, abs_zero]
    exact mul_nonneg hC_nonneg
      (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · -- (2,1) off-diagonal block: the DERIVED residual.
    have hres : (∑ k : Fin (r + m),
          ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.natAdd r c) k
            * L k (Fin.castAdd m d))
        = (∑ b : Fin r, ch14ext_method2C_offdiag fp r m (ch14ext_blk11 r m L) X22
              (ch14ext_blk21 r m L) c b * ch14ext_blk11 r m L b d)
          + (∑ l : Fin m, X22 c l * ch14ext_blk21 r m L l d) := by
      rw [Fin.sum_univ_add]
      simp only [ch14ext_m2c_inv_cb, ch14ext_m2c_inv_cd]
      rfl
    have hbud : (∑ k : Fin (r + m),
          |ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.natAdd r c) k|
            * |L k (Fin.castAdd m d)|)
        = (∑ b : Fin r, |ch14ext_method2C_offdiag fp r m (ch14ext_blk11 r m L) X22
              (ch14ext_blk21 r m L) c b| * |ch14ext_blk11 r m L b d|)
          + (∑ l : Fin m, |X22 c l| * |ch14ext_blk21 r m L l d|) := by
      rw [Fin.sum_univ_add]
      simp only [ch14ext_m2c_inv_cb, ch14ext_m2c_inv_cd]
      rfl
    rw [hres, hbud, if_neg ((ch14ext_castAdd_ne_natAdd d c).symm), sub_zero]
    refine le_trans (hoff c d) ?_
    apply mul_le_mul_of_nonneg_right hCoff
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · -- (2,2) diagonal block: reduce to residual on L22.
    have hres : (∑ k : Fin (r + m),
          ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.natAdd r c) k
            * L k (Fin.natAdd r d))
        = ∑ k : Fin m, X22 c k * ch14ext_blk22 r m L k d := by
      rw [Fin.sum_univ_add]
      have h1 : (∑ k : Fin r,
          ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.natAdd r c) (Fin.castAdd m k)
            * L (Fin.castAdd m k) (Fin.natAdd r d)) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        have hz : L (Fin.castAdd m k) (Fin.natAdd r d) = 0 := by
          apply hLT; simp only [Fin.val_castAdd, Fin.val_natAdd]; have := k.isLt; omega
        rw [hz, mul_zero]
      rw [h1, zero_add]
      simp only [ch14ext_m2c_inv_cd]
      rfl
    have hbud : (∑ k : Fin (r + m),
          |ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.natAdd r c) k|
            * |L k (Fin.natAdd r d)|)
        = ∑ k : Fin m, |X22 c k| * |ch14ext_blk22 r m L k d| := by
      rw [Fin.sum_univ_add]
      have h1 : (∑ k : Fin r,
          |ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.natAdd r c) (Fin.castAdd m k)|
            * |L (Fin.castAdd m k) (Fin.natAdd r d)|) = 0 := by
        apply Finset.sum_eq_zero; intro k _
        have hz : L (Fin.castAdd m k) (Fin.natAdd r d) = 0 := by
          apply hLT; simp only [Fin.val_castAdd, Fin.val_natAdd]; have := k.isLt; omega
        rw [hz, abs_zero, mul_zero]
      rw [h1, zero_add]
      simp only [ch14ext_m2c_inv_cd]
      rfl
    rw [hres, hbud]
    simp only [ch14ext_natAdd_eq_iff]
    exact h22 c d

end Ch14Ext
end NumStability
