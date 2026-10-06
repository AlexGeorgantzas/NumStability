-- Algorithms/TreeDotProduct.lean

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import NumStability.Algorithms.Summation.Tree.Balanced
import NumStability.Algorithms.Summation.Tree.Core

namespace NumStability

open scoped BigOperators

/-!
# Dot products evaluated by summation trees

This file specializes the `SumTree` error analysis to Higham Chapter 3's
product-first dot products.  Each product is rounded once, then the rounded
products are accumulated by a binary summation tree.  The extra multiplication
rounding raises the tree-depth summation radius from `gamma depth` to
`gamma (depth + 1)`.
-/

/-- Dot product whose rounded products are accumulated by a summation tree. -/
noncomputable def fl_sumTreeDotProduct (fp : FPModel) {n : ℕ}
    (t : SumTree n) (x y : Fin n → ℝ) : ℝ :=
  t.eval fp (fun i => fp.fl_mul (x i) (y i))

/-- **Summation-tree dot-product backward error**.

If a summation tree has depth `d`, then accumulating rounded products through
that tree gives one product rounding plus at most `d` addition roundings per
term, hence a componentwise dot-product backward error bounded by
`gamma (d + 1)`. -/
theorem sumTreeDotProduct_backward_error (fp : FPModel) {n : ℕ}
    (t : SumTree n) (x y : Fin n → ℝ)
    (hγ : gammaValid fp (t.depth + 1)) :
    ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp (t.depth + 1)) ∧
      fl_sumTreeDotProduct fp t x y =
        ∑ i : Fin n, x i * y i * (1 + η i) := by
  have hγdepth : gammaValid fp t.depth :=
    gammaValid_mono fp (Nat.le_succ t.depth) hγ
  have hγone : gammaValid fp 1 :=
    gammaValid_mono fp (Nat.succ_le_succ (Nat.zero_le t.depth)) hγ
  let δ : Fin n → ℝ := fun i => Classical.choose (fp.model_mul (x i) (y i))
  have hδ :
      ∀ i,
        |δ i| ≤ fp.u ∧ fp.fl_mul (x i) (y i) = x i * y i * (1 + δ i) :=
    fun i => Classical.choose_spec (fp.model_mul (x i) (y i))
  have hδone : ∀ i, |δ i| ≤ gamma fp 1 :=
    fun i => le_trans (hδ i).1 (u_le_gamma fp one_pos hγone)
  obtain ⟨θ, hθ, hsum⟩ :=
    SumTree.backward_error fp t hγdepth (fun i => fp.fl_mul (x i) (y i))
  let η : Fin n → ℝ := fun i =>
    Classical.choose (gamma_mul fp t.depth 1 (θ i) (δ i)
      (hθ i) (hδone i) hγ)
  have hη : ∀ i, |η i| ≤ gamma fp (t.depth + 1) := by
    intro i
    exact (Classical.choose_spec (gamma_mul fp t.depth 1 (θ i) (δ i)
      (hθ i) (hδone i) hγ)).1
  refine ⟨η, hη, ?_⟩
  rw [fl_sumTreeDotProduct, hsum]
  apply Finset.sum_congr rfl
  intro i _
  have hcomb :
      (1 + δ i) * (1 + θ i) = 1 + η i := by
    have heq :=
      (Classical.choose_spec (gamma_mul fp t.depth 1 (θ i) (δ i)
        (hθ i) (hδone i) hγ)).2
    rw [mul_comm, heq]
  rw [(hδ i).2]
  calc
    x i * y i * (1 + δ i) * (1 + θ i) =
        x i * y i * ((1 + δ i) * (1 + θ i)) := by ring
    _ = x i * y i * (1 + η i) := by rw [hcomb]

/-- **Summation-tree dot-product forward error bound**.

For a tree of depth `d`, the product-first tree dot product satisfies the
Higham-style componentwise forward bound with radius `gamma (d + 1)`. -/
theorem sumTreeDotProduct_error_bound (fp : FPModel) {n : ℕ}
    (t : SumTree n) (x y : Fin n → ℝ)
    (hγ : gammaValid fp (t.depth + 1)) :
    |fl_sumTreeDotProduct fp t x y - ∑ i : Fin n, x i * y i| ≤
      gamma fp (t.depth + 1) * ∑ i : Fin n, |x i| * |y i| := by
  obtain ⟨η, hη, hfl⟩ := sumTreeDotProduct_backward_error fp t x y hγ
  have herr :
      fl_sumTreeDotProduct fp t x y - ∑ i : Fin n, x i * y i =
        ∑ i : Fin n, x i * y i * η i := by
    rw [hfl, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [herr]
  calc
    |∑ i : Fin n, x i * y i * η i|
        ≤ ∑ i : Fin n, |x i * y i * η i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |x i| * |y i| * |η i| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_mul]
    _ ≤ ∑ i : Fin n, |x i| * |y i| * gamma fp (t.depth + 1) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hη i)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = gamma fp (t.depth + 1) * ∑ i : Fin n, |x i| * |y i| := by
          rw [← Finset.sum_mul, mul_comm]

/-- Balanced-tree specialization for `2^r` products.

For powers of two, the balanced summation tree has depth `r`, so the rounded
product-first dot product has the Chapter 3 pairwise radius `gamma (r + 1)`. -/
theorem balancedTreeDotProduct_backward_error (fp : FPModel) (r : ℕ)
    (x y : Fin (2 ^ r) → ℝ) (hγ : gammaValid fp (r + 1)) :
    ∃ η : Fin (2 ^ r) → ℝ,
      (∀ i, |η i| ≤ gamma fp (r + 1)) ∧
      fl_sumTreeDotProduct fp (SumTree.balancedTree r) x y =
        ∑ i : Fin (2 ^ r), x i * y i * (1 + η i) := by
  have hdepth : (SumTree.balancedTree r).depth = r :=
    SumTree.balancedTree_depth r
  have hγdepth : gammaValid fp ((SumTree.balancedTree r).depth + 1) := by
    rw [hdepth]
    exact hγ
  obtain ⟨η, hη, heq⟩ :=
    sumTreeDotProduct_backward_error fp (SumTree.balancedTree r) x y hγdepth
  rw [hdepth] at hη
  exact ⟨η, hη, heq⟩

/-- Balanced-tree product-first dot-product forward error bound. -/
theorem balancedTreeDotProduct_error_bound (fp : FPModel) (r : ℕ)
    (x y : Fin (2 ^ r) → ℝ) (hγ : gammaValid fp (r + 1)) :
    |fl_sumTreeDotProduct fp (SumTree.balancedTree r) x y -
        ∑ i : Fin (2 ^ r), x i * y i| ≤
      gamma fp (r + 1) * ∑ i : Fin (2 ^ r), |x i| * |y i| := by
  have hdepth : (SumTree.balancedTree r).depth = r :=
    SumTree.balancedTree_depth r
  have hγdepth : gammaValid fp ((SumTree.balancedTree r).depth + 1) := by
    rw [hdepth]
    exact hγ
  have hbound :=
    sumTreeDotProduct_error_bound fp (SumTree.balancedTree r) x y hγdepth
  rw [hdepth] at hbound
  exact hbound

/-- Pad a finite vector by zeros to a larger finite index set. -/
noncomputable def finZeroPad (n m : ℕ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else 0

private lemma sum_finZeroPad_eq {n m : ℕ} (h : n ≤ m) (f : Fin n → ℝ) :
    (∑ i : Fin m, finZeroPad n m f i) = ∑ i : Fin n, f i := by
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.sum_fin_eq_sum_range]
  have hleft :
      (∑ i ∈ Finset.range m,
        if hi : i < m then finZeroPad n m f ⟨i, hi⟩ else 0) =
        ∑ i ∈ Finset.range m, if hi : i < n then f ⟨i, hi⟩ else 0 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k < m := by
      simpa only [Finset.mem_range] using hk
    by_cases hkn : k < n
    · simp [finZeroPad, hkm, hkn]
    · simp [finZeroPad, hkm, hkn]
  rw [hleft]
  symm
  apply Finset.sum_subset
    (by
      intro k hk
      simp only [Finset.mem_range] at hk ⊢
      exact lt_of_lt_of_le hk h)
  intro k hk_m hk_n
  have hkn : ¬ k < n := by
    simpa only [Finset.mem_range] using hk_n
  simp [hkn]

private lemma sum_finZeroPad_mul_eq {n m : ℕ} (h : n ≤ m)
    (x y : Fin n → ℝ) :
    (∑ i : Fin m, finZeroPad n m x i * finZeroPad n m y i) =
      ∑ i : Fin n, x i * y i := by
  have hterm :
      ∀ i : Fin m,
        finZeroPad n m x i * finZeroPad n m y i =
          finZeroPad n m (fun j => x j * y j) i := by
    intro i
    by_cases hi : i.val < n
    · simp [finZeroPad, hi]
    · simp [finZeroPad, hi]
  calc
    (∑ i : Fin m, finZeroPad n m x i * finZeroPad n m y i) =
        ∑ i : Fin m, finZeroPad n m (fun j => x j * y j) i := by
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = ∑ i : Fin n, x i * y i := sum_finZeroPad_eq h (fun j => x j * y j)

private lemma sum_finZeroPad_abs_mul_eq {n m : ℕ} (h : n ≤ m)
    (x y : Fin n → ℝ) :
    (∑ i : Fin m, |finZeroPad n m x i| * |finZeroPad n m y i|) =
      ∑ i : Fin n, |x i| * |y i| := by
  have hterm :
      ∀ i : Fin m,
        |finZeroPad n m x i| * |finZeroPad n m y i| =
          finZeroPad n m (fun j => |x j| * |y j|) i := by
    intro i
    by_cases hi : i.val < n
    · simp [finZeroPad, hi]
    · simp [finZeroPad, hi]
  calc
    (∑ i : Fin m, |finZeroPad n m x i| * |finZeroPad n m y i|) =
        ∑ i : Fin m, finZeroPad n m (fun j => |x j| * |y j|) i := by
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = ∑ i : Fin n, |x i| * |y i| :=
        sum_finZeroPad_eq h (fun j => |x j| * |y j|)

/-- Pairwise dot product for arbitrary length by zero-padding to `2^(Nat.clog 2 n)`.

This is the standard balanced-tree/pairwise route for non-power-of-two lengths:
pad the product list by zeros to the next power of two, then use the perfect
balanced tree.  The zero products contribute no rounding error because the
relative-error multiplication model implies `fl_mul 0 0 = 0`. -/
noncomputable def fl_clog2PairwiseDotProduct (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  let r := Nat.clog 2 n
  fl_sumTreeDotProduct fp (SumTree.balancedTree r)
    (finZeroPad n (2 ^ r) x) (finZeroPad n (2 ^ r) y)

/-- Arbitrary-length padded pairwise dot-product forward error bound.

`Nat.clog 2 n` is mathlib's natural-number ceiling logarithm: the least `r`
with `n <= 2^r`.  Thus this theorem is the formal `gamma_{ceil(log2 n)+1}`
version of the product-first pairwise dot-product bound. -/
theorem clog2PairwiseDotProduct_error_bound (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hγ : gammaValid fp (Nat.clog 2 n + 1)) :
    |fl_clog2PairwiseDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      gamma fp (Nat.clog 2 n + 1) * ∑ i : Fin n, |x i| * |y i| := by
  let r := Nat.clog 2 n
  have hpad : n ≤ 2 ^ r := by
    simpa [r] using Nat.le_pow_clog Nat.one_lt_two n
  have hbound :=
    balancedTreeDotProduct_error_bound fp r
      (finZeroPad n (2 ^ r) x) (finZeroPad n (2 ^ r) y)
      (by simpa [r] using hγ)
  have hsum :
      (∑ i : Fin (2 ^ r),
        finZeroPad n (2 ^ r) x i * finZeroPad n (2 ^ r) y i) =
        ∑ i : Fin n, x i * y i :=
    sum_finZeroPad_mul_eq hpad x y
  have habs :
      (∑ i : Fin (2 ^ r),
        |finZeroPad n (2 ^ r) x i| * |finZeroPad n (2 ^ r) y i|) =
        ∑ i : Fin n, |x i| * |y i| :=
    sum_finZeroPad_abs_mul_eq hpad x y
  simpa [fl_clog2PairwiseDotProduct, r, hsum, habs] using hbound

/-- Higham (3.4) for any binary-tree order of evaluation.

Every `SumTree n` performs the same rounded products and then combines them in
an arbitrary binary order.  Since `depth t + 1 ≤ n`, one multiplication plus
all additions on a root-to-leaf path fit inside the printed `γ_n` radius.  The
same per-component witness is packaged as a perturbation of either input. -/
theorem sumTreeDotProduct_backward_stable_any_order (fp : FPModel) {n : ℕ}
    (t : SumTree n) (x y : Fin n → ℝ) (hγ : gammaValid fp n) :
    ∃ Δx Δy : Fin n → ℝ,
      (∀ i, |Δx i| ≤ gamma fp n * |x i|) ∧
      (∀ i, |Δy i| ≤ gamma fp n * |y i|) ∧
      fl_sumTreeDotProduct fp t x y =
        ∑ i : Fin n, (x i + Δx i) * y i ∧
      fl_sumTreeDotProduct fp t x y =
        ∑ i : Fin n, x i * (y i + Δy i) := by
  have hdepth : t.depth + 1 ≤ n := by
    have ht := SumTree.depth_le t
    have hn := t.n_pos
    omega
  have hγdepth : gammaValid fp (t.depth + 1) :=
    gammaValid_mono fp hdepth hγ
  obtain ⟨η, hη, hfl⟩ :=
    sumTreeDotProduct_backward_error fp t x y hγdepth
  have hηn : ∀ i, |η i| ≤ gamma fp n := by
    intro i
    exact le_trans (hη i) (gamma_mono fp hdepth hγ)
  let Δx : Fin n → ℝ := fun i => x i * η i
  let Δy : Fin n → ℝ := fun i => y i * η i
  refine ⟨Δx, Δy, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [show |Δx i| = |x i| * |η i| by simp [Δx, abs_mul],
      mul_comm (gamma fp n)]
    exact mul_le_mul_of_nonneg_left (hηn i) (abs_nonneg (x i))
  · intro i
    rw [show |Δy i| = |y i| * |η i| by simp [Δy, abs_mul],
      mul_comm (gamma fp n)]
    exact mul_le_mul_of_nonneg_left (hηn i) (abs_nonneg (y i))
  · rw [hfl]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Δx]
    ring
  · rw [hfl]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Δy]
    ring

/-- Fully permuted form of Higham (3.4).

The permutation chooses the order in which the products enter the arbitrary
summation tree.  The resulting perturbations are transported back to the
original coordinates, so the conclusion is stated for the original `x` and
`y`, not for their reordered copies. -/
theorem sumTreeDotProduct_backward_stable_any_permuted_order
    (fp : FPModel) {n : ℕ} (t : SumTree n) (σ : Equiv.Perm (Fin n))
    (x y : Fin n → ℝ) (hγ : gammaValid fp n) :
    ∃ Δx Δy : Fin n → ℝ,
      (∀ i, |Δx i| ≤ gamma fp n * |x i|) ∧
      (∀ i, |Δy i| ≤ gamma fp n * |y i|) ∧
      fl_sumTreeDotProduct fp t (fun i => x (σ i)) (fun i => y (σ i)) =
        ∑ i : Fin n, (x i + Δx i) * y i ∧
      fl_sumTreeDotProduct fp t (fun i => x (σ i)) (fun i => y (σ i)) =
        ∑ i : Fin n, x i * (y i + Δy i) := by
  obtain ⟨δx, δy, hδx, hδy, heqx, heqy⟩ :=
    sumTreeDotProduct_backward_stable_any_order fp t
      (fun i => x (σ i)) (fun i => y (σ i)) hγ
  let Δx : Fin n → ℝ := fun i => δx (σ.symm i)
  let Δy : Fin n → ℝ := fun i => δy (σ.symm i)
  refine ⟨Δx, Δy, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [Δx] using hδx (σ.symm i)
  · intro i
    simpa [Δy] using hδy (σ.symm i)
  · calc
      fl_sumTreeDotProduct fp t (fun i => x (σ i)) (fun i => y (σ i))
          = ∑ i : Fin n, (x (σ i) + δx i) * y (σ i) := heqx
      _ = ∑ i : Fin n, (x i + Δx i) * y i := by
        calc
          (∑ i : Fin n, (x (σ i) + δx i) * y (σ i)) =
              ∑ i : Fin n, (x (σ i) + Δx (σ i)) * y (σ i) := by
                apply Finset.sum_congr rfl
                intro i _hi
                simp [Δx]
          _ = ∑ i : Fin n, (x i + Δx i) * y i :=
                Equiv.sum_comp σ (fun i => (x i + Δx i) * y i)
  · calc
      fl_sumTreeDotProduct fp t (fun i => x (σ i)) (fun i => y (σ i))
          = ∑ i : Fin n, x (σ i) * (y (σ i) + δy i) := heqy
      _ = ∑ i : Fin n, x i * (y i + Δy i) := by
        calc
          (∑ i : Fin n, x (σ i) * (y (σ i) + δy i)) =
              ∑ i : Fin n, x (σ i) * (y (σ i) + Δy (σ i)) := by
                apply Finset.sum_congr rfl
                intro i _hi
                simp [Δy]
          _ = ∑ i : Fin n, x i * (y i + Δy i) :=
                Equiv.sum_comp σ (fun i => x i * (y i + Δy i))

end NumStability
