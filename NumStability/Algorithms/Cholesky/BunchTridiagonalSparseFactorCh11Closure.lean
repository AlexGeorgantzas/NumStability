/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Theorem 11.7: support-aware tridiagonal factorization

The dense Schur kernels used by the general mixed-pivot development execute a
rounded subtraction even when tridiagonal structure makes the update exactly
zero.  In the abstract `FPModel`, `fl_sub x 0 = x` is deliberately not a global
law, so that dense implementation necessarily accumulates an `O(nu)` copying
budget.  Higham's Theorem 11.7 instead counts only the nonzero operations of the
tridiagonal algorithm.

This file gives that source-faithful policy.  `skipZeroSubFP fp` delegates every
genuine arithmetic operation to `fp`, but copies `x` when the subtrahend is
exactly zero.  It is itself an `FPModel`, with the same unit roundoff.  Thus all
existing executable schedule, factor, growth, middle-solve, and sparse outer
solve code can be instantiated with it; only structurally vacuous Schur
updates are skipped.

The remainder of the file derives the local rounded explicit-inverse residuals
and assembles a dimension-independent factorization error directly along a
`TriGrowthBounded` schedule.  No `FlMixedPivots` or target-shaped residual
premise is used.
-/
import NumStability.Algorithms.Cholesky.BunchTridiagonalSparseSolveCh11Closure
import NumStability.Algorithms.Cholesky.TwoByTwoSchurStepCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.SparseFactor

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed
open NumStability.Ch11Closure.BunchTri
open NumStability.Ch11Closure.BunchTriGrowth
open NumStability.Ch11Closure.TriGrowthInv
open NumStability.Ch11Closure.TwoStep

/-! ## A standard-model implementation that skips structural zero updates -/

/-- The support-aware arithmetic policy used by the tridiagonal factorization.
Every operation is the original operation of `fp`, except that `x - 0` is a
copy and therefore performs no rounded arithmetic. -/
noncomputable def skipZeroSubFP (fp : FPModel) : FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => if y = 0 then x else fp.fl_sub x y
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := fp.fl_sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    by_cases hy : y = 0
    · subst y
      refine ⟨0, ?_, ?_⟩
      · simpa using fp.u_nonneg
      · simp
    · obtain ⟨δ, hδ, heq⟩ := fp.model_sub x y
      refine ⟨δ, hδ, ?_⟩
      simp only [hy, if_false]
      exact heq
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := fp.model_sqrt

@[simp] theorem skipZeroSubFP_u (fp : FPModel) : (skipZeroSubFP fp).u = fp.u := rfl
@[simp] theorem skipZeroSubFP_fl_add (fp : FPModel) (x y : ℝ) :
    (skipZeroSubFP fp).fl_add x y = fp.fl_add x y := rfl
@[simp] theorem skipZeroSubFP_fl_mul (fp : FPModel) (x y : ℝ) :
    (skipZeroSubFP fp).fl_mul x y = fp.fl_mul x y := rfl
@[simp] theorem skipZeroSubFP_fl_div (fp : FPModel) (x y : ℝ) :
    (skipZeroSubFP fp).fl_div x y = fp.fl_div x y := rfl
@[simp] theorem skipZeroSubFP_fl_sub_zero (fp : FPModel) (x : ℝ) :
    (skipZeroSubFP fp).fl_sub x 0 = x := by simp [skipZeroSubFP]

theorem flSchurCompl_skipZero_of_ne_corner (fp : FPModel) {n : ℕ}
    (A : Fin (n + 1) → Fin (n + 1) → ℝ) (hA : IsSymTridiagonal (n + 1) A)
    (hA00 : A 0 0 ≠ 0) (i j : Fin n) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
    flSchurCompl n (skipZeroSubFP fp) A i j = A i.succ j.succ := by
  rw [flSchurCompl_eq_sub_zero_of_ne_corner (skipZeroSubFP fp) A hA hA00 i j hne]
  exact skipZeroSubFP_fl_sub_zero fp _

theorem flSchurCompl2_skipZero_of_ne_corner (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (hA : IsSymTridiagonal (m + 2) A)
    (i j : Fin m) (hne : i.val ≠ 0 ∨ j.val ≠ 0) :
    flSchurCompl2 m (skipZeroSubFP fp) A i j = A i.succ.succ j.succ.succ := by
  rw [flSchurCompl2_eq_sub_zero_of_ne_corner (skipZeroSubFP fp) A hA i j hne]
  exact skipZeroSubFP_fl_sub_zero fp _

/-! ## Rounded two-term exact identities -/

/-- Under `u ≤ 1/2`, an exact product is at most twice the magnitude of its
rounded product.  This is the only conversion needed to express the explicit
inverse residual relative to the *computed* pivot path. -/
theorem abs_mul_le_two_abs_fl_mul (fp : FPModel) (hu : fp.u ≤ 1 / 2)
    (x y : ℝ) : |x * y| ≤ 2 * |fp.fl_mul x y| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_mul x y
  have hlow : (1 : ℝ) / 2 ≤ |1 + δ| := by
    have htri : 1 ≤ |1 + δ| + |δ| := by
      simpa [abs_neg, add_assoc] using (abs_add_le (1 + δ) (-δ))
    linarith
  have habs : |fp.fl_mul x y| = |x * y| * |1 + δ| := by
    rw [heq, abs_mul]
  calc
    |x * y| ≤ 2 * (|x * y| * |1 + δ|) := by
      nlinarith [abs_nonneg (x * y)]
    _ = 2 * |fp.fl_mul x y| := by rw [habs]

/-- If two exact products satisfy a two-term identity, rounding the two
products separately leaves a residual bounded by `2u` times the corresponding
computed absolute path. -/
theorem two_rounded_products_residual (fp : FPModel) (hu : fp.u ≤ 1 / 2)
    (a0 a1 x0 y0 x1 y1 rhs : ℝ)
    (hexact : a0 * (x0 * y0) + a1 * (x1 * y1) = rhs) :
    |a0 * fp.fl_mul x0 y0 + a1 * fp.fl_mul x1 y1 - rhs|
      ≤ 2 * fp.u *
          (|a0| * |fp.fl_mul x0 y0| + |a1| * |fp.fl_mul x1 y1|) := by
  obtain ⟨δ0, hδ0, hw0⟩ := fp.model_mul x0 y0
  obtain ⟨δ1, hδ1, hw1⟩ := fp.model_mul x1 y1
  have hsplit :
      a0 * fp.fl_mul x0 y0 + a1 * fp.fl_mul x1 y1 - rhs =
        a0 * (x0 * y0) * δ0 + a1 * (x1 * y1) * δ1 := by
    rw [hw0, hw1]
    nlinarith [hexact]
  rw [hsplit]
  calc
    |a0 * (x0 * y0) * δ0 + a1 * (x1 * y1) * δ1|
        ≤ |a0 * (x0 * y0) * δ0| + |a1 * (x1 * y1) * δ1| := abs_add_le _ _
    _ = |a0| * |x0 * y0| * |δ0| + |a1| * |x1 * y1| * |δ1| := by
          simp only [abs_mul]
    _ ≤ |a0| * |x0 * y0| * fp.u + |a1| * |x1 * y1| * fp.u := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hδ0 (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
            (mul_le_mul_of_nonneg_left hδ1 (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ ≤ |a0| * (2 * |fp.fl_mul x0 y0|) * fp.u
          + |a1| * (2 * |fp.fl_mul x1 y1|) * fp.u := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (abs_mul_le_two_abs_fl_mul fp hu x0 y0)
                (abs_nonneg _)) fp.u_nonneg)
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (abs_mul_le_two_abs_fl_mul fp hu x1 y1)
                (abs_nonneg _)) fp.u_nonneg)
    _ = 2 * fp.u *
          (|a0| * |fp.fl_mul x0 y0| + |a1| * |fp.fl_mul x1 y1|) := by ring

theorem symmetric_twoByTwo_inverse_row0_identity
    (a b c z d : ℝ) (hd : d = a * c - b ^ 2) (hd0 : d ≠ 0) :
    a * (z * (-b / d)) + b * (z * (a / d)) = 0 := by
  rw [hd] at hd0 ⊢
  field_simp [hd0]
  ring

theorem symmetric_twoByTwo_inverse_row1_identity
    (a b c z d : ℝ) (hd : d = a * c - b ^ 2) (hd0 : d ≠ 0) :
    b * (z * (-b / d)) + c * (z * (a / d)) = z := by
  rw [hd] at hd0 ⊢
  field_simp [hd0]
  ring

/-- The actual rounded explicit-inverse multiplier at the unique nonzero
tridiagonal corner satisfies all four pivot row/column residual bounds. -/
theorem flMixedMult2_corner_residuals (fp : FPModel) (hu : fp.u ≤ 1 / 2)
    {m : ℕ} (A : Fin (m + 3) → Fin (m + 3) → ℝ)
    (hA : IsSymTridiagonal (m + 3) A)
    (hdet : mixedDet2 (m + 1) A ≠ 0) :
    let w0 := flMixedMult2 (m + 1) fp A 0 0
    let w1 := flMixedMult2 (m + 1) fp A 0 1
    |A 0 0 * w0 + A 0 (oneIdx (m + 1)) * w1 - A 0 (0 : Fin (m + 1)).succ.succ|
        ≤ 2 * fp.u * pivotRowPathAbs (m + 1) fp A 0 0 ∧
    |A (oneIdx (m + 1)) 0 * w0 + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1
        - A (oneIdx (m + 1)) (0 : Fin (m + 1)).succ.succ|
        ≤ 2 * fp.u * pivotRowPathAbs (m + 1) fp A 1 0 ∧
    |w0 * A 0 0 + w1 * A (oneIdx (m + 1)) 0 - A (0 : Fin (m + 1)).succ.succ 0|
        ≤ 2 * fp.u * pivotColPathAbs (m + 1) fp A 0 0 ∧
    |w0 * A 0 (oneIdx (m + 1)) + w1 * A (oneIdx (m + 1)) (oneIdx (m + 1))
        - A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1))|
        ≤ 2 * fp.u * pivotColPathAbs (m + 1) fp A 0 1 := by
  dsimp only
  have hsym01 : A 0 (oneIdx (m + 1)) = A (oneIdx (m + 1)) 0 :=
    hA.1 0 (oneIdx (m + 1))
  have hsym01v : A 0 (1 : Fin (m + 3)) = A (1 : Fin (m + 3)) 0 := hA.1 0 1
  have hsym12 :
      A (oneIdx (m + 1)) (0 : Fin (m + 1)).succ.succ =
        A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1)) :=
    hA.1 (oneIdx (m + 1)) (0 : Fin (m + 1)).succ.succ
  have hz02 : A 0 (0 : Fin (m + 1)).succ.succ = 0 := by
    apply hA.2
    left
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  have hz02v : A 0 (2 : Fin (m + 3)) = 0 := by simpa using hz02
  have hz20 : A (0 : Fin (m + 1)).succ.succ 0 = 0 := by
    apply hA.2
    right
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  have hz02v' : A 0 (2 : Fin (m + 3)) = 0 := by simpa using hz02
  have hz20v' : A (2 : Fin (m + 3)) 0 = 0 := by simpa using hz20
  have hz20v : A (2 : Fin (m + 3)) 0 = 0 := by simpa using hz20
  have hdetform : mixedDet2 (m + 1) A =
      A 0 0 * A (oneIdx (m + 1)) (oneIdx (m + 1))
        - A (oneIdx (m + 1)) 0 ^ 2 := by
    unfold mixedDet2
    rw [hsym01]
    ring
  have hex0 := symmetric_twoByTwo_inverse_row0_identity
    (A 0 0) (A (oneIdx (m + 1)) 0) (A (oneIdx (m + 1)) (oneIdx (m + 1)))
    (A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1)))
    (mixedDet2 (m + 1) A) hdetform hdet
  have hex1 := symmetric_twoByTwo_inverse_row1_identity
    (A 0 0) (A (oneIdx (m + 1)) 0) (A (oneIdx (m + 1)) (oneIdx (m + 1)))
    (A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1)))
    (mixedDet2 (m + 1) A) hdetform hdet
  have hr0 := two_rounded_products_residual fp hu
    (A 0 0) (A (oneIdx (m + 1)) 0)
    (A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1)))
    (-A (oneIdx (m + 1)) 0 / mixedDet2 (m + 1) A)
    (A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1)))
    (A 0 0 / mixedDet2 (m + 1) A) 0 hex0
  have hr1 := two_rounded_products_residual fp hu
    (A (oneIdx (m + 1)) 0) (A (oneIdx (m + 1)) (oneIdx (m + 1)))
    (A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1)))
    (-A (oneIdx (m + 1)) 0 / mixedDet2 (m + 1) A)
    (A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1)))
    (A 0 0 / mixedDet2 (m + 1) A)
    (A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1))) hex1
  rw [← flMixedMult2_corner0 fp A hA, ← flMixedMult2_corner1 fp A hA] at hr0 hr1
  have hrow0 :
      |A 0 0 * flMixedMult2 (m + 1) fp A 0 0
          + A 0 (oneIdx (m + 1)) * flMixedMult2 (m + 1) fp A 0 1
          - A 0 (0 : Fin (m + 1)).succ.succ|
        ≤ 2 * fp.u * pivotRowPathAbs (m + 1) fp A 0 0 := by
    rw [hz02, sub_zero, hsym01]
    simpa [pivotRowPathAbs, Fin.sum_univ_two, leadingTwoBlock_apply, hsym01,
      hsym01v] using hr0
  have hrow1 :
      |A (oneIdx (m + 1)) 0 * flMixedMult2 (m + 1) fp A 0 0
          + A (oneIdx (m + 1)) (oneIdx (m + 1)) * flMixedMult2 (m + 1) fp A 0 1
          - A (oneIdx (m + 1)) (0 : Fin (m + 1)).succ.succ|
        ≤ 2 * fp.u * pivotRowPathAbs (m + 1) fp A 1 0 := by
    rw [hsym12]
    simpa [pivotRowPathAbs, Fin.sum_univ_two, leadingTwoBlock_apply, hsym01,
      hsym01v] using hr1
  have hcol0 :
      |flMixedMult2 (m + 1) fp A 0 0 * A 0 0
          + flMixedMult2 (m + 1) fp A 0 1 * A (oneIdx (m + 1)) 0
          - A (0 : Fin (m + 1)).succ.succ 0|
        ≤ 2 * fp.u * pivotColPathAbs (m + 1) fp A 0 0 := by
    rw [hz20, sub_zero]
    simpa [pivotColPathAbs, Fin.sum_univ_two, leadingTwoBlock_apply, hsym01, hsym01v,
      mul_comm, mul_left_comm, mul_assoc] using hr0
  have hcol1 :
      |flMixedMult2 (m + 1) fp A 0 0 * A 0 (oneIdx (m + 1))
          + flMixedMult2 (m + 1) fp A 0 1 * A (oneIdx (m + 1)) (oneIdx (m + 1))
          - A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1))|
        ≤ 2 * fp.u * pivotColPathAbs (m + 1) fp A 0 1 := by
    rw [hsym01]
    simpa [pivotColPathAbs, Fin.sum_univ_two, leadingTwoBlock_apply, hsym01, hsym01v,
      mul_comm, mul_left_comm, mul_assoc] using hr1
  exact ⟨hrow0, hrow1, hcol0, hcol1⟩

/-- The unique nonzero 2x2 Schur update has a fully derived constant local
factorization residual.  The proof uses the computed explicit-inverse residual
above, rather than the false coefficient-one absolute coupling carried by the
old generic `FlMixedPivots` interface. -/
theorem flMixedMult2_corner_trailing_residual (fp : FPModel)
    (hval : gammaValid fp 3) (hu : fp.u ≤ 1 / 2)
    {m : ℕ} (A : Fin (m + 3) → Fin (m + 3) → ℝ)
    (hA : IsSymTridiagonal (m + 3) A)
    (hdet : mixedDet2 (m + 1) A ≠ 0) :
    |pivotPath2 (m + 1) fp A 0 0 + flSchurCompl2 (m + 1) fp A 0 0
        - A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ|
      ≤ 6 * gamma fp 3 *
          (|A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ|
            + pivotPath2Abs (m + 1) fp A 0 0) := by
  let w0 := flMixedMult2 (m + 1) fp A 0 0
  let w1 := flMixedMult2 (m + 1) fp A 0 1
  let z := A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1))
  have hsym01 : A 0 (oneIdx (m + 1)) = A (oneIdx (m + 1)) 0 :=
    hA.1 0 (oneIdx (m + 1))
  have hsym12 : A (oneIdx (m + 1)) (0 : Fin (m + 1)).succ.succ = z := by
    dsimp [z]
    exact hA.1 (oneIdx (m + 1)) (0 : Fin (m + 1)).succ.succ
  have hsym01v : A 0 (1 : Fin (m + 3)) = A (1 : Fin (m + 3)) 0 := hA.1 0 1
  have hsym12v : A (1 : Fin (m + 3)) (2 : Fin (m + 3)) = z := by
    simpa [oneIdx, z] using hsym12
  have hz02 : A 0 (0 : Fin (m + 1)).succ.succ = 0 := by
    apply hA.2
    left
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  have hz20 : A (0 : Fin (m + 1)).succ.succ 0 = 0 := by
    apply hA.2
    right
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  have hz02v2 : A 0 (2 : Fin (m + 3)) = 0 := by simpa using hz02
  have hz20v2 : A (2 : Fin (m + 3)) 0 = 0 := by simpa using hz20
  have hres := flMixedMult2_corner_residuals fp hu A hA hdet
  dsimp only at hres
  obtain ⟨hr0, hr1, _, _⟩ := hres
  have hppa :
      |w0| * pivotRowPathAbs (m + 1) fp A 0 0
          + |w1| * pivotRowPathAbs (m + 1) fp A 1 0 =
        pivotPath2Abs (m + 1) fp A 0 0 := by
    dsimp [w0, w1]
    simp only [pivotRowPathAbs, pivotPath2Abs, Fin.sum_univ_two,
      leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
    ring
  have hcoupleEq :
      pivotPath2 (m + 1) fp A 0 0 - w1 * z =
        w0 * (A 0 0 * w0 + A 0 (oneIdx (m + 1)) * w1)
          + w1 * (A (oneIdx (m + 1)) 0 * w0
            + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1 - z) := by
    dsimp [w0, w1]
    rw [pivotPath2, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [leadingTwoBlock_apply, embedTwo_zero, embedTwo_one_eq]
    simp only [oneIdx] at hsym01 ⊢
    simp only [show (Fin.succ 0 : Fin (m + 3)) = 1 from rfl]
    rw [hsym01v]
    ring
  have hcouple :
      |pivotPath2 (m + 1) fp A 0 0 - w1 * z|
        ≤ 2 * fp.u * pivotPath2Abs (m + 1) fp A 0 0 := by
    rw [hcoupleEq]
    calc
      |w0 * (A 0 0 * w0 + A 0 (oneIdx (m + 1)) * w1)
          + w1 * (A (oneIdx (m + 1)) 0 * w0
            + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1 - z)|
          ≤ |w0| * |A 0 0 * w0 + A 0 (oneIdx (m + 1)) * w1|
              + |w1| * |A (oneIdx (m + 1)) 0 * w0
                + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1 - z| := by
            simpa only [abs_mul] using abs_add_le
              (w0 * (A 0 0 * w0 + A 0 (oneIdx (m + 1)) * w1))
              (w1 * (A (oneIdx (m + 1)) 0 * w0
                + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1 - z))
      _ ≤ |w0| * (2 * fp.u * pivotRowPathAbs (m + 1) fp A 0 0)
            + |w1| * (2 * fp.u * pivotRowPathAbs (m + 1) fp A 1 0) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            simpa [w0, w1, hz02, hz02v2, hsym01, z] using hr0
          · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            simpa [w0, w1, hsym12, hsym12v, z] using hr1
      _ = 2 * fp.u * pivotPath2Abs (m + 1) fp A 0 0 := by
          rw [← hppa]
          ring
  have hrow1abs :
      |A (oneIdx (m + 1)) 0 * w0
          + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1|
        ≤ pivotRowPathAbs (m + 1) fp A 1 0 := by
    calc
      |A (oneIdx (m + 1)) 0 * w0
          + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1|
        ≤ |A (oneIdx (m + 1)) 0 * w0|
            + |A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1| := abs_add_le _ _
      _ = pivotRowPathAbs (m + 1) fp A 1 0 := by
          dsimp [w0, w1]
          simp [pivotRowPathAbs, Fin.sum_univ_two, leadingTwoBlock_apply, abs_mul]
  have hzbound :
      |w1| * |z| ≤ (1 + 2 * fp.u) * pivotPath2Abs (m + 1) fp A 0 0 := by
    have hztri :
        |z| ≤
          |A (oneIdx (m + 1)) 0 * w0
              + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1|
            + |A (oneIdx (m + 1)) 0 * w0
              + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1 - z| := by
      let ew := A (oneIdx (m + 1)) 0 * w0
        + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1
      calc
        |z| = |ew + -(ew - z)| := by congr 1; dsimp [ew]; ring
        _ ≤ |ew| + |-(ew - z)| := abs_add_le _ _
        _ = |A (oneIdx (m + 1)) 0 * w0
              + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1|
            + |A (oneIdx (m + 1)) 0 * w0
              + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1 - z| := by
          rw [abs_sub_comm]
          simp [ew]
    have hzrow :
        |z| ≤ (1 + 2 * fp.u) * pivotRowPathAbs (m + 1) fp A 1 0 := by
      calc
        |z| ≤
            |A (oneIdx (m + 1)) 0 * w0
                + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1|
              + |A (oneIdx (m + 1)) 0 * w0
                + A (oneIdx (m + 1)) (oneIdx (m + 1)) * w1 - z| := hztri
        _ ≤ pivotRowPathAbs (m + 1) fp A 1 0
              + 2 * fp.u * pivotRowPathAbs (m + 1) fp A 1 0 := by
            exact add_le_add hrow1abs
              (by simpa [w0, w1, hsym12, hsym12v, z] using hr1)
        _ = (1 + 2 * fp.u) * pivotRowPathAbs (m + 1) fp A 1 0 := by ring
    calc
      |w1| * |z| ≤ |w1| * ((1 + 2 * fp.u) *
          pivotRowPathAbs (m + 1) fp A 1 0) :=
        mul_le_mul_of_nonneg_left hzrow (abs_nonneg _)
      _ ≤ (1 + 2 * fp.u) * pivotPath2Abs (m + 1) fp A 0 0 := by
        have hpart : |w1| * pivotRowPathAbs (m + 1) fp A 1 0
            ≤ pivotPath2Abs (m + 1) fp A 0 0 := by
          rw [← hppa]
          exact le_add_of_nonneg_left
            (mul_nonneg (abs_nonneg _) (by
              rw [pivotRowPathAbs]
              exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        nlinarith [hpart, fp.u_nonneg]
  have hzbound2 : |w1| * |z| ≤ 2 * pivotPath2Abs (m + 1) fp A 0 0 := by
    have hcoef : 1 + 2 * fp.u ≤ 2 := by linarith
    have hppa0 : 0 ≤ pivotPath2Abs (m + 1) fp A 0 0 := by
      rw [pivotPath2Abs]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
    exact hzbound.trans (mul_le_mul_of_nonneg_right hcoef hppa0)
  have hround0 := schur2_dot_residual fp A (0 : Fin (m + 1)) (0 : Fin (m + 1))
  have hcube := cube_sub_one_le_two_gamma3 fp hval
  have hcubenonneg : 0 ≤ (1 + fp.u) ^ 3 - 1 := by
    nlinarith [fp.u_nonneg, mul_nonneg fp.u_nonneg fp.u_nonneg,
      mul_nonneg (mul_nonneg fp.u_nonneg fp.u_nonneg) fp.u_nonneg]
  have hround :
      |w1 * z + flSchurCompl2 (m + 1) fp A 0 0
          - A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ|
        ≤ 2 * gamma fp 3 *
          (|A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ|
            + 2 * pivotPath2Abs (m + 1) fp A 0 0) := by
    have harg :
        |A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ|
            + |flMixedMult2 (m + 1) fp A 0 0| *
                |A (0 : Fin (m + 1)).succ.succ 0|
            + |flMixedMult2 (m + 1) fp A 0 1| *
                |A (0 : Fin (m + 1)).succ.succ (oneIdx (m + 1))|
          ≤ |A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ|
              + 2 * pivotPath2Abs (m + 1) fp A 0 0 := by
      rw [hz20, abs_zero, mul_zero, add_zero]
      simpa [w1, z] using add_le_add_left hzbound2
        |A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ|
    have harg0 : 0 ≤
        |A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ|
          + 2 * pivotPath2Abs (m + 1) fp A 0 0 := by
      have hppa0 : 0 ≤ pivotPath2Abs (m + 1) fp A 0 0 := by
        rw [pivotPath2Abs]
        exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
      exact add_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) hppa0)
    have hstep := mul_le_mul_of_nonneg_left harg hcubenonneg
    have hstep2 := mul_le_mul_of_nonneg_right hcube harg0
    have hfin := hround0.trans (hstep.trans hstep2)
    simpa [w0, w1, z, hz20, hz20v2] using hfin
  have hsplit :
      pivotPath2 (m + 1) fp A 0 0 + flSchurCompl2 (m + 1) fp A 0 0
          - A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ =
        (pivotPath2 (m + 1) fp A 0 0 - w1 * z)
          + (w1 * z + flSchurCompl2 (m + 1) fp A 0 0
            - A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ) := by ring
  rw [hsplit]
  calc
    |(pivotPath2 (m + 1) fp A 0 0 - w1 * z)
        + (w1 * z + flSchurCompl2 (m + 1) fp A 0 0
          - A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ)|
      ≤ |pivotPath2 (m + 1) fp A 0 0 - w1 * z|
          + |w1 * z + flSchurCompl2 (m + 1) fp A 0 0
            - A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ| :=
        abs_add_le _ _
    _ ≤ 2 * fp.u * pivotPath2Abs (m + 1) fp A 0 0
          + 2 * gamma fp 3 *
            (|A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ|
              + 2 * pivotPath2Abs (m + 1) fp A 0 0) := add_le_add hcouple hround
    _ ≤ 6 * gamma fp 3 *
          (|A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ|
            + pivotPath2Abs (m + 1) fp A 0 0) := by
      have huγ : fp.u ≤ gamma fp 3 := u_le_gamma fp (by norm_num) hval
      have hg0 := gamma_nonneg fp hval
      have hA0 := abs_nonneg
        (A (0 : Fin (m + 1)).succ.succ (0 : Fin (m + 1)).succ.succ)
      have hppa0 : 0 ≤ pivotPath2Abs (m + 1) fp A 0 0 := by
        rw [pivotPath2Abs]
        exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
      nlinarith

/-! ## Structural product reductions used by the sparse induction -/

/-- Signed counterpart of `productEntry_consOne_split`. -/
theorem mixedProduct_consOne_trailing (fp : FPModel) {n : ℕ}
    (s : PivotSchedule n) (A : Fin (n + 1) → Fin (n + 1) → ℝ) (i j : Fin n) :
    (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
        flMixedL fp s.consOne A i.succ p * flMixedD fp s.consOne A p q *
          flMixedL fp s.consOne A j.succ q) =
      fp.fl_div (A i.succ 0) (A 0 0) * A 0 0 * fp.fl_div (A j.succ 0) (A 0 0)
        + (∑ p : Fin n, ∑ q : Fin n,
          flMixedL fp s (flSchurCompl n fp A) i p *
            flMixedD fp s (flSchurCompl n fp A) p q *
              flMixedL fp s (flSchurCompl n fp A) j q) := by
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [Fin.sum_univ_succ]
    have hz : (∑ q : Fin n,
        flMixedL fp s.consOne A i.succ 0 * flMixedD fp s.consOne A 0 q.succ *
          flMixedL fp s.consOne A j.succ q.succ) = 0 := by
      apply Finset.sum_eq_zero
      intro q _
      simp
    rw [hz, add_zero]
    simp
  · apply Finset.sum_congr rfl
    intro p _
    rw [Fin.sum_univ_succ]
    have hz : flMixedL fp s.consOne A i.succ p.succ *
        flMixedD fp s.consOne A p.succ 0 * flMixedL fp s.consOne A j.succ 0 = 0 := by
      simp
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro q _
    simp

/-- Every nonempty mixed schedule reproduces its leading `(0,0)` entry exactly. -/
theorem mixedProduct_head00 (fp : FPModel) {n : ℕ}
    (s : PivotSchedule (n + 1)) (A : Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
      flMixedL fp s A 0 p * flMixedD fp s A p q * flMixedL fp s A 0 q) = A 0 0 := by
  cases s with
  | consOne s' =>
      simp only [Fin.sum_univ_succ, flMixedL_consOne_00, flMixedL_consOne_0s,
        flMixedD_consOne_00,
        zero_mul, mul_zero, one_mul, mul_one, add_zero, Finset.sum_const_zero]
  | consTwo s' => exact product_consTwo_00 fp s' A

theorem oneByOne_exact_corner_path_le (M0 a c : ℝ)
    (hchoice : BunchTridiagonalPivotChoice M0 a c PivotSize.one)
    (ha : a ≠ 0) : |c * c / a| ≤ M0 / bunchTridiagonalAlpha := by
  have hα := bunch_tridiagonal_alpha_pos
  have haabs : 0 < |a| := abs_pos.mpr ha
  have htest := bunch_tridiagonal_pivot_choice_one_threshold M0 a c hchoice
  rw [abs_div, abs_mul]
  apply (div_le_div_iff₀ haabs hα).2
  nlinarith [sq_abs c]

/-- A bounded accepted 2x2 tridiagonal pivot has nonzero exact determinant. -/
theorem mixedDet2_ne_zero_of_growth_bounded (M0 τ : ℝ) (hM0 : 0 < M0)
    (hslack : bunchTridiagonalAlpha * τ < M0) {m : ℕ}
    (A : Fin (m + 3) → Fin (m + 3) → ℝ)
    (hA : IsSymTridiagonal (m + 3) A)
    (hchoice : BunchTridiagonalPivotChoice M0 (A 0 0) (A (oneIdx (m + 1)) 0)
      PivotSize.two)
    (ha22 : |A (oneIdx (m + 1)) (oneIdx (m + 1))| ≤ τ) :
    mixedDet2 (m + 1) A ≠ 0 := by
  have hsym : A 0 (oneIdx (m + 1)) = A (oneIdx (m + 1)) 0 :=
    hA.1 0 (oneIdx (m + 1))
  have hdetform : mixedDet2 (m + 1) A =
      A 0 0 * A (oneIdx (m + 1)) (oneIdx (m + 1))
        - A (oneIdx (m + 1)) 0 ^ 2 := by
    unfold mixedDet2
    rw [hsym]
    ring
  have ha21 := bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg
    M0 (A 0 0) (A (oneIdx (m + 1)) 0) hchoice hM0.le
  have hgap : 0 < M0 - bunchTridiagonalAlpha * τ := by linarith
  have hlower := twoByTwo_absdet_lower_decoupled' M0 τ (A 0 0)
    (A (oneIdx (m + 1)) 0) (A (oneIdx (m + 1)) (oneIdx (m + 1)))
    hchoice hM0 ha22
  have hleft : 0 < A (oneIdx (m + 1)) 0 ^ 2 *
      (M0 - bunchTridiagonalAlpha * τ) :=
    mul_pos (sq_pos_of_ne_zero ha21) hgap
  have hright : 0 < M0 * |mixedDet2 (m + 1) A| := by
    rw [hdetform]
    exact lt_of_lt_of_le hleft hlower
  exact abs_pos.mp (by nlinarith [hM0] : 0 < |mixedDet2 (m + 1) A|)

/-! ## Source-scale radius -/

/-- A fixed off-corner growth cap.  The global smallness assumption gives
`gamma_stages ≤ 1/50`, hence every active off-corner entry is bounded by
`(51/50) M0`. -/
noncomputable def bunchTriTauCap (M0 : ℝ) : ℝ := (51 / 50 : ℝ) * M0

/-- Dimension-independent factorization radius for the support-aware policy.
The summands dominate, respectively, 1x1 pivot rows, 1x1 corner updates, 2x2
pivot rows/columns, and 2x2 corner updates. -/
noncomputable def bunchTriSparseFactorRadius (fp : FPModel) (M0 : ℝ) : ℝ :=
  let τ := bunchTriTauCap M0
  fp.u * τ
    + 2 * gamma fp 3 * (τ + M0 / bunchTridiagonalAlpha)
    + 2 * fp.u * pathConstRC fp.u M0 τ
    + 6 * gamma fp 3 * (τ + pathConst2 fp.u M0 τ)

theorem bunchTriTauCap_nonneg (M0 : ℝ) (hM0 : 0 < M0) :
    0 ≤ bunchTriTauCap M0 := by unfold bunchTriTauCap; positivity

theorem bunchTriTauCap_ge (M0 : ℝ) (hM0 : 0 < M0) :
    M0 ≤ bunchTriTauCap M0 := by unfold bunchTriTauCap; nlinarith

theorem bunchTriTauCap_slack (M0 : ℝ) (hM0 : 0 < M0) :
    bunchTridiagonalAlpha * bunchTriTauCap M0 < M0 := by
  have hα := alpha_lt_three_quarters
  unfold bunchTriTauCap
  nlinarith

theorem sparseFactorRadius_summands_nonneg (fp : FPModel) (hval : gammaValid fp 3)
    (M0 : ℝ) (hM0 : 0 < M0) :
    0 ≤ fp.u * bunchTriTauCap M0 ∧
    0 ≤ 2 * gamma fp 3 * (bunchTriTauCap M0 + M0 / bunchTridiagonalAlpha) ∧
    0 ≤ 2 * fp.u * pathConstRC fp.u M0 (bunchTriTauCap M0) ∧
    0 ≤ 6 * gamma fp 3 *
      (bunchTriTauCap M0 + pathConst2 fp.u M0 (bunchTriTauCap M0)) := by
  have hτ0 := bunchTriTauCap_nonneg M0 hM0
  have hslack := bunchTriTauCap_slack M0 hM0
  have hrc := pathConstRC_nonneg fp.u M0 (bunchTriTauCap M0)
    fp.u_nonneg hM0 hτ0 hslack
  have hp2 := pathConst2_nonneg fp.u M0 (bunchTriTauCap M0)
    fp.u_nonneg hM0 hτ0 hslack
  have hα := bunch_tridiagonal_alpha_pos
  have hg := gamma_nonneg fp hval
  refine ⟨mul_nonneg fp.u_nonneg hτ0, ?_,
    mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg) hrc,
    mul_nonneg (mul_nonneg (by norm_num) hg) (add_nonneg hτ0 hp2)⟩
  exact mul_nonneg (mul_nonneg (by norm_num) hg)
    (add_nonneg hτ0 (div_nonneg hM0.le hα.le))

theorem bunchTriSparseFactorRadius_nonneg (fp : FPModel) (hval : gammaValid fp 3)
    (M0 : ℝ) (hM0 : 0 < M0) : 0 ≤ bunchTriSparseFactorRadius fp M0 := by
  obtain ⟨h1, h2, h3, h4⟩ := sparseFactorRadius_summands_nonneg fp hval M0 hM0
  unfold bunchTriSparseFactorRadius
  dsimp only
  linarith

theorem sparseFactorRadius_dom_oneRow (fp : FPModel) (hval : gammaValid fp 3)
    (M0 : ℝ) (hM0 : 0 < M0) :
    fp.u * bunchTriTauCap M0 ≤ bunchTriSparseFactorRadius fp M0 := by
  obtain ⟨h1, h2, h3, h4⟩ := sparseFactorRadius_summands_nonneg fp hval M0 hM0
  unfold bunchTriSparseFactorRadius
  dsimp only
  linarith

theorem sparseFactorRadius_dom_oneCorner (fp : FPModel) (hval : gammaValid fp 3)
    (M0 : ℝ) (hM0 : 0 < M0) :
    2 * gamma fp 3 * (bunchTriTauCap M0 + M0 / bunchTridiagonalAlpha)
      ≤ bunchTriSparseFactorRadius fp M0 := by
  obtain ⟨h1, h2, h3, h4⟩ := sparseFactorRadius_summands_nonneg fp hval M0 hM0
  unfold bunchTriSparseFactorRadius
  dsimp only
  linarith

theorem sparseFactorRadius_dom_twoRow (fp : FPModel) (hval : gammaValid fp 3)
    (M0 : ℝ) (hM0 : 0 < M0) :
    2 * fp.u * pathConstRC fp.u M0 (bunchTriTauCap M0)
      ≤ bunchTriSparseFactorRadius fp M0 := by
  obtain ⟨h1, h2, h3, h4⟩ := sparseFactorRadius_summands_nonneg fp hval M0 hM0
  unfold bunchTriSparseFactorRadius
  dsimp only
  linarith

theorem sparseFactorRadius_dom_twoCorner (fp : FPModel) (hval : gammaValid fp 3)
    (M0 : ℝ) (hM0 : 0 < M0) :
    6 * gamma fp 3 *
      (bunchTriTauCap M0 + pathConst2 fp.u M0 (bunchTriTauCap M0))
      ≤ bunchTriSparseFactorRadius fp M0 := by
  obtain ⟨h1, h2, h3, h4⟩ := sparseFactorRadius_summands_nonneg fp hval M0 hM0
  unfold bunchTriSparseFactorRadius
  dsimp only
  linarith

/-! ## Dimension-independent schedule-level factorization residual -/

/-- The executable mixed factors produced with the structural-zero policy have
a componentwise factorization residual bounded independently of the matrix
dimension.  The only hypotheses are the actual accepted Bunch schedule with its
derived off-corner growth bound and ordinary no-breakdown. -/
theorem bunch_tridiagonal_sparse_factor_residual (fp : FPModel)
    (hval : gammaValid fp 3) (hu : fp.u ≤ 1 / 2)
    (M0 : ℝ) (hM0 : 0 < M0) :
    ∀ {k : ℕ} (s : PivotSchedule k) (A : Fin k → Fin k → ℝ),
      TriGrowthBounded (skipZeroSubFP fp) M0 (bunchTriTauCap M0) s A →
      ∀ I J : Fin k,
        |(∑ p : Fin k, ∑ q : Fin k,
            flMixedL (skipZeroSubFP fp) s A I p *
              flMixedD (skipZeroSubFP fp) s A p q *
                flMixedL (skipZeroSubFP fp) s A J q) - A I J|
          ≤ bunchTriSparseFactorRadius fp M0 := by
  intro k s
  induction s with
  | nil =>
      intro A _ I
      exact Fin.elim0 I
  | @consOne n s ih =>
      intro A hbounded I J
      obtain ⟨hA, hA00, hchoices, hoff, hrec⟩ := hbounded
      let q := skipZeroSubFP fp
      have hsym1 : ∀ i : Fin n, A 0 i.succ = A i.succ 0 := fun i => hA.1 0 i.succ
      have hrowAll := fl_blockLDLT_pivot_row_bound n q A hA00 hsym1
        (flMixedL q s.consOne A) (flMixedD q s.consOne A)
        (by simp) (by intro i; simp) (by intro j; simp) (by simp) (by intro j; simp)
      have hcolAll := fl_blockLDLT_pivot_col_bound n q A hA00
        (flMixedL q s.consOne A) (flMixedD q s.consOne A)
        (by simp) (by intro i; simp) (by intro j; simp) (by simp) (by intro i; simp)
      rcases Fin.eq_zero_or_eq_succ I with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨j, rfl⟩
        · rw [hrowAll.1, sub_self, abs_zero]
          exact bunchTriSparseFactorRadius_nonneg fp hval M0 hM0
        · calc
            |(∑ p, ∑ q_1, flMixedL q s.consOne A 0 p * flMixedD q s.consOne A p q_1 *
                flMixedL q s.consOne A j.succ q_1) - A 0 j.succ|
                ≤ q.u * |A 0 j.succ| := hrowAll.2 j
            _ ≤ fp.u * bunchTriTauCap M0 := by
              change fp.u * |A 0 j.succ| ≤ fp.u * bunchTriTauCap M0
              exact mul_le_mul_of_nonneg_left
                (hoff 0 j.succ (Or.inr (by simp))) fp.u_nonneg
            _ ≤ bunchTriSparseFactorRadius fp M0 :=
              sparseFactorRadius_dom_oneRow fp hval M0 hM0
      · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨j, rfl⟩
        · calc
            |(∑ p, ∑ q_1, flMixedL q s.consOne A i.succ p * flMixedD q s.consOne A p q_1 *
                flMixedL q s.consOne A 0 q_1) - A i.succ 0|
                ≤ q.u * |A i.succ 0| := hcolAll i
            _ ≤ fp.u * bunchTriTauCap M0 := by
              change fp.u * |A i.succ 0| ≤ fp.u * bunchTriTauCap M0
              exact mul_le_mul_of_nonneg_left
                (hoff i.succ 0 (Or.inl (by simp))) fp.u_nonneg
            _ ≤ bunchTriSparseFactorRadius fp M0 :=
              sparseFactorRadius_dom_oneRow fp hval M0 hM0
        · cases n with
          | zero => exact Fin.elim0 i
          | succ m =>
            rw [mixedProduct_consOne_trailing]
            by_cases hc : i.val = 0 ∧ j.val = 0
            · have hi : i = 0 := Fin.ext hc.1
              have hj : j = 0 := Fin.ext hc.2
              subst hi
              subst hj
              have hhead := mixedProduct_head00 q s (flSchurCompl (m + 1) q A)
              obtain ⟨Δ, hΔ, hstage⟩ := fl_oneByOne_stage_trailing_error q
                (A 0 0) (A (0 : Fin (m + 1)).succ 0) (A 0 (0 : Fin (m + 1)).succ)
                (A (0 : Fin (m + 1)).succ (0 : Fin (m + 1)).succ) hA00 hval
              have hlocal :
                  |q.fl_div (A (0 : Fin (m + 1)).succ 0) (A 0 0) * A 0 0 *
                      q.fl_div (A (0 : Fin (m + 1)).succ 0) (A 0 0)
                    + (∑ p : Fin (m + 1), ∑ q_1 : Fin (m + 1),
                        flMixedL q s (flSchurCompl (m + 1) q A) 0 p *
                          flMixedD q s (flSchurCompl (m + 1) q A) p q_1 *
                            flMixedL q s (flSchurCompl (m + 1) q A) 0 q_1)
                    - A (0 : Fin (m + 1)).succ (0 : Fin (m + 1)).succ|
                    ≤ 2 * gamma fp 3 *
                      (|A (0 : Fin (m + 1)).succ (0 : Fin (m + 1)).succ|
                        + |A (0 : Fin (m + 1)).succ 0 *
                            A 0 (0 : Fin (m + 1)).succ / A 0 0|) := by
                rw [hhead]
                have hqgamma : gamma q 3 = gamma fp 3 := rfl
                change |q.fl_div (A (0 : Fin (m + 1)).succ 0) (A 0 0) * A 0 0 *
                    q.fl_div (A (0 : Fin (m + 1)).succ 0) (A 0 0)
                  + q.fl_sub (A (0 : Fin (m + 1)).succ (0 : Fin (m + 1)).succ)
                      (q.fl_mul (q.fl_div (A (0 : Fin (m + 1)).succ 0) (A 0 0))
                        (A 0 (0 : Fin (m + 1)).succ))
                  - A (0 : Fin (m + 1)).succ (0 : Fin (m + 1)).succ|
                    ≤ 2 * gamma fp 3 *
                      (|A (0 : Fin (m + 1)).succ (0 : Fin (m + 1)).succ|
                        + |A (0 : Fin (m + 1)).succ 0 *
                            A 0 (0 : Fin (m + 1)).succ / A 0 0|)
                have hsym := hsym1 (0 : Fin (m + 1))
                rw [hsym] at hstage hΔ ⊢
                rw [hstage, add_sub_cancel_left]
                simpa [hqgamma] using hΔ
              have hb := hoff (0 : Fin (m + 1)).succ (0 : Fin (m + 1)).succ
                (Or.inl (by simp))
              have hp := oneByOne_exact_corner_path_le M0 (A 0 0)
                (A (0 : Fin (m + 1)).succ 0) (hchoices 0) hA00
              have hsym := hsym1 (0 : Fin (m + 1))
              have hp' : |A (0 : Fin (m + 1)).succ 0 *
                    A 0 (0 : Fin (m + 1)).succ / A 0 0|
                  ≤ M0 / bunchTridiagonalAlpha := by
                rw [hsym]
                exact hp
              exact hlocal.trans <| (mul_le_mul_of_nonneg_left
                (add_le_add hb hp') (mul_nonneg (by norm_num) (gamma_nonneg fp hval))).trans
                  (sparseFactorRadius_dom_oneCorner fp hval M0 hM0)
            · have hne : i.val ≠ 0 ∨ j.val ≠ 0 := by
                by_contra h
                push_neg at h
                exact hc ⟨h.1, h.2⟩
              have hpiv : q.fl_div (A i.succ 0) (A 0 0) * A 0 0 *
                    q.fl_div (A j.succ 0) (A 0 0) = 0 := by
                rcases hne with hi | hj
                · have hz : A i.succ 0 = 0 := by
                    apply hA.2
                    right
                    simp only [Fin.val_succ, Fin.val_zero]
                    omega
                  rw [hz, fl_div_zero_left q (A 0 0) hA00]
                  ring
                · have hz : A j.succ 0 = 0 := by
                    apply hA.2
                    right
                    simp only [Fin.val_succ, Fin.val_zero]
                    omega
                  rw [hz, fl_div_zero_left q (A 0 0) hA00]
                  ring
              have hcopy := flSchurCompl_skipZero_of_ne_corner fp A hA hA00 i j hne
              rw [hpiv, zero_add, ← hcopy]
              exact ih (flSchurCompl (m + 1) q A) hrec i j
  | @consTwo n s ih =>
      intro A hbounded I J
      obtain ⟨hA, hchoice, hoff, hrec⟩ := hbounded
      let q := skipZeroSubFP fp
      have hslack := bunchTriTauCap_slack M0 hM0
      have hR0 := bunchTriSparseFactorRadius_nonneg fp hval M0 hM0
      rcases Fin.eq_zero_or_eq_succ I with rfl | ⟨I', rfl⟩
      · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
        · rw [product_consTwo_00 q s A, sub_self, abs_zero]
          exact hR0
        · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
          · rw [product_consTwo_0one q s A, sub_self, abs_zero]
            exact hR0
          · rw [product_consTwo_0t q s A j]
            cases n with
            | zero => exact Fin.elim0 j
            | succ m =>
              by_cases hj : j.val = 0
              · have hj0 : j = 0 := Fin.ext hj
                subst hj0
                have ha22 := hoff (oneIdx (m + 1)) (oneIdx (m + 1))
                  (Or.inl (by simp [oneIdx]))
                have hdet := mixedDet2_ne_zero_of_growth_bounded M0
                  (bunchTriTauCap M0) hM0 hslack A hA hchoice ha22
                have hr := (flMixedMult2_corner_residuals q hu A hA hdet).1
                have hp := pivotRowPathAbs_le_decoupled q M0 (bunchTriTauCap M0)
                  hM0 hslack A hA hoff hchoice 0 0
                exact hr.trans <| (mul_le_mul_of_nonneg_left hp
                  (mul_nonneg (by norm_num) fp.u_nonneg)).trans
                    (sparseFactorRadius_dom_twoRow fp hval M0 hM0)
              · have hw := flMixedMult2_eq_zero_of_tridiag q A hA j (by omega)
                have hz : A 0 j.succ.succ = 0 := by
                  apply hA.2
                  left
                  simp only [Fin.val_succ, Fin.val_zero]
                  omega
                rw [hw.1, hw.2, mul_zero, mul_zero, add_zero, hz, sub_zero, abs_zero]
                exact hR0
      · rcases Fin.eq_zero_or_eq_succ I' with rfl | ⟨i, rfl⟩
        · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
          · rw [product_consTwo_one0 q s A, sub_self, abs_zero]
            exact hR0
          · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
            · rw [product_consTwo_oneone q s A, sub_self, abs_zero]
              exact hR0
            · rw [product_consTwo_1t q s A j]
              cases n with
              | zero => exact Fin.elim0 j
              | succ m =>
                by_cases hj : j.val = 0
                · have hj0 : j = 0 := Fin.ext hj
                  subst hj0
                  have ha22 := hoff (oneIdx (m + 1)) (oneIdx (m + 1))
                    (Or.inl (by simp [oneIdx]))
                  have hdet := mixedDet2_ne_zero_of_growth_bounded M0
                    (bunchTriTauCap M0) hM0 hslack A hA hchoice ha22
                  have hr := (flMixedMult2_corner_residuals q hu A hA hdet).2.1
                  have hp := pivotRowPathAbs_le_decoupled q M0 (bunchTriTauCap M0)
                    hM0 hslack A hA hoff hchoice 1 0
                  exact hr.trans <| (mul_le_mul_of_nonneg_left hp
                    (mul_nonneg (by norm_num) fp.u_nonneg)).trans
                      (sparseFactorRadius_dom_twoRow fp hval M0 hM0)
                · have hw := flMixedMult2_eq_zero_of_tridiag q A hA j (by omega)
                  have hz : A (oneIdx (m + 1)) j.succ.succ = 0 := by
                    apply hA.2
                    left
                    simp only [oneIdx, Fin.val_succ, Fin.val_zero]
                    omega
                  rw [hw.1, hw.2, mul_zero, mul_zero, add_zero, hz, sub_zero, abs_zero]
                  exact hR0
        · rcases Fin.eq_zero_or_eq_succ J with rfl | ⟨J', rfl⟩
          · rw [product_consTwo_t0 q s A i]
            cases n with
            | zero => exact Fin.elim0 i
            | succ m =>
              by_cases hi : i.val = 0
              · have hi0 : i = 0 := Fin.ext hi
                subst hi0
                have ha22 := hoff (oneIdx (m + 1)) (oneIdx (m + 1))
                  (Or.inl (by simp [oneIdx]))
                have hdet := mixedDet2_ne_zero_of_growth_bounded M0
                  (bunchTriTauCap M0) hM0 hslack A hA hchoice ha22
                have hr := (flMixedMult2_corner_residuals q hu A hA hdet).2.2.1
                have hp := pivotColPathAbs_le_decoupled q M0 (bunchTriTauCap M0)
                  hM0 hslack A hA hoff hchoice 0 0
                exact hr.trans <| (mul_le_mul_of_nonneg_left hp
                  (mul_nonneg (by norm_num) fp.u_nonneg)).trans
                    (sparseFactorRadius_dom_twoRow fp hval M0 hM0)
              · have hw := flMixedMult2_eq_zero_of_tridiag q A hA i (by omega)
                have hz : A i.succ.succ 0 = 0 := by
                  apply hA.2
                  right
                  simp only [Fin.val_succ, Fin.val_zero]
                  omega
                rw [hw.1, hw.2, zero_mul, zero_mul, add_zero, hz, sub_zero, abs_zero]
                exact hR0
          · rcases Fin.eq_zero_or_eq_succ J' with rfl | ⟨j, rfl⟩
            · rw [product_consTwo_t1 q s A i]
              cases n with
              | zero => exact Fin.elim0 i
              | succ m =>
                by_cases hi : i.val = 0
                · have hi0 : i = 0 := Fin.ext hi
                  subst hi0
                  have ha22 := hoff (oneIdx (m + 1)) (oneIdx (m + 1))
                    (Or.inl (by simp [oneIdx]))
                  have hdet := mixedDet2_ne_zero_of_growth_bounded M0
                    (bunchTriTauCap M0) hM0 hslack A hA hchoice ha22
                  have hr := (flMixedMult2_corner_residuals q hu A hA hdet).2.2.2
                  have hp := pivotColPathAbs_le_decoupled q M0 (bunchTriTauCap M0)
                    hM0 hslack A hA hoff hchoice 0 1
                  exact hr.trans <| (mul_le_mul_of_nonneg_left hp
                    (mul_nonneg (by norm_num) fp.u_nonneg)).trans
                      (sparseFactorRadius_dom_twoRow fp hval M0 hM0)
                · have hw := flMixedMult2_eq_zero_of_tridiag q A hA i (by omega)
                  have hz : A i.succ.succ (oneIdx (m + 1)) = 0 := by
                    apply hA.2
                    right
                    simp only [oneIdx, Fin.val_succ, Fin.val_zero]
                    omega
                  rw [hw.1, hw.2, zero_mul, zero_mul, add_zero, hz, sub_zero, abs_zero]
                  exact hR0
            · rw [product_consTwo_trailing q s A i j]
              cases n with
              | zero => exact Fin.elim0 i
              | succ m =>
                by_cases hc : i.val = 0 ∧ j.val = 0
                · have hi : i = 0 := Fin.ext hc.1
                  have hj : j = 0 := Fin.ext hc.2
                  subst hi
                  subst hj
                  have ha22 := hoff (oneIdx (m + 1)) (oneIdx (m + 1))
                    (Or.inl (by simp [oneIdx]))
                  have hdet := mixedDet2_ne_zero_of_growth_bounded M0
                    (bunchTriTauCap M0) hM0 hslack A hA hchoice ha22
                  have hlocal := flMixedMult2_corner_trailing_residual q hval hu A hA hdet
                  have hhead := mixedProduct_head00 q s (flSchurCompl2 (m + 1) q A)
                  rw [hhead]
                  have hb := hoff (0 : Fin (m + 1)).succ.succ
                    (0 : Fin (m + 1)).succ.succ
                    (Or.inl (by simp only [Fin.val_succ, Fin.val_zero]; omega))
                  have hp := pivotPath2Abs_le_decoupled q M0 (bunchTriTauCap M0)
                    hM0 hslack A hA hoff hchoice 0 0
                  exact hlocal.trans <| (mul_le_mul_of_nonneg_left
                    (add_le_add hb hp) (mul_nonneg (by norm_num) (gamma_nonneg fp hval))).trans
                      (sparseFactorRadius_dom_twoCorner fp hval M0 hM0)
                · have hne : i.val ≠ 0 ∨ j.val ≠ 0 := by
                    by_contra h
                    push_neg at h
                    exact hc ⟨h.1, h.2⟩
                  have hpath := pivotPath2_eq_zero_of_ne_corner q A hA i j hne
                  have hcopy := flSchurCompl2_skipZero_of_ne_corner fp A hA i j hne
                  rw [hpath, zero_add, ← hcopy]
                  exact ih (flSchurCompl2 (m + 1) q A) hrec i j

end NumStability.Ch11Closure.SparseFactor
