-- Algorithms/OuterProduct.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import NumStability.FloatingPoint.Model

namespace NumStability

/-- Floating-point outer product Â = fl(xyᵀ).

    Computed entrywise: each entry (i, j) of Â is the floating-point
    multiplication of xᵢ by yⱼ (Higham §3.1):
      Âᵢⱼ = fl(xᵢ * yⱼ) -/
noncomputable def fl_outerProduct (fp : FPModel) (m n : ℕ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => fp.fl_mul (x i) (y j)

/-- **Outer product forward error bound** (Higham §3.1, equation 3.6).

    The computed outer product satisfies, componentwise:
      |Â - xyᵀ| ≤ u|xyᵀ|

    Formally: for each entry (i, j),
      |fl_outerProduct fp x y i j - x i * y j| ≤ fp.u * |x i * y j|

    Proof: by definition Âᵢⱼ = fl(xᵢ * yⱼ) = xᵢ * yⱼ * (1 + δᵢⱼ)
    with |δᵢⱼ| ≤ u, so Âᵢⱼ − xᵢyⱼ = xᵢyⱼ · δᵢⱼ,
    and |Âᵢⱼ − xᵢyⱼ| = |xᵢyⱼ| · |δᵢⱼ| ≤ u|xᵢyⱼ|. -/
theorem outerProduct_error_bound (fp : FPModel) (m n : ℕ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    ∀ i : Fin m, ∀ j : Fin n,
      |fl_outerProduct fp m n x y i j - x i * y j| ≤ fp.u * |x i * y j| := by
  intro i j
  unfold fl_outerProduct
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul (x i) (y j)
  rw [hfl]
  -- (x i * y j) * (1 + δ) - x i * y j = x i * y j * δ
  have h_eq : (x i * y j) * (1 + δ) - x i * y j = x i * y j * δ := by ring
  rw [h_eq, abs_mul, mul_comm (|x i * y j|)]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

/-- **Outer product error decomposition** (Higham §3.1, equation 3.6).

    This is the displayed matrix form
      Â = xyᵀ + Δ,   |Δ| ≤ u |xyᵀ|.

    The companion theorem `outerProduct_error_bound` is the per-entry
    inequality; this theorem packages the explicit perturbation matrix `Δ`
    used in the source statement. -/
theorem outerProduct_error_decomposition (fp : FPModel) (m n : ℕ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    ∃ Δ : Fin m → Fin n → ℝ,
      (∀ i j, fl_outerProduct fp m n x y i j = x i * y j + Δ i j) ∧
      (∀ i j, |Δ i j| ≤ fp.u * |x i * y j|) := by
  refine ⟨fun i j => fl_outerProduct fp m n x y i j - x i * y j, ?_, ?_⟩
  · intro i j
    ring
  · intro i j
    exact outerProduct_error_bound fp m n x y i j

/-- **Outer product backward error** (Higham §3.1).

    The computed outer product is the exact outer product of x with a
    perturbed ỹ: there exists Δy such that
      ∀ j, |Δy j| ≤ fp.u * |y j|
      ∀ i j, fl_outerProduct fp x y i j = x i * (y j + Δy j)

    Proof: for each j, take Δy j = y j * δᵢⱼ.  However, since δᵢⱼ may
    vary with i, a single global Δy independent of i does not exist in
    general.  The "backward error in y" form is therefore stated column-
    by-column (fixing i): for each row i there exists Δyᵢ with the
    stated bound.

    This is the column-indexed form. -/
theorem outerProduct_backward_error (fp : FPModel) (m n : ℕ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    ∀ i : Fin m, ∃ Δy : Fin n → ℝ,
      (∀ j, |Δy j| ≤ fp.u * |y j|) ∧
      ∀ j, fl_outerProduct fp m n x y i j = x i * (y j + Δy j) := by
  intro i
  let δ : Fin n → ℝ := fun j => Classical.choose (fp.model_mul (x i) (y j))
  have hδ : ∀ j, |δ j| ≤ fp.u ∧ fp.fl_mul (x i) (y j) = x i * y j * (1 + δ j) :=
    fun j => Classical.choose_spec (fp.model_mul (x i) (y j))
  refine ⟨fun j => y j * δ j, fun j => ?_, fun j => ?_⟩
  · -- bound: |y j * δ j| ≤ u * |y j|
    rw [abs_mul, mul_comm (|y j|)]
    exact mul_le_mul_of_nonneg_right (hδ j).1 (abs_nonneg _)
  · -- equality: fl_mul (x i) (y j) = x i * (y j + y j * δ j)
    unfold fl_outerProduct
    rw [(hδ j).2]; ring

/-- Any exact 2-by-2 outer product has zero determinant. -/
theorem rankOne_outerProduct2x2_det_zero (a b : Fin 2 → ℝ) :
    (a 0 * b 0) * (a 1 * b 1) -
      (a 0 * b 1) * (a 1 * b 0) = 0 := by
  ring

/-- A concrete 2-by-2 matrix that will arise from rounded entrywise
outer-product multiplication but is not rank one. -/
noncomputable def outerProductCounterexampleMatrix : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then 1 else 2
    else
      if j = 0 then 2 else 8

/-- The counterexample matrix is not an exact outer product of two vectors. -/
theorem outerProductCounterexampleMatrix_not_rank_one :
    ¬ ∃ a b : Fin 2 → ℝ,
      ∀ i j, outerProductCounterexampleMatrix i j = a i * b j := by
  rintro ⟨a, b, h⟩
  have hdet := rankOne_outerProduct2x2_det_zero a b
  rw [← h 0 0, ← h 1 1, ← h 0 1, ← h 1 0] at hdet
  norm_num [outerProductCounterexampleMatrix] at hdet
  exact (by norm_num : (4 : ℝ) ≠ 0) hdet

/-- A valid abstract floating-point model that rounds only the product
`2 * 2` upward by a relative error of `1`. -/
noncomputable def outerProductCounterexampleFP : FPModel where
  u := 1
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => if x = 2 ∧ y = 2 then x * y * 2 else x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by
    intro x
    ring
  model_add := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_sub := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_mul := by
    intro x y
    by_cases h : x = 2 ∧ y = 2
    · refine ⟨1, by norm_num, ?_⟩
      simp [h]
      ring
    · refine ⟨0, by norm_num, ?_⟩
      simp [h]
  model_div := by
    intro x y _hy
    refine ⟨0, by norm_num, by ring⟩
  model_sqrt := by
    intro x _hx
    refine ⟨0, by norm_num, by ring⟩

/-- The input vector for the 2-by-2 outer-product counterexample. -/
noncomputable def outerProductCounterexampleVec : Fin 2 → ℝ :=
  fun i => if i = 0 then 1 else 2

/-- The counterexample floating-point model computes a non-rank-one matrix
from the entrywise outer product of `[1, 2]` with itself. -/
theorem fl_outerProduct_counterexample_eq :
    fl_outerProduct outerProductCounterexampleFP 2 2
      outerProductCounterexampleVec outerProductCounterexampleVec =
    outerProductCounterexampleMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fl_outerProduct, outerProductCounterexampleFP,
      outerProductCounterexampleVec, outerProductCounterexampleMatrix]

/-- Higham, p. 71: outer-product computation is not backward stable in
general.  For this valid `FPModel` and input vector, the computed matrix cannot
be represented as `(x + Δx)(x + Δy)^T` for any perturbations at all, because it
is not rank one. -/
theorem fl_outerProduct_counterexample_not_global_backward :
    ¬ ∃ Δx Δy : Fin 2 → ℝ,
      ∀ i j,
        fl_outerProduct outerProductCounterexampleFP 2 2
          outerProductCounterexampleVec outerProductCounterexampleVec i j =
          (outerProductCounterexampleVec i + Δx i) *
            (outerProductCounterexampleVec j + Δy j) := by
  rintro ⟨Δx, Δy, h⟩
  apply outerProductCounterexampleMatrix_not_rank_one
  refine ⟨fun i => outerProductCounterexampleVec i + Δx i,
    fun j => outerProductCounterexampleVec j + Δy j, ?_⟩
  intro i j
  have hA := congrFun (congrFun fl_outerProduct_counterexample_eq i) j
  exact hA.symm.trans (h i j)

end NumStability
