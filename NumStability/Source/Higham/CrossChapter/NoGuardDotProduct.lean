import NumStability.Algorithms.Arithmetic.DotProduct.NoGuard.Core
import NumStability.Algorithms.Arithmetic.DotProduct.NoGuard.Tree

/-!
# Higham Chapters 2 and 3: no-guard dot products

Source-correspondence endpoints for equations (3.3)--(3.5) under the
no-guard-digit model (2.6), built on the reusable sequential and tree APIs.
-/

namespace NumStability

open scoped BigOperators

/-- Equation (3.4), literally for any pairwise evaluation order: every binary
tree shape and every input permutation computes the exact inner product after
a componentwise perturbation of either input bounded by `gamma_n`. -/
theorem higham3_4_noGuard_any_order_backward_error
    (fp : NoGuardFPModel) {n : ℕ}
    (t : SumTree n) (perm : Equiv.Perm (Fin n))
    (x y : Fin n → ℝ)
    (hvalid : noGuardDotGammaValid fp n) :
    ∃ deltaX deltaY : Fin n → ℝ,
      (∀ i, |deltaX i| ≤ noGuardDotGamma fp n * |x i|) ∧
      (∀ i, |deltaY i| ≤ noGuardDotGamma fp n * |y i|) ∧
      fl_noGuardDotProductTree fp t perm x y =
        ∑ i : Fin n, (x i + deltaX i) * y i ∧
      fl_noGuardDotProductTree fp t perm x y =
        ∑ i : Fin n, x i * (y i + deltaY i) := by
  have hdepth : t.depth + 1 ≤ n := by
    have hn := SumTree.n_pos t
    have hd := SumTree.depth_le t
    omega
  have hdepthValid : noGuardDotGammaValid fp (t.depth + 1) :=
    gammaValid_mono (noGuardDotGammaProxy fp) hdepth hvalid
  obtain ⟨eta, hetaLocal, hfl⟩ :=
    noGuardDotTree_factor_backward_error fp t perm x y hdepthValid
  have heta : ∀ i, |eta i| ≤ noGuardDotGamma fp n := by
    intro i
    exact le_trans (hetaLocal i)
      (gamma_mono (noGuardDotGammaProxy fp) hdepth hvalid)
  let deltaX : Fin n → ℝ := fun i => x i * eta i
  let deltaY : Fin n → ℝ := fun i => y i * eta i
  refine ⟨deltaX, deltaY, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [deltaX, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (heta i) (abs_nonneg (x i))
  · intro i
    simp only [deltaY, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (heta i) (abs_nonneg (y i))
  · rw [hfl]
    apply Finset.sum_congr rfl
    intro i _
    simp only [deltaX]
    ring
  · rw [hfl]
    apply Finset.sum_congr rfl
    intro i _
    simp only [deltaY]
    ring

/-- Equation (3.5) for every no-guard binary-tree/permuted evaluation order. -/
theorem higham3_5_noGuard_any_order_forward_error
    (fp : NoGuardFPModel) {n : ℕ}
    (t : SumTree n) (perm : Equiv.Perm (Fin n))
    (x y : Fin n → ℝ)
    (hvalid : noGuardDotGammaValid fp n) :
    |(∑ i : Fin n, x i * y i) -
        fl_noGuardDotProductTree fp t perm x y| ≤
      noGuardDotGamma fp n * ∑ i : Fin n, |x i| * |y i| := by
  obtain ⟨deltaX, _deltaY, hdeltaX, _hdeltaY, hback, _⟩ :=
    higham3_4_noGuard_any_order_backward_error fp t perm x y hvalid
  rw [hback, ← Finset.sum_sub_distrib]
  calc
    |∑ i : Fin n, (x i * y i - (x i + deltaX i) * y i)| ≤
        ∑ i : Fin n, |x i * y i - (x i + deltaX i) * y i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |deltaX i| * |y i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show x i * y i - (x i + deltaX i) * y i = -deltaX i * y i by ring,
        abs_mul, abs_neg]
    _ ≤ ∑ i : Fin n,
        (noGuardDotGamma fp n * |x i|) * |y i| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hdeltaX i) (abs_nonneg _)
    _ = noGuardDotGamma fp n *
        ∑ i : Fin n, |x i| * |y i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Equations (3.3)--(3.4) for the concrete no-guard executor: the computed
dot product is exact after perturbing either input vector componentwise by at
most `gamma_n`. -/
theorem higham3_3_3_4_noGuard_backward_error (fp : NoGuardFPModel) (m : ℕ)
    (x y : Fin (m + 1) → ℝ)
    (hvalid : noGuardDotGammaValid fp (m + 1)) :
    ∃ deltaX deltaY : Fin (m + 1) → ℝ,
      (∀ i, |deltaX i| ≤ noGuardDotGamma fp (m + 1) * |x i|) ∧
      (∀ i, |deltaY i| ≤ noGuardDotGamma fp (m + 1) * |y i|) ∧
      fl_noGuardDotProduct fp (m + 1) x y =
        ∑ i : Fin (m + 1), (x i + deltaX i) * y i ∧
      fl_noGuardDotProduct fp (m + 1) x y =
        ∑ i : Fin (m + 1), x i * (y i + deltaY i) := by
  obtain ⟨mulDelta, alpha, beta, hmul, halpha, hbeta, hfl⟩ :=
    noGuardDot_factor_expansion_sum_succ fp m x y
  let factor := noGuardDotLocalFactor m mulDelta alpha beta
  have hfactor : ∀ i, |factor i - 1| ≤ noGuardDotGamma fp (m + 1) :=
    noGuardDotLocalFactor_abs_sub_one_le fp m mulDelta alpha beta
      hmul halpha hbeta hvalid
  let deltaX : Fin (m + 1) → ℝ := fun i => x i * (factor i - 1)
  let deltaY : Fin (m + 1) → ℝ := fun i => y i * (factor i - 1)
  refine ⟨deltaX, deltaY, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [deltaX, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hfactor i) (abs_nonneg (x i))
  · intro i
    simp only [deltaY, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hfactor i) (abs_nonneg (y i))
  · rw [hfl]
    apply Finset.sum_congr rfl
    intro i _
    simp only [deltaX, factor]
    ring
  · rw [hfl]
    apply Finset.sum_congr rfl
    intro i _
    simp only [deltaY, factor]
    ring

/-- Equation (3.5) for the actual no-guard executor. -/
theorem higham3_5_noGuard_forward_error (fp : NoGuardFPModel) (m : ℕ)
    (x y : Fin (m + 1) → ℝ)
    (hvalid : noGuardDotGammaValid fp (m + 1)) :
    |(∑ i : Fin (m + 1), x i * y i) -
        fl_noGuardDotProduct fp (m + 1) x y| ≤
      noGuardDotGamma fp (m + 1) *
        ∑ i : Fin (m + 1), |x i| * |y i| := by
  obtain ⟨deltaX, _deltaY, hdeltaX, _hdeltaY, hback, _⟩ :=
    higham3_3_3_4_noGuard_backward_error fp m x y hvalid
  rw [hback, ← Finset.sum_sub_distrib]
  calc
    |∑ i : Fin (m + 1),
        (x i * y i - (x i + deltaX i) * y i)| ≤
        ∑ i : Fin (m + 1),
          |x i * y i - (x i + deltaX i) * y i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (m + 1), |deltaX i| * |y i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show x i * y i - (x i + deltaX i) * y i = -deltaX i * y i by ring,
        abs_mul, abs_neg]
    _ ≤ ∑ i : Fin (m + 1),
        (noGuardDotGamma fp (m + 1) * |x i|) * |y i| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hdeltaX i) (abs_nonneg _)
    _ = noGuardDotGamma fp (m + 1) *
        ∑ i : Fin (m + 1), |x i| * |y i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end NumStability
