import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Algorithms NormEstimation OneNorm FiniteIndex Basic

Canonical destination for material split out of
`NumStability.Algorithms.CondEstimation` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Standard basis vector e_j. -/
noncomputable def basisVec {n : ℕ} (j : Fin n) : Fin n → ℝ :=
  fun i => if i = j then 1 else 0

/-- Index achieving the maximum of |z_j| over Fin n. -/
noncomputable def argmaxAbs {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) : Fin n :=
  (Finset.exists_max_image Finset.univ (fun j => |z j|)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩).choose

/-- The argmax achieves the maximum. -/
lemma argmaxAbs_spec {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ) :
    ∀ j : Fin n, |z j| ≤ |z (argmaxAbs hn z)| := by
  intro j
  exact ((Finset.exists_max_image Finset.univ (fun j => |z j|)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩).choose_spec.2 j (Finset.mem_univ j))

/-- For nonnegative diagonal scaling, the infinity norm of `|A⁻¹|d`
equals the matrix infinity norm of `A⁻¹D`. -/
theorem cond_norm_identity (n : ℕ) (_hn : 0 < n)
    (A_inv : Fin n → Fin n → ℝ) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    infNormVec (fun i => ∑ j : Fin n, |A_inv i j| * d j) =
    infNorm (fun i j => A_inv i j * d j) := by
  let w : Fin n → ℝ := fun i => ∑ j : Fin n, |A_inv i j| * d j
  let B : Fin n → Fin n → ℝ := fun i j => A_inv i j * d j
  have hrow : ∀ i : Fin n, w i = ∑ j : Fin n, |B i j| := by
    intro i
    unfold w B
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_mul, abs_of_nonneg (hd j)]
  have hw_nonneg : ∀ i : Fin n, 0 ≤ w i := by
    intro i
    unfold w
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hd j))
  change infNormVec w = infNorm B
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      rw [abs_of_nonneg (hw_nonneg i), hrow i]
      exact row_sum_le_infNorm B i
    · exact infNorm_nonneg B
  · apply infNorm_le_of_row_sum_le
    · intro i
      rw [← hrow i, ← abs_of_nonneg (hw_nonneg i)]
      exact abs_le_infNormVec w i
    · exact infNormVec_nonneg w

/-- The matrix one-norm equals the infinity norm of the transpose. -/
theorem oneNorm_eq_infNorm_transpose' (n : ℕ) (_hn : 0 < n)
    (B : Fin n → Fin n → ℝ) :
    oneNorm B = infNorm (fun i j => B j i) :=
  oneNorm_eq_infNorm_transpose B

end NumStability
