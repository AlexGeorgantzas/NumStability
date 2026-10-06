import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Source.Higham.Chapter13.Section01.OperationModels

This module formalizes the source-facing Chapter 13 statements for
`Section01.OperationModels`.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open Filter Asymptotics


/-- Source-facing local model for **Algorithm 13.3, Implementation 1**
    (Higham, 2nd ed., Chapter 13, pp.247 and 250): the block solve in step 2
    is governed by equation (13.14), and the diagonal-block systems in block
    back substitution are governed by equation (13.15).  This records the
    computed path used by Theorem 13.6 without proving the omitted
    Demmel--Higham--Schreiber implementation theorem. -/
structure Algorithm13_3Implementation1LocalSpec {r s p : Type*} [Fintype r]
    (u c₄ c₅ normLhat21 normA11 normE21 normUii normDeltaUii : ℝ)
    (Lhat21 A21 E21 : Matrix s r ℝ) (A11 Uii DeltaUii : Matrix r r ℝ)
    (Xhat D : Matrix r p ℝ) : Prop where
  step2 :
    BlockSolveFirstOrderSpec u c₄ normLhat21 normA11 normE21
      Lhat21 A21 E21 A11
  diagonal_solve :
    DiagonalBlockSolveFirstOrderSpec u c₅ normUii normDeltaUii
      Uii DeltaUii Xhat D

/-- Source-facing local model for **Algorithm 13.3, Implementation 2**
    (Higham, 2nd ed., Chapter 13, p.247): the leading diagonal block inverse
    is computed explicitly, so step 2 is represented as a matrix multiplication,
    and diagonal-block solves are represented as inverse-times-right-hand-side
    multiplications.  This is a computed-path specification only; the p.251
    scalar condition-number multiplier is handled by
    `higham13_algorithm13_3_implementation2_eq13_16_firstOrder_multiplier`. -/
structure Algorithm13_3Implementation2ExplicitInverseSpec {r s p : Type*} [Fintype r]
    (A11invHat UiiInvHat : Matrix r r ℝ)
    (Lhat21 A21 : Matrix s r ℝ) (Xhat D : Matrix r p ℝ) : Prop where
  step2_as_matmul : Lhat21 = A21 * A11invHat
  diagonal_solve_as_matmul : Xhat = UiiInvHat * D

/-- One rounded subtraction has an absolute error bounded by unit roundoff
    times the sum of the input magnitudes. -/
theorem higham13_fl_sub_error_le_abs_add_abs (fp : FPModel) (x y : ℝ) :
    |fp.fl_sub x y - (x - y)| ≤ fp.u * (|x| + |y|) := by
  obtain ⟨delta, hdelta, hfl⟩ := fp.model_sub x y
  rw [hfl]
  have hdiff :
      (x - y) * (1 + delta) - (x - y) = (x - y) * delta := by ring
  rw [hdiff, abs_mul]
  have hsub : |x - y| ≤ |x| + |y| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_sub_le x 0 y
  calc
    |x - y| * |delta| ≤ (|x| + |y|) * fp.u :=
      mul_le_mul hsub hdelta (abs_nonneg _)
        (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = fp.u * (|x| + |y|) := by ring

/-- Entrywise rounded matrix subtraction used by the concrete Chapter 13
    subtraction model. -/
noncomputable def higham13_fl_matrixSub (fp : FPModel) {m p : ℕ}
    (A B : Matrix (Fin m) (Fin p) ℝ) : Matrix (Fin m) (Fin p) ℝ :=
  fun i j => fp.fl_sub (A i j) (B i j)

/-- Residual of entrywise rounded matrix subtraction. -/
noncomputable def higham13_fl_matrixSubError (fp : FPModel) {m p : ℕ}
    (A B : Matrix (Fin m) (Fin p) ℝ) : Matrix (Fin m) (Fin p) ℝ :=
  fun i j => higham13_fl_matrixSub fp A B i j - (A i j - B i j)

/-- Concrete max-entry instance of the Chapter 13 subtraction residual model.

    This supplies the ordinary rounded subtraction step needed, together with
    equation (13.4), when forming a block-back-substitution right-hand side. -/
theorem higham13_conventional_subtraction_spec_maxEntry {m p : ℕ}
    (fp : FPModel) (hm : 0 < m) (hp : 0 < p)
    (A B : Matrix (Fin m) (Fin p) ℝ) :
    SubtractionFirstOrderSpec fp.u
      (maxEntryNormRect hm hp A) (maxEntryNormRect hm hp B)
      (maxEntryNormRect hm hp (higham13_fl_matrixSubError fp A B))
      A B (higham13_fl_matrixSubError fp A B)
      (higham13_fl_matrixSub fp A B) := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [higham13_fl_matrixSub, higham13_fl_matrixSubError,
      Matrix.sub_apply, Matrix.add_apply]
    ring
  · apply maxEntryNormRect_le_of_entry_abs_le
    intro i j
    calc
      |higham13_fl_matrixSubError fp A B i j| ≤
          fp.u * (|A i j| + |B i j|) := by
        simpa [higham13_fl_matrixSubError, higham13_fl_matrixSub] using
          higham13_fl_sub_error_le_abs_add_abs fp (A i j) (B i j)
      _ ≤ fp.u *
          (maxEntryNormRect hm hp A + maxEntryNormRect hm hp B) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (entry_le_maxEntryNormRect hm hp A i j)
            (entry_le_maxEntryNormRect hm hp B i j)) fp.u_nonneg

/-- Higham, 2nd ed., Chapter 13, p.248: the conventional matrix product
    satisfies the first-order norm bound in (13.4) with
    `c₁(m,n,p) = n^2`, for the chapter's entrywise max norm.  This wrapper
    converts the existing componentwise `γ_n` matrix-multiply bound to the
    displayed `n^2 u + O(u^2)` form. -/
theorem higham13_conventional_matmul_c1_maxEntry_bound {m n p : ℕ}
    (fp : FPModel) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hγ : gammaValid fp n) :
    MatMulFirstOrderBound fp.u ((n : ℝ) ^ 2)
      (maxEntryNormRect hm hn A) (maxEntryNormRect hn hp B)
      (maxEntryNormRect hm hp
        (fun i : Fin m => fun j : Fin p =>
          fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j)) := by
  let normA : ℝ := maxEntryNormRect hm hn A
  let normB : ℝ := maxEntryNormRect hn hp B
  let E : Fin m → Fin p → ℝ :=
    fun i j => fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j
  have hnormA : 0 ≤ normA := maxEntryNormRect_nonneg hm hn A
  have hnormB : 0 ≤ normB := maxEntryNormRect_nonneg hn hp B
  have hγ_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hγ
  have hentry : ∀ i : Fin m, ∀ j : Fin p,
      |E i j| ≤ gamma fp n * (n : ℝ) * normA * normB := by
    intro i j
    have hsum :
        (∑ k : Fin n, |A i k| * |B k j|) ≤ (n : ℝ) * (normA * normB) := by
      calc
        (∑ k : Fin n, |A i k| * |B k j|)
            ≤ ∑ _k : Fin n, normA * normB := by
                apply Finset.sum_le_sum
                intro k _hk
                exact mul_le_mul
                  (entry_le_maxEntryNormRect hm hn A i k)
                  (entry_le_maxEntryNormRect hn hp B k j)
                  (abs_nonneg (B k j)) hnormA
        _ = (n : ℝ) * (normA * normB) := by simp
    calc
      |E i j|
          ≤ gamma fp n * ∑ k : Fin n, |A i k| * |B k j| := by
            simpa [E] using matMul_error_bound fp m n p A B hγ i j
      _ ≤ gamma fp n * ((n : ℝ) * (normA * normB)) :=
            mul_le_mul_of_nonneg_left hsum hγ_nonneg
      _ = gamma fp n * (n : ℝ) * normA * normB := by ring
  have hDelta :
      maxEntryNormRect hm hp E ≤ gamma fp n * (n : ℝ) * normA * normB :=
    maxEntryNormRect_le_of_entry_abs_le hm hp E
      (gamma fp n * (n : ℝ) * normA * normB) hentry
  unfold MatMulFirstOrderBound
  refine ⟨((n : ℝ) ^ 3 * normA * normB) / (1 - (n : ℝ) * fp.u), ?_, ?_⟩
  · have hden_pos : 0 < 1 - (n : ℝ) * fp.u := by
      unfold gammaValid at hγ
      linarith
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast n.zero_le
    have hn3_nonneg : 0 ≤ (n : ℝ) ^ 3 := pow_nonneg hn_nonneg 3
    exact div_nonneg (mul_nonneg (mul_nonneg hn3_nonneg hnormA) hnormB)
      (le_of_lt hden_pos)
  · calc
      maxEntryNormRect hm hp E
          ≤ gamma fp n * (n : ℝ) * normA * normB := hDelta
      _ = ((n : ℝ) ^ 2) * fp.u * normA * normB +
            (((n : ℝ) ^ 3 * normA * normB) /
              (1 - (n : ℝ) * fp.u)) * fp.u ^ 2 := by
            have hγeq := gamma_eq_linear_plus_quadratic_remainder fp n hγ
            have hden_ne : 1 - (n : ℝ) * fp.u ≠ 0 := by
              unfold gammaValid at hγ
              linarith
            rw [hγeq]
            field_simp [hden_ne]

/-- Higham, 2nd ed., Chapter 13, equation (13.4), conventional matrix
    multiplication instance: `Ĉ = AB + ΔC` and the entrywise max-norm
    first-order bound holds with `c₁(m,n,p) = n^2`. -/
theorem higham13_conventional_matmul_spec_c1_maxEntry {m n p : ℕ}
    (fp : FPModel) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ)
    (hγ : gammaValid fp n) :
    MatMulFirstOrderSpec fp.u ((n : ℝ) ^ 2)
      (maxEntryNormRect hm hn A) (maxEntryNormRect hn hp B)
      (maxEntryNormRect hm hp
        (fun i : Fin m => fun j : Fin p =>
          fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j))
      A B (fl_matMul fp m n p A B)
      (fun i : Fin m => fun j : Fin p =>
        fl_matMul fp m n p A B i j - ∑ k : Fin n, A i k * B k j) := by
  constructor
  · ext i j
    simp [Matrix.mul_apply]
  · exact higham13_conventional_matmul_c1_maxEntry_bound fp hm hn hp A B hγ

/-- Columnwise back substitution for multiple right-hand sides. -/
noncomputable def fl_backSubCols (fp : FPModel) (m p : ℕ)
    (T : Fin m → Fin m → ℝ) (B : Fin m → Fin p → ℝ) :
    Fin m → Fin p → ℝ :=
  fun i j => fl_backSub fp m T (fun r => B r j) i

/-- Columnwise forward substitution for multiple right-hand sides. -/
noncomputable def fl_forwardSubCols (fp : FPModel) (m p : ℕ)
    (T : Fin m → Fin m → ℝ) (B : Fin m → Fin p → ℝ) :
    Fin m → Fin p → ℝ :=
  fun i j => fl_forwardSub fp m T (fun r => B r j) i

/-- Higham, 2nd ed., Chapter 13, p.248: bridge from a componentwise
    triangular-matrix backward perturbation to the residual form of (13.5),
    with the chapter's entrywise max norm and `c₂(m,p) = m^2`. -/
theorem higham13_triangular_solve_c2_maxEntry_from_componentwise_backward {m p : ℕ}
    (fp : FPModel) (hm : 0 < m) (hp : 0 < p)
    (T : Fin m → Fin m → ℝ) (B Xhat : Fin m → Fin p → ℝ)
    (hγ : gammaValid fp m)
    (hBackward : ∀ j : Fin p, ∃ DeltaT : Fin m → Fin m → ℝ,
      (∀ i k : Fin m, |DeltaT i k| ≤ gamma fp m * |T i k|) ∧
      ∀ i : Fin m, ∑ k : Fin m, (T i k + DeltaT i k) * Xhat k j = B i j) :
    TriangularSolveFirstOrderSpec fp.u ((m : ℝ) ^ 2)
      (maxEntryNormRect hm hm T) (maxEntryNormRect hm hp Xhat)
      (maxEntryNormRect hm hp
        (fun i : Fin m => fun j : Fin p => ∑ k : Fin m, T i k * Xhat k j - B i j))
      T B
      (fun i : Fin m => fun j : Fin p => ∑ k : Fin m, T i k * Xhat k j - B i j)
      Xhat := by
  let DeltaB : Fin m → Fin p → ℝ :=
    fun i j => ∑ k : Fin m, T i k * Xhat k j - B i j
  let normT : ℝ := maxEntryNormRect hm hm T
  let normX : ℝ := maxEntryNormRect hm hp Xhat
  have hnormT : 0 ≤ normT := maxEntryNormRect_nonneg hm hm T
  have hnormX : 0 ≤ normX := maxEntryNormRect_nonneg hm hp Xhat
  have hγ_nonneg : 0 ≤ gamma fp m := gamma_nonneg fp hγ
  have hentry : ∀ i : Fin m, ∀ j : Fin p,
      |DeltaB i j| ≤ gamma fp m * (m : ℝ) * normT * normX := by
    intro i j
    obtain ⟨DeltaT, hDeltaT_bound, hDeltaT_eq⟩ := hBackward j
    have hsplit :
        (∑ k : Fin m, T i k * Xhat k j) +
            (∑ k : Fin m, DeltaT i k * Xhat k j) = B i j := by
      simpa [Finset.sum_add_distrib, add_mul] using hDeltaT_eq i
    have hDeltaB_eq :
        DeltaB i j = -∑ k : Fin m, DeltaT i k * Xhat k j := by
      dsimp [DeltaB]
      rw [← hsplit]
      ring
    calc
      |DeltaB i j|
          = |∑ k : Fin m, DeltaT i k * Xhat k j| := by
            rw [hDeltaB_eq, abs_neg]
      _ ≤ ∑ k : Fin m, |DeltaT i k * Xhat k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin m, |DeltaT i k| * |Xhat k j| := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [abs_mul]
      _ ≤ ∑ _k : Fin m, gamma fp m * normT * normX := by
            apply Finset.sum_le_sum
            intro k _hk
            calc
              |DeltaT i k| * |Xhat k j|
                  ≤ (gamma fp m * |T i k|) * |Xhat k j| :=
                    mul_le_mul_of_nonneg_right (hDeltaT_bound i k) (abs_nonneg _)
              _ ≤ (gamma fp m * normT) * normX := by
                    have hT : gamma fp m * |T i k| ≤ gamma fp m * normT :=
                      mul_le_mul_of_nonneg_left
                        (entry_le_maxEntryNormRect hm hm T i k) hγ_nonneg
                    exact mul_le_mul hT
                      (entry_le_maxEntryNormRect hm hp Xhat k j)
                      (abs_nonneg _) (mul_nonneg hγ_nonneg hnormT)
              _ = gamma fp m * normT * normX := by ring
      _ = (m : ℝ) * (gamma fp m * normT * normX) := by simp
      _ = gamma fp m * (m : ℝ) * normT * normX := by ring
  have hDeltaNorm :
      maxEntryNormRect hm hp DeltaB ≤ gamma fp m * (m : ℝ) * normT * normX :=
    maxEntryNormRect_le_of_entry_abs_le hm hp DeltaB
      (gamma fp m * (m : ℝ) * normT * normX) hentry
  constructor
  · ext i j
    simp [Matrix.mul_apply]
  · unfold TriangularSolveFirstOrderBound
    exact FirstOrderLe.of_gamma_dim_mul fp m hγ hnormT hnormX hDeltaNorm

/-- Higham, 2nd ed., Chapter 13, equation (13.5), conventional upper-triangular
    back substitution applied columnwise.  The residual form
    `T X̂ = B + ΔB` satisfies the entrywise max-norm first-order bound with
    `c₂(m,p) = m^2`. -/
theorem higham13_conventional_backSub_spec_c2_maxEntry {m p : ℕ}
    (fp : FPModel) (hm : 0 < m) (hp : 0 < p)
    (T : Fin m → Fin m → ℝ) (B : Fin m → Fin p → ℝ)
    (hdiag : ∀ i : Fin m, T i i ≠ 0)
    (hupper : ∀ i k : Fin m, k.val < i.val → T i k = 0)
    (hγ : gammaValid fp m) :
    TriangularSolveFirstOrderSpec fp.u ((m : ℝ) ^ 2)
      (maxEntryNormRect hm hm T) (maxEntryNormRect hm hp (fl_backSubCols fp m p T B))
      (maxEntryNormRect hm hp
        (fun i : Fin m => fun j : Fin p =>
          ∑ k : Fin m, T i k * fl_backSubCols fp m p T B k j - B i j))
      T B
      (fun i : Fin m => fun j : Fin p =>
        ∑ k : Fin m, T i k * fl_backSubCols fp m p T B k j - B i j)
      (fl_backSubCols fp m p T B) := by
  exact higham13_triangular_solve_c2_maxEntry_from_componentwise_backward fp hm hp T B
    (fl_backSubCols fp m p T B) hγ (by
      intro j
      simpa [fl_backSubCols] using
        backSub_backward_error fp m T (fun r : Fin m => B r j) hdiag hupper hγ)

/-- Higham, 2nd ed., Chapter 13, equation (13.5), conventional lower-triangular
    forward substitution applied columnwise.  This is the lower-triangular
    analogue of `higham13_conventional_backSub_spec_c2_maxEntry`. -/
theorem higham13_conventional_forwardSub_spec_c2_maxEntry {m p : ℕ}
    (fp : FPModel) (hm : 0 < m) (hp : 0 < p)
    (T : Fin m → Fin m → ℝ) (B : Fin m → Fin p → ℝ)
    (hdiag : ∀ i : Fin m, T i i ≠ 0)
    (hlower : ∀ i k : Fin m, i.val < k.val → T i k = 0)
    (hγ : gammaValid fp m) :
    TriangularSolveFirstOrderSpec fp.u ((m : ℝ) ^ 2)
      (maxEntryNormRect hm hm T) (maxEntryNormRect hm hp (fl_forwardSubCols fp m p T B))
      (maxEntryNormRect hm hp
        (fun i : Fin m => fun j : Fin p =>
          ∑ k : Fin m, T i k * fl_forwardSubCols fp m p T B k j - B i j))
      T B
      (fun i : Fin m => fun j : Fin p =>
        ∑ k : Fin m, T i k * fl_forwardSubCols fp m p T B k j - B i j)
      (fl_forwardSubCols fp m p T B) := by
  exact higham13_triangular_solve_c2_maxEntry_from_componentwise_backward fp hm hp T B
    (fl_forwardSubCols fp m p T B) hγ (by
      intro j
      simpa [fl_forwardSubCols] using
        forwardSub_backward_error fp m T (fun r : Fin m => B r j) hdiag hlower hγ)

end NumStability
