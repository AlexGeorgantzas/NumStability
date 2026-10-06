import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockTriInverse

/-!
# Chapter14 Section02 TriangularInversion Method1B Method1BWhole

Canonical destination for material split out of
`NumStability.Algorithms.Ch14Method1BWhole` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators
open NumStability

namespace NumStability

namespace Ch14Ext

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

end Ch14Ext
end NumStability
