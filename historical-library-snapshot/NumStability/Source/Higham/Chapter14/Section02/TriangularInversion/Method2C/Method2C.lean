import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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
# Chapter14 Section02 TriangularInversion Method2C Method2C

Canonical destination for material split out of
`NumStability.Algorithms.Ch14Method2C` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

namespace Ch14Ext

/-- The block product step of Method 2C: `T̂ = fl(X̂₂₂ · L₂₁)`.

    `X̂₂₂` is the already-computed `s×s` trailing inverse and `L₂₁` is the
    `s×r` below-diagonal block of `L`; the computed product is committed with
    the standard column-by-column matrix-multiply rounding errors. -/
noncomputable def ch14ext_method2C_temp (fp : FPModel) (r s : ℕ)
    (X22 : Fin s → Fin s → ℝ) (L21 : Fin s → Fin r → ℝ) : Fin s → Fin r → ℝ :=
  fl_matMul fp s s r X22 L21

/-- The back-substitution step of Method 2C: solve `X̂₂₁ · L₁₁ = −T̂` for the
    off-diagonal block `X̂₂₁` (an `s×r` matrix).

    Each of the `s` rows of `X̂₂₁` is obtained by back substitution: row `i`
    solves `(X̂₂₁)ᵢ L₁₁ = −T̂ᵢ`, i.e. `L₁₁ᵀ (X̂₂₁)ᵢᵀ = −T̂ᵢᵀ`.  Because `L₁₁`
    is lower triangular, `L₁₁ᵀ` is upper triangular, so the row solve is exactly
    `fl_backSub` applied to `U := L₁₁ᵀ`. -/
noncomputable def ch14ext_method2C_offdiag (fp : FPModel) (r s : ℕ)
    (L11 : Fin r → Fin r → ℝ) (X22 : Fin s → Fin s → ℝ) (L21 : Fin s → Fin r → ℝ) :
    Fin s → Fin r → ℝ :=
  fun i => fl_backSub fp r (fun a b => L11 b a)
             (fun a => - ch14ext_method2C_temp fp r s X22 L21 i a)

/-- **Method 2C off-diagonal block left residual** (Higham §14.2.2, the
    analogue of (14.14) for Method 2C, p. 266), DERIVED form.

    For the `2×2` block partition `L = [[L₁₁,0],[L₂₁,L₂₂]]`, Method 2C forms
    `T̂ = fl(X̂₂₂·L₂₁)` and then solves `X̂₂₁·L₁₁ = −T̂` by back substitution.
    This theorem derives the componentwise off-diagonal residual bound directly
    from the floating-point error models of those two steps -- no residual
    bound is assumed.

    The derived (two-budget) constant is explicit:
      |(X̂₂₁L₁₁)ᵢₐ + (X̂₂₂L₂₁)ᵢₐ|
        ≤ γ_{r+1}·(|X̂₂₁||L₁₁|)ᵢₐ + (γ_s + γ_r + γ_r·γ_s)·(|X̂₂₂||L₂₁|)ᵢₐ,
    where `γ_{r+1}` is the back-substitution coefficient (`r×r` solve),
    `γ_s` is the block-product coefficient (inner dimension `s`), and the
    `γ_r(1+γ_s)` term propagates the right-hand-side perturbation of the solve.
    This is Higham's `cₙu(|X̂₂₁||L₁₁| + |X̂₂₂||L₂₁|)` with a concrete constant. -/
theorem ch14ext_method2C_offdiag_residual_of_spec
    (fp : FPModel) (r s : ℕ)
    (L11 : Fin r → Fin r → ℝ) (L21 : Fin s → Fin r → ℝ) (X22 : Fin s → Fin s → ℝ)
    (X21 : Fin s → Fin r → ℝ) (That : Fin s → Fin r → ℝ)
    (hL11diag : ∀ a : Fin r, L11 a a ≠ 0)
    (hL11lt : ∀ p q : Fin r, q.val > p.val → L11 p q = 0)
    (hval : gammaValid fp (r + s + 1))
    (hThat : ∀ i a, That i a = fl_matMul fp s s r X22 L21 i a)
    (hX21 : ∀ i, X21 i = fl_backSub fp r (fun a b => L11 b a) (fun a => - That i a)) :
    ∀ (i : Fin s) (a : Fin r),
      |(∑ b : Fin r, X21 i b * L11 b a) + (∑ l : Fin s, X22 i l * L21 l a)| ≤
        gamma fp (r + 1) * (∑ b : Fin r, |X21 i b| * |L11 b a|) +
        (gamma fp s + gamma fp r + gamma fp r * gamma fp s) *
          (∑ l : Fin s, |X22 i l| * |L21 l a|) := by
  intro i a
  -- Validity of the various gamma-constants.
  have hval_r1 : gammaValid fp (r + 1) := gammaValid_mono fp (by omega) hval
  have hval_r : gammaValid fp r := gammaValid_mono fp (by omega) hval
  have hval_s : gammaValid fp s := gammaValid_mono fp (by omega) hval
  have hγr1_nonneg : 0 ≤ gamma fp (r + 1) := gamma_nonneg fp hval_r1
  have hγr_nonneg : 0 ≤ gamma fp r := gamma_nonneg fp hval_r
  have hγs_nonneg : 0 ≤ gamma fp s := gamma_nonneg fp hval_s
  -- Nonnegativity of the absolute-product budgets.
  have hB2_nonneg : 0 ≤ (∑ l : Fin s, |X22 i l| * |L21 l a|) :=
    Finset.sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- (a) Block matrix-product error: T̂ = X̂₂₂·L₂₁ + E, |E| ≤ γ_s·(|X̂₂₂||L₂₁|).
  have hmm : |That i a - (∑ l : Fin s, X22 i l * L21 l a)| ≤
      gamma fp s * (∑ l : Fin s, |X22 i l| * |L21 l a|) := by
    have h := matMul_error_bound fp s s r X22 L21 hval_s i a
    rw [← hThat i a] at h
    exact h
  -- (b) Rectangular back-substitution solve, via the transpose Lᵀ (upper tri).
  obtain ⟨ΔU, Δb, hΔU, hΔb, heq⟩ :=
    backSub_backward_error_dual fp r (fun a b => L11 b a) (fun a => - That i a)
      (fun p => hL11diag p) (fun p q hpq => hL11lt q p hpq) hval_r1
  -- The back-substitution output is exactly the constructed X̂₂₁ row.
  have hsol : ∀ j, fl_backSub fp r (fun a b => L11 b a) (fun a => - That i a) j = X21 i j :=
    fun j => (congrFun (hX21 i) j).symm
  -- Instantiate the solve's equation at column `a` and rewrite into X̂₂₁.
  have heqa : (∑ j : Fin r, (L11 j a + ΔU a j) * X21 i j) = - That i a + Δb a := by
    have h := heq a
    simp only [hsol] at h
    exact h
  -- Split the perturbed sum.
  have hsum_split : (∑ j : Fin r, (L11 j a + ΔU a j) * X21 i j)
      = (∑ j : Fin r, L11 j a * X21 i j) + (∑ j : Fin r, ΔU a j * X21 i j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum_split] at heqa
  -- Rewrite the residual's X̂₂₁L₁₁ part.
  have hLHS : (∑ b : Fin r, X21 i b * L11 b a) = (∑ j : Fin r, L11 j a * X21 i j) :=
    Finset.sum_congr rfl fun j _ => by ring
  -- The residual identity: (X̂₂₁L₁₁ + X̂₂₂L₂₁)ᵢₐ = −E + Δb − Σ(ΔU·X̂₂₁).
  have hR : (∑ b : Fin r, X21 i b * L11 b a) + (∑ l : Fin s, X22 i l * L21 l a)
      = -(That i a - (∑ l : Fin s, X22 i l * L21 l a)) + Δb a
        - (∑ j : Fin r, ΔU a j * X21 i j) := by
    rw [hLHS]
    have h' : (∑ j : Fin r, L11 j a * X21 i j)
        = - That i a + Δb a - (∑ j : Fin r, ΔU a j * X21 i j) := by
      linear_combination heqa
    rw [h']; ring
  rw [hR]
  -- Bound the RHS-perturbation sum by γ_{r+1}·(|X̂₂₁||L₁₁|).
  have ht3 : (∑ j : Fin r, |ΔU a j| * |X21 i j|)
      ≤ gamma fp (r + 1) * (∑ b : Fin r, |X21 i b| * |L11 b a|) := by
    have hstep : (∑ j : Fin r, |ΔU a j| * |X21 i j|)
        ≤ ∑ j : Fin r, (gamma fp (r + 1) * |L11 j a|) * |X21 i j| := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have := hΔU a j
      simpa using this
    refine le_trans hstep ?_
    rw [Finset.mul_sum]
    exact le_of_eq (Finset.sum_congr rfl fun j _ => by ring)
  -- Bound |T̂ᵢₐ| ≤ (1 + γ_s)·(|X̂₂₂||L₂₁|).
  have hS22_abs : |∑ l : Fin s, X22 i l * L21 l a|
      ≤ (∑ l : Fin s, |X22 i l| * |L21 l a|) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact le_of_eq (Finset.sum_congr rfl fun l _ => by rw [abs_mul])
  have hThatBound : |That i a| ≤ (1 + gamma fp s) * (∑ l : Fin s, |X22 i l| * |L21 l a|) := by
    calc |That i a|
        = |(That i a - (∑ l : Fin s, X22 i l * L21 l a))
            + (∑ l : Fin s, X22 i l * L21 l a)| := by ring_nf
      _ ≤ |That i a - (∑ l : Fin s, X22 i l * L21 l a)|
            + |∑ l : Fin s, X22 i l * L21 l a| := abs_add_le _ _
      _ ≤ gamma fp s * (∑ l : Fin s, |X22 i l| * |L21 l a|)
            + (∑ l : Fin s, |X22 i l| * |L21 l a|) := add_le_add hmm hS22_abs
      _ = (1 + gamma fp s) * (∑ l : Fin s, |X22 i l| * |L21 l a|) := by ring
  -- Bound |Δb a| ≤ γ_r·|T̂ᵢₐ| ≤ γ_r·(1 + γ_s)·(|X̂₂₂||L₂₁|).
  have ht2' : |Δb a| ≤ gamma fp r * |That i a| := by
    have := hΔb a
    simpa [abs_neg] using this
  have ht2 : |Δb a| ≤ gamma fp r * ((1 + gamma fp s) * (∑ l : Fin s, |X22 i l| * |L21 l a|)) :=
    le_trans ht2' (mul_le_mul_of_nonneg_left hThatBound hγr_nonneg)
  -- Assemble the three term bounds through the triangle inequality.
  calc |(-(That i a - (∑ l : Fin s, X22 i l * L21 l a))) + Δb a
          - (∑ j : Fin r, ΔU a j * X21 i j)|
      ≤ |That i a - (∑ l : Fin s, X22 i l * L21 l a)| + |Δb a|
          + (∑ j : Fin r, |ΔU a j| * |X21 i j|) := by
        have h1 : |(-(That i a - (∑ l : Fin s, X22 i l * L21 l a))) + Δb a
              - (∑ j : Fin r, ΔU a j * X21 i j)|
            ≤ |(-(That i a - (∑ l : Fin s, X22 i l * L21 l a))) + Δb a|
              + |∑ j : Fin r, ΔU a j * X21 i j| := by
          have h := abs_add_le ((-(That i a - (∑ l : Fin s, X22 i l * L21 l a))) + Δb a)
            (-(∑ j : Fin r, ΔU a j * X21 i j))
          rw [abs_neg, ← sub_eq_add_neg] at h
          exact h
        have h2 : |(-(That i a - (∑ l : Fin s, X22 i l * L21 l a))) + Δb a|
            ≤ |That i a - (∑ l : Fin s, X22 i l * L21 l a)| + |Δb a| := by
          have h := abs_add_le (-(That i a - (∑ l : Fin s, X22 i l * L21 l a))) (Δb a)
          rw [abs_neg] at h
          exact h
        have h3 : |∑ j : Fin r, ΔU a j * X21 i j|
            ≤ (∑ j : Fin r, |ΔU a j| * |X21 i j|) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          exact le_of_eq (Finset.sum_congr rfl fun j _ => by rw [abs_mul])
        linarith [h1, h2, h3]
    _ ≤ gamma fp s * (∑ l : Fin s, |X22 i l| * |L21 l a|)
          + gamma fp r * ((1 + gamma fp s) * (∑ l : Fin s, |X22 i l| * |L21 l a|))
          + gamma fp (r + 1) * (∑ b : Fin r, |X21 i b| * |L11 b a|) := by
        linarith [hmm, ht2, ht3]
    _ = gamma fp (r + 1) * (∑ b : Fin r, |X21 i b| * |L11 b a|)
          + (gamma fp s + gamma fp r + gamma fp r * gamma fp s)
            * (∑ l : Fin s, |X22 i l| * |L21 l a|) := by ring

/-- **Method 2C off-diagonal residual, single-constant (Higham eq. (482)) form.**

    Collapsing the two-budget bound onto the single constant
    `cₙ := γ_{r+1} + γ_s + γ_r + γ_r·γ_s` gives exactly Higham's printed shape
    `|X̂₂₁L₁₁ + X̂₂₂L₂₁| ≤ cₙu(|X̂₂₁||L₁₁| + |X̂₂₂||L₂₁|)`. -/
theorem ch14ext_method2C_offdiag_residual_of_spec_uniform
    (fp : FPModel) (r s : ℕ)
    (L11 : Fin r → Fin r → ℝ) (L21 : Fin s → Fin r → ℝ) (X22 : Fin s → Fin s → ℝ)
    (X21 : Fin s → Fin r → ℝ) (That : Fin s → Fin r → ℝ)
    (hL11diag : ∀ a : Fin r, L11 a a ≠ 0)
    (hL11lt : ∀ p q : Fin r, q.val > p.val → L11 p q = 0)
    (hval : gammaValid fp (r + s + 1))
    (hThat : ∀ i a, That i a = fl_matMul fp s s r X22 L21 i a)
    (hX21 : ∀ i, X21 i = fl_backSub fp r (fun a b => L11 b a) (fun a => - That i a)) :
    ∀ (i : Fin s) (a : Fin r),
      |(∑ b : Fin r, X21 i b * L11 b a) + (∑ l : Fin s, X22 i l * L21 l a)| ≤
        (gamma fp (r + 1) + gamma fp s + gamma fp r + gamma fp r * gamma fp s) *
          ((∑ b : Fin r, |X21 i b| * |L11 b a|) + (∑ l : Fin s, |X22 i l| * |L21 l a|)) := by
  intro i a
  have hbase := ch14ext_method2C_offdiag_residual_of_spec fp r s L11 L21 X22 X21 That
    hL11diag hL11lt hval hThat hX21 i a
  have hγr1 : 0 ≤ gamma fp (r + 1) := gamma_nonneg fp (gammaValid_mono fp (by omega) hval)
  have hγr : 0 ≤ gamma fp r := gamma_nonneg fp (gammaValid_mono fp (by omega) hval)
  have hγs : 0 ≤ gamma fp s := gamma_nonneg fp (gammaValid_mono fp (by omega) hval)
  have hB1 : 0 ≤ (∑ b : Fin r, |X21 i b| * |L11 b a|) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hB2 : 0 ≤ (∑ l : Fin s, |X22 i l| * |L21 l a|) :=
    Finset.sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  refine le_trans hbase ?_
  have hG : (0:ℝ) ≤ gamma fp s + gamma fp r + gamma fp r * gamma fp s :=
    add_nonneg (add_nonneg hγs hγr) (mul_nonneg hγr hγs)
  have hextra : 0 ≤ gamma fp (r + 1) * (∑ l : Fin s, |X22 i l| * |L21 l a|)
      + (gamma fp s + gamma fp r + gamma fp r * gamma fp s)
        * (∑ b : Fin r, |X21 i b| * |L11 b a|) :=
    add_nonneg (mul_nonneg hγr1 hB2) (mul_nonneg hG hB1)
  nlinarith [hextra]

/-- **Concrete Method 2C off-diagonal residual** (two-budget form).

    The same bound as `ch14ext_method2C_offdiag_residual_of_spec` but stated for
    the concrete constructed blocks `ch14ext_method2C_offdiag` /
    `ch14ext_method2C_temp`: the hypotheses `hThat`/`hX21` hold definitionally. -/
theorem ch14ext_method2C_offdiag_residual (fp : FPModel) (r s : ℕ)
    (L11 : Fin r → Fin r → ℝ) (L21 : Fin s → Fin r → ℝ) (X22 : Fin s → Fin s → ℝ)
    (hL11diag : ∀ a : Fin r, L11 a a ≠ 0)
    (hL11lt : ∀ p q : Fin r, q.val > p.val → L11 p q = 0)
    (hval : gammaValid fp (r + s + 1)) :
    ∀ (i : Fin s) (a : Fin r),
      |(∑ b : Fin r, ch14ext_method2C_offdiag fp r s L11 X22 L21 i b * L11 b a)
          + (∑ l : Fin s, X22 i l * L21 l a)| ≤
        gamma fp (r + 1)
          * (∑ b : Fin r, |ch14ext_method2C_offdiag fp r s L11 X22 L21 i b| * |L11 b a|)
        + (gamma fp s + gamma fp r + gamma fp r * gamma fp s)
          * (∑ l : Fin s, |X22 i l| * |L21 l a|) :=
  ch14ext_method2C_offdiag_residual_of_spec fp r s L11 L21 X22
    (ch14ext_method2C_offdiag fp r s L11 X22 L21)
    (ch14ext_method2C_temp fp r s X22 L21)
    hL11diag hL11lt hval (fun _ _ => rfl) (fun _ => rfl)

/-- The Method 2C computed inverse for the two-block partition, assembled from
    the diagonal block inverses `X11`, `X22` (computed by Method 2 / recursion)
    and the derived off-diagonal block (matmul + back-substitution). -/
noncomputable def ch14ext_method2CBlockInverse (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ)
    (X11 : Fin r → Fin r → ℝ) (X22 : Fin m → Fin m → ℝ) :
    Fin (r + m) → Fin (r + m) → ℝ :=
  fun i j =>
    Fin.addCases
      (fun b : Fin r =>
        Fin.addCases (fun d : Fin r => X11 b d) (fun _ : Fin m => (0 : ℝ)) j)
      (fun c : Fin m =>
        Fin.addCases
          (fun d : Fin r =>
            ch14ext_method2C_offdiag fp r m (ch14ext_blk11 r m L) X22
              (ch14ext_blk21 r m L) c d)
          (fun d : Fin m => X22 c d) j)
      i

lemma ch14ext_m2c_inv_bb (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) (X11 : Fin r → Fin r → ℝ)
    (X22 : Fin m → Fin m → ℝ) (b d : Fin r) :
    ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.castAdd m b) (Fin.castAdd m d)
      = X11 b d := by
  simp only [ch14ext_method2CBlockInverse, Fin.addCases_left]

lemma ch14ext_m2c_inv_bd (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) (X11 : Fin r → Fin r → ℝ)
    (X22 : Fin m → Fin m → ℝ) (b : Fin r) (d : Fin m) :
    ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.castAdd m b) (Fin.natAdd r d)
      = 0 := by
  simp only [ch14ext_method2CBlockInverse, Fin.addCases_left, Fin.addCases_right]

lemma ch14ext_m2c_inv_cb (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) (X11 : Fin r → Fin r → ℝ)
    (X22 : Fin m → Fin m → ℝ) (c : Fin m) (d : Fin r) :
    ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.natAdd r c) (Fin.castAdd m d)
      = ch14ext_method2C_offdiag fp r m (ch14ext_blk11 r m L) X22
          (ch14ext_blk21 r m L) c d := by
  simp only [ch14ext_method2CBlockInverse, Fin.addCases_right, Fin.addCases_left]

lemma ch14ext_m2c_inv_cd (fp : FPModel) (r m : ℕ)
    (L : Fin (r + m) → Fin (r + m) → ℝ) (X11 : Fin r → Fin r → ℝ)
    (X22 : Fin m → Fin m → ℝ) (c d : Fin m) :
    ch14ext_method2CBlockInverse fp r m L X11 X22 (Fin.natAdd r c) (Fin.natAdd r d)
      = X22 c d := by
  simp only [ch14ext_method2CBlockInverse, Fin.addCases_right]

end Ch14Ext
end NumStability
