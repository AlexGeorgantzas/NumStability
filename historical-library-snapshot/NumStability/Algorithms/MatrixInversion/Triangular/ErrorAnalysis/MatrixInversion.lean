import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.MatrixInversion.Triangular.Specifications.MatrixInversion
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms MatrixInversion Triangular ErrorAnalysis MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Method 1 right residual for triangular inversion** (Higham eq. 14.4).

    Method 1 computes L⁻¹ by solving Lx̂ⱼ = eⱼ for each column j.
    From Theorem 8.5 (forwardSub_backward_error), each column satisfies
    (L + ΔLⱼ)x̂ⱼ = eⱼ with |ΔLⱼ| ≤ γ(n)|L|.

    This gives the componentwise right residual:
      |LX̂ − I| ≤ γ(n)|L||X̂|. -/
theorem triInv_method1_right_residual (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n) :
    -- X̂ is computed column-by-column: column j = forwardSub(L, eⱼ)
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    -- For each column j: ∃ ΔLⱼ with |ΔLⱼ| ≤ γ(n)|L| and (L+ΔLⱼ)x̂ⱼ = eⱼ
    ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k : Fin n, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i : Fin n, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0 := by
  intro X_hat j
  exact forwardSub_backward_error fp n L (fun k => if k = j then 1 else 0) hL_diag hLT hn

/-- **Method 1 right residual — matrix form** (Higham eq. 14.4).

    Consequence: |LX̂ − I| ≤ γ(n)|L||X̂| componentwise. -/
theorem triInv_method1_right_residual_matrix (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
  intro X_hat i j
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ :=
    triInv_method1_right_residual n fp L hL_diag hLT hn j
  have hLX : ∑ k : Fin n, L i k * X_hat k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔL i k * X_hat k j) := by
    have h := hΔL_eq i
    have hsplit : ∑ k : Fin n, L i k * X_hat k j +
        ∑ k : Fin n, ΔL i k * X_hat k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hLX, abs_neg]
  calc |∑ k : Fin n, ΔL i k * X_hat k j|
      ≤ ∑ k : Fin n, |ΔL i k * X_hat k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔL i k| * |X_hat k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, (gamma fp n * |L i k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔL_bound i k) (abs_nonneg _)
    _ = gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- **Method 1 forward error** (Higham eq. 14.5).

    |X̂ − L⁻¹| ≤ γ(n)|L⁻¹||L||X̂|  (componentwise).

    Proof: From LX̂ = I + E with |E| ≤ γₙ|L||X̂|, multiply by L⁻¹ on the left:
    X̂ = L⁻¹ + L⁻¹E, so |X̂ − L⁻¹| = |L⁻¹E| ≤ |L⁻¹||E| ≤ γₙ|L⁻¹||L||X̂|. -/
theorem triInv_method1_forward_error (n : ℕ) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hn : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j : Fin n,
      |X_hat i j - L_inv i j| ≤
      gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := by
  intro X_hat i j
  -- Get residual: |LX̂ − I|_{k₁j} ≤ γ(n) ∑_{k₂} |L_{k₁k₂}| |X̂_{k₂j}|
  have hRes := triInv_method1_right_residual_matrix n fp L hL_diag hLT hn
  -- Define E_{k₁j} = (LX̂)_{k₁j} − δ_{k₁j}
  -- From LX̂ = I + E, multiply by L⁻¹: X̂ = L⁻¹ + L⁻¹E
  -- So X̂_{ij} − L⁻¹_{ij} = (L⁻¹E)_{ij} = ∑_{k₁} L⁻¹_{ik₁} E_{k₁j}
  have hDiff : X_hat i j - L_inv i j =
      ∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) := by
    -- RHS = ∑ k₁, L⁻¹(i,k₁) · (LX̂)(k₁,j) − ∑ k₁, L⁻¹(i,k₁) · δ(k₁,j)
    -- First part = (L⁻¹LX̂)(i,j) = X̂(i,j), second part = L⁻¹(i,j)
    have hRHS_expand : ∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0) =
        ∑ k₁ : Fin n, L_inv i k₁ * (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j) -
        ∑ k₁ : Fin n, L_inv i k₁ * (if k₁ = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro k₁ _; ring
    rw [hRHS_expand]
    -- Second sum = L⁻¹(i,j)
    have hSecond : ∑ k₁ : Fin n, L_inv i k₁ *
        (if k₁ = j then (1 : ℝ) else 0) = L_inv i j := by
      simp [Finset.sum_ite_eq', Finset.mem_univ]
    -- First sum = (L⁻¹ · L · X̂)(i,j) = X̂(i,j)
    have hFirst : ∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j) = X_hat i j := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have hInvL : ∀ k₂ : Fin n,
          (∑ k₁ : Fin n, L_inv i k₁ * L k₁ k₂) = if i = k₂ then 1 else 0 :=
        fun k₂ => hInv i k₂
      simp_rw [hInvL]
      simp [Finset.mem_univ]
    rw [hFirst, hSecond]
  rw [hDiff]
  calc |∑ k₁ : Fin n, L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)|
      ≤ ∑ k₁ : Fin n, |L_inv i k₁ *
        (∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k₁ : Fin n, |L_inv i k₁| *
        |∑ k₂ : Fin n, L k₁ k₂ * X_hat k₂ j -
          if k₁ = j then (1 : ℝ) else 0| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k₁ : Fin n, |L_inv i k₁| *
        (gamma fp n * ∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := by
        apply Finset.sum_le_sum; intro k₁ _
        exact mul_le_mul_of_nonneg_left (hRes k₁ j) (abs_nonneg _)
    _ = gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k₁ _; ring

/-- **Method 1 first-order forward error** (Higham eq. 14.6).

    |X̂ − L⁻¹| ≤ γ(n)|L⁻¹||L||L⁻¹| + O(u²).

    Since X̂ = L⁻¹ + O(u), replacing |X̂| by |L⁻¹| in eq. 14.5 gives
    this first-order bound. We state the "pre-replacement" form:
    for any X̂_bound satisfying |X̂| ≤ X̂_bound, we get the bound
    with X̂_bound in place of |X̂|. -/
theorem triInv_method1_forward_error_firstorder (n : ℕ) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (X_bound : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hn : gammaValid fp n)
    (hBound : ∀ i j : Fin n,
      |fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i| ≤
        X_bound i j) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    ∀ i j : Fin n,
      |X_hat i j - L_inv i j| ≤
      gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
        (∑ k₂ : Fin n, |L k₁ k₂| * X_bound k₂ j) := by
  intro X_hat i j
  have hFwd := triInv_method1_forward_error n fp L L_inv hL_diag hLT hInv hn i j
  calc |X_hat i j - L_inv i j|
      ≤ gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|) := hFwd
    _ ≤ gamma fp n * ∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * X_bound k₂ j) := by
        apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn)
        apply Finset.sum_le_sum; intro k₁ _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum; intro k₂ _
        exact mul_le_mul_of_nonneg_left (hBound k₂ j) (abs_nonneg _)

/-- **Method 1 normwise forward error** (Higham eq. 14.7).

    ‖X̂ − L⁻¹‖∞ ≤ γ(n) · ‖|L⁻¹||L||X̂|‖∞.

    When ‖X̂‖∞ ≈ ‖L⁻¹‖∞ (i.e. to first order), this gives
    relative error ≤ cₙu · cond(L⁻¹). -/
theorem triInv_method1_normwise_error (n : ℕ) (_hn0 : 0 < n) (fp : FPModel)
    (L L_inv : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hInv : IsLeftInverse n L L_inv)
    (hgv : gammaValid fp n) :
    let X_hat : Fin n → Fin n → ℝ :=
      fun i j => fl_forwardSub fp n L (fun k => if k = j then 1 else 0) i
    infNorm (fun i j => X_hat i j - L_inv i j) ≤
      gamma fp n * infNorm (fun i j =>
        ∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|)) := by
  intro X_hat
  have hFwd := triInv_method1_forward_error n fp L L_inv hL_diag hLT hInv hgv
  -- infNorm is max_i ∑_j |M i j|. We bound each row sum then take the max.
  let M := fun i j => ∑ k₁ : Fin n, |L_inv i k₁| *
    (∑ k₂ : Fin n, |L k₁ k₂| * |X_hat k₂ j|)
  have hnn : ∀ i j : Fin n, 0 ≤ M i j := by
    intro i' j'; apply Finset.sum_nonneg; intro k₁ _
    exact mul_nonneg (abs_nonneg _) (Finset.sum_nonneg
      (fun k₂ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  -- Each entry: |X̂ij − L⁻¹ij| ≤ γ(n) · M i j
  have hEntry : ∀ i j : Fin n, |X_hat i j - L_inv i j| ≤ gamma fp n * M i j :=
    fun i j => hFwd i j
  -- Row sum bound: ∑_j |X̂ij − L⁻¹ij| ≤ γ(n) · ∑_j M i j
  have hRow : ∀ i : Fin n, ∑ j : Fin n, |X_hat i j - L_inv i j| ≤
      gamma fp n * ∑ j : Fin n, M i j := by
    intro i
    calc ∑ j : Fin n, |X_hat i j - L_inv i j|
        ≤ ∑ j : Fin n, gamma fp n * M i j :=
          Finset.sum_le_sum (fun j _ => hEntry i j)
      _ = gamma fp n * ∑ j : Fin n, M i j :=
          (Finset.mul_sum Finset.univ _ (gamma fp n)).symm
  -- ∑_j M i j = ∑_j |M i j| since M ≥ 0
  have habs_eq : ∀ i j : Fin n, |M i j| = M i j :=
    fun i j => abs_of_nonneg (hnn i j)
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |(fun i j => X_hat i j - L_inv i j) i j|
        ≤ gamma fp n * ∑ j : Fin n, M i j := hRow i
      _ = gamma fp n * ∑ j : Fin n, |(fun i j => M i j) i j| := by
          congr 1; apply Finset.sum_congr rfl; intro j _; exact (habs_eq i j).symm
      _ ≤ gamma fp n * infNorm M := by
          apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hgv)
          exact row_sum_le_infNorm M i
  · exact mul_nonneg (gamma_nonneg fp hgv) (infNorm_nonneg M)

/-- Lower-triangular column split used by Method 2: in column `j`, entries
    above the diagonal vanish, so the column product separates into the diagonal
    term plus the strict trailing tail. -/
theorem lowerTri_column_sum_eq_diag_add_tail (n : ℕ)
    (L X_hat : Fin n → Fin n → ℝ)
    (hLT : ∀ a b : Fin n, b.val > a.val → L a b = 0) :
    ∀ i j : Fin n,
      (∑ k : Fin n, X_hat i k * L k j) =
        X_hat i j * L j j +
          ∑ k : Fin n, if j.val < k.val then X_hat i k * L k j else 0 := by
  intro i j
  classical
  rw [← Finset.add_sum_erase Finset.univ
    (fun k : Fin n => X_hat i k * L k j) (Finset.mem_univ j)]
  congr 1
  calc
    (∑ k ∈ Finset.univ.erase j, X_hat i k * L k j)
        = ∑ k ∈ Finset.univ.erase j,
            (if j.val < k.val then X_hat i k * L k j else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk_ne : k ≠ j := by
            simpa [Finset.mem_erase] using hk
          by_cases hjk : j.val < k.val
          · simp [hjk]
          · have hkj : j.val > k.val := by
              have hle : k.val ≤ j.val := Nat.le_of_not_gt hjk
              have hne_val : k.val ≠ j.val := by
                intro hval
                exact hk_ne (Fin.ext hval)
              omega
            rw [hLT k j hkj]
            simp [hjk]
    _ = ∑ k : Fin n, if j.val < k.val then X_hat i k * L k j else 0 := by
          rw [Finset.sum_erase]
          simp

/-- Source-shaped Method 2 off-diagonal identity from a strict trailing update.
    The update hypothesis uses only the tail `k > j`, avoiding the
    self-reference in the full column sum. -/
theorem triInv_method2_offdiag_trailing_update_identity (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hLT : ∀ a b : Fin n, b.val > a.val → L a b = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ) :
    ∀ j row : Fin n, row.val > j.val →
      ∃ δ Δ : ℝ, |δ| ≤ fp.u ∧
        (∑ k : Fin n, X_hat row k * L k j) -
            (if row = j then 1 else 0) =
          Δ * L j j - δ *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) := by
  intro j row hij
  obtain ⟨δ, hδ, hdiag⟩ := hDiag j
  obtain ⟨Δ, hupdate⟩ := hTrail j row hij
  refine ⟨δ, Δ, hδ, ?_⟩
  let tail : ℝ :=
    ∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0
  have hupdate_tail : X_hat row j = -X_hat j j * tail + Δ := by
    simpa [tail] using hupdate
  have hne : row ≠ j := by
    intro h
    exact (Nat.ne_of_gt hij) (congrArg Fin.val h)
  have hsplit :
      (∑ k : Fin n, X_hat row k * L k j) =
        X_hat row j * L j j + tail := by
    simpa [tail] using lowerTri_column_sum_eq_diag_add_tail n L X_hat hLT row j
  rw [if_neg hne, sub_zero, hsplit]
  calc
    X_hat row j * L j j + tail
        = (-X_hat j j * tail + Δ) * L j j + tail := by
            rw [hupdate_tail]
    _ = (-(X_hat j j * L j j) * tail + Δ * L j j) + tail := by ring
    _ = (-(1 + δ) * tail + Δ * L j j) + tail := by rw [hdiag]
    _ = Δ * L j j - δ * tail := by ring

/-- Source-shaped Method 2 off-diagonal residual bound from a strict trailing
    update.  The constant `η` is left abstract so later product-error analyses
    can instantiate the matvec/scalar rounding budget without using the current
    full-column `Method2Spec.offdiag_err` field. -/
theorem triInv_method2_offdiag_trailing_update_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ) {η : ℝ}
    (_hη : 0 ≤ η)
    (hLT : ∀ a b : Fin n, b.val > a.val → L a b = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ η *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ) :
    ∀ j row : Fin n, row.val > j.val →
      |(∑ k : Fin n, X_hat row k * L k j) -
          (if row = j then 1 else 0)| ≤
        (fp.u + η) *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) := by
  intro j row hij
  let tail : ℝ :=
    ∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0
  let tailAbs : ℝ :=
    ∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0
  obtain ⟨δ, hδ, hdiag⟩ := hDiag j
  obtain ⟨Δ, hΔ, hupdate⟩ := hTrail j row hij
  have hupdate_tail : X_hat row j = -X_hat j j * tail + Δ := by
    simpa [tail] using hupdate
  have hne : row ≠ j := by
    intro h
    exact (Nat.ne_of_gt hij) (congrArg Fin.val h)
  have hsplit :
      (∑ k : Fin n, X_hat row k * L k j) =
        X_hat row j * L j j + tail := by
    simpa [tail] using lowerTri_column_sum_eq_diag_add_tail n L X_hat hLT row j
  have hid :
      (∑ k : Fin n, X_hat row k * L k j) -
          (if row = j then 1 else 0) =
        Δ * L j j - δ * tail := by
    rw [if_neg hne, sub_zero, hsplit]
    calc
      X_hat row j * L j j + tail
          = (-X_hat j j * tail + Δ) * L j j + tail := by
              rw [hupdate_tail]
      _ = (-(X_hat j j * L j j) * tail + Δ * L j j) + tail := by ring
      _ = (-(1 + δ) * tail + Δ * L j j) + tail := by rw [hdiag]
      _ = Δ * L j j - δ * tail := by ring
  have htail_abs : |tail| ≤ tailAbs := by
    calc
      |tail| =
          |∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0| := by
            rfl
      _ ≤ ∑ k : Fin n,
            |if j.val < k.val then X_hat row k * L k j else 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = tailAbs := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hjk : j.val < k.val <;> simp [hjk, abs_mul]
  have hδ_tail : |δ * tail| ≤ fp.u * tailAbs := by
    calc
      |δ * tail| = |δ| * |tail| := abs_mul _ _
      _ ≤ fp.u * tailAbs :=
          mul_le_mul hδ htail_abs (abs_nonneg _) fp.u_nonneg
  rw [hid]
  calc
    |Δ * L j j - δ * tail|
        ≤ |Δ * L j j| + |δ * tail| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le (Δ * L j j) (-(δ * tail))
    _ ≤ η * tailAbs + fp.u * tailAbs := by
        exact add_le_add (by simpa [tailAbs] using hΔ) hδ_tail
    _ = (fp.u + η) * tailAbs := by ring

/-- Full-column budget form of `triInv_method2_offdiag_trailing_update_bound`:
    the strict trailing absolute product is bounded by the complete
    `|X_hat|*|L|` column budget used in Lemma 14.1. -/
theorem triInv_method2_offdiag_trailing_update_full_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ) {η : ℝ}
    (hη : 0 ≤ η)
    (hLT : ∀ a b : Fin n, b.val > a.val → L a b = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ η *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ) :
    ∀ j row : Fin n, row.val > j.val →
      |(∑ k : Fin n, X_hat row k * L k j) -
          (if row = j then 1 else 0)| ≤
        (fp.u + η) * (∑ k : Fin n, |X_hat row k| * |L k j|) := by
  intro j row hij
  have htail :=
    triInv_method2_offdiag_trailing_update_bound n fp L X_hat hη hLT hDiag hTrail
      j row hij
  have htail_le_full :
      (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ≤
        ∑ k : Fin n, |X_hat row k| * |L k j| := by
    apply Finset.sum_le_sum
    intro k _
    have hterm_nonneg : 0 ≤ |X_hat row k| * |L k j| :=
      mul_nonneg (abs_nonneg (X_hat row k)) (abs_nonneg (L k j))
    by_cases hjk : j.val < k.val <;> simp [hjk, hterm_nonneg]
  have hcoef : 0 ≤ fp.u + η := add_nonneg fp.u_nonneg hη
  exact le_trans htail (mul_le_mul_of_nonneg_left htail_le_full hcoef)

/-- Triangular-shape support for Method 2: if both `X_hat` and `L` are lower
    triangular, then the left residual `X_hat * L - I` is zero strictly above
    the diagonal. -/
theorem triInv_lower_left_residual_upper_zero (n : ℕ)
    (L X_hat : Fin n → Fin n → ℝ)
    (hX_lower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hL_lower : ∀ i j : Fin n, j.val > i.val → L i j = 0) :
    ∀ i j : Fin n, i.val < j.val →
      ∑ k : Fin n, X_hat i k * L k j -
        (if i = j then 1 else 0) = 0 := by
  intro i j hij
  have hne : i ≠ j := by
    intro h
    have hval : i.val = j.val := congrArg Fin.val h
    omega
  have hsum : ∑ k : Fin n, X_hat i k * L k j = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i.val < k.val
    · rw [hX_lower i k hik]
      ring
    · have hkj : j.val > k.val := by
        exact Nat.lt_of_le_of_lt (Nat.le_of_not_gt hik) hij
      rw [hL_lower k j hkj]
      ring
  simp [hsum, hne]

/-- Method 2's stored triangular shape makes the left residual vanish above
    the diagonal.  This closes the easy structural part of the Lemma 14.1
    residual; the below-diagonal induction remains separate. -/
theorem triInv_method2_left_residual_upper_zero (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat) :
    ∀ i j : Fin n, i.val < j.val →
      ∑ k : Fin n, X_hat i k * L k j -
        (if i = j then 1 else 0) = 0 :=
  triInv_lower_left_residual_upper_zero n L X_hat
    hSpec.upper_zero hLT

/-- Method 2's diagonal residual bound from the diagonal error field in
    `Method2Spec`: on the diagonal, triangularity reduces `(X_hat * L)_{jj}`
    to `X_hat j j * L j j = 1 + δ`, with `|δ| ≤ u`. -/
theorem triInv_method2_left_residual_diag_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat) :
    ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤ fp.u := by
  intro j
  obtain ⟨δ, hδ, hdiag⟩ := hSpec.diag_err j
  have hsum : ∑ k : Fin n, X_hat j k * L k j =
      X_hat j j * L j j := by
    apply Finset.sum_eq_single j
    · intro k _ hk
      by_cases hjk : j.val < k.val
      · rw [hSpec.upper_zero j k hjk]
        ring
      · have hkj : j.val > k.val := by
          have hle : k.val ≤ j.val := Nat.le_of_not_gt hjk
          have hne_val : k.val ≠ j.val := by
            intro hval
            exact hk (Fin.ext hval)
          omega
        rw [hLT k j hkj]
        ring
    · intro hnot
      simp at hnot
  simpa [hsum, hdiag] using hδ

/-- Lemma 14.1 support: Method 2's diagonal residual has the product-budget
    shape needed by the all-region assembly theorem.  The diagonal relation
    `X_hat j j * L j j = 1 + δ`, together with `|δ| ≤ u` and
    `gammaValid fp (n + 1)`, ensures the diagonal product budget is nonvacuous:
    the full column budget is at least `1 - u`, while
    `gamma_(n+1) * (1 - u) ≥ u`. -/
theorem triInv_method2_left_residual_diag_product_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat) :
    ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤
        gamma fp (n + 1) * ∑ k : Fin n, |X_hat j k| * |L k j| := by
  intro j
  have hdiag_res :=
    triInv_method2_left_residual_diag_bound n fp L X_hat hLT hSpec j
  obtain ⟨δ, hδ, hdiag⟩ := hSpec.diag_err j
  have hle1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp hle1 hn1
  have hgamma1_le : gamma fp 1 ≤ gamma fp (n + 1) :=
    gamma_mono fp hle1 hn1
  have hu_lt_one : fp.u < 1 := by
    have h := hvalid1
    unfold gammaValid at h
    norm_num at h
    exact h
  have hone_minus_nonneg : 0 ≤ 1 - fp.u := by linarith
  have hgamma1_mul : gamma fp 1 * (1 - fp.u) = fp.u := by
    have hden : (1 - fp.u) ≠ 0 := by linarith
    unfold gamma
    norm_num
    field_simp [hden]
  let S : ℝ := ∑ k : Fin n, |X_hat j k| * |L k j|
  have hdiag_term_le_S : |X_hat j j| * |L j j| ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (abs_nonneg (X_hat j k)) (abs_nonneg (L k j)))
      (Finset.mem_univ j)
  have hone_minus_le_prod : 1 - fp.u ≤ |X_hat j j| * |L j j| := by
    have habs_lower : 1 - |δ| ≤ |1 + δ| := by
      have htri : (1 : ℝ) ≤ |1 + δ| + |δ| := by
        simpa [abs_neg, add_assoc] using (abs_add_le (1 + δ) (-δ))
      linarith
    calc
      1 - fp.u ≤ 1 - |δ| := by linarith
      _ ≤ |1 + δ| := habs_lower
      _ = |X_hat j j * L j j| := by rw [hdiag]
      _ = |X_hat j j| * |L j j| := by rw [abs_mul]
  have hu_le_coeff_budget : fp.u ≤ gamma fp (n + 1) * S := by
    calc
      fp.u = gamma fp 1 * (1 - fp.u) := hgamma1_mul.symm
      _ ≤ gamma fp (n + 1) * (1 - fp.u) :=
        mul_le_mul_of_nonneg_right hgamma1_le hone_minus_nonneg
      _ ≤ gamma fp (n + 1) * S := by
        apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn1)
        exact le_trans hone_minus_le_prod hdiag_term_le_S
  exact le_trans hdiag_res hu_le_coeff_budget

/-- Lemma 14.1 support: diagonal Method 2 product-budget bound from only the
    diagonal rounded-reciprocal certificate and triangular shape.

This is the same diagonal edge as
`triInv_method2_left_residual_diag_product_bound`, but it avoids depending on
the older full-column `Method2Spec.offdiag_err` field. -/
theorem triInv_method2_left_residual_diag_product_bound_of_diag_upper
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hUpper : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0) :
    ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤
        gamma fp (n + 1) * ∑ k : Fin n, |X_hat j k| * |L k j| := by
  intro j
  obtain ⟨δ, hδ, hdiag⟩ := hDiag j
  have hsum : ∑ k : Fin n, X_hat j k * L k j =
      X_hat j j * L j j := by
    apply Finset.sum_eq_single j
    · intro k _ hk
      by_cases hjk : j.val < k.val
      · rw [hUpper j k hjk]
        ring
      · have hkj : j.val > k.val := by
          have hle : k.val ≤ j.val := Nat.le_of_not_gt hjk
          have hne_val : k.val ≠ j.val := by
            intro hval
            exact hk (Fin.ext hval)
          omega
        rw [hLT k j hkj]
        ring
    · intro hnot
      simp at hnot
  have hdiag_res : |∑ k : Fin n, X_hat j k * L k j - 1| ≤ fp.u := by
    simpa [hsum, hdiag] using hδ
  have hle1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hvalid1 : gammaValid fp 1 :=
    gammaValid_mono fp hle1 hn1
  have hgamma1_le : gamma fp 1 ≤ gamma fp (n + 1) :=
    gamma_mono fp hle1 hn1
  have hu_lt_one : fp.u < 1 := by
    have h := hvalid1
    unfold gammaValid at h
    norm_num at h
    exact h
  have hone_minus_nonneg : 0 ≤ 1 - fp.u := by linarith
  have hgamma1_mul : gamma fp 1 * (1 - fp.u) = fp.u := by
    have hden : (1 - fp.u) ≠ 0 := by linarith
    unfold gamma
    norm_num
    field_simp [hden]
  let S : ℝ := ∑ k : Fin n, |X_hat j k| * |L k j|
  have hdiag_term_le_S : |X_hat j j| * |L j j| ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (abs_nonneg (X_hat j k)) (abs_nonneg (L k j)))
      (Finset.mem_univ j)
  have hone_minus_le_prod : 1 - fp.u ≤ |X_hat j j| * |L j j| := by
    have habs_lower : 1 - |δ| ≤ |1 + δ| := by
      have htri : (1 : ℝ) ≤ |1 + δ| + |δ| := by
        simpa [abs_neg, add_assoc] using (abs_add_le (1 + δ) (-δ))
      linarith
    calc
      1 - fp.u ≤ 1 - |δ| := by linarith
      _ ≤ |1 + δ| := habs_lower
      _ = |X_hat j j * L j j| := by rw [hdiag]
      _ = |X_hat j j| * |L j j| := by rw [abs_mul]
  have hu_le_coeff_budget : fp.u ≤ gamma fp (n + 1) * S := by
    calc
      fp.u = gamma fp 1 * (1 - fp.u) := hgamma1_mul.symm
      _ ≤ gamma fp (n + 1) * (1 - fp.u) :=
        mul_le_mul_of_nonneg_right hgamma1_le hone_minus_nonneg
      _ ≤ gamma fp (n + 1) * S := by
        apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp hn1)
        exact le_trans hone_minus_le_prod hdiag_term_le_S
  exact le_trans hdiag_res hu_le_coeff_budget

/-- Lemma 14.1 support: regionwise Method 2 residual bounds assemble into
    the full componentwise left-residual bound.  This is only an assembly
    theorem: the diagonal and below-diagonal product-budget estimates remain
    explicit hypotheses, so the missing rounded-loop induction is not hidden. -/
theorem triInv_method2_left_residual_from_region_bounds (n : ℕ)
    (L X_hat : Fin n → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps)
    (hUpper : ∀ i j : Fin n, i.val < j.val →
      ∑ k : Fin n, X_hat i k * L k j -
        (if i = j then 1 else 0) = 0)
    (hDiag : ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤
        eps * ∑ k : Fin n, |X_hat j k| * |L k j|)
    (hLower : ∀ j row : Fin n, row.val > j.val →
      |∑ k : Fin n, X_hat row k * L k j -
          (if row = j then 1 else 0)| ≤
        eps * ∑ k : Fin n, |X_hat row k| * |L k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        eps * ∑ k : Fin n, |X_hat i k| * |L k j| := by
  intro i j
  by_cases hij : i.val < j.val
  · have hzero := hUpper i j hij
    have hS_nonneg :
        0 ≤ ∑ k : Fin n, |X_hat i k| * |L k j| := by
      exact Finset.sum_nonneg fun k _ =>
        mul_nonneg (abs_nonneg (X_hat i k)) (abs_nonneg (L k j))
    have hres_zero :
        |∑ k : Fin n, X_hat i k * L k j -
            (if i = j then 1 else 0)| = 0 := by
      rw [hzero]
      simp
    rw [hres_zero]
    exact mul_nonneg heps hS_nonneg
  · by_cases hji : j.val < i.val
    · exact hLower j i hji
    · have hij_eq : i = j := Fin.ext (by omega)
      subst i
      simpa using hDiag j

/-- Method 2 off-diagonal update residual unpacked from `Method2Spec`:
    for `i > j`, the update equation gives a local delta certificate for
    `X_hat i j + X_hat j j * (X_hat * L) i j`. -/
theorem triInv_method2_offdiag_update_delta_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hSpec : Method2Spec fp n L X_hat) :
    ∀ j i : Fin n, i.val > j.val →
      ∃ Δ : ℝ,
        |Δ| ≤ gamma fp n * |X_hat i j| * |L j j| ∧
        X_hat i j +
          X_hat j j * (∑ k : Fin n, X_hat i k * L k j) = Δ := by
  intro j i hij
  obtain ⟨Δ_mv, hΔ, hupdate⟩ := hSpec.offdiag_err j i hij
  refine ⟨Δ_mv j, ?_, ?_⟩
  · simpa using hΔ j
  · rw [hupdate]
    ring

/-- Method 2 off-diagonal update residual after multiplying by the diagonal
    entry `L j j`.  This combines `offdiag_err` with the diagonal error field
    and is a below-diagonal support lemma for the Lemma 14.1 induction. -/
theorem triInv_method2_offdiag_scaled_residual_bound (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hSpec : Method2Spec fp n L X_hat) :
    ∀ j i : Fin n, i.val > j.val →
      ∃ δ : ℝ, |δ| ≤ fp.u ∧
        |X_hat i j * L j j +
          (1 + δ) * (∑ k : Fin n, X_hat i k * L k j)| ≤
        (gamma fp n * |X_hat i j| * |L j j|) * |L j j| := by
  intro j i hij
  obtain ⟨δ, hδ, hdiag⟩ := hSpec.diag_err j
  obtain ⟨Δ, hΔ, hΔeq⟩ :=
    triInv_method2_offdiag_update_delta_bound n fp L X_hat hSpec j i hij
  refine ⟨δ, hδ, ?_⟩
  have hmain :
      X_hat i j * L j j +
          (1 + δ) * (∑ k : Fin n, X_hat i k * L k j) =
        Δ * L j j := by
    calc
      X_hat i j * L j j +
          (1 + δ) * (∑ k : Fin n, X_hat i k * L k j)
          = (X_hat i j +
              X_hat j j * (∑ k : Fin n, X_hat i k * L k j)) * L j j := by
              rw [← hdiag]
              ring
      _ = Δ * L j j := by rw [hΔeq]
  rw [hmain]
  calc
    |Δ * L j j| = |Δ| * |L j j| := abs_mul _ _
    _ ≤ (gamma fp n * |X_hat i j| * |L j j|) * |L j j| :=
      mul_le_mul_of_nonneg_right hΔ (abs_nonneg _)

/-- **Abstract Lemma 14.1 interface** (Higham eq. 14.8): Method 2 left residual.

    The computed inverse X̂ from Method 2 satisfies the left residual bound:
      |X̂L − I| ≤ c'ₙu · (|X̂| · |L|).

    Higham proves this by induction on n using the 2×2 block partition
    L = [[α, 0], [y, M]], X̂ = [[β̂, 0], [ẑ, N̂]].

    This theorem is an abstract interface: the hypothesis `hLeftRes` is the
    Method 2 local/inductive analysis, and the theorem records the named
    contract for reuse by later matrix-inversion results. -/
theorem triInv_method2_left_residual (n : ℕ) (fp : FPModel)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ)
    (_hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (_hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (_hn : gammaValid fp n)
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j| :=
  hLeftRes

/-- Problem 14.2 / Lemma 14.1 normwise form:
    Method 2's componentwise left-residual interface implies the corresponding
    infinity-norm residual bound. -/
theorem triInv_method2_left_residual_normwise (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel)
    (L : Fin n → Fin n → ℝ) (X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j|) :
    infNorm (fun i j =>
      ∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm X_hat * infNorm L := by
  have hComp :=
    triInv_method2_left_residual n fp L X_hat hL_diag hLT hn hLeftRes
  exact higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (R := fun i j => ∑ k : Fin n, X_hat i k * L k j -
      if i = j then 1 else 0)
    (A := X_hat) (B := L) (gamma_nonneg fp hn) hComp

/-- **Method 1B row-to-column assembly** (Higham eqs. 14.11--14.13 support).

    If each row of a fixed computed column has its own local backward-error
    row certificate, assemble those rows into the full matrix perturbation
    certificate expected by `BlockMethod1BSpec.column_backward_error`. -/
theorem triInv_method1B_column_backward_error_of_row_certificates
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ) (j : Fin n)
    (hRows : ∀ i : Fin n, ∃ Δrow : Fin n → ℝ,
      (∀ k : Fin n, |Δrow k| ≤ gamma fp n * |L i k|) ∧
      ∑ k : Fin n, (L i k + Δrow k) * X_hat k j =
        if i = j then 1 else 0) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k : Fin n, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i : Fin n, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0 := by
  classical
  let ΔL : Fin n → Fin n → ℝ := fun i k => Classical.choose (hRows i) k
  refine ⟨ΔL, ?_, ?_⟩
  · intro i k
    simpa [ΔL] using (Classical.choose_spec (hRows i)).1 k
  · intro i
    simpa [ΔL] using (Classical.choose_spec (hRows i)).2

/-- **Method 1B specification from column backward errors** (Higham eqs.
    14.11--14.13 support).

    This source-facing packaging theorem records the exact data needed by the
    abstract block Method 1B interface: a compatible block count, lower
    triangular shape of the computed inverse, and per-column backward-error
    certificates.  The block-loop derivation of those column certificates
    remains a separate dependency. -/
theorem triInv_method1B_spec_of_column_backward_error
    (n N : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hCol : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0) :
    BlockMethod1BSpec fp n N L X_hat :=
  { block_count_le_dim := hBlockCount
    lower_triangular_inverse := hLower
    column_backward_error := hCol }

/-- **Method 1B specification from row-local certificates** (Higham eqs.
    14.11--14.13 support).

    This bridge reduces the open block-loop obligation to row-local
    backward-error certificates for each computed column. -/
theorem triInv_method1B_spec_of_row_certificates
    (n N : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hRows : ∀ j i : Fin n, ∃ Δrow : Fin n → ℝ,
      (∀ k : Fin n, |Δrow k| ≤ gamma fp n * |L i k|) ∧
      ∑ k : Fin n, (L i k + Δrow k) * X_hat k j =
        if i = j then 1 else 0) :
    BlockMethod1BSpec fp n N L X_hat :=
  triInv_method1B_spec_of_column_backward_error n N fp L X_hat
    hBlockCount hLower
    (fun j => triInv_method1B_column_backward_error_of_row_certificates
      n fp L X_hat j (hRows j))

/-- **Lemma 14.2** (Higham eq. 14.10): Method 1B right residual.

    |LX̂ − I| ≤ cₙu|L||X̂|.

    The block version achieves the same right residual bound as the
    unblocked Method 1. -/
theorem triInv_method1B_right_residual (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (_hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (_hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (_hn : gammaValid fp n)
    -- Hypothesis: each column of X̂ satisfies the same per-column backward error
    -- as Method 1 (forwardSub_backward_error).
    (hCol : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
  intro i j
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ := hCol j
  have hLX : ∑ k : Fin n, L i k * X_hat k j - (if i = j then (1 : ℝ) else 0) =
      -(∑ k : Fin n, ΔL i k * X_hat k j) := by
    have h := hΔL_eq i
    have hsplit : ∑ k : Fin n, L i k * X_hat k j +
        ∑ k : Fin n, ΔL i k * X_hat k j =
        (if i = j then (1 : ℝ) else 0) := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hLX, abs_neg]
  calc |∑ k : Fin n, ΔL i k * X_hat k j|
      ≤ ∑ k : Fin n, |ΔL i k * X_hat k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |ΔL i k| * |X_hat k j| := by
        apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
    _ ≤ ∑ k : Fin n, (gamma fp n * |L i k|) * |X_hat k j| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (hΔL_bound i k) (abs_nonneg _)
    _ = gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _; ring

/-- Method 1B right residual obtained from the block-method specification. -/
theorem triInv_method1B_right_residual_from_spec (n N : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hSpec : BlockMethod1BSpec fp n N L X_hat) :
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| :=
  triInv_method1B_right_residual n fp L X_hat hL_diag hLT hn
    hSpec.column_backward_error

/-- **Lemma 14.2 bridge**: Method 1B right residual from explicit column
    backward-error certificates.

    This theorem separates the residual consequence from the still-open block
    partition proof of the column certificates in equations (14.11)--(14.13). -/
theorem triInv_method1B_right_residual_of_column_backward_error
    (n N : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hCol : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| :=
  triInv_method1B_right_residual_from_spec n N fp L X_hat hL_diag hLT hn
    (triInv_method1B_spec_of_column_backward_error n N fp L X_hat
      hBlockCount hLower hCol)

/-- **Lemma 14.2 bridge**: Method 1B right residual from row-local
    backward-error certificates.

    This is a row-local companion to
    `triInv_method1B_right_residual_of_column_backward_error`; the remaining
    source obligation is to derive the row certificates from the block Method
    1B update loop. -/
theorem triInv_method1B_right_residual_of_row_certificates
    (n N : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hRows : ∀ j i : Fin n, ∃ Δrow : Fin n → ℝ,
      (∀ k : Fin n, |Δrow k| ≤ gamma fp n * |L i k|) ∧
      ∑ k : Fin n, (L i k + Δrow k) * X_hat k j =
        if i = j then 1 else 0) :
    ∀ i j : Fin n,
      |∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |L i k| * |X_hat k j| :=
  triInv_method1B_right_residual_from_spec n N fp L X_hat hL_diag hLT hn
    (triInv_method1B_spec_of_row_certificates n N fp L X_hat
      hBlockCount hLower hRows)

/-- Problem 14.2 / Lemma 14.2 normwise form:
    Method 1B's componentwise right-residual bound implies the corresponding
    infinity-norm residual bound. -/
theorem triInv_method1B_right_residual_normwise (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hCol : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0) :
    infNorm (fun i j =>
      ∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm L * infNorm X_hat := by
  have hComp :=
    triInv_method1B_right_residual n fp L X_hat hL_diag hLT hn hCol
  exact higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (R := fun i j => ∑ k : Fin n, L i k * X_hat k j -
      if i = j then 1 else 0)
    (A := L) (B := X_hat) (gamma_nonneg fp hn) hComp

/-- Method 1B normwise right-residual bound obtained from the block-method
    specification. -/
theorem triInv_method1B_right_residual_normwise_from_spec
    (n N : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hSpec : BlockMethod1BSpec fp n N L X_hat) :
    infNorm (fun i j =>
      ∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm L * infNorm X_hat :=
  triInv_method1B_right_residual_normwise n hn0 fp L X_hat
    hL_diag hLT hn hSpec.column_backward_error

/-- Problem 14.2 / Lemma 14.2 normwise bridge:
    Method 1B's explicit column backward-error certificates imply the
    corresponding infinity-norm right-residual bound.

    This is the normwise companion of
    `triInv_method1B_right_residual_of_column_backward_error`; the open source
    obligation is still to derive the column certificates from the block Method
    1B loop in equations (14.11)--(14.13). -/
theorem triInv_method1B_right_residual_normwise_of_column_backward_error
    (n N : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hCol : ∀ j : Fin n, ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i k, |ΔL i k| ≤ gamma fp n * |L i k|) ∧
      ∀ i, ∑ k : Fin n, (L i k + ΔL i k) * X_hat k j =
        if i = j then 1 else 0) :
    infNorm (fun i j =>
      ∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm L * infNorm X_hat :=
  triInv_method1B_right_residual_normwise_from_spec n N hn0 fp L X_hat
    hL_diag hLT hn
    (triInv_method1B_spec_of_column_backward_error n N fp L X_hat
      hBlockCount hLower hCol)

/-- Problem 14.2 / Lemma 14.2 normwise bridge:
    Method 1B's row-local backward-error certificates imply the corresponding
    infinity-norm right-residual bound after assembling the rows into the
    column-certificate interface.

    This is the normwise companion of
    `triInv_method1B_right_residual_of_row_certificates`; the open source
    obligation is still to derive the row certificates from the block Method
    1B loop in equations (14.11)--(14.13). -/
theorem triInv_method1B_right_residual_normwise_of_row_certificates
    (n N : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hBlockCount : N ≤ n)
    (hLower : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hRows : ∀ j i : Fin n, ∃ Δrow : Fin n → ℝ,
      (∀ k : Fin n, |Δrow k| ≤ gamma fp n * |L i k|) ∧
      ∑ k : Fin n, (L i k + Δrow k) * X_hat k j =
        if i = j then 1 else 0) :
    infNorm (fun i j =>
      ∑ k : Fin n, L i k * X_hat k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm L * infNorm X_hat :=
  triInv_method1B_right_residual_normwise_from_spec n N hn0 fp L X_hat
    hL_diag hLT hn
    (triInv_method1B_spec_of_row_certificates n N fp L X_hat
      hBlockCount hLower hRows)

/-- **Abstract Lemma 14.3 interface**: Method 2C left residual.

    |X̂L − I| ≤ cₙu|X̂||L|.

    Method 2C (LAPACK's xTRTRI) achieves the same left residual bound as
    the unblocked Method 2.

    This theorem is a named abstract interface: `hLeftRes` supplies the
    Method 2C block-loop residual analysis. -/
theorem triInv_method2C_left_residual (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (_hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (_hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (_hn : gammaValid fp n)
    -- Hypothesis: X̂ satisfies Method 2C spec (solve with L_jj from right,
    -- then back substitution with L_jj from right).
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j|) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j| :=
  hLeftRes

/-- Problem 14.2 / Lemma 14.3 normwise form:
    Method 2C's componentwise left-residual interface implies the corresponding
    infinity-norm residual bound. -/
theorem triInv_method2C_left_residual_normwise (n : ℕ) (hn0 : 0 < n)
    (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hn : gammaValid fp n)
    (hLeftRes : ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0| ≤
      gamma fp n * ∑ k : Fin n, |X_hat i k| * |L k j|) :
    infNorm (fun i j =>
      ∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0) ≤
      gamma fp n * infNorm X_hat * infNorm L := by
  have hComp :=
    triInv_method2C_left_residual n fp L X_hat hL_diag hLT hn hLeftRes
  exact higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (R := fun i j => ∑ k : Fin n, X_hat i k * L k j -
      if i = j then 1 else 0)
    (A := X_hat) (B := L) (gamma_nonneg fp hn) hComp

/-- Lemma 14.1 support: a strict-tail Method 2 update with a `gamma_n`
    scaled product certificate gives the source-shaped below-diagonal
    `gamma_{n+1}` full-column residual budget. -/
theorem triInv_method2_offdiag_trailing_update_gamma_full_bound
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLT : ∀ a b : Fin n, b.val > a.val → L a b = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ gamma fp n *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ) :
    ∀ j row : Fin n, row.val > j.val →
      |(∑ k : Fin n, X_hat row k * L k j) -
          (if row = j then 1 else 0)| ≤
        gamma fp (n + 1) * (∑ k : Fin n, |X_hat row k| * |L k j|) := by
  intro j row hij
  have hn : gammaValid fp n := gammaValid_mono fp (Nat.le_succ n) hn1
  have hbase :=
    triInv_method2_offdiag_trailing_update_full_bound n fp L X_hat
      (gamma_nonneg fp hn) hLT hDiag hTrail j row hij
  let S : ℝ := ∑ k : Fin n, |X_hat row k| * |L k j|
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg (fun k _ =>
      mul_nonneg (abs_nonneg (X_hat row k)) (abs_nonneg (L k j)))
  have hcoeff : fp.u + gamma fp n ≤ gamma fp (n + 1) :=
    higham14_unit_roundoff_add_gamma_le_gamma_succ fp n hn1
  exact le_trans hbase (mul_le_mul_of_nonneg_right hcoeff hS_nonneg)

/-- Lemma 14.1 support: once the rounded strict-tail Method 2 update supplies
    a `gamma_n` certificate, the already-proved upper, diagonal, and
    below-diagonal regional estimates assemble into the source-shaped
    `gamma_{n+1}` componentwise left-residual bound.

This is still conditional infrastructure: the rounded strict-tail certificate
is the remaining source-facing induction obligation. -/
theorem triInv_method2_left_residual_of_strict_tail_gamma
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat)
    (hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ gamma fp n *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 1) * ∑ k : Fin n, |X_hat i k| * |L k j| := by
  have hUpper :=
    triInv_method2_left_residual_upper_zero n fp L X_hat hLT hSpec
  have hDiag :=
    triInv_method2_left_residual_diag_product_bound n fp L X_hat hn1 hLT hSpec
  have hLower :=
    triInv_method2_offdiag_trailing_update_gamma_full_bound n fp L X_hat
      hn1 hLT hSpec.diag_err hTrail
  exact triInv_method2_left_residual_from_region_bounds n L X_hat
    (gamma_nonneg fp hn1) hUpper hDiag hLower

/-- Lemma 14.1 support: if the below-diagonal Method 2 entry is obtained by a
    rounded strict-tail dot product and then scaled exactly by `-X_hat j j`,
    the full componentwise left-residual bound follows with coefficient
    `gamma_{n+1}`.

This is a concrete dot-product adapter, not the final fully rounded Method 2
loop theorem: the subsequent scalar scaling is still exact on this surface. -/
theorem triInv_method2_left_residual_of_strict_tail_fl_dot
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat)
    (hUpdate : ∀ j row : Fin n, row.val > j.val →
      X_hat row j =
        -X_hat j j *
          fl_dotProduct fp n
            (fun k : Fin n => if j.val < k.val then X_hat row k else 0)
            (fun k : Fin n => L k j)) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 1) * ∑ k : Fin n, |X_hat i k| * |L k j| := by
  have hn : gammaValid fp n := gammaValid_mono fp (Nat.le_succ n) hn1
  have hη_nonneg : 0 ≤ (1 + fp.u) * gamma fp n := by
    exact mul_nonneg (by linarith [fp.u_nonneg]) (gamma_nonneg fp hn)
  have hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ ((1 + fp.u) * gamma fp n) *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ := by
    intro j row hij
    let x : Fin n → ℝ := fun k => if j.val < k.val then X_hat row k else 0
    let y : Fin n → ℝ := fun k => L k j
    let exactTail : ℝ :=
      ∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0
    let tailAbs : ℝ :=
      ∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0
    let flTail : ℝ := fl_dotProduct fp n x y
    let Δ : ℝ := -X_hat j j * (flTail - exactTail)
    refine Exists.intro Δ (And.intro ?_ ?_)
    case refine_1 =>
      have hdot := dotProduct_error_bound fp n x y hn
      have hsum_exact :
          (∑ k : Fin n, x k * y k) = exactTail := by
        dsimp [x, y, exactTail]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hsum_abs :
          (∑ k : Fin n, |x k| * |y k|) = tailAbs := by
        dsimp [x, y, tailAbs]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hdot_tail : |flTail - exactTail| ≤ gamma fp n * tailAbs := by
        simpa [flTail, hsum_exact, hsum_abs] using hdot
      let δ : ℝ := Classical.choose (hSpec.diag_err j)
      have hδ_diag := Classical.choose_spec (hSpec.diag_err j)
      have hδ : |δ| ≤ fp.u := hδ_diag.1
      have hdiag : X_hat j j * L j j = 1 + δ := hδ_diag.2
      have hdiag_abs : |X_hat j j * L j j| ≤ 1 + fp.u := by
        calc
          |X_hat j j * L j j| = |1 + δ| := by rw [hdiag]
          _ ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by
            norm_num
            exact hδ
      have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      calc
        |Δ * L j j| = |X_hat j j * L j j| * |flTail - exactTail| := by
          dsimp [Δ]
          rw [abs_mul, abs_mul, abs_neg, abs_mul]
          ring
        _ ≤ (1 + fp.u) * (gamma fp n * tailAbs) := by
          exact mul_le_mul hdiag_abs hdot_tail (abs_nonneg _) honeu_nonneg
        _ = ((1 + fp.u) * gamma fp n) * tailAbs := by ring
    case refine_2 =>
      have hupdate := hUpdate j row hij
      calc
        X_hat row j = -X_hat j j * flTail := by
          simpa [flTail, x, y] using hupdate
        _ = -X_hat j j * exactTail + Δ := by
          dsimp [Δ]
          ring
  have hUpper :=
    triInv_method2_left_residual_upper_zero n fp L X_hat hLT hSpec
  have hDiag :=
    triInv_method2_left_residual_diag_product_bound n fp L X_hat hn1 hLT hSpec
  have hLowerEta :=
    triInv_method2_offdiag_trailing_update_full_bound n fp L X_hat
      hη_nonneg hLT hSpec.diag_err hTrail
  have hcoeff : fp.u + (1 + fp.u) * gamma fp n ≤ gamma fp (n + 1) :=
    higham14_unit_roundoff_add_one_plus_u_mul_gamma_le_gamma_succ fp n hn1
  have hLower : ∀ j row : Fin n, row.val > j.val →
      |∑ k : Fin n, X_hat row k * L k j -
          (if row = j then 1 else 0)| ≤
        gamma fp (n + 1) * ∑ k : Fin n, |X_hat row k| * |L k j| := by
    intro j row hij
    have hbase := hLowerEta j row hij
    have hS_nonneg : 0 ≤ ∑ k : Fin n, |X_hat row k| * |L k j| := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_trans hbase (mul_le_mul_of_nonneg_right hcoeff hS_nonneg)
  exact triInv_method2_left_residual_from_region_bounds n L X_hat
    (gamma_nonneg fp hn1) hUpper hDiag hLower

/-- Lemma 14.1 support: if the below-diagonal Method 2 entry is obtained by a
    rounded strict-tail dot product and then by one rounded scalar
    multiplication with `-X_hat j j`, the full componentwise left-residual bound
    follows with the conservative coefficient `gamma_{n+2}`.

This closes the local dot/scalar rounding wrapper for the strict-tail update.
It is still not the full source loop theorem, since it assumes the stored
below-diagonal entries are exactly produced by this one dot/scalar kernel. -/
theorem triInv_method2_left_residual_of_strict_tail_fl_dot_fl_mul
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hSpec : Method2Spec fp n L X_hat)
    (hUpdate : ∀ j row : Fin n, row.val > j.val →
      X_hat row j =
        fp.fl_mul (-X_hat j j)
          (fl_dotProduct fp n
            (fun k : Fin n => if j.val < k.val then X_hat row k else 0)
            (fun k : Fin n => L k j))) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat i k| * |L k j| := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega : n ≤ n + 2) hn2
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega : n + 1 ≤ n + 2) hn2
  have hη_nonneg :
      0 ≤ (1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n)) := by
    have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hn
    have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have honeγ_nonneg : 0 ≤ 1 + gamma fp n := by linarith
    exact mul_nonneg honeu_nonneg
      (add_nonneg hγn_nonneg (mul_nonneg fp.u_nonneg honeγ_nonneg))
  have hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ ((1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n))) *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ := by
    intro j row hij
    let x : Fin n → ℝ := fun k => if j.val < k.val then X_hat row k else 0
    let y : Fin n → ℝ := fun k => L k j
    let exactTail : ℝ :=
      ∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0
    let tailAbs : ℝ :=
      ∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0
    let flTail : ℝ := fl_dotProduct fp n x y
    let Δ : ℝ := fp.fl_mul (-X_hat j j) flTail - (-X_hat j j * exactTail)
    refine Exists.intro Δ (And.intro ?_ ?_)
    · obtain ⟨δmul, hδmul, hmul⟩ := fp.model_mul (-X_hat j j) flTail
      have hdot := dotProduct_error_bound fp n x y hn
      have hsum_exact :
          (∑ k : Fin n, x k * y k) = exactTail := by
        dsimp [x, y, exactTail]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hsum_abs :
          (∑ k : Fin n, |x k| * |y k|) = tailAbs := by
        dsimp [x, y, tailAbs]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hdot_tail : |flTail - exactTail| ≤ gamma fp n * tailAbs := by
        simpa [flTail, hsum_exact, hsum_abs] using hdot
      have htail_abs : |exactTail| ≤ tailAbs := by
        calc
          |exactTail| =
              |∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0| := by
                rfl
          _ ≤ ∑ k : Fin n,
                |if j.val < k.val then X_hat row k * L k j else 0| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = tailAbs := by
              apply Finset.sum_congr rfl
              intro k _
              by_cases hjk : j.val < k.val <;> simp [hjk, abs_mul]
      have htail_nonneg : 0 ≤ tailAbs := by
        dsimp [tailAbs]
        exact Finset.sum_nonneg (fun k _ => by
          by_cases hjk : j.val < k.val
          · simpa [hjk] using
              mul_nonneg (abs_nonneg (X_hat row k)) (abs_nonneg (L k j))
          · simp [hjk])
      have hfl_abs : |flTail| ≤ (1 + gamma fp n) * tailAbs := by
        calc
          |flTail| = |exactTail + (flTail - exactTail)| := by
            congr 1
            ring
          _ ≤ |exactTail| + |flTail - exactTail| :=
              abs_add_le exactTail (flTail - exactTail)
          _ ≤ tailAbs + gamma fp n * tailAbs :=
              add_le_add htail_abs hdot_tail
          _ = (1 + gamma fp n) * tailAbs := by ring
      let δ : ℝ := Classical.choose (hSpec.diag_err j)
      have hδ_diag := Classical.choose_spec (hSpec.diag_err j)
      have hδ : |δ| ≤ fp.u := hδ_diag.1
      have hdiag : X_hat j j * L j j = 1 + δ := hδ_diag.2
      have hdiag_abs : |X_hat j j * L j j| ≤ 1 + fp.u := by
        calc
          |X_hat j j * L j j| = |1 + δ| := by rw [hdiag]
          _ ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by
            norm_num
            exact hδ
      have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have honeγ_nonneg : 0 ≤ 1 + gamma fp n := by
        linarith [gamma_nonneg fp hn]
      have hcoef_nonneg :
          0 ≤ (1 + fp.u) * ((1 + gamma fp n) * tailAbs) := by
        exact mul_nonneg honeu_nonneg
          (mul_nonneg honeγ_nonneg htail_nonneg)
      have hΔ_decomp :
          Δ * L j j =
            (-X_hat j j * L j j) * (flTail - exactTail) +
              ((-X_hat j j * L j j) * flTail) * δmul := by
        dsimp [Δ]
        rw [hmul]
        ring
      have hfirst :
          |(-X_hat j j * L j j) * (flTail - exactTail)| ≤
            (1 + fp.u) * (gamma fp n * tailAbs) := by
        have hneg_abs : |(-X_hat j j * L j j)| = |X_hat j j * L j j| := by
          have hneg : (-X_hat j j * L j j) = -(X_hat j j * L j j) := by ring
          rw [hneg, abs_neg]
        calc
          |(-X_hat j j * L j j) * (flTail - exactTail)|
              = |X_hat j j * L j j| * |flTail - exactTail| := by
                rw [abs_mul, hneg_abs]
          _ ≤ (1 + fp.u) * (gamma fp n * tailAbs) :=
              mul_le_mul hdiag_abs hdot_tail (abs_nonneg _) honeu_nonneg
      have hsecond :
          |((-X_hat j j * L j j) * flTail) * δmul| ≤
            ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u := by
        have hneg_abs : |(-X_hat j j * L j j)| = |X_hat j j * L j j| := by
          have hneg : (-X_hat j j * L j j) = -(X_hat j j * L j j) := by ring
          rw [hneg, abs_neg]
        have hleft :
            |X_hat j j * L j j| * |flTail| ≤
              (1 + fp.u) * ((1 + gamma fp n) * tailAbs) :=
          mul_le_mul hdiag_abs hfl_abs (abs_nonneg _) honeu_nonneg
        calc
          |((-X_hat j j * L j j) * flTail) * δmul|
              = |X_hat j j * L j j| * |flTail| * |δmul| := by
                rw [abs_mul, abs_mul, hneg_abs]
          _ ≤ ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u :=
              mul_le_mul hleft hδmul (abs_nonneg _) hcoef_nonneg
      calc
        |Δ * L j j|
            = |(-X_hat j j * L j j) * (flTail - exactTail) +
                ((-X_hat j j * L j j) * flTail) * δmul| := by
              rw [hΔ_decomp]
        _ ≤ |(-X_hat j j * L j j) * (flTail - exactTail)| +
              |((-X_hat j j * L j j) * flTail) * δmul| :=
            abs_add_le _ _
        _ ≤ (1 + fp.u) * (gamma fp n * tailAbs) +
              ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u :=
            add_le_add hfirst hsecond
        _ = ((1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n))) *
              tailAbs := by ring
    · have hupdate := hUpdate j row hij
      calc
        X_hat row j = fp.fl_mul (-X_hat j j) flTail := by
          simpa [flTail, x, y] using hupdate
        _ = -X_hat j j * exactTail + Δ := by
          dsimp [Δ]
          ring
  have hUpper :=
    triInv_method2_left_residual_upper_zero n fp L X_hat hLT hSpec
  have hDiagBase :=
    triInv_method2_left_residual_diag_product_bound n fp L X_hat hn1 hLT hSpec
  have hDiag : ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat j k| * |L k j| := by
    intro j
    have hS_nonneg : 0 ≤ ∑ k : Fin n, |X_hat j k| * |L k j| := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hmono : gamma fp (n + 1) ≤ gamma fp (n + 2) :=
      gamma_mono fp (by omega : n + 1 ≤ n + 2) hn2
    exact le_trans (hDiagBase j) (mul_le_mul_of_nonneg_right hmono hS_nonneg)
  have hLowerEta :=
    triInv_method2_offdiag_trailing_update_full_bound n fp L X_hat
      hη_nonneg hLT hSpec.diag_err hTrail
  have hcoeff :
      fp.u + (1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n)) ≤
        gamma fp (n + 2) :=
    higham14_unit_roundoff_add_one_plus_u_mul_rounded_gamma_le_gamma_succ_succ
      fp n hn2
  have hLower : ∀ j row : Fin n, row.val > j.val →
      |∑ k : Fin n, X_hat row k * L k j -
          (if row = j then 1 else 0)| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat row k| * |L k j| := by
    intro j row hij
    have hbase := hLowerEta j row hij
    have hS_nonneg : 0 ≤ ∑ k : Fin n, |X_hat row k| * |L k j| := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_trans hbase (mul_le_mul_of_nonneg_right hcoeff hS_nonneg)
  exact triInv_method2_left_residual_from_region_bounds n L X_hat
    (gamma_nonneg fp hn2) hUpper hDiag hLower

/-- Lemma 14.1 support: a strict-tail Method 2 storage recurrence implies
    the full componentwise left-residual bound using only the diagonal
    rounded-reciprocal certificate, triangular shape, and stored rounded
    dot/scalar update.

Compared with `triInv_method2_left_residual_of_strict_tail_fl_dot_fl_mul`,
this theorem removes the dependency on the older `Method2Spec.offdiag_err`
field.  It still assumes the storage recurrence itself; the remaining
source-facing loop obligation is to prove `hStore` from the concrete
reverse-column implementation. -/
theorem triInv_method2_left_residual_of_strict_tail_storage
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hUpper : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hStore : ∀ j row : Fin n, row.val > j.val →
      X_hat row j =
        fp.fl_mul (-X_hat j j)
          (fl_dotProduct fp n
            (fun k : Fin n => if j.val < k.val then X_hat row k else 0)
            (fun k : Fin n => L k j))) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat i k| * |L k j| := by
  have hn : gammaValid fp n := gammaValid_mono fp (by omega : n ≤ n + 2) hn2
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega : n + 1 ≤ n + 2) hn2
  have hη_nonneg :
      0 ≤ (1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n)) := by
    have hγn_nonneg : 0 ≤ gamma fp n := gamma_nonneg fp hn
    have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have honeγ_nonneg : 0 ≤ 1 + gamma fp n := by linarith
    exact mul_nonneg honeu_nonneg
      (add_nonneg hγn_nonneg (mul_nonneg fp.u_nonneg honeγ_nonneg))
  have hTrail : ∀ j row : Fin n, row.val > j.val →
      ∃ Δ : ℝ,
        |Δ * L j j| ≤ ((1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n))) *
          (∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0) ∧
        X_hat row j =
          -X_hat j j *
            (∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0) + Δ := by
    intro j row hij
    let x : Fin n → ℝ := fun k => if j.val < k.val then X_hat row k else 0
    let y : Fin n → ℝ := fun k => L k j
    let exactTail : ℝ :=
      ∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0
    let tailAbs : ℝ :=
      ∑ k : Fin n, if j.val < k.val then |X_hat row k| * |L k j| else 0
    let flTail : ℝ := fl_dotProduct fp n x y
    let Δ : ℝ := fp.fl_mul (-X_hat j j) flTail - (-X_hat j j * exactTail)
    refine Exists.intro Δ (And.intro ?_ ?_)
    · obtain ⟨δmul, hδmul, hmul⟩ := fp.model_mul (-X_hat j j) flTail
      have hdot := dotProduct_error_bound fp n x y hn
      have hsum_exact :
          (∑ k : Fin n, x k * y k) = exactTail := by
        dsimp [x, y, exactTail]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hsum_abs :
          (∑ k : Fin n, |x k| * |y k|) = tailAbs := by
        dsimp [x, y, tailAbs]
        apply Finset.sum_congr rfl
        intro k _
        by_cases hjk : j.val < k.val <;> simp [hjk]
      have hdot_tail : |flTail - exactTail| ≤ gamma fp n * tailAbs := by
        simpa [flTail, hsum_exact, hsum_abs] using hdot
      have htail_abs : |exactTail| ≤ tailAbs := by
        calc
          |exactTail| =
              |∑ k : Fin n, if j.val < k.val then X_hat row k * L k j else 0| := by
                rfl
          _ ≤ ∑ k : Fin n,
                |if j.val < k.val then X_hat row k * L k j else 0| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = tailAbs := by
              apply Finset.sum_congr rfl
              intro k _
              by_cases hjk : j.val < k.val <;> simp [hjk, abs_mul]
      have htail_nonneg : 0 ≤ tailAbs := by
        dsimp [tailAbs]
        exact Finset.sum_nonneg (fun k _ => by
          by_cases hjk : j.val < k.val
          · simpa [hjk] using
              mul_nonneg (abs_nonneg (X_hat row k)) (abs_nonneg (L k j))
          · simp [hjk])
      have hfl_abs : |flTail| ≤ (1 + gamma fp n) * tailAbs := by
        calc
          |flTail| = |exactTail + (flTail - exactTail)| := by
            congr 1
            ring
          _ ≤ |exactTail| + |flTail - exactTail| :=
              abs_add_le exactTail (flTail - exactTail)
          _ ≤ tailAbs + gamma fp n * tailAbs :=
              add_le_add htail_abs hdot_tail
          _ = (1 + gamma fp n) * tailAbs := by ring
      obtain ⟨δ, hδ, hdiag⟩ := hDiag j
      have hdiag_abs : |X_hat j j * L j j| ≤ 1 + fp.u := by
        calc
          |X_hat j j * L j j| = |1 + δ| := by rw [hdiag]
          _ ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
          _ ≤ 1 + fp.u := by
            norm_num
            exact hδ
      have honeu_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have honeγ_nonneg : 0 ≤ 1 + gamma fp n := by
        linarith [gamma_nonneg fp hn]
      have hcoef_nonneg :
          0 ≤ (1 + fp.u) * ((1 + gamma fp n) * tailAbs) := by
        exact mul_nonneg honeu_nonneg
          (mul_nonneg honeγ_nonneg htail_nonneg)
      have hΔ_decomp :
          Δ * L j j =
            (-X_hat j j * L j j) * (flTail - exactTail) +
              ((-X_hat j j * L j j) * flTail) * δmul := by
        dsimp [Δ]
        rw [hmul]
        ring
      have hfirst :
          |(-X_hat j j * L j j) * (flTail - exactTail)| ≤
            (1 + fp.u) * (gamma fp n * tailAbs) := by
        have hneg_abs : |(-X_hat j j * L j j)| = |X_hat j j * L j j| := by
          have hneg : (-X_hat j j * L j j) = -(X_hat j j * L j j) := by ring
          rw [hneg, abs_neg]
        calc
          |(-X_hat j j * L j j) * (flTail - exactTail)|
              = |X_hat j j * L j j| * |flTail - exactTail| := by
                rw [abs_mul, hneg_abs]
          _ ≤ (1 + fp.u) * (gamma fp n * tailAbs) :=
              mul_le_mul hdiag_abs hdot_tail (abs_nonneg _) honeu_nonneg
      have hsecond :
          |((-X_hat j j * L j j) * flTail) * δmul| ≤
            ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u := by
        have hneg_abs : |(-X_hat j j * L j j)| = |X_hat j j * L j j| := by
          have hneg : (-X_hat j j * L j j) = -(X_hat j j * L j j) := by ring
          rw [hneg, abs_neg]
        have hleft :
            |X_hat j j * L j j| * |flTail| ≤
              (1 + fp.u) * ((1 + gamma fp n) * tailAbs) :=
          mul_le_mul hdiag_abs hfl_abs (abs_nonneg _) honeu_nonneg
        calc
          |((-X_hat j j * L j j) * flTail) * δmul|
              = |X_hat j j * L j j| * |flTail| * |δmul| := by
                rw [abs_mul, abs_mul, hneg_abs]
          _ ≤ ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u :=
              mul_le_mul hleft hδmul (abs_nonneg _) hcoef_nonneg
      calc
        |Δ * L j j|
            = |(-X_hat j j * L j j) * (flTail - exactTail) +
                ((-X_hat j j * L j j) * flTail) * δmul| := by
              rw [hΔ_decomp]
        _ ≤ |(-X_hat j j * L j j) * (flTail - exactTail)| +
              |((-X_hat j j * L j j) * flTail) * δmul| :=
            abs_add_le _ _
        _ ≤ (1 + fp.u) * (gamma fp n * tailAbs) +
              ((1 + fp.u) * ((1 + gamma fp n) * tailAbs)) * fp.u :=
            add_le_add hfirst hsecond
        _ = ((1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n))) *
              tailAbs := by ring
    · have hstore := hStore j row hij
      calc
        X_hat row j = fp.fl_mul (-X_hat j j) flTail := by
          simpa [flTail, x, y] using hstore
        _ = -X_hat j j * exactTail + Δ := by
          dsimp [Δ]
          ring
  have hUpperRes :=
    triInv_lower_left_residual_upper_zero n L X_hat hUpper hLT
  have hDiagBase :=
    triInv_method2_left_residual_diag_product_bound_of_diag_upper
      n fp L X_hat hn1 hLT hDiag hUpper
  have hDiagBudget : ∀ j : Fin n,
      |∑ k : Fin n, X_hat j k * L k j - 1| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat j k| * |L k j| := by
    intro j
    have hS_nonneg : 0 ≤ ∑ k : Fin n, |X_hat j k| * |L k j| := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hmono : gamma fp (n + 1) ≤ gamma fp (n + 2) :=
      gamma_mono fp (by omega : n + 1 ≤ n + 2) hn2
    exact le_trans (hDiagBase j) (mul_le_mul_of_nonneg_right hmono hS_nonneg)
  have hLowerEta :=
    triInv_method2_offdiag_trailing_update_full_bound n fp L X_hat
      hη_nonneg hLT hDiag hTrail
  have hcoeff :
      fp.u + (1 + fp.u) * (gamma fp n + fp.u * (1 + gamma fp n)) ≤
        gamma fp (n + 2) :=
    higham14_unit_roundoff_add_one_plus_u_mul_rounded_gamma_le_gamma_succ_succ
      fp n hn2
  have hLower : ∀ j row : Fin n, row.val > j.val →
      |∑ k : Fin n, X_hat row k * L k j -
          (if row = j then 1 else 0)| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat row k| * |L k j| := by
    intro j row hij
    have hbase := hLowerEta j row hij
    have hS_nonneg : 0 ≤ ∑ k : Fin n, |X_hat row k| * |L k j| := by
      exact Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact le_trans hbase (mul_le_mul_of_nonneg_right hcoeff hS_nonneg)
  exact triInv_method2_left_residual_from_region_bounds n L X_hat
    (gamma_nonneg fp hn2) hUpperRes hDiagBudget hLower

/-- Problem 14.2 / Lemma 14.1 normwise bridge:
    the strict-tail Method 2 storage recurrence implies the corresponding
    infinity-norm left-residual bound.

This is the normwise companion to
`triInv_method2_left_residual_of_strict_tail_storage`.  It remains conditional
on the source-facing storage recurrence `hStore`, so the concrete reverse-column
loop proof producing that recurrence is still explicit. -/
theorem triInv_method2_left_residual_normwise_of_strict_tail_storage
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hDiag : ∀ j : Fin n, ∃ δ : ℝ, |δ| ≤ fp.u ∧
      X_hat j j * L j j = 1 + δ)
    (hUpper : ∀ i j : Fin n, i.val < j.val → X_hat i j = 0)
    (hStore : ∀ j row : Fin n, row.val > j.val →
      X_hat row j =
        fp.fl_mul (-X_hat j j)
          (fl_dotProduct fp n
            (fun k : Fin n => if j.val < k.val then X_hat row k else 0)
            (fun k : Fin n => L k j))) :
    infNorm (fun i j =>
      ∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0) ≤
      gamma fp (n + 2) * infNorm X_hat * infNorm L := by
  have hComp :=
    triInv_method2_left_residual_of_strict_tail_storage
      n fp L X_hat hn2 hLT hDiag hUpper hStore
  exact higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (R := fun i j => ∑ k : Fin n, X_hat i k * L k j -
      if i = j then 1 else 0)
    (A := X_hat) (B := L) (gamma_nonneg fp hn2) hComp

/-- Higham, 2nd ed., Chapter 14, Lemma 14.1 / equation (14.8), Method 2
    strict-tail kernel surface:
    a source-facing strict-tail dot/scalar kernel certificate implies the
    componentwise left-residual bound with coefficient `gamma_(n+2)`.

    This closes the residual consequence of the packaged kernel certificate.
    The concrete reverse-column loop proof that produces
    `Method2StrictTailKernelSpec` remains a separate selected dependency. -/
theorem triInv_method2_left_residual_of_strict_tail_kernel_spec
    (n : ℕ) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hKernel : Method2StrictTailKernelSpec fp n L X_hat) :
    ∀ i j : Fin n,
      |∑ k : Fin n, X_hat i k * L k j -
          (if i = j then 1 else 0)| ≤
        gamma fp (n + 2) * ∑ k : Fin n, |X_hat i k| * |L k j| :=
  triInv_method2_left_residual_of_strict_tail_fl_dot_fl_mul
    n fp L X_hat hn2 hLT hKernel.method2 hKernel.strict_tail_dot_scalar

/-- Problem 14.2 / Lemma 14.1 normwise bridge:
    a Method 2 strict-tail kernel certificate implies the corresponding
    infinity-norm left-residual bound, with the same conservative
    `gamma_(n+2)` coefficient as the rounded dot/scalar componentwise theorem.

    This is still conditional on the concrete reverse-column loop producing
    `Method2StrictTailKernelSpec`, but it removes the remaining normwise
    handoff once that kernel package is available. -/
theorem triInv_method2_left_residual_normwise_of_strict_tail_kernel_spec
    (n : ℕ) (hn0 : 0 < n) (fp : FPModel)
    (L X_hat : Fin n → Fin n → ℝ)
    (hn2 : gammaValid fp (n + 2))
    (hLT : ∀ i j : Fin n, j.val > i.val → L i j = 0)
    (hKernel : Method2StrictTailKernelSpec fp n L X_hat) :
    infNorm (fun i j =>
      ∑ k : Fin n, X_hat i k * L k j - if i = j then 1 else 0) ≤
      gamma fp (n + 2) * infNorm X_hat * infNorm L := by
  have hComp :=
    triInv_method2_left_residual_of_strict_tail_kernel_spec
      n fp L X_hat hn2 hLT hKernel
  exact higham14_infNorm_le_of_componentwise_matmul_bound hn0
    (R := fun i j => ∑ k : Fin n, X_hat i k * L k j -
      if i = j then 1 else 0)
    (A := X_hat) (B := L) (gamma_nonneg fp hn2) hComp

end NumStability
