-- Algorithms/Norm2.lean
--
-- Floating-point Euclidean norm kernels.
--
-- This file provides the low-level operation needed by Householder reflector
-- construction: compute a sum of squares using the existing floating-point dot
-- product, then apply the rounded square-root primitive from `FPModel`.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FieldSimp
import NumStability.Algorithms.DotProduct

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Exact Mathlib facts and floating-point vector 2-norm kernels
-- ============================================================

/-- Mathlib's finite-product L2 norm is the square root of the dot product. -/
theorem norm_toLp_two_eq_sqrt_dotProduct (n : ℕ) (x : Fin n → ℝ) :
    ‖WithLp.toLp 2 x‖ = Real.sqrt (x ⬝ᵥ x) := by
  rw [PiLp.norm_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
  unfold dotProduct
  simp [pow_two]

/-- Floating-point squared 2-norm computed as the dot product `xᵀx`. -/
noncomputable def fl_norm2Sq (fp : FPModel) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  fl_dotProduct fp n x x

/-- Floating-point 2-norm: rounded square root of the computed sum of squares.

    The domain side condition for the square-root error model is carried by
    theorems that reason about this definition. -/
noncomputable def fl_norm2 (fp : FPModel) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  fp.fl_sqrt (fl_norm2Sq fp n x)

theorem dotProduct_self_nonneg_real (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ x := by
  unfold dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- The squared 2-norm is zero exactly for the zero vector. -/
theorem dotProduct_self_eq_zero_iff_real (n : ℕ) (x : Fin n → ℝ) :
    x ⬝ᵥ x = 0 ↔ x = 0 := by
  exact dotProduct_self_eq_zero

/-- The squared 2-norm is nonzero exactly for a nonzero vector. -/
theorem dotProduct_self_ne_zero_iff_real (n : ℕ) (x : Fin n → ℝ) :
    x ⬝ᵥ x ≠ 0 ↔ x ≠ 0 := by
  exact not_congr (dotProduct_self_eq_zero_iff_real n x)

/-- The squared 2-norm is positive exactly for a nonzero vector. -/
theorem dotProduct_self_pos_iff_real (n : ℕ) (x : Fin n → ℝ) :
    0 < x ⬝ᵥ x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    rw [hx] at h
    simp [dotProduct] at h
  · intro hx
    have hne : x ⬝ᵥ x ≠ 0 :=
      (dotProduct_self_ne_zero_iff_real n x).2 hx
    exact lt_of_le_of_ne (dotProduct_self_nonneg_real n x) (Ne.symm hne)

theorem norm_toLp_two_nonneg (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ ‖WithLp.toLp 2 x‖ := by
  exact norm_nonneg _

/-- Collapse componentwise relative errors in a nonnegative weighted sum into
    one scalar relative error with the same bound.

    This is the exact algebraic step used when turning the dot-product
    componentwise result for `∑ xᵢ²(1+ηᵢ)` into Higham's scalar
    `(1+θₙ) xᵀx` form. -/
theorem weighted_sum_relative_error_nonneg (n : ℕ)
    (a η : Fin n → ℝ) (γ : ℝ)
    (hγ : 0 ≤ γ) (ha : ∀ i : Fin n, 0 ≤ a i)
    (hη : ∀ i : Fin n, |η i| ≤ γ) :
    ∃ θ : ℝ,
      |θ| ≤ γ ∧
      (∑ i : Fin n, a i * (1 + η i)) =
        (∑ i : Fin n, a i) * (1 + θ) := by
  let S : ℝ := ∑ i : Fin n, a i
  let E : ℝ := ∑ i : Fin n, a i * η i
  have hsum_expand : (∑ i : Fin n, a i * (1 + η i)) = S + E := by
    unfold S E
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hS_nonneg : 0 ≤ S := by
    unfold S
    exact Finset.sum_nonneg fun i _ => ha i
  by_cases hS : S = 0
  · refine ⟨0, ?_, ?_⟩
    · simpa using hγ
    · have ha_zero : ∀ i : Fin n, a i = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp hS i
          (Finset.mem_univ i)
      have hE_zero : E = 0 := by
        unfold E
        simp [ha_zero]
      rw [hsum_expand, hE_zero]
      simp [S, hS]
  · have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS)
    refine ⟨E / S, ?_, ?_⟩
    · have hE_abs : |E| ≤ γ * S := by
        calc
          |E| = |∑ i : Fin n, a i * η i| := by rfl
          _ ≤ ∑ i : Fin n, |a i * η i| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i : Fin n, a i * |η i| := by
              apply Finset.sum_congr rfl
              intro i _
              rw [abs_mul, abs_of_nonneg (ha i)]
          _ ≤ ∑ i : Fin n, a i * γ := by
              apply Finset.sum_le_sum
              intro i _
              exact mul_le_mul_of_nonneg_left (hη i) (ha i)
          _ = γ * S := by
              unfold S
              rw [← Finset.sum_mul]
              ring
      have hdiv : |E| / S ≤ γ := by
        rw [div_le_iff₀ hS_pos]
        simpa [mul_comm] using hE_abs
      rw [abs_div, abs_of_pos hS_pos]
      exact hdiv
    · rw [hsum_expand]
      field_simp [hS]
      ring

/-- Backward-error form for the computed sum of squares. -/
theorem fl_norm2Sq_backward_error (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp n) :
    ∃ η : Fin n → ℝ,
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      fl_norm2Sq fp n x = ∑ i : Fin n, x i * x i * (1 + η i) := by
  simpa [fl_norm2Sq] using dotProduct_backward_error fp n x x hn

/-- Scalar relative-error form for the computed sum of squares.

    This is the formal version of the Higham Lemma 18.1 proof step
    `fl(xᵀx) = (1 + θₙ) xᵀx`. -/
theorem fl_norm2Sq_relative_error (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp n) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp n ∧
      fl_norm2Sq fp n x =
        (∑ i : Fin n, x i * x i) * (1 + θ) := by
  obtain ⟨η, hη, hsum⟩ := fl_norm2Sq_backward_error fp n x hn
  obtain ⟨θ, hθ, hrel⟩ :=
    weighted_sum_relative_error_nonneg n
      (fun i : Fin n => x i * x i) η (gamma fp n)
      (gamma_nonneg fp hn) (fun i => mul_self_nonneg (x i)) hη
  exact ⟨θ, hθ, by rw [hsum]; exact hrel⟩

/-- The computed sum of squares is nonnegative when the dot-product error
    factors remain nonnegative.  The `2*n` validity condition is the standard
    way to obtain `gamma fp n < 1`. -/
theorem fl_norm2Sq_nonneg_of_gammaValid_two_mul (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp (2 * n)) :
    0 ≤ fl_norm2Sq fp n x := by
  have hn_small : gammaValid fp n := gammaValid_mono fp (by omega) hn
  obtain ⟨η, hη, hsum⟩ := fl_norm2Sq_backward_error fp n x hn_small
  rw [hsum]
  exact Finset.sum_nonneg fun i _ => by
    have hγ_lt : gamma fp n < 1 := gamma_lt_one fp n hn
    have hfactor : 0 ≤ 1 + η i := by
      linarith [neg_abs_le (η i), hη i, hγ_lt]
    exact mul_nonneg (mul_self_nonneg (x i)) hfactor

/-- Square-root-factor form for the floating-point 2-norm.

    This exposes the next step in Higham Lemma 18.1:
    after `fl(xᵀx) = (1+θₙ)xᵀx`, the rounded square root gives
    `fl(||x||₂) = sqrt(xᵀx) * sqrt(1+θₙ) * (1+δ)`.

    Collapsing `sqrt(1+θₙ) * (1+δ)` into one `θ_{n+1}` term is a further
    gamma/square-root inequality and is intentionally kept as the next bridge. -/
theorem fl_norm2_relative_error_sqrt_factor (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp (2 * n)) :
    ∃ (θ δ : ℝ),
      |θ| ≤ gamma fp n ∧
      |δ| ≤ fp.u ∧
      0 ≤ 1 + θ ∧
      fl_norm2 fp n x =
        (Real.sqrt (∑ i : Fin n, x i * x i) * Real.sqrt (1 + θ)) *
          (1 + δ) := by
  have hn_small : gammaValid fp n := gammaValid_mono fp (by omega) hn
  obtain ⟨θ, hθ, hsq⟩ := fl_norm2Sq_relative_error fp n x hn_small
  have hσ_nonneg : 0 ≤ fl_norm2Sq fp n x :=
    fl_norm2Sq_nonneg_of_gammaValid_two_mul fp n x hn
  obtain ⟨δ, hδ, hsqrt⟩ := fp.model_sqrt (fl_norm2Sq fp n x) hσ_nonneg
  have hS_nonneg : 0 ≤ ∑ i : Fin n, x i * x i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hγ_lt : gamma fp n < 1 := gamma_lt_one fp n hn
  have hθ_nonneg : 0 ≤ 1 + θ := by
    linarith [neg_abs_le θ, hθ, hγ_lt]
  refine ⟨θ, δ, hθ, hδ, hθ_nonneg, ?_⟩
  unfold fl_norm2
  rw [hsqrt, hsq]
  rw [Real.sqrt_mul hS_nonneg]

/-- Square-root perturbation bound used to collapse
    `sqrt(1+theta)` into one relative-error factor.

    This is an exact real-analysis lemma, not a floating-point assumption:
    for `theta ≥ 0`, `sqrt(1+theta) - 1 ≤ theta`; for `theta ≤ 0`,
    `1 - sqrt(1+theta) ≤ -theta`. -/
theorem sqrt_one_add_sub_one_abs_le_abs_of_neg_one_le {θ : ℝ} (hθ : -1 ≤ θ) :
    |Real.sqrt (1 + θ) - 1| ≤ |θ| := by
  by_cases hnonneg : 0 ≤ θ
  · have hroot_ge : 1 ≤ Real.sqrt (1 + θ) := by
      rw [Real.one_le_sqrt]
      linarith
    have hroot_le : Real.sqrt (1 + θ) ≤ 1 + θ := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith [hnonneg, sq_nonneg θ]
    rw [abs_of_nonneg (sub_nonneg.mpr hroot_ge), abs_of_nonneg hnonneg]
    linarith
  · have hnonpos : θ ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
    have harg_nonneg : 0 ≤ 1 + θ := by linarith
    have hroot_le : Real.sqrt (1 + θ) ≤ 1 := by
      rw [Real.sqrt_le_one]
      linarith
    have harg_le_root : 1 + θ ≤ Real.sqrt (1 + θ) := by
      rw [Real.le_sqrt harg_nonneg harg_nonneg]
      nlinarith [harg_nonneg, hnonpos]
    rw [abs_of_nonpos (sub_nonpos.mpr hroot_le), abs_of_nonpos hnonpos]
    linarith

/-- Collapse the square-root perturbation and the final rounded square root
    into one Higham-style relative-error factor.

    This is the local bridge from
    `sqrt(1+theta_n) * (1+delta)` to `1+theta_{n+1}`.  The stronger
    `gammaValid fp (2*n)` side condition is used only to obtain
    `gamma fp n < 1`, hence `-1 ≤ theta_n`. -/
theorem sqrt_one_add_mul_roundoff_gamma (fp : FPModel) (n : ℕ)
    (θ δ : ℝ)
    (hθ : |θ| ≤ gamma fp n) (hδ : |δ| ≤ fp.u)
    (hvalid2n : gammaValid fp (2 * n))
    (hvalidn1 : gammaValid fp (n + 1)) :
    ∃ ψ : ℝ,
      |ψ| ≤ gamma fp (n + 1) ∧
      Real.sqrt (1 + θ) * (1 + δ) = 1 + ψ := by
  let ρ : ℝ := Real.sqrt (1 + θ) - 1
  have hγ_lt : gamma fp n < 1 := gamma_lt_one fp n hvalid2n
  have hθ_lower : -1 ≤ θ := by
    linarith [neg_abs_le θ, hθ, hγ_lt]
  have hρ_bound : |ρ| ≤ gamma fp n := by
    unfold ρ
    exact le_trans (sqrt_one_add_sub_one_abs_le_abs_of_neg_one_le hθ_lower) hθ
  have hsqrt : Real.sqrt (1 + θ) = 1 + ρ := by
    unfold ρ
    ring
  have hvalid1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalidn1
  have hδγ : |δ| ≤ gamma fp 1 :=
    le_trans hδ (u_le_gamma fp one_pos hvalid1)
  obtain ⟨ψ, hψ, hprod⟩ :=
    gamma_mul fp n 1 ρ δ hρ_bound hδγ hvalidn1
  refine ⟨ψ, hψ, ?_⟩
  rw [hsqrt]
  exact hprod

/-- Collapse a square-root relative factor and another relative-error factor
    into one gamma term.

    This is the exact real/gamma bridge needed when a normalized Householder
    vector is written as `sqrt(1+theta_j) * (1+theta_k)` times the exact
    normalized vector. -/
theorem sqrt_one_add_mul_relative_gamma (fp : FPModel) (j k : ℕ)
    (θj θk : ℝ)
    (hj : |θj| ≤ gamma fp j) (hk : |θk| ≤ gamma fp k)
    (hvalid2j : gammaValid fp (2 * j))
    (hvalidjk : gammaValid fp (j + k)) :
    ∃ ψ : ℝ,
      |ψ| ≤ gamma fp (j + k) ∧
      Real.sqrt (1 + θj) * (1 + θk) = 1 + ψ := by
  let ρ : ℝ := Real.sqrt (1 + θj) - 1
  have hγ_lt : gamma fp j < 1 := gamma_lt_one fp j hvalid2j
  have hθ_lower : -1 ≤ θj := by
    linarith [neg_abs_le θj, hj, hγ_lt]
  have hρ_bound : |ρ| ≤ gamma fp j := by
    unfold ρ
    exact le_trans (sqrt_one_add_sub_one_abs_le_abs_of_neg_one_le hθ_lower) hj
  have hsqrt : Real.sqrt (1 + θj) = 1 + ρ := by
    unfold ρ
    ring
  obtain ⟨ψ, hψ, hprod⟩ :=
    gamma_mul fp j k ρ θk hρ_bound hk hvalidjk
  refine ⟨ψ, hψ, ?_⟩
  rw [hsqrt]
  exact hprod

/-- Higham-style scalar relative-error form for the floating-point 2-norm:
    `fl_norm2(x) = ||x||₂ * (1 + theta_{n+1})`.

    The theorem is proved from the concrete `fl_norm2` implementation:
    rounded dot product for `xᵀx`, followed by `FPModel.fl_sqrt`. -/
theorem fl_norm2_relative_error (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp (2 * (n + 1))) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp (n + 1) ∧
      fl_norm2 fp n x =
        Real.sqrt (∑ i : Fin n, x i * x i) * (1 + θ) := by
  have hvalid2n : gammaValid fp (2 * n) := gammaValid_mono fp (by omega) hn
  have hvalidn1 : gammaValid fp (n + 1) := gammaValid_mono fp (by omega) hn
  obtain ⟨θ, δ, hθ, hδ, _hθ_nonneg, hnorm⟩ :=
    fl_norm2_relative_error_sqrt_factor fp n x hvalid2n
  obtain ⟨ψ, hψ, hcollapse⟩ :=
    sqrt_one_add_mul_roundoff_gamma fp n θ δ hθ hδ hvalid2n hvalidn1
  refine ⟨ψ, hψ, ?_⟩
  rw [hnorm]
  rw [← hcollapse]
  ring

/-- Unrolled form for the floating-point 2-norm.

    This exposes both layers of rounding:

    * `η` comes from the dot-product/sum-of-squares computation;
    * `δ` comes from the rounded square root.

    The hypothesis `0 ≤ fl_norm2Sq fp n x` is the domain condition needed to
    apply the square-root model.  Proving it from small-error assumptions is a
    later positivity lemma, not an extra QR-specific assumption. -/
theorem fl_norm2_unroll (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp n)
    (hσ_nonneg : 0 ≤ fl_norm2Sq fp n x) :
    ∃ (η : Fin n → ℝ) (δ : ℝ),
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      |δ| ≤ fp.u ∧
      fl_norm2 fp n x =
        Real.sqrt (∑ i : Fin n, x i * x i * (1 + η i)) * (1 + δ) := by
  obtain ⟨η, hη, hsum⟩ := fl_norm2Sq_backward_error fp n x hn
  obtain ⟨δ, hδ, hsqrt⟩ := fp.model_sqrt (fl_norm2Sq fp n x) hσ_nonneg
  refine ⟨η, δ, hη, hδ, ?_⟩
  unfold fl_norm2
  rw [hsqrt, hsum]

/-- Convenience form of `fl_norm2_unroll` using the standard `2*n`
    `gammaValid` side condition to discharge square-root nonnegativity. -/
theorem fl_norm2_unroll_of_gammaValid_two_mul (fp : FPModel) (n : ℕ)
    (x : Fin n → ℝ) (hn : gammaValid fp (2 * n)) :
    ∃ (η : Fin n → ℝ) (δ : ℝ),
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      |δ| ≤ fp.u ∧
      fl_norm2 fp n x =
        Real.sqrt (∑ i : Fin n, x i * x i * (1 + η i)) * (1 + δ) := by
  exact fl_norm2_unroll fp n x (gammaValid_mono fp (by omega) hn)
    (fl_norm2Sq_nonneg_of_gammaValid_two_mul fp n x hn)

end NumStability
