-- Algorithms/RandNLA/UniformRowSamplingFP.lean
--
-- Floating-point transfer for Algorithm 3 uniform row sampling after
-- signed-Hadamard preprocessing.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.RandNLA.UniformRowSamplingComposition

namespace NumStability

open scoped BigOperators

/-!
## Floating-point uniform row sketches

The exact Algorithm 3 uniform row sketch samples row `i` and rescales it by
`1 / sqrt(s / m)`, so its Gram matrix is the uniform sample-average matrix
already analyzed in `UniformRowSamplingMGF`.  This file adds the corresponding
rounded row-scaling and rounded Gram-dot-product layer, reusing the repository's
division, row-sketch Gram, and dot-product perturbation lemmas.
-/

-- ============================================================
-- Uniform row-scaling kernels
-- ============================================================

/-- Uniform row-scaling denominator `sqrt(s / m)` for an `s`-row sketch sampled
from `m` rows. -/
noncomputable def uniformRowSampleScaleDen {m : ℕ} (s : ℕ) : ℝ :=
  Real.sqrt ((s : ℝ) * (m : ℝ)⁻¹)

/-- The uniform row-scaling denominator is nonzero when both `m` and `s` are
positive. -/
theorem uniformRowSampleScaleDen_ne_zero {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    uniformRowSampleScaleDen (m := m) s ≠ 0 := by
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmul : 0 < (s : ℝ) * (m : ℝ)⁻¹ :=
    mul_pos hs (inv_pos.mpr hmRpos)
  exact ne_of_gt (by
    unfold uniformRowSampleScaleDen
    exact Real.sqrt_pos.2 hmul)

/-- A floating-point computation of the uniform row-rescaling denominator
    `sqrt(s / m)` used after Algorithm 3 preprocessing. -/
structure ComputedUniformRowScaleDen (fp : FPModel) (m s : ℕ) where
  den : ℝ
  den_abs_error : ℝ
  den_abs_error_nonneg : 0 ≤ den_abs_error
  den_abs_error_bound :
    |den - uniformRowSampleScaleDen (m := m) s| ≤ den_abs_error
  den_ne_zero : den ≠ 0

namespace ComputedUniformRowScaleDen

variable {fp : FPModel} {m s : ℕ}

theorem abs_error_bound (dhat : ComputedUniformRowScaleDen fp m s) :
    |dhat.den - uniformRowSampleScaleDen (m := m) s| ≤ dhat.den_abs_error :=
  dhat.den_abs_error_bound

/-- Scalar square-root perturbation used by concrete denominator routines:
if `1 + delta` is nonnegative, then replacing `sqrt 1` by
`sqrt (1 + delta)` costs at most `|delta|`. -/
theorem abs_sqrt_one_add_sub_one_le_abs (delta : ℝ)
    (hpos : 0 ≤ 1 + delta) :
    |Real.sqrt (1 + delta) - 1| ≤ |delta| := by
  have hden_pos : 0 < Real.sqrt (1 + delta) + 1 := by
    nlinarith [Real.sqrt_nonneg (1 + delta)]
  have hden_ge_one : 1 ≤ Real.sqrt (1 + delta) + 1 := by
    nlinarith [Real.sqrt_nonneg (1 + delta)]
  have hden_ne : Real.sqrt (1 + delta) + 1 ≠ 0 := ne_of_gt hden_pos
  have hsqrt_sq : Real.sqrt (1 + delta) ^ 2 = 1 + delta :=
    Real.sq_sqrt hpos
  have hidentity :
      Real.sqrt (1 + delta) - 1 =
        delta / (Real.sqrt (1 + delta) + 1) := by
    field_simp [hden_ne]
    nlinarith
  rw [hidentity, abs_div]
  have hden_abs_ge_one : 1 ≤ |Real.sqrt (1 + delta) + 1| := by
    simp [abs_of_pos hden_pos, hden_ge_one]
  have hden_abs_pos : 0 < |Real.sqrt (1 + delta) + 1| :=
    lt_of_lt_of_le zero_lt_one hden_abs_ge_one
  have hmul :
      |delta| ≤ |delta| * |Real.sqrt (1 + delta) + 1| := by
    simpa using
      (mul_le_mul_of_nonneg_left hden_abs_ge_one (abs_nonneg delta))
  exact (div_le_iff₀ hden_abs_pos).2 hmul

/-- Exact uniform row-scale denominator certificate.  This is the
zero-denominator-error specialization used when the implementation supplies
`sqrt(s / m)` exactly and only the subsequent row scaling divisions are
rounded. -/
noncomputable def exact (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    ComputedUniformRowScaleDen fp m s where
  den := uniformRowSampleScaleDen (m := m) s
  den_abs_error := 0
  den_abs_error_nonneg := le_rfl
  den_abs_error_bound := by simp
  den_ne_zero := uniformRowSampleScaleDen_ne_zero hm hs

@[simp] theorem exact_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    (exact fp hm hs).den = uniformRowSampleScaleDen (m := m) s := rfl

@[simp] theorem exact_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    (exact fp hm hs).den_abs_error = 0 := rfl

/-- Concrete denominator certificate for the routine
`fl_sqrt ((s : ℝ) * (m : ℝ)⁻¹)` when the input ratio is supplied exactly.

This charges the rounded square-root primitive itself.  If an implementation
also forms `(s : ℝ) * (m : ℝ)⁻¹` in floating point, that earlier scalar
computation must instantiate a separate certificate before this constructor is
used. -/
noncomputable def flSqrtExactInput (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    ComputedUniformRowScaleDen fp m s where
  den := fp.fl_sqrt ((s : ℝ) * (m : ℝ)⁻¹)
  den_abs_error := uniformRowSampleScaleDen (m := m) s * fp.u
  den_abs_error_nonneg := by
    exact mul_nonneg (Real.sqrt_nonneg _) fp.u_nonneg
  den_abs_error_bound := by
    let x : ℝ := (s : ℝ) * (m : ℝ)⁻¹
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      exact mul_nonneg (le_of_lt hs) (inv_nonneg.mpr (le_of_lt hmRpos))
    obtain ⟨δ, hδ, hfl⟩ := fp.model_sqrt x hx_nonneg
    have hd_nonneg : 0 ≤ uniformRowSampleScaleDen (m := m) s :=
      Real.sqrt_nonneg _
    calc
      |fp.fl_sqrt x - uniformRowSampleScaleDen (m := m) s|
          = |uniformRowSampleScaleDen (m := m) s * δ| := by
              unfold uniformRowSampleScaleDen
              rw [hfl]
              dsimp [x]
              ring_nf
      _ = uniformRowSampleScaleDen (m := m) s * |δ| := by
              rw [abs_mul, abs_of_nonneg hd_nonneg]
      _ ≤ uniformRowSampleScaleDen (m := m) s * fp.u :=
              mul_le_mul_of_nonneg_left hδ hd_nonneg
  den_ne_zero := by
    let x : ℝ := (s : ℝ) * (m : ℝ)⁻¹
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      exact mul_nonneg (le_of_lt hs) (inv_nonneg.mpr (le_of_lt hmRpos))
    obtain ⟨δ, hδ, hfl⟩ := fp.model_sqrt x hx_nonneg
    have hd_ne : Real.sqrt x ≠ 0 := by
      simpa [uniformRowSampleScaleDen, x] using
        uniformRowSampleScaleDen_ne_zero hm hs
    have hδ_lower : -fp.u ≤ δ := (abs_le.mp hδ).1
    have hfactor_pos : 0 < 1 + δ := by linarith
    rw [hfl]
    exact mul_ne_zero hd_ne (ne_of_gt hfactor_pos)

@[simp] theorem flSqrtExactInput_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtExactInput fp hm hs hu).den =
      fp.fl_sqrt ((s : ℝ) * (m : ℝ)⁻¹) := rfl

@[simp] theorem flSqrtExactInput_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtExactInput fp hm hs hu).den_abs_error =
      uniformRowSampleScaleDen (m := m) s * fp.u := rfl

/-- Concrete denominator certificate for the routine
`fl_sqrt (fl_div (s : R) (m : R))`.

The sampling law is still the exact uniform law.  This constructor charges the
rounded scalar ratio `s/m` and the rounded square-root primitive used to form
the non-probability scale denominator. -/
noncomputable def flDivThenSqrt (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    ComputedUniformRowScaleDen fp m s where
  den := fp.fl_sqrt (fp.fl_div (s : ℝ) (m : ℝ))
  den_abs_error :=
    uniformRowSampleScaleDen (m := m) s *
      (Real.sqrt (1 + fp.u) * fp.u + fp.u)
  den_abs_error_nonneg := by
    have hsqrt_nonneg :
        0 ≤ Real.sqrt (1 + fp.u) * fp.u + fp.u := by
      exact add_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) fp.u_nonneg) fp.u_nonneg
    exact mul_nonneg (Real.sqrt_nonneg _) hsqrt_nonneg
  den_abs_error_bound := by
    let x : ℝ := (s : ℝ) / (m : ℝ)
    let xhat : ℝ := fp.fl_div (s : ℝ) (m : ℝ)
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmR_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
    have hx_pos : 0 < x := by
      dsimp [x]
      exact div_pos hs hmRpos
    obtain ⟨δr, hδr, hdiv⟩ := fp.model_div (s : ℝ) (m : ℝ) hmR_ne
    have hxhat_eq : xhat = x * (1 + δr) := by
      dsimp [xhat, x]
      simpa using hdiv
    have hδr_lower : -fp.u ≤ δr := (abs_le.mp hδr).1
    have hδr_upper : δr ≤ fp.u := (abs_le.mp hδr).2
    have hfactor_pos : 0 < 1 + δr := by linarith
    have hfactor_nonneg : 0 ≤ 1 + δr := le_of_lt hfactor_pos
    have hxhat_pos : 0 < xhat := by
      rw [hxhat_eq]
      exact mul_pos hx_pos hfactor_pos
    obtain ⟨δs, hδs, hsqrt⟩ :=
      fp.model_sqrt xhat (le_of_lt hxhat_pos)
    let d : ℝ := Real.sqrt x
    let a : ℝ := Real.sqrt (1 + δr)
    have hd_nonneg : 0 ≤ d := Real.sqrt_nonneg _
    have ha_nonneg : 0 ≤ a := Real.sqrt_nonneg _
    have h1u_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have ha_le : a ≤ Real.sqrt (1 + fp.u) := by
      dsimp [a]
      exact Real.sqrt_le_sqrt (by linarith)
    have hsqrt_ratio : |a - 1| ≤ fp.u := by
      exact
        (abs_sqrt_one_add_sub_one_le_abs δr hfactor_nonneg).trans hδr
    have hscalar :
        |a * (1 + δs) - 1| ≤
          Real.sqrt (1 + fp.u) * fp.u + fp.u := by
      have hsplit : a * (1 + δs) - 1 = a * δs + (a - 1) := by ring
      calc
        |a * (1 + δs) - 1|
            = |a * δs + (a - 1)| := by rw [hsplit]
        _ ≤ |a * δs| + |a - 1| := abs_add_le _ _
        _ = a * |δs| + |a - 1| := by
              rw [abs_mul, abs_of_nonneg ha_nonneg]
        _ ≤ a * fp.u + fp.u := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hδs ha_nonneg)
                hsqrt_ratio
        _ ≤ Real.sqrt (1 + fp.u) * fp.u + fp.u := by
              have h :=
                add_le_add_right
                  (mul_le_mul_of_nonneg_right ha_le fp.u_nonneg) fp.u
              linarith
    have hsqrt_xhat :
        Real.sqrt xhat = d * a := by
      rw [hxhat_eq]
      dsimp [d, a]
      rw [Real.sqrt_mul (le_of_lt hx_pos) (1 + δr)]
    have hmain :
        |Real.sqrt xhat * (1 + δs) - d| ≤
          d * (Real.sqrt (1 + fp.u) * fp.u + fp.u) := by
      rw [hsqrt_xhat]
      have hsplit : d * a * (1 + δs) - d =
          d * (a * (1 + δs) - 1) := by ring
      calc
        |d * a * (1 + δs) - d|
            = |d * (a * (1 + δs) - 1)| := by rw [hsplit]
        _ = d * |a * (1 + δs) - 1| := by
              rw [abs_mul, abs_of_nonneg hd_nonneg]
        _ ≤ d * (Real.sqrt (1 + fp.u) * fp.u + fp.u) :=
              mul_le_mul_of_nonneg_left hscalar hd_nonneg
    have htarget :
        |fp.fl_sqrt xhat - d| ≤
          d * (Real.sqrt (1 + fp.u) * fp.u + fp.u) := by
      rw [hsqrt]
      exact hmain
    simpa [xhat, x, d, uniformRowSampleScaleDen, div_eq_mul_inv]
      using htarget
  den_ne_zero := by
    let x : ℝ := (s : ℝ) / (m : ℝ)
    let xhat : ℝ := fp.fl_div (s : ℝ) (m : ℝ)
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmR_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
    have hx_pos : 0 < x := by
      dsimp [x]
      exact div_pos hs hmRpos
    obtain ⟨δr, hδr, hdiv⟩ := fp.model_div (s : ℝ) (m : ℝ) hmR_ne
    have hxhat_eq : xhat = x * (1 + δr) := by
      dsimp [xhat, x]
      simpa using hdiv
    have hδr_lower : -fp.u ≤ δr := (abs_le.mp hδr).1
    have hfactor_pos : 0 < 1 + δr := by linarith
    have hxhat_pos : 0 < xhat := by
      rw [hxhat_eq]
      exact mul_pos hx_pos hfactor_pos
    obtain ⟨δs, hδs, hsqrt⟩ :=
      fp.model_sqrt xhat (le_of_lt hxhat_pos)
    have hsqrt_ne : Real.sqrt xhat ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hxhat_pos)
    have hδs_lower : -fp.u ≤ δs := (abs_le.mp hδs).1
    have hfactor_s_pos : 0 < 1 + δs := by linarith
    rw [hsqrt]
    exact mul_ne_zero hsqrt_ne (ne_of_gt hfactor_s_pos)

@[simp] theorem flDivThenSqrt_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flDivThenSqrt fp hm hs hu).den =
      fp.fl_sqrt (fp.fl_div (s : ℝ) (m : ℝ)) := rfl

@[simp] theorem flDivThenSqrt_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flDivThenSqrt fp hm hs hu).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        (Real.sqrt (1 + fp.u) * fp.u + fp.u) := rfl

/-- Concrete denominator certificate for the routine
`fl_sqrt (fl_mul (s : R) (fl_div 1 (m : R)))`.

This is a second non-probability scale-denominator implementation for the
Algorithm 3 uniform row sketch: it forms a rounded reciprocal of `m`, multiplies
by `s`, and finally takes a rounded square root.  The uniform sampling law is
still exact; this constructor only charges the scalar arithmetic used to build
the row-rescaling denominator. -/
noncomputable def flInvMulThenSqrt (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    ComputedUniformRowScaleDen fp m s where
  den := fp.fl_sqrt (fp.fl_mul (s : ℝ) (fp.fl_div 1 (m : ℝ)))
  den_abs_error :=
    uniformRowSampleScaleDen (m := m) s *
      (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
        (2 * fp.u + fp.u ^ 2))
  den_abs_error_nonneg := by
    have htail : 0 ≤
        Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
          (2 * fp.u + fp.u ^ 2) := by
      exact add_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) fp.u_nonneg)
        (by nlinarith [fp.u_nonneg])
    exact mul_nonneg (Real.sqrt_nonneg _) htail
  den_abs_error_bound := by
    let x : ℝ := (s : ℝ) * (m : ℝ)⁻¹
    let invhat : ℝ := fp.fl_div 1 (m : ℝ)
    let xhat : ℝ := fp.fl_mul (s : ℝ) invhat
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmR_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
    have hx_pos : 0 < x := by
      dsimp [x]
      exact mul_pos hs (inv_pos.mpr hmRpos)
    obtain ⟨δi, hδi, hdiv⟩ := fp.model_div 1 (m : ℝ) hmR_ne
    have hinvhat_eq : invhat = ((m : ℝ)⁻¹) * (1 + δi) := by
      dsimp [invhat]
      simpa [one_div] using hdiv
    obtain ⟨δm, hδm, hmul⟩ := fp.model_mul (s : ℝ) invhat
    let f : ℝ := (1 + δi) * (1 + δm)
    have hxhat_eq : xhat = x * f := by
      dsimp [xhat]
      rw [hmul, hinvhat_eq]
      dsimp [x, f]
      ring
    have hδi_lower : -fp.u ≤ δi := (abs_le.mp hδi).1
    have hδi_upper : δi ≤ fp.u := (abs_le.mp hδi).2
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hδm_upper : δm ≤ fp.u := (abs_le.mp hδm).2
    have hi_pos : 0 < 1 + δi := by linarith
    have hm_pos : 0 < 1 + δm := by linarith
    have hf_pos : 0 < f := by
      dsimp [f]
      exact mul_pos hi_pos hm_pos
    have hf_nonneg : 0 ≤ f := le_of_lt hf_pos
    have hxhat_pos : 0 < xhat := by
      rw [hxhat_eq]
      exact mul_pos hx_pos hf_pos
    obtain ⟨δs, hδs, hsqrt⟩ :=
      fp.model_sqrt xhat (le_of_lt hxhat_pos)
    let d : ℝ := Real.sqrt x
    let a : ℝ := Real.sqrt f
    have hd_nonneg : 0 ≤ d := Real.sqrt_nonneg _
    have ha_nonneg : 0 ≤ a := Real.sqrt_nonneg _
    have h1u_nonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have hf_upper : f ≤ (1 + fp.u) * (1 + fp.u) := by
      dsimp [f]
      have hi_le : 1 + δi ≤ 1 + fp.u := by linarith
      have hm_le : 1 + δm ≤ 1 + fp.u := by linarith
      exact mul_le_mul hi_le hm_le (le_of_lt hm_pos) h1u_nonneg
    have ha_le : a ≤ Real.sqrt ((1 + fp.u) * (1 + fp.u)) := by
      dsimp [a]
      exact Real.sqrt_le_sqrt hf_upper
    have hf_abs :
        |f - 1| ≤ 2 * fp.u + fp.u ^ 2 := by
      have hf_expand : f - 1 = δi + δm + δi * δm := by
        dsimp [f]
        ring
      calc
        |f - 1| = |δi + δm + δi * δm| := by rw [hf_expand]
        _ ≤ |δi + δm| + |δi * δm| := abs_add_le _ _
        _ ≤ (|δi| + |δm|) + |δi * δm| := by
              simpa [add_assoc, add_comm, add_left_comm] using
                add_le_add_right (abs_add_le δi δm) |δi * δm|
        _ = |δi| + |δm| + |δi| * |δm| := by
              rw [abs_mul]
        _ ≤ fp.u + fp.u + fp.u * fp.u := by
              have hprod : |δi| * |δm| ≤ fp.u * fp.u :=
                mul_le_mul hδi hδm (abs_nonneg δm) fp.u_nonneg
              nlinarith
        _ = 2 * fp.u + fp.u ^ 2 := by ring
    have hsqrt_ratio : |a - 1| ≤ 2 * fp.u + fp.u ^ 2 := by
      have hone : 1 + (f - 1) = f := by ring
      have hpos : 0 ≤ 1 + (f - 1) := by
        simpa [hone] using hf_nonneg
      have h :=
        abs_sqrt_one_add_sub_one_le_abs (f - 1) hpos
      simpa [a, hone] using h.trans hf_abs
    have hscalar :
        |a * (1 + δs) - 1| ≤
          Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
            (2 * fp.u + fp.u ^ 2) := by
      have hsplit : a * (1 + δs) - 1 = a * δs + (a - 1) := by ring
      calc
        |a * (1 + δs) - 1|
            = |a * δs + (a - 1)| := by rw [hsplit]
        _ ≤ |a * δs| + |a - 1| := abs_add_le _ _
        _ = a * |δs| + |a - 1| := by
              rw [abs_mul, abs_of_nonneg ha_nonneg]
        _ ≤ a * fp.u + (2 * fp.u + fp.u ^ 2) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hδs ha_nonneg)
                hsqrt_ratio
        _ ≤ Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
              (2 * fp.u + fp.u ^ 2) := by
              simpa [add_assoc, add_comm, add_left_comm] using
                add_le_add_right
                (mul_le_mul_of_nonneg_right ha_le fp.u_nonneg)
                (2 * fp.u + fp.u ^ 2)
    have hsqrt_xhat : Real.sqrt xhat = d * a := by
      rw [hxhat_eq]
      dsimp [d, a]
      rw [Real.sqrt_mul (le_of_lt hx_pos) f]
    have hmain :
        |Real.sqrt xhat * (1 + δs) - d| ≤
          d * (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
            (2 * fp.u + fp.u ^ 2)) := by
      rw [hsqrt_xhat]
      have hsplit : d * a * (1 + δs) - d =
          d * (a * (1 + δs) - 1) := by ring
      calc
        |d * a * (1 + δs) - d|
            = |d * (a * (1 + δs) - 1)| := by rw [hsplit]
        _ = d * |a * (1 + δs) - 1| := by
              rw [abs_mul, abs_of_nonneg hd_nonneg]
        _ ≤ d * (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
            (2 * fp.u + fp.u ^ 2)) :=
              mul_le_mul_of_nonneg_left hscalar hd_nonneg
    have htarget :
        |fp.fl_sqrt xhat - d| ≤
          d * (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
            (2 * fp.u + fp.u ^ 2)) := by
      rw [hsqrt]
      exact hmain
    simpa [xhat, x, d, uniformRowSampleScaleDen]
      using htarget
  den_ne_zero := by
    let x : ℝ := (s : ℝ) * (m : ℝ)⁻¹
    let invhat : ℝ := fp.fl_div 1 (m : ℝ)
    let xhat : ℝ := fp.fl_mul (s : ℝ) invhat
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmR_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
    have hx_pos : 0 < x := by
      dsimp [x]
      exact mul_pos hs (inv_pos.mpr hmRpos)
    obtain ⟨δi, hδi, hdiv⟩ := fp.model_div 1 (m : ℝ) hmR_ne
    have hinvhat_eq : invhat = ((m : ℝ)⁻¹) * (1 + δi) := by
      dsimp [invhat]
      simpa [one_div] using hdiv
    obtain ⟨δm, hδm, hmul⟩ := fp.model_mul (s : ℝ) invhat
    let f : ℝ := (1 + δi) * (1 + δm)
    have hxhat_eq : xhat = x * f := by
      dsimp [xhat]
      rw [hmul, hinvhat_eq]
      dsimp [x, f]
      ring
    have hδi_lower : -fp.u ≤ δi := (abs_le.mp hδi).1
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hi_pos : 0 < 1 + δi := by linarith
    have hm_pos : 0 < 1 + δm := by linarith
    have hf_pos : 0 < f := by
      dsimp [f]
      exact mul_pos hi_pos hm_pos
    have hxhat_pos : 0 < xhat := by
      rw [hxhat_eq]
      exact mul_pos hx_pos hf_pos
    obtain ⟨δs, hδs, hsqrt⟩ :=
      fp.model_sqrt xhat (le_of_lt hxhat_pos)
    have hsqrt_ne : Real.sqrt xhat ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hxhat_pos)
    have hδs_lower : -fp.u ≤ δs := (abs_le.mp hδs).1
    have hfactor_s_pos : 0 < 1 + δs := by linarith
    rw [hsqrt]
    exact mul_ne_zero hsqrt_ne (ne_of_gt hfactor_s_pos)

@[simp] theorem flInvMulThenSqrt_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flInvMulThenSqrt fp hm hs hu).den =
      fp.fl_sqrt (fp.fl_mul (s : ℝ) (fp.fl_div 1 (m : ℝ))) := rfl

@[simp] theorem flInvMulThenSqrt_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flInvMulThenSqrt fp hm hs hu).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
          (2 * fp.u + fp.u ^ 2)) := rfl

/-- Concrete denominator certificate for the routine
`fl_div (fl_sqrt (s : R)) (fl_sqrt (m : R))`.

This covers an implementation that forms the two square roots separately and
then divides them.  The uniform sampling law remains exact; the only charged
operations are the two rounded square roots and the rounded scalar division
used to compute the non-probability row-rescaling denominator. -/
noncomputable def flSqrtDivSqrt (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    ComputedUniformRowScaleDen fp m s where
  den := fp.fl_div (fp.fl_sqrt (s : ℝ)) (fp.fl_sqrt (m : ℝ))
  den_abs_error :=
    uniformRowSampleScaleDen (m := m) s *
      ((3 * fp.u + fp.u ^ 2) / (1 - fp.u))
  den_abs_error_nonneg := by
    have hnum : 0 ≤ 3 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg]
    have hden : 0 ≤ 1 - fp.u := le_of_lt (sub_pos.mpr hu)
    exact mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hnum hden)
  den_abs_error_bound := by
    let sR : ℝ := (s : ℝ)
    let mR : ℝ := (m : ℝ)
    let shat : ℝ := fp.fl_sqrt sR
    let mhat : ℝ := fp.fl_sqrt mR
    let sqrtS : ℝ := Real.sqrt sR
    let sqrtM : ℝ := Real.sqrt mR
    let d : ℝ := uniformRowSampleScaleDen (m := m) s
    have hmRpos : 0 < mR := by
      dsimp [mR]
      exact_mod_cast hm
    have hsRpos : 0 < sR := by
      dsimp [sR]
      exact hs
    have hsR_nonneg : 0 ≤ sR := le_of_lt hsRpos
    have hmR_nonneg : 0 ≤ mR := le_of_lt hmRpos
    obtain ⟨δs, hδs, hsqrt_s⟩ := fp.model_sqrt sR hsR_nonneg
    obtain ⟨δm, hδm, hsqrt_m⟩ := fp.model_sqrt mR hmR_nonneg
    have hsqrtM_ne : sqrtM ≠ 0 := by
      dsimp [sqrtM]
      exact ne_of_gt (Real.sqrt_pos.2 hmRpos)
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hδm_upper : δm ≤ fp.u := (abs_le.mp hδm).2
    have hfactor_m_pos : 0 < 1 + δm := by linarith
    have hfactor_m_ne : 1 + δm ≠ 0 := ne_of_gt hfactor_m_pos
    have hmhat_ne : mhat ≠ 0 := by
      dsimp [mhat]
      rw [hsqrt_m]
      exact mul_ne_zero hsqrtM_ne (ne_of_gt hfactor_m_pos)
    obtain ⟨δd, hδd, hdiv⟩ := fp.model_div shat mhat hmhat_ne
    let g : ℝ := ((1 + δs) / (1 + δm)) * (1 + δd)
    have hd_eq : d = sqrtS / sqrtM := by
      dsimp [d, uniformRowSampleScaleDen, sqrtS, sqrtM, sR, mR]
      rw [show (s : ℝ) * (m : ℝ)⁻¹ = (s : ℝ) / (m : ℝ) by ring]
      rw [Real.sqrt_div (le_of_lt hs) (m : ℝ)]
    have hden_eq :
        fp.fl_div shat mhat = d * g := by
      rw [hdiv]
      dsimp [shat, mhat]
      rw [hsqrt_s, hsqrt_m, hd_eq]
      dsimp [sqrtS, sqrtM, g]
      field_simp [hsqrtM_ne, hfactor_m_ne]
    have hδs_upper : δs ≤ fp.u := (abs_le.mp hδs).2
    have hδd_upper : δd ≤ fp.u := (abs_le.mp hδd).2
    have hnum_bound :
        |(1 + δs) * (1 + δd) - (1 + δm)| ≤
          3 * fp.u + fp.u ^ 2 := by
      have hexpand :
          (1 + δs) * (1 + δd) - (1 + δm) =
            δs + δd + δs * δd - δm := by ring
      have htri :
          |δs + δd + δs * δd - δm| ≤
            |δs| + |δd| + |δs * δd| + |δm| := by
        have htri₁ :
            |δs + δd + δs * δd| ≤
              |δs + δd| + |δs * δd| :=
          abs_add_le (δs + δd) (δs * δd)
        have htri₂ : |δs + δd| ≤ |δs| + |δd| :=
          abs_add_le δs δd
        calc
          |δs + δd + δs * δd - δm|
              = |(δs + δd + δs * δd) + (-δm)| := by ring_nf
          _ ≤ |δs + δd + δs * δd| + |-δm| :=
              abs_add_le _ _
          _ ≤ (|δs + δd| + |δs * δd|) + |-δm| :=
              by linarith
          _ ≤ ((|δs| + |δd|) + |δs * δd|) + |-δm| :=
              by linarith
          _ = |δs| + |δd| + |δs * δd| + |δm| := by
              simp [abs_neg, add_assoc]
      have hprod : |δs * δd| ≤ fp.u * fp.u := by
        rw [abs_mul]
        exact mul_le_mul hδs hδd (abs_nonneg δd) fp.u_nonneg
      calc
        |(1 + δs) * (1 + δd) - (1 + δm)|
            = |δs + δd + δs * δd - δm| := by rw [hexpand]
        _ ≤ |δs| + |δd| + |δs * δd| + |δm| := htri
        _ ≤ fp.u + fp.u + fp.u * fp.u + fp.u := by
              nlinarith [hδs, hδd, hδm, hprod]
        _ = 3 * fp.u + fp.u ^ 2 := by ring
    have hnum_nonneg : 0 ≤ 3 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg]
    have hden_pos : 0 < 1 - fp.u := sub_pos.mpr hu
    have hden_abs_lower : 1 - fp.u ≤ |1 + δm| := by
      rw [abs_of_pos hfactor_m_pos]
      linarith
    have hg_bound :
        |g - 1| ≤ (3 * fp.u + fp.u ^ 2) / (1 - fp.u) := by
      have hg_identity :
          g - 1 =
            ((1 + δs) * (1 + δd) - (1 + δm)) / (1 + δm) := by
        dsimp [g]
        field_simp [hfactor_m_ne]
      calc
        |g - 1|
            = |((1 + δs) * (1 + δd) - (1 + δm)) / (1 + δm)| := by
                rw [hg_identity]
        _ = |(1 + δs) * (1 + δd) - (1 + δm)| / |1 + δm| :=
            abs_div _ _
        _ ≤ (3 * fp.u + fp.u ^ 2) / |1 + δm| :=
            div_le_div_of_nonneg_right hnum_bound (abs_nonneg _)
        _ ≤ (3 * fp.u + fp.u ^ 2) / (1 - fp.u) :=
            div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_abs_lower
    have hd_nonneg : 0 ≤ d := by
      dsimp [d, uniformRowSampleScaleDen]
      exact Real.sqrt_nonneg _
    have htarget :
        |fp.fl_div shat mhat - d| ≤
          d * ((3 * fp.u + fp.u ^ 2) / (1 - fp.u)) := by
      rw [hden_eq]
      have hsplit : d * g - d = d * (g - 1) := by ring
      calc
        |d * g - d|
            = |d * (g - 1)| := by rw [hsplit]
        _ = d * |g - 1| := by
              rw [abs_mul, abs_of_nonneg hd_nonneg]
        _ ≤ d * ((3 * fp.u + fp.u ^ 2) / (1 - fp.u)) :=
              mul_le_mul_of_nonneg_left hg_bound hd_nonneg
    simpa [shat, mhat, d]
      using htarget
  den_ne_zero := by
    let sR : ℝ := (s : ℝ)
    let mR : ℝ := (m : ℝ)
    let shat : ℝ := fp.fl_sqrt sR
    let mhat : ℝ := fp.fl_sqrt mR
    have hmRpos : 0 < mR := by
      dsimp [mR]
      exact_mod_cast hm
    have hsRpos : 0 < sR := by
      dsimp [sR]
      exact hs
    obtain ⟨δs, hδs, hsqrt_s⟩ := fp.model_sqrt sR (le_of_lt hsRpos)
    obtain ⟨δm, hδm, hsqrt_m⟩ := fp.model_sqrt mR (le_of_lt hmRpos)
    have hsqrtS_ne : Real.sqrt sR ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hsRpos)
    have hsqrtM_ne : Real.sqrt mR ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hmRpos)
    have hδs_lower : -fp.u ≤ δs := (abs_le.mp hδs).1
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hfactor_s_pos : 0 < 1 + δs := by linarith
    have hfactor_m_pos : 0 < 1 + δm := by linarith
    have hshat_ne : shat ≠ 0 := by
      dsimp [shat]
      rw [hsqrt_s]
      exact mul_ne_zero hsqrtS_ne (ne_of_gt hfactor_s_pos)
    have hmhat_ne : mhat ≠ 0 := by
      dsimp [mhat]
      rw [hsqrt_m]
      exact mul_ne_zero hsqrtM_ne (ne_of_gt hfactor_m_pos)
    obtain ⟨δd, hδd, hdiv⟩ := fp.model_div shat mhat hmhat_ne
    have hratio_ne : shat / mhat ≠ 0 := div_ne_zero hshat_ne hmhat_ne
    have hδd_lower : -fp.u ≤ δd := (abs_le.mp hδd).1
    have hfactor_d_pos : 0 < 1 + δd := by linarith
    rw [hdiv]
    exact mul_ne_zero hratio_ne (ne_of_gt hfactor_d_pos)

@[simp] theorem flSqrtDivSqrt_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtDivSqrt fp hm hs hu).den =
      fp.fl_div (fp.fl_sqrt (s : ℝ)) (fp.fl_sqrt (m : ℝ)) := rfl

@[simp] theorem flSqrtDivSqrt_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtDivSqrt fp hm hs hu).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        ((3 * fp.u + fp.u ^ 2) / (1 - fp.u)) := rfl

/-- Concrete denominator certificate for the routine
`fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (m : R)))`.

This covers the common implementation pattern "form `sqrt(s)`, form
`sqrt(m)`, compute a rounded reciprocal of the latter, and multiply."  The
uniform sampling law remains exact; this constructor charges only the scalar
arithmetic used to compute the non-probability row-rescaling denominator. -/
noncomputable def flSqrtMulInvSqrt (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    ComputedUniformRowScaleDen fp m s where
  den :=
    fp.fl_mul (fp.fl_sqrt (s : ℝ))
      (fp.fl_div 1 (fp.fl_sqrt (m : ℝ)))
  den_abs_error :=
    uniformRowSampleScaleDen (m := m) s *
      ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u))
  den_abs_error_nonneg := by
    have hnum : 0 ≤ 4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3 := by
      nlinarith [fp.u_nonneg]
    have hden : 0 ≤ 1 - fp.u := le_of_lt (sub_pos.mpr hu)
    exact mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hnum hden)
  den_abs_error_bound := by
    let sR : ℝ := (s : ℝ)
    let mR : ℝ := (m : ℝ)
    let shat : ℝ := fp.fl_sqrt sR
    let mhat : ℝ := fp.fl_sqrt mR
    let invMhat : ℝ := fp.fl_div 1 mhat
    let sqrtS : ℝ := Real.sqrt sR
    let sqrtM : ℝ := Real.sqrt mR
    let d : ℝ := uniformRowSampleScaleDen (m := m) s
    have hmRpos : 0 < mR := by
      dsimp [mR]
      exact_mod_cast hm
    have hsRpos : 0 < sR := by
      dsimp [sR]
      exact hs
    have hsR_nonneg : 0 ≤ sR := le_of_lt hsRpos
    have hmR_nonneg : 0 ≤ mR := le_of_lt hmRpos
    obtain ⟨δs, hδs, hsqrt_s⟩ := fp.model_sqrt sR hsR_nonneg
    obtain ⟨δm, hδm, hsqrt_m⟩ := fp.model_sqrt mR hmR_nonneg
    have hsqrtM_ne : sqrtM ≠ 0 := by
      dsimp [sqrtM]
      exact ne_of_gt (Real.sqrt_pos.2 hmRpos)
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hδm_upper : δm ≤ fp.u := (abs_le.mp hδm).2
    have hfactor_m_pos : 0 < 1 + δm := by linarith
    have hfactor_m_ne : 1 + δm ≠ 0 := ne_of_gt hfactor_m_pos
    have hmhat_ne : mhat ≠ 0 := by
      dsimp [mhat]
      rw [hsqrt_m]
      exact mul_ne_zero hsqrtM_ne (ne_of_gt hfactor_m_pos)
    obtain ⟨δi, hδi, hdiv⟩ := fp.model_div 1 mhat hmhat_ne
    obtain ⟨δp, hδp, hmul⟩ := fp.model_mul shat invMhat
    let g : ℝ := ((1 + δs) * (1 + δi) * (1 + δp)) / (1 + δm)
    have hd_eq : d = sqrtS / sqrtM := by
      dsimp [d, uniformRowSampleScaleDen, sqrtS, sqrtM, sR, mR]
      rw [show (s : ℝ) * (m : ℝ)⁻¹ = (s : ℝ) / (m : ℝ) by ring]
      rw [Real.sqrt_div (le_of_lt hs) (m : ℝ)]
    have hden_eq :
        fp.fl_mul shat invMhat = d * g := by
      rw [hmul]
      dsimp [shat, invMhat]
      rw [hdiv, hsqrt_s]
      dsimp [mhat]
      rw [hsqrt_m, hd_eq]
      dsimp [sqrtS, sqrtM, g]
      field_simp [hsqrtM_ne, hfactor_m_ne]
    have hprod_abs :
        |δs * δi| ≤ fp.u * fp.u := by
      rw [abs_mul]
      exact mul_le_mul hδs hδi (abs_nonneg _) fp.u_nonneg
    have hprod_sp_abs :
        |δs * δp| ≤ fp.u * fp.u := by
      rw [abs_mul]
      exact mul_le_mul hδs hδp (abs_nonneg _) fp.u_nonneg
    have hprod_ip_abs :
        |δi * δp| ≤ fp.u * fp.u := by
      rw [abs_mul]
      exact mul_le_mul hδi hδp (abs_nonneg _) fp.u_nonneg
    have hprod3_abs :
        |δs * δi * δp| ≤ fp.u * fp.u * fp.u := by
      rw [abs_mul, abs_mul]
      have hprod_si : |δs| * |δi| ≤ fp.u * fp.u :=
        mul_le_mul hδs hδi (abs_nonneg _) fp.u_nonneg
      exact mul_le_mul hprod_si hδp (abs_nonneg _)
        (mul_nonneg fp.u_nonneg fp.u_nonneg)
    have htri :
        |δs + δi + δp + δs * δi + δs * δp + δi * δp +
            δs * δi * δp - δm| ≤
          |δs| + |δi| + |δp| + |δs * δi| + |δs * δp| +
            |δi * δp| + |δs * δi * δp| + |δm| := by
      have h0 :
          |δs + δi + δp + δs * δi + δs * δp + δi * δp +
              δs * δi * δp - δm| ≤
            |δs + δi + δp + δs * δi + δs * δp + δi * δp +
                δs * δi * δp| + |δm| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le
            (δs + δi + δp + δs * δi + δs * δp + δi * δp +
              δs * δi * δp) (-δm)
      have h1 :
          |δs + δi + δp + δs * δi + δs * δp + δi * δp +
              δs * δi * δp| ≤
            |δs + δi + δp + δs * δi + δs * δp + δi * δp| +
              |δs * δi * δp| := by
        simpa [add_assoc] using
          abs_add_le
            (δs + δi + δp + δs * δi + δs * δp + δi * δp)
            (δs * δi * δp)
      have h2 :
          |δs + δi + δp + δs * δi + δs * δp + δi * δp| ≤
            |δs + δi + δp + δs * δi + δs * δp| + |δi * δp| := by
        simpa [add_assoc] using
          abs_add_le
            (δs + δi + δp + δs * δi + δs * δp) (δi * δp)
      have h3 :
          |δs + δi + δp + δs * δi + δs * δp| ≤
            |δs + δi + δp + δs * δi| + |δs * δp| := by
        simpa [add_assoc] using
          abs_add_le (δs + δi + δp + δs * δi) (δs * δp)
      have h4 :
          |δs + δi + δp + δs * δi| ≤
            |δs + δi + δp| + |δs * δi| := by
        simpa [add_assoc] using abs_add_le (δs + δi + δp) (δs * δi)
      have h5 : |δs + δi + δp| ≤ |δs + δi| + |δp| := by
        simpa [add_assoc] using abs_add_le (δs + δi) δp
      have h6 : |δs + δi| ≤ |δs| + |δi| :=
        abs_add_le δs δi
      linarith
    have hnum_bound :
        |(1 + δs) * (1 + δi) * (1 + δp) - (1 + δm)| ≤
          4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3 := by
      have hexpand :
          (1 + δs) * (1 + δi) * (1 + δp) - (1 + δm) =
            δs + δi + δp + δs * δi + δs * δp + δi * δp +
              δs * δi * δp - δm := by
        ring
      calc
        |(1 + δs) * (1 + δi) * (1 + δp) - (1 + δm)|
            =
          |δs + δi + δp + δs * δi + δs * δp + δi * δp +
              δs * δi * δp - δm| := by rw [hexpand]
        _ ≤ |δs| + |δi| + |δp| + |δs * δi| + |δs * δp| +
              |δi * δp| + |δs * δi * δp| + |δm| := htri
        _ ≤ 4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3 := by
              nlinarith [hδs, hδi, hδp, hδm, hprod_abs,
                hprod_sp_abs, hprod_ip_abs, hprod3_abs]
    have hnum_nonneg : 0 ≤ 4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3 := by
      nlinarith [fp.u_nonneg]
    have hden_pos : 0 < 1 - fp.u := sub_pos.mpr hu
    have hden_abs_lower : 1 - fp.u ≤ |1 + δm| := by
      rw [abs_of_pos hfactor_m_pos]
      linarith
    have hg_bound :
        |g - 1| ≤
          (4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u) := by
      have hg_identity :
          g - 1 =
            ((1 + δs) * (1 + δi) * (1 + δp) - (1 + δm)) /
              (1 + δm) := by
        dsimp [g]
        field_simp [hfactor_m_ne]
      calc
        |g - 1|
            = |((1 + δs) * (1 + δi) * (1 + δp) - (1 + δm)) /
                (1 + δm)| := by rw [hg_identity]
        _ =
            |(1 + δs) * (1 + δi) * (1 + δp) - (1 + δm)| /
              |1 + δm| := abs_div _ _
        _ ≤ (4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / |1 + δm| :=
            div_le_div_of_nonneg_right hnum_bound (abs_nonneg _)
        _ ≤ (4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u) :=
            div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_abs_lower
    have hd_nonneg : 0 ≤ d := by
      dsimp [d, uniformRowSampleScaleDen]
      exact Real.sqrt_nonneg _
    have htarget :
        |fp.fl_mul shat invMhat - d| ≤
          d * ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u)) := by
      rw [hden_eq]
      have hsplit : d * g - d = d * (g - 1) := by ring
      calc
        |d * g - d|
            = |d * (g - 1)| := by rw [hsplit]
        _ = d * |g - 1| := by
              rw [abs_mul, abs_of_nonneg hd_nonneg]
        _ ≤ d * ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) /
              (1 - fp.u)) :=
              mul_le_mul_of_nonneg_left hg_bound hd_nonneg
    simpa [shat, invMhat, d]
      using htarget
  den_ne_zero := by
    let sR : ℝ := (s : ℝ)
    let mR : ℝ := (m : ℝ)
    let shat : ℝ := fp.fl_sqrt sR
    let mhat : ℝ := fp.fl_sqrt mR
    let invMhat : ℝ := fp.fl_div 1 mhat
    have hmRpos : 0 < mR := by
      dsimp [mR]
      exact_mod_cast hm
    have hsRpos : 0 < sR := by
      dsimp [sR]
      exact hs
    obtain ⟨δs, hδs, hsqrt_s⟩ := fp.model_sqrt sR (le_of_lt hsRpos)
    obtain ⟨δm, hδm, hsqrt_m⟩ := fp.model_sqrt mR (le_of_lt hmRpos)
    have hsqrtS_ne : Real.sqrt sR ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hsRpos)
    have hsqrtM_ne : Real.sqrt mR ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hmRpos)
    have hδs_lower : -fp.u ≤ δs := (abs_le.mp hδs).1
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hfactor_s_pos : 0 < 1 + δs := by linarith
    have hfactor_m_pos : 0 < 1 + δm := by linarith
    have hshat_ne : shat ≠ 0 := by
      dsimp [shat]
      rw [hsqrt_s]
      exact mul_ne_zero hsqrtS_ne (ne_of_gt hfactor_s_pos)
    have hmhat_ne : mhat ≠ 0 := by
      dsimp [mhat]
      rw [hsqrt_m]
      exact mul_ne_zero hsqrtM_ne (ne_of_gt hfactor_m_pos)
    obtain ⟨δi, hδi, hdiv⟩ := fp.model_div 1 mhat hmhat_ne
    have hinv_ne : invMhat ≠ 0 := by
      dsimp [invMhat]
      rw [hdiv]
      have hone_div_ne : (1 : ℝ) / mhat ≠ 0 :=
        div_ne_zero one_ne_zero hmhat_ne
      have hδi_lower : -fp.u ≤ δi := (abs_le.mp hδi).1
      have hfactor_i_pos : 0 < 1 + δi := by linarith
      exact mul_ne_zero hone_div_ne (ne_of_gt hfactor_i_pos)
    obtain ⟨δp, hδp, hmul⟩ := fp.model_mul shat invMhat
    have hδp_lower : -fp.u ≤ δp := (abs_le.mp hδp).1
    have hfactor_p_pos : 0 < 1 + δp := by linarith
    rw [hmul]
    exact mul_ne_zero (mul_ne_zero hshat_ne hinv_ne)
      (ne_of_gt hfactor_p_pos)

@[simp] theorem flSqrtMulInvSqrt_den (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtMulInvSqrt fp hm hs hu).den =
      fp.fl_mul (fp.fl_sqrt (s : ℝ))
        (fp.fl_div 1 (fp.fl_sqrt (m : ℝ))) := rfl

@[simp] theorem flSqrtMulInvSqrt_den_abs_error (fp : FPModel) {m s : ℕ}
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flSqrtMulInvSqrt fp hm hs hu).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u)) := rfl

end ComputedUniformRowScaleDen

/- ============================================================
   Concrete denominator routine used by the final SRHT endpoints
   ============================================================ -/

/-- Positive `gammaValid` horizons imply the unit roundoff is below one.

This adapter lets concrete denominator routines use the same sample-count
roundoff guard as the downstream Gram-dot-product analysis. -/
theorem uniformRowUnitRoundoff_lt_one_of_pos_gammaValid
    (fp : FPModel) {s : ℕ} (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) :
    fp.u < 1 := by
  have hsNat : 0 < s := by exact_mod_cast hs
  have hone_le_s_nat : 1 ≤ s := Nat.succ_le_iff.mpr hsNat
  have hone_le_s : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hone_le_s_nat
  have hu_le_su : fp.u ≤ (s : ℝ) * fp.u := by
    simpa using mul_le_mul_of_nonneg_right hone_le_s fp.u_nonneg
  have hsu_lt_one : (s : ℝ) * fp.u < 1 := by
    simpa [gammaValid] using hγ
  exact lt_of_le_of_lt hu_le_su hsu_lt_one

/-- Concrete uniform-row denominator routine for Algorithm 3.

The row-sampling law remains the exact uniform law.  The non-probability
denominator used by the implementation is the rounded routine
`fl_sqrt ((s : R) * (m : R)^{-1})`, where the scalar input ratio is supplied
exactly, and the constructor below carries the proved absolute
denominator-error bound for that routine. -/
noncomputable def uniformRowFlSqrtExactInputScaleDen
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    ComputedUniformRowScaleDen fp m s :=
  ComputedUniformRowScaleDen.flSqrtExactInput fp hm hs
    (uniformRowUnitRoundoff_lt_one_of_pos_gammaValid fp hs hγs)

@[simp] theorem uniformRowFlSqrtExactInputScaleDen_den
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtExactInputScaleDen fp hm hs hγs).den =
      fp.fl_sqrt ((s : ℝ) * (m : ℝ)⁻¹) := rfl

@[simp] theorem uniformRowFlSqrtExactInputScaleDen_den_abs_error
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtExactInputScaleDen fp hm hs hγs).den_abs_error =
      uniformRowSampleScaleDen (m := m) s * fp.u := rfl

/-- Concrete uniform-row denominator routine for Algorithm 3.

The row-sampling law remains the exact uniform law.  The non-probability
denominator used by the implementation is the rounded routine
`fl_sqrt (fl_div (s : R) (m : R))`, and the constructor below carries the
proved absolute denominator-error bound for that routine. -/
noncomputable def uniformRowFlDivThenSqrtScaleDen
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    ComputedUniformRowScaleDen fp m s :=
  ComputedUniformRowScaleDen.flDivThenSqrt fp hm hs
    (uniformRowUnitRoundoff_lt_one_of_pos_gammaValid fp hs hγs)

@[simp] theorem uniformRowFlDivThenSqrtScaleDen_den
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlDivThenSqrtScaleDen fp hm hs hγs).den =
      fp.fl_sqrt (fp.fl_div (s : ℝ) (m : ℝ)) := rfl

@[simp] theorem uniformRowFlDivThenSqrtScaleDen_den_abs_error
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlDivThenSqrtScaleDen fp hm hs hγs).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        (Real.sqrt (1 + fp.u) * fp.u + fp.u) := rfl

/-- Concrete uniform-row denominator routine for Algorithm 3.

The row-sampling law remains the exact uniform law.  The non-probability
denominator used by the implementation is the rounded routine
`fl_sqrt (fl_mul (s : R) (fl_div 1 (m : R)))`, and the constructor below
carries the proved absolute denominator-error bound for that routine. -/
noncomputable def uniformRowFlInvMulThenSqrtScaleDen
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    ComputedUniformRowScaleDen fp m s :=
  ComputedUniformRowScaleDen.flInvMulThenSqrt fp hm hs
    (uniformRowUnitRoundoff_lt_one_of_pos_gammaValid fp hs hγs)

@[simp] theorem uniformRowFlInvMulThenSqrtScaleDen_den
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlInvMulThenSqrtScaleDen fp hm hs hγs).den =
      fp.fl_sqrt (fp.fl_mul (s : ℝ) (fp.fl_div 1 (m : ℝ))) := rfl

@[simp] theorem uniformRowFlInvMulThenSqrtScaleDen_den_abs_error
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlInvMulThenSqrtScaleDen fp hm hs hγs).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        (Real.sqrt ((1 + fp.u) * (1 + fp.u)) * fp.u +
          (2 * fp.u + fp.u ^ 2)) := rfl

/-- Concrete uniform-row denominator routine for Algorithm 3.

The row-sampling law remains the exact uniform law.  The non-probability
denominator used by the implementation is the rounded routine
`fl_div (fl_sqrt (s : R)) (fl_sqrt (m : R))`, and the constructor below
carries the proved absolute denominator-error bound for that routine. -/
noncomputable def uniformRowFlSqrtDivSqrtScaleDen
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    ComputedUniformRowScaleDen fp m s :=
  ComputedUniformRowScaleDen.flSqrtDivSqrt fp hm hs
    (uniformRowUnitRoundoff_lt_one_of_pos_gammaValid fp hs hγs)

@[simp] theorem uniformRowFlSqrtDivSqrtScaleDen_den
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtDivSqrtScaleDen fp hm hs hγs).den =
      fp.fl_div (fp.fl_sqrt (s : ℝ)) (fp.fl_sqrt (m : ℝ)) := rfl

@[simp] theorem uniformRowFlSqrtDivSqrtScaleDen_den_abs_error
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtDivSqrtScaleDen fp hm hs hγs).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        ((3 * fp.u + fp.u ^ 2) / (1 - fp.u)) := rfl

/-- Concrete uniform-row denominator routine for Algorithm 3.

The row-sampling law remains the exact uniform law.  The non-probability
denominator used by the implementation is the rounded routine
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt m))`, and the constructor below carries
the proved absolute denominator-error bound for that routine. -/
noncomputable def uniformRowFlSqrtMulInvSqrtScaleDen
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    ComputedUniformRowScaleDen fp m s :=
  ComputedUniformRowScaleDen.flSqrtMulInvSqrt fp hm hs
    (uniformRowUnitRoundoff_lt_one_of_pos_gammaValid fp hs hγs)

@[simp] theorem uniformRowFlSqrtMulInvSqrtScaleDen_den
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs).den =
      fp.fl_mul (fp.fl_sqrt (s : ℝ))
        (fp.fl_div 1 (fp.fl_sqrt (m : ℝ))) := rfl

@[simp] theorem uniformRowFlSqrtMulInvSqrtScaleDen_den_abs_error
    (fp : FPModel) {m s : ℕ} (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγs : gammaValid fp s) :
    (uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs).den_abs_error =
      uniformRowSampleScaleDen (m := m) s *
        ((4 * fp.u + 3 * fp.u ^ 2 + fp.u ^ 3) / (1 - fp.u)) := rfl

/-- Exact uniform row-sampling sketch entry. -/
noncomputable def uniformRowSampleIncrement {m n : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  U i j / uniformRowSampleScaleDen (m := m) s

/-- Floating-point uniform row-sampling sketch entry, using the repository's
rounded division primitive. -/
noncomputable def fl_uniformRowSampleIncrement (fp : FPModel)
    {m n : ℕ} (s : ℕ) (U : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  fp.fl_div (U i j) (uniformRowSampleScaleDen (m := m) s)

/-- Exact uniform row-sampling sketch entry using a computed scale
    denominator. -/
noncomputable def uniformRowSampleIncrementWithComputedDen {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (den : ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  U i j / den

/-- Floating-point uniform row-sampling sketch entry using a computed scale
    denominator. -/
noncomputable def fl_uniformRowSampleIncrementWithComputedDen (fp : FPModel)
    {m n : ℕ} (U : Fin m → Fin n → ℝ) (den : ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  fp.fl_div (U i j) den

/-- Forward-error bound for one floating-point uniform row-scaling division. -/
theorem fl_uniformRowSampleIncrement_error_bound (fp : FPModel)
    {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n)
    (hdenom : uniformRowSampleScaleDen (m := m) s ≠ 0) :
    |fl_uniformRowSampleIncrement fp s U i j -
      uniformRowSampleIncrement s U i j| ≤
      |uniformRowSampleIncrement s U i j| * fp.u := by
  unfold fl_uniformRowSampleIncrement uniformRowSampleIncrement
  exact fl_div_error_bound fp (U i j)
    (uniformRowSampleScaleDen (m := m) s) hdenom

/-- Forward-error bound for one floating-point uniform row-scaling division
    with a computed denominator. -/
theorem fl_uniformRowSampleIncrementWithComputedDen_error_bound
    (fp : FPModel) {m n : ℕ} (U : Fin m → Fin n → ℝ)
    (den : ℝ) (i : Fin m) (j : Fin n) (hdenom : den ≠ 0) :
    |fl_uniformRowSampleIncrementWithComputedDen fp U den i j -
      uniformRowSampleIncrementWithComputedDen U den i j| ≤
      |uniformRowSampleIncrementWithComputedDen U den i j| * fp.u := by
  unfold fl_uniformRowSampleIncrementWithComputedDen
    uniformRowSampleIncrementWithComputedDen
  exact fl_div_error_bound fp (U i j) den hdenom

/-- Exact uniform row sketch for a trace of sampled rows. -/
noncomputable def uniformRowSampleSketch {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin steps → Fin n → ℝ :=
  fun t j => uniformRowSampleIncrement s U (samples t) j

/-- Floating-point uniform row sketch for a trace of sampled rows. -/
noncomputable def fl_uniformRowSampleSketch (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin steps → Fin n → ℝ :=
  fun t j => fl_uniformRowSampleIncrement fp s U (samples t) j

/-- Exact uniform row sketch using a computed scale denominator. -/
noncomputable def uniformRowSampleSketchWithComputedDen {m n steps : ℕ}
    (U : Fin m → Fin n → ℝ) (den : ℝ) (samples : RowTrace m steps) :
    Fin steps → Fin n → ℝ :=
  fun t j => uniformRowSampleIncrementWithComputedDen U den (samples t) j

/-- Floating-point uniform row sketch using a computed scale denominator. -/
noncomputable def fl_uniformRowSampleSketchWithComputedDen (fp : FPModel)
    {m n steps : ℕ} (U : Fin m → Fin n → ℝ) (den : ℝ)
    (samples : RowTrace m steps) : Fin steps → Fin n → ℝ :=
  fun t j => fl_uniformRowSampleIncrementWithComputedDen fp U den (samples t) j

/-- Entrywise forward-error bound for the floating-point uniform row sketch. -/
theorem fl_uniformRowSampleSketch_error_bound (fp : FPModel)
    {m n steps s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hdenom : uniformRowSampleScaleDen (m := m) s ≠ 0) :
    |fl_uniformRowSampleSketch fp s U samples t j -
      uniformRowSampleSketch s U samples t j| ≤
      |uniformRowSampleSketch s U samples t j| * fp.u := by
  exact fl_uniformRowSampleIncrement_error_bound fp U (samples t) j hdenom

/-- Entrywise forward-error bound for the floating-point uniform row sketch
    with a computed scale denominator. -/
theorem fl_uniformRowSampleSketchWithComputedDen_error_bound (fp : FPModel)
    {m n steps : ℕ} (U : Fin m → Fin n → ℝ) (den : ℝ)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hdenom : den ≠ 0) :
    |fl_uniformRowSampleSketchWithComputedDen fp U den samples t j -
      uniformRowSampleSketchWithComputedDen U den samples t j| ≤
      |uniformRowSampleSketchWithComputedDen U den samples t j| * fp.u := by
  exact fl_uniformRowSampleIncrementWithComputedDen_error_bound fp U den
    (samples t) j hdenom

/-- Uniform row-scaling bound packaged for a computed denominator
    certificate. -/
theorem fl_uniformRowSampleSketch_computedDen_error_bound (fp : FPModel)
    {m n steps s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s) (samples : RowTrace m steps)
    (t : Fin steps) (j : Fin n) :
    |fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples t j -
      uniformRowSampleSketchWithComputedDen U dhat.den samples t j| ≤
      |uniformRowSampleSketchWithComputedDen U dhat.den samples t j| * fp.u :=
  fl_uniformRowSampleSketchWithComputedDen_error_bound fp U dhat.den
    samples t j dhat.den_ne_zero

/-- Perturbation from using a computed row-scale denominator instead of the
ideal `sqrt(s / m)` denominator.  The sampling law is still exact; this theorem
charges only the non-probability scalar used by the row scaling step. -/
theorem uniformRowSampleIncrementWithComputedDen_ideal_error_bound
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (i : Fin m) (j : Fin n)
    (hdenom : uniformRowSampleScaleDen (m := m) s ≠ 0) :
    |uniformRowSampleIncrementWithComputedDen U dhat.den i j -
      uniformRowSampleIncrement s U i j| ≤
      |U i j| * dhat.den_abs_error /
        (|dhat.den| * |uniformRowSampleScaleDen (m := m) s|) := by
  let d : ℝ := uniformRowSampleScaleDen (m := m) s
  have hdelta : |d - dhat.den| ≤ dhat.den_abs_error := by
    simpa [d, abs_sub_comm] using dhat.den_abs_error_bound
  have hd : d ≠ 0 := by
    simpa [d] using hdenom
  have hdenprod_nonneg : 0 ≤ |dhat.den| * |d| :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsplit :
      U i j / dhat.den - U i j / d =
        U i j * (d - dhat.den) / (dhat.den * d) := by
    field_simp [dhat.den_ne_zero, hd]
  unfold uniformRowSampleIncrementWithComputedDen uniformRowSampleIncrement
  calc
    |U i j / dhat.den - U i j / d|
        = |U i j * (d - dhat.den) / (dhat.den * d)| := by
            rw [hsplit]
    _ = |U i j| * |d - dhat.den| / (|dhat.den| * |d|) := by
            rw [abs_div, abs_mul, abs_mul]
    _ ≤ |U i j| * dhat.den_abs_error / (|dhat.den| * |d|) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdelta (abs_nonneg _))
              hdenprod_nonneg

/-- Total entrywise row-scaling error when the uniform-row denominator is
computed approximately and the division itself is rounded. -/
theorem fl_uniformRowSampleSketch_computedDen_total_error_bound
    (fp : FPModel) {m n steps s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s) (samples : RowTrace m steps)
    (t : Fin steps) (j : Fin n) (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    |fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples t j -
      uniformRowSampleSketch s U samples t j| ≤
      |uniformRowSampleSketchWithComputedDen U dhat.den samples t j| * fp.u +
        |U (samples t) j| * dhat.den_abs_error /
          (|dhat.den| * |uniformRowSampleScaleDen (m := m) s|) := by
  let Comp : ℝ :=
    uniformRowSampleSketchWithComputedDen U dhat.den samples t j
  let Exact : ℝ := uniformRowSampleSketch s U samples t j
  let Fl : ℝ :=
    fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples t j
  have hround :
      |Fl - Comp| ≤ |Comp| * fp.u := by
    simpa [Fl, Comp] using
      fl_uniformRowSampleSketch_computedDen_error_bound
        fp U dhat samples t j
  have hdenom : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  have hden :
      |Comp - Exact| ≤
        |U (samples t) j| * dhat.den_abs_error /
          (|dhat.den| * |uniformRowSampleScaleDen (m := m) s|) := by
    simpa [Comp, Exact, uniformRowSampleSketch,
      uniformRowSampleSketchWithComputedDen] using
      uniformRowSampleIncrementWithComputedDen_ideal_error_bound
        fp U dhat (samples t) j hdenom
  have hsplit : Fl - Exact = (Fl - Comp) + (Comp - Exact) := by ring
  calc
    |Fl - Exact|
        = |(Fl - Comp) + (Comp - Exact)| := by rw [hsplit]
    _ ≤ |Fl - Comp| + |Comp - Exact| := abs_add_le _ _
    _ ≤ |Comp| * fp.u +
        |U (samples t) j| * dhat.den_abs_error /
          (|dhat.den| * |uniformRowSampleScaleDen (m := m) s|) :=
        add_le_add hround hden

/-- Exact-denominator specialization of the computed-denominator row-scaling
bound.  With zero denominator error, the result reduces to the ordinary rounded
division bound for the ideal uniform row sketch. -/
theorem fl_uniformRowSampleSketch_computedDen_total_error_bound_exact
    (fp : FPModel) {m n steps s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    |fl_uniformRowSampleSketchWithComputedDen fp U
        (ComputedUniformRowScaleDen.exact fp hm hs).den samples t j -
      uniformRowSampleSketch s U samples t j| ≤
      |uniformRowSampleSketch s U samples t j| * fp.u := by
  have hdenom : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  simpa [fl_uniformRowSampleSketchWithComputedDen, fl_uniformRowSampleSketch,
    uniformRowSampleSketchWithComputedDen] using
    fl_uniformRowSampleSketch_error_bound fp U samples t j hdenom

/-- The exact row-sketch Gram of the uniformly rescaled sampled rows is the
uniform sample-average Gram matrix used by the exact concentration theorem. -/
theorem rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
    {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    rowSketchGram (uniformRowSampleSketch s U samples) =
      uniformRowSampleGram U samples := by
  classical
  funext j k
  have hden_ne : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
  have hden_sq :
      uniformRowSampleScaleDen (m := m) s ^ 2 =
        (s : ℝ) * (m : ℝ)⁻¹ := by
    unfold uniformRowSampleScaleDen
    rw [Real.sq_sqrt]
    exact mul_nonneg (le_of_lt hs) (inv_nonneg.mpr (le_of_lt hmRpos))
  unfold rowSketchGram uniformRowSampleSketch uniformRowSampleIncrement
    uniformRowSampleGram uniformRowOuterGramSample
  calc
    (∑ t : Fin s,
      U (samples t) j / uniformRowSampleScaleDen (m := m) s *
        (U (samples t) k / uniformRowSampleScaleDen (m := m) s))
        =
      ∑ t : Fin s,
        ((m : ℝ) * U (samples t) j * U (samples t) k) / (s : ℝ) := by
          apply Finset.sum_congr rfl
          intro t _
          calc
            U (samples t) j / uniformRowSampleScaleDen (m := m) s *
                (U (samples t) k / uniformRowSampleScaleDen (m := m) s)
                =
              (U (samples t) j * U (samples t) k) /
                (uniformRowSampleScaleDen (m := m) s ^ 2) := by
                  field_simp [hden_ne]
            _ =
              (U (samples t) j * U (samples t) k) /
                ((s : ℝ) * (m : ℝ)⁻¹) := by
                  rw [hden_sq]
            _ =
              ((m : ℝ) * U (samples t) j * U (samples t) k) / (s : ℝ) := by
                  field_simp [hs_ne, hm_ne]
    _ =
      (∑ t : Fin s, (m : ℝ) * U (samples t) j * U (samples t) k) /
        (s : ℝ) := by
          rw [Finset.sum_div]

/-- Sample-dependent exact sampled-Gram perturbation budget induced by an
entrywise absolute error certificate for a computed preconditioned basis
`Vhat`.  This budget charges only the computed basis entries; it does not charge
the uniform row law, which is exact and implementation-independent. -/
noncomputable def uniformRowSampleGramBasisPerturbBudget {m n s : ℕ}
    (V Vhat : Fin m → Fin n → ℝ) (E : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) : ℝ :=
  frobNorm
    (fun j k : Fin n =>
      ∑ t : Fin s,
        ((E (samples t) j / uniformRowSampleScaleDen (m := m) s) *
            |uniformRowSampleSketch s Vhat samples t k| +
          |uniformRowSampleSketch s V samples t j| *
            (E (samples t) k / uniformRowSampleScaleDen (m := m) s)))

/-- A computed preconditioned basis with entrywise absolute error `E` induces
the displayed sampled-Gram perturbation budget. -/
theorem uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
    {m n s : ℕ} (V Vhat : Fin m → Fin n → ℝ)
    (E : Fin m → Fin n → ℝ) (samples : RowTrace m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hE_nonneg : ∀ i j, 0 ≤ E i j)
    (hentry : ∀ i j, |Vhat i j - V i j| ≤ E i j) :
    frobNorm
      (fun j k =>
        uniformRowSampleGram Vhat samples j k -
          uniformRowSampleGram V samples j k) ≤
      uniformRowSampleGramBasisPerturbBudget V Vhat E samples := by
  classical
  let B : Fin s → Fin n → ℝ := uniformRowSampleSketch s V samples
  let Bhat : Fin s → Fin n → ℝ := uniformRowSampleSketch s Vhat samples
  let Escaled : Fin s → Fin n → ℝ :=
    fun t j => E (samples t) j / uniformRowSampleScaleDen (m := m) s
  have hden_pos : 0 < uniformRowSampleScaleDen (m := m) s := by
    unfold uniformRowSampleScaleDen
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    exact Real.sqrt_pos.2 (mul_pos hs (inv_pos.mpr hmRpos))
  have hEscaled_nonneg : ∀ t j, 0 ≤ Escaled t j := by
    intro t j
    exact div_nonneg (hE_nonneg (samples t) j) (le_of_lt hden_pos)
  have hBentry : ∀ t j, |Bhat t j - B t j| ≤ Escaled t j := by
    intro t j
    dsimp [B, Bhat, Escaled, uniformRowSampleSketch,
      uniformRowSampleIncrement]
    rw [← sub_div, abs_div, abs_of_pos hden_pos]
    exact div_le_div_of_nonneg_right
      (hentry (samples t) j) (le_of_lt hden_pos)
  have hgram :=
    rowSketchGram_frob_abs_error_bound_of_entrywise
      B Bhat Escaled hEscaled_nonneg hBentry
  have hB :
      rowSketchGram B = uniformRowSampleGram V samples := by
    simpa [B] using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        V samples hm hs
  have hBhat :
      rowSketchGram Bhat = uniformRowSampleGram Vhat samples := by
    simpa [Bhat] using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        Vhat samples hm hs
  simpa [uniformRowSampleGramBasisPerturbBudget, B, Bhat, Escaled, hB, hBhat]
    using hgram

-- ============================================================
-- Fully floating-point uniform sample Gram
-- ============================================================

/-- Fully floating-point uniform sampled Gram: form the rounded uniform row
sketch and compute each Gram entry using the repository dot-product algorithm. -/
noncomputable def fl_uniformRowSampleGramDot (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k =>
    fl_dotProduct fp steps
      (fun t => fl_uniformRowSampleSketch fp s U samples t j)
      (fun t => fl_uniformRowSampleSketch fp s U samples t k)

/-- Fully floating-point uniform sampled Gram with a computed denominator:
form each sampled row using `den` instead of the exact mathematical
`sqrt(s/m)`, round that division, and compute each Gram entry using the
repository dot-product algorithm. -/
noncomputable def fl_uniformRowSampleGramDotWithComputedDen (fp : FPModel)
    {m n steps : ℕ} (_s : ℕ)
    (U : Fin m → Fin n → ℝ) (den : ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k =>
    fl_dotProduct fp steps
      (fun t => fl_uniformRowSampleSketchWithComputedDen fp U den samples t j)
      (fun t => fl_uniformRowSampleSketchWithComputedDen fp U den samples t k)

/-- Sample-dependent row-scaling perturbation budget for a uniform row sketch.
It is expressed in terms of the exact uniformly rescaled sketch entries. -/
noncomputable def uniformRowSampleGramFpPerturbBudget (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) : ℝ :=
  frobNorm
    (fun j k : Fin n =>
      (2 * fp.u + fp.u ^ 2) *
        ∑ t : Fin steps,
          |uniformRowSampleSketch s U samples t j| *
            |uniformRowSampleSketch s U samples t k|)

/-- Sample-dependent dot-product perturbation budget for the fully
floating-point uniform sampled Gram. -/
noncomputable def uniformRowSampleGramDotProductBudget (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) : ℝ :=
  frobNorm
    (fun j k : Fin n =>
      gamma fp steps * (1 + fp.u) ^ 2 *
        ∑ t : Fin steps,
          |uniformRowSampleSketch s U samples t j| *
            |uniformRowSampleSketch s U samples t k|)

/-- Total sample-dependent perturbation budget for the fully floating-point
uniform sampled Gram. -/
noncomputable def uniformRowSampleGramFullFpPerturbBudget (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) : ℝ :=
  uniformRowSampleGramFpPerturbBudget fp s U samples +
    uniformRowSampleGramDotProductBudget fp s U samples

/-- Entrywise absolute error budget for a rounded uniform-row sketch built
with a computed denominator.  The first term is the rounded sampled-row
division, and the second term is the denominator-computation error measured
against the exact denominator `sqrt(s/m)`. -/
noncomputable def uniformRowSampleSketchComputedDenEntryAbsBudget
    (fp : FPModel) {m n steps s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n) : ℝ :=
  |uniformRowSampleSketchWithComputedDen U dhat.den samples t j| * fp.u +
    |U (samples t) j| * dhat.den_abs_error /
      (|dhat.den| * |uniformRowSampleScaleDen (m := m) s|)

/-- Sample-dependent exact-Gram perturbation budget for a uniform-row sketch
whose row denominator has been computed before the rounded row divisions. -/
noncomputable def uniformRowSampleGramComputedDenScalePerturbBudget
    (fp : FPModel) {m n steps s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (samples : RowTrace m steps) : ℝ :=
  let B : Fin steps → Fin n → ℝ := uniformRowSampleSketch s U samples
  let Bhat : Fin steps → Fin n → ℝ :=
    fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples
  let E : Fin steps → Fin n → ℝ :=
    uniformRowSampleSketchComputedDenEntryAbsBudget fp U dhat samples
  frobNorm
    (fun j k : Fin n =>
      ∑ t : Fin steps, (E t j * |Bhat t k| + |B t j| * E t k))

/-- Sample-dependent dot-product budget for a uniform sampled Gram whose row
sketch was formed with a computed denominator.  It is written directly in
terms of the actually rounded sketch inputs to the dot products. -/
noncomputable def uniformRowSampleGramComputedDenDotProductBudget
    (fp : FPModel) {m n steps s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (samples : RowTrace m steps) : ℝ :=
  let Bhat : Fin steps → Fin n → ℝ :=
    fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples
  frobNorm
    (fun j k : Fin n =>
      gamma fp steps *
        ∑ t : Fin steps, |Bhat t j| * |Bhat t k|)

/-- Total sample-dependent perturbation budget for the fully floating-point
uniform sampled Gram with computed denominator. -/
noncomputable def uniformRowSampleGramComputedDenFullFpPerturbBudget
    (fp : FPModel) {m n steps s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (samples : RowTrace m steps) : ℝ :=
  uniformRowSampleGramComputedDenScalePerturbBudget fp U dhat samples +
    uniformRowSampleGramComputedDenDotProductBudget fp U dhat samples

/-- The sample-dependent uniform FP Gram perturbation budget is nonnegative. -/
theorem uniformRowSampleGramFullFpPerturbBudget_nonneg (fp : FPModel)
    {m n steps : ℕ} (s : ℕ)
    (U : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    0 ≤ uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
  unfold uniformRowSampleGramFullFpPerturbBudget
    uniformRowSampleGramFpPerturbBudget
    uniformRowSampleGramDotProductBudget
  exact add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

/-- The sample-dependent computed-denominator uniform FP Gram perturbation
budget is nonnegative. -/
theorem uniformRowSampleGramComputedDenFullFpPerturbBudget_nonneg
    (fp : FPModel) {m n steps s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (samples : RowTrace m steps) :
    0 ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
  unfold uniformRowSampleGramComputedDenFullFpPerturbBudget
  exact add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

/-- Deterministic constant budget for the row-scaling part of the uniform
sampled-Gram perturbation.  The scalar `C` bounds every sampled absolute-product
sum `∑ₜ |B_tj| |B_tk|`. -/
noncomputable def uniformRowSampleGramFpPerturbConstBudget (fp : FPModel)
    {n : ℕ} (C : ℝ) : ℝ :=
  frobNorm (fun _j _k : Fin n => (2 * fp.u + fp.u ^ 2) * C)

/-- Deterministic constant budget for the dot-product part of the uniform
sampled-Gram perturbation. -/
noncomputable def uniformRowSampleGramDotProductConstBudget (fp : FPModel)
    {n : ℕ} (steps : ℕ) (C : ℝ) : ℝ :=
  frobNorm
    (fun _j _k : Fin n => gamma fp steps * (1 + fp.u) ^ 2 * C)

/-- Total deterministic constant budget for the fully floating-point uniform
sampled Gram. -/
noncomputable def uniformRowSampleGramFullFpConstBudget (fp : FPModel)
    {n : ℕ} (steps : ℕ) (C : ℝ) : ℝ :=
  uniformRowSampleGramFpPerturbConstBudget fp (n := n) C +
    uniformRowSampleGramDotProductConstBudget fp (n := n) steps C

/-- Closed form of the row-scaling constant budget, exposing the dimension of
the Gram matrix. -/
theorem uniformRowSampleGramFpPerturbConstBudget_eq_nat_mul
    (fp : FPModel) {n : ℕ} {C : ℝ} (hC : 0 ≤ C) :
    uniformRowSampleGramFpPerturbConstBudget fp (n := n) C =
      (n : ℝ) * ((2 * fp.u + fp.u ^ 2) * C) := by
  have hscale : 0 ≤ (2 * fp.u + fp.u ^ 2) * C := by
    have hu : 0 ≤ 2 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg, sq_nonneg fp.u]
    exact mul_nonneg hu hC
  unfold uniformRowSampleGramFpPerturbConstBudget
  exact frobNorm_const hscale

/-- Closed form of the dot-product constant budget, exposing the dimension of
the Gram matrix. -/
theorem uniformRowSampleGramDotProductConstBudget_eq_nat_mul
    (fp : FPModel) {n steps : ℕ} {C : ℝ}
    (hγ : gammaValid fp steps) (hC : 0 ≤ C) :
    uniformRowSampleGramDotProductConstBudget fp (n := n) steps C =
      (n : ℝ) * (gamma fp steps * (1 + fp.u) ^ 2 * C) := by
  have hscale : 0 ≤ gamma fp steps * (1 + fp.u) ^ 2 * C := by
    have hleft : 0 ≤ gamma fp steps * (1 + fp.u) ^ 2 :=
      mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + fp.u))
    exact mul_nonneg hleft hC
  unfold uniformRowSampleGramDotProductConstBudget
  exact frobNorm_const hscale

/-- A row-norm bound controls one unscaled row product. -/
theorem abs_mul_entry_le_rowNormSq {m n : ℕ}
    (U : Fin m → Fin n → ℝ) (i : Fin m) (j k : Fin n) :
    |U i j| * |U i k| ≤ rowNormSq U i := by
  let x : Fin n → ℝ := fun l => U i l
  have hj : |U i j| ≤ vecNorm2 x := by
    simpa [x] using abs_coord_le_vecNorm2 x j
  have hk : |U i k| ≤ vecNorm2 x := by
    simpa [x] using abs_coord_le_vecNorm2 x k
  calc
    |U i j| * |U i k|
        ≤ vecNorm2 x * vecNorm2 x :=
          mul_le_mul hj hk (abs_nonneg _) (vecNorm2_nonneg x)
    _ = rowNormSq U i := by
          rw [← sq, vecNorm2_sq]
          rfl

/-- If every sampled row has squared norm at most `R`, then every
absolute-product sum in the uniformly rescaled sketch is at most `m R`. -/
theorem uniformRowSampleSketch_abs_mul_sum_le_of_rowNormSq_le
    {m n s : ℕ} (U : Fin m → Fin n → ℝ) (samples : RowTrace m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    {R : ℝ} (hrow : ∀ t : Fin s, rowNormSq U (samples t) ≤ R)
    (j k : Fin n) :
    (∑ t : Fin s,
        |uniformRowSampleSketch s U samples t j| *
          |uniformRowSampleSketch s U samples t k|) ≤
      (m : ℝ) * R := by
  classical
  have hden_ne : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  have hden_pos : 0 < uniformRowSampleScaleDen (m := m) s := by
    unfold uniformRowSampleScaleDen
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    exact Real.sqrt_pos.2 (mul_pos hs (inv_pos.mpr hmRpos))
  have hden_sq :
      uniformRowSampleScaleDen (m := m) s ^ 2 =
        (s : ℝ) * (m : ℝ)⁻¹ := by
    unfold uniformRowSampleScaleDen
    have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
    rw [Real.sq_sqrt]
    exact mul_nonneg (le_of_lt hs) (inv_nonneg.mpr (le_of_lt hmRpos))
  have hden_sq_pos : 0 < uniformRowSampleScaleDen (m := m) s ^ 2 := by
    exact sq_pos_of_ne_zero hden_ne
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
  calc
    (∑ t : Fin s,
        |uniformRowSampleSketch s U samples t j| *
          |uniformRowSampleSketch s U samples t k|)
        ≤ ∑ _t : Fin s, ((m : ℝ) * R) / (s : ℝ) := by
            apply Finset.sum_le_sum
            intro t _
            have hprodU :
                |U (samples t) j| * |U (samples t) k| ≤ R :=
              (abs_mul_entry_le_rowNormSq U (samples t) j k).trans (hrow t)
            unfold uniformRowSampleSketch uniformRowSampleIncrement
            calc
              |U (samples t) j / uniformRowSampleScaleDen (m := m) s| *
                  |U (samples t) k / uniformRowSampleScaleDen (m := m) s|
                  =
                (|U (samples t) j| * |U (samples t) k|) /
                  (uniformRowSampleScaleDen (m := m) s ^ 2) := by
                    rw [abs_div, abs_div, abs_of_pos hden_pos]
                    field_simp [hden_ne]
              _ ≤ R / (uniformRowSampleScaleDen (m := m) s ^ 2) :=
                    div_le_div_of_nonneg_right hprodU (le_of_lt hden_sq_pos)
              _ = ((m : ℝ) * R) / (s : ℝ) := by
                    rw [hden_sq]
                    field_simp [hs_ne, hm_ne]
    _ = (m : ℝ) * R := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
          field_simp [hs_ne]

/-- The sample-dependent uniform row-scaling FP budget is bounded by the
constant budget whenever all sampled absolute-product sums are bounded by `C`.
-/
theorem uniformRowSampleGramFpPerturbBudget_le_const_of_abs_mul_sum_le
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) {C : ℝ} (hC : 0 ≤ C)
    (hprod :
      ∀ j k : Fin n,
        (∑ t : Fin s,
          |uniformRowSampleSketch s U samples t j| *
            |uniformRowSampleSketch s U samples t k|) ≤ C) :
    uniformRowSampleGramFpPerturbBudget fp s U samples ≤
      uniformRowSampleGramFpPerturbConstBudget fp (n := n) C := by
  classical
  let c : ℝ := 2 * fp.u + fp.u ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  unfold uniformRowSampleGramFpPerturbBudget
    uniformRowSampleGramFpPerturbConstBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hc hC
  · intro j k
    let S : ℝ :=
      ∑ t : Fin s,
        |uniformRowSampleSketch s U samples t j| *
          |uniformRowSampleSketch s U samples t k|
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      |(2 * fp.u + fp.u ^ 2) * S|
          = c * S := by
              simp [c, S, abs_of_nonneg (mul_nonneg hc hS_nonneg)]
      _ ≤ c * C := mul_le_mul_of_nonneg_left (by simpa [S] using hprod j k) hc
      _ = (2 * fp.u + fp.u ^ 2) * C := by simp [c]

/-- The sample-dependent uniform dot-product FP budget is bounded by the
constant budget whenever all sampled absolute-product sums are bounded by `C`.
-/
theorem uniformRowSampleGramDotProductBudget_le_const_of_abs_mul_sum_le
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) {C : ℝ} (hγ : gammaValid fp s) (hC : 0 ≤ C)
    (hprod :
      ∀ j k : Fin n,
        (∑ t : Fin s,
          |uniformRowSampleSketch s U samples t j| *
            |uniformRowSampleSketch s U samples t k|) ≤ C) :
    uniformRowSampleGramDotProductBudget fp s U samples ≤
      uniformRowSampleGramDotProductConstBudget fp (n := n) s C := by
  classical
  let c : ℝ := gamma fp s * (1 + fp.u) ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + fp.u))
  unfold uniformRowSampleGramDotProductBudget
    uniformRowSampleGramDotProductConstBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hc hC
  · intro j k
    let S : ℝ :=
      ∑ t : Fin s,
        |uniformRowSampleSketch s U samples t j| *
          |uniformRowSampleSketch s U samples t k|
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      |gamma fp s * (1 + fp.u) ^ 2 * S|
          = c * S := by
              simp [c, S, abs_of_nonneg (mul_nonneg hc hS_nonneg)]
      _ ≤ c * C := mul_le_mul_of_nonneg_left (by simpa [S] using hprod j k) hc
      _ = gamma fp s * (1 + fp.u) ^ 2 * C := by simp [c]

/-- The sample-dependent total FP budget is bounded by a deterministic constant
budget under the same absolute-product-sum bound. -/
theorem uniformRowSampleGramFullFpPerturbBudget_le_const_of_abs_mul_sum_le
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) {C : ℝ} (hγ : gammaValid fp s) (hC : 0 ≤ C)
    (hprod :
      ∀ j k : Fin n,
        (∑ t : Fin s,
          |uniformRowSampleSketch s U samples t j| *
            |uniformRowSampleSketch s U samples t k|) ≤ C) :
    uniformRowSampleGramFullFpPerturbBudget fp s U samples ≤
      uniformRowSampleGramFullFpConstBudget fp (n := n) s C := by
  unfold uniformRowSampleGramFullFpPerturbBudget
    uniformRowSampleGramFullFpConstBudget
  exact add_le_add
    (uniformRowSampleGramFpPerturbBudget_le_const_of_abs_mul_sum_le
      fp U samples hC hprod)
    (uniformRowSampleGramDotProductBudget_le_const_of_abs_mul_sum_le
      fp U samples hγ hC hprod)

/-- Row-norm version of the deterministic constant FP-budget cap: if every
sampled row of `U` has squared norm at most `R`, then the full sampled-Gram FP
budget is bounded by the constant-budget expression with `C = m R`. -/
theorem uniformRowSampleGramFullFpPerturbBudget_le_const_of_sample_rowNormSq_le
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (samples : RowTrace m s) (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ t : Fin s, rowNormSq U (samples t) ≤ R) :
    uniformRowSampleGramFullFpPerturbBudget fp s U samples ≤
      uniformRowSampleGramFullFpConstBudget fp (n := n) s ((m : ℝ) * R) := by
  have hC : 0 ≤ (m : ℝ) * R := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le m) hR
  exact
    uniformRowSampleGramFullFpPerturbBudget_le_const_of_abs_mul_sum_le
      fp U samples hγ hC
      (uniformRowSampleSketch_abs_mul_sum_le_of_rowNormSq_le
        U samples hm hs hrow)

/-- Deterministic fully-floating-point perturbation bound for uniform row
sampling, reusing the repository division and dot-product stability results. -/
theorem fl_uniformRowSampleGramDot_perturb_bound
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (samples : RowTrace m s) :
    frobNorm
      (fun j k =>
        fl_uniformRowSampleGramDot fp s U samples j k -
          uniformRowSampleGram U samples j k) ≤
      uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
  classical
  let B : Fin s → Fin n → ℝ := uniformRowSampleSketch s U samples
  let Bhat : Fin s → Fin n → ℝ := fl_uniformRowSampleSketch fp s U samples
  have hden_ne : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  have hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * fp.u := by
    intro t j
    simpa [B, Bhat] using
      fl_uniformRowSampleSketch_error_bound fp U samples t j hden_ne
  have hdot :
      frobNorm
        (fun j k =>
          fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) ≤
        uniformRowSampleGramDotProductBudget fp s U samples := by
    have hlocal :=
      rowSketchGram_dot_frob_error_bound_of_entrywise
        fp B Bhat fp.u fp.u_nonneg hγ hentry
    simpa [uniformRowSampleGramDotProductBudget, B] using hlocal
  have hBgram :
      rowSketchGram B = uniformRowSampleGram U samples := by
    simpa [B] using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        U samples hm hs
  have hscale :
      frobNorm
        (fun j k =>
          rowSketchGram Bhat j k - uniformRowSampleGram U samples j k) ≤
        uniformRowSampleGramFpPerturbBudget fp s U samples := by
    have hpoint :=
      rowSketchGram_frob_error_bound_of_entrywise
        B Bhat fp.u fp.u_nonneg hentry
    simpa [uniformRowSampleGramFpPerturbBudget, B, hBgram] using hpoint
  have hsplit :
      (fun j k =>
        fl_uniformRowSampleGramDot fp s U samples j k -
          uniformRowSampleGram U samples j k) =
      (fun j k =>
        (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k) +
        (rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)) := by
    funext j k
    simp [fl_uniformRowSampleGramDot, Bhat]
  have htri :=
    frobNorm_add_le
      (fun j k =>
        fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k)
      (fun j k => rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)
  calc
    frobNorm
      (fun j k =>
        fl_uniformRowSampleGramDot fp s U samples j k -
          uniformRowSampleGram U samples j k)
        =
      frobNorm
        (fun j k =>
          (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) +
          (rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)) := by
          rw [hsplit]
    _ ≤
        frobNorm
          (fun j k =>
            fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
        frobNorm
          (fun j k =>
            rowSketchGram Bhat j k - uniformRowSampleGram U samples j k) :=
          htri
    _ ≤ uniformRowSampleGramDotProductBudget fp s U samples +
        uniformRowSampleGramFpPerturbBudget fp s U samples :=
          add_le_add hdot hscale
    _ = uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
          unfold uniformRowSampleGramFullFpPerturbBudget
          ring

/-- Deterministic fully-floating-point perturbation bound for uniform row
sampling when the non-probability denominator `sqrt(s/m)` is itself computed.

The exact row law is still the uniform law.  The budget charges the computed
denominator certificate, rounded row divisions, and rounded Gram dot products.
-/
theorem fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (samples : RowTrace m s) :
    frobNorm
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s U dhat.den samples j k -
          uniformRowSampleGram U samples j k) ≤
      uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
  classical
  let B : Fin s → Fin n → ℝ := uniformRowSampleSketch s U samples
  let Bhat : Fin s → Fin n → ℝ :=
    fl_uniformRowSampleSketchWithComputedDen fp U dhat.den samples
  let E : Fin s → Fin n → ℝ :=
    uniformRowSampleSketchComputedDenEntryAbsBudget fp U dhat samples
  have hden_ne : uniformRowSampleScaleDen (m := m) s ≠ 0 :=
    uniformRowSampleScaleDen_ne_zero hm hs
  have hE_nonneg : ∀ t j, 0 ≤ E t j := by
    intro t j
    dsimp [E, uniformRowSampleSketchComputedDenEntryAbsBudget]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _) fp.u_nonneg)
      (div_nonneg
        (mul_nonneg (abs_nonneg _) dhat.den_abs_error_nonneg)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have hentry : ∀ t j, |Bhat t j - B t j| ≤ E t j := by
    intro t j
    simpa [B, Bhat, E, uniformRowSampleSketchComputedDenEntryAbsBudget] using
      fl_uniformRowSampleSketch_computedDen_total_error_bound
        fp U dhat samples t j hm hs
  have hscale :
      frobNorm
        (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k) ≤
      uniformRowSampleGramComputedDenScalePerturbBudget fp U dhat samples := by
    simpa [uniformRowSampleGramComputedDenScalePerturbBudget, B, Bhat, E] using
      rowSketchGram_frob_abs_error_bound_of_entrywise
        B Bhat E hE_nonneg hentry
  have hdot :
      frobNorm
        (fun j k =>
          fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) ≤
      uniformRowSampleGramComputedDenDotProductBudget fp U dhat samples := by
    apply frobNorm_le_of_entry_abs_le
    · intro j k
      apply mul_nonneg (gamma_nonneg fp hγ)
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    · intro j k
      simpa [uniformRowSampleGramComputedDenDotProductBudget, Bhat] using
        dotProduct_error_bound fp s
          (fun t => Bhat t j) (fun t => Bhat t k) hγ
  have hBgram :
      rowSketchGram B = uniformRowSampleGram U samples := by
    simpa [B] using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        U samples hm hs
  have hscale' :
      frobNorm
        (fun j k => rowSketchGram Bhat j k - uniformRowSampleGram U samples j k) ≤
      uniformRowSampleGramComputedDenScalePerturbBudget fp U dhat samples := by
    simpa [hBgram] using hscale
  have hsplit :
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s U dhat.den samples j k -
          uniformRowSampleGram U samples j k) =
      (fun j k =>
        (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k) +
        (rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)) := by
    funext j k
    simp [fl_uniformRowSampleGramDotWithComputedDen, Bhat]
  have htri :=
    frobNorm_add_le
      (fun j k =>
        fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k)
      (fun j k => rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)
  calc
    frobNorm
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s U dhat.den samples j k -
          uniformRowSampleGram U samples j k)
        =
      frobNorm
        (fun j k =>
          (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) +
          (rowSketchGram Bhat j k - uniformRowSampleGram U samples j k)) := by
          rw [hsplit]
    _ ≤
        frobNorm
          (fun j k =>
            fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
        frobNorm
          (fun j k =>
            rowSketchGram Bhat j k - uniformRowSampleGram U samples j k) :=
          htri
    _ ≤ uniformRowSampleGramComputedDenDotProductBudget fp U dhat samples +
        uniformRowSampleGramComputedDenScalePerturbBudget fp U dhat samples :=
          add_le_add hdot hscale'
    _ = uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
          unfold uniformRowSampleGramComputedDenFullFpPerturbBudget
          ring

-- ============================================================
-- High-probability Frobenius FP transfer for arbitrary uniform-row inputs
-- ============================================================

/-- Exact iid uniform-row Frobenius event around the exact Gram `UᵀU`.

This event is exact arithmetic: the row law is exact and the sampled Gram is
the exact mathematical average. -/
def uniformRowSampleGramRowGramFrobErrorEvent {m n s : ℕ}
    (U : Fin m → Fin n → ℝ) (η : ℝ) :
    Set (RowTrace m s) :=
  {samples |
    frobNorm
      (fun j k : Fin n => uniformRowSampleGram U samples j k - rowGram U j k) ≤
      η}

/-- Floating-point iid uniform-row Frobenius event around the exact Gram
`UᵀU`, using the exact mathematical denominator in the row-scaling division.

The event charges rounded row divisions and rounded Gram dot products through
the concrete sample-dependent budget. -/
def uniformRowFlSampleGramDotRowGramFrobErrorEvent
    (fp : FPModel) {m n s : ℕ}
    (U : Fin m → Fin n → ℝ) (η : ℝ) :
    Set (RowTrace m s) :=
  {samples |
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s U samples j k - rowGram U j k) ≤
      η + uniformRowSampleGramFullFpPerturbBudget fp s U samples}

/-- Floating-point iid uniform-row Frobenius event around the exact Gram
`UᵀU`, with a computed non-probability denominator.  The event charges
denominator computation, rounded row divisions, and rounded Gram dot products
through the concrete sample-dependent budget. -/
def uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent
    (fp : FPModel) {m n s : ℕ}
    (U : Fin m → Fin n → ℝ) (dhat : ComputedUniformRowScaleDen fp m s)
    (η : ℝ) :
    Set (RowTrace m s) :=
  {samples |
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s U dhat.den samples j k -
          rowGram U j k) ≤
      η + uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples}

/-- The exact Frobenius event transfers to the fully floating-point event with
the exact mathematical row-scale denominator. -/
theorem uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDot
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) :
    uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η ⊆
      uniformRowFlSampleGramDotRowGramFrobErrorEvent (s := s) fp U η := by
  classical
  intro samples hsamples
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDot fp s U samples j k -
        uniformRowSampleGram U samples j k
  let DeltaExact : Fin n → Fin n → ℝ :=
    fun j k => uniformRowSampleGram U samples j k - rowGram U j k
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
    simpa [DeltaFp] using
      fl_uniformRowSampleGramDot_perturb_bound fp U hm hs hγ samples
  have hExact : frobNorm DeltaExact ≤ η := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent, DeltaExact]
      using hsamples
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s U samples j k - rowGram U j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaExact j k) := by
    funext j k
    dsimp [DeltaFp, DeltaExact]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaExact
  have hbound :
      frobNorm
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s U samples j k - rowGram U j k) ≤
        η + uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
    calc
      frobNorm
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s U samples j k - rowGram U j k)
          =
        frobNorm (fun j k : Fin n => DeltaFp j k + DeltaExact j k) := by
          rw [hsplit]
      _ ≤ frobNorm DeltaFp + frobNorm DeltaExact := htri
      _ ≤ η + uniformRowSampleGramFullFpPerturbBudget fp s U samples := by
          linarith
  simpa [uniformRowFlSampleGramDotRowGramFrobErrorEvent] using hbound

/-- The exact Frobenius event transfers to the fully floating-point event with
a computed non-probability row-scale denominator. -/
theorem uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDotWithComputedDen
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) :
    uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η ⊆
      uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent
        (s := s) fp U dhat η := by
  classical
  intro samples hsamples
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen
          fp s U dhat.den samples j k -
        uniformRowSampleGram U samples j k
  let DeltaExact : Fin n → Fin n → ℝ :=
    fun j k => uniformRowSampleGram U samples j k - rowGram U j k
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
    simpa [DeltaFp] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp U dhat hm hs hγ samples
  have hExact : frobNorm DeltaExact ≤ η := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent, DeltaExact]
      using hsamples
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s U dhat.den samples j k -
          rowGram U j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaExact j k) := by
    funext j k
    dsimp [DeltaFp, DeltaExact]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaExact
  have hbound :
      frobNorm
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s U dhat.den samples j k -
            rowGram U j k) ≤
        η + uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
    calc
      frobNorm
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s U dhat.den samples j k -
            rowGram U j k)
          =
        frobNorm (fun j k : Fin n => DeltaFp j k + DeltaExact j k) := by
          rw [hsplit]
      _ ≤ frobNorm DeltaFp + frobNorm DeltaExact := htri
      _ ≤
          η + uniformRowSampleGramComputedDenFullFpPerturbBudget fp U dhat samples := by
          linarith
  simpa [uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent]
    using hbound

/-- High-probability Frobenius/Markov theorem for the fully floating-point
uniform-row sampled Gram of an arbitrary exact matrix, using the exact
mathematical row-scale denominator in the division operation. -/
theorem uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_rowGram_frob_error_le_ge_one_sub
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) (hη : 0 < η) :
    1 - (((m : ℝ) / (s : ℝ)) *
        ∑ i : Fin m, rowNormSq U i ^ 2) / η ^ 2 ≤
      (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
        (uniformRowFlSampleGramDotRowGramFrobErrorEvent fp U η) := by
  have hExact :=
    uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub
      U hm hs η hη
  have hsubset :=
    uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDot
      fp U hm hs hγ η
  have hExactEvent :
      1 - (((m : ℝ) / (s : ℝ)) *
          ∑ i : Fin m, rowNormSq U i ^ 2) / η ^ 2 ≤
        (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
          (uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η) := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent] using hExact
  exact
    hExactEvent.trans
      (FiniteProbability.eventProb_mono
        (uniformRowTraceProbability (m := m) (steps := s) hm) hsubset)

/-- Readable Frobenius-norm simplification of
`uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_rowGram_frob_error_le_ge_one_sub`.
-/
theorem uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_rowGram_frob_error_le_ge_one_sub_frobNorm
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) (hη : 0 < η) :
    1 - (((m : ℝ) / (s : ℝ)) * frobNormSqRect U ^ 2) / η ^ 2 ≤
      (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
        (uniformRowFlSampleGramDotRowGramFrobErrorEvent fp U η) := by
  have hExact :=
    uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
      U hm hs η hη
  have hsubset :=
    uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDot
      fp U hm hs hγ η
  have hExactEvent :
      1 - (((m : ℝ) / (s : ℝ)) * frobNormSqRect U ^ 2) / η ^ 2 ≤
        (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
          (uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η) := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent] using hExact
  exact
    hExactEvent.trans
      (FiniteProbability.eventProb_mono
        (uniformRowTraceProbability (m := m) (steps := s) hm) hsubset)

/-- High-probability Frobenius/Markov theorem for the fully floating-point
uniform-row sampled Gram of an arbitrary exact matrix, with a computed
non-probability row-scale denominator. -/
theorem uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) (hη : 0 < η) :
    1 - (((m : ℝ) / (s : ℝ)) *
        ∑ i : Fin m, rowNormSq U i ^ 2) / η ^ 2 ≤
      (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
        (uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent
          fp U dhat η) := by
  have hExact :=
    uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub
      U hm hs η hη
  have hsubset :=
    uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDotWithComputedDen
      fp U dhat hm hs hγ η
  have hExactEvent :
      1 - (((m : ℝ) / (s : ℝ)) *
          ∑ i : Fin m, rowNormSq U i ^ 2) / η ^ 2 ≤
        (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
          (uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η) := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent] using hExact
  exact
    hExactEvent.trans
      (FiniteProbability.eventProb_mono
        (uniformRowTraceProbability (m := m) (steps := s) hm) hsubset)

/-- Readable Frobenius-norm simplification of the computed-denominator
uniform-row sampled-Gram Frobenius/Markov theorem. -/
theorem uniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub_frobNorm
    (fp : FPModel) {m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (η : ℝ) (hη : 0 < η) :
    1 - (((m : ℝ) / (s : ℝ)) * frobNormSqRect U ^ 2) / η ^ 2 ≤
      (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
        (uniformRowFlSampleGramDotWithComputedDenRowGramFrobErrorEvent
          fp U dhat η) := by
  have hExact :=
    uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
      U hm hs η hη
  have hsubset :=
    uniformRowSampleGramRowGramFrobErrorEvent_subset_flSampleGramDotWithComputedDen
      fp U dhat hm hs hγ η
  have hExactEvent :
      1 - (((m : ℝ) / (s : ℝ)) * frobNormSqRect U ^ 2) / η ^ 2 ≤
        (uniformRowTraceProbability (m := m) (steps := s) hm).eventProb
          (uniformRowSampleGramRowGramFrobErrorEvent (s := s) U η) := by
    simpa [uniformRowSampleGramRowGramFrobErrorEvent] using hExact
  exact
    hExactEvent.trans
      (FiniteProbability.eventProb_mono
        (uniformRowTraceProbability (m := m) (steps := s) hm) hsubset)

-- ============================================================
-- High-probability floating-point transfer for Algorithm 3
-- ============================================================

/-- The floating-point two-sided uniform-row sample-Gram event after
signed-Hadamard preprocessing.  The Loewner radius is the exact sampling radius
plus the explicit sample-dependent FP perturbation budget. -/
def signedHadamardFlUniformRowSampleGramTwoSidedEvent (fp : FPModel)
    {m n s : ℕ} (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (ε : ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    let τ : ℝ := uniformRowSampleGramFullFpPerturbBudget fp s V x.2
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k)}

/-- Floating-point two-sided uniform-row sample-Gram event with a deterministic
FP perturbation radius `τ`. -/
def signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent (fp : FPModel)
    {m n s : ℕ} (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (ε τ : ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k)}

/-- Floating-point two-sided uniform-row sample-Gram event for an implemented
preprocessed basis `Vhat`.  The function `τ` is allowed to depend on both the
Rademacher preprocessing outcome and the sampled row trace, so it can charge
computed Hadamard/sign/basis arithmetic, computed row scaling, and rounded Gram
dot products in one visible radius. -/
def signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
    (fp : FPModel) {m n s : ℕ}
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace m s → ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Constant-radius version of the computed-preprocessed floating-point
uniform-row event. -/
def signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent
    (fp : FPModel) {m n s : ℕ}
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (ε τ : ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
    fp Vhat ε (fun _ => τ)

/-- Floating-point two-sided uniform-row sample-Gram event for an implemented
preprocessed basis `Vhat` when the row-scale denominator `sqrt(s/m)` is also a
computed non-probability quantity. -/
def signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {m n s : ℕ}
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace m s → ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Perturbation event connecting the implemented preprocessed basis `Vhat` to
the exact signed-Hadamard basis `H D_ω U`.  This event is intentionally generic:
it is where a concrete FP implementation of `H`, the diagonal signs, a basis
`U`, or any singular-vector routine must pay its error budget. -/
def signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (τ : RademacherTrace m × RowTrace m s → ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

/-- Constant-radius version of the computed-preprocessed perturbation event. -/
def signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (τ : ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
    fp H U Vhat (fun _ => τ)

/-- Perturbation event connecting the implemented preprocessed basis `Vhat`,
computed row denominator, rounded row scaling, and rounded Gram dot products
to the exact signed-Hadamard basis `H D_ω U`. -/
def signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (τ : RademacherTrace m × RowTrace m s → ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

-- ============================================================
-- Exact right-factor congruence for Algorithm 3 input matrices
-- ============================================================

/-- Right-factor congruence `Cᵀ M C` for finite real matrices.

This is the exact analysis bridge from an orthonormal-column basis `U` to an
Algorithm 3 input matrix factored as `A = U C`. -/
noncomputable def rightGramCongruence {r n : ℕ}
    (M : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ a : Fin r, ∑ b : Fin r, C a j * M a b * C b k

/-- Left preprocessing commutes with a deterministic right factor. -/
theorem preconditionRows_preconditionColumns_assoc {m r n : ℕ}
    (P : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) :
    preconditionRows P (preconditionColumns U C) =
      preconditionColumns (preconditionRows P U) C := by
  classical
  ext i j
  unfold preconditionRows preconditionColumns
  conv_lhs => arg 2; ext k; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Rectangular left preprocessing commutes with a deterministic right factor. -/
theorem preconditionRows_preconditionColumns_assoc_rect {r m q n : ℕ}
    (P : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ) :
    preconditionRows P (preconditionColumns U C) =
      preconditionColumns (preconditionRows P U) C := by
  classical
  ext i j
  unfold preconditionRows preconditionColumns
  conv_lhs => arg 2; ext k; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Quadratic forms commute with the right-factor congruence `Cᵀ M C`. -/
theorem finiteQuadraticForm_rightGramCongruence {r n : ℕ}
    (M : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (x : Fin n → ℝ) :
    finiteQuadraticForm (rightGramCongruence M C) x =
      finiteQuadraticForm M (fun a : Fin r => ∑ j : Fin n, C a j * x j) := by
  classical
  let y : Fin r → ℝ := fun a => ∑ j : Fin n, C a j * x j
  have hmat : ∀ j : Fin n,
      finiteMatVec (rightGramCongruence M C) x j =
        ∑ a : Fin r, C a j * finiteMatVec M y a := by
    intro j
    unfold finiteMatVec rightGramCongruence y
    conv_lhs => arg 2; ext k; rw [Finset.sum_mul]
    conv_lhs => arg 2; ext k; arg 2; ext a; rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    finiteQuadraticForm (rightGramCongruence M C) x
        =
      ∑ j : Fin n, x j * (∑ a : Fin r, C a j * finiteMatVec M y a) := by
        unfold finiteQuadraticForm
        apply Finset.sum_congr rfl
        intro j _
        rw [hmat]
    _ =
      ∑ a : Fin r, (∑ j : Fin n, C a j * x j) * finiteMatVec M y a := by
        conv_lhs => arg 2; ext j; rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ =
      finiteQuadraticForm M y := by
        rfl

/-- Loewner order is preserved by right-factor congruence. -/
theorem finiteLoewnerLe_rightGramCongruence {r n : ℕ}
    {M N : Fin r → Fin r → ℝ} (C : Fin r → Fin n → ℝ)
    (hMN : finiteLoewnerLe M N) :
    finiteLoewnerLe (rightGramCongruence M C)
      (rightGramCongruence N C) := by
  intro x
  rw [finiteQuadraticForm_rightGramCongruence,
    finiteQuadraticForm_rightGramCongruence]
  exact hMN (fun a : Fin r => ∑ j : Fin n, C a j * x j)

/-- Congruence of a scalar identity is the scalar Gram of the right factor. -/
theorem rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram {r n : ℕ}
    (C : Fin r → Fin n → ℝ) (ε : ℝ) :
    rightGramCongruence (fun a b : Fin r => ε * finiteIdMatrix a b) C =
      fun j k : Fin n => ε * rowGram C j k := by
  classical
  ext j k
  unfold rightGramCongruence rowGram finiteIdMatrix
  calc
    ∑ a : Fin r, ∑ b : Fin r, C a j * (ε * if a = b then 1 else 0) * C b k
        =
      ∑ a : Fin r, C a j * (ε * 1) * C a k := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hb
          have hneq : a ≠ b := Ne.symm hb
          simp [hneq]
        · intro hnot
          exact (hnot (Finset.mem_univ a)).elim
    _ = ε * ∑ a : Fin r, C a j * C a k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring

/-- Congruence of the identity is the Gram of the right factor. -/
theorem rightGramCongruence_finiteIdMatrix_eq_rowGram {r n : ℕ}
    (C : Fin r → Fin n → ℝ) :
    rightGramCongruence (finiteIdMatrix : Fin r → Fin r → ℝ) C =
      rowGram C := by
  have h := rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1
  simpa using h

/-- Right-factor congruence is additive. -/
theorem rightGramCongruence_add {r n : ℕ}
    (M N : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ) :
    rightGramCongruence (fun a b => M a b + N a b) C =
      fun j k => rightGramCongruence M C j k +
        rightGramCongruence N C j k := by
  classical
  ext j k
  unfold rightGramCongruence
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Right-factor congruence commutes with negation. -/
theorem rightGramCongruence_neg {r n : ℕ}
    (M : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ) :
    rightGramCongruence (fun a b => -M a b) C =
      fun j k => -rightGramCongruence M C j k := by
  classical
  ext j k
  unfold rightGramCongruence
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Right-factor congruence commutes with subtraction. -/
theorem rightGramCongruence_sub {r n : ℕ}
    (M N : Fin r → Fin r → ℝ) (C : Fin r → Fin n → ℝ) :
    rightGramCongruence (fun a b => M a b - N a b) C =
      fun j k => rightGramCongruence M C j k -
        rightGramCongruence N C j k := by
  classical
  ext j k
  unfold rightGramCongruence
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A two-sided Loewner bound with an arbitrary exact right-hand side is stable
under an additive perturbation whose Frobenius norm is at most `τ`; the
right-hand side gains `τ I`. -/
theorem finiteLoewnerLe_two_sided_add_general_of_frobNorm_le {n : ℕ}
    (Exact Delta Eps : Fin n → Fin n → ℝ) {τ : ℝ}
    (hExactUpper : finiteLoewnerLe Exact Eps)
    (hExactLower : finiteLoewnerLe (fun j k => -Exact j k) Eps)
    (hpert : frobNorm Delta ≤ τ) :
    finiteLoewnerLe
        (fun j k : Fin n => Exact j k + Delta j k)
        (fun j k : Fin n => Eps j k + τ * finiteIdMatrix j k) ∧
      finiteLoewnerLe
        (fun j k : Fin n => -(Exact j k + Delta j k))
        (fun j k : Fin n => Eps j k + τ * finiteIdMatrix j k) := by
  classical
  have hDeltaOp : opNorm2Le Delta τ :=
    opNorm2Le_of_frobNorm_le Delta hpert
  have hDeltaUpper :
      finiteLoewnerLe Delta
        (fun j k : Fin n => τ * finiteIdMatrix j k) := by
    intro x
    rw [finiteQuadraticForm_smul_finiteIdMatrix]
    have habs :=
      abs_vecInnerProduct_matMulVec_le_of_opNorm2Le Delta hDeltaOp x
    have hquad :
        |finiteQuadraticForm Delta x| ≤ τ * finiteVecNorm2Sq x := by
      simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
        finiteVecNorm2Sq, vecNorm2Sq] using habs
    exact (le_abs_self (finiteQuadraticForm Delta x)).trans hquad
  have hDeltaLower :
      finiteLoewnerLe (fun j k : Fin n => -Delta j k)
        (fun j k : Fin n => τ * finiteIdMatrix j k) := by
    intro x
    rw [finiteQuadraticForm_smul_finiteIdMatrix]
    have hDeltaNegOp :
        opNorm2Le (fun j k : Fin n => -Delta j k) τ := by
      have hneg : frobNorm (fun j k : Fin n => -Delta j k) ≤ τ := by
        simpa [frobNorm_neg] using hpert
      exact opNorm2Le_of_frobNorm_le (fun j k : Fin n => -Delta j k) hneg
    have habs :=
      abs_vecInnerProduct_matMulVec_le_of_opNorm2Le
        (fun j k : Fin n => -Delta j k) hDeltaNegOp x
    have hquad :
        |finiteQuadraticForm (fun j k : Fin n => -Delta j k) x| ≤
          τ * finiteVecNorm2Sq x := by
      simpa [finiteQuadraticForm, finiteMatVec, matMulVec,
        finiteVecNorm2Sq, vecNorm2Sq] using habs
    exact (le_abs_self
      (finiteQuadraticForm (fun j k : Fin n => -Delta j k) x)).trans hquad
  have hUpper := finiteLoewnerLe_add hExactUpper hDeltaUpper
  have hLower' := finiteLoewnerLe_add hExactLower hDeltaLower
  have hLower :
      finiteLoewnerLe
        (fun j k : Fin n => -(Exact j k + Delta j k))
        (fun j k : Fin n => Eps j k + τ * finiteIdMatrix j k) := by
    convert hLower' using 1
    ext j k
    ring
  exact ⟨hUpper, hLower⟩

/-- Sampling after a right factor is congruent to sampling the basis first. -/
theorem uniformRowSampleGram_preconditionColumns_eq_rightGramCongruence
    {m r n s : ℕ} (V : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) (samples : RowTrace m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    uniformRowSampleGram (preconditionColumns V C) samples =
      rightGramCongruence (uniformRowSampleGram V samples) C := by
  classical
  have hsketch :
      uniformRowSampleSketch s (preconditionColumns V C) samples =
        preconditionColumns (uniformRowSampleSketch s V samples) C := by
    ext t j
    unfold uniformRowSampleSketch uniformRowSampleIncrement preconditionColumns
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hleft :
      rowSketchGram (uniformRowSampleSketch s (preconditionColumns V C) samples) =
        uniformRowSampleGram (preconditionColumns V C) samples := by
    simpa using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        (preconditionColumns V C) samples hm hs
  have hright :
      rowSketchGram (uniformRowSampleSketch s V samples) =
        uniformRowSampleGram V samples := by
    simpa using
      rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram
        V samples hm hs
  have hgram :
      rowSketchGram
          (preconditionColumns (uniformRowSampleSketch s V samples) C) =
        rightGramCongruence
          (rowSketchGram (uniformRowSampleSketch s V samples)) C := by
    ext j k
    unfold rowSketchGram preconditionColumns rightGramCongruence
    conv_lhs => arg 2; ext i; rw [Finset.sum_mul]
    conv_lhs => arg 2; ext i; arg 2; ext a; rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    uniformRowSampleGram (preconditionColumns V C) samples
        = rowSketchGram
            (uniformRowSampleSketch s (preconditionColumns V C) samples) := by
            exact hleft.symm
    _ = rowSketchGram
            (preconditionColumns (uniformRowSampleSketch s V samples) C) := by
            rw [hsketch]
    _ = rightGramCongruence
            (rowSketchGram (uniformRowSampleSketch s V samples)) C := hgram
    _ = rightGramCongruence (uniformRowSampleGram V samples) C := by
            rw [hright]

/-- Ordinary Grams after a right factor are right-factor congruences. -/
theorem rowGram_preconditionColumns_eq_rightGramCongruence
    {m r n : ℕ} (V : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) :
    rowGram (preconditionColumns V C) =
      rightGramCongruence (rowGram V) C := by
  classical
  ext j k
  unfold rowGram preconditionColumns rightGramCongruence
  conv_lhs => arg 2; ext i; rw [Finset.sum_mul]
  conv_lhs => arg 2; ext i; arg 2; ext a; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact sampled-Gram error for a factored input `A = U C` is the right-factor
congruence of the orthonormal-basis sampled-Gram error. -/
theorem uniformRowSampleGram_factoredInput_error_eq_rightGramCongruence_error
    {m r n s : ℕ} (P : Fin m → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (samples : RowTrace m s) (hU : HasOrthonormalColumns U)
    (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    (fun j k : Fin n =>
        uniformRowSampleGram
            (preconditionRows P (preconditionColumns U C)) samples j k -
          rowGram (preconditionColumns U C) j k) =
      rightGramCongruence
        (fun a b : Fin r =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C := by
  classical
  let V : Fin m → Fin r → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  have hY :
      preconditionRows P A = preconditionColumns V C := by
    simpa [A, V] using preconditionRows_preconditionColumns_assoc P U C
  have hsample :
      uniformRowSampleGram (preconditionRows P A) samples =
        rightGramCongruence (uniformRowSampleGram V samples) C := by
    rw [hY]
    exact
      uniformRowSampleGram_preconditionColumns_eq_rightGramCongruence
        V C samples hm hs
  have hAgram : rowGram A = rowGram C := by
    change rowGram (preconditionColumns U C) = rowGram C
    rw [rowGram_preconditionColumns_eq_rightGramCongruence]
    have hgram : rowGram U = idMatrix r :=
      rowGram_eq_id_of_orthonormal_columns U hU
    ext j k
    have hcong :
        rightGramCongruence
            (fun a b : Fin r => (1 : ℝ) * finiteIdMatrix a b) C j k =
          (fun j k : Fin n => (1 : ℝ) * rowGram C j k) j k := by
      simpa using
        congrFun (congrFun
          (rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1) j) k
    simpa [hgram, idMatrix] using hcong
  ext j k
  calc
    uniformRowSampleGram (preconditionRows P (preconditionColumns U C)) samples j k -
        rowGram (preconditionColumns U C) j k
        =
      rightGramCongruence (uniformRowSampleGram V samples) C j k -
        rightGramCongruence (finiteIdMatrix : Fin r → Fin r → ℝ) C j k := by
        simp [A, V, hsample, hAgram,
          rightGramCongruence_finiteIdMatrix_eq_rowGram]
    _ =
      rightGramCongruence
        (fun a b : Fin r =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C j k := by
        have hsub :=
          congrFun (congrFun
            (rightGramCongruence_sub
              (uniformRowSampleGram V samples)
              (finiteIdMatrix : Fin r → Fin r → ℝ) C) j) k
        simpa [V] using hsub.symm

/-- The right-factor congruence of `ε I` is `ε AᵀA` for a factored input
`A = U C` with exact orthonormal analysis basis. -/
theorem rightGramCongruence_smul_finiteIdMatrix_eq_smul_factoredInputGram
    {m r n : ℕ} (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U) (ε : ℝ) :
    rightGramCongruence (fun a b : Fin r => ε * finiteIdMatrix a b) C =
      fun j k : Fin n => ε * rowGram (preconditionColumns U C) j k := by
  have hAgram : rowGram (preconditionColumns U C) = rowGram C := by
    rw [rowGram_preconditionColumns_eq_rightGramCongruence]
    have hgram : rowGram U = idMatrix r :=
      rowGram_eq_id_of_orthonormal_columns U hU
    ext j k
    have hcong :
        rightGramCongruence
            (fun a b : Fin r => (1 : ℝ) * finiteIdMatrix a b) C j k =
          (fun j k : Fin n => (1 : ℝ) * rowGram C j k) j k := by
      simpa using
        congrFun (congrFun
          (rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1) j) k
    simpa [hgram, idMatrix] using hcong
  rw [rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram]
  rw [hAgram]

/-- Exact two-sided sampled-Gram event for an Algorithm 3 input matrix factored
as `A = U C`, where `U` is the exact orthonormal analysis basis. -/
def signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
    {m r n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) (ε : ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let P : Fin m → Fin m → ℝ :=
      matMul m H (diagMatrix (rademacherSignVector x.1))
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Y : Fin m → Fin n → ℝ := preconditionRows P A
    finiteLoewnerLe
      (fun j k : Fin n => uniformRowSampleGram Y x.2 j k - rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n => -(uniformRowSampleGram Y x.2 j k - rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k)}

/-- The orthonormal-basis SRHT sample-Gram event implies the corresponding
factored-input event for `A = U C`. -/
theorem signedHadamardUniformRowSampleGramTwoSidedEvent_subset_factoredInput
    {m r n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) (ε : ℝ)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) (hs : 0 < (s : ℝ)) :
    signedHadamardUniformRowSampleGramTwoSidedEvent
        (m := m) (n := r) (s := s) H U ε ⊆
      signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
        (m := m) (r := r) (n := n) (s := s) H U C ε := by
  classical
  intro x hx
  let P : Fin m → Fin m → ℝ :=
    matMul m H (diagMatrix (rademacherSignVector x.1))
  let V : Fin m → Fin r → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  let Y : Fin m → Fin n → ℝ := preconditionRows P A
  let ExactU : Fin r → Fin r → ℝ :=
    fun a b => uniformRowSampleGram V x.2 a b - finiteIdMatrix a b
  let ExactA : Fin n → Fin n → ℝ :=
    fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
  let EpsU : Fin r → Fin r → ℝ :=
    fun a b => ε * finiteIdMatrix a b
  let EpsA : Fin n → Fin n → ℝ :=
    fun j k => ε * rowGram A j k
  have hxU :
      finiteLoewnerLe ExactU EpsU ∧
      finiteLoewnerLe (fun a b : Fin r => -ExactU a b) EpsU := by
    simpa [signedHadamardUniformRowSampleGramTwoSidedEvent, P, V, ExactU, EpsU]
      using hx
  have hErr :
      ExactA = rightGramCongruence ExactU C := by
    simpa [P, V, A, Y, ExactU, ExactA] using
      uniformRowSampleGram_factoredInput_error_eq_rightGramCongruence_error
        P U C x.2 hU hm hs
  have hEps :
      rightGramCongruence EpsU C = EpsA := by
    simpa [A, EpsU, EpsA] using
      rightGramCongruence_smul_finiteIdMatrix_eq_smul_factoredInputGram
        U C hU ε
  have hUpperBase :
      finiteLoewnerLe (rightGramCongruence ExactU C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.1
  have hLowerBase :
      finiteLoewnerLe
        (rightGramCongruence (fun a b : Fin r => -ExactU a b) C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.2
  have hUpper : finiteLoewnerLe ExactA EpsA := by
    rw [hErr, ← hEps]
    exact hUpperBase
  have hNegErr :
      (fun j k : Fin n => -ExactA j k) =
        rightGramCongruence (fun a b : Fin r => -ExactU a b) C := by
    rw [hErr]
    rw [rightGramCongruence_neg]
  have hLower : finiteLoewnerLe (fun j k : Fin n => -ExactA j k) EpsA := by
    rw [hNegErr, ← hEps]
    exact hLowerBase
  simpa [signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent,
    P, A, Y, ExactA, EpsA] using And.intro hUpper hLower

/-- Source-sharp logarithmic SRHT preprocessing plus uniform row sampling for
the actual Algorithm 3 input matrix `A = U C`.  The random signs and uniform row
law remain exact; `U` and `C` are exact analysis-only factors. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    {m r n s : ℕ} (H : Fin m → Fin m → ℝ)
    (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
          H U C ε) := by
  have hExactU :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
    simpa using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
        hsampleBudget
  exact hExactU.trans
    (FiniteProbability.eventProb_mono
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm)
      (signedHadamardUniformRowSampleGramTwoSidedEvent_subset_factoredInput
        (m := m) (r := r) (n := n) (s := s) H U C ε hU hm hs))

/-- Fully floating-point computed-input event for Algorithm 3 on a factored
input `A = U C`, using a computed uniform row-scale denominator. -/
def signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {m r n s : ℕ}
    (U : Fin m → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace m s → ℝ) :
    Set (RademacherTrace m × RowTrace m s) :=
  {x |
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k)}

/-- Transfer an exact factored-input Algorithm 3 event and a concrete
computed-input perturbation event to the fully floating-point sampled Gram. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {m r n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε))
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H (preconditionColumns U C) Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C Vhat dhat ε τ) := by
  classical
  let Pprob := signedHadamardUniformRowTraceProbability (m := m) (s := s) hm
  let E : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent H U C ε
  let F : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp H (preconditionColumns U C) Vhat dhat τ
  let G : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp U C Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ Pprob.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Pprob E F δExact δComp (by simpa [Pprob, E] using hExact)
        (by simpa [Pprob, F] using hComp)
  have hsubset : E ∩ F ⊆ G := by
    intro x hx
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pmat : Fin m → Fin m → ℝ :=
      matMul m H (diagMatrix (rademacherSignVector x.1))
    let Y : Fin m → Fin n → ℝ := preconditionRows Pmat A
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram Y x.2 j k
    let Eps : Fin n → Fin n → ℝ :=
      fun j k => ε * rowGram A j k
    have hxExact :
        finiteLoewnerLe Exact Eps ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k) Eps := by
      simpa [E, signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent,
        A, Pmat, Y, Exact, Eps] using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        A, Pmat, Y, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_general_of_frobNorm_le
        Exact Delta Eps hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    exact ⟨hUpper, hLower⟩
  exact hInter.trans (by
    simpa [Pprob, G] using FiniteProbability.eventProb_mono Pprob hsubset)

/-- If `U` has orthonormal columns, the Gram of `U C` is the Gram of `C`. -/
theorem rowGram_preconditionColumns_eq_rowGram_of_orthonormal
    {m r n : ℕ} (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ) (hU : HasOrthonormalColumns U) :
    rowGram (preconditionColumns U C) = rowGram C := by
  rw [rowGram_preconditionColumns_eq_rightGramCongruence]
  have hgram : rowGram U = idMatrix r :=
    rowGram_eq_id_of_orthonormal_columns U hU
  ext j k
  have hcong :
      rightGramCongruence (fun a b : Fin r => (1 : ℝ) * finiteIdMatrix a b) C
        j k =
      (fun j k : Fin n => (1 : ℝ) * rowGram C j k) j k := by
    simpa using
      congrFun (congrFun
        (rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1) j) k
  simpa [hgram, idMatrix] using hcong

/-- Implemented signed-Hadamard preconditioned basis formed by a computed or
stored left preconditioner certificate and one rounded matrix product. -/
noncomputable def signedHadamardComputedLeftPreconditionedBasis
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (ω : RademacherTrace m) : Fin m → Fin n → ℝ :=
  fl_preconditionRowsWithComputedLeft fp (Pihat ω) U

/-- Entrywise basis-error budget for
`signedHadamardComputedLeftPreconditionedBasis`.  It charges both the
generated/stored preconditioner-entry errors in `Pihat` and the rounded matrix
product used to form `Vhat = fl(Pihat * U)`. -/
noncomputable def signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
        (matMul m H (diagMatrix (rademacherSignVector ω))))
    (ω : RademacherTrace m) (i : Fin m) (j : Fin n) : ℝ :=
  flPreconditionRowsWithComputedLeftEntryErrorBudget fp (Pihat ω) U i j

/-- Implemented signed-Hadamard preconditioned basis formed from both a
computed/stored left preconditioner and a computed/stored input basis.  This
is the Algorithm 3 surface for singular vectors or bases that are computed
before preprocessing. -/
noncomputable def signedHadamardComputedLeftInputPreconditionedBasis
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (ω : RademacherTrace m) : Fin m → Fin n → ℝ :=
  fl_preconditionRowsWithComputedLeftAndInput fp (Pihat ω) Uhat

/-- Entrywise basis-error budget for
`signedHadamardComputedLeftInputPreconditionedBasis`.  It charges
generated/stored preconditioner-entry errors, computed input-basis errors, and
the rounded matrix product used to form `Vhat = fl(Pihat * Uhat)`. -/
noncomputable def signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
        (matMul m H (diagMatrix (rademacherSignVector ω))))
    (ω : RademacherTrace m) (i : Fin m) (j : Fin n) : ℝ :=
  flPreconditionRowsWithComputedLeftInputEntryErrorBudget
    fp (Pihat ω) Uhat i j

/-- Exact/stored signed-Hadamard preconditioner certificate.  This instantiates
the computed-preconditioner surface when the realized `H D_omega` matrix is
available exactly; the subsequent `Vhat = fl((H D_omega) U)` product is still
charged by floating-point matrix multiplication. -/
noncomputable def signedHadamardExactStoredPreconditioner
    (fp : FPModel) {m : ℕ} (H : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) :
    ComputedPreconditioner fp
      (matMul m H (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.exact fp
    (matMul m H (diagMatrix (rademacherSignVector ω)))

/-- Exact supplied signed-Hadamard factors with rounded preconditioner
formation.  The Hadamard/FHT table `H` and realized Rademacher sign vector are
treated as exact mathematical inputs, while the realized preconditioner
`H * diag(sign)` is produced by a rounded matrix product. -/
noncomputable def signedHadamardExactFactorPreconditioner
    (fp : FPModel) {m : ℕ} (H : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (matMul m H (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardExactFactors
    fp H (rademacherSignVector ω) hγm

/-- Signed-Hadamard preconditioner from a supplied sign-pattern table with
rounded `sqrt (1 / m)` scaling.  The Rademacher sign law is exact, while the
scaled table and the realized `H D_omega` product are represented by computed
certificates. -/
noncomputable def signedHadamardScaledPatternPreconditioner
    (fp : FPModel) {m : ℕ} (S : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (matMul m (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardScaledPattern
    fp S (rademacherSignVector ω) hγm

/-- Signed-Hadamard preconditioner from a supplied sign-pattern table with
rounded `sqrt (1 / m)` scaling and rounded storage of the realized
Rademacher signs.  The Rademacher law itself is exact; this certificate only
charges the non-probability sign-storage/copy arithmetic before the diagonal is
formed and multiplied into the scaled table. -/
noncomputable def signedHadamardScaledPatternStoredSignPreconditioner
    (fp : FPModel) {m : ℕ} (S : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (matMul m (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardScaledPatternStoredSign
    fp S (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- Signed-Hadamard preconditioner from a supplied sign-pattern table with
rounded `sqrt (1 / m)` scaling and rounded add-zero storage of the realized
Rademacher signs.  The Rademacher law itself is exact; this certificate only
charges the non-probability sign-storage/copy arithmetic `fl_add sign_i 0`
before the diagonal is formed and multiplied into the scaled table. -/
noncomputable def signedHadamardScaledPatternStoredSignAddZeroRightPreconditioner
    (fp : FPModel) {m : ℕ} (S : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (matMul m (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardScaledPatternStoredSignAddZeroRight
    fp S (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- Signed-Hadamard preconditioner from a supplied sign-pattern table with
rounded `sqrt (1 / m)` scaling and rounded subtract-zero storage of the
realized Rademacher signs.  The Rademacher law itself is exact; this
certificate only charges the non-probability sign-storage/copy arithmetic
`fl_sub sign_i 0` before the diagonal is formed and multiplied into the scaled
table. -/
noncomputable def signedHadamardScaledPatternStoredSignSubZeroRightPreconditioner
    (fp : FPModel) {m : ℕ} (S : Fin m → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (matMul m (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardScaledPatternStoredSignSubZeroRight
    fp S (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- Signed-Hadamard preconditioner from the concrete generated
Sylvester/Walsh sign-pattern table with rounded `sqrt (1 / 2^p)` scaling.
The bit-parity table is generated exactly; the FP budget starts with scale
formation and the rounded `H D_omega` product. -/
noncomputable def signedHadamardSylvesterPatternPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p))
    (hγm : gammaValid fp (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterPattern
    fp p (rademacherSignVector ω) hγm

/-- Signed-Hadamard preconditioner computed by applying the rounded generated
Sylvester/Walsh FHT schedule to the diagonal Rademacher sign matrix.

This is the fast-schedule implementation path for `H D_ω`: the Rademacher law
is exact, while the generated FHT butterfly arithmetic and rounded
`sqrt(1/2^p)` scale are charged by the `ComputedPreconditioner` certificate. -/
noncomputable def signedHadamardSylvesterFhtSchedulePreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtSchedule
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with explicit rounded
`fl_add y_i 0` storage/copy after every FHT pair update.  The Rademacher law
itself remains exact; this charges only non-probability FHT writeback
arithmetic in addition to butterfly arithmetic and rounded normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredAddZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredAddZeroRight
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with explicit rounded
`fl_mul y_i 1` storage/copy after every FHT pair update.  The Rademacher law
itself remains exact; this charges only non-probability FHT writeback
arithmetic in addition to butterfly arithmetic and rounded normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredMulOnePreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredMulOne
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with explicit rounded
`fl_sub y_i 0` storage/copy after every FHT pair update.  The Rademacher law
itself remains exact; this charges only non-probability FHT writeback
arithmetic in addition to butterfly arithmetic and rounded normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSubZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredSubZeroRight
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_add y_i 0`
storage/copy only on the two outputs modified by each FHT pair update.  The
Rademacher law itself remains exact; this charges only non-probability FHT
writeback arithmetic in addition to butterfly arithmetic and rounded
normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRight
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul y_i 1`
storage/copy only on the two outputs modified by each FHT pair update.  The
Rademacher law itself remains exact; this charges only non-probability FHT
writeback arithmetic in addition to butterfly arithmetic and rounded
normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleModifiedStoredMulOnePreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredMulOne
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_sub y_i 0`
storage/copy only on the two outputs modified by each FHT pair update.  The
Rademacher law itself remains exact; this charges only non-probability FHT
writeback arithmetic in addition to butterfly arithmetic and rounded
normalization. -/
noncomputable def signedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRight
    fp p (ComputedVector.exact fp (rademacherSignVector ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs before the FHT stages are applied to
the diagonal input.  The Rademacher law itself remains exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtSchedule
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and explicit rounded `fl_add y_i 0`
storage/copy after every FHT pair update.  Probability laws remain exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredAddZeroRight
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and explicit rounded `fl_mul y_i 1`
storage/copy after every FHT pair update.  Probability laws remain exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignStoredMulOnePreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredMulOne
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and explicit rounded `fl_sub y_i 0`
storage/copy after every FHT pair update.  Probability laws remain exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignStoredSubZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleStoredSubZeroRight
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and rounded `fl_add y_i 0`
storage/copy only on modified FHT pair outputs.  Probability laws remain
exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRight
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and rounded `fl_mul y_i 1`
storage/copy only on modified FHT pair outputs.  Probability laws remain
exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredMulOnePreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredMulOne
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Fast generated-FHT `H D_ω` preconditioner with rounded `fl_mul sign_i 1`
storage of the realized Rademacher signs and rounded `fl_sub y_i 0`
storage/copy only on modified FHT pair outputs.  Probability laws remain
exact. -/
noncomputable def signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRight
    fp p
      (ComputedVector.flStoredSign fp
        (rademacherSignVector ω) (rademacherSignVector_abs ω))

/-- Generated Sylvester/Walsh sign-pattern preconditioner with rounded
`fl_mul sign_i 1` storage of the realized Rademacher signs. -/
noncomputable def signedHadamardSylvesterPatternStoredSignPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p))
    (hγm : gammaValid fp (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSign
    fp p (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- Generated Sylvester/Walsh sign-pattern preconditioner with rounded
`fl_add sign_i 0` storage of the realized Rademacher signs. -/
noncomputable def signedHadamardSylvesterPatternStoredSignAddZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p))
    (hγm : gammaValid fp (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSignAddZeroRight
    fp p (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- Generated Sylvester/Walsh sign-pattern preconditioner with rounded
`fl_sub sign_i 0` storage of the realized Rademacher signs. -/
noncomputable def signedHadamardSylvesterPatternStoredSignSubZeroRightPreconditioner
    (fp : FPModel) {p : ℕ} (ω : RademacherTrace (2 ^ p))
    (hγm : gammaValid fp (2 ^ p)) :
    ComputedPreconditioner fp
      (matMul (2 ^ p)
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        (diagMatrix (rademacherSignVector ω))) :=
  ComputedPreconditioner.flSignedHadamardSylvesterPatternStoredSignSubZeroRight
    fp p (rademacherSignVector ω) (rademacherSignVector_abs ω) hγm

/-- With an exact/stored signed-Hadamard preconditioner certificate, the
computed-left basis-entry budget contains no transform-storage term. -/
@[simp] theorem signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget_exactStored
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (ω : RademacherTrace m) (i : Fin m) (j : Fin n) :
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget fp H U
        (signedHadamardExactStoredPreconditioner fp H) ω i j =
      gamma fp m *
        ∑ k : Fin m,
          |(matMul m H (diagMatrix (rademacherSignVector ω))) i k| *
            |U k j| := by
  simp [signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget,
    signedHadamardExactStoredPreconditioner]

/-- With an exact input basis certificate, the computed-left/input budget
reduces to the existing computed-left basis-entry budget. -/
@[simp] theorem signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget_exactInput
    (fp : FPModel) {m n : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (ω : RademacherTrace m) (i : Fin m) (j : Fin n) :
    signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
        fp H (ComputedMatrix.exact fp U) Pihat ω i j =
      signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
        fp H U Pihat ω i j := by
  simp [signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget,
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget]

/-- Sample-dependent perturbation budget for the concrete computed-left
preconditioned Algorithm 3 path.  The first term charges rounded row scaling
and sampled-Gram dot products after `Vhat` has been formed.  The second term
charges the difference between the exact sampled Gram of `Vhat` and that of the
ideal signed-Hadamard basis `H D_ω U`. -/
noncomputable def signedHadamardComputedLeftUniformRowPerturbBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (x : RademacherTrace m × RowTrace m s) : ℝ :=
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
      fp H U Pihat x.1
  uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for the concrete computed-left
preconditioned Algorithm 3 path when the uniform row-scale denominator is
computed.  It charges the computed denominator, rounded row divisions, rounded
Gram dot products, and the basis drift from `Vhat` back to the exact
`H D_ω U`. -/
noncomputable def signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (dhat : ComputedUniformRowScaleDen fp m s)
    (x : RademacherTrace m × RowTrace m s) : ℝ :=
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
      fp H U Pihat x.1
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- The concrete computed-left preconditioned basis satisfies the generic
computed-`Vhat` perturbation event with probability one under the joint
signed-Hadamard/uniform-row law. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp H U
        (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
        (signedHadamardComputedLeftUniformRowPerturbBudget fp H U Pihat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
      fp H U Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDot fp s Vhat x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E, signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftEntryErrorBudget_nonneg
          fp (Pihat x.1) U hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedHadamardComputedLeftPreconditionedBasis,
      signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeft_entry_error_budget_bound
          fp (Pihat x.1) U hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDot_perturb_bound fp Vhat hm hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hm hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedHadamardComputedLeftUniformRowPerturbBudget fp H U Pihat x := by
        simp [signedHadamardComputedLeftUniformRowPerturbBudget, V, Vhat, E]

/-- The concrete computed-left preconditioned basis with a computed uniform
row-scale denominator satisfies the computed-denominator perturbation event
with probability one under the joint signed-Hadamard/uniform-row law. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp H U
        (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
        dhat
        (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
          fp H U Pihat dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget
      fp H U Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E, signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftEntryErrorBudget_nonneg
          fp (Pihat x.1) U hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedHadamardComputedLeftPreconditionedBasis,
      signedHadamardComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeft_entry_error_budget_bound
          fp (Pihat x.1) U hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hm hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hm hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
          fp H U Pihat dhat x := by
        simp [signedHadamardComputedLeftUniformRowComputedDenPerturbBudget,
          V, Vhat, E]

/-- Floating-point two-sided sample-Gram event for an implemented finite
signed-mixing preprocessed basis.  Here the sign law and the uniform row trace
are exact probability laws; the matrix entries in `Vhat`, row scaling, and Gram
dot products are the computed non-probability quantities. -/
def signedMixingComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
    (fp : FPModel) {r m n s : ℕ}
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace r s → ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Floating-point two-sided sample-Gram event for an implemented finite
signed-mixing preprocessed basis when the uniform row-scale denominator
`sqrt(s/r)` is also computed. -/
def signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {r m n s : ℕ}
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace r s → ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Perturbation event connecting an implemented finite signed-mixing
preprocessed basis `Vhat` to the exact analysis basis
`(G diag(ω)) U`. -/
def signedMixingComputedPreconditionedFlUniformRowPerturbEvent
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (τ : RademacherTrace m × RowTrace r s → ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (signedMixingRows G (rademacherSignVector x.1)) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

/-- Perturbation event for finite signed mixing with a computed uniform
row-scale denominator. -/
def signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (τ : RademacherTrace m × RowTrace r s → ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (signedMixingRows G (rademacherSignVector x.1)) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

/-- Implemented finite signed-mixing preconditioned basis formed by a computed
or stored left preconditioner certificate and one rounded matrix product. -/
noncomputable def signedMixingComputedLeftPreconditionedBasis
    (fp : FPModel) {r m n : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (ω : RademacherTrace m) : Fin r → Fin n → ℝ :=
  fl_preconditionRowsWithComputedLeft fp (Pihat ω) U

/-- Entrywise basis-error budget for
`signedMixingComputedLeftPreconditionedBasis`.  It charges both the computed
preconditioner-entry errors in `Pihat` and the rounded matrix product used to
form `Vhat = fl(Pihat * U)`. -/
noncomputable def signedMixingComputedLeftPreconditionedBasisEntryErrorBudget
    (fp : FPModel) {r m n : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (ω : RademacherTrace m) (i : Fin r) (j : Fin n) : ℝ :=
  flPreconditionRowsWithComputedLeftEntryErrorBudget fp (Pihat ω) U i j

/-- Exact/stored signed-mixing preconditioner certificate.  The subsequent
`Vhat = fl(Pihat * U)` product is still charged. -/
noncomputable def signedMixingExactStoredPreconditioner
    (fp : FPModel) {r m : ℕ} (G : Fin r → Fin m → ℝ)
    (ω : RademacherTrace m) :
    ComputedPreconditioner fp
      (signedMixingRows G (rademacherSignVector ω)) :=
  ComputedPreconditioner.exact fp
    (signedMixingRows G (rademacherSignVector ω))

/-- Exact supplied finite signed-mixing factors with rounded preconditioner
formation.  The deterministic table `G` and exact Rademacher sign vector are
mathematical inputs; forming `G * diag(sign)` is a rounded matrix product. -/
noncomputable def signedMixingExactFactorPreconditioner
    (fp : FPModel) {r m : ℕ} (G : Fin r → Fin m → ℝ)
    (ω : RademacherTrace m) (hγm : gammaValid fp m) :
    ComputedPreconditioner fp
      (signedMixingRows G (rademacherSignVector ω)) :=
  ComputedPreconditioner.flSignedMixingExactFactors
    fp G (rademacherSignVector ω) hγm

/-- With an exact/stored signed-mixing preconditioner certificate, the
computed-left basis-entry budget contains no preconditioner-storage term. -/
@[simp] theorem signedMixingComputedLeftPreconditionedBasisEntryErrorBudget_exactStored
    (fp : FPModel) {r m n : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (ω : RademacherTrace m) (i : Fin r) (j : Fin n) :
    signedMixingComputedLeftPreconditionedBasisEntryErrorBudget fp G U
        (signedMixingExactStoredPreconditioner fp G) ω i j =
      gamma fp m *
        ∑ k : Fin m,
          |signedMixingRows G (rademacherSignVector ω) i k| *
            |U k j| := by
  simp [signedMixingComputedLeftPreconditionedBasisEntryErrorBudget,
    signedMixingExactStoredPreconditioner]

/-- Sample-dependent perturbation budget for the concrete computed-left finite
signed-mixing path.  It charges rounded row scaling and Gram dot products after
`Vhat` has been formed, plus the sampled-Gram drift from `Vhat` back to the
exact basis `(G diag(ω)) U`. -/
noncomputable def signedMixingComputedLeftUniformRowPerturbBudget
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (x : RademacherTrace m × RowTrace r s) : ℝ :=
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (signedMixingRows G (rademacherSignVector x.1)) U
  let Vhat : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1
  let E : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasisEntryErrorBudget
      fp G U Pihat x.1
  uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for the concrete computed-left finite
signed-mixing path when the uniform row-scale denominator `sqrt(s/r)` is
computed. -/
noncomputable def signedMixingComputedLeftUniformRowComputedDenPerturbBudget
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (x : RademacherTrace m × RowTrace r s) : ℝ :=
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (signedMixingRows G (rademacherSignVector x.1)) U
  let Vhat : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1
  let E : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasisEntryErrorBudget
      fp G U Pihat x.1
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- The concrete computed-left finite signed-mixing basis satisfies the
generic computed-`Vhat` perturbation event with probability one. -/
theorem signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (signedMixingComputedPreconditionedFlUniformRowPerturbEvent
        fp G U
        (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
        (signedMixingComputedLeftUniformRowPerturbBudget fp G U Pihat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (signedMixingRows G (rademacherSignVector x.1)) U
  let Vhat : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1
  let E : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasisEntryErrorBudget
      fp G U Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDot fp s Vhat x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E, signedMixingComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftEntryErrorBudget_nonneg
          fp (Pihat x.1) U hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedMixingComputedLeftPreconditionedBasis,
      signedMixingComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeft_entry_error_budget_bound
          fp (Pihat x.1) U hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDot_perturb_bound fp Vhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (signedMixingRows G (rademacherSignVector x.1)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (signedMixingRows G (rademacherSignVector x.1)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedMixingComputedLeftUniformRowPerturbBudget fp G U Pihat x := by
        simp [signedMixingComputedLeftUniformRowPerturbBudget, V, Vhat, E]

/-- The concrete computed-left finite signed-mixing basis satisfies the
computed-denominator perturbation event with probability one. -/
theorem signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp G U
        (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
        dhat
        (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
          fp G U Pihat dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (signedMixingRows G (rademacherSignVector x.1)) U
  let Vhat : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1
  let E : Fin r → Fin n → ℝ :=
    signedMixingComputedLeftPreconditionedBasisEntryErrorBudget
      fp G U Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E, signedMixingComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftEntryErrorBudget_nonneg
          fp (Pihat x.1) U hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedMixingComputedLeftPreconditionedBasis,
      signedMixingComputedLeftPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeft_entry_error_budget_bound
          fp (Pihat x.1) U hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (signedMixingRows G (rademacherSignVector x.1)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (signedMixingRows G (rademacherSignVector x.1)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedMixingComputedLeftUniformRowComputedDenPerturbBudget
          fp G U Pihat dhat x := by
        simp [signedMixingComputedLeftUniformRowComputedDenPerturbBudget,
          V, Vhat, E]

/-- Generic exact-to-computed transfer for finite signed mixing with the exact
mathematical row-scale denominator.  The preprocessing, row divisions, and Gram
arithmetic are charged by the perturbation event. -/
theorem signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (hr : 0 < r) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace r s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowSampleGramTwoSidedEvent G U ε))
    (hComp :
      1 - δComp ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbEvent
            fp G U Vhat τ)) :
    1 - (δExact + δComp) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp Vhat ε τ) := by
  classical
  let P := signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let E : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingUniformRowSampleGramTwoSidedEvent G U ε
  let F : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFlUniformRowPerturbEvent
      fp G U Vhat τ
  let M : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
      fp Vhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F δExact δComp (by simpa [P, E] using hExact)
        (by simpa [P, F] using hComp)
  have hsubset : E ∩ F ⊆ M := by
    intro x hx
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (signedMixingRows G (rademacherSignVector x.1)) U
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxExact :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [E, signedMixingUniformRowSampleGramTwoSidedEvent, V, Exact]
        using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F, signedMixingComputedPreconditionedFlUniformRowPerturbEvent,
        V, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
            finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [M,
      signedMixingComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent]
      using And.intro hUpper hLower
  exact hInter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Generic exact-to-computed transfer for finite signed mixing with a computed
uniform row-scale denominator. -/
theorem signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace r s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowSampleGramTwoSidedEvent G U ε))
    (hComp :
      1 - δComp ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp G U Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp Vhat dhat ε τ) := by
  classical
  let P := signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let E : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingUniformRowSampleGramTwoSidedEvent G U ε
  let F : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp G U Vhat dhat τ
  let M : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F δExact δComp (by simpa [P, E] using hExact)
        (by simpa [P, F] using hComp)
  have hsubset : E ∩ F ⊆ M := by
    intro x hx
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (signedMixingRows G (rademacherSignVector x.1)) U
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxExact :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [E, signedMixingUniformRowSampleGramTwoSidedEvent, V, Exact]
        using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        V, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [M,
      signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent]
      using And.intro hUpper hLower
  exact hInter.trans (FiniteProbability.eventProb_mono P hsubset)

/- ============================================================
-- CountSketch computed preprocessing plus uniform-row FP transfer
-- ============================================================ -/

/-- Floating-point two-sided sample-Gram event for an implemented CountSketch
preprocessed basis.  The exact hash/sign and uniform row laws are probability
objects; `Vhat`, row scaling, and Gram dot products are computed
non-probability quantities charged by `τ`. -/
def countSketchComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
    (fp : FPModel) {r m n s : ℕ}
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (ε : ℝ)
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Floating-point two-sided sample-Gram event for an implemented CountSketch
preprocessed basis when the uniform row-scale denominator `sqrt(s/r)` is also
computed. -/
def countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {r m n s : ℕ}
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ε : ℝ)
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k)
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          finiteIdMatrix j k))
      (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k)}

/-- Perturbation event connecting an implemented CountSketch-preconditioned
basis `Vhat` to the exact analysis basis `S_{h,\omega} U`. -/
def countSketchComputedPreconditionedFlUniformRowPerturbEvent
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

/-- Perturbation event for CountSketch preprocessing with a computed uniform
row-scale denominator. -/
def countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k) ≤ τ x}

/-- Implemented sparse CountSketch-preconditioned basis: exact hash/sign
selection, rounded signed products, and rounded bucket accumulation. -/
noncomputable def countSketchSparseComputedPreconditionedBasis
    (fp : FPModel) {r m n : ℕ} (U : Fin m → Fin n → ℝ)
    (x : CountSketchHash r m × RademacherTrace m) : Fin r → Fin n → ℝ :=
  fl_countSketchSparseApply fp x.1 (rademacherSignVector x.2) U

/-- Implemented sparse CountSketch-preconditioned basis when the realized
Rademacher signs are first stored or copied in floating point before the
sparse bucket accumulation.  The hash/sign probability law is exact; only the
stored sign table and subsequent arithmetic are computed quantities. -/
noncomputable def countSketchSparseComputedPreconditionedBasisWithStoredSign
    (fp : FPModel) {r m n : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (x : CountSketchHash r m × RademacherTrace m) : Fin r → Fin n → ℝ :=
  fl_countSketchSparseApplyWithStoredSign
    fp x.1 (rademacherSignVector x.2) (storedSignOf x.2) U

/-- Implemented sparse CountSketch-preconditioned basis when realized
Rademacher signs are stored or copied in floating point and each realized
hash bucket is traversed in an exact fixed order.  The order is a discrete
memory-layout choice, not a floating-point computation. -/
noncomputable def countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
    (fp : FPModel) {r m n : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (x : CountSketchHash r m × RademacherTrace m) : Fin r → Fin n → ℝ :=
  fl_countSketchSparseApplyWithStoredSignPermuted
    fp x.1 (rademacherSignVector x.2) (storedSignOf x.2) U (orderOf x.1)

/-- Implemented sparse CountSketch-preconditioned basis when realized
Rademacher signs are stored or copied in floating point and each realized
hash bucket is accumulated by an exact supplied binary summation tree.  The
tree shape is a discrete implementation choice, not a floating-point real
quantity. -/
noncomputable def countSketchSparseComputedPreconditionedBasisWithStoredSignTree
    (fp : FPModel) {r m n : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (x : CountSketchHash r m × RademacherTrace m) : Fin r → Fin n → ℝ :=
  fl_countSketchSparseApplyWithStoredSignTree
    fp x.1 (rademacherSignVector x.2) (storedSignOf x.2) U (treeOf x.1)

/-- Sample-dependent perturbation budget for sparse computed CountSketch
preprocessing followed by exact-denominator rounded uniform row sampling. -/
noncomputable def countSketchSparseUniformRowPerturbBudget
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s) : ℝ :=
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasis fp U x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyFpAbsBudget
      fp x.1.1 (rademacherSignVector x.1.2) U
  uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for sparse computed CountSketch
preprocessing followed by computed-denominator rounded uniform row sampling. -/
noncomputable def countSketchSparseUniformRowComputedDenPerturbBudget
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s) : ℝ :=
  let V : Fin r → Fin n → ℝ :=
    preconditionRows
      (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasis fp U x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyFpAbsBudget
      fp x.1.1 (rademacherSignVector x.1.2) U
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for stored-sign sparse computed
CountSketch preprocessing followed by computed-denominator rounded uniform row
sampling.  This budget explicitly includes sign storage/copying, rounded signed
products, bucket accumulation, the computed denominator, sampled-row divisions,
and sampled-Gram dot products. -/
noncomputable def countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s) : ℝ :=
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows x.1.1 sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSign
      fp U storedSignOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignFpAbsBudget
      fp x.1.1 sign signhat U
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for stored-sign sparse computed
CountSketch preprocessing with exact per-bucket traversal orders, followed by
computed-denominator rounded uniform row sampling.  This budget charges sign
storage/copying, rounded signed products, bucket accumulation in the selected
order, the computed denominator, sampled-row divisions, and sampled-Gram dot
products. -/
noncomputable def countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s) : ℝ :=
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows x.1.1 sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
      fp U storedSignOf orderOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignPermutedFpAbsBudget
      fp x.1.1 sign signhat U (orderOf x.1.1)
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- Sample-dependent perturbation budget for stored-sign sparse computed
CountSketch preprocessing with tree-reduced bucket accumulations, followed by
computed-denominator rounded uniform row sampling.  This budget charges sign
storage/copying, rounded signed products, tree-depth bucket accumulation, the
computed denominator, sampled-row divisions, and sampled-Gram dot products. -/
noncomputable def countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s) : ℝ :=
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows x.1.1 sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSignTree
      fp U storedSignOf treeOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignTreeFpAbsBudget
      fp x.1.1 sign signhat U (treeOf x.1.1)
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- The sparse computed CountSketch basis satisfies the exact-denominator
uniform-row perturbation event with probability one. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (countSketchComputedPreconditionedFlUniformRowPerturbEvent
        fp U
        (countSketchSparseComputedPreconditionedBasis fp U)
        (countSketchSparseUniformRowPerturbBudget fp U)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let hash : CountSketchHash r m := x.1.1
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows hash sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasis fp U x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyFpAbsBudget fp hash sign U
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDot fp s Vhat x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hb : ∀ i : Fin r, gammaValid fp (countSketchBucketSize hash i) := by
    intro i
    exact gammaValid_mono fp (countSketchBucketSize_le hash i) hγm
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    have hcoeff_nonneg :
        0 ≤ fp.u + gamma fp (countSketchBucketSize hash i) +
            fp.u * gamma fp (countSketchBucketSize hash i) := by
      exact add_nonneg
        (add_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
        (mul_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
    have hsum_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          |sign (countSketchBucketIndex hash i t)| *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    simpa [E, countSketchSparseApplyFpAbsBudget,
      countSketchSparseApplyEntryFpAbsBudget] using
      mul_nonneg hcoeff_nonneg hsum_nonneg
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, countSketchSparseComputedPreconditionedBasis]
      using
        fl_countSketchSparseApply_entry_error_bound
          fp hash sign U hb i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDot_perturb_bound fp Vhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (countSketchSparseComputedPreconditionedBasis fp U x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat, hash, sign]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (countSketchSparseComputedPreconditionedBasis fp U x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        countSketchSparseUniformRowPerturbBudget fp U x := by
        simp [countSketchSparseUniformRowPerturbBudget, V, Vhat, E,
          hash, sign]

/-- The sparse computed CountSketch basis satisfies the computed-denominator
uniform-row perturbation event with probability one. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp U
        (countSketchSparseComputedPreconditionedBasis fp U)
        dhat
        (countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let hash : CountSketchHash r m := x.1.1
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows hash sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasis fp U x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyFpAbsBudget fp hash sign U
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hb : ∀ i : Fin r, gammaValid fp (countSketchBucketSize hash i) := by
    intro i
    exact gammaValid_mono fp (countSketchBucketSize_le hash i) hγm
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    have hcoeff_nonneg :
        0 ≤ fp.u + gamma fp (countSketchBucketSize hash i) +
            fp.u * gamma fp (countSketchBucketSize hash i) := by
      exact add_nonneg
        (add_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
        (mul_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
    have hsum_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          |sign (countSketchBucketIndex hash i t)| *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    simpa [E, countSketchSparseApplyFpAbsBudget,
      countSketchSparseApplyEntryFpAbsBudget] using
      mul_nonneg hcoeff_nonneg hsum_nonneg
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, countSketchSparseComputedPreconditionedBasis]
      using
        fl_countSketchSparseApply_entry_error_bound
          fp hash sign U hb i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasis fp U x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat, hash, sign]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasis fp U x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat x := by
        simp [countSketchSparseUniformRowComputedDenPerturbBudget, V, Vhat, E,
          hash, sign]

/-- The stored-sign sparse computed CountSketch basis satisfies the
computed-denominator uniform-row perturbation event with probability one. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp U
        (countSketchSparseComputedPreconditionedBasisWithStoredSign
          fp U storedSignOf)
        dhat
        (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
          fp U storedSignOf dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let hash : CountSketchHash r m := x.1.1
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows hash sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSign
      fp U storedSignOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignFpAbsBudget fp hash sign signhat U
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hb : ∀ i : Fin r, gammaValid fp (countSketchBucketSize hash i) := by
    intro i
    exact gammaValid_mono fp (countSketchBucketSize_le hash i) hγm
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    have hcoeff_nonneg :
        0 ≤ fp.u + gamma fp (countSketchBucketSize hash i) +
            fp.u * gamma fp (countSketchBucketSize hash i) := by
      exact add_nonneg
        (add_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
        (mul_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
    have hsum_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          |signhat.vector (countSketchBucketIndex hash i t)| *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hbase_nonneg :
        0 ≤ countSketchSparseApplyEntryFpAbsBudget
          fp hash signhat.vector U i j := by
      exact mul_nonneg hcoeff_nonneg hsum_nonneg
    have hstore_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          signhat.abs_error (countSketchBucketIndex hash i t) *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg
        (signhat.abs_error_nonneg (countSketchBucketIndex hash i t))
        (abs_nonneg _)
    simpa [E, countSketchSparseApplyStoredSignFpAbsBudget,
      countSketchSparseApplyStoredSignEntryFpAbsBudget,
      countSketchSparseApplyEntryFpAbsBudget] using
      add_nonneg hbase_nonneg hstore_nonneg
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E,
      countSketchSparseComputedPreconditionedBasisWithStoredSign,
      countSketchSparseApplyStoredSignFpAbsBudget] using
        fl_countSketchSparseApplyWithStoredSign_entry_error_bound
          fp hash sign signhat U hb i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSign
              fp U storedSignOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat, hash, sign]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSign
              fp U storedSignOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
          fp U storedSignOf dhat x := by
        simp [countSketchSparseUniformRowComputedDenStoredSignPerturbBudget,
          V, Vhat, E, hash, sign, signhat]

/-- The stored-sign sparse computed CountSketch basis with exact per-bucket
traversal orders satisfies the computed-denominator uniform-row perturbation
event with probability one. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp U
        (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
          fp U storedSignOf orderOf)
        dhat
        (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
          fp U storedSignOf orderOf dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let hash : CountSketchHash r m := x.1.1
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let order :
      (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i) := orderOf hash
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows hash sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
      fp U storedSignOf orderOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignPermutedFpAbsBudget
      fp hash sign signhat U order
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hb : ∀ i : Fin r, gammaValid fp (countSketchBucketSize hash i) := by
    intro i
    exact gammaValid_mono fp (countSketchBucketSize_le hash i) hγm
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    have hcoeff_nonneg :
        0 ≤ fp.u + gamma fp (countSketchBucketSize hash i) +
            fp.u * gamma fp (countSketchBucketSize hash i) := by
      exact add_nonneg
        (add_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
        (mul_nonneg fp.u_nonneg (gamma_nonneg fp (hb i)))
    have hbase_sum_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          |signhat.vector (countSketchBucketIndex hash i (order i t))| *
            |U (countSketchBucketIndex hash i (order i t)) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hbase_nonneg :
        0 ≤ countSketchSparseApplyPermutedEntryFpAbsBudget
          fp hash signhat.vector U order i j := by
      exact mul_nonneg hcoeff_nonneg hbase_sum_nonneg
    have hstore_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          signhat.abs_error (countSketchBucketIndex hash i (order i t)) *
            |U (countSketchBucketIndex hash i (order i t)) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg
        (signhat.abs_error_nonneg (countSketchBucketIndex hash i (order i t)))
        (abs_nonneg _)
    simpa [E, countSketchSparseApplyStoredSignPermutedFpAbsBudget,
      countSketchSparseApplyStoredSignPermutedEntryFpAbsBudget] using
      add_nonneg hbase_nonneg hstore_nonneg
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E,
      countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted,
      countSketchSparseApplyStoredSignPermutedFpAbsBudget, hash, sign,
      signhat, order] using
        fl_countSketchSparseApplyWithStoredSignPermuted_entry_error_bound
          fp hash sign signhat U order hb i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
              fp U storedSignOf orderOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat, hash, sign]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
              fp U storedSignOf orderOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
          fp U storedSignOf orderOf dhat x := by
        simp [countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget,
          V, Vhat, E, hash, sign, signhat, order]

/-- The stored-sign sparse computed CountSketch basis with tree-reduced
bucket accumulations satisfies the computed-denominator uniform-row
perturbation event with probability one. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) :
    (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
      (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp U
        (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
          fp U storedSignOf treeOf)
        dhat
        (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
          fp U storedSignOf treeOf dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let hash : CountSketchHash r m := x.1.1
  let sign : Fin m → ℝ := rademacherSignVector x.1.2
  let signhat : ComputedVector fp sign := storedSignOf x.1.2
  let tree :
      (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1) := treeOf hash
  let V : Fin r → Fin n → ℝ :=
    preconditionRows (countSketchRows hash sign) U
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasisWithStoredSignTree
      fp U storedSignOf treeOf x.1
  let E : Fin r → Fin n → ℝ :=
    countSketchSparseApplyStoredSignTreeFpAbsBudget
      fp hash sign signhat U tree
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    have hcoeff_nonneg :
        0 ≤ fp.u + gamma fp (tree i).depth +
            fp.u * gamma fp (tree i).depth := by
      exact add_nonneg
        (add_nonneg fp.u_nonneg (gamma_nonneg fp (hdepth hash i)))
        (mul_nonneg fp.u_nonneg (gamma_nonneg fp (hdepth hash i)))
    have hbase_sum_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          |signhat.vector (countSketchBucketIndex hash i t)| *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hbase_nonneg :
        0 ≤ countSketchSparseApplyTreeEntryFpAbsBudget
          fp hash signhat.vector U tree i j := by
      exact mul_nonneg hcoeff_nonneg hbase_sum_nonneg
    have hstore_nonneg :
        0 ≤ ∑ t : Fin (countSketchBucketSize hash i),
          signhat.abs_error (countSketchBucketIndex hash i t) *
            |U (countSketchBucketIndex hash i t) j| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg
        (signhat.abs_error_nonneg (countSketchBucketIndex hash i t))
        (abs_nonneg _)
    simpa [E, countSketchSparseApplyStoredSignTreeFpAbsBudget,
      countSketchSparseApplyStoredSignTreeEntryFpAbsBudget] using
      add_nonneg hbase_nonneg hstore_nonneg
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E,
      countSketchSparseComputedPreconditionedBasisWithStoredSignTree,
      countSketchSparseApplyStoredSignTreeFpAbsBudget, hash, sign, signhat,
      tree] using
        fl_countSketchSparseApplyWithStoredSignTree_entry_error_bound
          fp hash sign signhat U tree (hdepth hash) i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hr hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hr hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
              fp U storedSignOf treeOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat, hash, sign]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
              fp U storedSignOf treeOf x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
          fp U storedSignOf treeOf dhat x := by
        simp [countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget,
          V, Vhat, E, hash, sign, signhat, tree]

/-- Generic exact-to-computed transfer for CountSketch preprocessing with a
computed uniform row-scale denominator.  The exact event is the collision-free
CountSketch plus exact uniform-row concentration event; the perturbation event
charges computed CountSketch application, computed row scaling, and rounded
Gram dot products. -/
theorem countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) {ε δExact δComp : ℝ}
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ)
    (hExact :
      1 - δExact ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowSampleGramTwoSidedEvent U ε))
    (hComp :
      1 - δComp ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp U Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp Vhat dhat ε τ) := by
  classical
  let P := countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let E : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchUniformRowSampleGramTwoSidedEvent U ε
  let F : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp U Vhat dhat τ
  let M : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F δExact δComp (by simpa [P, E] using hExact)
        (by simpa [P, F] using hComp)
  have hsubset : E ∩ F ⊆ M := by
    intro x hx
    let V : Fin r → Fin n → ℝ :=
      preconditionRows
        (countSketchRows x.1.1 (rademacherSignVector x.1.2)) U
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxExact :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [E, countSketchUniformRowSampleGramTwoSidedEvent, V, Exact]
        using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        V, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [M,
      countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent]
      using And.intro hUpper hLower
  exact hInter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Nonconditional sparse CountSketch FP endpoint with rounded sparse
CountSketch application, computed uniform row-scale denominator, rounded row
divisions, and rounded Gram dot products.

The only exact probability losses are the CountSketch hash-collision bound
`m^2 / r` and the downstream uniform-row sampling tail budget.  All
non-probability computations displayed in the event are charged by the explicit
radius `countSketchSparseUniformRowComputedDenPerturbBudget`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (countSketchSparseComputedPreconditionedBasis fp U)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat)) := by
  have hExact :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowSampleGramTwoSidedEvent U ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U hr hU hs htheta hδSample hsampleBudget
  have hCompEq :
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp U
          (countSketchSparseComputedPreconditionedBasis fp U)
          dhat
          (countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat)) = 1 := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp U dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp U
            (countSketchSparseComputedPreconditionedBasis fp U)
            dhat
            (countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (U := U)
      (Vhat := countSketchSparseComputedPreconditionedBasis fp U)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample)
      (δComp := 0)
      (τ := countSketchSparseUniformRowComputedDenPerturbBudget fp U dhat)
      hExact hComp
  simpa [add_zero] using hTransfer

/-- Concrete-denominator specialization of the collision-free sparse
CountSketch FP endpoint for an exact orthonormal analysis basis.

The uniform row-scale denominator is computed by the modeled scalar routine
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`, so the final theorem has no
generic denominator parameter. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m n s : ℕ} (U : Fin m → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (countSketchSparseComputedPreconditionedBasis fp U)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp U
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
      fp U (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget

/-- Exact sampled-Gram error for a rectangularly preconditioned factored input
`A = U C`, specialized for the CountSketch section before the later generic
factored-input block. -/
theorem uniformRowSampleGram_countSketchRectFactoredInput_error_eq_rightGramCongruence_error
    {r m q n s : ℕ} (P : Fin r → Fin m → ℝ)
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (samples : RowTrace r s) (hU : HasOrthonormalColumns U)
    (hr : 0 < r) (hs : 0 < (s : ℝ)) :
    (fun j k : Fin n =>
        uniformRowSampleGram
            (preconditionRows P (preconditionColumns U C)) samples j k -
          rowGram (preconditionColumns U C) j k) =
      rightGramCongruence
        (fun a b : Fin q =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C := by
  classical
  let V : Fin r → Fin q → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  have hY :
      preconditionRows P A = preconditionColumns V C := by
    simpa [A, V] using preconditionRows_preconditionColumns_assoc_rect P U C
  have hsample :
      uniformRowSampleGram (preconditionRows P A) samples =
        rightGramCongruence (uniformRowSampleGram V samples) C := by
    rw [hY]
    exact
      uniformRowSampleGram_preconditionColumns_eq_rightGramCongruence
        V C samples hr hs
  have hAgram : rowGram A = rowGram C := by
    change rowGram (preconditionColumns U C) = rowGram C
    rw [rowGram_preconditionColumns_eq_rightGramCongruence]
    have hgram : rowGram U = idMatrix q :=
      rowGram_eq_id_of_orthonormal_columns U hU
    ext j k
    have hcong :
        rightGramCongruence
            (fun a b : Fin q => (1 : ℝ) * finiteIdMatrix a b) C j k =
          (fun j k : Fin n => (1 : ℝ) * rowGram C j k) j k := by
      simpa using
        congrFun (congrFun
          (rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1) j) k
    simpa [hgram, idMatrix] using hcong
  ext j k
  calc
    uniformRowSampleGram (preconditionRows P (preconditionColumns U C)) samples j k -
        rowGram (preconditionColumns U C) j k
        =
      rightGramCongruence (uniformRowSampleGram V samples) C j k -
        rightGramCongruence (finiteIdMatrix : Fin q → Fin q → ℝ) C j k := by
        simp [A, V, hsample, hAgram,
          rightGramCongruence_finiteIdMatrix_eq_rowGram]
    _ =
      rightGramCongruence
        (fun a b : Fin q =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C j k := by
        have hsub :=
          congrFun (congrFun
            (rightGramCongruence_sub
              (uniformRowSampleGram V samples)
              (finiteIdMatrix : Fin q → Fin q → ℝ) C) j) k
        simpa [V] using hsub.symm

/-- Exact two-sided sampled-Gram event for CountSketch followed by uniform row
sampling on an actual input matrix factored as `A = U C`, where `U` is the
exact orthonormal analysis basis and `C` is an exact right factor used only in
the analysis. -/
def countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
    {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ) (ε : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let P : Fin r → Fin m → ℝ :=
      countSketchRows x.1.1 (rademacherSignVector x.1.2)
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Y : Fin r → Fin n → ℝ := preconditionRows P A
    finiteLoewnerLe
      (fun j k : Fin n => uniformRowSampleGram Y x.2 j k - rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n => -(uniformRowSampleGram Y x.2 j k - rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k)}

/-- The exact orthonormal-basis CountSketch sample-Gram event implies the
corresponding actual-input event for `A = U C`. -/
theorem countSketchUniformRowSampleGramTwoSidedEvent_subset_factoredInput
    {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ) (ε : ℝ)
    (hU : HasOrthonormalColumns U) (hr : 0 < r) (hs : 0 < (s : ℝ)) :
    countSketchUniformRowSampleGramTwoSidedEvent
        (r := r) (m := m) (n := q) (s := s) U ε ⊆
      countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
        (r := r) (m := m) (q := q) (n := n) (s := s) U C ε := by
  classical
  intro x hx
  let P : Fin r → Fin m → ℝ :=
    countSketchRows x.1.1 (rademacherSignVector x.1.2)
  let V : Fin r → Fin q → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  let Y : Fin r → Fin n → ℝ := preconditionRows P A
  let ExactU : Fin q → Fin q → ℝ :=
    fun a b => uniformRowSampleGram V x.2 a b - finiteIdMatrix a b
  let ExactA : Fin n → Fin n → ℝ :=
    fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
  let EpsU : Fin q → Fin q → ℝ :=
    fun a b => ε * finiteIdMatrix a b
  let EpsA : Fin n → Fin n → ℝ :=
    fun j k => ε * rowGram A j k
  have hxU :
      finiteLoewnerLe ExactU EpsU ∧
      finiteLoewnerLe (fun a b : Fin q => -ExactU a b) EpsU := by
    simpa [countSketchUniformRowSampleGramTwoSidedEvent, P, V, ExactU, EpsU]
      using hx
  have hErr :
      ExactA = rightGramCongruence ExactU C := by
    simpa [P, V, A, Y, ExactU, ExactA] using
      uniformRowSampleGram_countSketchRectFactoredInput_error_eq_rightGramCongruence_error
        P U C x.2 hU hr hs
  have hEps :
      rightGramCongruence EpsU C = EpsA := by
    simpa [A, EpsU, EpsA] using
      rightGramCongruence_smul_finiteIdMatrix_eq_smul_factoredInputGram
        U C hU ε
  have hUpperBase :
      finiteLoewnerLe (rightGramCongruence ExactU C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.1
  have hLowerBase :
      finiteLoewnerLe
        (rightGramCongruence (fun a b : Fin q => -ExactU a b) C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.2
  have hUpper : finiteLoewnerLe ExactA EpsA := by
    rw [hErr, ← hEps]
    exact hUpperBase
  have hNegErr :
      (fun j k : Fin n => -ExactA j k) =
        rightGramCongruence (fun a b : Fin q => -ExactU a b) C := by
    rw [hErr]
    rw [rightGramCongruence_neg]
  have hLower : finiteLoewnerLe (fun j k : Fin n => -ExactA j k) EpsA := by
    rw [hNegErr, ← hEps]
    exact hLowerBase
  simpa [countSketchUniformRowFactoredInputSampleGramTwoSidedEvent,
    P, A, Y, ExactA, EpsA] using And.intro hUpper hLower

/-- Exact CountSketch preprocessing plus uniform row sampling for an actual
input matrix `A = U C`.  The hash/sign and row-sampling laws remain exact; `U`
and `C` are exact analysis witnesses, not computed algorithm outputs. -/
theorem countSketchUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    {r m q n s : ℕ} (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent U C ε) := by
  have hExactU :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowSampleGramTwoSidedEvent U ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U hr hU hs htheta hδSample hsampleBudget
  exact hExactU.trans
    (FiniteProbability.eventProb_mono
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr)
      (countSketchUniformRowSampleGramTwoSidedEvent_subset_factoredInput
        (r := r) (m := m) (q := q) (n := n) (s := s) U C ε hU hr hs))

/-- Fully floating-point computed event for CountSketch on an actual input
matrix `A = U C`, using a computed uniform row-scale denominator.  The computed
matrix is `Vhat`, normally the sparse rounded CountSketch apply to `A`. -/
def countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ε : ℝ)
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k)}

/-- Transfer an exact CountSketch factored-input event and a concrete computed
perturbation event to the fully floating-point sampled Gram. -/
theorem countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (Vhat : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) {ε δExact δComp : ℝ}
    (τ : (CountSketchHash r m × RademacherTrace m) × RowTrace r s → ℝ)
    (hExact :
      1 - δExact ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
            U C ε))
    (hComp :
      1 - δComp ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp (preconditionColumns U C) Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C Vhat dhat ε τ) := by
  classical
  let Pprob := countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let E : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchUniformRowFactoredInputSampleGramTwoSidedEvent U C ε
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  let F : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A Vhat dhat τ
  let M : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp U C Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ Pprob.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Pprob E F δExact δComp (by simpa [Pprob, E] using hExact)
        (by simpa [Pprob, F, A] using hComp)
  have hsubset : E ∩ F ⊆ M := by
    intro x hx
    let Pmat : Fin r → Fin m → ℝ :=
      countSketchRows x.1.1 (rademacherSignVector x.1.2)
    let Y : Fin r → Fin n → ℝ := preconditionRows Pmat A
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram Y x.2 j k
    let Eps : Fin n → Fin n → ℝ :=
      fun j k => ε * rowGram A j k
    have hxExact :
        finiteLoewnerLe Exact Eps ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k) Eps := by
      simpa [E, countSketchUniformRowFactoredInputSampleGramTwoSidedEvent,
        A, Pmat, Y, Exact, Eps] using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        A, Pmat, Y, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_general_of_frobNorm_le
        Exact Delta Eps hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    exact ⟨hUpper, hLower⟩
  exact hInter.trans (by
    simpa [Pprob, M] using FiniteProbability.eventProb_mono Pprob hsubset)

/-- Nonconditional CountSketch FP endpoint for an actual Algorithm 3 input
matrix factored as `A = U C`.  The algorithm computes the sparse rounded
CountSketch apply to `A`, uses a computed uniform row-scale denominator, rounds
sampled-row divisions, and rounds Gram dot products.  The exact factors `U,C`
are analysis witnesses; they are not computed quantities in this theorem. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasis fp A)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)) := by
  intro A
  have hExact :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
            U C ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U C hr hU hs htheta hδSample hsampleBudget
  have hCompEq :
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp A
          (countSketchSparseComputedPreconditionedBasis fp A)
          dhat
          (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)) = 1 := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp A
            (countSketchSparseComputedPreconditionedBasis fp A)
            dhat
            (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (U := U) (C := C)
      (Vhat := countSketchSparseComputedPreconditionedBasis fp A)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample)
      (δComp := 0)
      (τ := countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)
      hExact hComp
  simpa [A, add_zero] using hTransfer

/-- Target-failure-budget form of the collision-free actual-input CountSketch
endpoint.

This packages the same fully computed event as
`..._ge_one_sub_square_inv_add_delta` with a single user-facing failure
probability `δ`.  The only probability losses are the exact collision-free
hash bound and the exact downstream row-sampling tail budget; all
non-probability computations are charged by the concrete displayed radius. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasis fp A)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)) := by
  intro A
  have hbase :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
            fp U C
            (countSketchSparseComputedPreconditionedBasis fp A)
            dhat
            ε
            (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)) := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        fp U C dhat hr hU hs hγm hγs htheta hδSample hsampleBudget
  have hleft :
      1 - δ ≤ 1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator specialization of the collision-free actual-input
CountSketch FP endpoint.

The algorithm computes with \(A=UC\), not with the analysis factors.  The
uniform row-scale denominator is fixed to the locally proved routine
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasis fp A)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp A
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
      fp U C (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget

/-- Direct target-failure-budget form of the concrete-denominator actual-input
CountSketch endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasis fp A)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenPerturbBudget fp A
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Stored-sign collision-free CountSketch FP endpoint for an actual Algorithm 3
input matrix factored as `A = U C`, using a computed uniform row-scale
denominator.

The algorithm computes with the actual input `A`, stores the realized signs via
`storedSignOf`, applies sparse CountSketch arithmetic to `A`, rounds sampled-row
divisions, and rounds Gram dot products.  The exact factors `U,C` are analysis
witnesses; they are not computed quantities in this theorem. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A storedSignOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A storedSignOf dhat)) := by
  intro A
  have hExact :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
            U C ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U C hr hU hs htheta hδSample hsampleBudget
  have hCompEq :
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp A
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A storedSignOf)
          dhat
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A storedSignOf dhat)) = 1 := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp A
            (countSketchSparseComputedPreconditionedBasisWithStoredSign
              fp A storedSignOf)
            dhat
            (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
              fp A storedSignOf dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (U := U) (C := C)
      (Vhat := countSketchSparseComputedPreconditionedBasisWithStoredSign
        fp A storedSignOf)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample)
      (δComp := 0)
      (τ := countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
        fp A storedSignOf dhat)
      hExact hComp
  simpa [A, add_zero] using hTransfer

/-- Target-failure-budget form of the stored-sign collision-free actual-input
CountSketch endpoint with a computed denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A storedSignOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A storedSignOf dhat)) := by
  intro A
  have hbase :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
            fp U C
            (countSketchSparseComputedPreconditionedBasisWithStoredSign
              fp A storedSignOf)
            dhat
            ε
            (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
              fp A storedSignOf dhat)) := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        fp U C storedSignOf dhat hr hU hs hγm hγs htheta hδSample hsampleBudget
  have hleft :
      1 - δ ≤ 1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator specialization of the stored-sign collision-free
actual-input CountSketch FP endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A storedSignOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A storedSignOf (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
      fp U C storedSignOf (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget

/-- Target-failure-budget form of the concrete-denominator stored-sign
collision-free actual-input CountSketch endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A storedSignOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A storedSignOf (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C storedSignOf (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_mul sign 1` stored-sign collision-free CountSketch endpoint for
an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω)))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_add sign 0` stored-sign collision-free CountSketch endpoint for
an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω)))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_sub sign 0` stored-sign collision-free CountSketch endpoint for
an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSign
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω)))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Permuted-bucket stored-sign collision-free CountSketch FP endpoint for an
actual Algorithm 3 input matrix factored as `A = U C`, using a computed
uniform row-scale denominator.

The algorithm computes with the actual input `A`, stores the realized signs via
`storedSignOf`, applies sparse CountSketch arithmetic to `A` in the supplied
per-bucket traversal order, rounds sampled-row divisions, and rounds Gram dot
products.  The exact factors `U,C` are analysis witnesses; they are not
computed quantities in this theorem. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A storedSignOf orderOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A storedSignOf orderOf dhat)) := by
  intro A
  have hExact :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
            U C ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U C hr hU hs htheta hδSample hsampleBudget
  have hCompEq :
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp A
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A storedSignOf orderOf)
          dhat
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A storedSignOf orderOf dhat)) = 1 := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf orderOf dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp A
            (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
              fp A storedSignOf orderOf)
            dhat
            (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
              fp A storedSignOf orderOf dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (U := U) (C := C)
      (Vhat := countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
        fp A storedSignOf orderOf)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample)
      (δComp := 0)
      (τ := countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
        fp A storedSignOf orderOf dhat)
      hExact hComp
  simpa [A, add_zero] using hTransfer

/-- Target-failure-budget form of the permuted-bucket stored-sign
collision-free actual-input CountSketch endpoint with a computed denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A storedSignOf orderOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A storedSignOf orderOf dhat)) := by
  intro A
  have hbase :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
            fp U C
            (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
              fp A storedSignOf orderOf)
            dhat
            ε
            (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
              fp A storedSignOf orderOf dhat)) := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        fp U C storedSignOf orderOf dhat hr hU hs hγm hγs htheta
        hδSample hsampleBudget
  have hleft :
      1 - δ ≤ 1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator specialization of the permuted-bucket stored-sign
collision-free actual-input CountSketch FP endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A storedSignOf orderOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A storedSignOf orderOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
      fp U C storedSignOf orderOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget

/-- Target-failure-budget form of the concrete-denominator permuted-bucket
stored-sign collision-free actual-input CountSketch endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A storedSignOf orderOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A storedSignOf orderOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C storedSignOf orderOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hγm hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_mul sign 1` permuted-bucket stored-sign collision-free
CountSketch endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf hr hU hs hγm hγs htheta hδSample hsampleBudget
      htotalBudget

/-- Final `fl_add sign 0` permuted-bucket stored-sign collision-free
CountSketch endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf hr hU hs hγm hγs htheta hδSample hsampleBudget
      htotalBudget

/-- Final `fl_sub sign 0` permuted-bucket stored-sign collision-free
CountSketch endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            orderOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf hr hU hs hγm hγs htheta hδSample hsampleBudget
      htotalBudget

/-- Tree-reduced stored-sign collision-free CountSketch FP endpoint for an
actual Algorithm 3 input matrix factored as `A = U C`, using a computed
uniform row-scale denominator.

The algorithm computes with the actual input `A`, stores the realized signs via
`storedSignOf`, applies sparse CountSketch arithmetic to `A` with the supplied
per-bucket summation tree, rounds sampled-row divisions, and rounds Gram dot
products.  The exact factors `U,C` are analysis witnesses; they are not
computed quantities in this theorem. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A storedSignOf treeOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A storedSignOf treeOf dhat)) := by
  intro A
  have hExact :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchUniformRowFactoredInputSampleGramTwoSidedEvent
            U C ε) := by
    simpa using
      countSketchUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        U C hr hU hs htheta hδSample hsampleBudget
  have hCompEq :
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp A
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A storedSignOf treeOf)
          dhat
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A storedSignOf treeOf dhat)) = 1 := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf treeOf dhat hr hs hdepth hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp A
            (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
              fp A storedSignOf treeOf)
            dhat
            (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
              fp A storedSignOf treeOf dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    countSketchUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (U := U) (C := C)
      (Vhat := countSketchSparseComputedPreconditionedBasisWithStoredSignTree
        fp A storedSignOf treeOf)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample)
      (δComp := 0)
      (τ := countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
        fp A storedSignOf treeOf dhat)
      hExact hComp
  simpa [A, add_zero] using hTransfer

/-- Target-failure-budget form of the tree-reduced stored-sign collision-free
actual-input CountSketch endpoint with a computed denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A storedSignOf treeOf)
          dhat
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A storedSignOf treeOf dhat)) := by
  intro A
  have hbase :
      1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
            fp U C
            (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
              fp A storedSignOf treeOf)
            dhat
            ε
            (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
              fp A storedSignOf treeOf dhat)) := by
    simpa [A] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
        fp U C storedSignOf treeOf dhat hr hU hs hdepth hγs htheta
        hδSample hsampleBudget
  have hleft :
      1 - δ ≤ 1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator specialization of the tree-reduced stored-sign
collision-free actual-input CountSketch FP endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - ((m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A storedSignOf treeOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A storedSignOf treeOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_square_inv_add_delta
      fp U C storedSignOf treeOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hdepth hγs htheta hδSample hsampleBudget

/-- Target-failure-budget form of the concrete-denominator tree-reduced
stored-sign collision-free actual-input CountSketch endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A storedSignOf treeOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A storedSignOf treeOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C storedSignOf treeOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hU hs hdepth hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_mul sign 1` tree-reduced stored-sign collision-free CountSketch
endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSign
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf hr hU hs hdepth hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_add sign 0` tree-reduced stored-sign collision-free CountSketch
endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignAddZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf hr hU hs hdepth hγs htheta hδSample hsampleBudget htotalBudget

/-- Final `fl_sub sign 0` tree-reduced stored-sign collision-free CountSketch
endpoint for an actual input matrix, with concrete denominator. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (hr : 0 < r) (hU : HasOrthonormalColumns U)
    {theta ε δSample δ : ℝ}
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let L : ℝ := (r : ℝ)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget :
      (m : ℝ) * (m : ℝ) * (r : ℝ)⁻¹ + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
            fp A
            (fun ω =>
              ComputedVector.flStoredSignSubZeroRight
                fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
            treeOf
            (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  intro A
  simpa [A] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_square_inv_budget
      fp U C
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf hr hU hs hdepth hγs htheta hδSample hsampleBudget htotalBudget

/-- Exact Frobenius event for non-injective CountSketch followed by iid
uniform-row sampling.  The first conjunct controls the exact CountSketch Gram
error around `AᵀA`; the second controls exact row sampling around the exact
preconditioned Gram `(S A)ᵀ(S A)`. -/
def countSketchUniformRowSampleGramRowGramFrobEvent {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ) (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let V : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    frobNorm (fun j k : Fin n => rowGram V j k - rowGram A j k) ≤ ηCS ∧
      frobNorm
        (fun j k : Fin n => uniformRowSampleGram V x.2 j k - rowGram V j k) ≤
        ηRow}

/-- Computed Frobenius event for non-injective CountSketch followed by iid
uniform-row sampling with a computed row-scale denominator.  The event charges
the sparse CountSketch apply, denominator computation, rounded row divisions,
and rounded sampled-Gram dot products through the realized budget. -/
def countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasis fp A x.1
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s Vhat dhat.den x.2 j k -
          rowGram A j k) ≤
      ηCS + ηRow +
        countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat x}

/-- Exact-product-law Frobenius/Markov composition for non-injective
CountSketch followed by exact iid uniform-row sampling.

The CountSketch probability term is the exact non-injective Frobenius/Markov
coefficient term.  The downstream uniform-row term is made deterministic using
`frobNormSqRect_preconditionRows_countSketchRows_le`, so there is no conditional
row-sampling certificate. -/
theorem countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_rowGram_frob_error_le_ge_one_sub
    {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ) {ηCS ηRow : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) :
    let δCS : ℝ :=
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ηCS ^ 2
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchUniformRowSampleGramRowGramFrobEvent A ηCS ηRow) := by
  intro δCS δRow
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramFrobErrorEvent (r := r) (m := m) A ηCS
  let V : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) A
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      uniformRowSampleGramRowGramFrobErrorEvent (s := s) (V x) ηRow
  have hPre : 1 - δCS ≤ P.eventProb Epre := by
    simpa [P, Epre, δCS] using
      countSketchProbability_eventProb_rowGram_frob_error_le_ge_one_sub
        (r := r) (m := m) hr A hηCS
  have hδRow_nonneg : 0 ≤ δRow := by
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    exact div_nonneg
      (mul_nonneg hrs_nonneg (sq_nonneg ((m : ℝ) * frobNormSqRect A)))
      (sq_nonneg ηRow)
  have hSample :
      ∀ x ∈ Epre, 1 - δRow ≤ Q.eventProb (Fsample x) := by
    intro x _hx
    have hbase :
        1 -
            (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          Q.eventProb (Fsample x) := by
      simpa [Q, Fsample] using
        uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
          (m := r) (s := s) (U := V x) hr hs ηRow hηRow
    have hsign_abs : ∀ k : Fin m, |rademacherSignVector x.2 k| ≤ 1 := by
      intro k
      simp [rademacherSignVector_abs x.2 k]
    have hV :
        frobNormSqRect (V x) ≤ (m : ℝ) * frobNormSqRect A := by
      simpa [V] using
        frobNormSqRect_preconditionRows_countSketchRows_le
          x.1 (rademacherSignVector x.2) A hsign_abs
    have hM_nonneg : 0 ≤ (m : ℝ) * frobNormSqRect A := by
      exact mul_nonneg (Nat.cast_nonneg m) (frobNormSqRect_nonneg A)
    have hV_abs :
        |frobNormSqRect (V x)| ≤ |(m : ℝ) * frobNormSqRect A| := by
      simpa [abs_of_nonneg (frobNormSqRect_nonneg (V x)),
        abs_of_nonneg hM_nonneg] using hV
    have hV_sq :
        frobNormSqRect (V x) ^ 2 ≤
          ((m : ℝ) * frobNormSqRect A) ^ 2 :=
      sq_le_sq.mpr hV_abs
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    have hbudget :
        (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          δRow := by
      have hmul :
          ((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2 ≤
            ((r : ℝ) / (s : ℝ)) *
              ((m : ℝ) * frobNormSqRect A) ^ 2 :=
        mul_le_mul_of_nonneg_left hV_sq hrs_nonneg
      simpa [δRow] using
        div_le_div_of_nonneg_right hmul (sq_nonneg ηRow)
    have hleft :
        1 - δRow ≤
          1 - (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 := by
      linarith
    exact hleft.trans hbase
  have hprod :
      1 - (δCS + δRow) ≤
        (P.prod Q).eventProb
          {x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s |
            x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δCS δRow hδRow_nonneg hPre hSample
  have hsubset :
      {x : (CountSketchHash r m × RademacherTrace m) × RowTrace r s |
        x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} ⊆
        countSketchUniformRowSampleGramRowGramFrobEvent A ηCS ηRow := by
    intro x hx
    rcases hx with ⟨hcs, hrow⟩
    constructor
    · simpa [Epre, countSketchRowGramFrobErrorEvent, V] using hcs
    · simpa [Fsample, uniformRowSampleGramRowGramFrobErrorEvent, V] using hrow
  exact hprod.trans (by
    simpa [countSketchUniformRowTraceProbability, P, Q] using
      FiniteProbability.eventProb_mono (P.prod Q) hsubset)

/-- Implementation-facing Frobenius/Markov endpoint for non-injective
CountSketch followed by computed-denominator iid uniform-row sampling.

The exact hash/sign and row-sampling laws remain mathematical probability
objects.  The computed quantities are the sparse CountSketch apply, the
uniform-row denominator, the sampled-row divisions, and the sampled-Gram dot
products; all are charged in the realized radius
`countSketchSparseUniformRowComputedDenPerturbBudget`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ηCS ηRow : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let δCS : ℝ :=
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ηCS ^ 2
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
          fp A dhat ηCS ηRow) := by
  intro δCS δRow
  classical
  let Ptot :=
    countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let Eexact :=
    countSketchUniformRowSampleGramRowGramFrobEvent
      (r := r) (m := m) (s := s) A ηCS ηRow
  let Epert :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A
      (countSketchSparseComputedPreconditionedBasis fp A)
      dhat
      (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)
  have hExact : 1 - (δCS + δRow) ≤ Ptot.eventProb Eexact := by
    simpa [Ptot, Eexact, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_uniformRowSampleGram_rowGram_frob_error_le_ge_one_sub
        (r := r) (m := m) (s := s) hr A hηCS hηRow hs
  have hPertEq : Ptot.eventProb Epert = 1 := by
    simpa [Ptot, Epert] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A dhat hr hs hγm hγs
  have hPert : 1 - (0 : ℝ) ≤ Ptot.eventProb Epert := by
    rw [hPertEq]
    norm_num
  have hInter :
      1 - ((δCS + δRow) + 0) ≤ Ptot.eventProb (Eexact ∩ Epert) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Ptot Eexact Epert (δCS + δRow) 0 hExact hPert
  have hsubset :
      Eexact ∩ Epert ⊆
        countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
          fp A dhat ηCS ηRow := by
    intro x hx
    rcases hx with ⟨hexact, hpert⟩
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let V : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasis fp A x.1
    let τ : ℝ := countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat x
    let DeltaPert : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k
    let DeltaRow : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - rowGram V j k
    let DeltaCS : Fin n → Fin n → ℝ :=
      fun j k => rowGram V j k - rowGram A j k
    have hCS : frobNorm DeltaCS ≤ ηCS := by
      simpa [Eexact, countSketchUniformRowSampleGramRowGramFrobEvent,
        DeltaCS, V, sign] using hexact.1
    have hRow : frobNorm DeltaRow ≤ ηRow := by
      simpa [Eexact, countSketchUniformRowSampleGramRowGramFrobEvent,
        DeltaRow, V, sign] using hexact.2
    have hPertBound : frobNorm DeltaPert ≤ τ := by
      simpa [Epert,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        DeltaPert, V, Vhat, τ, sign] using hpert
    have hsplit :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n =>
          DeltaPert j k + (DeltaRow j k + DeltaCS j k)) := by
      funext j k
      dsimp [DeltaPert, DeltaRow, DeltaCS]
      ring
    have htri₁ := frobNorm_add_le DeltaPert (fun j k => DeltaRow j k + DeltaCS j k)
    have htri₂ := frobNorm_add_le DeltaRow DeltaCS
    have hbound :
        frobNorm
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k) ≤
          ηCS + ηRow + τ := by
      calc
        frobNorm
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k)
            =
          frobNorm
            (fun j k : Fin n =>
              DeltaPert j k + (DeltaRow j k + DeltaCS j k)) := by
              rw [hsplit]
        _ ≤ frobNorm DeltaPert + frobNorm (fun j k => DeltaRow j k + DeltaCS j k) :=
              htri₁
        _ ≤ τ + (ηRow + ηCS) := by
              linarith
        _ = ηCS + ηRow + τ := by ring
    simpa [countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent,
      Vhat, τ] using hbound
  have hmono := FiniteProbability.eventProb_mono Ptot hsubset
  have hfinal := hInter.trans hmono
  simpa [add_assoc] using hfinal

/-- Readable Frobenius-norm simplification of the non-injective CountSketch
plus computed-denominator uniform-row FP endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub_frobNorm
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ηCS ηRow : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let δCS : ℝ :=
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ηCS ^ 2
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
          fp A dhat ηCS ηRow) := by
  intro δCS δRow
  classical
  let coeff : ℝ :=
    ∑ j : Fin n, ∑ k : Fin n,
      ∑ p : CountSketchDistinctPair m,
        (A p.1.1 j * A p.1.2 k) ^ 2
  let δCoeff : ℝ := (2 * (r : ℝ)⁻¹ * coeff) / ηCS ^ 2
  have hbase :
      1 - (δCoeff + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
            fp A dhat ηCS ηRow) := by
    simpa [δCoeff, δRow, coeff] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub
        fp (r := r) (m := m) (s := s) hr A dhat hηCS hηRow hs hγm hγs
  have hcoeff : coeff ≤ frobNormSqRect A ^ 2 := by
    simpa [coeff] using
      countSketchDistinctPair_gramCoeffSq_sum_le_frobNormSqRect_sq A
  have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
  have hδCS :
      δCoeff ≤ δCS := by
    have hmul :
        2 * (r : ℝ)⁻¹ * coeff ≤
          2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
    simpa [δCoeff, δCS] using
      div_le_div_of_nonneg_right hmul (sq_nonneg ηCS)
  have hleft : 1 - (δCS + δRow) ≤ 1 - (δCoeff + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Computed non-injective CountSketch plus downstream uniform-row sample-Gram
two-sided finite-Loewner event centered at the exact input Gram.

The radius is exactly the S9z Frobenius radius:
`ηCS + ηRow` for the two exact Markov events plus the concrete realized
floating-point radius for sparse CountSketch apply, computed denominator,
sampled-row divisions, and sampled-Gram dot products. -/
def countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasis fp A x.1
    let τ : ℝ :=
      ηCS + ηRow +
        countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat x
    finiteLoewnerLe
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k)
      (fun j k => τ * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k =>
        -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k))
      (fun j k => τ * finiteIdMatrix j k)}

/-- Stored-sign computed non-injective CountSketch plus downstream uniform-row
sample-Gram two-sided finite-Loewner event centered at the exact input Gram.

The event radius charges the exact CountSketch cover radius `ηCS`, the exact
downstream row-sampling radius `ηRow`, and the concrete stored-sign
floating-point radius for sign storage/copying, sparse bucket accumulation,
computed denominator, sampled-row divisions, and sampled-Gram dot products. -/
def countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSign
        fp A storedSignOf x.1
    let τ : ℝ :=
      ηCS + ηRow +
        countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
          fp A storedSignOf dhat x
    finiteLoewnerLe
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k)
      (fun j k => τ * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k =>
        -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k))
      (fun j k => τ * finiteIdMatrix j k)}

/-- Stored-sign computed non-injective CountSketch with exact per-bucket
traversal orders, followed by downstream uniform-row sample-Gram, centered at
the exact input Gram.

The event radius charges the exact CountSketch cover radius `ηCS`, the exact
downstream row-sampling radius `ηRow`, and the concrete floating-point radius
for sign storage/copying, bucket accumulation in the selected order, computed
denominator, sampled-row divisions, and sampled-Gram dot products. -/
def countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
        fp A storedSignOf orderOf x.1
    let τ : ℝ :=
      ηCS + ηRow +
        countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
          fp A storedSignOf orderOf dhat x
    finiteLoewnerLe
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k)
      (fun j k => τ * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k =>
        -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k))
      (fun j k => τ * finiteIdMatrix j k)}

/-- Stored-sign computed non-injective CountSketch with tree-reduced bucket
accumulations, followed by downstream uniform-row sample-Gram, centered at
the exact input Gram.

The event radius charges the exact CountSketch cover radius `ηCS`, the exact
downstream row-sampling radius `ηRow`, and the concrete floating-point radius
for sign storage/copying, tree-reduced bucket accumulation, computed
denominator, sampled-row divisions, and sampled-Gram dot products. -/
def countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
  {x |
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSignTree
        fp A storedSignOf treeOf x.1
    let τ : ℝ :=
      ηCS + ηRow +
        countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
          fp A storedSignOf treeOf dhat x
    finiteLoewnerLe
      (fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k)
      (fun j k => τ * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k =>
        -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          rowGram A j k))
      (fun j k => τ * finiteIdMatrix j k)}

/-- The S9z computed Frobenius event implies the corresponding two-sided
finite-Loewner event.  This is a deterministic Frobenius-to-operator bridge
applied after all computed non-probability quantities have already been
charged. -/
theorem countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent_subset_twoSidedLoewnerEvent
    (fp : FPModel) {r m n s : ℕ}
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ηCS ηRow : ℝ) :
    countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
      fp A dhat ηCS ηRow ⊆
      countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
        fp A dhat ηCS ηRow := by
  classical
  intro x hx
  let Vhat : Fin r → Fin n → ℝ :=
    countSketchSparseComputedPreconditionedBasis fp A x.1
  let τ : ℝ :=
    ηCS + ηRow +
      countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat x
  let Delta : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        rowGram A j k
  have hpert : frobNorm Delta ≤ τ := by
    simpa [
      countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent,
      Delta, Vhat, τ] using hx
  have hzeroUpper :
      finiteLoewnerLe (fun _j _k : Fin n => 0)
        (fun j k : Fin n => (0 : ℝ) * finiteIdMatrix j k) := by
    intro z
    simp
  have hzeroLower :
      finiteLoewnerLe (fun j k : Fin n => -(fun _j _k : Fin n => 0) j k)
        (fun j k : Fin n => (0 : ℝ) * finiteIdMatrix j k) := by
    intro z
    simp
  have h :=
    finiteLoewnerLe_two_sided_add_of_frobNorm_le
      (Exact := fun _j _k : Fin n => 0)
      (Delta := Delta) (ε := 0) (τ := τ)
      hzeroUpper hzeroLower hpert
  simpa [
    countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent,
    Delta, Vhat, τ] using h

/-- Non-injective CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint.

The probability loss is the same exact coefficient loss as S9z; the conclusion
is the two-sided finite-Loewner event obtained from the computed Frobenius
event.  This remains Markov/Frobenius-derived rather than optimal CountSketch
subspace-embedding concentration. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ηCS ηRow : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let δCS : ℝ :=
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ηCS ^ 2
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat ηCS ηRow) := by
  intro δCS δRow
  classical
  let P := countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  have hbase :
      1 - (δCS + δRow) ≤
        P.eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
            fp A dhat ηCS ηRow) := by
    simpa [P, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub
        fp (r := r) (m := m) (s := s) hr A dhat hηCS hηRow hs hγm hγs
  have hsubset :=
    countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent_subset_twoSidedLoewnerEvent
      fp (r := r) (m := m) (s := s) A dhat ηCS ηRow
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Exact-coefficient sample-budget form of the non-injective CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint.

This wrapper keeps the sharp S9z CountSketch coefficient loss instead of
replacing it by `||A||_F^4`; the downstream uniform-row loss remains the
proved Frobenius growth bound for `S_{h,ω} A`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ηCS ηRow δ : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ηCS ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat ηCS ηRow) := by
  classical
  let δCS : ℝ :=
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / ηCS ^ 2
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A dhat ηCS ηRow) := by
    simpa [δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub
        fp (r := r) (m := m) (s := s) hr A dhat hηCS hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Readable Frobenius-norm simplification of the non-injective CountSketch
plus downstream uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_frobNorm
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ηCS ηRow : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let δCS : ℝ :=
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ηCS ^ 2
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat ηCS ηRow) := by
  intro δCS δRow
  classical
  let P := countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  have hbase :
      1 - (δCS + δRow) ≤
        P.eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent
            fp A dhat ηCS ηRow) := by
    simpa [P, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_frob_error_le_ge_one_sub_frobNorm
        fp (r := r) (m := m) (s := s) hr A dhat hηCS hηRow hs hγm hγs
  have hsubset :=
    countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramFrobEvent_subset_twoSidedLoewnerEvent
      fp (r := r) (m := m) (s := s) A dhat ηCS ηRow
  exact hbase.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Sample-budget form of the non-injective CountSketch plus downstream
uniform-row floating-point finite-Loewner endpoint.

The hypothesis is the readable S9za failure loss bounded by the target
failure probability `δ`.  The exact probability laws are unchanged, while the
event still charges the concrete sparse CountSketch apply, computed uniform
denominator, sampled-row divisions, and sampled-Gram dot products. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ηCS ηRow δ : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ηCS ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat ηCS ηRow) := by
  classical
  let δCS : ℝ :=
    (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ηCS ^ 2
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A dhat ηCS ηRow) := by
    simpa [δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_frobNorm
        fp (r := r) (m := m) (s := s) hr A dhat hηCS hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Equal-radius sample-budget form of the S9za endpoint.

Taking `ηCS = ηRow = ε / 2` makes the exact part of the finite-Loewner radius
equal to `ε`, so every realization in the event satisfies
`-((ε + T_fp) I) <= Ghat - A^T A <= (ε + T_fp) I`, where `T_fp` is the
irreducible concrete floating-point perturbation budget already built into the
event definition. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let η : ℝ := ε / 2
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / η ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat (ε / 2) (ε / 2)) := by
  have hη : 0 < ε / 2 := by
    linarith
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget
      fp (r := r) (m := m) (s := s) hr A dhat hη hη hs hγm hγs (by
        simpa using hbudget)

/-- Expanded equal-radius readable sample-budget form of the S9za endpoint.

This theorem is algebraically the same as the preceding equal-radius wrapper,
but substitutes `η = ε / 2` in the hypothesis. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget_expanded
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (8 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ε ^ 2 +
        (4 * (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2)) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat (ε / 2) (ε / 2)) := by
  have hη : 0 < ε / 2 := by
    linarith
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget
      fp (r := r) (m := m) (s := s) hr A dhat hη hη hs hγm hγs (by
        convert hbudget using 1
        field_simp [ne_of_gt hε]
        ring)

/-- Equal-radius exact-coefficient sample-budget form of the S9za endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let η : ℝ := ε / 2
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / η ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat (ε / 2) (ε / 2)) := by
  have hη : 0 < ε / 2 := by
    linarith
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget
      fp (r := r) (m := m) (s := s) hr A dhat hη hη hs hγm hγs (by
        simpa using hbudget)

/-- Expanded equal-radius exact-coefficient sample-budget form of the S9za
endpoint.  The hypothesis substitutes `η = ε / 2` explicitly, so the
CountSketch term carries the factor `8 / ε^2` and the downstream row-sampling
term carries the factor `4 / ε^2`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget_expanded
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (8 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ε ^ 2 +
        (4 * (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2)) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat (ε / 2) (ε / 2)) := by
  have hη : 0 < ε / 2 := by
    linarith
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget
      fp (r := r) (m := m) (s := s) hr A dhat hη hη hs hγm hγs (by
        convert hbudget using 1
        field_simp [ne_of_gt hε]
        ring)

/-- Concrete-denominator exact-coefficient sample-budget form of the
non-injective CountSketch plus downstream uniform-row finite-Loewner endpoint.
-/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ηCS ηRow δ : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ηCS ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) ηCS ηRow) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_coeff_budget
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hηCS hηRow hs hγm hγs hbudget

/-- Concrete-denominator equal-radius exact-coefficient sample-budget form of
the non-injective CountSketch plus downstream uniform-row finite-Loewner
endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let η : ℝ := ε / 2
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / η ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          (ε / 2) (ε / 2)) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hε hs hγm hγs hbudget

/-- Concrete-denominator expanded equal-radius exact-coefficient sample-budget
form of the non-injective CountSketch plus downstream uniform-row
finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget_expanded
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (8 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / ε ^ 2 +
        (4 * (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2)) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          (ε / 2) (ε / 2)) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_coeff_budget_expanded
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hε hs hγm hγs hbudget

/-- Concrete-denominator sample-budget form of the non-injective CountSketch
plus downstream uniform-row finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ηCS ηRow δ : ℝ}
    (hηCS : 0 < ηCS) (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ηCS ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) ηCS ηRow) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_frobNorm_budget
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hηCS hηRow hs hγm hγs hbudget

/-- Concrete-denominator equal-radius sample-budget form of the non-injective
CountSketch plus downstream uniform-row finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let η : ℝ := ε / 2
      (2 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / η ^ 2 +
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / η ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          (ε / 2) (ε / 2)) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hε hs hγm hγs hbudget

/-- Concrete-denominator expanded equal-radius readable sample-budget form of
the non-injective CountSketch plus downstream uniform-row finite-Loewner
endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget_expanded
    (fp : FPModel) {r m n s : ℕ} (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      (8 * (r : ℝ)⁻¹ * frobNormSqRect A ^ 2) / ε ^ 2 +
        (4 * (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2)) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          (ε / 2) (ε / 2)) := by
  simpa using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_ge_one_sub_delta_of_equal_radius_frobNorm_budget_expanded
      fp (r := r) (m := m) (s := s) hr A
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hε hs hγm hγs hbudget

/-- Finite-cover CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint.

The CountSketch preprocessing event is the exact finite-cover two-sided Loewner
event with radius `η + L * (2 * ρ + ρ^2)`.  The downstream uniform-row
sampling contributes the exact Frobenius radius `ηRow`, and the sparse apply,
computed denominator, row divisions, and sampled-Gram dot products are charged
through the concrete realized perturbation budget in the event. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Ptot :=
    countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L
  let V : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) A
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      uniformRowSampleGramRowGramFrobErrorEvent (s := s) (V x) ηRow
  let Eprod : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    {x | x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1}
  let Epert : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A
      (countSketchSparseComputedPreconditionedBasis fp A)
      dhat
      (countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat)
  have hPre : 1 - δCS ≤ P.eventProb Epre := by
    simpa [P, Epre, δCS] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
        (r := r) (m := m) (n := n) (ι := ι)
        hr A net hcover hη hL hρ
  have hδRow_nonneg : 0 ≤ δRow := by
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    exact div_nonneg
      (mul_nonneg hrs_nonneg (sq_nonneg ((m : ℝ) * frobNormSqRect A)))
      (sq_nonneg ηRow)
  have hSample :
      ∀ x ∈ Epre, 1 - δRow ≤ Q.eventProb (Fsample x) := by
    intro x _hx
    have hbase :
        1 -
            (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          Q.eventProb (Fsample x) := by
      simpa [Q, Fsample] using
        uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
          (m := r) (s := s) (U := V x) hr hs ηRow hηRow
    have hsign_abs : ∀ k : Fin m, |rademacherSignVector x.2 k| ≤ 1 := by
      intro k
      simp [rademacherSignVector_abs x.2 k]
    have hV :
        frobNormSqRect (V x) ≤ (m : ℝ) * frobNormSqRect A := by
      simpa [V] using
        frobNormSqRect_preconditionRows_countSketchRows_le
          x.1 (rademacherSignVector x.2) A hsign_abs
    have hM_nonneg : 0 ≤ (m : ℝ) * frobNormSqRect A := by
      exact mul_nonneg (Nat.cast_nonneg m) (frobNormSqRect_nonneg A)
    have hV_abs :
        |frobNormSqRect (V x)| ≤ |(m : ℝ) * frobNormSqRect A| := by
      simpa [abs_of_nonneg (frobNormSqRect_nonneg (V x)),
        abs_of_nonneg hM_nonneg] using hV
    have hV_sq :
        frobNormSqRect (V x) ^ 2 ≤
          ((m : ℝ) * frobNormSqRect A) ^ 2 :=
      sq_le_sq.mpr hV_abs
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    have hbudgetRow :
        (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          δRow := by
      have hmul :
          ((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2 ≤
            ((r : ℝ) / (s : ℝ)) *
              ((m : ℝ) * frobNormSqRect A) ^ 2 :=
        mul_le_mul_of_nonneg_left hV_sq hrs_nonneg
      simpa [δRow] using
        div_le_div_of_nonneg_right hmul (sq_nonneg ηRow)
    have hleft :
        1 - δRow ≤
          1 - (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 := by
      linarith
    exact hleft.trans hbase
  have hprod :
      1 - (δCS + δRow) ≤ (P.prod Q).eventProb Eprod :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δCS δRow hδRow_nonneg hPre hSample
  have hprod' : 1 - (δCS + δRow) ≤ Ptot.eventProb Eprod := by
    simpa [Ptot, P, Q, Eprod, countSketchUniformRowTraceProbability] using hprod
  have hPertEq : Ptot.eventProb Epert = 1 := by
    simpa [Ptot, Epert] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A dhat hr hs hγm hγs
  have hPert : 1 - (0 : ℝ) ≤ Ptot.eventProb Epert := by
    rw [hPertEq]
    norm_num
  have hinter :
      1 - ((δCS + δRow) + 0) ≤ Ptot.eventProb (Eprod ∩ Epert) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Ptot Eprod Epert (δCS + δRow) 0 hprod' hPert
  have hsubset :
      Eprod ∩ Epert ⊆
        countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat τCS ηRow := by
    intro x hx
    rcases hx with ⟨hprodMem, hpert⟩
    rcases hprodMem with ⟨hcs, hrow⟩
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let Vexact : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasis fp A x.1
    let τfp : ℝ := countSketchSparseUniformRowComputedDenPerturbBudget fp A dhat x
    let DeltaCS : Fin n → Fin n → ℝ :=
      fun j k => rowGram Vexact j k - rowGram A j k
    let DeltaRow : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Vexact x.2 j k - rowGram Vexact j k
    let DeltaPert : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          uniformRowSampleGram Vexact x.2 j k
    have hCS :
        finiteLoewnerLe DeltaCS
            (fun j k : Fin n => τCS * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin n => -DeltaCS j k)
            (fun j k : Fin n => τCS * finiteIdMatrix j k) := by
      simpa [Epre, countSketchRowGramTwoSidedLoewnerCoverEvent,
        DeltaCS, Vexact, sign, τCS] using hcs
    have hRow : frobNorm DeltaRow ≤ ηRow := by
      simpa [Fsample, uniformRowSampleGramRowGramFrobErrorEvent,
        DeltaRow, V, Vexact, sign] using hrow
    have hPertBound : frobNorm DeltaPert ≤ τfp := by
      simpa [Epert,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        DeltaPert, V, Vexact, Vhat, τfp, sign] using hpert
    have hrowAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        DeltaCS DeltaRow hCS.1 hCS.2 hRow
    have hallAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        (fun j k : Fin n => DeltaCS j k + DeltaRow j k)
        DeltaPert hrowAdd.1 hrowAdd.2 hPertBound
    have hsplit :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n =>
          (DeltaCS j k + DeltaRow j k) + DeltaPert j k) := by
      funext j k
      dsimp [DeltaCS, DeltaRow, DeltaPert]
      ring
    have hsplitNeg :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n =>
          -((DeltaCS j k + DeltaRow j k) + DeltaPert j k)) := by
      funext j k
      exact congrArg (fun z : ℝ => -z) (congrFun (congrFun hsplit j) k)
    have hUpper :
        finiteLoewnerLe
          (fun j k =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplit]
      simpa [add_assoc] using hallAdd.1
    have hLower :
        finiteLoewnerLe
          (fun j k =>
            -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplitNeg]
      simpa [add_assoc] using hallAdd.2
    exact ⟨hUpper, hLower⟩
  have hmono := FiniteProbability.eventProb_mono Ptot hsubset
  have hfinal := hinter.trans hmono
  simpa [add_assoc] using hfinal

/-- Target-failure-budget wrapper for the finite-cover CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow δ : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : ι,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (net a) p.1.1 *
                rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat τCS ηRow) := by
  intro τCS
  classical
  let δCS : ℝ :=
    ((∑ a : ι,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (net a) p.1.1 *
            rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A dhat τCS ηRow) := by
    simpa [τCS, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
        fp (r := r) (m := m) (n := n) (s := s) (ι := ι)
        hr A dhat net hcover hη hL hρ hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow, add_assoc] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator target-failure-budget wrapper for the finite-cover
CountSketch plus downstream uniform-row floating-point finite-Loewner endpoint.

The denominator routine is the locally proved computation
`fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow δ : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : ι,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (net a) p.1.1 *
                rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (ι := ι)
      hr A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      net hcover hη hL hρ hηRow hs hγm hγs hbudget

/-- Product-grid specialization of the finite-cover CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint.

The one-dimensional grid is an exact analysis object.  The computed event still
charges sparse CountSketch apply, computed denominator, row divisions, and
sampled-Gram dot products through the existing realized perturbation budget. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  have hcover :
      finiteUnitBallCover
        (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ :=
    finiteUnitBallCover_product_grid grid hgrid hδgrid hρgrid
  have hρ_nonneg : 0 ≤ ρ := by
    exact le_trans
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hδgrid) hρgrid
  simpa [τCS, δCS, δRow] using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
      fp (r := r) (m := m) (n := n) (s := s) (ι := Fin n → α)
      hr A dhat
      (fun a : Fin n → α => fun j : Fin n => grid (a j))
      hcover hη hL hρ_nonneg hηRow hs hγm hγs

/-- Target-failure-budget wrapper for the product-grid CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A dhat τCS ηRow) := by
  intro τCS
  classical
  let δCS : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A dhat τCS ηRow) := by
    simpa [τCS, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
        fp (r := r) (m := m) (n := n) (s := s) (α := α)
        hr A dhat grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow, add_assoc] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator target-failure-budget wrapper for the product-grid
CountSketch plus downstream uniform-row floating-point finite-Loewner endpoint.

The denominator routine is the locally proved computation
`fl_mul (fl_sqrt (s : R)) (fl_div 1 (fl_sqrt (r : R)))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Finite-cover CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint when the realized Rademacher signs are stored or copied
before sparse bucket accumulation.

The exact probability terms are unchanged from the exact-sign theorem.  The
computed event radius uses the stored-sign sparse-apply/downstream uniform-row
budget, so sign storage/copying is charged rather than assumed exact. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Ptot :=
    countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L
  let V : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) A
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      uniformRowSampleGramRowGramFrobErrorEvent (s := s) (V x) ηRow
  let Eprod : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    {x | x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1}
  let Epert : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A
      (countSketchSparseComputedPreconditionedBasisWithStoredSign
        fp A storedSignOf)
      dhat
      (countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
        fp A storedSignOf dhat)
  have hPre : 1 - δCS ≤ P.eventProb Epre := by
    simpa [P, Epre, δCS] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
        (r := r) (m := m) (n := n) (ι := ι)
        hr A net hcover hη hL hρ
  have hδRow_nonneg : 0 ≤ δRow := by
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    exact div_nonneg
      (mul_nonneg hrs_nonneg (sq_nonneg ((m : ℝ) * frobNormSqRect A)))
      (sq_nonneg ηRow)
  have hSample :
      ∀ x ∈ Epre, 1 - δRow ≤ Q.eventProb (Fsample x) := by
    intro x _hx
    have hbase :
        1 -
            (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          Q.eventProb (Fsample x) := by
      simpa [Q, Fsample] using
        uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
          (m := r) (s := s) (U := V x) hr hs ηRow hηRow
    have hsign_abs : ∀ k : Fin m, |rademacherSignVector x.2 k| ≤ 1 := by
      intro k
      simp [rademacherSignVector_abs x.2 k]
    have hV :
        frobNormSqRect (V x) ≤ (m : ℝ) * frobNormSqRect A := by
      simpa [V] using
        frobNormSqRect_preconditionRows_countSketchRows_le
          x.1 (rademacherSignVector x.2) A hsign_abs
    have hM_nonneg : 0 ≤ (m : ℝ) * frobNormSqRect A := by
      exact mul_nonneg (Nat.cast_nonneg m) (frobNormSqRect_nonneg A)
    have hV_abs :
        |frobNormSqRect (V x)| ≤ |(m : ℝ) * frobNormSqRect A| := by
      simpa [abs_of_nonneg (frobNormSqRect_nonneg (V x)),
        abs_of_nonneg hM_nonneg] using hV
    have hV_sq :
        frobNormSqRect (V x) ^ 2 ≤
          ((m : ℝ) * frobNormSqRect A) ^ 2 :=
      sq_le_sq.mpr hV_abs
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    have hbudgetRow :
        (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          δRow := by
      have hmul :
          ((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2 ≤
            ((r : ℝ) / (s : ℝ)) *
              ((m : ℝ) * frobNormSqRect A) ^ 2 :=
        mul_le_mul_of_nonneg_left hV_sq hrs_nonneg
      simpa [δRow] using
        div_le_div_of_nonneg_right hmul (sq_nonneg ηRow)
    have hleft :
        1 - δRow ≤
          1 - (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 := by
      linarith
    exact hleft.trans hbase
  have hprod :
      1 - (δCS + δRow) ≤ (P.prod Q).eventProb Eprod :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δCS δRow hδRow_nonneg hPre hSample
  have hprod' : 1 - (δCS + δRow) ≤ Ptot.eventProb Eprod := by
    simpa [Ptot, P, Q, Eprod, countSketchUniformRowTraceProbability] using hprod
  have hPertEq : Ptot.eventProb Epert = 1 := by
    simpa [Ptot, Epert] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf dhat hr hs hγm hγs
  have hPert : 1 - (0 : ℝ) ≤ Ptot.eventProb Epert := by
    rw [hPertEq]
    norm_num
  have hinter :
      1 - ((δCS + δRow) + 0) ≤ Ptot.eventProb (Eprod ∩ Epert) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Ptot Eprod Epert (δCS + δRow) 0 hprod' hPert
  have hsubset :
      Eprod ∩ Epert ⊆
        countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf dhat τCS ηRow := by
    intro x hx
    rcases hx with ⟨hprodMem, hpert⟩
    rcases hprodMem with ⟨hcs, hrow⟩
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let Vexact : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSign
        fp A storedSignOf x.1
    let τfp : ℝ :=
      countSketchSparseUniformRowComputedDenStoredSignPerturbBudget
        fp A storedSignOf dhat x
    let DeltaCS : Fin n → Fin n → ℝ :=
      fun j k => rowGram Vexact j k - rowGram A j k
    let DeltaRow : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Vexact x.2 j k - rowGram Vexact j k
    let DeltaPert : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          uniformRowSampleGram Vexact x.2 j k
    have hCS :
        finiteLoewnerLe DeltaCS
            (fun j k : Fin n => τCS * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin n => -DeltaCS j k)
            (fun j k : Fin n => τCS * finiteIdMatrix j k) := by
      simpa [Epre, countSketchRowGramTwoSidedLoewnerCoverEvent,
        DeltaCS, Vexact, sign, τCS] using hcs
    have hRow : frobNorm DeltaRow ≤ ηRow := by
      simpa [Fsample, uniformRowSampleGramRowGramFrobErrorEvent,
        DeltaRow, V, Vexact, sign] using hrow
    have hPertBound : frobNorm DeltaPert ≤ τfp := by
      simpa [Epert,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        DeltaPert, V, Vexact, Vhat, τfp, sign] using hpert
    have hrowAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        DeltaCS DeltaRow hCS.1 hCS.2 hRow
    have hallAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        (fun j k : Fin n => DeltaCS j k + DeltaRow j k)
        DeltaPert hrowAdd.1 hrowAdd.2 hPertBound
    have hsplit :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n =>
          (DeltaCS j k + DeltaRow j k) + DeltaPert j k) := by
      funext j k
      dsimp [DeltaCS, DeltaRow, DeltaPert]
      ring
    have hsplitNeg :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n =>
          -((DeltaCS j k + DeltaRow j k) + DeltaPert j k)) := by
      funext j k
      exact congrArg (fun z : ℝ => -z) (congrFun (congrFun hsplit j) k)
    have hUpper :
        finiteLoewnerLe
          (fun j k =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplit]
      simpa [add_assoc] using hallAdd.1
    have hLower :
        finiteLoewnerLe
          (fun j k =>
            -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplitNeg]
      simpa [add_assoc] using hallAdd.2
    exact ⟨hUpper, hLower⟩
  have hmono := FiniteProbability.eventProb_mono Ptot hsubset
  have hfinal := hinter.trans hmono
  simpa [add_assoc] using hfinal

/-- Product-grid specialization of the finite-cover CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint with stored
realized signs.

The product grid is an exact analysis object.  The computed event charges the
stored sign table, sparse bucket arithmetic, computed denominator, sampled-row
divisions, and sampled-Gram dot products through the realized stored-sign
budget. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  have hcover :
      finiteUnitBallCover
        (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ :=
    finiteUnitBallCover_product_grid grid hgrid hδgrid hρgrid
  have hρ_nonneg : 0 ≤ ρ := by
    exact le_trans
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hδgrid) hρgrid
  simpa [τCS, δCS, δRow] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
      fp (r := r) (m := m) (n := n) (s := s) (ι := Fin n → α)
      hr A storedSignOf dhat
      (fun a : Fin n → α => fun j : Fin n => grid (a j))
      hcover hη hL hρ_nonneg hηRow hs hγm hγs

/-- Target-failure-budget wrapper for the stored-sign product-grid CountSketch
plus downstream uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf dhat τCS ηRow) := by
  intro τCS
  classical
  let δCS : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A storedSignOf dhat τCS ηRow) := by
    simpa [τCS, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
        fp (r := r) (m := m) (n := n) (s := s) (α := α)
        hr A storedSignOf dhat grid hgrid hδgrid hρgrid hη hL
        hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow, add_assoc] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint, using `fl_sqrt ((s : R) * (r : R)^{-1})` with an
exactly supplied scalar input ratio. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtExactInputDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf
          (uniformRowFlSqrtExactInputScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf (uniformRowFlSqrtExactInputScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint, using `fl_sqrt (fl_div (s : R) (r : R))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlDivThenSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf
          (uniformRowFlDivThenSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf (uniformRowFlDivThenSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint, using
`fl_sqrt (fl_mul (s : R) (fl_div 1 (r : R)))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlInvMulThenSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf
          (uniformRowFlInvMulThenSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf (uniformRowFlInvMulThenSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint, using
`fl_div (fl_sqrt (s : R)) (fl_sqrt (r : R))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtDivSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf
          (uniformRowFlSqrtDivSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf (uniformRowFlSqrtDivSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for signs copied by
`fl_mul sign_i 1` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for signs copied by
`fl_add sign_i 0` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for signs copied by
`fl_sub sign_i 0` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Deterministic budget adapter for orthonormal product-grid CountSketch plus
downstream uniform-row sampling.

The exact coefficient/Frobenius product-grid loss for an orthonormal-column
input is bounded by the readable loss involving only the product-grid vector
norms and `n`; the downstream row term uses `||U||_F^2 = n`. -/
theorem countSketchUniformRow_productGrid_orthonormal_coeff_add_frob_add_row_budget
    {r m n s : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (grid : α → ℝ) {η L ηRow δ : ℝ}
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let δCS : ℝ :=
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
    δCS + δRow ≤ δ := by
  classical
  let δCoeff : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
  let δCoeffReadable : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
  let δRowExact : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
  let δRowReadable : ℝ :=
    (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
  have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
  have hvecTerm :
      ∀ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2 ≤
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
            η ^ 2 := by
    intro a
    have hpair :
        (∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) ≤
          vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 := by
      calc
        (∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2)
            ≤
          vecNorm2Sq (rectMatMulVec U (fun j : Fin n => grid (a j))) ^ 2 :=
            countSketchDistinctPair_vecCoeffSq_sum_le_vecNorm2Sq_sq
              (rectMatMulVec U (fun j : Fin n => grid (a j)))
        _ = vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 := by
            rw [hasOrthonormalColumns_vecNorm2Sq_rectMatMulVec_eq U hU]
    have hmul :
        2 * (r : ℝ)⁻¹ *
            (∑ p : CountSketchDistinctPair m,
              (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) ≤
          2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 :=
      mul_le_mul_of_nonneg_left hpair hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg η)
  have hvecSum :
      (∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) ≤
        ∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2 :=
    Finset.sum_le_sum (fun a _ => hvecTerm a)
  have hgram :
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2 ≤
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2 := by
    have hcoeff :
        (∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2) ≤
          (n : ℝ) ^ 2 := by
      calc
        (∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2)
            ≤ frobNormSqRect U ^ 2 :=
              countSketchDistinctPair_gramCoeffSq_sum_le_frobNormSqRect_sq U
        _ = (n : ℝ) ^ 2 := by
              rw [frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU]
    have hmul :
        2 * (r : ℝ)⁻¹ *
            (∑ j : Fin n, ∑ k : Fin n,
              ∑ p : CountSketchDistinctPair m,
                (U p.1.1 j * U p.1.2 k) ^ 2) ≤
          2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg L)
  have hcoeffReadable : δCoeff ≤ δCoeffReadable := by
    dsimp [δCoeff, δCoeffReadable]
    linarith
  have hrowEq : δRowExact = δRowReadable := by
    dsimp [δRowExact, δRowReadable]
    rw [frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU]
  dsimp
  have hreadable : δCoeffReadable + δRowReadable ≤ δ := by
    simpa [δCoeffReadable, δRowReadable] using hbudget
  have hmono : δCoeff + δRowExact ≤ δCoeffReadable + δRowReadable := by
    rw [hrowEq]
    linarith
  exact hmono.trans hreadable

/-- Orthonormal-input readable-budget wrapper for stored-sign product-grid
CountSketch plus downstream uniform-row floating-point finite-Loewner endpoint.

This theorem replaces the exact CountSketch coefficient loss by the sufficient
orthonormal loss involving only the product-grid vector norms and `n`, while
retaining the downstream uniform-row loss with `||U||_F^2 = n`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf dhat τCS ηRow) := by
  intro τCS
  classical
  let δCoeff : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
  let δCoeffReadable : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
  let δRowExact : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
  let δRowReadable : ℝ :=
    (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
  have hfactor_nonneg : 0 ≤ 2 * (r : ℝ)⁻¹ := by
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr (Nat.cast_nonneg r))
  have hvecTerm :
      ∀ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2 ≤
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
            η ^ 2 := by
    intro a
    have hpair :
        (∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) ≤
          vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 := by
      calc
        (∑ p : CountSketchDistinctPair m,
          (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2)
            ≤
          vecNorm2Sq (rectMatMulVec U (fun j : Fin n => grid (a j))) ^ 2 :=
            countSketchDistinctPair_vecCoeffSq_sum_le_vecNorm2Sq_sq
              (rectMatMulVec U (fun j : Fin n => grid (a j)))
        _ = vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 := by
            rw [hasOrthonormalColumns_vecNorm2Sq_rectMatMulVec_eq U hU]
    have hmul :
        2 * (r : ℝ)⁻¹ *
            (∑ p : CountSketchDistinctPair m,
              (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) ≤
          2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2 :=
      mul_le_mul_of_nonneg_left hpair hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg η)
  have hvecSum :
      (∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) ≤
        ∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2 :=
    Finset.sum_le_sum (fun a _ => hvecTerm a)
  have hgram :
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2 ≤
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2 := by
    have hcoeff :
        (∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2) ≤
          (n : ℝ) ^ 2 := by
      calc
        (∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (U p.1.1 j * U p.1.2 k) ^ 2)
            ≤ frobNormSqRect U ^ 2 :=
              countSketchDistinctPair_gramCoeffSq_sum_le_frobNormSqRect_sq U
        _ = (n : ℝ) ^ 2 := by
              rw [frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU]
    have hmul :
        2 * (r : ℝ)⁻¹ *
            (∑ j : Fin n, ∑ k : Fin n,
              ∑ p : CountSketchDistinctPair m,
                (U p.1.1 j * U p.1.2 k) ^ 2) ≤
          2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hcoeff hfactor_nonneg
    exact div_le_div_of_nonneg_right hmul (sq_nonneg L)
  have hcoeffReadable : δCoeff ≤ δCoeffReadable := by
    dsimp [δCoeff, δCoeffReadable]
    linarith
  have hrowEq : δRowExact = δRowReadable := by
    dsimp [δRowExact, δRowReadable]
    rw [frobNormSqRect_eq_nat_of_hasOrthonormalColumns U hU]
  have hbudgetExact :
      (let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) := by
    dsimp
    have hreadable : δCoeffReadable + δRowReadable ≤ δ := by
      simpa [δCoeffReadable, δRowReadable] using hbudget
    have hmono : δCoeff + δRowExact ≤ δCoeffReadable + δRowReadable := by
      rw [hrowEq]
      linarith
    exact hmono.trans hreadable
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U storedSignOf dhat grid hgrid hδgrid hρgrid hη hL hηRow
      hs hγm hγs hbudgetExact

/-- Concrete-denominator form of the orthonormal-input readable-budget wrapper
for stored-sign product-grid CountSketch plus downstream uniform-row
floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU storedSignOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for signs copied by
`fl_mul sign_i 1` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for signs copied by
`fl_add sign_i 0` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for signs copied by
`fl_sub sign_i 0` and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Finite-cover CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint when realized Rademacher signs are stored or copied
and each realized bucket is traversed in an exact fixed order.

The exact probability terms are unchanged from the exact-sign theorem.  The
computed event radius uses the stored-sign permuted-bucket
sparse-apply/downstream uniform-row budget, so every modeled non-probability
operation on this implementation path is charged. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf orderOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Ptot :=
    countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L
  let V : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) A
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      uniformRowSampleGramRowGramFrobErrorEvent (s := s) (V x) ηRow
  let Eprod : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    {x | x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1}
  let Epert : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A
      (countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
        fp A storedSignOf orderOf)
      dhat
      (countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
        fp A storedSignOf orderOf dhat)
  have hPre : 1 - δCS ≤ P.eventProb Epre := by
    simpa [P, Epre, δCS] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
        (r := r) (m := m) (n := n) (ι := ι)
        hr A net hcover hη hL hρ
  have hδRow_nonneg : 0 ≤ δRow := by
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    exact div_nonneg
      (mul_nonneg hrs_nonneg (sq_nonneg ((m : ℝ) * frobNormSqRect A)))
      (sq_nonneg ηRow)
  have hSample :
      ∀ x ∈ Epre, 1 - δRow ≤ Q.eventProb (Fsample x) := by
    intro x _hx
    have hbase :
        1 -
            (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          Q.eventProb (Fsample x) := by
      simpa [Q, Fsample] using
        uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
          (m := r) (s := s) (U := V x) hr hs ηRow hηRow
    have hsign_abs : ∀ k : Fin m, |rademacherSignVector x.2 k| ≤ 1 := by
      intro k
      simp [rademacherSignVector_abs x.2 k]
    have hV :
        frobNormSqRect (V x) ≤ (m : ℝ) * frobNormSqRect A := by
      simpa [V] using
        frobNormSqRect_preconditionRows_countSketchRows_le
          x.1 (rademacherSignVector x.2) A hsign_abs
    have hM_nonneg : 0 ≤ (m : ℝ) * frobNormSqRect A := by
      exact mul_nonneg (Nat.cast_nonneg m) (frobNormSqRect_nonneg A)
    have hV_abs :
        |frobNormSqRect (V x)| ≤ |(m : ℝ) * frobNormSqRect A| := by
      simpa [abs_of_nonneg (frobNormSqRect_nonneg (V x)),
        abs_of_nonneg hM_nonneg] using hV
    have hV_sq :
        frobNormSqRect (V x) ^ 2 ≤
          ((m : ℝ) * frobNormSqRect A) ^ 2 :=
      sq_le_sq.mpr hV_abs
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    have hbudgetRow :
        (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          δRow := by
      have hmul :
          ((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2 ≤
            ((r : ℝ) / (s : ℝ)) *
              ((m : ℝ) * frobNormSqRect A) ^ 2 :=
        mul_le_mul_of_nonneg_left hV_sq hrs_nonneg
      simpa [δRow] using
        div_le_div_of_nonneg_right hmul (sq_nonneg ηRow)
    have hleft :
        1 - δRow ≤
          1 - (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 := by
      linarith
    exact hleft.trans hbase
  have hprod :
      1 - (δCS + δRow) ≤ (P.prod Q).eventProb Eprod :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δCS δRow hδRow_nonneg hPre hSample
  have hprod' : 1 - (δCS + δRow) ≤ Ptot.eventProb Eprod := by
    simpa [Ptot, P, Q, Eprod, countSketchUniformRowTraceProbability] using hprod
  have hPertEq : Ptot.eventProb Epert = 1 := by
    simpa [Ptot, Epert] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf orderOf dhat hr hs hγm hγs
  have hPert : 1 - (0 : ℝ) ≤ Ptot.eventProb Epert := by
    rw [hPertEq]
    norm_num
  have hinter :
      1 - ((δCS + δRow) + 0) ≤ Ptot.eventProb (Eprod ∩ Epert) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Ptot Eprod Epert (δCS + δRow) 0 hprod' hPert
  have hsubset :
      Eprod ∩ Epert ⊆
        countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf orderOf dhat τCS ηRow := by
    intro x hx
    rcases hx with ⟨hprodMem, hpert⟩
    rcases hprodMem with ⟨hcs, hrow⟩
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let Vexact : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSignPermuted
        fp A storedSignOf orderOf x.1
    let τfp : ℝ :=
      countSketchSparseUniformRowComputedDenStoredSignPermutedPerturbBudget
        fp A storedSignOf orderOf dhat x
    let DeltaCS : Fin n → Fin n → ℝ :=
      fun j k => rowGram Vexact j k - rowGram A j k
    let DeltaRow : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Vexact x.2 j k - rowGram Vexact j k
    let DeltaPert : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          uniformRowSampleGram Vexact x.2 j k
    have hCS :
        finiteLoewnerLe DeltaCS
            (fun j k : Fin n => τCS * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin n => -DeltaCS j k)
            (fun j k : Fin n => τCS * finiteIdMatrix j k) := by
      simpa [Epre, countSketchRowGramTwoSidedLoewnerCoverEvent,
        DeltaCS, Vexact, sign, τCS] using hcs
    have hRow : frobNorm DeltaRow ≤ ηRow := by
      simpa [Fsample, uniformRowSampleGramRowGramFrobErrorEvent,
        DeltaRow, V, Vexact, sign] using hrow
    have hPertBound : frobNorm DeltaPert ≤ τfp := by
      simpa [Epert,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        DeltaPert, V, Vexact, Vhat, τfp, sign] using hpert
    have hrowAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        DeltaCS DeltaRow hCS.1 hCS.2 hRow
    have hallAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        (fun j k : Fin n => DeltaCS j k + DeltaRow j k)
        DeltaPert hrowAdd.1 hrowAdd.2 hPertBound
    have hsplit :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n =>
          (DeltaCS j k + DeltaRow j k) + DeltaPert j k) := by
      funext j k
      dsimp [DeltaCS, DeltaRow, DeltaPert]
      ring
    have hsplitNeg :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n =>
          -((DeltaCS j k + DeltaRow j k) + DeltaPert j k)) := by
      funext j k
      exact congrArg (fun z : ℝ => -z) (congrFun (congrFun hsplit j) k)
    have hUpper :
        finiteLoewnerLe
          (fun j k =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplit]
      simpa [add_assoc] using hallAdd.1
    have hLower :
        finiteLoewnerLe
          (fun j k =>
            -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplitNeg]
      simpa [add_assoc] using hallAdd.2
    exact ⟨hUpper, hLower⟩
  have hmono := FiniteProbability.eventProb_mono Ptot hsubset
  have hfinal := hinter.trans hmono
  simpa [add_assoc] using hfinal

/-- Product-grid specialization of the finite-cover CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint with stored
realized signs and exact per-bucket traversal orders. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf orderOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  have hcover :
      finiteUnitBallCover
        (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ :=
    finiteUnitBallCover_product_grid grid hgrid hδgrid hρgrid
  have hρ_nonneg : 0 ≤ ρ := by
    exact le_trans
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hδgrid) hρgrid
  simpa [τCS, δCS, δRow] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
      fp (r := r) (m := m) (n := n) (s := s) (ι := Fin n → α)
      hr A storedSignOf orderOf dhat
      (fun a : Fin n → α => fun j : Fin n => grid (a j))
      hcover hη hL hρ_nonneg hηRow hs hγm hγs

/-- Target-failure-budget wrapper for the stored-sign permuted-bucket
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf orderOf dhat τCS ηRow) := by
  intro τCS
  classical
  let δCS : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A storedSignOf orderOf dhat τCS ηRow) := by
    simpa [τCS, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
        fp (r := r) (m := m) (n := n) (s := s) (α := α)
        hr A storedSignOf orderOf dhat grid hgrid hδgrid hρgrid hη hL
        hηRow hs hγm hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow, add_assoc] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
permuted-bucket product-grid CountSketch plus downstream uniform-row
floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf orderOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for per-bucket permuted sparse
CountSketch, signs copied by `fl_mul sign_i 1`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for per-bucket permuted sparse
CountSketch, signs copied by `fl_add sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete product-grid downstream endpoint for per-bucket permuted sparse
CountSketch, signs copied by `fl_sub sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Orthonormal-input readable-budget wrapper for permuted-bucket stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf orderOf dhat τCS ηRow) := by
  intro τCS
  have hbudgetExact :
      (let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :=
    countSketchUniformRow_productGrid_orthonormal_coeff_add_frob_add_row_budget
      (r := r) (m := m) (n := n) (s := s) (α := α)
      U hU grid hbudget
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U storedSignOf orderOf dhat grid hgrid hδgrid hρgrid hη hL
      hηRow hs hγm hγs hbudgetExact

/-- Concrete-denominator form of the orthonormal-input readable-budget wrapper
for permuted-bucket stored-sign product-grid CountSketch plus downstream
uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU storedSignOf orderOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for per-bucket permuted
CountSketch, signs copied by `fl_mul sign_i 1`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for per-bucket permuted
CountSketch, signs copied by `fl_add sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Concrete orthonormal downstream endpoint for per-bucket permuted
CountSketch, signs copied by `fl_sub sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (orderOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        Fin (countSketchBucketSize hash i) ≃
          Fin (countSketchBucketSize hash i))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignPermutedComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          orderOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignPermutedComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      orderOf grid hgrid hδgrid hρgrid hη hL hηRow hs hγm hγs hbudget

/-- Finite-cover CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint when realized Rademacher signs are stored or copied
and each realized bucket is accumulated by an exact supplied summation tree.

The exact probability terms are unchanged from the exact-sign theorem.  The
computed event radius uses the stored-sign tree-reduced sparse-apply/downstream
uniform-row budget, so every modeled non-probability operation on this
implementation path is charged. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (net : ι → Fin n → ℝ)
    {ρ η L ηRow : ℝ}
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : ι,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (net a) p.1.1 *
              rectMatMulVec A (net a) p.1.2) ^ 2) / η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf treeOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  let P := countSketchProbability (r := r) (m := m) hr
  let Q := uniformRowTraceProbability (m := r) (steps := s) hr
  let Ptot :=
    countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let Epre : Set (CountSketchHash r m × RademacherTrace m) :=
    countSketchRowGramTwoSidedLoewnerCoverEvent (r := r) (m := m) A ρ η L
  let V : CountSketchHash r m × RademacherTrace m → Fin r → Fin n → ℝ :=
    fun x =>
      preconditionRows
        (countSketchRows x.1 (rademacherSignVector x.2)) A
  let Fsample : CountSketchHash r m × RademacherTrace m → Set (RowTrace r s) :=
    fun x =>
      uniformRowSampleGramRowGramFrobErrorEvent (s := s) (V x) ηRow
  let Eprod : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    {x | x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1}
  let Epert : Set ((CountSketchHash r m × RademacherTrace m) × RowTrace r s) :=
    countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp A
      (countSketchSparseComputedPreconditionedBasisWithStoredSignTree
        fp A storedSignOf treeOf)
      dhat
      (countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
        fp A storedSignOf treeOf dhat)
  have hPre : 1 - δCS ≤ P.eventProb Epre := by
    simpa [P, Epre, δCS] using
      countSketchProbability_eventProb_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob
        (r := r) (m := m) (n := n) (ι := ι)
        hr A net hcover hη hL hρ
  have hδRow_nonneg : 0 ≤ δRow := by
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    exact div_nonneg
      (mul_nonneg hrs_nonneg (sq_nonneg ((m : ℝ) * frobNormSqRect A)))
      (sq_nonneg ηRow)
  have hSample :
      ∀ x ∈ Epre, 1 - δRow ≤ Q.eventProb (Fsample x) := by
    intro x _hx
    have hbase :
        1 -
            (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          Q.eventProb (Fsample x) := by
      simpa [Q, Fsample] using
        uniformRowTraceProbability_eventProb_uniformRowSampleGram_frob_error_le_ge_one_sub_frobNorm
          (m := r) (s := s) (U := V x) hr hs ηRow hηRow
    have hsign_abs : ∀ k : Fin m, |rademacherSignVector x.2 k| ≤ 1 := by
      intro k
      simp [rademacherSignVector_abs x.2 k]
    have hV :
        frobNormSqRect (V x) ≤ (m : ℝ) * frobNormSqRect A := by
      simpa [V] using
        frobNormSqRect_preconditionRows_countSketchRows_le
          x.1 (rademacherSignVector x.2) A hsign_abs
    have hM_nonneg : 0 ≤ (m : ℝ) * frobNormSqRect A := by
      exact mul_nonneg (Nat.cast_nonneg m) (frobNormSqRect_nonneg A)
    have hV_abs :
        |frobNormSqRect (V x)| ≤ |(m : ℝ) * frobNormSqRect A| := by
      simpa [abs_of_nonneg (frobNormSqRect_nonneg (V x)),
        abs_of_nonneg hM_nonneg] using hV
    have hV_sq :
        frobNormSqRect (V x) ^ 2 ≤
          ((m : ℝ) * frobNormSqRect A) ^ 2 :=
      sq_le_sq.mpr hV_abs
    have hrs_nonneg : 0 ≤ (r : ℝ) / (s : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg r) (le_of_lt hs)
    have hbudgetRow :
        (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 ≤
          δRow := by
      have hmul :
          ((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2 ≤
            ((r : ℝ) / (s : ℝ)) *
              ((m : ℝ) * frobNormSqRect A) ^ 2 :=
        mul_le_mul_of_nonneg_left hV_sq hrs_nonneg
      simpa [δRow] using
        div_le_div_of_nonneg_right hmul (sq_nonneg ηRow)
    have hleft :
        1 - δRow ≤
          1 - (((r : ℝ) / (s : ℝ)) * frobNormSqRect (V x) ^ 2) / ηRow ^ 2 := by
      linarith
    exact hleft.trans hbase
  have hprod :
      1 - (δCS + δRow) ≤ (P.prod Q).eventProb Eprod :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      P Q Epre Fsample δCS δRow hδRow_nonneg hPre hSample
  have hprod' : 1 - (δCS + δRow) ≤ Ptot.eventProb Eprod := by
    simpa [Ptot, P, Q, Eprod, countSketchUniformRowTraceProbability] using hprod
  have hPertEq : Ptot.eventProb Epert = 1 := by
    simpa [Ptot, Epert] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp A storedSignOf treeOf dhat hr hs hdepth hγs
  have hPert : 1 - (0 : ℝ) ≤ Ptot.eventProb Epert := by
    rw [hPertEq]
    norm_num
  have hinter :
      1 - ((δCS + δRow) + 0) ≤ Ptot.eventProb (Eprod ∩ Epert) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Ptot Eprod Epert (δCS + δRow) 0 hprod' hPert
  have hsubset :
      Eprod ∩ Epert ⊆
        countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf treeOf dhat τCS ηRow := by
    intro x hx
    rcases hx with ⟨hprodMem, hpert⟩
    rcases hprodMem with ⟨hcs, hrow⟩
    let sign : Fin m → ℝ := rademacherSignVector x.1.2
    let Vexact : Fin r → Fin n → ℝ :=
      preconditionRows (countSketchRows x.1.1 sign) A
    let Vhat : Fin r → Fin n → ℝ :=
      countSketchSparseComputedPreconditionedBasisWithStoredSignTree
        fp A storedSignOf treeOf x.1
    let τfp : ℝ :=
      countSketchSparseUniformRowComputedDenStoredSignTreePerturbBudget
        fp A storedSignOf treeOf dhat x
    let DeltaCS : Fin n → Fin n → ℝ :=
      fun j k => rowGram Vexact j k - rowGram A j k
    let DeltaRow : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Vexact x.2 j k - rowGram Vexact j k
    let DeltaPert : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
          uniformRowSampleGram Vexact x.2 j k
    have hCS :
        finiteLoewnerLe DeltaCS
            (fun j k : Fin n => τCS * finiteIdMatrix j k) ∧
          finiteLoewnerLe (fun j k : Fin n => -DeltaCS j k)
            (fun j k : Fin n => τCS * finiteIdMatrix j k) := by
      simpa [Epre, countSketchRowGramTwoSidedLoewnerCoverEvent,
        DeltaCS, Vexact, sign, τCS] using hcs
    have hRow : frobNorm DeltaRow ≤ ηRow := by
      simpa [Fsample, uniformRowSampleGramRowGramFrobErrorEvent,
        DeltaRow, V, Vexact, sign] using hrow
    have hPertBound : frobNorm DeltaPert ≤ τfp := by
      simpa [Epert,
        countSketchComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        DeltaPert, V, Vexact, Vhat, τfp, sign] using hpert
    have hrowAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        DeltaCS DeltaRow hCS.1 hCS.2 hRow
    have hallAdd :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        (fun j k : Fin n => DeltaCS j k + DeltaRow j k)
        DeltaPert hrowAdd.1 hrowAdd.2 hPertBound
    have hsplit :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n =>
          (DeltaCS j k + DeltaRow j k) + DeltaPert j k) := by
      funext j k
      dsimp [DeltaCS, DeltaRow, DeltaPert]
      ring
    have hsplitNeg :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n =>
          -((DeltaCS j k + DeltaRow j k) + DeltaPert j k)) := by
      funext j k
      exact congrArg (fun z : ℝ => -z) (congrFun (congrFun hsplit j) k)
    have hUpper :
        finiteLoewnerLe
          (fun j k =>
            fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplit]
      simpa [add_assoc] using hallAdd.1
    have hLower :
        finiteLoewnerLe
          (fun j k =>
            -(fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => (τCS + ηRow + τfp) * finiteIdMatrix j k) := by
      rw [hsplitNeg]
      simpa [add_assoc] using hallAdd.2
    exact ⟨hUpper, hLower⟩
  have hmono := FiniteProbability.eventProb_mono Ptot hsubset
  have hfinal := hinter.trans hmono
  simpa [add_assoc] using hfinal

/-- Product-grid specialization of the finite-cover CountSketch plus
downstream uniform-row floating-point finite-Loewner endpoint with stored
realized signs and tree-reduced bucket accumulation. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    let δCS : ℝ :=
      ((∑ a : Fin n → α,
        (2 * (r : ℝ)⁻¹ *
          ∑ p : CountSketchDistinctPair m,
            (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
              rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
            η ^ 2) +
      (2 * (r : ℝ)⁻¹ *
        ∑ j : Fin n, ∑ k : Fin n,
          ∑ p : CountSketchDistinctPair m,
            (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
    let δRow : ℝ :=
      (((r : ℝ) / (s : ℝ)) *
        ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
    1 - (δCS + δRow) ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf treeOf dhat τCS ηRow) := by
  intro τCS δCS δRow
  classical
  have hcover :
      finiteUnitBallCover
        (fun a : Fin n → α => fun j : Fin n => grid (a j)) ρ :=
    finiteUnitBallCover_product_grid grid hgrid hδgrid hρgrid
  have hρ_nonneg : 0 ≤ ρ := by
    exact le_trans
      (mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hδgrid) hρgrid
  simpa [τCS, δCS, δRow] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_cover_ge_one_sub_sum_coeff_add_frob_add_row
      fp (r := r) (m := m) (n := n) (s := s) (ι := Fin n → α)
      hr A storedSignOf treeOf dhat
      (fun a : Fin n → α => fun j : Fin n => grid (a j))
      hcover hη hL hρ_nonneg hηRow hs hdepth hγs

/-- Target-failure-budget wrapper for the stored-sign tree-reduced product-grid
CountSketch plus downstream uniform-row floating-point finite-Loewner
endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf treeOf dhat τCS ηRow) := by
  intro τCS
  classical
  let δCS : ℝ :=
    ((∑ a : Fin n → α,
      (2 * (r : ℝ)⁻¹ *
        ∑ p : CountSketchDistinctPair m,
          (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
            rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
          η ^ 2) +
    (2 * (r : ℝ)⁻¹ *
      ∑ j : Fin n, ∑ k : Fin n,
        ∑ p : CountSketchDistinctPair m,
          (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
  let δRow : ℝ :=
    (((r : ℝ) / (s : ℝ)) *
      ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
  have hbase :
      1 - (δCS + δRow) ≤
        (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
            fp A storedSignOf treeOf dhat τCS ηRow) := by
    simpa [τCS, δCS, δRow] using
      countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_sum_coeff_add_frob_add_row
        fp (r := r) (m := m) (n := n) (s := s) (α := α)
        hr A storedSignOf treeOf dhat grid hgrid hδgrid hρgrid hη hL
        hηRow hs hdepth hγs
  have hbudget' : δCS + δRow ≤ δ := by
    simpa [δCS, δRow, add_assoc] using hbudget
  have hleft : 1 - δ ≤ 1 - (δCS + δRow) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator target-failure-budget wrapper for the stored-sign
tree-reduced product-grid CountSketch plus downstream uniform-row
floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A storedSignOf treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  simpa [τCS] using
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A storedSignOf treeOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete product-grid downstream endpoint for tree-reduced sparse
CountSketch, signs copied by `fl_mul sign_i 1`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete product-grid downstream endpoint for tree-reduced sparse
CountSketch, signs copied by `fl_add sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete product-grid downstream endpoint for tree-reduced sparse
CountSketch, signs copied by `fl_sub sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (A : Fin m → Fin n → ℝ)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec A (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (A p.1.1 j * A p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect A) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp A
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr A
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Orthonormal-input readable-budget wrapper for tree-reduced stored-sign
product-grid CountSketch plus downstream uniform-row floating-point
finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (dhat : ComputedUniformRowScaleDen fp r s)
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf treeOf dhat τCS ηRow) := by
  intro τCS
  have hbudgetExact :
      (let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            ∑ p : CountSketchDistinctPair m,
              (rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.1 *
                rectMatMulVec U (fun j : Fin n => grid (a j)) p.1.2) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin n,
            ∑ p : CountSketchDistinctPair m,
              (U p.1.1 j * U p.1.2 k) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) *
          ((m : ℝ) * frobNormSqRect U) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :=
    countSketchUniformRow_productGrid_orthonormal_coeff_add_frob_add_row_budget
      (r := r) (m := m) (n := n) (s := s) (α := α)
      U hU grid hbudget
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_coeff_add_frob_add_row_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U storedSignOf treeOf dhat grid hgrid hδgrid hρgrid hη hL
      hηRow hs hdepth hγs hbudgetExact

/-- Concrete-denominator form of the orthonormal-input readable-budget wrapper
for tree-reduced stored-sign product-grid CountSketch plus downstream
uniform-row floating-point finite-Loewner endpoint. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (storedSignOf :
      (ω : RademacherTrace m) → ComputedVector fp (rademacherSignVector ω))
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U storedSignOf treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU storedSignOf treeOf
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete orthonormal downstream endpoint for tree-reduced CountSketch,
signs copied by `fl_mul sign_i 1`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSign
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSign
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete orthonormal downstream endpoint for tree-reduced CountSketch,
signs copied by `fl_add sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignAddZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignAddZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignAddZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Concrete orthonormal downstream endpoint for tree-reduced CountSketch,
signs copied by `fl_sub sign_i 0`, and denominator computed as
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`. -/
theorem countSketchUniformRowTraceProbability_eventProb_sparseFlStoredSignSubZeroRightTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
    (fp : FPModel) {r m n s : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (hr : 0 < r)
    (U : Fin m → Fin n → ℝ) (hU : HasOrthonormalColumns U)
    (treeOf :
      (hash : CountSketchHash r m) → (i : Fin r) →
        SumTree (countSketchBucketSize hash i + 1))
    (grid : α → ℝ)
    {δgrid ρ η L ηRow δ : ℝ}
    (hgrid : realUnitIntervalCover grid δgrid)
    (hδgrid : 0 ≤ δgrid)
    (hρgrid : Real.sqrt (n : ℝ) * δgrid ≤ ρ)
    (hη : 0 < η) (hL : 0 < L)
    (hηRow : 0 < ηRow)
    (hs : 0 < (s : ℝ))
    (hdepth :
      ∀ (hash : CountSketchHash r m) (i : Fin r),
        gammaValid fp ((treeOf hash i).depth))
    (hγs : gammaValid fp s)
    (hbudget :
      let δCS : ℝ :=
        ((∑ a : Fin n → α,
          (2 * (r : ℝ)⁻¹ *
            vecNorm2Sq (fun j : Fin n => grid (a j)) ^ 2) /
              η ^ 2) +
        (2 * (r : ℝ)⁻¹ * (n : ℝ) ^ 2) / L ^ 2)
      let δRow : ℝ :=
        (((r : ℝ) / (s : ℝ)) * ((m : ℝ) * (n : ℝ)) ^ 2) / ηRow ^ 2
      δCS + δRow ≤ δ) :
    let τCS : ℝ := η + L * (2 * ρ + ρ ^ 2)
    1 - δ ≤
      (countSketchUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (countSketchSparseStoredSignTreeComputedPreconditionedFlUniformRowSampleGramWithComputedDenRowGramTwoSidedLoewnerEvent
          fp U
          (fun ω =>
            ComputedVector.flStoredSignSubZeroRight
              fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
          treeOf
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs) τCS ηRow) := by
  intro τCS
  exact
    countSketchUniformRowTraceProbability_eventProb_sparseStoredSignTreeComputedPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_rowGram_twoSidedLoewner_productGrid_ge_one_sub_delta_of_sum_gridNorm_add_nat_add_row_orthonormal_budget
      fp (r := r) (m := m) (n := n) (s := s) (α := α)
      hr U hU
      (fun ω =>
        ComputedVector.flStoredSignSubZeroRight
          fp (rademacherSignVector ω) (rademacherSignVector_abs ω))
      treeOf grid hgrid hδgrid hρgrid hη hL hηRow hs hdepth hγs hbudget

/-- Nonconditional finite signed-mixing FP endpoint with exact supplied
factors, rounded formation of `G diag(ω)`, rounded formation of
`Vhat = fl((G diag(ω))U)`, rounded row divisions by the exact mathematical
denominator, and rounded Gram dot products. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hr : 0 < r) (hn : 0 < n)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin n, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp
          (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
          ε
          (signedMixingComputedLeftUniformRowPerturbBudget fp G U Pihat)) := by
  intro Pihat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowSampleGramTwoSidedEvent G U ε) := by
    simpa using
      signedMixingUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
        G U hr hn hGorth hU halpha hB hs htheta hδSample hGcap
        hpreBudget hsampleBudget
  have hCompEq :
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowPerturbEvent
          fp G U
          (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
          (signedMixingComputedLeftUniformRowPerturbBudget
            fp G U Pihat)) = 1 := by
    simpa [Pihat] using
      signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
        fp G U Pihat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbEvent
            fp G U
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
            (signedMixingComputedLeftUniformRowPerturbBudget
              fp G U Pihat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (G := G) (U := U)
      (Vhat := signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
      (hr := hr) (ε := ε) (δExact := δPre + δSample)
      (δComp := 0)
      (τ := signedMixingComputedLeftUniformRowPerturbBudget fp G U Pihat)
      hExact hComp
  simpa [add_zero] using hTransfer

/-- Nonconditional finite signed-mixing FP endpoint with exact supplied
factors, rounded formation of `G diag(ω)`, rounded formation of
`Vhat = fl((G diag(ω))U)`, a computed uniform row-scale denominator, rounded
row divisions, and rounded Gram dot products. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hn : 0 < n)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin n, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
          dhat
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G U Pihat dhat)) := by
  intro Pihat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowSampleGramTwoSidedEvent G U ε) := by
    simpa using
      signedMixingUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
        G U hr hn hGorth hU halpha hB hs htheta hδSample hGcap
        hpreBudget hsampleBudget
  have hCompEq :
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp G U
          (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
          dhat
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G U Pihat dhat)) = 1 := by
    simpa [Pihat] using
      signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp G U Pihat dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp G U
            (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
            dhat
            (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
              fp G U Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (G := G) (U := U)
      (Vhat := signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := δPre + δSample) (δComp := 0)
      (τ := signedMixingComputedLeftUniformRowComputedDenPerturbBudget
        fp G U Pihat dhat)
      hExact hComp
  simpa [add_zero] using hTransfer

/-- Concrete-denominator finite signed-mixing FP endpoint with exact supplied
factors.  The denominator used by the implemented row scaling is
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`, represented by
`uniformRowFlSqrtMulInvSqrtScaleDen`; exact Rademacher and uniform-row laws
remain mathematical laws. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    (fp : FPModel) {r m n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hr : 0 < r) (hn : 0 < n)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin n, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (signedMixingComputedLeftPreconditionedBasis fp G U Pihat)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G U Pihat (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  simpa using
    signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
      fp G U (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hn hGorth hU halpha hB hs hγm hγs htheta hδSample
      hGcap hpreBudget hsampleBudget

/-- Exact sampled-Gram error for a rectangularly preconditioned factored input
`A = U C` is the right-factor congruence of the orthonormal-basis sampled-Gram
error. -/
theorem uniformRowSampleGram_rectFactoredInput_error_eq_rightGramCongruence_error
    {r m q n s : ℕ} (P : Fin r → Fin m → ℝ)
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (samples : RowTrace r s) (hU : HasOrthonormalColumns U)
    (hr : 0 < r) (hs : 0 < (s : ℝ)) :
    (fun j k : Fin n =>
        uniformRowSampleGram
            (preconditionRows P (preconditionColumns U C)) samples j k -
          rowGram (preconditionColumns U C) j k) =
      rightGramCongruence
        (fun a b : Fin q =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C := by
  classical
  let V : Fin r → Fin q → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  have hY :
      preconditionRows P A = preconditionColumns V C := by
    simpa [A, V] using preconditionRows_preconditionColumns_assoc_rect P U C
  have hsample :
      uniformRowSampleGram (preconditionRows P A) samples =
        rightGramCongruence (uniformRowSampleGram V samples) C := by
    rw [hY]
    exact
      uniformRowSampleGram_preconditionColumns_eq_rightGramCongruence
        V C samples hr hs
  have hAgram : rowGram A = rowGram C := by
    change rowGram (preconditionColumns U C) = rowGram C
    rw [rowGram_preconditionColumns_eq_rightGramCongruence]
    have hgram : rowGram U = idMatrix q :=
      rowGram_eq_id_of_orthonormal_columns U hU
    ext j k
    have hcong :
        rightGramCongruence
            (fun a b : Fin q => (1 : ℝ) * finiteIdMatrix a b) C j k =
          (fun j k : Fin n => (1 : ℝ) * rowGram C j k) j k := by
      simpa using
        congrFun (congrFun
          (rightGramCongruence_smul_finiteIdMatrix_eq_smul_rowGram C 1) j) k
    simpa [hgram, idMatrix] using hcong
  ext j k
  calc
    uniformRowSampleGram (preconditionRows P (preconditionColumns U C)) samples j k -
        rowGram (preconditionColumns U C) j k
        =
      rightGramCongruence (uniformRowSampleGram V samples) C j k -
        rightGramCongruence (finiteIdMatrix : Fin q → Fin q → ℝ) C j k := by
        simp [A, V, hsample, hAgram,
          rightGramCongruence_finiteIdMatrix_eq_rowGram]
    _ =
      rightGramCongruence
        (fun a b : Fin q =>
          uniformRowSampleGram (preconditionRows P U) samples a b -
            finiteIdMatrix a b) C j k := by
        have hsub :=
          congrFun (congrFun
            (rightGramCongruence_sub
              (uniformRowSampleGram V samples)
              (finiteIdMatrix : Fin q → Fin q → ℝ) C) j) k
        simpa [V] using hsub.symm

/-- Exact two-sided sampled-Gram event for a finite signed-mixing Algorithm 3
input matrix factored as `A = U C`, where `U` is the exact orthonormal analysis
basis. -/
def signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent
    {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ) (ε : ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    let P : Fin r → Fin m → ℝ :=
      signedMixingRows G (rademacherSignVector x.1)
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Y : Fin r → Fin n → ℝ := preconditionRows P A
    finiteLoewnerLe
      (fun j k : Fin n => uniformRowSampleGram Y x.2 j k - rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n => -(uniformRowSampleGram Y x.2 j k - rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k)}

/-- The orthonormal-basis signed-mixing sample-Gram event implies the
corresponding factored-input event for `A = U C`. -/
theorem signedMixingUniformRowSampleGramTwoSidedEvent_subset_factoredInput
    {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ) (ε : ℝ)
    (hU : HasOrthonormalColumns U) (hr : 0 < r) (hs : 0 < (s : ℝ)) :
    signedMixingUniformRowSampleGramTwoSidedEvent
        (r := r) (m := m) (n := q) (s := s) G U ε ⊆
      signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent
        (r := r) (m := m) (q := q) (n := n) (s := s) G U C ε := by
  classical
  intro x hx
  let P : Fin r → Fin m → ℝ :=
    signedMixingRows G (rademacherSignVector x.1)
  let V : Fin r → Fin q → ℝ := preconditionRows P U
  let A : Fin m → Fin n → ℝ := preconditionColumns U C
  let Y : Fin r → Fin n → ℝ := preconditionRows P A
  let ExactU : Fin q → Fin q → ℝ :=
    fun a b => uniformRowSampleGram V x.2 a b - finiteIdMatrix a b
  let ExactA : Fin n → Fin n → ℝ :=
    fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
  let EpsU : Fin q → Fin q → ℝ :=
    fun a b => ε * finiteIdMatrix a b
  let EpsA : Fin n → Fin n → ℝ :=
    fun j k => ε * rowGram A j k
  have hxU :
      finiteLoewnerLe ExactU EpsU ∧
      finiteLoewnerLe (fun a b : Fin q => -ExactU a b) EpsU := by
    simpa [signedMixingUniformRowSampleGramTwoSidedEvent, P, V, ExactU, EpsU]
      using hx
  have hErr :
      ExactA = rightGramCongruence ExactU C := by
    simpa [P, V, A, Y, ExactU, ExactA] using
      uniformRowSampleGram_rectFactoredInput_error_eq_rightGramCongruence_error
        P U C x.2 hU hr hs
  have hEps :
      rightGramCongruence EpsU C = EpsA := by
    simpa [A, EpsU, EpsA] using
      rightGramCongruence_smul_finiteIdMatrix_eq_smul_factoredInputGram
        U C hU ε
  have hUpperBase :
      finiteLoewnerLe (rightGramCongruence ExactU C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.1
  have hLowerBase :
      finiteLoewnerLe
        (rightGramCongruence (fun a b : Fin q => -ExactU a b) C)
        (rightGramCongruence EpsU C) :=
    finiteLoewnerLe_rightGramCongruence C hxU.2
  have hUpper : finiteLoewnerLe ExactA EpsA := by
    rw [hErr, ← hEps]
    exact hUpperBase
  have hNegErr :
      (fun j k : Fin n => -ExactA j k) =
        rightGramCongruence (fun a b : Fin q => -ExactU a b) C := by
    rw [hErr]
    rw [rightGramCongruence_neg]
  have hLower : finiteLoewnerLe (fun j k : Fin n => -ExactA j k) EpsA := by
    rw [hNegErr, ← hEps]
    exact hLowerBase
  simpa [signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent,
    P, A, Y, ExactA, EpsA] using And.intro hUpper hLower

/-- Exact finite signed-mixing preprocessing plus uniform row sampling for the
actual Algorithm 3 input matrix `A = U C`.  The signs and uniform row law remain
exact; `U` and `C` are exact analysis factors. -/
theorem signedMixingUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    {r m q n s : ℕ} (G : Fin r → Fin m → ℝ)
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hq : 0 < q)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin q, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((q : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent
          G U C ε) := by
  have hExactU :
      1 - (δPre + δSample) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowSampleGramTwoSidedEvent G U ε) := by
    simpa using
      signedMixingUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
        G U hr hq hGorth hU halpha hB hs htheta hδSample hGcap
        hpreBudget hsampleBudget
  exact hExactU.trans
    (FiniteProbability.eventProb_mono
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr)
      (signedMixingUniformRowSampleGramTwoSidedEvent_subset_factoredInput
        (r := r) (m := m) (q := q) (n := n) (s := s) G U C ε hU hr hs))

/-- Fully floating-point computed-input event for finite signed mixing on a
factored input `A = U C`, using a computed uniform row-scale denominator. -/
def signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
    (fp : FPModel) {r m q n s : ℕ}
    (U : Fin m → Fin q → ℝ) (C : Fin q → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (ε : ℝ) (τ : RademacherTrace m × RowTrace r s → ℝ) :
    Set (RademacherTrace m × RowTrace r s) :=
  {x |
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    finiteLoewnerLe
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k)
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) ∧
    finiteLoewnerLe
      (fun j k : Fin n =>
        -(fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          rowGram A j k))
      (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k)}

/-- Transfer an exact finite signed-mixing factored-input event and a concrete
computed perturbation event to the fully floating-point sampled Gram. -/
theorem signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace r s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent
            G U C ε))
    (hComp :
      1 - δComp ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp G (preconditionColumns U C) Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C Vhat dhat ε τ) := by
  classical
  let Pprob := signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr
  let E : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent G U C ε
  let F : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp G (preconditionColumns U C) Vhat dhat τ
  let M : Set (RademacherTrace m × RowTrace r s) :=
    signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp U C Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ Pprob.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      Pprob E F δExact δComp (by simpa [Pprob, E] using hExact)
        (by simpa [Pprob, F] using hComp)
  have hsubset : E ∩ F ⊆ M := by
    intro x hx
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pmat : Fin r → Fin m → ℝ :=
      signedMixingRows G (rademacherSignVector x.1)
    let Y : Fin r → Fin n → ℝ := preconditionRows Pmat A
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram Y x.2 j k - rowGram A j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram Y x.2 j k
    let Eps : Fin n → Fin n → ℝ :=
      fun j k => ε * rowGram A j k
    have hxExact :
        finiteLoewnerLe Exact Eps ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k) Eps := by
      simpa [E, signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent,
        A, Pmat, Y, Exact, Eps] using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        A, Pmat, Y, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_general_of_frobNorm_le
        Exact Delta Eps hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            rowGram A j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k)
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              rowGram A j k))
          (fun j k : Fin n => ε * rowGram A j k + τ x * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    exact ⟨hUpper, hLower⟩
  exact hInter.trans (by
    simpa [Pprob, M] using FiniteProbability.eventProb_mono Pprob hsubset)

/-- Nonconditional finite signed-mixing FP endpoint for an actual Algorithm 3
input factored as `A = U C`, using exact supplied `G`, exact analysis factors
`U,C`, rounded `G diag(ω)`, rounded `Vhat = fl(Pihat * A)`, a computed
uniform row-scale denominator, rounded row divisions, and rounded Gram dot
products. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    (fp : FPModel) {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hq : 0 < q)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin q, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((q : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
          dhat
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G A Pihat dhat)) := by
  intro A Pihat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingUniformRowFactoredInputSampleGramTwoSidedEvent
            G U C ε) := by
    simpa using
      signedMixingUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
        G U C hr hq hGorth hU halpha hB hs htheta hδSample hGcap
        hpreBudget hsampleBudget
  have hCompEq :
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp G A
          (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
          dhat
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G A Pihat dhat)) = 1 := by
    simpa [A, Pihat] using
      signedMixingUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp G A Pihat dhat hr hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp G A
            (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
            dhat
            (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
              fp G A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have hTransfer :=
    signedMixingUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      (fp := fp) (G := G) (U := U) (C := C)
      (Vhat := signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
      (dhat := dhat) (hr := hr) (ε := ε)
      (δExact := δPre + δSample) (δComp := 0)
      (τ := signedMixingComputedLeftUniformRowComputedDenPerturbBudget
        fp G A Pihat dhat)
      hExact hComp
  simpa [A, Pihat, add_zero] using hTransfer

/-- Total-failure-budget form of the actual-input finite signed-mixing endpoint.

This is the same fully computed theorem as
`..._ge_one_sub_delta_of_entry_sq_le_uniform`, but the preprocessing and sample
failures are combined into a single target `δ`. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_total_budget
    (fp : FPModel) {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp r s)
    (hr : 0 < r) (hq : 0 < q)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample δ : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin q, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((q : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget : δPre + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - δ ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
          dhat
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G A Pihat dhat)) := by
  intro A Pihat
  have hbase :
      1 - (δPre + δSample) ≤
        (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
          (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
            fp U C
            (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
            dhat
            ε
            (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
              fp G A Pihat dhat)) := by
    simpa [A, Pihat] using
      signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
        fp G U C dhat hr hq hGorth hU halpha hB hs hγm hγs htheta
        hδSample hGcap hpreBudget hsampleBudget
  have hleft : 1 - δ ≤ 1 - (δPre + δSample) := by
    linarith
  exact hleft.trans hbase

/-- Concrete-denominator finite signed-mixing FP endpoint for an actual input
factored as `A = U C`.  The theorem instantiates the generic computed
denominator with `fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt r))`, charging rounded
denominator formation in addition to rounded `G diag(ω)`, `Vhat`, row
division, and Gram-dot arithmetic. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
    (fp : FPModel) {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hq : 0 < q)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin q, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((q : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - (δPre + δSample) ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G A Pihat (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  simpa using
    signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_entry_sq_le_uniform
      fp G U C (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hq hGorth hU halpha hB hs hγm hγs htheta hδSample
      hGcap hpreBudget hsampleBudget

/-- Total-failure-budget version of the concrete-denominator finite
signed-mixing factored-input FP endpoint. -/
theorem signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_total_budget
    (fp : FPModel) {r m q n s : ℕ}
    (G : Fin r → Fin m → ℝ) (U : Fin m → Fin q → ℝ)
    (C : Fin q → Fin n → ℝ)
    (hr : 0 < r) (hq : 0 < q)
    (hGorth : HasOrthonormalColumns G) (hU : HasOrthonormalColumns U)
    {alpha B theta ε δPre δSample δ : ℝ}
    (halpha : 0 < alpha) (hB : 0 < B)
    (hs : 0 < (s : ℝ)) (hγm : gammaValid fp m)
    (hγs : gammaValid fp s) (htheta : 0 < theta)
    (hδSample : 0 ≤ δSample)
    (hGcap : ∀ i : Fin r, ∀ k : Fin m, G i k ^ 2 ≤ alpha ^ 2)
    (hpreBudget :
      (∑ _i : Fin r,
        ∑ _j : Fin q, 2 * Real.exp (-(B ^ 2 / (2 * alpha ^ 2)))) ≤
        δPre)
    (hsampleBudget :
      let L : ℝ := (r : ℝ) * ((q : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((q : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample)
    (htotalBudget : δPre + δSample ≤ δ) :
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (signedMixingRows G (rademacherSignVector ω)) :=
      fun ω => signedMixingExactFactorPreconditioner fp G ω hγm
    1 - δ ≤
      (signedMixingUniformRowTraceProbability (r := r) (m := m) (s := s) hr).eventProb
        (signedMixingComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedMixingComputedLeftPreconditionedBasis fp G A Pihat)
          (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
          ε
          (signedMixingComputedLeftUniformRowComputedDenPerturbBudget
            fp G A Pihat (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs))) := by
  simpa using
    signedMixingUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_total_budget
      fp G U C (uniformRowFlSqrtMulInvSqrtScaleDen fp hr hs hγs)
      hr hq hGorth hU halpha hB hs hγm hγs htheta hδSample
      hGcap hpreBudget hsampleBudget htotalBudget

/-- Sample-dependent perturbation budget for the concrete computed-left and
computed-input Algorithm 3 path.  The first term charges rounded row scaling
and sampled-Gram dot products after `Vhat` has been formed.  The second term
charges the difference between the exact sampled Gram of
`Vhat = fl(Pihat * Uhat)` and that of the ideal signed-Hadamard basis
`H D_ω U`. -/
noncomputable def signedHadamardComputedLeftInputUniformRowPerturbBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (x : RademacherTrace m × RowTrace m s) : ℝ :=
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
      fp H Uhat Pihat x.1
  uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- The concrete computed-left and computed-input preconditioned basis
satisfies the generic computed-`Vhat` perturbation event with probability one
under the joint signed-Hadamard/uniform-row law.  This theorem charges a
computed basis or singular-vector table through `Uhat` instead of silently using
the exact analysis basis as an implemented object. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp H U
        (signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat)
        (signedHadamardComputedLeftInputUniformRowPerturbBudget
          fp H Uhat Pihat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
      fp H Uhat Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDot fp s Vhat x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E,
      signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftInputEntryErrorBudget_nonneg
          fp (Pihat x.1) Uhat hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedHadamardComputedLeftInputPreconditionedBasis,
      signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeftInput_entry_error_budget_bound
          fp (Pihat x.1) Uhat hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDot_perturb_bound fp Vhat hm hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hm hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedHadamardComputedLeftInputPreconditionedBasis
              fp H Uhat Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDot fp s
            (signedHadamardComputedLeftInputPreconditionedBasis
              fp H Uhat Pihat x.1)
            x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramFullFpPerturbBudget fp s Vhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedHadamardComputedLeftInputUniformRowPerturbBudget
          fp H Uhat Pihat x := by
        simp [signedHadamardComputedLeftInputUniformRowPerturbBudget, V, Vhat, E]

/-- Sample-dependent perturbation budget for the concrete computed-left and
computed-input Algorithm 3 path when the uniform row-scale denominator is
computed.  It charges the computed denominator, rounded row divisions, rounded
Gram dot products, the computed left preconditioner, and the computed/stored
input matrix before comparing back to the exact signed-Hadamard product
`H D_ω U`. -/
noncomputable def signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (dhat : ComputedUniformRowScaleDen fp m s)
    (x : RademacherTrace m × RowTrace m s) : ℝ :=
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
      fp H Uhat Pihat x.1
  uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
    uniformRowSampleGramBasisPerturbBudget V Vhat E x.2

/-- The concrete computed-left and computed-input preconditioned basis with a
computed uniform row-scale denominator satisfies the computed-denominator
perturbation event with probability one under the joint signed-Hadamard/uniform
row law.  This theorem charges a computed or stored input matrix through
`Uhat` and does not add any probability-construction loss. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) {U : Fin m → Fin n → ℝ}
    (Uhat : ComputedMatrix fp U)
    (Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))))
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
        fp H U
        (signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat)
        dhat
        (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
          fp H Uhat Pihat dhat)) = 1 := by
  classical
  apply FiniteProbability.eventProb_eq_one_of_forall
  intro x
  let V : Fin m → Fin n → ℝ :=
    preconditionRows
      (matMul m H (diagMatrix (rademacherSignVector x.1))) U
  let Vhat : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasis fp H Uhat Pihat x.1
  let E : Fin m → Fin n → ℝ :=
    signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget
      fp H Uhat Pihat x.1
  let DeltaFp : Fin n → Fin n → ℝ :=
    fun j k =>
      fl_uniformRowSampleGramDotWithComputedDen fp s Vhat dhat.den x.2 j k -
        uniformRowSampleGram Vhat x.2 j k
  let DeltaBasis : Fin n → Fin n → ℝ :=
    fun j k =>
      uniformRowSampleGram Vhat x.2 j k -
        uniformRowSampleGram V x.2 j k
  have hE_nonneg : ∀ i j, 0 ≤ E i j := by
    intro i j
    simpa [E,
      signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget]
      using
        flPreconditionRowsWithComputedLeftInputEntryErrorBudget_nonneg
          fp (Pihat x.1) Uhat hγm i j
  have hVentry : ∀ i j, |Vhat i j - V i j| ≤ E i j := by
    intro i j
    simpa [V, Vhat, E, signedHadamardComputedLeftInputPreconditionedBasis,
      signedHadamardComputedLeftInputPreconditionedBasisEntryErrorBudget]
      using
        fl_preconditionRowsWithComputedLeftInput_entry_error_budget_bound
          fp (Pihat x.1) Uhat hγm i j
  have hFp :
      frobNorm DeltaFp ≤
        uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 := by
    simpa [DeltaFp, Vhat] using
      fl_uniformRowSampleGramDotWithComputedDen_perturb_bound
        fp Vhat dhat hm hs hγs x.2
  have hBasis :
      frobNorm DeltaBasis ≤
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 := by
    simpa [DeltaBasis] using
      uniformRowSampleGram_frob_error_bound_of_basis_entrywise_abs
        V Vhat E x.2 hm hs hE_nonneg hVentry
  have hsplit :
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedHadamardComputedLeftInputPreconditionedBasis
              fp H Uhat Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k) =
      (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
    funext j k
    dsimp [DeltaFp, DeltaBasis, V, Vhat]
    ring
  have htri := frobNorm_add_le DeltaFp DeltaBasis
  calc
    frobNorm
      (fun j k : Fin n =>
        fl_uniformRowSampleGramDotWithComputedDen fp s
            (signedHadamardComputedLeftInputPreconditionedBasis
              fp H Uhat Pihat x.1)
            dhat.den x.2 j k -
          uniformRowSampleGram
            (preconditionRows
              (matMul m H (diagMatrix (rademacherSignVector x.1))) U)
            x.2 j k)
        =
      frobNorm (fun j k : Fin n => DeltaFp j k + DeltaBasis j k) := by
        rw [hsplit]
    _ ≤ frobNorm DeltaFp + frobNorm DeltaBasis := htri
    _ ≤ uniformRowSampleGramComputedDenFullFpPerturbBudget fp Vhat dhat x.2 +
        uniformRowSampleGramBasisPerturbBudget V Vhat E x.2 :=
        add_le_add hFp hBasis
    _ =
        signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
          fp H Uhat Pihat dhat x := by
        simp [signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget,
          V, Vhat, E]

/-- Exact/stored signed-Hadamard specialization of the concrete computed-left
perturbation certificate.  This closes the zero-transform-storage baseline for
the SRHT computed-`Vhat` path: the perturbation event still charges rounded
formation of `Vhat`, rounded row scaling, and rounded Gram dot products, but
not preprocessing-matrix storage error. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_exactStoredComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp H U
        (signedHadamardComputedLeftPreconditionedBasis fp H U
          (signedHadamardExactStoredPreconditioner fp H))
        (signedHadamardComputedLeftUniformRowPerturbBudget fp H U
          (signedHadamardExactStoredPreconditioner fp H))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp H U (signedHadamardExactStoredPreconditioner fp H) hm hs hγm hγs

/-- Exact signed-Hadamard factors with rounded preconditioner formation still
instantiate the computed-left SRHT perturbation event with probability one.
Compared with `signedHadamardExactStoredPreconditioner`, the transform budget
now includes the rounded product that forms `H * diag(sign)`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_exactFactorComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp H U
        (signedHadamardComputedLeftPreconditionedBasis fp H U
          (fun ω => signedHadamardExactFactorPreconditioner fp H ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget fp H U
          (fun ω => signedHadamardExactFactorPreconditioner fp H ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp H U
      (fun ω => signedHadamardExactFactorPreconditioner fp H ω hγm)
      hm hs hγm hγs

/-- A supplied sign-pattern table with rounded `sqrt (1 / m)` scaling and
rounded signed preconditioner formation instantiates the computed-left SRHT
perturbation event with probability one.  The Rademacher and uniform-row laws
remain exact; the budget charges the rounded scale table, `H D_omega`
formation, `Vhat` formation, row scaling, and Gram dot products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
        (signedHadamardComputedLeftPreconditionedBasis
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternPreconditioner fp S ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternPreconditioner fp S ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
      (fun ω => signedHadamardScaledPatternPreconditioner fp S ω hγm)
      hm hs hγm hγs

/-- A supplied sign-pattern table with rounded `sqrt (1 / m)` scaling,
rounded storage of the realized Rademacher signs, and rounded signed
preconditioner formation instantiates the computed-left SRHT perturbation
event with probability one.  The Rademacher and uniform-row laws remain exact;
the budget charges the rounded scale table, sign storage, `H D_omega`
formation, `Vhat` formation, row scaling, and Gram dot products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
        (signedHadamardComputedLeftPreconditionedBasis
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
      (fun ω =>
        signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm)
      hm hs hγm hγs

/-- A supplied sign-pattern table with rounded `sqrt (1 / m)` scaling,
rounded add-zero storage of the realized Rademacher signs, and rounded signed
preconditioner formation instantiates the computed-left SRHT perturbation
event with probability one.  The Rademacher and uniform-row laws remain exact;
the budget charges the rounded scale table, add-zero sign storage,
`H D_omega` formation, `Vhat` formation, row scaling, and Gram dot products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
        (signedHadamardComputedLeftPreconditionedBasis
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignAddZeroRightPreconditioner
              fp S ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignAddZeroRightPreconditioner
              fp S ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
      (fun ω =>
        signedHadamardScaledPatternStoredSignAddZeroRightPreconditioner
          fp S ω hγm)
      hm hs hγm hγs

/-- A supplied sign-pattern table with rounded `sqrt (1 / m)` scaling,
rounded subtract-zero storage of the realized Rademacher signs, and rounded
signed preconditioner formation instantiates the computed-left SRHT
perturbation event with probability one.  The Rademacher and uniform-row laws
remain exact; the budget charges the rounded scale table, subtract-zero sign
storage, `H D_omega` formation, `Vhat` formation, row scaling, and Gram dot
products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
        (signedHadamardComputedLeftPreconditionedBasis
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignSubZeroRightPreconditioner
              fp S ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
          (fun ω =>
            signedHadamardScaledPatternStoredSignSubZeroRightPreconditioner
              fp S ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k) U
      (fun ω =>
        signedHadamardScaledPatternStoredSignSubZeroRightPreconditioner
          fp S ω hγm)
      hm hs hγm hγs

/-- The concrete generated Sylvester/Walsh sign-pattern table with rounded
`sqrt (1 / 2^p)` scaling and rounded signed-preconditioner formation
instantiates the computed-left SRHT perturbation event with probability one.
The bit-parity table, Rademacher law, and uniform-row law are exact; the budget
charges scale formation, `H D_omega` formation, `Vhat` formation, row scaling,
and Gram dot products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternPreconditioner fp ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternPreconditioner fp ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterPatternPreconditioner fp ω hγm)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner instantiates the computed-left SRHT perturbation event
with probability one.  The Rademacher and uniform-row laws remain exact; the
budget charges the generated FHT butterfly schedule, rounded FHT scale,
`Vhat` formation, row scaling, and Gram dot products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtSchedulePreconditioner fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtSchedulePreconditioner fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtSchedulePreconditioner fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with explicit rounded add-zero storage/copy after every
FHT pair update instantiates the computed-left SRHT perturbation event with
probability one.  The Rademacher and uniform-row laws remain exact; only
non-probability writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredAddZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredAddZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredAddZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with explicit rounded multiply-one storage/copy after
every FHT pair update instantiates the computed-left SRHT perturbation event
with probability one.  The Rademacher and uniform-row laws remain exact; only
non-probability writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredMulOneComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredMulOnePreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredMulOnePreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredMulOnePreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with explicit rounded subtract-zero storage/copy after
every FHT pair update instantiates the computed-left SRHT perturbation event
with probability one.  The Rademacher and uniform-row laws remain exact; only
non-probability writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSubZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSubZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSubZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with modified-coordinate rounded add-zero writeback
instantiates the computed-left SRHT perturbation event with probability one.
The Rademacher and uniform-row laws remain exact; only non-probability
writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleModifiedStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleModifiedStoredAddZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with modified-coordinate rounded multiply-one writeback
instantiates the computed-left SRHT perturbation event with probability one.
The Rademacher and uniform-row laws remain exact; only non-probability
writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleModifiedStoredMulOneComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredMulOnePreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredMulOnePreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleModifiedStoredMulOnePreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of the concrete Sylvester/Walsh
`H D_ω` preconditioner with modified-coordinate rounded subtract-zero
writeback instantiates the computed-left SRHT perturbation event with
probability one.  The Rademacher and uniform-row laws remain exact; only
non-probability writeback arithmetic is added to the existing FHT budget. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleModifiedStoredSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleModifiedStoredSubZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded Rademacher-sign
storage before the FHT stages instantiates the computed-left SRHT perturbation
event with probability one.  Only non-probability storage/arithmetic is
charged; the Rademacher and uniform-row laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignPreconditioner fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and explicit rounded add-zero
storage/copy after every FHT pair update instantiates the computed-left SRHT
perturbation event with probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and explicit rounded multiply-one
storage/copy after every FHT pair update instantiates the computed-left SRHT
perturbation event with probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredMulOneComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredMulOnePreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredMulOnePreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredMulOnePreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and explicit rounded subtract-zero
storage/copy after every FHT pair update instantiates the computed-left SRHT
perturbation event with probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredSubZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignStoredSubZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredSubZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and modified-coordinate rounded
add-zero writeback instantiates the computed-left SRHT perturbation event with
probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and modified-coordinate rounded
multiply-one writeback instantiates the computed-left SRHT perturbation event
with probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredMulOneComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredMulOnePreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredMulOnePreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredMulOnePreconditioner
          fp ω)
      hm hs hγm hγs

/-- The fast generated-FHT computation of `H D_ω` with rounded
`fl_mul sign_i 1` Rademacher-sign storage and modified-coordinate rounded
subtract-zero writeback instantiates the computed-left SRHT perturbation
event with probability one.  Probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightPreconditioner
              fp ω))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightPreconditioner
              fp ω))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightPreconditioner
          fp ω)
      hm hs hγm hγs

/-- The concrete generated Sylvester/Walsh sign-pattern table with rounded
scale formation, rounded `fl_mul sign_i 1` Rademacher-sign storage, and rounded
signed-preconditioner formation instantiates the computed-left SRHT
perturbation event with probability one.  The probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignPreconditioner
              fp ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignPreconditioner
              fp ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterPatternStoredSignPreconditioner fp ω hγm)
      hm hs hγm hγs

/-- The concrete generated Sylvester/Walsh sign-pattern table with rounded
scale formation, rounded `fl_add sign_i 0` Rademacher-sign storage, and rounded
signed-preconditioner formation instantiates the computed-left SRHT
perturbation event with probability one.  The probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternStoredSignAddZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignAddZeroRightPreconditioner
              fp ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignAddZeroRightPreconditioner
              fp ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterPatternStoredSignAddZeroRightPreconditioner
          fp ω hγm)
      hm hs hγm hγs

/-- The concrete generated Sylvester/Walsh sign-pattern table with rounded
scale formation, rounded `fl_sub sign_i 0` Rademacher-sign storage, and rounded
signed-preconditioner formation instantiates the computed-left SRHT
perturbation event with probability one.  The probability laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterPatternStoredSignSubZeroRightComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
    (fp : FPModel) {p n s : ℕ}
    (U : Fin (2 ^ p) → Fin n → ℝ)
    (hm : 0 < 2 ^ p) (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s) :
    (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
      (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
        fp
        (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
          sylvesterHadamardSignPattern p i k)
        U
        (signedHadamardComputedLeftPreconditionedBasis
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignSubZeroRightPreconditioner
              fp ω hγm))
        (signedHadamardComputedLeftUniformRowPerturbBudget
          fp
          (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
            sylvesterHadamardSignPattern p i k)
          U
          (fun ω =>
            signedHadamardSylvesterPatternStoredSignSubZeroRightPreconditioner
              fp ω hγm))) = 1 := by
  simpa using
    signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
      fp
      (fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k)
      U
      (fun ω =>
        signedHadamardSylvesterPatternStoredSignSubZeroRightPreconditioner
          fp ω hγm)
      hm hs hγm hγs

/-- Generic transfer from the exact signed-Hadamard/uniform-row event to an
implemented preprocessed basis `Vhat`.  The theorem does not assume the
preprocessing arithmetic is exact: all errors in computing `Vhat`, row scaling,
and the final Gram entries are charged by the perturbation event. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hm : 0 < m) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε))
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
            fp H U Vhat τ)) :
    1 - (δExact + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp Vhat ε τ) := by
  classical
  let P := signedHadamardUniformRowTraceProbability (m := m) (s := s) hm
  let E : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardUniformRowSampleGramTwoSidedEvent H U ε
  let F : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
      fp H U Vhat τ
  let G : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
      fp Vhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F δExact δComp (by simpa [P, E] using hExact)
        (by simpa [P, F] using hComp)
  have hsubset : E ∩ F ⊆ G := by
    intro x hx
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxExact :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [E, signedHadamardUniformRowSampleGramTwoSidedEvent, V, Exact]
        using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F, signedHadamardComputedPreconditionedFlUniformRowPerturbEvent,
        V, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
            finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDot fp s (Vhat x.1) x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [G,
      signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent]
      using And.intro hUpper hLower
  exact hInter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Generic transfer from the exact signed-Hadamard/uniform-row event to an
implemented preprocessed basis whose uniform row-scale denominator is computed
in floating point.  All non-probability computation is charged by the supplied
computed-denominator perturbation event. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hm : 0 < m) {ε δExact δComp : ℝ}
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hExact :
      1 - δExact ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε))
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H U Vhat dhat τ)) :
    1 - (δExact + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp Vhat dhat ε τ) := by
  classical
  let P := signedHadamardUniformRowTraceProbability (m := m) (s := s) hm
  let E : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardUniformRowSampleGramTwoSidedEvent H U ε
  let F : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
      fp H U Vhat dhat τ
  let G : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
      fp Vhat dhat ε τ
  have hInter :
      1 - (δExact + δComp) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F δExact δComp (by simpa [P, E] using hExact)
        (by simpa [P, F] using hComp)
  have hsubset : E ∩ F ⊆ G := by
    intro x hx
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDotWithComputedDen
            fp s (Vhat x.1) dhat.den x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxExact :
        finiteLoewnerLe Exact
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe (fun j k : Fin n => -Exact j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [E, signedHadamardUniformRowSampleGramTwoSidedEvent, V, Exact]
        using hx.1
    have hpert : frobNorm Delta ≤ τ x := by
      simpa [F,
        signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent,
        V, Delta] using hx.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxExact.1 hxExact.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDotWithComputedDen
              fp s (Vhat x.1) dhat.den x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDotWithComputedDen
                fp s (Vhat x.1) dhat.den x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ x) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [G,
      signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent]
      using And.intro hUpper hLower
  exact hInter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Coordinate-Hoeffding signed-Hadamard preprocessing composed with iid uniform
row sampling, with the sampled Gram matrix formed in floating point.

This is the floating-point transfer for the scoped Algorithm 3 route: it reuses
the exact joint preprocessing-plus-uniform-sampling theorem and the local
division/dot-product perturbation bound above. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) (hn : 0 < n)
    {B lam theta ε δPre δSample : ℝ}
    (hB : 0 < B) (hlam : 0 < lam) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hpreBudget :
      (∑ _ij : Fin m × Fin n,
        2 * (Real.exp (-(lam * B)) *
          Real.exp ((lam ^ 2 * (m : ℝ)⁻¹) / 2))) ≤ δPre)
    (hsampleBudget :
      let L : ℝ := (m : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardFlUniformRowSampleGramTwoSidedEvent fp H U ε) := by
  classical
  let P := signedHadamardUniformRowTraceProbability (m := m) (s := s) hm
  let E : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardUniformRowSampleGramTwoSidedEvent H U ε
  let G : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardFlUniformRowSampleGramTwoSidedEvent fp H U ε
  have hExact :
      1 - (δPre + δSample) ≤ P.eventProb E := by
    simpa [P, E] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta
        H U hH hflat hU hm hn hB hlam hs htheta hδSample
        hpreBudget hsampleBudget
  have hsubset : E ⊆ G := by
    intro x hx
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    let τ : ℝ := uniformRowSampleGramFullFpPerturbBudget fp s V x.2
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDot fp s V x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hpert : frobNorm Delta ≤ τ := by
      simpa [Delta, τ] using
        fl_uniformRowSampleGramDot_perturb_bound fp V hm hs hγ x.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hx.1 hx.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDot fp s V x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact hUpperAdd
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDot fp s V x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact hLowerAdd
    simpa [G, signedHadamardFlUniformRowSampleGramTwoSidedEvent, V, τ] using
      And.intro hUpper hLower
  exact hExact.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Coordinate-Hoeffding signed-Hadamard preprocessing with an implemented
preprocessed basis `Vhat`.  The additional `δComp` event charges every
floating-point operation used to build `Vhat` and then compute the sampled Gram
from it. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) (hn : 0 < n)
    {B lam theta ε δPre δSample δComp : ℝ}
    (hB : 0 < B) (hlam : 0 < lam) (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
            fp H U Vhat τ))
    (hpreBudget :
      (∑ _ij : Fin m × Fin n,
        2 * (Real.exp (-(lam * B)) *
          Real.exp ((lam ^ 2 * (m : ℝ)⁻¹) / 2))) ≤ δPre)
    (hsampleBudget :
      let L : ℝ := (m : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp Vhat ε τ) := by
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
    simpa using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta
        H U hH hflat hU hm hn hB hlam hs htheta hδSample
        hpreBudget hsampleBudget
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U Vhat hm τ hExact hComp
  simpa [add_assoc] using h

/-- Constant-radius coordinate-Hoeffding wrapper for an implemented
preprocessed basis `Vhat`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) (hn : 0 < n)
    {B lam theta ε τ δPre δSample δComp : ℝ}
    (hB : 0 < B) (hlam : 0 < lam) (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent
            fp H U Vhat τ))
    (hpreBudget :
      (∑ _ij : Fin m × Fin n,
        2 * (Real.exp (-(lam * B)) *
          Real.exp ((lam ^ 2 * (m : ℝ)⁻¹) / 2))) ≤ δPre)
    (hsampleBudget :
      let L : ℝ := (m : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent
          fp Vhat ε τ) := by
  simpa [signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent,
    signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent]
    using
      signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta
        fp H U Vhat hH hflat hU hm hn hB hlam hs htheta hδSample
        (fun _ => τ) hComp hpreBudget hsampleBudget

/-- Deterministic-radius version of the floating-point uniform-sketch transfer.

If a deterministic budget `τ` dominates the sample-dependent FP perturbation
budget for every joint preprocessing/sampling outcome, then the same joint
probability lower bound holds with radius `ε + τ`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m) (hn : 0 < n)
    {B lam theta ε τ δPre δSample : ℝ}
    (hB : 0 < B) (hlam : 0 < lam) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hτ :
      ∀ x : RademacherTrace m × RowTrace m s,
        let V : Fin m → Fin n → ℝ :=
          preconditionRows
            (matMul m H (diagMatrix (rademacherSignVector x.1))) U
        uniformRowSampleGramFullFpPerturbBudget fp s V x.2 ≤ τ)
    (hpreBudget :
      (∑ _ij : Fin m × Fin n,
        2 * (Real.exp (-(lam * B)) *
          Real.exp ((lam ^ 2 * (m : ℝ)⁻¹) / 2))) ≤ δPre)
    (hsampleBudget :
      let L : ℝ := (m : ℝ) * ((n : ℝ) * B ^ 2)
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent fp H U ε τ) := by
  classical
  let P := signedHadamardUniformRowTraceProbability (m := m) (s := s) hm
  let E : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardUniformRowSampleGramTwoSidedEvent H U ε
  let G : Set (RademacherTrace m × RowTrace m s) :=
    signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent fp H U ε τ
  have hExact :
      1 - (δPre + δSample) ≤ P.eventProb E := by
    simpa [P, E] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta
        H U hH hflat hU hm hn hB hlam hs htheta hδSample
        hpreBudget hsampleBudget
  have hsubset : E ⊆ G := by
    intro x hx
    let V : Fin m → Fin n → ℝ :=
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector x.1))) U
    let τx : ℝ := uniformRowSampleGramFullFpPerturbBudget fp s V x.2
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDot fp s V x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hpert : frobNorm Delta ≤ τx := by
      simpa [Delta, τx] using
        fl_uniformRowSampleGramDot_perturb_bound fp V hm hs hγ x.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hx.1 hx.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hτ_le : τx ≤ τ := by
      simpa [V, τx] using hτ x
    have hscalar : ε + τx ≤ ε + τ := by linarith
    have hRhs :
        finiteLoewnerLe
          (fun j k : Fin n => (ε + τx) * finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) :=
      finiteLoewnerLe_smul_finiteIdMatrix_mono hscalar
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDot fp s V x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact finiteLoewnerLe_trans hUpperAdd hRhs
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDot fp s V x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact finiteLoewnerLe_trans hLowerAdd hRhs
    simpa [G, signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent, V]
      using And.intro hUpper hLower
  exact hExact.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Source-sharp SRHT floating-point transfer with a fixed row-norm-derived
budget.

This theorem does not assume a global perturbation domination hypothesis.  It
uses the same SRHT preprocessing event as the exact source-sharp theorem; on
that event every sampled row has squared norm at most
`S^2 = (sqrt(n / m) + t)^2`, so the local FP perturbation budget is bounded by
`uniformRowSampleGramFullFpConstBudget fp s (m * S^2)`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {t theta ε δPre δSample : ℝ}
    (ht : 0 < t) (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hpreBudget :
      (m : ℝ) * Real.exp (-((m : ℝ) * t ^ 2 / 8)) ≤ δPre)
    (hsampleBudget :
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
    let τ : ℝ :=
      uniformRowSampleGramFullFpConstBudget fp (n := n) s ((m : ℝ) * S ^ 2)
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent
          fp H U ε τ) := by
  classical
  intro S τ
  let Psign := rademacherTraceProbability m
  let Q := uniformRowTraceProbability (m := m) (steps := s) hm
  let M : RademacherTrace m → Fin m → Fin n → ℝ :=
    fun ω =>
      preconditionRows
        (matMul m H (diagMatrix (rademacherSignVector ω))) U
  let Epre : Set (RademacherTrace m) :=
    {ω | ∀ i : Fin m, rowNormSq (M ω) i ≤ S ^ 2}
  let Fsample : RademacherTrace m → Set (RowTrace m s) :=
    fun ω =>
      {samples |
        finiteLoewnerLe
          (fun j k : Fin n =>
            uniformRowSampleGram (M ω) samples j k - finiteIdMatrix j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(uniformRowSampleGram (M ω) samples j k - finiteIdMatrix j k))
          (fun j k : Fin n => ε * finiteIdMatrix j k)}
  have hS_def : S = Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t := rfl
  have hPre : 1 - δPre ≤ Psign.eventProb Epre := by
    have hdelta :=
      rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_sqrt_add_sq_ge_one_sub_m_exp_m_t_sq_div_eight
        H U hm hflat hU t ht
    linarith
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hS_pos : 0 < S := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) :=
      Real.sqrt_nonneg _
    dsimp [S]
    linarith
  let L : ℝ := (m : ℝ) * S ^ 2
  have hLpos : 0 < L := by
    dsimp [L]
    exact mul_pos hmRpos (sq_pos_of_ne_zero (ne_of_gt hS_pos))
  have hSample : ∀ ω, ω ∈ Epre → 1 - δSample ≤ Q.eventProb (Fsample ω) := by
    intro ω hω
    have hMorth : HasOrthonormalColumns (M ω) := by
      simpa [M] using
        signedOrthogonalPreconditionRows_hasOrthonormalColumns
          H (rademacherSignVector ω) U hH
          (rademacherSignVector_sq ω) hU
    have hrowBound :
        ∀ i : RowSample m, (m : ℝ) * rowNormSq (M ω) i ≤ L := by
      intro i
      have hm_nonneg : 0 ≤ (m : ℝ) := le_of_lt hmRpos
      calc
        (m : ℝ) * rowNormSq (M ω) i
            ≤ (m : ℝ) * S ^ 2 :=
              mul_le_mul_of_nonneg_left (hω i) hm_nonneg
        _ = L := by simp [L]
    have hY :
        ∀ i : RowSample m,
          finiteLoewnerLe
            (fun j k : Fin n => uniformRowOuterGramSample (M ω) i j k)
            (fun j k : Fin n => L * finiteIdMatrix j k) := by
      intro i
      have hbase :=
        uniformRowOuterGramSample_finiteLoewnerLe_of_rowNormSq_le
          (M ω) i (hω i)
      simpa [L] using hbase
    have hbudget' :
        let betaUpper : ℝ :=
          (Real.exp (theta * L) - theta * L - 1) / L ^ 2
        let betaLower : ℝ := Real.exp theta - theta - 1
        let tailUpper : ℝ :=
          Real.exp (-(theta * (s : ℝ) * ε)) *
            ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
        let tailLower : ℝ :=
          Real.exp (-(theta * (s : ℝ) * ε)) *
            ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
        tailUpper + tailLower ≤ δSample := by
      simpa [S, L] using hsampleBudget
    simpa [Q, Fsample] using
      uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget
        (s := s) (theta := theta) (ε := ε) (δ := δSample) (L := L)
        (M ω) hMorth hm hs htheta hLpos hrowBound hY hbudget'
  have hprod :
      1 - (δPre + δSample) ≤
        (Psign.prod Q).eventProb
          {x : RademacherTrace m × RowTrace m s |
            x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} :=
    FiniteProbability.prod_eventProb_inter_dependent_ge_one_sub_add
      Psign Q Epre Fsample δPre δSample hδSample hPre hSample
  have hsubset :
      {x : RademacherTrace m × RowTrace m s |
        x.1 ∈ Epre ∧ x.2 ∈ Fsample x.1} ⊆
      signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent
        fp H U ε τ := by
    intro x hx
    let V : Fin m → Fin n → ℝ := M x.1
    let τx : ℝ := uniformRowSampleGramFullFpPerturbBudget fp s V x.2
    let Exact : Fin n → Fin n → ℝ :=
      fun j k => uniformRowSampleGram V x.2 j k - finiteIdMatrix j k
    let Delta : Fin n → Fin n → ℝ :=
      fun j k =>
        fl_uniformRowSampleGramDot fp s V x.2 j k -
          uniformRowSampleGram V x.2 j k
    have hxsample :
        finiteLoewnerLe
          (fun j k : Fin n =>
            uniformRowSampleGram V x.2 j k - finiteIdMatrix j k)
          (fun j k : Fin n => ε * finiteIdMatrix j k) ∧
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(uniformRowSampleGram V x.2 j k - finiteIdMatrix j k))
          (fun j k : Fin n => ε * finiteIdMatrix j k) := by
      simpa [Fsample, V] using hx.2
    have hpert : frobNorm Delta ≤ τx := by
      simpa [Delta, τx, V] using
        fl_uniformRowSampleGramDot_perturb_bound fp V hm hs hγ x.2
    have htwosided :=
      finiteLoewnerLe_two_sided_add_of_frobNorm_le
        Exact Delta hxsample.1 hxsample.2 hpert
    rcases htwosided with ⟨hUpperAdd, hLowerAdd⟩
    have hrow_samples : ∀ r : Fin s, rowNormSq V (x.2 r) ≤ S ^ 2 := by
      intro r
      simpa [V] using hx.1 (x.2 r)
    have hτ_le : τx ≤ τ := by
      have hR_nonneg : 0 ≤ S ^ 2 := sq_nonneg S
      simpa [τ, τx, V] using
        uniformRowSampleGramFullFpPerturbBudget_le_const_of_sample_rowNormSq_le
          fp V x.2 hm hs hγ hR_nonneg hrow_samples
    have hscalar : ε + τx ≤ ε + τ := by linarith
    have hRhs :
        finiteLoewnerLe
          (fun j k : Fin n => (ε + τx) * finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) :=
      finiteLoewnerLe_smul_finiteIdMatrix_mono hscalar
    have hUpperEq :
        (fun j k : Fin n =>
          fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k) =
        (fun j k : Fin n => Exact j k + Delta j k) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hLowerEq :
        (fun j k : Fin n =>
          -(fl_uniformRowSampleGramDot fp s V x.2 j k -
            finiteIdMatrix j k)) =
        (fun j k : Fin n => -(Exact j k + Delta j k)) := by
      funext j k
      dsimp [Exact, Delta]
      ring
    have hUpper :
        finiteLoewnerLe
          (fun j k : Fin n =>
            fl_uniformRowSampleGramDot fp s V x.2 j k - finiteIdMatrix j k)
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hUpperEq]
      exact finiteLoewnerLe_trans hUpperAdd hRhs
    have hLower :
        finiteLoewnerLe
          (fun j k : Fin n =>
            -(fl_uniformRowSampleGramDot fp s V x.2 j k -
              finiteIdMatrix j k))
          (fun j k : Fin n => (ε + τ) * finiteIdMatrix j k) := by
      rw [hLowerEq]
      exact finiteLoewnerLe_trans hLowerAdd hRhs
    simpa [signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent, V]
      using And.intro hUpper hLower
  exact hprod.trans (by
    simpa [signedHadamardUniformRowTraceProbability, Psign, Q] using
      FiniteProbability.eventProb_mono (Psign.prod Q) hsubset)

/-- Source-sharp SRHT wrapper for an implemented preprocessed basis `Vhat`.
The SRHT concentration is still proved for the exact `H D_ω U`; the additional
`δComp` event is the explicit place where floating-point construction of
`Vhat` is charged. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {t theta ε δPre δSample δComp : ℝ}
    (ht : 0 < t) (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
            fp H U Vhat τ))
    (hpreBudget :
      (m : ℝ) * Real.exp (-((m : ℝ) * t ^ 2 / 8)) ≤ δPre)
    (hsampleBudget :
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp Vhat ε τ) := by
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
    simpa using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht
        H U hH hflat hU hm ht hs htheta hδSample
        hpreBudget hsampleBudget
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U Vhat hm τ hExact hComp
  simpa [add_assoc] using h

/-- Constant-radius source-sharp SRHT wrapper for an implemented preprocessed
basis `Vhat`. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {t theta ε τ δPre δSample δComp : ℝ}
    (ht : 0 < t) (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent
            fp H U Vhat τ))
    (hpreBudget :
      (m : ℝ) * Real.exp (-((m : ℝ) * t ^ 2 / 8)) ≤ δPre)
    (hsampleBudget :
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent
          fp Vhat ε τ) := by
  simpa [signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent,
    signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent]
    using
      signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht
        fp H U Vhat hH hflat hU hm ht hs htheta hδSample
        (fun _ => τ) hComp hpreBudget hsampleBudget

/-- Logarithmic-preprocessing wrapper for the source-sharp SRHT floating-point
constant-budget theorem. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ)) (hγ : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
    let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
    let τ : ℝ :=
      uniformRowSampleGramFullFpConstBudget fp (n := n) s ((m : ℝ) * S ^ 2)
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardFlUniformRowSampleGramTwoSidedConstBudgetEvent
          fp H U ε τ) := by
  intro t S τ
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht : 0 < t := by
    simpa [t] using
      real_sqrt_eight_log_div_pos_of_pos_lt
        (B := (m : ℝ)) (δ := δPre) hmR hδPre_pos hδPre_lt
  have hpreBudget :
      (m : ℝ) * Real.exp (-((m : ℝ) * t ^ 2 / 8)) ≤ δPre := by
    have heq :=
      real_mul_exp_neg_mul_sqrt_eight_log_div_sq_div_eight_eq
        (B := (m : ℝ)) (δ := δPre) hmR hδPre_pos hδPre_lt
    exact le_of_eq (by simpa [t] using heq)
  simpa [t, S, τ] using
    signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht
      fp H U hH hflat hU hm ht hs hγ htheta hδSample
      hpreBudget hsampleBudget

/-- Logarithmic-preprocessing source-sharp SRHT wrapper for an implemented
preprocessed basis `Vhat`, with all construction errors charged in the
computed-preprocessing perturbation event. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε τ δPre δSample δComp : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hComp :
      1 - δComp ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent
            fp H U Vhat τ))
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample + δComp) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent
          fp Vhat ε τ) := by
  let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht : 0 < t := by
    simpa [t] using
      real_sqrt_eight_log_div_pos_of_pos_lt
        (B := (m : ℝ)) (δ := δPre) hmR hδPre_pos hδPre_lt
  have hpreBudget :
      (m : ℝ) * Real.exp (-((m : ℝ) * t ^ 2 / 8)) ≤ δPre := by
    have heq :=
      real_mul_exp_neg_mul_sqrt_eight_log_div_sq_div_eight_eq
        (B := (m : ℝ)) (δ := δPre) hmR hδPre_pos hδPre_lt
    exact le_of_eq (by simpa [t] using heq)
  simpa [t,
    signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedConstBudgetEvent,
    signedHadamardComputedPreconditionedFlUniformRowPerturbConstBudgetEvent] using
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht
      fp H U Vhat hH hflat hU hm ht hs htheta hδSample
      hComp hpreBudget hsampleBudget

/-- Logarithmic-preprocessing source-sharp SRHT wrapper for a concrete
computed preprocessed basis whose perturbation event has already been proved
with probability one.

This is an intermediate adapter: unlike the constant-budget theorem above, the
radius is the supplied sample-dependent concrete perturbation budget `τ`.  It
removes the artificial `δComp` loss when a later theorem instantiates the
probability-one perturbation certificate for an actual computed SRHT path. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess_of_perturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hCompEq :
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
          fp H U Vhat τ) = 1)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp Vhat ε τ) := by
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
    simpa using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
        hsampleBudget
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
            fp H U Vhat τ) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U Vhat hm τ hExact hComp
  simpa using h

/-- Logarithmic-preprocessing source-sharp SRHT wrapper for a concrete
computed preprocessed basis with a computed uniform row-scale denominator,
assuming the concrete computed-denominator perturbation event has already been
proved with probability one. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess_of_perturbEvent_eq_one
    (fp : FPModel) {m n s : ℕ}
    (H : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (Vhat : RademacherTrace m → Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hH : IsOrthogonal m H) (hflat : HadamardFlat m H)
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (τ : RademacherTrace m × RowTrace m s → ℝ)
    (hCompEq :
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H U Vhat dhat τ) = 1)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let S : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * S ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp Vhat dhat ε τ) := by
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowSampleGramTwoSidedEvent H U ε) := by
    simpa using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
        hsampleBudget
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H U Vhat dhat τ) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U Vhat dhat hm τ hExact hComp
  simpa using h

/-- Final nonconditional exact-denominator SRHT endpoint for the modeled
materialized scaled-pattern path with rounded `fl_mul sign_i 1` sign storage.

The random signs and uniform row trace are exact laws.  The computed
non-probability objects are the rounded scale/sign-pattern preconditioner,
the rounded stored signs, the rounded formation of `H D_ω`, the rounded
matrix product forming `Vhat`, the rounded uniform row divisions by the exact
mathematical denominator `sqrt(s/m)`, and the rounded Gram dot products.  All
of these errors are charged by the concrete budget
`signedHadamardComputedLeftUniformRowPerturbBudget`; no perturbation event or
`δComp` hypothesis appears in the theorem statement. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH :
      IsOrthogonal m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hflat :
      HadamardFlat m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let H : Fin m → Fin m → ℝ :=
      fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramTwoSidedEvent
          fp
          (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
          ε
          (signedHadamardComputedLeftUniformRowPerturbBudget fp H U Pihat)) := by
  intro H Pihat
  have hCompEq :
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbEvent
          fp H U
          (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
          (signedHadamardComputedLeftUniformRowPerturbBudget fp H U Pihat)) = 1 := by
    simpa [H, Pihat] using
      signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowPerturbEvent_eq_one
        fp S U hm hs hγm hγs
  simpa [H, Pihat] using
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess_of_perturbEvent_eq_one
      fp H U
      (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
      hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
      (signedHadamardComputedLeftUniformRowPerturbBudget fp H U Pihat)
      hCompEq hsampleBudget

/-- Final nonconditional computed-denominator SRHT endpoint for the modeled
materialized scaled-pattern path with rounded `fl_mul sign_i 1` sign storage.

The random signs and uniform row trace are exact laws.  The computed
non-probability objects are the rounded scale/sign-pattern preconditioner,
rounded stored signs, rounded formation of `H D_ω`, rounded matrix product
forming `Vhat`, the computed nonzero denominator `dhat`, rounded row divisions
by `dhat.den`, and rounded Gram dot products.  All of these errors are charged
by the concrete budget
`signedHadamardComputedLeftUniformRowComputedDenPerturbBudget`; no
perturbation-event or `δComp` hypothesis appears in the theorem statement. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hH :
      IsOrthogonal m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hflat :
      HadamardFlat m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let H : Fin m → Fin m → ℝ :=
      fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H U Pihat dhat)) := by
  intro H Pihat
  have hCompEq :
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H U
          (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H U Pihat dhat)) = 1 := by
    simpa [H, Pihat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H U Pihat dhat hm hs hγm hγs
  simpa [H, Pihat] using
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess_of_perturbEvent_eq_one
      fp H U
      (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
      dhat hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H U Pihat dhat)
      hCompEq hsampleBudget

/-- Final concrete-denominator SRHT endpoint for the modeled materialized
scaled-pattern path with rounded `fl_mul sign_i 1` sign storage.

This specializes the computed-denominator endpoint to the actual scalar
routine `fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt m))` for the uniform row-scale
denominator.  Thus the denominator formation, row divisions, and Gram dot
products are all charged by locally proved floating-point bounds, with no
remaining denominator-certificate parameter in the final theorem surface. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {m n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin n → ℝ)
    (hH :
      IsOrthogonal m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hflat :
      HadamardFlat m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((n : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((n : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let H : Fin m → Fin m → ℝ :=
      fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm
    let dhat : ComputedUniformRowScaleDen fp m s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp
          (signedHadamardComputedLeftPreconditionedBasis fp H U Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H U Pihat dhat)) := by
  intro H Pihat dhat
  simpa [H, Pihat, dhat] using
    signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
      fp S U
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs)
      hH hflat hU hm hδPre_pos hδPre_lt hs hγm hγs htheta hδSample
      hsampleBudget

/-- Final nonconditional computed-denominator SRHT endpoint for the modeled
materialized scaled-pattern path on the actual Algorithm 3 input matrix
`A = U C`.

The exact factors `U` and `C` are analysis-only objects used to state the
source-sharp SRHT row-norm theorem; the algorithm computes with the input
matrix `A = U C` through the rounded product `fl(Pihat * A)`.  The random signs
and uniform row trace are exact laws.  The computed non-probability objects are
the rounded scale/sign-pattern preconditioner, rounded stored signs, rounded
formation of `H D_ω`, rounded matrix product forming `Yhat = fl(Pihat * A)`,
the computed nonzero denominator `dhat`, rounded row divisions by `dhat.den`,
and rounded Gram dot products.  All errors are charged by the concrete budget
`signedHadamardComputedLeftUniformRowComputedDenPerturbBudget`; no perturbation
event or `δComp` hypothesis appears in the theorem statement. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {m r n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (dhat : ComputedUniformRowScaleDen fp m s)
    (hH :
      IsOrthogonal m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hflat :
      HadamardFlat m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let H : Fin m → Fin m → ℝ :=
      fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro H A Pihat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C hH hflat hU hm hδPre_pos hδPre_lt hs htheta hδSample
        hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat] using h

/-- Final concrete-denominator SRHT endpoint for the modeled materialized
scaled-pattern path on the actual Algorithm 3 input matrix `A = U C`.

This is the implementation-facing version of the factored-input theorem for
the closed denominator routine
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt m))`.  The exact factors `U` and `C`
are analysis-only witnesses for the source-sharp SRHT row-norm theorem, while
the algorithm computes with `A = U C`.  The theorem charges rounded
preconditioner formation, rounded formation of `Yhat = fl(Pihat * A)`, the
concrete computed denominator, rounded row divisions, and rounded Gram dot
products. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {m r n s : ℕ}
    (S : Fin m → Fin m → ℝ) (U : Fin m → Fin r → ℝ)
    (C : Fin r → Fin n → ℝ)
    (hH :
      IsOrthogonal m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hflat :
      HadamardFlat m
        (fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k))
    (hU : HasOrthonormalColumns U) (hm : 0 < m)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre) (hδPre_lt : δPre < (m : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp m) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ := Real.sqrt (8 * Real.log ((m : ℝ) / δPre) / (m : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (m : ℝ)⁻¹) + t
      let L : ℝ := (m : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let H : Fin m → Fin m → ℝ :=
      fun i k => Real.sqrt ((m : ℝ)⁻¹) * S i k
    let A : Fin m → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace m,
        ComputedPreconditioner fp
          (matMul m H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardScaledPatternStoredSignPreconditioner fp S ω hγm
    let dhat : ComputedUniformRowScaleDen fp m s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability (m := m) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro H A Pihat dhat
  simpa [H, A, Pihat, dhat] using
    signedHadamardUniformRowTraceProbability_eventProb_scaledPatternStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
      fp S U C
      (uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs)
      hH hflat hU hm hδPre_pos hδPre_lt hs hγm hγs htheta hδSample
      hsampleBudget

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path on the actual Algorithm 3 input matrix `A = U C`.

The exact factors `U` and `C` are analysis-only witnesses for the source-sharp
SRHT row-norm theorem; the algorithm computes with `A = U C`.  The
Sylvester/Walsh table is generated exactly by bit parity, its normalized
orthogonality and flatness are proved locally, and the computed
non-probability path charges rounded Rademacher-sign storage, generated FHT
butterfly arithmetic, rounded normalization, rounded formation of
`Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
        fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path when the actual Algorithm 3 input matrix `A = U C` is first
stored by rounded multiply-one copies before the preconditioned product is
formed.

Compared with
`signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`,
this theorem charges the additional computed non-probability path
`Ahat_ij = fl_mul A_ij 1` and then forms
`Yhat = fl(Pihat * Ahat)`.  The exact factors `U` and `C` remain
analysis-only witnesses for the input identity `A=UC`; the implemented path
uses the stored matrix certificate `ComputedMatrix.flMulOne fp A`.  The
Rademacher and uniform-row laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredInputMulOneComputedLeftInputPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Ahat : ComputedMatrix fp A := ComputedMatrix.flMulOne fp A
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
        fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          ε
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) := by
  intro hm H A Ahat Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) = 1 := by
    simpa [H, A, Ahat, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H Ahat Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
            dhat
            (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
              fp H Ahat Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
      dhat hm
      (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
        fp H Ahat Pihat dhat)
      hExact hComp
  simpa [H, A, Ahat, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path when the actual Algorithm 3 input matrix `A = U C` is first
stored by rounded add-zero copies before the preconditioned product is formed.

This is the add-zero stored-input sibling of the multiply-one theorem above:
it charges `Ahat_ij = fl_add A_ij 0` before forming
`Yhat = fl(Pihat * Ahat)`.  The exact factors `U` and `C` remain
analysis-only witnesses for the input identity `A=UC`, while the implemented
path uses the stored matrix certificate `ComputedMatrix.flAddZeroRight fp A`.
The Rademacher and uniform-row laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredInputAddZeroRightComputedLeftInputPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Ahat : ComputedMatrix fp A := ComputedMatrix.flAddZeroRight fp A
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
        fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          ε
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) := by
  intro hm H A Ahat Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) = 1 := by
    simpa [H, A, Ahat, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H Ahat Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
            dhat
            (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
              fp H Ahat Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
      dhat hm
      (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
        fp H Ahat Pihat dhat)
      hExact hComp
  simpa [H, A, Ahat, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path when the actual Algorithm 3 input matrix `A = U C` is first
stored by rounded subtract-zero copies before the preconditioned product is
formed.

This is the subtract-zero stored-input sibling of the multiply-one theorem
above: it charges `Ahat_ij = fl_sub A_ij 0` before forming
`Yhat = fl(Pihat * Ahat)`.  The exact factors `U` and `C` remain
analysis-only witnesses for the input identity `A=UC`, while the implemented
path uses the stored matrix certificate `ComputedMatrix.flSubZeroRight fp A`.
The Rademacher and uniform-row laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredInputSubZeroRightComputedLeftInputPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Ahat : ComputedMatrix fp A := ComputedMatrix.flSubZeroRight fp A
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω => signedHadamardSylvesterFhtScheduleStoredSignPreconditioner
        fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          ε
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) := by
  intro hm H A Ahat Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
          dhat
          (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
            fp H Ahat Pihat dhat)) = 1 := by
    simpa [H, A, Ahat, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftInputPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H Ahat Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
            dhat
            (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
              fp H Ahat Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftInputPreconditionedBasis fp H Ahat Pihat)
      dhat hm
      (signedHadamardComputedLeftInputUniformRowComputedDenPerturbBudget
        fp H Ahat Pihat dhat)
      hExact hComp
  simpa [H, A, Ahat, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with explicit rounded add-zero writeback/copy after every FHT
pair update, on the actual Algorithm 3 input matrix `A = U C`.

This is the add-zero writeback specialization of the generated-FHT endpoint
above.  The exact factors `U` and `C` are analysis-only witnesses; the
algorithm computes with `A = U C`.  The Sylvester/Walsh table is generated
exactly by bit parity, its normalized orthogonality and flatness are proved
locally, and the computed non-probability path charges rounded
Rademacher-sign storage, generated FHT butterfly arithmetic, rounded
`fl_add y_i 0` writeback/copy after every pair update, rounded normalization,
rounded formation of `Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredAddZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredAddZeroRightPreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with modified-coordinate rounded add-zero writeback/copy, on
the actual Algorithm 3 input matrix `A = U C`.

This variant charges `fl_add y_i 0` only on the two coordinates modified by
each FHT pair update; untouched coordinates are propagated without a writeback
term.  The exact factors `U` and `C` are analysis-only witnesses; the algorithm
computes with `A = U C`.  The Sylvester/Walsh table is generated exactly by bit
parity, its normalized orthogonality and flatness are proved locally, and the
computed non-probability path charges rounded Rademacher-sign storage,
generated FHT butterfly arithmetic, the modified-coordinate writeback/copy
terms, rounded normalization, rounded formation of `Yhat = fl(Pihat * A)`,
the concrete computed denominator `fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt
(2^p)))`, rounded sampled-row divisions, and rounded Gram dot products.  The
Rademacher and uniform-row laws remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredAddZeroRightPreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with explicit rounded multiply-one writeback/copy after every
FHT pair update, on the actual Algorithm 3 input matrix `A = U C`.

This is the multiply-one writeback specialization of the generated-FHT
endpoint.  The exact factors `U` and `C` are analysis-only witnesses; the
algorithm computes with `A = U C`.  The Sylvester/Walsh table is generated
exactly by bit parity, its normalized orthogonality and flatness are proved
locally, and the computed non-probability path charges rounded
Rademacher-sign storage, generated FHT butterfly arithmetic, rounded
`fl_mul y_i 1` writeback/copy after every pair update, rounded normalization,
rounded formation of `Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredMulOneComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredMulOnePreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with explicit rounded subtract-zero writeback/copy after every
FHT pair update, on the actual Algorithm 3 input matrix `A = U C`.

This is the subtract-zero writeback specialization of the generated-FHT
endpoint.  The exact factors `U` and `C` are analysis-only witnesses; the
algorithm computes with `A = U C`.  The Sylvester/Walsh table is generated
exactly by bit parity, its normalized orthogonality and flatness are proved
locally, and the computed non-probability path charges rounded
Rademacher-sign storage, generated FHT butterfly arithmetic, rounded
`fl_sub y_i 0` writeback/copy after every pair update, rounded normalization,
rounded formation of `Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignStoredSubZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignStoredSubZeroRightPreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with modified-coordinate rounded multiply-one writeback/copy,
on the actual Algorithm 3 input matrix `A = U C`.

This variant charges `fl_mul y_i 1` only on the two coordinates modified by
each FHT pair update; untouched coordinates are propagated without a writeback
term.  The exact factors `U` and `C` are analysis-only witnesses; the algorithm
computes with `A = U C`.  The Sylvester/Walsh table is generated exactly by
bit parity, its normalized orthogonality and flatness are proved locally, and
the computed non-probability path charges rounded Rademacher-sign storage,
generated FHT butterfly arithmetic, the modified-coordinate multiply-one
writeback/copy terms, rounded normalization, rounded formation of
`Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredMulOneComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredMulOnePreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

/-- Final concrete-denominator SRHT endpoint for the fast generated-FHT
stored-sign path with modified-coordinate rounded subtract-zero writeback/copy,
on the actual Algorithm 3 input matrix `A = U C`.

This variant charges `fl_sub y_i 0` only on the two coordinates modified by
each FHT pair update; untouched coordinates are propagated without a writeback
term.  The exact factors `U` and `C` are analysis-only witnesses; the algorithm
computes with `A = U C`.  The Sylvester/Walsh table is generated exactly by
bit parity, its normalized orthogonality and flatness are proved locally, and
the computed non-probability path charges rounded Rademacher-sign storage,
generated FHT butterfly arithmetic, the modified-coordinate subtract-zero
writeback/copy terms, rounded normalization, rounded formation of
`Yhat = fl(Pihat * A)`, the concrete computed denominator
`fl_mul (fl_sqrt s) (fl_div 1 (fl_sqrt (2^p)))`, rounded sampled-row
divisions, and rounded Gram dot products.  The Rademacher and uniform-row laws
remain exact. -/
theorem signedHadamardUniformRowTraceProbability_eventProb_sylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightComputedLeftPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithFlSqrtMulInvSqrtDen_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
    (fp : FPModel) {p r n s : ℕ}
    (U : Fin (2 ^ p) → Fin r → ℝ) (C : Fin r → Fin n → ℝ)
    (hU : HasOrthonormalColumns U)
    {theta ε δPre δSample : ℝ}
    (hδPre_pos : 0 < δPre)
    (hδPre_lt : δPre < ((2 ^ p : ℕ) : ℝ))
    (hs : 0 < (s : ℝ))
    (hγm : gammaValid fp (2 ^ p)) (hγs : gammaValid fp s)
    (htheta : 0 < theta) (hδSample : 0 ≤ δSample)
    (hsampleBudget :
      let t : ℝ :=
        Real.sqrt (8 * Real.log (((2 ^ p : ℕ) : ℝ) / δPre) /
          ((2 ^ p : ℕ) : ℝ))
      let Sradius : ℝ := Real.sqrt ((r : ℝ) * (((2 ^ p : ℕ) : ℝ))⁻¹) + t
      let L : ℝ := ((2 ^ p : ℕ) : ℝ) * Sradius ^ 2
      let betaUpper : ℝ :=
        (Real.exp (theta * L) - theta * L - 1) / L ^ 2
      let betaLower : ℝ := Real.exp theta - theta - 1
      let tailUpper : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaUpper * (L ^ 2 + 1))))
      let tailLower : ℝ :=
        Real.exp (-(theta * (s : ℝ) * ε)) *
          ((r : ℝ) * Real.exp ((s : ℝ) * (betaLower * (L ^ 2 + 1))))
      tailUpper + tailLower ≤ δSample) :
    let hm : 0 < 2 ^ p := pow_pos (by norm_num : (0 : ℕ) < 2) p
    let H : Fin (2 ^ p) → Fin (2 ^ p) → ℝ :=
      fun i k => Real.sqrt (((2 ^ p : ℕ) : ℝ)⁻¹) *
        sylvesterHadamardSignPattern p i k
    let A : Fin (2 ^ p) → Fin n → ℝ := preconditionColumns U C
    let Pihat :
      ∀ ω : RademacherTrace (2 ^ p),
        ComputedPreconditioner fp
          (matMul (2 ^ p) H (diagMatrix (rademacherSignVector ω))) :=
      fun ω =>
        signedHadamardSylvesterFhtScheduleStoredSignModifiedStoredSubZeroRightPreconditioner
          fp ω
    let dhat : ComputedUniformRowScaleDen fp (2 ^ p) s :=
      uniformRowFlSqrtMulInvSqrtScaleDen fp hm hs hγs
    1 - (δPre + δSample) ≤
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFactoredInputFlUniformRowSampleGramWithComputedDenTwoSidedEvent
          fp U C
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          ε
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) := by
  intro hm H A Pihat dhat
  have hExact :
      1 - (δPre + δSample) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardUniformRowFactoredInputSampleGramTwoSidedEvent
            H U C ε) := by
    simpa [H] using
      signedHadamardUniformRowTraceProbability_eventProb_uniformRowFactoredInputSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess
        H U C
        (isOrthogonal_sqrt_inv_nat_mul_sylvesterSignPattern p)
        (hadamardFlat_sqrt_inv_nat_mul_sylvesterSignPattern p)
        hU hm hδPre_pos hδPre_lt hs htheta hδSample hsampleBudget
  have hCompEq :
      (signedHadamardUniformRowTraceProbability
        (m := 2 ^ p) (s := s) hm).eventProb
        (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
          fp H A
          (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
          dhat
          (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
            fp H A Pihat dhat)) = 1 := by
    simpa [H, A, Pihat, dhat] using
      signedHadamardUniformRowTraceProbability_eventProb_computedLeftPreconditioned_fl_uniformRowComputedDenPerturbEvent_eq_one
        fp H A Pihat dhat hm hs hγm hγs
  have hComp :
      1 - (0 : ℝ) ≤
        (signedHadamardUniformRowTraceProbability
          (m := 2 ^ p) (s := s) hm).eventProb
          (signedHadamardComputedPreconditionedFlUniformRowPerturbWithComputedDenEvent
            fp H A
            (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
            dhat
            (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
              fp H A Pihat dhat)) := by
    rw [hCompEq]
    norm_num
  have h :=
    signedHadamardUniformRowTraceProbability_eventProb_computedPreconditioned_factoredInput_fl_uniformRowSampleGramDotWithComputedDen_two_sided_finiteLoewnerLe_ge_one_sub_of_exact_event
      fp H U C
      (signedHadamardComputedLeftPreconditionedBasis fp H A Pihat)
      dhat hm
      (signedHadamardComputedLeftUniformRowComputedDenPerturbBudget
        fp H A Pihat dhat)
      hExact hComp
  simpa [H, A, Pihat, dhat] using h

end NumStability
