-- Algorithms/QR/HouseholderReflector.lean
--
-- Low-level floating-point kernels for constructing a Householder reflector.
--
-- This file is intentionally below the QR-factorization layer.  It defines the
-- rounded operations used to form the scalar alpha, vector v, and scalar beta
-- for P = I - beta * v * v^T.  It proves the concrete construction satisfies
-- Higham Lemma 18.1; Lemma 18.2 application stability is handled separately.

import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp
import NumStability.Algorithms.Norm2
import NumStability.Algorithms.QR.HouseholderSpec

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §18.1  Householder construction primitives
-- ============================================================

/-- Householder sign convention.

    We choose `1` at zero, as is customary in the stable Householder vector
    construction `alpha = -sign(x_0) * ||x||_2`.  This differs from
    `SignType.sign` only at zero. -/
noncomputable def householderSign (x : ℝ) : ℝ :=
  if x < 0 then -1 else 1

@[simp] theorem householderSign_zero : householderSign 0 = 1 := by
  simp [householderSign]

@[simp] theorem abs_householderSign (x : ℝ) : |householderSign x| = 1 := by
  unfold householderSign
  by_cases hx : x < 0 <;> simp [hx]

/-- Away from zero, `householderSign` agrees with Mathlib's `SignType.sign`
    coerced to `ℝ`. -/
theorem householderSign_eq_sign_of_ne {x : ℝ} (hx : x ≠ 0) :
    householderSign x = (SignType.sign x : ℝ) := by
  by_cases hneg : x < 0
  · simp [householderSign, hneg, sign_neg hneg]
  · have hpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hx)
    simp [householderSign, hneg, sign_pos hpos]

/-- Exact `s = sign(x_0) * ||x||_2` used in Higham Lemma 18.1.

    This is exact algebra, not a floating-point operation.  The rounded
    counterpart is `fl_householderScale`. -/
noncomputable def householderScale {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  householderSign (x ⟨0, hn⟩) *
    Real.sqrt (∑ i : Fin n, x i * x i)

/-- Exact `alpha = -sign(x_0) * ||x||_2`.

    This is a compatibility alias for the opposite of Higham's scale `s`. -/
noncomputable def householderAlpha {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  -householderScale hn x

/-- Exact Householder vector before normalization.

    The first component is `x_0 + s`; all tail components are copied from
    `x`.  The rounded counterpart is `fl_householderVector`. -/
noncomputable def householderVector {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if i = ⟨0, hn⟩ then
      x i + householderScale hn x
    else
      x i

/-- Exact `beta = 2 / (vᵀv)` for the unnormalized Householder vector. -/
noncomputable def householderBeta {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  let v := householderVector hn x
  2 / (∑ i : Fin n, v i * v i)

/-- Exact beta in the operation order used by Higham Lemma 18.1:
    `beta = 1 / (s * v_0)`.

    This is the exact target for the rounded beta kernel below.  It is
    mathematically equivalent to `2/(vᵀv)` for the exact Householder vector;
    the equivalence proof is a later exact-algebra bridge needed before full
    QR can consume the source-aligned construction result. -/
noncomputable def householderBetaFromScale {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  1 / (householderScale hn x * householderVector hn x ⟨0, hn⟩)

/-- The exact Householder scale satisfies `s^2 = x^T x`. -/
theorem householderScale_mul_self {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    householderScale hn x * householderScale hn x =
      ∑ i : Fin n, x i * x i := by
  unfold householderScale
  have hsign_sq :
      householderSign (x ⟨0, hn⟩) * householderSign (x ⟨0, hn⟩) = 1 := by
    unfold householderSign
    by_cases h : x ⟨0, hn⟩ < 0 <;> simp [h]
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, x i * x i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  calc
    (householderSign (x ⟨0, hn⟩) *
        Real.sqrt (∑ i : Fin n, x i * x i)) *
        (householderSign (x ⟨0, hn⟩) *
          Real.sqrt (∑ i : Fin n, x i * x i))
        =
          (householderSign (x ⟨0, hn⟩) *
            householderSign (x ⟨0, hn⟩)) *
            (Real.sqrt (∑ i : Fin n, x i * x i) *
              Real.sqrt (∑ i : Fin n, x i * x i)) := by ring
    _ = 1 * (∑ i : Fin n, x i * x i) := by
          rw [hsign_sq, Real.mul_self_sqrt hsum_nonneg]
    _ = ∑ i : Fin n, x i * x i := by ring

@[simp] theorem householderVector_zero {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    householderVector hn x ⟨0, hn⟩ =
      x ⟨0, hn⟩ + householderScale hn x := by
  simp [householderVector]

/-- The Householder sign choice prevents cancellation in the first component:
    `x_0` and `s` have the same sign, so `|x_0+s| = |x_0| + |s|`.

    This is the exact algebra fact used in Higham Lemma 18.1 before bounding
    the rounded first component. -/
theorem householderVector_zero_abs_eq {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    |householderVector hn x ⟨0, hn⟩| =
      |x ⟨0, hn⟩| + |householderScale hn x| := by
  rw [householderVector_zero]
  unfold householderScale householderSign
  by_cases hneg : x ⟨0, hn⟩ < 0
  · simp [hneg]
    rw [abs_of_neg hneg]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (∑ i : Fin n, x i * x i) :=
      Real.sqrt_nonneg _
    have hsum_nonpos :
        x ⟨0, hn⟩ + -Real.sqrt (∑ i : Fin n, x i * x i) ≤ 0 := by
      linarith
    rw [abs_of_nonpos hsum_nonpos]
    rw [abs_of_nonneg hsqrt_nonneg]
    ring
  · have hx_nonneg : 0 ≤ x ⟨0, hn⟩ := le_of_not_gt hneg
    simp [hneg]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (∑ i : Fin n, x i * x i) :=
      Real.sqrt_nonneg _
    have hsum_nonneg :
        0 ≤ x ⟨0, hn⟩ + Real.sqrt (∑ i : Fin n, x i * x i) := by
      linarith
    rw [abs_of_nonneg hsum_nonneg]
    rw [abs_of_nonneg hx_nonneg]
    rw [abs_of_nonneg hsqrt_nonneg]

/-- Tail components of the exact Householder vector are copied exactly. -/
theorem householderVector_tail {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (i : Fin n) (hi : i ≠ ⟨0, hn⟩) :
    householderVector hn x i = x i := by
  simp [householderVector, hi]

/-- Exact identity behind Higham's beta formula:
    `v^T v = 2*s*v_0` for `v = x + s e_0`. -/
theorem householderVector_norm_sq_eq_two_scale_mul {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    (∑ i : Fin n, householderVector hn x i * householderVector hn x i) =
      2 * householderScale hn x * householderVector hn x ⟨0, hn⟩ := by
  let first : Fin n := ⟨0, hn⟩
  let tailSum : ℝ :=
    ∑ i ∈ (Finset.univ : Finset (Fin n)).erase first, x i * x i
  have hmem : first ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ first
  have hsum_v : (∑ i : Fin n,
      householderVector hn x i * householderVector hn x i) =
        householderVector hn x first * householderVector hn x first + tailSum := by
    have hsplit :=
      Finset.sum_erase_add (Finset.univ : Finset (Fin n))
        (fun i => householderVector hn x i * householderVector hn x i)
        hmem
    calc
      (∑ i : Fin n, householderVector hn x i * householderVector hn x i)
          =
            (∑ i ∈ (Finset.univ : Finset (Fin n)).erase first,
              householderVector hn x i * householderVector hn x i) +
              householderVector hn x first * householderVector hn x first := by
                rw [hsplit]
      _ =
            householderVector hn x first * householderVector hn x first +
              tailSum := by
                rw [add_comm]
                congr 1
                unfold tailSum
                apply Finset.sum_congr rfl
                intro i hi
                have hne : i ≠ first := (Finset.mem_erase.mp hi).1
                rw [householderVector_tail hn x i hne]
  have hsum_x : (∑ i : Fin n, x i * x i) =
      x first * x first + tailSum := by
    have hsplit :=
      Finset.sum_erase_add (Finset.univ : Finset (Fin n))
        (fun i => x i * x i) hmem
    calc
      (∑ i : Fin n, x i * x i)
          =
            (∑ i ∈ (Finset.univ : Finset (Fin n)).erase first,
              x i * x i) + x first * x first := by
                rw [hsplit]
      _ = x first * x first + tailSum := by
            rw [add_comm]
  have hscale_sq := householderScale_mul_self hn x
  have hv0 : householderVector hn x first = x first + householderScale hn x := by
    simp [first, householderVector]
  rw [hsum_v, hv0]
  rw [hsum_x] at hscale_sq
  nlinarith

/-- Higham's exact beta formula `1/(s*v_0)` agrees with the reflector formula
    `2/(v^T v)` whenever `s*v_0` is nonzero. -/
theorem householderBetaFromScale_eq_householderBeta {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ)
    (hden : householderScale hn x * householderVector hn x ⟨0, hn⟩ ≠ 0) :
    householderBetaFromScale hn x = householderBeta hn x := by
  have hnorm := householderVector_norm_sq_eq_two_scale_mul hn x
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hden2 : 2 * (householderScale hn x *
      householderVector hn x ⟨0, hn⟩) ≠ 0 := mul_ne_zero htwo hden
  unfold householderBetaFromScale householderBeta
  simp only
  rw [hnorm]
  field_simp [hden, hden2]

/-- Exact `beta = 2/(vᵀv)` satisfies the orthogonality side condition for
    `householder_orthogonal` whenever the denominator is nonzero. -/
theorem householderBeta_mul_norm_sq {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ)
    (hden : (∑ i : Fin n,
      householderVector hn x i * householderVector hn x i) ≠ 0) :
    householderBeta hn x *
      (∑ i : Fin n, householderVector hn x i * householderVector hn x i) =
        2 := by
  unfold householderBeta
  have hden' : (∑ i : Fin n, householderVector hn x i ^ 2) ≠ 0 := by
    simpa [pow_two] using hden
  field_simp [hden, hden']

/-- Exact Householder construction produces an orthogonal reflector when
    `vᵀv` is nonzero. -/
theorem householder_exact_orthogonal {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ)
    (hden : (∑ i : Fin n,
      householderVector hn x i * householderVector hn x i) ≠ 0) :
    IsOrthogonal n
      (householder n (householderVector hn x) (householderBeta hn x)) := by
  exact householder_orthogonal n (householderVector hn x) (householderBeta hn x)
    (householderBeta_mul_norm_sq hn x hden)

/-- **Householder construction error contract** (Higham Lemma 18.1).

    This is the source-level intermediate result for the concrete construction
    below.  It says the computed vector has exact tail components, its first
    component is a relative perturbation of the exact first component with
    `γ_{n+2}`, and the computed beta is a relative perturbation of Higham's
    exact formula `1/(s*v_0)` with `γ_{4n+8}`.

    The contract is intentionally stated before the implementation-backed
    proof below.  The theorem `fl_householderConstruction_error` proves it from
    `fl_householderScale`, `fl_householderVector`, and
    `fl_householderBeta`; higher QR proofs consume that proved bridge. -/
structure HouseholderConstructionError (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x v_hat : Fin n → ℝ) (beta_hat : ℝ) : Prop where
  /-- Higham Lemma 18.1: `v_hat(2:n) = v(2:n)`. -/
  tail : ∀ i : Fin n, i ≠ ⟨0, hn⟩ →
    v_hat i = householderVector hn x i
  /-- Higham Lemma 18.1: `v_hat_1 = v_1(1 + θ_{n+2})`. -/
  first : ∃ θ : ℝ,
    |θ| ≤ gamma fp (n + 2) ∧
    v_hat ⟨0, hn⟩ = householderVector hn x ⟨0, hn⟩ * (1 + θ)
  /-- Higham Lemma 18.1: `beta_hat = beta(1 + θ_{4n+8})`, using the
      source formula `beta = 1/(s*v_1)`. -/
  beta : ∃ θ : ℝ,
    |θ| ≤ gamma fp (4 * n + 8) ∧
    beta_hat = householderBetaFromScale hn x * (1 + θ)

/-- Rounded scale `s_hat = sign(x_0) * fl_norm2(x)`.

    Higham's operation count treats the sign application as exact.  The only
    rounded arithmetic here is the norm computation; multiplying by `±1` is a
    sign change, not a call to `fp.fl_mul`. -/
noncomputable def fl_householderScale (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  householderSign (x ⟨0, hn⟩) * fl_norm2 fp n x

/-- Compatibility alias `alpha_hat = -s_hat`. -/
noncomputable def fl_householderAlpha (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  -fl_householderScale fp hn x

/-- Rounded Householder vector.

    Only the first component is formed by the rounded addition
    `v_0 = fl_add x_0 s_hat`, matching Higham Lemma 18.1.  All tail components
    are copied exactly. -/
noncomputable def fl_householderVector (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if i = ⟨0, hn⟩ then
      fp.fl_add (x i) (fl_householderScale fp hn x)
    else
      x i

/-- Rounded beta in the Higham Lemma 18.1 operation order:
    `beta_hat = fl_div 1 (fl_mul s_hat v_hat_0)`. -/
noncomputable def fl_householderBeta (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  let s := fl_householderScale fp hn x
  let v := fl_householderVector fp hn x
  fp.fl_div 1 (fp.fl_mul s (v ⟨0, hn⟩))

-- ============================================================
-- Unroll lemmas
-- ============================================================

/-- Unroll `fl_householderScale` through the rounded norm.

    The final `ε = 0` witness keeps the statement compatible with product-form
    gamma algebra while recording that Higham's sign application is exact. -/
theorem fl_householderScale_unroll_of_gammaValid_two_mul (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ)
    (hn : gammaValid fp (2 * n)) :
    ∃ (η : Fin n → ℝ) (δ ε : ℝ),
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      |δ| ≤ fp.u ∧
      |ε| ≤ fp.u ∧
      fl_householderScale fp hn0 x =
        (householderSign (x ⟨0, hn0⟩) *
          (Real.sqrt (∑ i : Fin n, x i * x i * (1 + η i)) * (1 + δ))) *
          (1 + ε) := by
  obtain ⟨η, δ, hη, hδ, hnorm⟩ :=
    fl_norm2_unroll_of_gammaValid_two_mul fp n x hn
  refine ⟨η, δ, 0, hη, hδ, by simp [fp.u_nonneg], ?_⟩
  unfold fl_householderScale
  rw [hnorm]
  ring

/-- Scalar square-root-factor form for the rounded Householder scale.

    This composes the `fl_norm2` scalar bridge with the exact sign change in
    `fl_householderScale`.  It is the source-aligned input for the
    first-component part of Higham Lemma 18.1. -/
theorem fl_householderScale_relative_error_sqrt_factor (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ)
    (hn : gammaValid fp (2 * n)) :
    ∃ (θ δ : ℝ),
      |θ| ≤ gamma fp n ∧
      |δ| ≤ fp.u ∧
      0 ≤ 1 + θ ∧
      fl_householderScale fp hn0 x =
        (householderScale hn0 x * Real.sqrt (1 + θ)) * (1 + δ) := by
  obtain ⟨θ, δ, hθ, hδ, hθ_nonneg, hnorm⟩ :=
    fl_norm2_relative_error_sqrt_factor fp n x hn
  refine ⟨θ, δ, hθ, hδ, hθ_nonneg, ?_⟩
  unfold fl_householderScale householderScale
  rw [hnorm]
  ring

/-- Higham-style relative-error form for the rounded Householder scale:
    `s_hat = s * (1 + theta_{n+1})`.

    This is proved from the concrete `fl_householderScale` implementation and
    the implementation-backed `fl_norm2_relative_error`; the sign multiplication
    is exact because `householderSign` is `±1`. -/
theorem fl_householderScale_relative_error (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ)
    (hn : gammaValid fp (2 * (n + 1))) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp (n + 1) ∧
      fl_householderScale fp hn0 x =
        householderScale hn0 x * (1 + θ) := by
  obtain ⟨θ, hθ, hnorm⟩ := fl_norm2_relative_error fp n x hn
  refine ⟨θ, hθ, ?_⟩
  unfold fl_householderScale householderScale
  rw [hnorm]
  ring

/-- For nonzero `x`, the exact Householder scale `s` is nonzero. -/
theorem householderScale_ne_zero_of_ne_zero {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    householderScale hn x ≠ 0 := by
  have hsum_pos : 0 < ∑ i : Fin n, x i * x i := by
    simpa [dotProduct] using (dotProduct_self_pos_iff_real n x).2 hx
  have hs_abs_pos : 0 < |householderScale hn x| := by
    have hsqrt_pos : 0 < Real.sqrt (∑ i : Fin n, x i * x i) :=
      Real.sqrt_pos.2 hsum_pos
    unfold householderScale
    rw [abs_mul, abs_householderSign]
    rw [abs_of_pos hsqrt_pos]
    linarith
  exact abs_pos.mp hs_abs_pos

/-- For nonzero `x`, the first exact Householder component `x_0+s` is nonzero.

    This is the precise non-cancellation fact used to turn the scale error into
    a relative error in the first component. -/
theorem householderVector_zero_ne_zero_of_ne_zero {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    householderVector hn x ⟨0, hn⟩ ≠ 0 := by
  have hsum_pos : 0 < ∑ i : Fin n, x i * x i := by
    simpa [dotProduct] using (dotProduct_self_pos_iff_real n x).2 hx
  have hscale_abs_pos : 0 < |householderScale hn x| := by
    have hsqrt_pos : 0 < Real.sqrt (∑ i : Fin n, x i * x i) :=
      Real.sqrt_pos.2 hsum_pos
    unfold householderScale
    rw [abs_mul, abs_householderSign]
    rw [abs_of_pos hsqrt_pos]
    linarith
  have hv_abs :
      |householderVector hn x ⟨0, hn⟩| =
        |x ⟨0, hn⟩| + |householderScale hn x| :=
    householderVector_zero_abs_eq hn x
  intro hv_zero
  have hv_abs_zero :
      |householderVector hn x ⟨0, hn⟩| = 0 := by
    simp [hv_zero]
  linarith [abs_nonneg (x ⟨0, hn⟩)]

/-- Higham's beta formula satisfies the reflector normalization condition. -/
theorem householderBetaFromScale_mul_norm_sq {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    householderBetaFromScale hn x *
      (∑ i : Fin n, householderVector hn x i * householderVector hn x i) =
        2 := by
  have hden_scale :
      householderScale hn x * householderVector hn x ⟨0, hn⟩ ≠ 0 :=
    mul_ne_zero
      (householderScale_ne_zero_of_ne_zero hn x hx)
      (householderVector_zero_ne_zero_of_ne_zero hn x hx)
  have hbeta_eq :=
    householderBetaFromScale_eq_householderBeta hn x hden_scale
  have hnorm_ne :
      (∑ i : Fin n, householderVector hn x i * householderVector hn x i) ≠ 0 := by
    rw [householderVector_norm_sq_eq_two_scale_mul hn x]
    simpa [mul_assoc] using
      mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hden_scale
  rw [hbeta_eq]
  exact householderBeta_mul_norm_sq hn x hnorm_ne

/-- Higham's beta formula is positive for nonzero input. -/
theorem householderBetaFromScale_pos_of_ne_zero {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    0 < householderBetaFromScale hn x := by
  have hv_ne : householderVector hn x ≠ 0 := by
    intro hv_zero
    have hv0_ne := householderVector_zero_ne_zero_of_ne_zero hn x hx
    exact hv0_ne (by simpa using congrFun hv_zero ⟨0, hn⟩)
  have hsum_pos :
      0 < ∑ i : Fin n, householderVector hn x i * householderVector hn x i := by
    simpa [dotProduct] using
      (dotProduct_self_pos_iff_real n (householderVector hn x)).2 hv_ne
  have hnorm :=
    householderVector_norm_sq_eq_two_scale_mul hn x
  have hden_pos :
      0 < householderScale hn x * householderVector hn x ⟨0, hn⟩ := by
    nlinarith
  unfold householderBetaFromScale
  exact one_div_pos.mpr hden_pos

/-- Compatibility unroll for `alpha_hat = -s_hat`. -/
theorem fl_householderAlpha_unroll_of_gammaValid_two_mul (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ)
    (hn : gammaValid fp (2 * n)) :
    ∃ (η : Fin n → ℝ) (δ ε : ℝ),
      (∀ i : Fin n, |η i| ≤ gamma fp n) ∧
      |δ| ≤ fp.u ∧
      |ε| ≤ fp.u ∧
      fl_householderAlpha fp hn0 x =
        -((householderSign (x ⟨0, hn0⟩) *
          (Real.sqrt (∑ i : Fin n, x i * x i * (1 + η i)) * (1 + δ))) *
          (1 + ε)) := by
  obtain ⟨η, δ, ε, hη, hδ, hε, hscale⟩ :=
    fl_householderScale_unroll_of_gammaValid_two_mul fp hn0 x hn
  exact ⟨η, δ, ε, hη, hδ, hε, by simp [fl_householderAlpha, hscale]⟩

@[simp] theorem fl_householderVector_zero (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    fl_householderVector fp hn x ⟨0, hn⟩ =
      fp.fl_add (x ⟨0, hn⟩) (fl_householderScale fp hn x) := by
  simp [fl_householderVector]

/-- Tail components of the rounded Householder vector are copied exactly. -/
theorem fl_householderVector_tail (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n)
    (hi : i ≠ ⟨0, hn⟩) :
    fl_householderVector fp hn x i = x i := by
  simp [fl_householderVector, hi]

/-- Tail components of the rounded Householder vector agree with the exact
    Householder vector.  This is the exact-copy part of Higham Lemma 18.1; the
    first-component perturbation bound is proved later in this file by
    `fl_householderVector_zero_relative_error`. -/
theorem fl_householderVector_tail_eq_householderVector (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n)
    (hi : i ≠ ⟨0, hn⟩) :
    fl_householderVector fp hn x i = householderVector hn x i := by
  rw [fl_householderVector_tail fp hn x i hi,
    householderVector_tail hn x i hi]

/-- The first component of the Householder vector is one rounded addition. -/
theorem fl_householderVector_zero_unroll (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∃ δ : ℝ,
      |δ| ≤ fp.u ∧
      fl_householderVector fp hn x ⟨0, hn⟩ =
        (x ⟨0, hn⟩ + fl_householderScale fp hn x) * (1 + δ) := by
  obtain ⟨δ, hδ, hadd⟩ :=
    fp.model_add (x ⟨0, hn⟩) (fl_householderScale fp hn x)
  exact ⟨δ, hδ, by simpa [fl_householderVector] using hadd⟩

/-- First-component part of Higham Lemma 18.1 for the concrete rounded
    Householder vector.

    For nonzero `x`, the rounded first component produced by
    `fl_householderVector` is a relative perturbation of the exact first
    component `x_0+s`, with a `γ_{n+2}` bound.  The proof combines:

    * the implementation-backed norm/scale theorem
      `fl_householderScale_relative_error`;
    * the no-cancellation exact lemma `householderVector_zero_abs_eq`;
    * one rounded addition via `FPModel.model_add`;
    * `gamma_mul` to combine the `γ_{n+1}` scale error with the final
      addition rounding. -/
theorem fl_householderVector_zero_relative_error (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hn : gammaValid fp (2 * (n + 2))) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp (n + 2) ∧
      fl_householderVector fp hn0 x ⟨0, hn0⟩ =
        householderVector hn0 x ⟨0, hn0⟩ * (1 + θ) := by
  let first : Fin n := ⟨0, hn0⟩
  let s : ℝ := householderScale hn0 x
  let v0 : ℝ := householderVector hn0 x first
  have hvalid_scale : gammaValid fp (2 * (n + 1)) :=
    gammaValid_mono fp (by omega) hn
  have hvalid_n2 : gammaValid fp (n + 2) :=
    gammaValid_mono fp (by omega) hn
  have hvalid_1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
  obtain ⟨θs, hθs, hscale⟩ :=
    fl_householderScale_relative_error fp hn0 x hvalid_scale
  obtain ⟨δadd, hδadd, hadd⟩ :=
    fp.model_add (x first) (fl_householderScale fp hn0 x)
  have hv0_ne : v0 ≠ 0 := by
    simpa [v0, first] using householderVector_zero_ne_zero_of_ne_zero hn0 x hx
  let φ : ℝ := s * θs / v0
  have hs_abs_le_v0_abs : |s| ≤ |v0| := by
    have hv_abs := householderVector_zero_abs_eq hn0 x
    rw [hv_abs]
    linarith [abs_nonneg (x first)]
  have hγ_nonneg : 0 ≤ gamma fp (n + 1) :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hn)
  have hφ_bound : |φ| ≤ gamma fp (n + 1) := by
    have hv0_abs_pos : 0 < |v0| := abs_pos.mpr hv0_ne
    have hnum :
        |s| * |θs| ≤ |v0| * gamma fp (n + 1) :=
      mul_le_mul hs_abs_le_v0_abs hθs (abs_nonneg θs) (abs_nonneg v0)
    have hdiv :
        |s| * |θs| / |v0| ≤
          (|v0| * gamma fp (n + 1)) / |v0| :=
      div_le_div_of_nonneg_right hnum (abs_nonneg v0)
    have hcancel :
        (|v0| * gamma fp (n + 1)) / |v0| =
          gamma fp (n + 1) := by
      field_simp [hv0_abs_pos.ne']
    unfold φ
    calc
      |s * θs / v0| = |s| * |θs| / |v0| := by
        rw [abs_div, abs_mul]
      _ ≤ (|v0| * gamma fp (n + 1)) / |v0| := hdiv
      _ = gamma fp (n + 1) := hcancel
  have hδ_gamma : |δadd| ≤ gamma fp 1 :=
    le_trans hδadd (u_le_gamma fp one_pos hvalid_1)
  obtain ⟨θ, hθ, hprod⟩ :=
    gamma_mul fp (n + 1) 1 φ δadd hφ_bound hδ_gamma hvalid_n2
  refine ⟨θ, hθ, ?_⟩
  have hbase : x first + fl_householderScale fp hn0 x = v0 * (1 + φ) := by
    have hv0_eq : v0 = x first + s := by
      simp [v0, s, first]
    have hscale_s : fl_householderScale fp hn0 x = s * (1 + θs) := by
      simpa [s] using hscale
    unfold φ
    rw [hscale_s]
    calc
      x first + s * (1 + θs) = v0 + s * θs := by
        rw [hv0_eq]
        ring
      _ = v0 * (1 + s * θs / v0) := by
        field_simp [hv0_ne]
  simp only [fl_householderVector_zero]
  rw [hadd, hbase]
  rw [mul_assoc, hprod]

/-- Relative-error bridge for the rounded beta denominator.

    The denominator used by Higham Lemma 18.1 is `s*v_0`.  The concrete beta
    kernel first computes `fl_mul s_hat v_hat_0`; this theorem proves that this
    product is a relative perturbation of the exact denominator.  It packages
    the already-proved scale error, first-component error, and one rounded
    multiplication. -/
theorem fl_householderBeta_denominator_relative_error (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hn : gammaValid fp (2 * n + 4)) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp (2 * n + 4) ∧
      fp.fl_mul (fl_householderScale fp hn0 x)
          (fl_householderVector fp hn0 x ⟨0, hn0⟩) =
        (householderScale hn0 x *
          householderVector hn0 x ⟨0, hn0⟩) * (1 + θ) := by
  have hvalid_scale : gammaValid fp (2 * (n + 1)) :=
    gammaValid_mono fp (by omega) hn
  have hvalid_first : gammaValid fp (2 * (n + 2)) := by
    simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn
  have hvalid_pair : gammaValid fp ((n + 1) + (n + 2)) :=
    gammaValid_mono fp (by omega) hn
  have hvalid_total : gammaValid fp (((n + 1) + (n + 2)) + 1) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, two_mul] using hn
  obtain ⟨θs, hθs, hscale⟩ :=
    fl_householderScale_relative_error fp hn0 x hvalid_scale
  obtain ⟨θv, hθv, hv0⟩ :=
    fl_householderVector_zero_relative_error fp hn0 x hx hvalid_first
  obtain ⟨δmul, hδmul, hmul⟩ :=
    fp.model_mul (fl_householderScale fp hn0 x)
      (fl_householderVector fp hn0 x ⟨0, hn0⟩)
  obtain ⟨θsv, hθsv, hprod_sv⟩ :=
    gamma_mul fp (n + 1) (n + 2) θs θv hθs hθv hvalid_pair
  have hvalid_one : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
  have hδ_gamma : |δmul| ≤ gamma fp 1 :=
    le_trans hδmul (u_le_gamma fp one_pos hvalid_one)
  obtain ⟨θ, hθ, hprod⟩ :=
    gamma_mul fp ((n + 1) + (n + 2)) 1 θsv δmul
      hθsv hδ_gamma hvalid_total
  refine ⟨θ, ?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, two_mul] using hθ
  · rw [hmul, hscale, hv0]
    calc
      householderScale hn0 x * (1 + θs) *
          (householderVector hn0 x ⟨0, hn0⟩ * (1 + θv)) *
          (1 + δmul)
          =
            (householderScale hn0 x *
              householderVector hn0 x ⟨0, hn0⟩) *
              (((1 + θs) * (1 + θv)) * (1 + δmul)) := by
                ring
      _ =
            (householderScale hn0 x *
              householderVector hn0 x ⟨0, hn0⟩) *
              ((1 + θsv) * (1 + δmul)) := by
                rw [hprod_sv]
      _ =
            (householderScale hn0 x *
              householderVector hn0 x ⟨0, hn0⟩) * (1 + θ) := by
                rw [hprod]

/-- Beta part of Higham Lemma 18.1 for the concrete rounded beta kernel.

    This proves the source constant `γ_{4n+8}` for
    `beta_hat = fl_div 1 (fl_mul s_hat v_hat_0)`.  The proof first uses
    `fl_householderBeta_denominator_relative_error` to obtain a
    `γ_{2n+4}` denominator perturbation, then applies
    `gamma_inv_mul_roundoff` to combine the reciprocal and final rounded
    division without losing an extra gamma index. -/
theorem fl_householderBeta_relative_error (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hn : gammaValid fp (4 * n + 8)) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp (4 * n + 8) ∧
      fl_householderBeta fp hn0 x =
        householderBetaFromScale hn0 x * (1 + θ) := by
  let d : ℝ :=
    householderScale hn0 x * householderVector hn0 x ⟨0, hn0⟩
  have hvalid_den : gammaValid fp (2 * n + 4) :=
    gammaValid_mono fp (by omega) hn
  obtain ⟨θd, hθd, hden⟩ :=
    fl_householderBeta_denominator_relative_error fp hn0 x hx hvalid_den
  have hd_ne : d ≠ 0 := by
    unfold d
    exact mul_ne_zero
      (householderScale_ne_zero_of_ne_zero hn0 x hx)
      (householderVector_zero_ne_zero_of_ne_zero hn0 x hx)
  have hvalid_2den : gammaValid fp (2 * (2 * n + 4)) :=
    gammaValid_mono fp (by omega) hn
  have hγ_lt : gamma fp (2 * n + 4) < 1 :=
    gamma_lt_one fp (2 * n + 4) hvalid_2den
  have hfactor_pos : 0 < 1 + θd := by
    linarith [neg_abs_le θd, hθd, hγ_lt]
  have hden' :
      fp.fl_mul (fl_householderScale fp hn0 x)
          (fl_householderVector fp hn0 x ⟨0, hn0⟩) =
        d * (1 + θd) := by
    simpa [d] using hden
  have hden_hat_ne :
      fp.fl_mul (fl_householderScale fp hn0 x)
          (fl_householderVector fp hn0 x ⟨0, hn0⟩) ≠ 0 := by
    rw [hden']
    exact mul_ne_zero hd_ne (ne_of_gt hfactor_pos)
  obtain ⟨δdiv, hδdiv, hdiv⟩ :=
    fp.model_div 1
      (fp.fl_mul (fl_householderScale fp hn0 x)
        (fl_householderVector fp hn0 x ⟨0, hn0⟩)) hden_hat_ne
  obtain ⟨θ, hθ, hrecip⟩ :=
    gamma_inv_mul_roundoff fp (2 * n + 4) θd δdiv
      (by omega) hθd hδdiv hfactor_pos hvalid_2den
  refine ⟨θ, ?_, ?_⟩
  · have hidx : 2 * (2 * n + 4) = 4 * n + 8 := by omega
    simpa [hidx] using hθ
  · calc
      fl_householderBeta fp hn0 x =
          (1 / (d * (1 + θd))) * (1 + δdiv) := by
            unfold fl_householderBeta
            simp only
            rw [hdiv, hden']
      _ =
          (1 / d) * ((1 / (1 + θd)) * (1 + δdiv)) := by
            field_simp [hd_ne, hfactor_pos.ne']
      _ = (1 / d) * (1 + θ) := by
            rw [hrecip]
      _ = householderBetaFromScale hn0 x * (1 + θ) := by
            simp [d, householderBetaFromScale]

/-- Concrete Householder construction satisfies the Higham Lemma 18.1
    construction contract.

    This is the first full implementation-backed bridge for the Householder
    construction layer: the tail, first-component, and beta clauses of
    `HouseholderConstructionError` are all proved from `fl_householderScale`,
    `fl_householderVector`, `fl_householderBeta`, and lower-level `FPModel`
    primitive rounding theorems. -/
theorem fl_householderConstructionError (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hn : gammaValid fp (4 * n + 8)) :
    HouseholderConstructionError fp hn0 x
      (fl_householderVector fp hn0 x)
      (fl_householderBeta fp hn0 x) := by
  refine ⟨?tail, ?first, ?beta⟩
  · intro i hi
    exact fl_householderVector_tail_eq_householderVector fp hn0 x i hi
  · exact fl_householderVector_zero_relative_error fp hn0 x hx
      (gammaValid_mono fp (by omega) hn)
  · exact fl_householderBeta_relative_error fp hn0 x hx hn

/-- Analysis-only normalized computed Householder vector.

    Higham rewrites `I - beta*v*vᵀ` as `I - w*wᵀ` with
    `w = sqrt(beta) v`.  This definition applies the same algebraic
    normalization to the computed pair `(v_hat, beta_hat)`; it is not an extra
    floating-point operation in the algorithm. -/
noncomputable def fl_householderNormalizedVector (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) : Fin n → ℝ :=
  householderNormalizedVector n
    (fl_householderVector fp hn x)
    (fl_householderBeta fp hn x)

/-- Tail entries of the analysis-only normalized computed Householder vector.

The normalized vector is `sqrt(beta_hat) * v_hat`; since the rounded
Householder vector copies all tail entries of the active vector exactly, its
normalized tail is the same common scale times the input tail. -/
theorem fl_householderNormalizedVector_tail (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n)
    (hi : i ≠ ⟨0, hn⟩) :
    fl_householderNormalizedVector fp hn x i =
      Real.sqrt (fl_householderBeta fp hn x) * x i := by
  rw [fl_householderNormalizedVector, householderNormalizedVector,
    fl_householderVector_tail fp hn x i hi]

/-- Successor-index form of `fl_householderNormalizedVector_tail`. -/
theorem fl_householderNormalizedVector_succ (fp : FPModel)
    {n : ℕ} (x : Fin (n + 1) → ℝ) (i : Fin n) :
    fl_householderNormalizedVector fp (Nat.succ_pos n) x i.succ =
      Real.sqrt (fl_householderBeta fp (Nat.succ_pos n) x) * x i.succ := by
  have hi : i.succ ≠ (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  exact fl_householderNormalizedVector_tail fp (Nat.succ_pos n) x i.succ hi

/-- Componentwise relative-error form for the vector part of
    `HouseholderConstructionError`. -/
theorem householderConstruction_vector_component_relative_error
    (fp : FPModel) {n : ℕ} (hn0 : 0 < n)
    (x v_hat : Fin n → ℝ) (beta_hat : ℝ)
    (hvalid : gammaValid fp (n + 2))
    (hcon : HouseholderConstructionError fp hn0 x v_hat beta_hat) :
    ∀ i : Fin n, ∃ θ : ℝ,
      |θ| ≤ gamma fp (n + 2) ∧
      v_hat i = householderVector hn0 x i * (1 + θ) := by
  intro i
  by_cases hi : i = ⟨0, hn0⟩
  · subst hi
    exact hcon.first
  · refine ⟨0, ?_, ?_⟩
    · simpa using gamma_nonneg fp hvalid
    · rw [hcon.tail i hi]
      ring

/-- Convert the implementation-backed Householder construction contract into
    Higham's normalized-vector perturbation model (equation 18.3).

    The exact normalized vector is `sqrt(beta) * v`; the computed normalized
    vector is the analysis-only `sqrt(beta_hat) * v_hat`.  The bound is stated
    explicitly as `γ_{5n+10}`, which is one concrete instance of Higham's
    generic `γ_{cm}` notation. -/
theorem householderVectorError_from_construction (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x v_hat : Fin n → ℝ) (beta_hat : ℝ)
    (hx : x ≠ 0)
    (hvalid : gammaValid fp (8 * n + 16))
    (hcon : HouseholderConstructionError fp hn0 x v_hat beta_hat) :
    HouseholderVectorError n
      (householderNormalizedVector n
        (householderVector hn0 x) (householderBetaFromScale hn0 x))
      (householderNormalizedVector n v_hat beta_hat)
      (gamma fp (5 * n + 10)) := by
  let beta : ℝ := householderBetaFromScale hn0 x
  let v : Fin n → ℝ := householderVector hn0 x
  let vnorm : Fin n → ℝ := householderNormalizedVector n v beta
  let vhatnorm : Fin n → ℝ := householderNormalizedVector n v_hat beta_hat
  have hvalid_beta : gammaValid fp (4 * n + 8) :=
    gammaValid_mono fp (by omega) hvalid
  have hvalid_vec : gammaValid fp (n + 2) :=
    gammaValid_mono fp (by omega) hvalid
  have hvalid_sqrt : gammaValid fp (2 * (4 * n + 8)) := by
    have hidx : 2 * (4 * n + 8) = 8 * n + 16 := by omega
    simpa [hidx] using hvalid
  have hvalid_combine : gammaValid fp ((4 * n + 8) + (n + 2)) :=
    gammaValid_mono fp (by omega) hvalid
  have hvalid_eps : gammaValid fp (5 * n + 10) :=
    gammaValid_mono fp (by omega) hvalid
  have hbeta_pos : 0 < beta := by
    simpa [beta] using householderBetaFromScale_pos_of_ne_zero hn0 x hx
  have hbeta_nonneg : 0 ≤ beta := le_of_lt hbeta_pos
  have hbeta_norm :
      beta * (∑ i : Fin n, v i * v i) = 2 := by
    simpa [beta, v] using householderBetaFromScale_mul_norm_sq hn0 x hx
  obtain ⟨θbeta, hθbeta, hbeta_hat⟩ := hcon.beta
  have hgamma_lt : gamma fp (4 * n + 8) < 1 :=
    gamma_lt_one fp (4 * n + 8) hvalid_sqrt
  have htheta_beta_pos : 0 < 1 + θbeta := by
    linarith [neg_abs_le θbeta, hθbeta, hgamma_lt]
  refine ⟨?norm_sq, ?pert⟩
  · simpa [vnorm, v, beta] using
      householderNormalizedVector_norm_sq n v beta hbeta_nonneg hbeta_norm
  · let Δv : Fin n → ℝ := fun i => vhatnorm i - vnorm i
    refine ⟨Δv, ?_, ?_⟩
    · intro i
      unfold Δv
      ring
    · intro i
      obtain ⟨θv, hθv, hv_hat⟩ :=
        householderConstruction_vector_component_relative_error
          fp hn0 x v_hat beta_hat hvalid_vec hcon i
      obtain ⟨ψ, hψ, hcollapse⟩ :=
        sqrt_one_add_mul_relative_gamma fp (4 * n + 8) (n + 2)
          θbeta θv hθbeta hθv hvalid_sqrt hvalid_combine
      have hrel :
          vhatnorm i = vnorm i * (1 + ψ) := by
        unfold vhatnorm vnorm householderNormalizedVector
        rw [hbeta_hat, hv_hat]
        change Real.sqrt (beta * (1 + θbeta)) * (v i * (1 + θv)) =
          (Real.sqrt beta * v i) * (1 + ψ)
        rw [Real.sqrt_mul hbeta_nonneg]
        calc
          Real.sqrt beta * Real.sqrt (1 + θbeta) * (v i * (1 + θv))
              =
                (Real.sqrt beta * v i) *
                  (Real.sqrt (1 + θbeta) * (1 + θv)) := by
                    ring
          _ = (Real.sqrt beta * v i) * (1 + ψ) := by
                rw [hcollapse]
      have hdelta :
          Δv i = vnorm i * ψ := by
        unfold Δv
        rw [hrel]
        ring
      rw [hdelta, abs_mul]
      calc
        |vnorm i| * |ψ| ≤ |vnorm i| * gamma fp (5 * n + 10) := by
          have hψ' : |ψ| ≤ gamma fp (5 * n + 10) := by
            have hidx : (4 * n + 8) + (n + 2) = 5 * n + 10 := by omega
            simpa [hidx] using hψ
          exact mul_le_mul_of_nonneg_left hψ' (abs_nonneg (vnorm i))
        _ = gamma fp (5 * n + 10) * |vnorm i| := by ring

/-- Concrete rounded Householder construction satisfies Higham equation (18.3)
    after algebraic normalization.

    This is the direct implementation-backed version of
    `householderVectorError_from_construction`. -/
theorem fl_householderVectorError (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hvalid : gammaValid fp (8 * n + 16)) :
    HouseholderVectorError n
      (householderNormalizedVector n
        (householderVector hn0 x) (householderBetaFromScale hn0 x))
      (fl_householderNormalizedVector fp hn0 x)
      (gamma fp (5 * n + 10)) := by
  have hcon : HouseholderConstructionError fp hn0 x
      (fl_householderVector fp hn0 x)
      (fl_householderBeta fp hn0 x) :=
    fl_householderConstructionError fp hn0 x hx
      (gammaValid_mono fp (by omega) hvalid)
  simpa [fl_householderNormalizedVector] using
    householderVectorError_from_construction fp hn0 x
      (fl_householderVector fp hn0 x)
      (fl_householderBeta fp hn0 x)
      hx hvalid hcon

/-- Unroll `fl_householderBeta` through the rounded product `s_hat*v_hat_0`
    and final division, matching Higham Lemma 18.1.  The nonzero denominator
    hypothesis is exactly the condition needed to invoke `FPModel.model_div`. -/
theorem fl_householderBeta_unroll (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ)
    (hden : fp.fl_mul (fl_householderScale fp hn0 x)
      (fl_householderVector fp hn0 x ⟨0, hn0⟩) ≠ 0) :
    ∃ (δmul δdiv : ℝ),
      |δmul| ≤ fp.u ∧
      |δdiv| ≤ fp.u ∧
      fl_householderBeta fp hn0 x =
        ((1 : ℝ) /
          ((fl_householderScale fp hn0 x) *
            (fl_householderVector fp hn0 x ⟨0, hn0⟩) * (1 + δmul))) *
          (1 + δdiv) := by
  obtain ⟨δmul, hδmul, hmul⟩ :=
    fp.model_mul (fl_householderScale fp hn0 x)
      (fl_householderVector fp hn0 x ⟨0, hn0⟩)
  obtain ⟨δdiv, hδdiv, hdiv⟩ :=
    fp.model_div 1
      (fp.fl_mul (fl_householderScale fp hn0 x)
        (fl_householderVector fp hn0 x ⟨0, hn0⟩)) hden
  refine ⟨δmul, δdiv, hδmul, hδdiv, ?_⟩
  unfold fl_householderBeta
  simp only
  rw [hdiv, hmul]

end NumStability
