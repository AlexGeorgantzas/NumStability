-- Algorithms/QR/HouseholderConstruction2.lean
--
-- Construction 2 (the "alternative"-sign, cancellation-avoiding construction)
-- of the Householder vector and its backward-error contract.
--
-- Source: Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- §19.3, Lemma 19.1 / eq (19.2) (p. 355, statement p. 357, proof p. 358).
--
-- Higham's Lemma 19.1 states the backward-error contract for BOTH sign
-- conventions.  Construction 1 (the "usual" sign, eq (19.1)) is formalized in
-- `HouseholderReflector.lean` (Codex-owned; imported here, never edited).  This
-- file adds Construction 2:
--
--   σ  = sign(x₁)‖x‖₂                     (eq (19.2a); the ALTERNATIVE +sign)
--   v  = x   except the first entry
--   v₁ = x₁ − σ = −(x₂²+…+xₙ²)/(x₁+σ)     (eq (19.2b), cancellation-avoiding)
--   β  = 2/(vᵀv)                          (source op-order form −1/(σ·v₁))
--
-- The point of Construction 2 is that x₁ and σ share sign, so the denominator
-- `x₁+σ` never cancels: `|x₁+σ| = |x₁| + ‖x‖₂ ≥ ‖x‖₂ > 0` for `x ≠ 0`.
--
-- The repository's `householderScale hn x = sign(x₀)·‖x‖₂` is exactly
-- Construction 2's σ (it is also the pseudocode variable `s`, shared by both
-- constructions), so this file reuses `householderScale` unchanged.
-- Construction 1's exact first entry is `x₀ + s`; Construction 2's is `x₀ − s`.
--
-- SCOPE / SIGN SUBTLETIES (documented honestly):
--
-- 1. Degenerate axis case.  Unlike Construction 1 (whose first entry `x₀+σ` is
--    `2x₀ ≠ 0` when x is aligned with e₀), Construction 2's first entry
--    `x₀−σ` VANISHES when x is a nonzero multiple of e₀ (then σ = x₀), so the
--    reflector `β = 2/(vᵀv)` is undefined there.  The tail/first-entry error
--    contract (the core of eq (19.2b)) needs only `x ≠ 0`; the β contract and
--    `vᵀv > 0` additionally require a nonzero tail (`householderTailSq ≠ 0`,
--    i.e. x not on the first coordinate axis).  In the QR reduction this is
--    exactly the nondegenerate stage where a reflector is actually needed.
--
-- 2. β sign.  p. 355 gives β = 2/(vᵀv) = −1/(σ·v₁).  With σ = s > 0 (case
--    x₀ > 0) and v₁ = x₀−s ≤ 0 the product σ·v₁ ≤ 0, so the CORRECT positive β
--    is −1/(σ·v₁), NOT the literal "1/(sv₁)" printed in the Lemma 19.1
--    pseudocode table.  We anchor exact β on 2/(vᵀv) and prove it equals
--    −1/(σ·v₁); the rounded kernel forms `fl(−1/(σ̂·v̂₁))` accordingly.
--
-- Everything below is proved from the Codex-owned `fl_norm2`/`gamma` workhorses;
-- there are no new floating-point assumptions.

import NumStability.Algorithms.Norm2
import NumStability.Algorithms.QR.HouseholderReflector
import NumStability.Algorithms.QR.HouseholderSpec

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §19.1  Construction 2 exact primitives (eq (19.2))
-- ============================================================

/-- Construction-2 scale `σ = sign(x₀)·‖x‖₂` (eq (19.2a), p. 355).

    The *alternative* sign `sign(σ) = sign(x₀)`, opposite to eq (19.1)'s
    `−sign(x₀)`.  In the repository's encoding this is definitionally the same
    expression as `householderScale` (`sign(x₀)·‖x‖₂` = the pseudocode variable
    `s`, shared by both constructions); the sign difference lives entirely in
    the first-entry formula, not in `s`. -/
noncomputable def householderScaleAlt {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  householderScale hn x

@[simp] theorem householderScaleAlt_eq {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    householderScaleAlt hn x = householderScale hn x := rfl

/-- Sum of squares of the tail entries `x₂² + … + xₙ²` (all indices `≠ 0`). -/
noncomputable def householderTailSq {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn⟩, x i * x i

/-- `x₂²+…+xₙ² = ‖x‖₂² − x₀²`: the tail sum of squares equals the total sum of
    squares minus the first term. -/
theorem householderTailSq_eq_sub {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    householderTailSq hn x =
      (∑ i : Fin n, x i * x i) - x ⟨0, hn⟩ * x ⟨0, hn⟩ := by
  unfold householderTailSq
  have hmem : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) :=
    Finset.mem_univ _
  have hsplit :=
    Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun i => x i * x i) hmem
  linarith [hsplit]

/-- The tail sum of squares is nonnegative. -/
theorem householderTailSq_nonneg {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    0 ≤ householderTailSq hn x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- Construction-2 exact first entry `v₁ = x₀ − σ` (eq (19.2b), first form). -/
noncomputable def householderVectorAltFirst {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  x ⟨0, hn⟩ - householderScale hn x

/-- **Non-cancellation denominator lemma** (the whole point of Construction 2).

    For nonzero `x`, the denominator `x₀ + σ` of eq (19.2b) is nonzero.  Because
    `x₀` and `σ = sign(x₀)‖x‖₂` share sign, `|x₀+σ| = |x₀| + ‖x‖₂ ≥ ‖x‖₂ > 0`.

    Reuses the Construction-1 non-cancellation fact: the sum `x₀ + σ` is
    literally Construction 1's first entry `householderVector hn x ⟨0⟩`, whose
    nonvanishing is `householderVector_zero_ne_zero_of_ne_zero`. -/
theorem householderVectorAlt_denom_ne_zero {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    x ⟨0, hn⟩ + householderScale hn x ≠ 0 := by
  have h := householderVector_zero_ne_zero_of_ne_zero hn x hx
  rwa [householderVector_zero] at h

/-- Explicit magnitude of the (19.2b) denominator: `|x₀+σ| = |x₀| + ‖x‖₂`.

    The quantitative no-cancellation statement; the repository's
    `householderVector_zero_abs_eq` already proves it for the sum `x₀ + s`. -/
theorem householderVectorAlt_denom_abs {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    |x ⟨0, hn⟩ + householderScale hn x| =
      |x ⟨0, hn⟩| + |householderScale hn x| := by
  have h := householderVector_zero_abs_eq hn x
  rwa [householderVector_zero] at h

/-- **Equation (19.2b)**: the cancellation-avoiding first-entry formula agrees
    with `x₀ − σ`.

    `v₁ = x₀ − σ = −(x₂²+…+xₙ²)/(x₀+σ)`, because
    `(x₀−σ)(x₀+σ) = x₀² − σ² = x₀² − ‖x‖₂² = −(x₂²+…+xₙ²)`, using `σ² = ‖x‖₂²`
    (`householderScale_mul_self`) and the nonzero denominator. -/
theorem householderVectorAltFirst_eq_quotient {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    householderVectorAltFirst hn x =
      (-householderTailSq hn x) / (x ⟨0, hn⟩ + householderScale hn x) := by
  have hden : x ⟨0, hn⟩ + householderScale hn x ≠ 0 :=
    householderVectorAlt_denom_ne_zero hn x hx
  have hscale_sq := householderScale_mul_self hn x
  have htail := householderTailSq_eq_sub hn x
  unfold householderVectorAltFirst
  rw [eq_div_iff hden]
  have hkey :
      (x ⟨0, hn⟩ - householderScale hn x) *
          (x ⟨0, hn⟩ + householderScale hn x) =
        x ⟨0, hn⟩ * x ⟨0, hn⟩ -
          householderScale hn x * householderScale hn x := by ring
  rw [hkey, hscale_sq, htail]
  ring

/-- Construction-2 exact Householder vector (eq (19.2)).

    First entry is the (19.2b) quotient `−(x₂²+…+xₙ²)/(x₀+σ)`; every tail entry
    is copied from `x`.  The rounded counterpart is `fl_householderVectorAlt`. -/
noncomputable def householderVectorAlt {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if i = ⟨0, hn⟩ then
      (-householderTailSq hn x) / (x ⟨0, hn⟩ + householderScale hn x)
    else
      x i

@[simp] theorem householderVectorAlt_zero {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    householderVectorAlt hn x ⟨0, hn⟩ =
      (-householderTailSq hn x) / (x ⟨0, hn⟩ + householderScale hn x) := by
  simp [householderVectorAlt]

/-- The exact Construction-2 first entry equals `x₀ − σ`. -/
theorem householderVectorAlt_zero_eq_first {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    householderVectorAlt hn x ⟨0, hn⟩ = householderVectorAltFirst hn x := by
  rw [householderVectorAlt_zero, householderVectorAltFirst_eq_quotient hn x hx]

/-- Tail entries of the exact Construction-2 vector are copied exactly. -/
theorem householderVectorAlt_tail {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (i : Fin n) (hi : i ≠ ⟨0, hn⟩) :
    householderVectorAlt hn x i = x i := by
  simp [householderVectorAlt, hi]

/-- Construction-2 exact `β = 2/(vᵀv)` for the unnormalized alternative vector.

    Definitionally the same reflector normalization as Construction 1's
    `householderBeta`, applied to the Construction-2 vector. -/
noncomputable def householderBetaAlt {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  2 / (∑ i : Fin n, householderVectorAlt hn x i * householderVectorAlt hn x i)

/-- Construction-2 exact `β` in Higham's source operation order `β = −1/(σ·v₁)`
    (p. 355, β = −1/(σv₁) with σ = s here).

    The leading minus sign is the documented sign subtlety (see file header):
    with the alternative sign `σ·v₁ = s·(x₀−s) ≤ 0`, so a positive β needs the
    negation.  Exact target of the rounded kernel `fl_householderBetaAlt`. -/
noncomputable def householderBetaAltFromScale {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  -1 / (householderScale hn x * householderVectorAltFirst hn x)

-- ============================================================
-- Exact algebra bridges for β  (vᵀv = −2 σ v₁)
-- ============================================================

/-- The Construction-2 norm-square splits as `v₁² + (x₂²+…+xₙ²)`. -/
theorem householderVectorAlt_norm_sq_split {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    (∑ i : Fin n, householderVectorAlt hn x i * householderVectorAlt hn x i) =
      householderVectorAltFirst hn x * householderVectorAltFirst hn x +
        householderTailSq hn x := by
  have hmem : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) :=
    Finset.mem_univ _
  have hv0 : householderVectorAlt hn x ⟨0, hn⟩ = householderVectorAltFirst hn x :=
    householderVectorAlt_zero_eq_first hn x hx
  calc
    (∑ i : Fin n, householderVectorAlt hn x i * householderVectorAlt hn x i)
        =
          (∑ i ∈ (Finset.univ : Finset (Fin n)).erase ⟨0, hn⟩,
            householderVectorAlt hn x i * householderVectorAlt hn x i) +
            householderVectorAlt hn x ⟨0, hn⟩ * householderVectorAlt hn x ⟨0, hn⟩ := by
          rw [Finset.sum_erase_add (Finset.univ : Finset (Fin n))
            (fun i => householderVectorAlt hn x i * householderVectorAlt hn x i) hmem]
    _ = householderTailSq hn x +
          householderVectorAltFirst hn x * householderVectorAltFirst hn x := by
          rw [hv0]
          congr 1
          unfold householderTailSq
          apply Finset.sum_congr rfl
          intro i hi
          have hne : i ≠ ⟨0, hn⟩ := (Finset.mem_erase.mp hi).1
          rw [householderVectorAlt_tail hn x i hne]
    _ = householderVectorAltFirst hn x * householderVectorAltFirst hn x +
          householderTailSq hn x := by ring

/-- `vᵀv = −2·σ·v₁` for the Construction-2 vector (`v₁ = x₀ − σ`).

    Analogue of `householderVector_norm_sq_eq_two_scale_mul`; the sign flips
    because Construction 2 uses `x₀ − σ` in place of `x₀ + σ`. -/
theorem householderVectorAlt_norm_sq_eq {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    (∑ i : Fin n, householderVectorAlt hn x i * householderVectorAlt hn x i) =
      -2 * householderScale hn x * householderVectorAltFirst hn x := by
  have hscale_sq := householderScale_mul_self hn x
  have htail := householderTailSq_eq_sub hn x
  rw [householderVectorAlt_norm_sq_split hn x hx, htail]
  unfold householderVectorAltFirst
  have hsumeq :
      (∑ i : Fin n, x i * x i) =
        householderScale hn x * householderScale hn x := hscale_sq.symm
  rw [hsumeq]; ring

/-- With a nonzero tail, `σ·v₁ < 0`, so `β = −1/(σv₁) > 0`. -/
theorem householderScale_mul_first_neg {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) (htail : householderTailSq hn x ≠ 0) :
    householderScale hn x * householderVectorAltFirst hn x < 0 := by
  have hnorm := householderVectorAlt_norm_sq_eq hn x hx
  have htail_pos : 0 < householderTailSq hn x :=
    lt_of_le_of_ne (householderTailSq_nonneg hn x) (Ne.symm htail)
  have hnorm_pos :
      0 < ∑ i : Fin n,
        householderVectorAlt hn x i * householderVectorAlt hn x i := by
    rw [householderVectorAlt_norm_sq_split hn x hx]
    have := mul_self_nonneg (householderVectorAltFirst hn x)
    linarith
  -- −2 σ v₁ = vᵀv > 0 ⟹ σ v₁ < 0.
  rw [hnorm] at hnorm_pos
  nlinarith [hnorm_pos]

/-- Construction-2 exact `vᵀv` is positive for nonzero `x` with nonzero tail. -/
theorem householderVectorAlt_norm_sq_pos {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) (htail : householderTailSq hn x ≠ 0) :
    0 < ∑ i : Fin n,
      householderVectorAlt hn x i * householderVectorAlt hn x i := by
  rw [householderVectorAlt_norm_sq_eq hn x hx]
  have hneg := householderScale_mul_first_neg hn x hx htail
  nlinarith [hneg]

/-- Higham's source `β = −1/(σv₁)` agrees with the reflector `β = 2/(vᵀv)`
    whenever the tail is nonzero. -/
theorem householderBetaAltFromScale_eq_betaAlt {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) (htail : householderTailSq hn x ≠ 0) :
    householderBetaAltFromScale hn x = householderBetaAlt hn x := by
  have hnorm := householderVectorAlt_norm_sq_eq hn x hx
  have hden : householderScale hn x * householderVectorAltFirst hn x < 0 :=
    householderScale_mul_first_neg hn x hx htail
  have hden_ne : householderScale hn x * householderVectorAltFirst hn x ≠ 0 :=
    ne_of_lt hden
  unfold householderBetaAltFromScale householderBetaAlt
  rw [hnorm]
  have hden2 :
      (-2 * householderScale hn x * householderVectorAltFirst hn x) ≠ 0 := by
    have : (-2 : ℝ) * (householderScale hn x * householderVectorAltFirst hn x) ≠ 0 :=
      mul_ne_zero (by norm_num) hden_ne
    simpa [mul_assoc] using this
  field_simp

/-- Higham's source `β` for Construction 2 is positive (nonzero tail). -/
theorem householderBetaAltFromScale_pos {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hx : x ≠ 0) (htail : householderTailSq hn x ≠ 0) :
    0 < householderBetaAltFromScale hn x := by
  have hden := householderScale_mul_first_neg hn x hx htail
  unfold householderBetaAltFromScale
  rw [div_pos_iff]
  right
  constructor
  · norm_num
  · exact hden

-- ============================================================
-- §19.3  Rounded Construction-2 kernels
-- ============================================================

/-- Rounded Construction-2 scale `σ̂ = sign(x₀)·fl_norm2(x)`.

    Identical to Construction 1's `fl_householderScale`: sign is exact, only the
    norm is rounded. -/
noncomputable def fl_householderScaleAlt (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  fl_householderScale fp hn x

@[simp] theorem fl_householderScaleAlt_eq (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) :
    fl_householderScaleAlt fp hn x = fl_householderScale fp hn x := rfl

/-- Rounded tail sum of squares.  Computed as the rounded sum of squares of the
    tail-masked vector `x·[i≠0]` (the first entry contributes `0·0 = 0`), so the
    only rounded arithmetic is the `n`-term accumulation, giving a `γ_n` bound.

    Using the full-length masked dot product (rather than an `(n−1)`-length one)
    costs at most one extra `γ` index and keeps the reuse of the Codex-owned
    `fl_norm2Sq_relative_error` verbatim; this is well within the printed
    `γ̃`-class contract. -/
noncomputable def fl_householderTailSq (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  fl_norm2Sq fp n (fun i => if i = ⟨0, hn⟩ then 0 else x i)

/-- The tail-masked vector has the same sum of squares as the tail. -/
theorem tailMasked_sum_sq {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    (∑ i : Fin n,
        (if i = ⟨0, hn⟩ then (0 : ℝ) else x i) *
          (if i = ⟨0, hn⟩ then (0 : ℝ) else x i)) =
      householderTailSq hn x := by
  unfold householderTailSq
  have hmem : (⟨0, hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) :=
    Finset.mem_univ _
  -- Split the masked sum over univ into (erase) + (first term = 0·0).
  have hsplit :=
    (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun i => (if i = ⟨0, hn⟩ then (0 : ℝ) else x i) *
        (if i = ⟨0, hn⟩ then (0 : ℝ) else x i)) hmem).symm
  rw [hsplit]
  -- first term is 0·0 = 0; erased terms equal xᵢ² since i ≠ ⟨0,hn⟩.
  have hfirst :
      (if (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ then (0 : ℝ) else x ⟨0, hn⟩) *
        (if (⟨0, hn⟩ : Fin n) = ⟨0, hn⟩ then (0 : ℝ) else x ⟨0, hn⟩) = 0 := by
    simp
  rw [hfirst, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hne : i ≠ ⟨0, hn⟩ := (Finset.mem_erase.mp hi).1
  simp [hne]

/-- Relative-error form for the rounded tail sum of squares:
    `fl_tailSq = tailSq·(1+θ_n)` with `|θ| ≤ γ_n`. -/
theorem fl_householderTailSq_relative_error (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (x : Fin n → ℝ) (hval : gammaValid fp n) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp n ∧
      fl_householderTailSq fp hn x = householderTailSq hn x * (1 + θ) := by
  obtain ⟨θ, hθ, hrel⟩ :=
    fl_norm2Sq_relative_error fp n
      (fun i => if i = ⟨0, hn⟩ then (0 : ℝ) else x i) hval
  refine ⟨θ, hθ, ?_⟩
  unfold fl_householderTailSq
  rw [hrel, tailMasked_sum_sq hn x]

/-- Rounded Construction-2 Householder vector (eq (19.2b) operation order).

    First entry `v̂₁ = fl_div(−fl_tailSq, fl_add(x₀, σ̂))`: rounded tail
    sum-of-squares, negated exactly, divided by the rounded sum `x₀+σ̂`
    (`σ̂ = sign(x₀)·fl_norm2`).  Tail copied exactly. -/
noncomputable def fl_householderVectorAlt (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if i = ⟨0, hn⟩ then
      fp.fl_div (-(fl_householderTailSq fp hn x))
        (fp.fl_add (x ⟨0, hn⟩) (fl_householderScale fp hn x))
    else
      x i

@[simp] theorem fl_householderVectorAlt_zero (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (x : Fin n → ℝ) :
    fl_householderVectorAlt fp hn x ⟨0, hn⟩ =
      fp.fl_div (-(fl_householderTailSq fp hn x))
        (fp.fl_add (x ⟨0, hn⟩) (fl_householderScale fp hn x)) := by
  simp [fl_householderVectorAlt]

/-- Tail entries of the rounded Construction-2 vector are copied exactly. -/
theorem fl_householderVectorAlt_tail (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (i : Fin n) (hi : i ≠ ⟨0, hn⟩) :
    fl_householderVectorAlt fp hn x i = x i := by
  simp [fl_householderVectorAlt, hi]

/-- Tail entries of the rounded vector agree with the exact Construction-2
    vector (exact-copy part of Lemma 19.1). -/
theorem fl_householderVectorAlt_tail_eq (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (i : Fin n) (hi : i ≠ ⟨0, hn⟩) :
    fl_householderVectorAlt fp hn x i = householderVectorAlt hn x i := by
  rw [fl_householderVectorAlt_tail fp hn x i hi,
    householderVectorAlt_tail hn x i hi]

/-- Rounded Construction-2 `β = fl_div(−1, fl_mul(σ̂, v̂₁))`. -/
noncomputable def fl_householderBetaAlt (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  let s := fl_householderScaleAlt fp hn x
  let v := fl_householderVectorAlt fp hn x
  fp.fl_div (-1) (fp.fl_mul s (v ⟨0, hn⟩))

-- ============================================================
-- Lemma 19.1 (Construction 2) backward-error contract
-- ============================================================

/-- **Householder Construction-2 error contract** (Higham Lemma 19.1, eq (19.2)).

    Mirrors the Construction-1 `HouseholderConstructionError` field SHAPE
    (exact tail / relative-error first entry / relative-error β), with the
    Construction-2 exact targets `householderVectorAlt` and
    `householderBetaAltFromScale`, and explicit `γ`-class constants:

    * `tail`:  `v̂(2:n) = v(2:n)` exactly;
    * `first`: `v̂₁ = v₁(1 + θ)`, `|θ| ≤ γ_{3n+4}`;
    * `beta`:  `β̂ = β(1 + θ')`, `|θ'| ≤ γ_{8n+12}`.

    HONEST CONSTANTS (differ from Construction 1's `γ_{n+2}` / `γ_{4n+8}`).
    Construction 2's first entry does strictly more arithmetic than
    Construction 1's single rounded add: a full tail sum of `n` squares
    (`γ_n`), a rounded denominator `x₀+σ̂` (`γ_{n+2}` as in Construction 1),
    and a rounded division.  Collapsing numerator (`γ_n`), reciprocal-of-
    denominator + division roundoff (`γ_{2n+4}` via `gamma_inv_mul_roundoff`),
    yields `γ_{3n+4}` for `v̂₁`.  The β denominator then carries
    `γ_{n+1}+γ_{3n+4}+γ_1 → γ_{4n+6}`, and the final reciprocal/division doubles
    it to `γ_{8n+12}`.  Both are in Higham's generic `γ̃`-class (he does not pin
    the integer `c`); the derivations are given in the proving theorems.

    The β clause carries a nonzero-tail nondegeneracy hypothesis in the proving
    theorem (see file header, scope note 1). -/
structure HouseholderConstruction2Error (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (x v_hat : Fin n → ℝ) (beta_hat : ℝ) : Prop where
  /-- Lemma 19.1: `v̂(2:n) = v(2:n)`. -/
  tail : ∀ i : Fin n, i ≠ ⟨0, hn⟩ →
    v_hat i = householderVectorAlt hn x i
  /-- Lemma 19.1: `v̂₁ = v₁(1 + θ)`, `|θ| ≤ γ_{3n+4}` (Construction-2 index). -/
  first : ∃ θ : ℝ,
    |θ| ≤ gamma fp (3 * n + 4) ∧
    v_hat ⟨0, hn⟩ = householderVectorAlt hn x ⟨0, hn⟩ * (1 + θ)
  /-- Lemma 19.1: `β̂ = β(1 + θ')`, `|θ'| ≤ γ_{8n+12}`, source `β = −1/(σ·v₁)`. -/
  beta : ∃ θ : ℝ,
    |θ| ≤ gamma fp (8 * n + 12) ∧
    beta_hat = householderBetaAltFromScale hn x * (1 + θ)

/-- **First-entry error (core of eq (19.2b))**: for nonzero `x`, the rounded
    Construction-2 first entry is a `γ_{3n+4}` relative perturbation of the exact
    `v₁ = −(x₂²+…+xₙ²)/(x₀+σ)`.

    Op count → constant:
    * numerator: `fl_tailSq = tailSq·(1+θt)`, `|θt| ≤ γ_n`
      (`fl_householderTailSq_relative_error`); negation is exact;
    * denominator: `fl_add(x₀,σ̂) = (x₀+σ)·(1+φ)`, `|φ| ≤ γ_{n+2}`, reusing
      Construction 1's proved `fl_householderVector_zero_relative_error`;
    * `(1/(1+φ))·(1+δ_div) = 1+ψ`, `|ψ| ≤ γ_{2n+4}` (`gamma_inv_mul_roundoff`);
    * `(1+θt)·(1+ψ) = 1+θ`, `|θ| ≤ γ_{n+(2n+4)} = γ_{3n+4}` (`gamma_mul`).

    The `x ≠ 0` hypothesis suffices (no nonzero-tail needed): the denominator
    `x₀+σ` is nonzero, and the quotient degrades gracefully to `0 = 0` when the
    tail vanishes. -/
theorem fl_householderVectorAlt_zero_relative_error (fp : FPModel) {n : ℕ}
    (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hval : gammaValid fp (3 * n + 4)) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp (3 * n + 4) ∧
      fl_householderVectorAlt fp hn0 x ⟨0, hn0⟩ =
        householderVectorAlt hn0 x ⟨0, hn0⟩ * (1 + θ) := by
  -- Exact denominator `den = x₀ + σ` (nonzero) and exact v₁ as its quotient.
  let den : ℝ := x ⟨0, hn0⟩ + householderScale hn0 x
  have hden_ne : den ≠ 0 := householderVectorAlt_denom_ne_zero hn0 x hx
  -- Validity specializations.
  have hval_n : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have hval_first : gammaValid fp (2 * (n + 2)) :=
    gammaValid_mono fp (by omega) hval
  have hval_n2 : gammaValid fp (n + 2) := gammaValid_mono fp (by omega) hval
  have hval_recip : gammaValid fp (2 * (n + 2)) :=
    gammaValid_mono fp (by omega) hval
  have hval_mul : gammaValid fp (n + (2 * (n + 2))) :=
    gammaValid_mono fp (by omega) hval
  -- (a) numerator relative error.
  obtain ⟨θt, hθt, htail_rel⟩ :=
    fl_householderTailSq_relative_error fp hn0 x hval_n
  -- (b) denominator relative error, reusing Construction 1's first-entry bound.
  obtain ⟨φ, hφ, hden_rel⟩ :=
    fl_householderVector_zero_relative_error fp hn0 x hx hval_first
  have hden_hat_eq :
      fp.fl_add (x ⟨0, hn0⟩) (fl_householderScale fp hn0 x) = den * (1 + φ) := by
    have h := hden_rel
    rw [fl_householderVector_zero, householderVector_zero] at h
    simpa [den] using h
  -- (c) 1 + φ > 0 ⟹ rounded denominator nonzero.
  have hγ_lt : gamma fp (n + 2) < 1 := gamma_lt_one fp (n + 2) hval_first
  have hφ_pos : 0 < 1 + φ := by
    linarith [neg_abs_le φ, hφ, hγ_lt]
  have hden_hat_ne :
      fp.fl_add (x ⟨0, hn0⟩) (fl_householderScale fp hn0 x) ≠ 0 := by
    rw [hden_hat_eq]; exact mul_ne_zero hden_ne (ne_of_gt hφ_pos)
  -- (d) rounded division roundoff.
  obtain ⟨δd, hδd, hdiv⟩ :=
    fp.model_div (-(fl_householderTailSq fp hn0 x))
      (fp.fl_add (x ⟨0, hn0⟩) (fl_householderScale fp hn0 x)) hden_hat_ne
  -- (e) collapse (1/(1+φ))·(1+δd) → 1 + ψ, |ψ| ≤ γ_{2(n+2)} = γ_{2n+4}.
  obtain ⟨ψ, hψ, hrecip⟩ :=
    gamma_inv_mul_roundoff fp (n + 2) φ δd (by omega) hφ hδd hφ_pos hval_recip
  -- (f) fold θt (index n) with ψ (index 2(n+2)) → θ, |θ| ≤ γ_{n+2(n+2)}.
  obtain ⟨θ, hθ, hprod⟩ :=
    gamma_mul fp n (2 * (n + 2)) θt ψ hθt hψ hval_mul
  refine ⟨θ, ?_, ?_⟩
  · -- n + 2(n+2) = 3n+4
    have hidx : n + 2 * (n + 2) = 3 * n + 4 := by omega
    simpa [hidx] using hθ
  · -- v̂₁ = (−tailSq (1+θt)) / (den (1+φ)) · (1+δd)
    --      = (−tailSq/den) · (1+θt)·(1/(1+φ))·(1+δd)
    --      = v₁ · (1+θt)·(1+ψ) = v₁ · (1+θ).
    have hv1 :
        householderVectorAlt hn0 x ⟨0, hn0⟩ = (-householderTailSq hn0 x) / den := by
      rw [householderVectorAlt_zero]
    simp only [fl_householderVectorAlt_zero]
    rw [hdiv, hden_hat_eq, htail_rel, hv1]
    -- goal: (−(tailSq(1+θt)))/(den(1+φ)) · (1+δd) = ((−tailSq)/den) · (1+θ)
    -- Expand θ = (1+θt)·((1/(1+φ))·(1+δd)) − 1 via hprod, hrecip.
    rw [← hprod, ← hrecip]
    field_simp [hden_ne, hφ_pos.ne']

/-- Relative-error bridge for the rounded β denominator `σ̂·v̂₁`.

    `fl_mul(σ̂, v̂₁) = (σ·v₁)·(1+θ)` with `|θ| ≤ γ_{4n+6}`, combining the scale
    error (`γ_{n+1}`), the first-entry error (`γ_{3n+4}`), and one rounded
    multiplication (`u ≤ γ_1`). -/
theorem fl_householderBetaAlt_denominator_relative_error (fp : FPModel) {n : ℕ}
    (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hval : gammaValid fp (4 * n + 6)) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp (4 * n + 6) ∧
      fp.fl_mul (fl_householderScaleAlt fp hn0 x)
          (fl_householderVectorAlt fp hn0 x ⟨0, hn0⟩) =
        (householderScale hn0 x * householderVectorAltFirst hn0 x) * (1 + θ) := by
  -- Validity specializations.
  have hval_scale : gammaValid fp (2 * (n + 1)) :=
    gammaValid_mono fp (by omega) hval
  have hval_first : gammaValid fp (3 * n + 4) :=
    gammaValid_mono fp (by omega) hval
  have hval_pair : gammaValid fp ((n + 1) + (3 * n + 4)) :=
    gammaValid_mono fp (by omega) hval
  have hval_total : gammaValid fp (((n + 1) + (3 * n + 4)) + 1) :=
    gammaValid_mono fp (by omega) hval
  have hval_one : gammaValid fp 1 := gammaValid_mono fp (by omega) hval
  -- σ̂ = s (1 + θs), |θs| ≤ γ_{n+1}.
  obtain ⟨θs, hθs, hscale⟩ :=
    fl_householderScale_relative_error fp hn0 x hval_scale
  -- v̂₁ = v₁ (1 + θv), |θv| ≤ γ_{3n+4}; here the exact v₁ is x₀ − σ.
  obtain ⟨θv, hθv, hv0⟩ :=
    fl_householderVectorAlt_zero_relative_error fp hn0 x hx hval_first
  have hv0' :
      fl_householderVectorAlt fp hn0 x ⟨0, hn0⟩ =
        householderVectorAltFirst hn0 x * (1 + θv) := by
    rw [hv0, householderVectorAlt_zero_eq_first hn0 x hx]
  -- rounded multiplication roundoff.
  obtain ⟨δmul, hδmul, hmul⟩ :=
    fp.model_mul (fl_householderScaleAlt fp hn0 x)
      (fl_householderVectorAlt fp hn0 x ⟨0, hn0⟩)
  -- combine θs, θv → θsv at index (n+1)+(3n+4).
  obtain ⟨θsv, hθsv, hprod_sv⟩ :=
    gamma_mul fp (n + 1) (3 * n + 4) θs θv hθs hθv hval_pair
  have hδ_gamma : |δmul| ≤ gamma fp 1 :=
    le_trans hδmul (u_le_gamma fp one_pos hval_one)
  -- combine with δmul → θ at index ((n+1)+(3n+4))+1.
  obtain ⟨θ, hθ, hprod⟩ :=
    gamma_mul fp ((n + 1) + (3 * n + 4)) 1 θsv δmul hθsv hδ_gamma hval_total
  refine ⟨θ, ?_, ?_⟩
  · have hidx : ((n + 1) + (3 * n + 4)) + 1 = 4 * n + 6 := by omega
    simpa [hidx] using hθ
  · rw [hmul, fl_householderScaleAlt_eq, hscale, hv0']
    calc
      householderScale hn0 x * (1 + θs) *
          (householderVectorAltFirst hn0 x * (1 + θv)) * (1 + δmul)
          =
            (householderScale hn0 x * householderVectorAltFirst hn0 x) *
              (((1 + θs) * (1 + θv)) * (1 + δmul)) := by ring
      _ =
            (householderScale hn0 x * householderVectorAltFirst hn0 x) *
              ((1 + θsv) * (1 + δmul)) := by rw [hprod_sv]
      _ =
            (householderScale hn0 x * householderVectorAltFirst hn0 x) *
              (1 + θ) := by rw [hprod]

/-- **β error (Construction 2)**: `β̂ = β·(1+θ')`, `|θ'| ≤ γ_{8n+12}`, with the
    source formula `β = −1/(σ·v₁)`.

    Uses `fl_householderBetaAlt_denominator_relative_error` (`γ_{4n+6}`
    denominator perturbation) then `gamma_inv_mul_roundoff` for the reciprocal
    and the final rounded division, doubling the index to `γ_{2(4n+6)} =
    γ_{8n+12}`.  The rounded numerator is the exact constant `−1`, so the
    reciprocal is of the perturbed denominator alone.  Requires a nonzero tail
    so that the exact denominator `σ·v₁ < 0` is nonzero. -/
theorem fl_householderBetaAlt_relative_error (fp : FPModel) {n : ℕ}
    (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (htail : householderTailSq hn0 x ≠ 0)
    (hval : gammaValid fp (8 * n + 12)) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp (8 * n + 12) ∧
      fl_householderBetaAlt fp hn0 x =
        householderBetaAltFromScale hn0 x * (1 + θ) := by
  let d : ℝ := householderScale hn0 x * householderVectorAltFirst hn0 x
  have hval_den : gammaValid fp (4 * n + 6) := gammaValid_mono fp (by omega) hval
  obtain ⟨θd, hθd, hden⟩ :=
    fl_householderBetaAlt_denominator_relative_error fp hn0 x hx hval_den
  -- exact denominator d < 0 (nonzero tail).
  have hd_neg : d < 0 := householderScale_mul_first_neg hn0 x hx htail
  have hd_ne : d ≠ 0 := ne_of_lt hd_neg
  -- γ_{4n+6} < 1 so 1 + θd > 0.
  have hval_2den : gammaValid fp (2 * (4 * n + 6)) :=
    gammaValid_mono fp (by omega) hval
  have hγ_lt : gamma fp (4 * n + 6) < 1 :=
    gamma_lt_one fp (4 * n + 6) hval_2den
  have hfactor_pos : 0 < 1 + θd := by
    linarith [neg_abs_le θd, hθd, hγ_lt]
  have hden' :
      fp.fl_mul (fl_householderScaleAlt fp hn0 x)
          (fl_householderVectorAlt fp hn0 x ⟨0, hn0⟩) =
        d * (1 + θd) := by simpa [d] using hden
  have hden_hat_ne :
      fp.fl_mul (fl_householderScaleAlt fp hn0 x)
          (fl_householderVectorAlt fp hn0 x ⟨0, hn0⟩) ≠ 0 := by
    rw [hden']; exact mul_ne_zero hd_ne (ne_of_gt hfactor_pos)
  -- rounded division −1 / den̂.
  obtain ⟨δdiv, hδdiv, hdiv⟩ :=
    fp.model_div (-1)
      (fp.fl_mul (fl_householderScaleAlt fp hn0 x)
        (fl_householderVectorAlt fp hn0 x ⟨0, hn0⟩)) hden_hat_ne
  -- reciprocal collapse.
  obtain ⟨θ, hθ, hrecip⟩ :=
    gamma_inv_mul_roundoff fp (4 * n + 6) θd δdiv (by omega)
      hθd hδdiv hfactor_pos hval_2den
  refine ⟨θ, ?_, ?_⟩
  · have hidx : 2 * (4 * n + 6) = 8 * n + 12 := by omega
    simpa [hidx] using hθ
  · calc
      fl_householderBetaAlt fp hn0 x
          = (-1 / (d * (1 + θd))) * (1 + δdiv) := by
            unfold fl_householderBetaAlt
            simp only
            rw [hdiv, hden']
      _ = (-1 / d) * ((1 / (1 + θd)) * (1 + δdiv)) := by
            field_simp [hd_ne, hfactor_pos.ne']
      _ = (-1 / d) * (1 + θ) := by rw [hrecip]
      _ = householderBetaAltFromScale hn0 x * (1 + θ) := by
            simp [d, householderBetaAltFromScale]

/-- **Full Construction-2 error contract**
    (Higham, 2nd ed., §19.3, Lemma 19.1 / eq (19.2) (p. 358)).

    The rounded Construction-2 kernels satisfy the tail / first-entry / β
    backward-error contract.  The nonzero-tail hypothesis `htail` is the
    Construction-2 nondegeneracy condition (file header, scope note 1); the tail
    and first-entry clauses would hold from `x ≠ 0` alone, but β needs a nonzero
    tail for `vᵀv > 0`.  Proved constants: `γ_{3n+4}` (first entry), `γ_{8n+12}`
    (β); both in Higham's generic `γ̃` class (he does not pin the integer `c`). -/
theorem fl_householderConstruction2Error (fp : FPModel) {n : ℕ}
    (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (htail : householderTailSq hn0 x ≠ 0)
    (hval : gammaValid fp (8 * n + 12)) :
    HouseholderConstruction2Error fp hn0 x
      (fl_householderVectorAlt fp hn0 x)
      (fl_householderBetaAlt fp hn0 x) := by
  refine ⟨?tail, ?first, ?beta⟩
  · intro i hi
    exact fl_householderVectorAlt_tail_eq fp hn0 x i hi
  · exact fl_householderVectorAlt_zero_relative_error fp hn0 x hx
      (gammaValid_mono fp (by omega) hval)
  · exact fl_householderBetaAlt_relative_error fp hn0 x hx htail hval

/-- **Labeled wrapper — Lemma 19.1, Construction 2**
    (Higham, 2nd ed., §19.3, Lemma 19.1 / eq (19.2) (p. 358)).

    Companion to `H19_Lemma19_1_construction1_backward_error` in
    `Higham19Labels.lean`.  Together the two labeled wrappers now cover BOTH sign
    conventions of the printed Lemma 19.1: Construction 1 (eq (19.1), usual sign)
    and Construction 2 (eq (19.2), alternative sign, this theorem).  The printed
    Lemma 19.1 is thereby fully formalized for both constructions.

    Scope: the constants proved here are the honest Construction-2 indices
    `γ_{3n+4}` (first entry) and `γ_{8n+12}` (β), each an instance of Higham's
    generic `γ̃` class (he does not pin the integer constant `c`).  The β clause
    requires the nonzero-tail nondegeneracy hypothesis (see file header, scope
    note 1); the tail and first-entry clauses hold from `x ≠ 0` alone. -/
theorem H19_Lemma19_1_construction2_backward_error (fp : FPModel) {n : ℕ}
    (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (htail : householderTailSq hn0 x ≠ 0)
    (hval : gammaValid fp (8 * n + 12)) :
    HouseholderConstruction2Error fp hn0 x
      (fl_householderVectorAlt fp hn0 x)
      (fl_householderBetaAlt fp hn0 x) :=
  fl_householderConstruction2Error fp hn0 x hx htail hval

end NumStability
