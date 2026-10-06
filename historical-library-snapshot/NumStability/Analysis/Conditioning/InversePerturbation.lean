-- Analysis/Conditioning/InversePerturbation.lean
--
-- Inverse perturbation and condition-number bounds.

import NumStability.Analysis.Asymptotics.Bounds
import NumStability.Analysis.Conditioning.DistanceToSingularity

/-!
# Inverse perturbation and conditioning

Develops inverse-stability estimates, condition-number formulations, and
finite-family perturbation bounds from subordinate norm hypotheses.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Exact first-order inverse perturbation identity in the local map model.
    If `S` is a left inverse of `A` and `B` is a right inverse of `A + Δ`,
    then
    `B - S = -S Δ S + S Δ S Δ B`.

    This is the algebraic resolvent expansion recommended by the GPT-5.5 Pro
    blocker consultation for turning the checked linearized inverse-condition
    value into the nonlinear perturbation-limit theorem. -/
theorem inversePerturbation_firstOrder_remainder_identity
    {n : ℕ} {A S Δ B : ComplexVectorMap n n}
    (hSlin : IsComplexVectorMapLinear S)
    (hΔlin : IsComplexVectorMapLinear Δ)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A Δ (B x) = x) :
    complexVectorMapSub B S =
      complexVectorMapAdd
        (complexVectorMapNeg
          (complexVectorMapComp S (complexVectorMapComp Δ S)))
        (complexVectorMapComp S
          (complexVectorMapComp Δ
            (complexVectorMapComp S (complexVectorMapComp Δ B)))) := by
  funext x
  have hmain : complexVecAdd (B x) (S (Δ (B x))) = S x := by
    calc
      complexVecAdd (B x) (S (Δ (B x))) =
          complexVecAdd (S (A (B x))) (S (Δ (B x))) := by
            rw [hS_left (B x)]
      _ = S (complexVecAdd (A (B x)) (Δ (B x))) := by
            exact (hSlin.map_add (A (B x)) (Δ (B x))).symm
      _ = S (complexVectorMapAdd A Δ (B x)) := by
            rfl
      _ = S x := by
            rw [hB_right x]
  have hB_decomp :
      B x = complexVecAdd (S x) (complexVecSMul (-1 : ℂ) (S (Δ (B x)))) := by
    ext i
    have hcoord : (B x) i + (S (Δ (B x))) i = (S x) i := by
      simpa [complexVecAdd] using congrFun hmain i
    calc
      (B x) i = (S x) i - (S (Δ (B x))) i := by
        exact eq_sub_of_add_eq hcoord
      _ = (complexVecAdd (S x) (complexVecSMul (-1 : ℂ) (S (Δ (B x))))) i := by
        simp [complexVecAdd, complexVecSMul]
        ring
  have hDelta_decomp :
      Δ (B x) =
        complexVecAdd (Δ (S x))
          (complexVecSMul (-1 : ℂ) (Δ (S (Δ (B x))))) := by
    calc
      Δ (B x) =
          Δ (complexVecAdd (S x)
            (complexVecSMul (-1 : ℂ) (S (Δ (B x))))) := by
            exact congrArg Δ hB_decomp
      _ = complexVecAdd (Δ (S x))
            (Δ (complexVecSMul (-1 : ℂ) (S (Δ (B x))))) := by
            exact hΔlin.map_add (S x)
              (complexVecSMul (-1 : ℂ) (S (Δ (B x))))
      _ = complexVecAdd (Δ (S x))
            (complexVecSMul (-1 : ℂ) (Δ (S (Δ (B x))))) := by
            rw [hΔlin.map_smul (-1 : ℂ) (S (Δ (B x)))]
  have hSDelta_decomp :
      S (Δ (B x)) =
        complexVecAdd (S (Δ (S x)))
          (complexVecSMul (-1 : ℂ) (S (Δ (S (Δ (B x)))))) := by
    calc
      S (Δ (B x)) =
          S (complexVecAdd (Δ (S x))
            (complexVecSMul (-1 : ℂ) (Δ (S (Δ (B x)))))) := by
            exact congrArg S hDelta_decomp
      _ = complexVecAdd (S (Δ (S x)))
            (S (complexVecSMul (-1 : ℂ) (Δ (S (Δ (B x)))))) := by
            exact hSlin.map_add (Δ (S x))
              (complexVecSMul (-1 : ℂ) (Δ (S (Δ (B x)))))
      _ = complexVecAdd (S (Δ (S x)))
            (complexVecSMul (-1 : ℂ) (S (Δ (S (Δ (B x)))))) := by
            rw [hSlin.map_smul (-1 : ℂ) (Δ (S (Δ (B x))))]
  ext i
  have hmain_i : (B x) i + (S (Δ (B x))) i = (S x) i := by
    simpa [complexVecAdd] using congrFun hmain i
  have hsd_i :
      (S (Δ (B x))) i =
        (S (Δ (S x))) i + -1 * (S (Δ (S (Δ (B x))))) i := by
    simpa [complexVecAdd, complexVecSMul] using congrFun hSDelta_decomp i
  simp [complexVectorMapSub, complexVectorMapAdd, complexVectorMapNeg,
    complexVectorMapSMul, complexVectorMapComp, complexVecAdd, complexVecSMul]
  calc
    (B x) i + -(S x) i = -(S (Δ (B x))) i := by
      have hb : (B x) i = (S x) i - (S (Δ (B x))) i :=
        eq_sub_of_add_eq hmain_i
      rw [hb]
      ring
    _ = -(S (Δ (S x))) i + (S (Δ (S (Δ (B x))))) i := by
      rw [hsd_i]
      ring

/-- Bound for the nonlinear remainder term in the exact inverse perturbation
    identity. If `S`, `Δ`, and the perturbed inverse `B` have local mixed
    subordinate upper bounds `s`, `d`, and `b`, then
    `S Δ S Δ B` has bound `s^2 d^2 b`. -/
theorem inversePerturbation_remainder_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {S Δ B : ComplexVectorMap n n}
    {s d b : ℝ} (hs0 : 0 ≤ s) (hd0 : 0 ≤ d)
    (hS : MixedSubordinateBound νβ να S s)
    (hΔ : MixedSubordinateBound να νβ Δ d)
    (hB : MixedSubordinateBound νβ να B b) :
    MixedSubordinateBound νβ να
      (complexVectorMapComp S
        (complexVectorMapComp Δ
          (complexVectorMapComp S (complexVectorMapComp Δ B))))
      (s ^ 2 * d ^ 2 * b) := by
  have hΔB : MixedSubordinateBound νβ νβ
      (complexVectorMapComp Δ B) (d * b) :=
    mixedSubordinateBound_comp hd0 hΔ hB
  have hSΔB : MixedSubordinateBound νβ να
      (complexVectorMapComp S (complexVectorMapComp Δ B)) (s * (d * b)) :=
    mixedSubordinateBound_comp hs0 hS hΔB
  have hΔSΔB : MixedSubordinateBound νβ νβ
      (complexVectorMapComp Δ
        (complexVectorMapComp S (complexVectorMapComp Δ B)))
      (d * (s * (d * b))) :=
    mixedSubordinateBound_comp hd0 hΔ hSΔB
  have hSΔSΔB : MixedSubordinateBound νβ να
      (complexVectorMapComp S
        (complexVectorMapComp Δ
          (complexVectorMapComp S (complexVectorMapComp Δ B))))
      (s * (d * (s * (d * b)))) :=
    mixedSubordinateBound_comp hs0 hS hΔSΔB
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hSΔSΔB

/-- Rearranged exact perturbation identity: after adding the linearized term
    `S Δ S` to `B - S`, the remaining error is exactly `S Δ S Δ B`. -/
theorem inversePerturbation_firstOrder_error_identity
    {n : ℕ} {A S Δ B : ComplexVectorMap n n}
    (hSlin : IsComplexVectorMapLinear S)
    (hΔlin : IsComplexVectorMapLinear Δ)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A Δ (B x) = x) :
    complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp Δ S)) =
      complexVectorMapComp S
        (complexVectorMapComp Δ
          (complexVectorMapComp S (complexVectorMapComp Δ B))) := by
  have hid :=
    inversePerturbation_firstOrder_remainder_identity
      hSlin hΔlin hS_left hB_right
  funext x
  change complexVecAdd ((complexVectorMapSub B S) x)
      ((complexVectorMapComp S (complexVectorMapComp Δ S)) x) =
    (complexVectorMapComp S
      (complexVectorMapComp Δ
        (complexVectorMapComp S (complexVectorMapComp Δ B)))) x
  rw [congrFun hid x]
  ext i
  simp [complexVectorMapAdd, complexVectorMapNeg, complexVectorMapSMul,
    complexVectorMapComp, complexVecAdd, complexVecSMul]

/-- Bound for the first-order inverse linearization error. Under the inverse
    hypotheses, `(B - S) + S Δ S` is exactly the quadratic remainder and hence
    has bound `s^2 d^2 b`. -/
theorem inversePerturbation_firstOrder_error_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A S Δ B : ComplexVectorMap n n}
    {s d b : ℝ} (hSlin : IsComplexVectorMapLinear S)
    (hΔlin : IsComplexVectorMapLinear Δ)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A Δ (B x) = x)
    (hs0 : 0 ≤ s) (hd0 : 0 ≤ d)
    (hS : MixedSubordinateBound νβ να S s)
    (hΔ : MixedSubordinateBound να νβ Δ d)
    (hB : MixedSubordinateBound νβ να B b) :
    MixedSubordinateBound νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp Δ S)))
      (s ^ 2 * d ^ 2 * b) := by
  rw [inversePerturbation_firstOrder_error_identity
    hSlin hΔlin hS_left hB_right]
  exact inversePerturbation_remainder_bound hs0 hd0 hS hΔ hB

/-- Least-value form of the first-order inverse linearization error bound:
    the local mixed subordinate value of `(B - S) + S Δ S` is at most the
    quadratic remainder scale `s^2 d^2 b`. -/
theorem inversePerturbation_firstOrder_error_value_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S Δ B : ComplexVectorMap n n}
    {s d b c : ℝ} (hSlin : IsComplexVectorMapLinear S)
    (hΔlin : IsComplexVectorMapLinear Δ)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A Δ (B x) = x)
    (hs0 : 0 ≤ s) (hd0 : 0 ≤ d)
    (hS : MixedSubordinateBound νβ να S s)
    (hΔ : MixedSubordinateBound να νβ Δ d)
    (hB : MixedSubordinateBound νβ να B b)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp Δ S))) c) :
    c ≤ s ^ 2 * d ^ 2 * b :=
  herr.2 (s ^ 2 * d ^ 2 * b)
    (inversePerturbation_firstOrder_error_bound
      hSlin hΔlin hS_left hB_right hs0 hd0 hS hΔ hB)

/-- Normalized first-order inverse linearization error bound. Dividing the
    quadratic error estimate by a positive perturbation size `d` leaves an
    `O(d)` upper bound, the local form needed for the eventual perturbation
    limit squeeze in Theorem 6.4. -/
theorem inversePerturbation_firstOrder_error_ratio_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S Δ B : ComplexVectorMap n n}
    {s d b c : ℝ} (hSlin : IsComplexVectorMapLinear S)
    (hΔlin : IsComplexVectorMapLinear Δ)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A Δ (B x) = x)
    (hs0 : 0 ≤ s) (hdpos : 0 < d)
    (hS : MixedSubordinateBound νβ να S s)
    (hΔ : MixedSubordinateBound να νβ Δ d)
    (hB : MixedSubordinateBound νβ να B b)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp Δ S))) c) :
    c / d ≤ s ^ 2 * d * b := by
  have hle : c ≤ s ^ 2 * d ^ 2 * b :=
    inversePerturbation_firstOrder_error_value_le
      hSlin hΔlin hS_left hB_right hs0 (le_of_lt hdpos) hS hΔ hB herr
  calc
    c / d ≤ (s ^ 2 * d ^ 2 * b) / d :=
      div_le_div_of_nonneg_right hle (le_of_lt hdpos)
    _ = s ^ 2 * d * b := by
      field_simp [ne_of_gt hdpos]

/-- Upper bound for the full nonlinear inverse difference `B - S`.  It is the
    sum of the sharp linearized term `S Δ S`, bounded by `s^2 d`, and the
    quadratic resolvent remainder, bounded by `s^2 d^2 b`. -/
theorem inversePerturbation_difference_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {s d b : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hs0 : 0 ≤ s) (hd0 : 0 ≤ d)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : MixedSubordinateBound να νβ D d)
    (hB : MixedSubordinateBound νβ να B b) :
    MixedSubordinateBound νβ να (complexVectorMapSub B S)
      (s ^ 2 * d + s ^ 2 * d ^ 2 * b) := by
  have hDS : MixedSubordinateBound νβ νβ
      (complexVectorMapComp D S) (d * s) :=
    mixedSubordinateBound_comp hd0 hD hS
  have hSDS : MixedSubordinateBound νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d) := by
    have hraw : MixedSubordinateBound νβ να
        (complexVectorMapComp S (complexVectorMapComp D S)) (s * (d * s)) :=
      mixedSubordinateBound_comp hs0 hS hDS
    simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hraw
  have hneg : MixedSubordinateBound νβ να
      (complexVectorMapNeg
        (complexVectorMapComp S (complexVectorMapComp D S))) (s ^ 2 * d) :=
    mixedSubordinateBound_neg hα hSDS
  have hrem : MixedSubordinateBound νβ να
      (complexVectorMapComp S
        (complexVectorMapComp D
          (complexVectorMapComp S (complexVectorMapComp D B))))
      (s ^ 2 * d ^ 2 * b) :=
    inversePerturbation_remainder_bound hs0 hd0 hS hD hB
  have hid :=
    inversePerturbation_firstOrder_remainder_identity
      hSlin hDlin hS_left hB_right
  rw [hid]
  exact mixedSubordinateBound_add hα hneg hrem

/-- Least-value form of the nonlinear inverse-difference bound. -/
theorem inversePerturbation_difference_value_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {s d b e : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hs0 : 0 ≤ s) (hd0 : 0 ≤ d)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : MixedSubordinateBound να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e) :
    e ≤ s ^ 2 * d + s ^ 2 * d ^ 2 * b :=
  hdiff.2 (s ^ 2 * d + s ^ 2 * d ^ 2 * b)
    (inversePerturbation_difference_bound
      hα hSlin hDlin hS_left hB_right hs0 hd0 hS hD hB)

/-- Normalized upper bound for the full inverse-difference ratio.  After
    division by the positive perturbation size, the nonlinear ratio is bounded
    by the derivative scale `s^2` plus the vanishing remainder `s^2 d b`. -/
theorem inversePerturbation_difference_ratio_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {s d b e : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hs0 : 0 ≤ s) (hdpos : 0 < d)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : MixedSubordinateBound να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e) :
    e / d ≤ s ^ 2 + s ^ 2 * d * b := by
  have hle : e ≤ s ^ 2 * d + s ^ 2 * d ^ 2 * b :=
    inversePerturbation_difference_value_le
      hα hSlin hDlin hS_left hB_right hs0 (le_of_lt hdpos) hS hD hB hdiff
  calc
    e / d ≤ (s ^ 2 * d + s ^ 2 * d ^ 2 * b) / d :=
      div_le_div_of_nonneg_right hle (le_of_lt hdpos)
    _ = s ^ 2 + s ^ 2 * d * b := by
      field_simp [ne_of_gt hdpos]

/-- Source-scaled nonlinear amplification upper bound.  This is the direct
    local estimate needed for the future `sSup` squeeze in Theorem 6.4:
    the relative inverse-change ratio is at most the product condition number
    `a*s`, up to the vanishing factor `a*s*d*b`. -/
theorem inversePerturbation_relative_difference_ratio_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s d b e : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : MixedSubordinateBound να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e) :
    (e / s) / (d / a) ≤ a * s * (1 + d * b) := by
  have hratio : e / d ≤ s ^ 2 + s ^ 2 * d * b :=
    inversePerturbation_difference_ratio_le
      hα hSlin hDlin hS_left hB_right (le_of_lt hspos) hdpos hS hD hB hdiff
  have hscale_nonneg : 0 ≤ a / s :=
    div_nonneg (le_of_lt hapos) (le_of_lt hspos)
  calc
    (e / s) / (d / a) = (a / s) * (e / d) := by
      field_simp [ne_of_gt hapos, ne_of_gt hspos, ne_of_gt hdpos]
    _ ≤ (a / s) * (s ^ 2 + s ^ 2 * d * b) :=
      mul_le_mul_of_nonneg_left hratio hscale_nonneg
    _ = a * s * (1 + d * b) := by
      field_simp [ne_of_gt hspos]

/-- Kernel-zero form of the small perturbation argument.  If `S A = I`,
    `S` has mixed bound `s`, `D` has mixed bound `d`, and `s*d < 1`, then
    the perturbed map `A + D` has no nonzero kernel vector. -/
theorem inversePerturbation_small_add_eq_zero_imp_eq_zero
    {n : ℕ} {nuA nuB : CVec n → ℝ} {A S D : ComplexVectorMap n n}
    {s d : ℝ} (hnorm : IsComplexVectorNorm nuA)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hs0 : 0 ≤ s) (hsmall : s * d < 1)
    (hS : MixedSubordinateBound nuB nuA S s)
    (hD : MixedSubordinateBound nuA nuB D d)
    {x : CVec n} (hx : complexVectorMapAdd A D x = 0) :
    x = 0 := by
  have hA_eq_negD : A x = complexVecSMul (-1 : ℂ) (D x) := by
    ext i
    have hcoord := congrFun hx i
    simp [complexVectorMapAdd, complexVecAdd, complexVecSMul] at hcoord ⊢
    exact eq_neg_of_add_eq_zero_left hcoord
  have hx_eq : x = complexVecSMul (-1 : ℂ) (S (D x)) := by
    calc
      x = S (A x) := (hS_left x).symm
      _ = S (complexVecSMul (-1 : ℂ) (D x)) := by rw [hA_eq_negD]
      _ = complexVecSMul (-1 : ℂ) (S (D x)) := by
            rw [hSlin.map_smul (-1 : ℂ) (D x)]
  have hneg :
      nuA (complexVecSMul (-1 : ℂ) (S (D x))) = nuA (S (D x)) := by
    rw [hnorm.smul]
    norm_num
  have hcontract : nuA x ≤ s * d * nuA x := by
    calc
      nuA x = nuA (complexVecSMul (-1 : ℂ) (S (D x))) :=
            congrArg nuA hx_eq
      _ = nuA (S (D x)) := hneg
      _ ≤ s * nuB (D x) := hS (D x)
      _ ≤ s * (d * nuA x) := mul_le_mul_of_nonneg_left (hD x) hs0
      _ = s * d * nuA x := by ring
  have hxnorm : nuA x = 0 := by
    have hnonneg := hnorm.nonneg x
    nlinarith
  exact (hnorm.eq_zero_iff x).mp hxnorm

/-- Small perturbations of a map with a bounded left inverse are nonsingular in
    the local kernel-vector sense. -/
theorem inversePerturbation_small_add_not_singular
    {n : ℕ} {nuA nuB : CVec n → ℝ} {A S D : ComplexVectorMap n n}
    {s d : ℝ} (hnorm : IsComplexVectorNorm nuA)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hs0 : 0 ≤ s) (hsmall : s * d < 1)
    (hS : MixedSubordinateBound nuB nuA S s)
    (hD : MixedSubordinateBound nuA nuB D d) :
    ¬ IsSingularComplexVectorMap (complexVectorMapAdd A D) := by
  intro hsing
  obtain ⟨x, hxne, hxzero⟩ := hsing
  exact hxne (inversePerturbation_small_add_eq_zero_imp_eq_zero
    hnorm hSlin hS_left hs0 hsmall hS hD hxzero)

/-- Injective form of the small perturbation argument for linear perturbations.
    This is the finite-dimensional algebraic bridge needed before extracting
    right-inverse witnesses for `A + D`. -/
theorem inversePerturbation_small_add_injective
    {n : ℕ} {nuA nuB : CVec n → ℝ} {A S D : ComplexVectorMap n n}
    {s d : ℝ} (hnorm : IsComplexVectorNorm nuA)
    (hAlin : IsComplexVectorMapLinear A)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hs0 : 0 ≤ s) (hsmall : s * d < 1)
    (hS : MixedSubordinateBound nuB nuA S s)
    (hD : MixedSubordinateBound nuA nuB D d) :
    Function.Injective (complexVectorMapAdd A D) := by
  let T : ComplexVectorMap n n := complexVectorMapAdd A D
  change Function.Injective T
  have hTlin : IsComplexVectorMapLinear T := by
    simpa [T] using complexVectorMapAdd_linear hAlin hDlin
  intro x y hxy
  let z : CVec n := complexVecAdd x (complexVecSMul (-1 : ℂ) y)
  have hz_apply :
      T z = complexVecAdd (T x) (complexVecSMul (-1 : ℂ) (T y)) := by
    calc
      T z = T (complexVecAdd x (complexVecSMul (-1 : ℂ) y)) := rfl
      _ = complexVecAdd (T x) (T (complexVecSMul (-1 : ℂ) y)) :=
            hTlin.map_add x (complexVecSMul (-1 : ℂ) y)
      _ = complexVecAdd (T x) (complexVecSMul (-1 : ℂ) (T y)) := by
            rw [hTlin.map_smul (-1 : ℂ) y]
  have hz0 : T z = 0 := by
    rw [hz_apply]
    ext i
    have hcoord := congrFun hxy i
    have hsub : (T x) i - (T y) i = 0 := sub_eq_zero.mpr hcoord
    simpa [complexVecAdd, complexVecSMul, sub_eq_add_neg] using hsub
  have hz_eq_zero : z = 0 :=
    inversePerturbation_small_add_eq_zero_imp_eq_zero
      hnorm hSlin hS_left hs0 hsmall hS hD (by simpa [T] using hz0)
  ext i
  have hzi := congrFun hz_eq_zero i
  have hsub : x i - y i = 0 := by
    simpa [z, complexVecAdd, complexVecSMul, sub_eq_add_neg] using hzi
  exact sub_eq_zero.mp hsub

/-- Resolvent-style perturbed-inverse bound. If `S` is a left inverse of `A`,
    `B` is a right inverse of `A + D`, `S` has mixed bound `s`, `D` has mixed
    bound `d`, and `s*d < 1`, then `B` has mixed bound
    `s / (1 - s*d)`.

    This supplies the concrete inverse-bound hypothesis needed by the later
    Theorem 6.4 fixed-scale convergence shell; it still assumes a right-inverse
    witness `B` for the perturbed map rather than proving existence of `B`. -/
theorem inversePerturbation_perturbedInverse_bound_of_small
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {s d : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hs0 : 0 ≤ s) (hsd : s * d < 1)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : MixedSubordinateBound να νβ D d) :
    MixedSubordinateBound νβ να B (s / (1 - s * d)) := by
  intro x
  have hmain : complexVecAdd (B x) (S (D (B x))) = S x := by
    calc
      complexVecAdd (B x) (S (D (B x))) =
          complexVecAdd (S (A (B x))) (S (D (B x))) := by
            rw [hS_left (B x)]
      _ = S (complexVecAdd (A (B x)) (D (B x))) := by
            exact (hSlin.map_add (A (B x)) (D (B x))).symm
      _ = S (complexVectorMapAdd A D (B x)) := by
            rfl
      _ = S x := by
            rw [hB_right x]
  have hB_decomp :
      B x = complexVecAdd (S x)
        (complexVecSMul (-1 : ℂ) (S (D (B x)))) := by
    ext i
    have hcoord : (B x) i + (S (D (B x))) i = (S x) i := by
      simpa [complexVecAdd] using congrFun hmain i
    calc
      (B x) i = (S x) i - (S (D (B x))) i := by
        exact eq_sub_of_add_eq hcoord
      _ = (complexVecAdd (S x)
          (complexVecSMul (-1 : ℂ) (S (D (B x))))) i := by
        simp [complexVecAdd, complexVecSMul]
        ring
  have hneg :
      να (complexVecSMul (-1 : ℂ) (S (D (B x)))) =
        να (S (D (B x))) := by
    rw [hα.smul]
    norm_num
  have hpre :
      να (B x) ≤ s * νβ x + s * d * να (B x) := by
    calc
      να (B x) =
          να (complexVecAdd (S x)
            (complexVecSMul (-1 : ℂ) (S (D (B x))))) := by
            exact congrArg να hB_decomp
      _ ≤ να (S x) + να (complexVecSMul (-1 : ℂ) (S (D (B x)))) :=
            hα.add_le (S x) (complexVecSMul (-1 : ℂ) (S (D (B x))))
      _ = να (S x) + να (S (D (B x))) := by
            rw [hneg]
      _ ≤ s * νβ x + s * νβ (D (B x)) :=
            add_le_add (hS x) (hS (D (B x)))
      _ ≤ s * νβ x + s * (d * να (B x)) := by
            exact add_le_add (le_refl (s * νβ x))
              (mul_le_mul_of_nonneg_left (hD (B x)) hs0)
      _ = s * νβ x + s * d * να (B x) := by ring
  have hden_pos : 0 < 1 - s * d := by linarith
  have hmul : (1 - s * d) * να (B x) ≤ s * νβ x := by
    nlinarith [hpre]
  have hdiv : να (B x) ≤ (s * νβ x) / (1 - s * d) :=
    (le_div_iff₀ hden_pos).mpr (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  calc
    να (B x) ≤ (s * νβ x) / (1 - s * d) := hdiv
    _ = (s / (1 - s * d)) * νβ x := by ring

/-- Small perturbations of a map with a bounded left inverse admit an actual
    source-facing right inverse.  The proof converts `A + D` to a Mathlib
    linear endomorphism, uses finite-dimensional injective-implies-invertible,
    and takes the inverse linear equivalence as the witness `B`.

    This removes the single-map existence gap for the perturbed right-inverse
    witnesses used by the Theorem 6.4 resolvent route. -/
theorem exists_inversePerturbation_perturbedRightInverse_of_small
    {n : ℕ} {nuA nuB : CVec n → ℝ} {A S D : ComplexVectorMap n n}
    {s d : ℝ} (hnorm : IsComplexVectorNorm nuA)
    (hAlin : IsComplexVectorMapLinear A)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hs0 : 0 ≤ s) (hsmall : s * d < 1)
    (hS : MixedSubordinateBound nuB nuA S s)
    (hD : MixedSubordinateBound nuA nuB D d) :
    ∃ B : ComplexVectorMap n n,
      IsComplexVectorMapLinear B ∧
        (∀ x : CVec n, complexVectorMapAdd A D (B x) = x) ∧
          MixedSubordinateBound nuB nuA B (s / (1 - s * d)) := by
  let T : ComplexVectorMap n n := complexVectorMapAdd A D
  have hTlin : IsComplexVectorMapLinear T := by
    simpa [T] using complexVectorMapAdd_linear hAlin hDlin
  let L : CVec n →ₗ[ℂ] CVec n := complexVectorMapLinearMap T hTlin
  have hTinj : Function.Injective T :=
    inversePerturbation_small_add_injective hnorm hAlin hSlin hDlin hS_left
      hs0 hsmall hS hD
  have hLinj : Function.Injective L := by
    intro x y hxy
    exact hTinj hxy
  let E : CVec n ≃ₗ[ℂ] CVec n := LinearEquiv.ofInjectiveEndo L hLinj
  let B : ComplexVectorMap n n := fun x => E.symm x
  have hBlin : IsComplexVectorMapLinear B := by
    constructor
    · intro x y
      ext i
      change E.symm (x + y) i = (E.symm x + E.symm y) i
      exact congrFun ((E.symm : CVec n →ₗ[ℂ] CVec n).map_add x y) i
    · intro a x
      ext i
      change E.symm (a • x) i = (a • E.symm x) i
      exact congrFun ((E.symm : CVec n →ₗ[ℂ] CVec n).map_smul a x) i
  have hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x := by
    intro x
    change T (E.symm x) = x
    have h : E (E.symm x) = x := E.apply_symm_apply x
    change L (E.symm x) = x at h
    exact h
  have hB_bound : MixedSubordinateBound nuB nuA B (s / (1 - s * d)) :=
    inversePerturbation_perturbedInverse_bound_of_small hnorm hSlin hS_left
      hB_right hs0 hsmall hS hD
  exact ⟨B, hBlin, hB_right, hB_bound⟩

/-- A supplied right inverse of the small perturbed map is automatically
    linear.  The proof uses the same contraction identity as the resolvent
    bound: from `(A + D) B = I` and `S A = I`, each additivity or homogeneity
    defect `z` of `B` satisfies `z = -S(D z)`.  Since `||S||*||D|| < 1`, the
    defect has norm zero.

    This removes the separate linearity bookkeeping hypothesis for perturbed
    right-inverse witnesses in the Theorem 6.4 radius-limit route. -/
theorem inversePerturbation_perturbedRightInverse_linear_of_small
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {s d : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hs0 : 0 ≤ s) (hsd : s * d < 1)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : MixedSubordinateBound να νβ D d) :
    IsComplexVectorMapLinear B := by
  have hdecomp : ∀ x : CVec n,
      B x = complexVecAdd (S x)
        (complexVecSMul (-1 : ℂ) (S (D (B x)))) := by
    intro x
    have hmain : complexVecAdd (B x) (S (D (B x))) = S x := by
      calc
        complexVecAdd (B x) (S (D (B x))) =
            complexVecAdd (S (A (B x))) (S (D (B x))) := by
              rw [hS_left (B x)]
        _ = S (complexVecAdd (A (B x)) (D (B x))) := by
              exact (hSlin.map_add (A (B x)) (D (B x))).symm
        _ = S (complexVectorMapAdd A D (B x)) := by
              rfl
        _ = S x := by
              rw [hB_right x]
    ext i
    have hcoord : (B x) i + (S (D (B x))) i = (S x) i := by
      simpa [complexVecAdd] using congrFun hmain i
    calc
      (B x) i = (S x) i - (S (D (B x))) i := by
        exact eq_sub_of_add_eq hcoord
      _ = (complexVecAdd (S x)
          (complexVecSMul (-1 : ℂ) (S (D (B x))))) i := by
        simp [complexVecAdd, complexVecSMul]
        ring
  have hdefect_zero :
      ∀ z : CVec n, z = complexVecSMul (-1 : ℂ) (S (D z)) → z = 0 := by
    intro z hz
    have hneg :
        να (complexVecSMul (-1 : ℂ) (S (D z))) = να (S (D z)) := by
      rw [hα.smul]
      norm_num
    have hcontract : να z ≤ s * d * να z := by
      calc
        να z = να (complexVecSMul (-1 : ℂ) (S (D z))) := congrArg να hz
        _ = να (S (D z)) := hneg
        _ ≤ s * νβ (D z) := hS (D z)
        _ ≤ s * (d * να z) :=
              mul_le_mul_of_nonneg_left (hD z) hs0
        _ = s * d * να z := by ring
    have hz_norm : να z = 0 := by
      have hnonneg := hα.nonneg z
      nlinarith
    exact (hα.eq_zero_iff z).mp hz_norm
  refine ⟨?_, ?_⟩
  · intro x y
    let z : CVec n :=
      complexVecAdd (B (complexVecAdd x y))
        (complexVecSMul (-1 : ℂ) (complexVecAdd (B x) (B y)))
    have hz : z = complexVecSMul (-1 : ℂ) (S (D z)) := by
      ext i
      have hxy_i := congrFun (hdecomp (complexVecAdd x y)) i
      have hx_i := congrFun (hdecomp x) i
      have hy_i := congrFun (hdecomp y) i
      have hSxy_i := congrFun (hSlin.map_add x y) i
      have hDz_i :
          (S (D z)) i =
            (S (D (B (complexVecAdd x y)))) i -
              ((S (D (B x))) i + (S (D (B y))) i) := by
        simp [z, complexVecAdd, complexVecSMul, hDlin.map_add,
          hDlin.map_smul, hSlin.map_add, hSlin.map_smul, sub_eq_add_neg]
      simp [z, complexVecAdd, complexVecSMul] at hxy_i hx_i hy_i hSxy_i ⊢
      rw [hDz_i, hxy_i, hx_i, hy_i, hSxy_i]
      ring
    have hz0 : z = 0 := hdefect_zero z hz
    ext i
    have hzi := congrFun hz0 i
    have hsub :
        (B (complexVecAdd x y)) i - ((B x) i + (B y) i) = 0 := by
      simpa [z, complexVecAdd, complexVecSMul, sub_eq_add_neg] using hzi
    exact sub_eq_zero.mp hsub
  · intro a x
    let z : CVec n :=
      complexVecAdd (B (complexVecSMul a x))
        (complexVecSMul (-a) (B x))
    have hz : z = complexVecSMul (-1 : ℂ) (S (D z)) := by
      ext i
      have hax_i := congrFun (hdecomp (complexVecSMul a x)) i
      have hx_i := congrFun (hdecomp x) i
      have hSax_i := congrFun (hSlin.map_smul a x) i
      have hDz_i :
          (S (D z)) i =
            (S (D (B (complexVecSMul a x)))) i -
              a * (S (D (B x))) i := by
        simp [z, complexVecAdd, complexVecSMul, hDlin.map_add,
          hDlin.map_smul, hSlin.map_add, hSlin.map_smul, sub_eq_add_neg]
      simp [z, complexVecAdd, complexVecSMul] at hax_i hx_i hSax_i ⊢
      rw [hDz_i, hax_i, hx_i, hSax_i]
      ring
    have hz0 : z = 0 := hdefect_zero z hz
    ext i
    have hzi := congrFun hz0 i
    have hsub :
        (B (complexVecSMul a x)) i - a * (B x) i = 0 := by
      simpa [z, complexVecAdd, complexVecSMul, sub_eq_add_neg] using hzi
    exact sub_eq_zero.mp hsub

/-- Reverse-triangle lower helper for the inverse perturbation proof.  If the
    first-order error `(B - S) + S D S` has value `c`, the full difference
    `B - S` has value `e`, and the linearized sandwich `S D S` has value `l`,
    then `l <= c + e`. -/
theorem inversePerturbation_linearized_value_le_difference_add_error
    {n : ℕ} {να νβ : CVec n → ℝ} {S D B : ComplexVectorMap n n}
    {l e c : ℝ} (hα : IsComplexVectorNorm να)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) l)
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c) :
    l ≤ c + e :=
  mixedSubordinateNormValue_right_le_add_of_add_eq
    hα rfl herr hdiff hlin

/-- Lower bound for the full inverse-difference value, once the linearized
    sandwich has the sharp value `s^2 d`.  The quadratic resolvent error can
    only reduce the nonlinear difference by at most `s^2 d^2 b`. -/
theorem inversePerturbation_difference_value_lower_le_of_linearized
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {s d b e c : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hs0 : 0 ≤ s) (hd0 : 0 ≤ d)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : MixedSubordinateBound να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d))
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c) :
    s ^ 2 * d - s ^ 2 * d ^ 2 * b ≤ e := by
  have htri : s ^ 2 * d ≤ c + e :=
    inversePerturbation_linearized_value_le_difference_add_error hα hlin hdiff herr
  have herr_le : c ≤ s ^ 2 * d ^ 2 * b :=
    inversePerturbation_firstOrder_error_value_le
      hSlin hDlin hS_left hB_right hs0 hd0 hS hD hB herr
  linarith

/-- Normalized lower bound for the nonlinear inverse-difference ratio.  This is
    the lower half of the local squeeze corresponding to the checked upper
    estimate `e / d <= s^2 + s^2 d b`. -/
theorem inversePerturbation_difference_ratio_lower_le_of_linearized
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {s d b e c : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hs0 : 0 ≤ s) (hdpos : 0 < d)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : MixedSubordinateBound να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d))
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c) :
    s ^ 2 - s ^ 2 * d * b ≤ e / d := by
  have hlow :
      s ^ 2 * d - s ^ 2 * d ^ 2 * b ≤ e :=
    inversePerturbation_difference_value_lower_le_of_linearized
      hα hSlin hDlin hS_left hB_right hs0 (le_of_lt hdpos) hS hD hB hlin hdiff herr
  have hdiv :
      (s ^ 2 * d - s ^ 2 * d ^ 2 * b) / d ≤ e / d :=
    div_le_div_of_nonneg_right hlow (le_of_lt hdpos)
  calc
    s ^ 2 - s ^ 2 * d * b =
        (s ^ 2 * d - s ^ 2 * d ^ 2 * b) / d := by
      field_simp [ne_of_gt hdpos]
    _ ≤ e / d := hdiv

/-- Source-scaled lower bound for the nonlinear relative inverse amplification.
    Together with `inversePerturbation_relative_difference_ratio_le`, this
    gives the local two-sided squeeze around the product condition number
    `a*s`, up to a vanishing factor. -/
theorem inversePerturbation_relative_difference_ratio_lower_le_of_linearized
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s d b e c : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : MixedSubordinateBound να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d))
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c) :
    a * s * (1 - d * b) ≤ (e / s) / (d / a) := by
  have hratio : s ^ 2 - s ^ 2 * d * b ≤ e / d :=
    inversePerturbation_difference_ratio_lower_le_of_linearized
      hα hSlin hDlin hS_left hB_right (le_of_lt hspos) hdpos hS hD hB hlin hdiff herr
  have hscale_nonneg : 0 ≤ a / s :=
    div_nonneg (le_of_lt hapos) (le_of_lt hspos)
  calc
    a * s * (1 - d * b) = (a / s) * (s ^ 2 - s ^ 2 * d * b) := by
      field_simp [ne_of_gt hspos]
    _ ≤ (a / s) * (e / d) :=
      mul_le_mul_of_nonneg_left hratio hscale_nonneg
    _ = (e / s) / (d / a) := by
      field_simp [ne_of_gt hapos, ne_of_gt hspos, ne_of_gt hdpos]

/-- Candidate nonlinear relative inverse-amplification values at a fixed
    perturbation scale `d` and a supplied perturbed-inverse bound `b`.
    An element is the source-scaled ratio
    `(||B - S|| / s) / (d / a)`, where `B` is a right inverse of `A + D`.

    This is a local predicate-level bridge toward the `sSup`/limit part of
    Theorem 6.4; it deliberately keeps the small-perturbation inverse-existence
    and limit machinery outside the definition. -/
def MixedInverseRelativeAmplificationAtScaleSet
    {n : ℕ} (να νβ : CVec n → ℝ) (A S : ComplexVectorMap n n)
    (a s d b : ℝ) : Set ℝ :=
  {q | ∃ D B : ComplexVectorMap n n, ∃ e : ℝ,
    IsComplexVectorMapLinear D ∧
      IsMixedSubordinateNormValue να νβ D d ∧
        MixedSubordinateBound νβ να B b ∧
          (∀ x : CVec n, complexVectorMapAdd A D (B x) = x) ∧
            IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e ∧
              q = (e / s) / (d / a)}

/-- Predicate-level supremum for the fixed-scale nonlinear inverse-amplification
    set.  This local least-upper-bound form avoids committing the Chapter 6 API
    to a concrete `sSup` function before the perturbation radius and invertible
    feasible set are finalized. -/
def IsSupMixedInverseRelativeAmplificationAtScale
    {n : ℕ} (να νβ : CVec n → ℝ) (A S : ComplexVectorMap n n)
    (a s d b Q : ℝ) : Prop :=
  (∀ q : ℝ,
    q ∈ MixedInverseRelativeAmplificationAtScaleSet να νβ A S a s d b → q ≤ Q) ∧
    ∀ U : ℝ,
      (∀ q : ℝ,
        q ∈ MixedInverseRelativeAmplificationAtScaleSet να νβ A S a s d b → q ≤ U) →
        Q ≤ U

/-- Membership constructor for the fixed-scale nonlinear inverse-amplification
    set. -/
theorem mixedInverseRelativeAmplificationAtScale_mem
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s d b e : ℝ}
    (hDlin : IsComplexVectorMapLinear D)
    (hD : IsMixedSubordinateNormValue να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e) :
    (e / s) / (d / a) ∈
      MixedInverseRelativeAmplificationAtScaleSet να νβ A S a s d b := by
  exact ⟨D, B, e, hDlin, hD, hB, hB_right, hdiff, rfl⟩

/-- Every fixed-scale nonlinear inverse-amplification value is bounded above by
    the product condition-number scale times `1 + d*b`. -/
theorem mixedInverseRelativeAmplificationAtScale_value_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s d b q : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hS : MixedSubordinateBound νβ να S s)
    (hq : q ∈ MixedInverseRelativeAmplificationAtScaleSet να νβ A S a s d b) :
    q ≤ a * s * (1 + d * b) := by
  obtain ⟨D, B, e, hDlin, hD, hB, hB_right, hdiff, hqeq⟩ := hq
  rw [hqeq]
  exact inversePerturbation_relative_difference_ratio_le
    hα hSlin hDlin hS_left hB_right hapos hspos hdpos hS hD.1 hB hdiff

/-- The predicate-level supremum of the fixed-scale nonlinear amplification set
    is bounded above by the product condition-number scale times `1 + d*b`. -/
theorem mixedInverseRelativeAmplificationAtScale_sup_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s d b Q : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hS : MixedSubordinateBound νβ να S s)
    (hQ : IsSupMixedInverseRelativeAmplificationAtScale να νβ A S a s d b Q) :
    Q ≤ a * s * (1 + d * b) := by
  exact hQ.2 (a * s * (1 + d * b))
    (fun q hq =>
      mixedInverseRelativeAmplificationAtScale_value_le
        hα hSlin hS_left hapos hspos hdpos hS hq)

/-- A checked lower witness for the fixed-scale nonlinear amplification set:
    when the linearized sandwich has the sharp value `s^2*d`, the corresponding
    nonlinear ratio is at least `a*s*(1 - d*b)`. -/
theorem exists_mixedInverseRelativeAmplificationAtScale_lower_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s d b e c : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : IsMixedSubordinateNormValue να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d))
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c) :
    ∃ q : ℝ,
      q ∈ MixedInverseRelativeAmplificationAtScaleSet να νβ A S a s d b ∧
        a * s * (1 - d * b) ≤ q := by
  refine ⟨(e / s) / (d / a), ?_, ?_⟩
  · exact mixedInverseRelativeAmplificationAtScale_mem hDlin hD hB hB_right hdiff
  · exact inversePerturbation_relative_difference_ratio_lower_le_of_linearized
      hα hSlin hDlin hS_left hB_right hapos hspos hdpos hS hD.1 hB
      hlin hdiff herr

/-- Lower bound for any predicate-level supremum once a checked lower witness
    exists in the fixed-scale nonlinear amplification set. -/
theorem mixedInverseRelativeAmplificationAtScale_lower_le_sup_of_exists
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s d b Q L : ℝ}
    (hQ : IsSupMixedInverseRelativeAmplificationAtScale να νβ A S a s d b Q)
    (hL : ∃ q : ℝ,
      q ∈ MixedInverseRelativeAmplificationAtScaleSet να νβ A S a s d b ∧
        L ≤ q) :
    L ≤ Q := by
  obtain ⟨q, hqmem, hLq⟩ := hL
  exact hLq.trans (hQ.1 q hqmem)

/-- Fixed-scale predicate-level squeeze for the nonlinear inverse-amplification
    supremum.  This packages the upper estimate and the sharp lower witness
    into the local form needed before the final perturbation-limit theorem. -/
theorem mixedInverseRelativeAmplificationAtScale_sup_squeeze_of_linearized
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s d b e c Q : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : IsMixedSubordinateNormValue να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d))
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c)
    (hQ : IsSupMixedInverseRelativeAmplificationAtScale να νβ A S a s d b Q) :
    a * s * (1 - d * b) ≤ Q ∧ Q ≤ a * s * (1 + d * b) := by
  refine ⟨?_, ?_⟩
  · exact mixedInverseRelativeAmplificationAtScale_lower_le_sup_of_exists hQ
      (exists_mixedInverseRelativeAmplificationAtScale_lower_bound
        hα hSlin hDlin hS_left hB_right hapos hspos hdpos hS hD hB hlin hdiff herr)
  · exact mixedInverseRelativeAmplificationAtScale_sup_le
      hα hSlin hS_left hapos hspos hdpos hS hQ

/-- Quantitative closeness form of the fixed-scale inverse-amplification
    supremum squeeze.  Once a sharp linearized lower witness is available, the
    fixed-scale supremum differs from the product condition number `a*s` by at
    most the vanishing error scale `a*s*d*b`.

    This is a dependency for the eventual perturbation-radius `sSup`/limit
    theorem in Theorem 6.4, not the final source theorem itself. -/
theorem mixedInverseRelativeAmplificationAtScale_sup_abs_sub_condition_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s d b e c Q : ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : IsMixedSubordinateNormValue να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d))
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c)
    (hQ : IsSupMixedInverseRelativeAmplificationAtScale να νβ A S a s d b Q) :
    |Q - a * s| ≤ a * s * d * b := by
  have hb0 : 0 ≤ b :=
    mixedSubordinateBound_nonneg_of_nonempty hn hβ hα hB
  have hsq :=
    mixedInverseRelativeAmplificationAtScale_sup_squeeze_of_linearized
      hα hSlin hDlin hS_left hB_right hapos hspos hdpos hS hD hB hlin hdiff herr hQ
  have hlow : -(a * s * d * b) ≤ Q - a * s := by
    nlinarith [hsq.1]
  have hup : Q - a * s ≤ a * s * d * b := by
    nlinarith [hsq.2]
  exact abs_le.mpr ⟨hlow, hup⟩

/-- Epsilon-ready form of the fixed-scale closeness estimate: any external
    error budget dominating `a*s*d*b` also dominates the absolute deviation of
    the fixed-scale supremum from the product condition number. -/
theorem mixedInverseRelativeAmplificationAtScale_sup_abs_sub_condition_le_of_error_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s d b e c Q ε : ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : IsMixedSubordinateNormValue να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d))
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c)
    (hQ : IsSupMixedInverseRelativeAmplificationAtScale να νβ A S a s d b Q)
    (hε : a * s * d * b ≤ ε) :
    |Q - a * s| ≤ ε :=
  (mixedInverseRelativeAmplificationAtScale_sup_abs_sub_condition_le
    hn hα hβ hSlin hDlin hS_left hB_right hapos hspos hdpos
    hS hD hB hlin hdiff herr hQ).trans hε

/-- Indexed convergence shell for the fixed-scale inverse-amplification
    supremum.  This is the Lean-facing version of the final Theorem 6.4 limit
    step supplied by the GPT-5.5 Pro route: once the fixed-scale hypotheses hold
    eventually and the product error `a*s*d_i*b_i` tends to zero, the supremum
    values tend to the product condition number `a*s`.

    The theorem still leaves the source-facing perturbation-radius feasible set,
    inverse-existence proof, and proof that `a*s*d_i*b_i → 0` to downstream
    declarations. -/
theorem mixedInverseRelativeAmplificationAtScale_sup_tendsto_condition_of_vanishing_error
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D B : ι → ComplexVectorMap n n} {a s : ℝ}
    {d b e c Q : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (B i x) = x) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (B i) (b i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hdiff : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να (complexVectorMapSub (B i) S) (e i)) l)
    (hrem : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapAdd (complexVectorMapSub (B i) S)
          (complexVectorMapComp S (complexVectorMapComp (D i) S))) (c i)) l)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationAtScale
        να νβ A S a s (d i) (b i) (Q i)) l)
    (hvanish : Filter.Tendsto (fun i => a * s * d i * b i) l (nhds 0)) :
    Filter.Tendsto Q l (nhds (a * s)) := by
  apply tendsto_of_eventually_abs_sub_le_tendsto_zero hvanish
  filter_upwards [hDlin, hB_right, hdpos, hD, hB, hlin, hdiff, hrem, hQ] with
    i hDlin_i hB_right_i hdpos_i hD_i hB_i hlin_i hdiff_i hrem_i hQ_i
  exact mixedInverseRelativeAmplificationAtScale_sup_abs_sub_condition_le
    hn hα hβ hSlin hDlin_i hS_left hB_right_i hapos hspos hdpos_i
    hS hD_i hB_i hlin_i hdiff_i hrem_i hQ_i

/-- Source-facing convergence variant for the local Theorem 6.4 fixed-scale
    supremum API.  Instead of assuming the product error already tends to zero,
    it is enough that the perturbation scale `d_i` tends to zero and the
    perturbed-inverse bound parameter `b_i` is eventually bounded.

    This is still not the final source theorem: it assumes the indexed
    fixed-scale hypotheses and the eventual inverse-bound envelope, which must
    later be derived from the perturbation-radius feasible set and
    small-perturbation inverse-existence machinery. -/
theorem mixedInverseRelativeAmplificationAtScale_sup_tendsto_condition_of_tendsto_scale_bounded_inverse
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D Bmap : ι → ComplexVectorMap n n} {a s B0 : ℝ}
    {d b e c Q : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (Bmap i) (b i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hdiff : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να (complexVectorMapSub (Bmap i) S) (e i)) l)
    (hrem : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapAdd (complexVectorMapSub (Bmap i) S)
          (complexVectorMapComp S (complexVectorMapComp (D i) S))) (c i)) l)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationAtScale
        να νβ A S a s (d i) (b i) (Q i)) l)
    (hd_tendsto : Filter.Tendsto d l (nhds 0))
    (hb_bound : Filter.Eventually (fun i => |b i| ≤ B0) l)
    (hB0 : 0 ≤ B0) :
    Filter.Tendsto Q l (nhds (a * s)) := by
  have hvanish : Filter.Tendsto (fun i => a * s * d i * b i) l (nhds 0) :=
    tendsto_const_mul_of_tendsto_zero_of_eventually_abs_le
      (mul_pos hapos hspos) hB0 hd_tendsto hb_bound
  exact mixedInverseRelativeAmplificationAtScale_sup_tendsto_condition_of_vanishing_error
    hn hα hβ hSlin hS_left hapos hspos hS hDlin hB_right hdpos
    hD hB hlin hdiff hrem hQ hvanish

/-- Real envelope behind the resolvent-style perturbed-inverse bound: if
    `d_i -> 0`, `b_i` is eventually nonnegative, and eventually
    `b_i <= s / (1 - s*d_i)` for a positive `s`, then `b_i` is eventually
    bounded by `2*s`. -/
theorem eventually_abs_le_two_mul_of_resolvent_bound_tendsto_zero
    {ι : Type*} {l : Filter ι} {d b : ι → ℝ} {s : ℝ}
    (hspos : 0 < s)
    (hd_tendsto : Filter.Tendsto d l (nhds 0))
    (hb_nonneg : Filter.Eventually (fun i => 0 ≤ b i) l)
    (hb_resolvent : Filter.Eventually (fun i => b i ≤ s / (1 - s * d i)) l) :
    Filter.Eventually (fun i => |b i| ≤ 2 * s) l := by
  have hscale_pos : 0 < 1 / (2 * s) :=
    one_div_pos.mpr (mul_pos (by norm_num) hspos)
  have hd_small :
      Filter.Eventually (fun i => dist (d i) 0 < 1 / (2 * s)) l :=
    (Metric.tendsto_nhds.mp hd_tendsto) (1 / (2 * s)) hscale_pos
  filter_upwards [hd_small, hb_nonneg, hb_resolvent] with i hdi_small hbi_nonneg hbi_bound
  have hdi_abs : |d i| < 1 / (2 * s) := by
    simpa [Real.dist_eq] using hdi_small
  have hdi_le : d i ≤ 1 / (2 * s) :=
    le_of_lt ((le_abs_self (d i)).trans_lt hdi_abs)
  have hsd_le_half : s * d i ≤ 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hdi_le (le_of_lt hspos)
    calc
      s * d i ≤ s * (1 / (2 * s)) := hmul
      _ = 1 / 2 := by
        field_simp [ne_of_gt hspos]
  have hden_ge_half : 1 / 2 ≤ 1 - s * d i := by
    linarith
  have hden_pos : 0 < 1 - s * d i :=
    lt_of_lt_of_le (by norm_num) hden_ge_half
  have hres_le : s / (1 - s * d i) ≤ 2 * s := by
    rw [div_le_iff₀ hden_pos]
    nlinarith [hspos, hsd_le_half]
  calc
    |b i| = b i := abs_of_nonneg hbi_nonneg
    _ ≤ s / (1 - s * d i) := hbi_bound
    _ ≤ 2 * s := hres_le

/-- Resolvent-bound variant of the local Theorem 6.4 convergence shell.  This
    packages the next source-facing step: an eventual bound of the form
    `b_i <= s / (1 - s*d_i)` for the perturbed inverse, together with
    `d_i -> 0`, supplies the bounded inverse-scale hypothesis required by
    `mixedInverseRelativeAmplificationAtScale_sup_tendsto_condition_of_tendsto_scale_bounded_inverse`.

    It still assumes the fixed-scale feasible data and the resolvent-style
    inverse bound eventually; deriving those from a concrete perturbation-radius
    `sSup` feasible set remains the next open source theorem layer. -/
theorem mixedInverseRelativeAmplificationAtScale_sup_tendsto_condition_of_resolvent_inverse_bound
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D Bmap : ι → ComplexVectorMap n n} {a s : ℝ}
    {d b e c Q : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (Bmap i) (b i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hdiff : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να (complexVectorMapSub (Bmap i) S) (e i)) l)
    (hrem : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapAdd (complexVectorMapSub (Bmap i) S)
          (complexVectorMapComp S (complexVectorMapComp (D i) S))) (c i)) l)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationAtScale
        να νβ A S a s (d i) (b i) (Q i)) l)
    (hd_tendsto : Filter.Tendsto d l (nhds 0))
    (hb_resolvent : Filter.Eventually (fun i => b i ≤ s / (1 - s * d i)) l) :
    Filter.Tendsto Q l (nhds (a * s)) := by
  have hb_nonneg : Filter.Eventually (fun i => 0 ≤ b i) l := by
    filter_upwards [hB] with i hB_i
    exact mixedSubordinateBound_nonneg_of_nonempty hn hβ hα hB_i
  have hb_bound : Filter.Eventually (fun i => |b i| ≤ 2 * s) l :=
    eventually_abs_le_two_mul_of_resolvent_bound_tendsto_zero
      hspos hd_tendsto hb_nonneg hb_resolvent
  have hB0 : 0 ≤ 2 * s := by
    nlinarith [hspos]
  exact
    mixedInverseRelativeAmplificationAtScale_sup_tendsto_condition_of_tendsto_scale_bounded_inverse
      hn hα hβ hSlin hS_left hapos hspos hS hDlin hB_right hdpos
      hD hB hlin hdiff hrem hQ hd_tendsto hb_bound hB0

/-- Small-perturbation right-inverse variant of the local Theorem 6.4
    convergence shell.  If each supplied perturbed map `A + D_i` has a right
    inverse `B_i`, the perturbation scale tends to zero, and the fixed-scale
    hypotheses are stated with the resolvent bound
    `b_i = s / (1 - s*d_i)`, then the fixed-scale amplification suprema tend
    to the product condition number.

    This removes the previously external perturbed-inverse bound hypothesis by
    deriving it from `(A + D_i) B_i = I` and `s*d_i < 1` eventually.  It still
    assumes right-inverse witnesses and the fixed-scale supremum/value
    hypotheses; the final perturbation-radius `sSup` feasible-set theorem
    remains a downstream source-facing layer. -/
theorem mixedInverseRelativeAmplificationAtScale_sup_tendsto_condition_of_small_right_inverse
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D Bmap : ι → ComplexVectorMap n n} {a s : ℝ}
    {d e c Q : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hdiff : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να (complexVectorMapSub (Bmap i) S) (e i)) l)
    (hrem : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapAdd (complexVectorMapSub (Bmap i) S)
          (complexVectorMapComp S (complexVectorMapComp (D i) S))) (c i)) l)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationAtScale
        να νβ A S a s (d i) (s / (1 - s * d i)) (Q i)) l)
    (hd_tendsto : Filter.Tendsto d l (nhds 0)) :
    Filter.Tendsto Q l (nhds (a * s)) := by
  have hscale_pos : 0 < 1 / (2 * s) :=
    one_div_pos.mpr (mul_pos (by norm_num) hspos)
  have hd_small :
      Filter.Eventually (fun i => dist (d i) 0 < 1 / (2 * s)) l :=
    (Metric.tendsto_nhds.mp hd_tendsto) (1 / (2 * s)) hscale_pos
  have hsmall : Filter.Eventually (fun i => s * d i < 1) l := by
    filter_upwards [hd_small] with i hdi_small
    have hdi_abs : |d i| < 1 / (2 * s) := by
      simpa [Real.dist_eq] using hdi_small
    have hdi_lt : d i < 1 / (2 * s) :=
      lt_of_le_of_lt (le_abs_self (d i)) hdi_abs
    have hmul : s * d i < s * (1 / (2 * s)) :=
      mul_lt_mul_of_pos_left hdi_lt hspos
    have hhalf : s * (1 / (2 * s)) = 1 / 2 := by
      field_simp [ne_of_gt hspos]
    have hsdi_half : s * d i < 1 / 2 := by
      exact hmul.trans_eq hhalf
    nlinarith
  have hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (Bmap i) (s / (1 - s * d i))) l := by
    filter_upwards [hB_right, hD, hsmall] with i hB_right_i hD_i hsmall_i
    exact inversePerturbation_perturbedInverse_bound_of_small
      hα hSlin hS_left hB_right_i (le_of_lt hspos) hsmall_i hS hD_i.1
  have hb_resolvent :
      Filter.Eventually (fun i => s / (1 - s * d i) ≤ s / (1 - s * d i)) l :=
    Filter.Eventually.of_forall (fun _ => le_rfl)
  exact
    mixedInverseRelativeAmplificationAtScale_sup_tendsto_condition_of_resolvent_inverse_bound
      hn hα hβ hSlin hS_left hapos hspos hS hDlin hB_right hdpos
      hD hB hlin hdiff hrem hQ hd_tendsto hb_resolvent

/-- Source-radius feasible nonlinear inverse-amplification values.  An element
    is the source-scaled ratio `(||B - S|| / s) / (d / a)` for a perturbation
    `D` whose mixed norm value is `d`, with `0 < d <= rho*a`, and for a right
    inverse `B` of `A + D`.

    The smallness hypothesis `s*d < 1` is included because this local
    source-facing set is intended for the small-radius side of Theorem 6.4,
    where the resolvent bound for the perturbed inverse is available. -/
def MixedInverseRelativeAmplificationRadiusSet
    {n : ℕ} (να νβ : CVec n → ℝ) (A S : ComplexVectorMap n n)
    (a s rho : ℝ) : Set ℝ :=
  {q | ∃ D B : ComplexVectorMap n n, ∃ d e : ℝ,
    IsComplexVectorMapLinear D ∧
      0 < d ∧ d ≤ rho * a ∧ s * d < 1 ∧
        IsMixedSubordinateNormValue να νβ D d ∧
          (∀ x : CVec n, complexVectorMapAdd A D (B x) = x) ∧
            IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e ∧
              q = (e / s) / (d / a)}

/-- Concrete `sSup` presentation of the source-radius feasible set.  The
    predicate-level `IsSupMixedInverseRelativeAmplificationRadius` below remains
    the proof-facing API until nonemptiness and boundedness are supplied by the
    final source theorem. -/
noncomputable def mixedInverseRelativeAmplificationRadiusSup
    {n : ℕ} (να νβ : CVec n → ℝ) (A S : ComplexVectorMap n n)
    (a s rho : ℝ) : ℝ :=
  sSup (MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho)

/-- Predicate-level supremum for the source-radius nonlinear
    inverse-amplification set. -/
def IsSupMixedInverseRelativeAmplificationRadius
    {n : ℕ} (να νβ : CVec n → ℝ) (A S : ComplexVectorMap n n)
    (a s rho Q : ℝ) : Prop :=
  (∀ q : ℝ,
    q ∈ MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho → q ≤ Q) ∧
    ∀ U : ℝ,
      (∀ q : ℝ,
        q ∈ MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho →
          q ≤ U) →
        Q ≤ U

/-- Membership constructor for the source-radius nonlinear
    inverse-amplification set. -/
theorem mixedInverseRelativeAmplificationRadius_mem
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s rho d e : ℝ}
    (hDlin : IsComplexVectorMapLinear D)
    (hdpos : 0 < d)
    (hdradius : d ≤ rho * a)
    (hsmall : s * d < 1)
    (hD : IsMixedSubordinateNormValue να νβ D d)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e) :
    (e / s) / (d / a) ∈
      MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho := by
  exact ⟨D, B, d, e, hDlin, hdpos, hdradius, hsmall, hD, hB_right, hdiff, rfl⟩

/-- Every source-radius feasible value belongs to the corresponding fixed-scale
    set with the resolvent perturbed-inverse bound `s / (1 - s*d)`.

    This is the bridge from the source radius set to the existing checked
    fixed-scale Theorem 6.4 squeeze. -/
theorem mixedInverseRelativeAmplificationRadius_mem_atScale_of_mem
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho q : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hq : q ∈ MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho) :
    ∃ d : ℝ,
      0 < d ∧ d ≤ rho * a ∧ s * d < 1 ∧
        q ∈ MixedInverseRelativeAmplificationAtScaleSet
          να νβ A S a s d (s / (1 - s * d)) := by
  obtain ⟨D, B, d, e, hDlin, hdpos, hdradius, hsmall,
    hD, hB_right, hdiff, hqeq⟩ := hq
  have hB : MixedSubordinateBound νβ να B (s / (1 - s * d)) :=
    inversePerturbation_perturbedInverse_bound_of_small
      hα hSlin hS_left hB_right (le_of_lt hspos) hsmall hS hD.1
  refine ⟨d, hdpos, hdradius, hsmall, ?_⟩
  rw [hqeq]
  exact mixedInverseRelativeAmplificationAtScale_mem hDlin hD hB hB_right hdiff

/-- Radius-level upper estimate inherited from the fixed-scale resolvent
    squeeze: each feasible source-radius value has a perturbation scale `d`
    inside the radius and is bounded by
    `a*s*(1 + d*(s/(1 - s*d)))`. -/
theorem mixedInverseRelativeAmplificationRadius_value_le_resolvent
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho q : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hq : q ∈ MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho) :
    ∃ d : ℝ,
      0 < d ∧ d ≤ rho * a ∧ s * d < 1 ∧
        q ≤ a * s * (1 + d * (s / (1 - s * d))) := by
  obtain ⟨d, hdpos, hdradius, hsmall, hqfixed⟩ :=
    mixedInverseRelativeAmplificationRadius_mem_atScale_of_mem
      hα hSlin hS_left hspos hS hq
  refine ⟨d, hdpos, hdradius, hsmall, ?_⟩
  exact mixedInverseRelativeAmplificationAtScale_value_le
    hα hSlin hS_left hapos hspos hdpos hS hqfixed

/-- Monotonicity of the scalar resolvent envelope used in the source-radius
    Theorem 6.4 bridge.  On the small-perturbation interval `s*t < 1`, the
    factor `t * s / (1 - s*t)` is monotone in `t`. -/
theorem resolventScale_mono_of_le_of_small
    {s d R : ℝ} (hspos : 0 < s) (hdR : d ≤ R)
    (hdsmall : s * d < 1) (hRsmall : s * R < 1) :
    d * (s / (1 - s * d)) ≤ R * (s / (1 - s * R)) := by
  have hdDen : 0 < 1 - s * d := by linarith
  have hRDen : 0 < 1 - s * R := by linarith
  have hfrac : (d * s) / (1 - s * d) ≤ (R * s) / (1 - s * R) := by
    rw [div_le_iff₀ hdDen]
    rw [div_mul_eq_mul_div]
    rw [le_div_iff₀ hRDen]
    nlinarith [mul_le_mul_of_nonneg_right hdR (le_of_lt hspos)]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hfrac

/-- Uniform radius-level upper estimate: if the whole radius is small
    (`s*(rho*a) < 1`), every feasible source-radius amplification value is
    bounded by the resolvent envelope at the endpoint `rho*a`. -/
theorem mixedInverseRelativeAmplificationRadius_value_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho q : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hradiusSmall : s * (rho * a) < 1)
    (hS : MixedSubordinateBound νβ να S s)
    (hq : q ∈ MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho) :
    q ≤ a * s * (1 + (rho * a) * (s / (1 - s * (rho * a)))) := by
  obtain ⟨d, _hdpos, hdradius, hsmall, hqle⟩ :=
    mixedInverseRelativeAmplificationRadius_value_le_resolvent
      hα hSlin hS_left hapos hspos hS hq
  have hmono :
      d * (s / (1 - s * d)) ≤
        (rho * a) * (s / (1 - s * (rho * a))) :=
    resolventScale_mono_of_le_of_small hspos hdradius hsmall hradiusSmall
  have hinner :
      1 + d * (s / (1 - s * d)) ≤
        1 + (rho * a) * (s / (1 - s * (rho * a))) := by
    linarith
  have hscale : 0 ≤ a * s := mul_nonneg (le_of_lt hapos) (le_of_lt hspos)
  exact hqle.trans (mul_le_mul_of_nonneg_left hinner hscale)

/-- Uniform upper bound for any source-radius supremum over a small radius. -/
theorem mixedInverseRelativeAmplificationRadius_sup_le
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho Q : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hradiusSmall : s * (rho * a) < 1)
    (hS : MixedSubordinateBound νβ να S s)
    (hQ : IsSupMixedInverseRelativeAmplificationRadius να νβ A S a s rho Q) :
    Q ≤ a * s * (1 + (rho * a) * (s / (1 - s * (rho * a)))) := by
  exact hQ.2 (a * s * (1 + (rho * a) * (s / (1 - s * (rho * a)))))
    (fun q hq =>
      mixedInverseRelativeAmplificationRadius_value_le
        hα hSlin hS_left hapos hspos hradiusSmall hS hq)

/-- A shrinking source radius is eventually inside the small-resolvent region
    `s*(rho_i*a) < 1`. -/
theorem eventually_radius_resolvent_small_of_tendsto_zero
    {ι : Type*} {l : Filter ι} {rho : ι → ℝ} {a s : ℝ}
    (hspos : 0 < s) (hrho : Filter.Tendsto rho l (nhds 0)) :
    Filter.Eventually (fun i => s * (rho i * a) < 1) l := by
  have hR : Filter.Tendsto (fun i => rho i * a) l (nhds 0) := by
    simpa using (hrho.mul_const a)
  have hscale_pos : 0 < 1 / (2 * s) :=
    one_div_pos.mpr (mul_pos (by norm_num) hspos)
  have hR_small :
      Filter.Eventually (fun i => dist (rho i * a) 0 < 1 / (2 * s)) l :=
    (Metric.tendsto_nhds.mp hR) (1 / (2 * s)) hscale_pos
  filter_upwards [hR_small] with i hi
  have hRi_abs : |rho i * a| < 1 / (2 * s) := by
    simpa [Real.dist_eq] using hi
  have hRi_lt : rho i * a < 1 / (2 * s) :=
    lt_of_le_of_lt (le_abs_self (rho i * a)) hRi_abs
  have hmul : s * (rho i * a) < s * (1 / (2 * s)) :=
    mul_lt_mul_of_pos_left hRi_lt hspos
  have hhalf : s * (1 / (2 * s)) = 1 / 2 := by
    field_simp [ne_of_gt hspos]
  have hlt_half : s * (rho i * a) < 1 / 2 := hmul.trans_eq hhalf
  nlinarith

/-- The radius endpoint resolvent envelope tends to the product condition
    number scale as the radius shrinks to zero. -/
theorem mixedInverseRelativeAmplificationRadius_upperEnvelope_tendsto
    {ι : Type*} {l : Filter ι} {rho : ι → ℝ} {a s : ℝ}
    (hapos : 0 < a) (hspos : 0 < s)
    (hrho : Filter.Tendsto rho l (nhds 0)) :
    Filter.Tendsto
      (fun i => a * s * (1 + (rho i * a) * (s / (1 - s * (rho i * a)))))
      l (nhds (a * s)) := by
  have hR : Filter.Tendsto (fun i => rho i * a) l (nhds 0) := by
    simpa using (hrho.mul_const a)
  have hsmall : Filter.Eventually (fun i => s * (rho i * a) < 1) l :=
    eventually_radius_resolvent_small_of_tendsto_zero hspos hrho
  have hb_nonneg :
      Filter.Eventually (fun i => 0 ≤ s / (1 - s * (rho i * a))) l := by
    filter_upwards [hsmall] with i hsmall_i
    have hden : 0 < 1 - s * (rho i * a) := by linarith
    exact div_nonneg (le_of_lt hspos) (le_of_lt hden)
  have hb_resolvent :
      Filter.Eventually
        (fun i => s / (1 - s * (rho i * a)) ≤
          s / (1 - s * (rho i * a))) l :=
    Filter.Eventually.of_forall (fun _ => le_rfl)
  have hb_bound :
      Filter.Eventually (fun i => |s / (1 - s * (rho i * a))| ≤ 2 * s) l :=
    eventually_abs_le_two_mul_of_resolvent_bound_tendsto_zero
      hspos hR hb_nonneg hb_resolvent
  have hB0 : 0 ≤ 2 * s := by nlinarith [hspos]
  have hvanish :
      Filter.Tendsto
        (fun i => a * s * (rho i * a) * (s / (1 - s * (rho i * a))))
        l (nhds 0) :=
    tendsto_const_mul_of_tendsto_zero_of_eventually_abs_le
      (mul_pos hapos hspos) hB0 hR hb_bound
  have hadd :
      Filter.Tendsto
        (fun i => a * s + a * s * (rho i * a) * (s / (1 - s * (rho i * a))))
        l (nhds (a * s + 0)) :=
    tendsto_const_nhds.add hvanish
  simpa [mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
    mul_assoc] using hadd

/-- Indexed upper-bound wrapper for source-radius suprema over a shrinking
    radius family.  This is the upper half of the final radius-limit squeeze:
    eventually each radius supremum is bounded by the radius endpoint envelope,
    and that envelope tends to `a*s`. -/
theorem mixedInverseRelativeAmplificationRadius_sup_eventually_le_upperEnvelope
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {rho Q : ι → ℝ} {a s : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationRadius
        να νβ A S a s (rho i) (Q i)) l)
    (hrho : Filter.Tendsto rho l (nhds 0)) :
    Filter.Eventually
      (fun i => Q i ≤
        a * s * (1 + (rho i * a) * (s / (1 - s * (rho i * a))))) l := by
  have hsmall : Filter.Eventually (fun i => s * (rho i * a) < 1) l :=
    eventually_radius_resolvent_small_of_tendsto_zero hspos hrho
  filter_upwards [hQ, hsmall] with i hQ_i hsmall_i
  exact mixedInverseRelativeAmplificationRadius_sup_le
    hα hSlin hS_left hapos hspos hsmall_i hS hQ_i

/-- Radius-supremum upper bound from any uniform bound on the resolvent
    envelope over all feasible perturbation scales inside the radius. -/
theorem mixedInverseRelativeAmplificationRadius_sup_le_of_resolvent_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho Q U : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hQ : IsSupMixedInverseRelativeAmplificationRadius να νβ A S a s rho Q)
    (hU : ∀ d : ℝ,
      0 < d → d ≤ rho * a → s * d < 1 →
        a * s * (1 + d * (s / (1 - s * d))) ≤ U) :
    Q ≤ U := by
  exact hQ.2 U (fun q hq => by
    obtain ⟨d, hdpos, hdradius, hsmall, hqle⟩ :=
      mixedInverseRelativeAmplificationRadius_value_le_resolvent
        hα hSlin hS_left hapos hspos hS hq
    exact hqle.trans (hU d hdpos hdradius hsmall))

/-- Radius-level lower witness inherited from the fixed-scale lower squeeze.
    Any admissible sharp linearized witness at scale `d` contributes a
    source-radius feasible value at least `a*s*(1 - d*b)`. -/
theorem exists_mixedInverseRelativeAmplificationRadius_lower_bound
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s rho d b e c : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hdradius : d ≤ rho * a)
    (hsmall : s * d < 1)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : IsMixedSubordinateNormValue να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d))
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c) :
    ∃ q : ℝ,
      q ∈ MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho ∧
        a * s * (1 - d * b) ≤ q := by
  refine ⟨(e / s) / (d / a), ?_, ?_⟩
  · exact mixedInverseRelativeAmplificationRadius_mem
      hDlin hdpos hdradius hsmall hD hB_right hdiff
  · exact inversePerturbation_relative_difference_ratio_lower_le_of_linearized
      hα hSlin hDlin hS_left hB_right hapos hspos hdpos hS hD.1 hB
      hlin hdiff herr

/-- Lower bound for any source-radius supremum once a checked lower witness
    exists in the source-radius feasible set. -/
theorem mixedInverseRelativeAmplificationRadius_lower_le_sup_of_exists
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho Q L : ℝ}
    (hQ : IsSupMixedInverseRelativeAmplificationRadius να νβ A S a s rho Q)
    (hL : ∃ q : ℝ,
      q ∈ MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho ∧
        L ≤ q) :
    L ≤ Q := by
  obtain ⟨q, hqmem, hLq⟩ := hL
  exact hLq.trans (hQ.1 q hqmem)

/-- Radius-supremum lower bound from a sharp fixed-scale linearized witness
    that lies inside the source radius. -/
theorem mixedInverseRelativeAmplificationRadius_sup_lower_le_of_linearized
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D B : ComplexVectorMap n n}
    {a s rho d b e c Q : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hB_right : ∀ x : CVec n, complexVectorMapAdd A D (B x) = x)
    (hapos : 0 < a) (hspos : 0 < s) (hdpos : 0 < d)
    (hdradius : d ≤ rho * a)
    (hsmall : s * d < 1)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : IsMixedSubordinateNormValue να νβ D d)
    (hB : MixedSubordinateBound νβ να B b)
    (hlin : IsMixedSubordinateNormValue νβ να
      (complexVectorMapComp S (complexVectorMapComp D S)) (s ^ 2 * d))
    (hdiff : IsMixedSubordinateNormValue νβ να (complexVectorMapSub B S) e)
    (herr : IsMixedSubordinateNormValue νβ να
      (complexVectorMapAdd (complexVectorMapSub B S)
        (complexVectorMapComp S (complexVectorMapComp D S))) c)
    (hQ : IsSupMixedInverseRelativeAmplificationRadius να νβ A S a s rho Q) :
    a * s * (1 - d * b) ≤ Q := by
  exact mixedInverseRelativeAmplificationRadius_lower_le_sup_of_exists hQ
    (exists_mixedInverseRelativeAmplificationRadius_lower_bound
      hα hSlin hDlin hS_left hB_right hapos hspos hdpos hdradius hsmall
      hS hD hB hlin hdiff herr)

/-- Indexed lower-bound wrapper for source-radius suprema.  If a sharp
    linearized witness family is eventually feasible inside the shrinking
    source-radius sets, each corresponding radius supremum is eventually bounded
    below by `a*s*(1 - d_i*b_i)`. -/
theorem mixedInverseRelativeAmplificationRadius_sup_eventually_lower_le_of_linearized
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D Bmap : ι → ComplexVectorMap n n} {a s : ℝ}
    {rho d b e c Q : ι → ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (Bmap i) (b i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hdiff : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να (complexVectorMapSub (Bmap i) S) (e i)) l)
    (hrem : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapAdd (complexVectorMapSub (Bmap i) S)
          (complexVectorMapComp S (complexVectorMapComp (D i) S))) (c i)) l)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationRadius
        να νβ A S a s (rho i) (Q i)) l) :
    Filter.Eventually (fun i => a * s * (1 - d i * b i) ≤ Q i) l := by
  filter_upwards [hDlin, hB_right, hdpos, hdradius, hsmall,
    hD, hB, hlin, hdiff, hrem, hQ] with
    i hDlin_i hB_right_i hdpos_i hdradius_i hsmall_i
    hD_i hB_i hlin_i hdiff_i hrem_i hQ_i
  exact mixedInverseRelativeAmplificationRadius_sup_lower_le_of_linearized
    hα hSlin hDlin_i hS_left hB_right_i hapos hspos hdpos_i
    hdradius_i hsmall_i hS hD_i hB_i hlin_i hdiff_i hrem_i hQ_i

/-- Extract the two least-value witnesses needed by the lower radius squeeze
    from the algebraic inverse-perturbation data.  If the chosen perturbations
    `D_i` and perturbed right inverses `B_i` are eventually linear, with the
    usual right-inverse equation and subordinate bounds, then one can choose
    actual mixed subordinate norm values for `B_i - S` and for the first-order
    error `(B_i - S) + S D_i S`.

    This removes two bookkeeping assumptions from the source-radius route; the
    genuinely remaining source-facing obligation is still to construct the
    linear perturbed right inverses `B_i`. -/
theorem exists_inversePerturbation_difference_error_normValue_family
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D Bmap : ι → ComplexVectorMap n n} {s : ℝ} {d b : ι → ℝ}
    (hn : 0 < n) (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hBlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (Bmap i)) l)
    (hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (Bmap i) (b i)) l) :
    ∃ e c : ι → ℝ,
      Filter.Eventually
        (fun i => IsMixedSubordinateNormValue νβ να
          (complexVectorMapSub (Bmap i) S) (e i)) l ∧
        Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapAdd (complexVectorMapSub (Bmap i) S)
          (complexVectorMapComp S (complexVectorMapComp (D i) S)))
        (c i)) l := by
  classical
  let diffReady : ι → Prop := fun i =>
    IsComplexVectorMapLinear (Bmap i) ∧
      MixedSubordinateBound νβ να (Bmap i) (b i)
  have hdiff_point : ∀ i, diffReady i →
      ∃ e : ℝ,
        IsMixedSubordinateNormValue νβ να
          (complexVectorMapSub (Bmap i) S) e := by
    intro i hi
    rcases hi with ⟨hBlin_i, hB_i⟩
    have hdiff_lin : IsComplexVectorMapLinear (complexVectorMapSub (Bmap i) S) :=
      complexVectorMapSub_linear hBlin_i hSlin
    have hdiff_bound :
        MixedSubordinateBound νβ να (complexVectorMapSub (Bmap i) S) (b i + s) :=
      mixedSubordinateBound_sub hα hB_i hS
    exact exists_mixedSubordinateNormValue_of_bound_nonempty
      (n := n) (m := n) (να := νβ) (νβ := να)
      hn hβ hα hdiff_lin hdiff_bound
  let e : ι → ℝ := fun i =>
    if hi : diffReady i then Classical.choose (hdiff_point i hi) else 0
  let errReady : ι → Prop := fun i =>
    IsComplexVectorMapLinear (D i) ∧
      IsComplexVectorMapLinear (Bmap i) ∧
      (∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) ∧
      0 < d i ∧
      IsMixedSubordinateNormValue να νβ (D i) (d i) ∧
      MixedSubordinateBound νβ να (Bmap i) (b i)
  have herr_point : ∀ i, errReady i →
      ∃ c : ℝ,
        IsMixedSubordinateNormValue νβ να
          (complexVectorMapAdd (complexVectorMapSub (Bmap i) S)
            (complexVectorMapComp S (complexVectorMapComp (D i) S)))
          c := by
    intro i hi
    rcases hi with
      ⟨hDlin_i, hBlin_i, hB_right_i, hdpos_i, hD_i, hB_i⟩
    have hdiff_lin : IsComplexVectorMapLinear (complexVectorMapSub (Bmap i) S) :=
      complexVectorMapSub_linear hBlin_i hSlin
    have hlin_sand :
        IsComplexVectorMapLinear
          (complexVectorMapComp S (complexVectorMapComp (D i) S)) :=
      complexVectorMapComp_linear hSlin (complexVectorMapComp_linear hDlin_i hSlin)
    have herr_lin :
        IsComplexVectorMapLinear
          (complexVectorMapAdd (complexVectorMapSub (Bmap i) S)
            (complexVectorMapComp S (complexVectorMapComp (D i) S))) :=
      complexVectorMapAdd_linear hdiff_lin hlin_sand
    have herr_bound :
        MixedSubordinateBound νβ να
          (complexVectorMapAdd (complexVectorMapSub (Bmap i) S)
            (complexVectorMapComp S (complexVectorMapComp (D i) S)))
          (s ^ 2 * d i ^ 2 * b i) :=
      inversePerturbation_firstOrder_error_bound
        hSlin hDlin_i hS_left hB_right_i (le_of_lt hspos)
        (le_of_lt hdpos_i) hS hD_i.1 hB_i
    exact exists_mixedSubordinateNormValue_of_bound_nonempty
      (n := n) (m := n) (να := νβ) (νβ := να)
      hn hβ hα herr_lin herr_bound
  let c : ι → ℝ := fun i =>
    if hi : errReady i then Classical.choose (herr_point i hi) else 0
  refine ⟨e, c, ?_, ?_⟩
  · have hready : Filter.Eventually (fun i => diffReady i) l := by
      filter_upwards [hBlin, hB] with i hBlin_i hB_i
      exact ⟨hBlin_i, hB_i⟩
    filter_upwards [hready] with i hi
    have hspec := Classical.choose_spec (hdiff_point i hi)
    simpa [e, hi] using hspec
  · have hready : Filter.Eventually (fun i => errReady i) l := by
      filter_upwards [hDlin, hBlin, hB_right, hdpos, hD, hB] with
        i hDlin_i hBlin_i hB_right_i hdpos_i hD_i hB_i
      exact ⟨hDlin_i, hBlin_i, hB_right_i, hdpos_i, hD_i, hB_i⟩
    filter_upwards [hready] with i hi
    have hspec := Classical.choose_spec (herr_point i hi)
    simpa [c, hi] using hspec

/-- Abstract source-radius convergence squeeze for Theorem 6.4.  If radius
    suprema are eventually bounded above by the shrinking-radius resolvent
    envelope and below by a sharp linearized witness family whose error
    `a*s*d_i*b_i` vanishes, then the radius suprema tend to the product
    condition number `a*s`.

    This theorem is still a local proof-facing bridge: it assumes the sharp
    lower-witness family, perturbed right-inverse witnesses, and radius
    membership eventually.  The remaining source-facing work is to extract those
    witnesses from the concrete perturbation feasible set. -/
theorem mixedInverseRelativeAmplificationRadius_sup_tendsto_condition_of_linearized_witnesses
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D Bmap : ι → ComplexVectorMap n n} {a s B0 : ℝ}
    {rho d b e c Q : ι → ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (Bmap i) (b i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hdiff : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να (complexVectorMapSub (Bmap i) S) (e i)) l)
    (hrem : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapAdd (complexVectorMapSub (Bmap i) S)
          (complexVectorMapComp S (complexVectorMapComp (D i) S))) (c i)) l)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationRadius
        να νβ A S a s (rho i) (Q i)) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0))
    (hb_bound : Filter.Eventually (fun i => |b i| ≤ B0) l)
    (hB0 : 0 ≤ B0) :
    Filter.Tendsto Q l (nhds (a * s)) := by
  have hlower_ev :
      Filter.Eventually (fun i => a * s * (1 - d i * b i) ≤ Q i) l :=
    mixedInverseRelativeAmplificationRadius_sup_eventually_lower_le_of_linearized
      hα hSlin hS_left hapos hspos hS hDlin hB_right hdpos hdradius
      hsmall hD hB hlin hdiff hrem hQ
  have hupper_ev :
      Filter.Eventually
        (fun i => Q i ≤
          a * s * (1 + (rho i * a) * (s / (1 - s * (rho i * a))))) l :=
    mixedInverseRelativeAmplificationRadius_sup_eventually_le_upperEnvelope
      hα hSlin hS_left hapos hspos hS hQ hrho
  have hvanish : Filter.Tendsto (fun i => a * s * d i * b i) l (nhds 0) :=
    tendsto_const_mul_of_tendsto_zero_of_eventually_abs_le
      (mul_pos hapos hspos) hB0 hd_tendsto hb_bound
  have hlower_tendsto :
      Filter.Tendsto (fun i => a * s * (1 - d i * b i)) l (nhds (a * s)) := by
    have hneg :
        Filter.Tendsto (fun i => -(a * s * d i * b i)) l (nhds 0) := by
      simpa using hvanish.neg
    have hadd :
        Filter.Tendsto
          (fun i => a * s + -(a * s * d i * b i)) l (nhds (a * s + 0)) :=
      tendsto_const_nhds.add hneg
    simpa [sub_eq_add_neg, mul_add, mul_sub, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hadd
  have hupper_tendsto :
      Filter.Tendsto
        (fun i => a * s * (1 + (rho i * a) * (s / (1 - s * (rho i * a)))))
        l (nhds (a * s)) :=
    mixedInverseRelativeAmplificationRadius_upperEnvelope_tendsto hapos hspos hrho
  exact tendsto_of_eventually_between_tendsto hlower_tendsto hupper_tendsto
    (by
      filter_upwards [hlower_ev, hupper_ev] with i hli hui
      exact ⟨hli, hui⟩)

/-- Source-radius convergence squeeze with automatic extraction of the
    inverse-difference and first-order-error norm values.  Compared with
    `mixedInverseRelativeAmplificationRadius_sup_tendsto_condition_of_linearized_witnesses`,
    this version assumes the perturbed right inverses `B_i` are eventually
    linear and derives the value witnesses for `B_i - S` and
    `(B_i - S) + S D_i S` from the existing bounds.

    The theorem still deliberately leaves the hard source-facing construction
    of the perturbed right inverses `B_i` outside the local predicate layer. -/
theorem mixedInverseRelativeAmplificationRadius_sup_tendsto_condition_of_linearized_witnesses_of_linear_right_inverses
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D Bmap : ι → ComplexVectorMap n n} {a s B0 : ℝ}
    {rho d b Q : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hBlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (Bmap i)) l)
    (hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (Bmap i) (b i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationRadius
        να νβ A S a s (rho i) (Q i)) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0))
    (hb_bound : Filter.Eventually (fun i => |b i| ≤ B0) l)
    (hB0 : 0 ≤ B0) :
    Filter.Tendsto Q l (nhds (a * s)) := by
  obtain ⟨e, c, hdiff, hrem⟩ :=
    exists_inversePerturbation_difference_error_normValue_family
      hn hα hβ hSlin hS_left hspos hS hDlin hBlin hB_right hdpos hD hB
  exact
    mixedInverseRelativeAmplificationRadius_sup_tendsto_condition_of_linearized_witnesses
      hα hSlin hS_left hapos hspos hS hDlin hB_right hdpos hdradius
      hsmall hD hB hlin hdiff hrem hQ hrho hd_tendsto hb_bound hB0

/-- Source-radius convergence squeeze where the perturbed right inverses need
    not be supplied as linear maps.  Under the smallness condition `s*d_i < 1`,
    linearity of each right-inverse witness follows from
    `inversePerturbation_perturbedRightInverse_linear_of_small`, so this theorem
    removes the explicit `hBlin` assumption from the previous wrapper. -/
theorem mixedInverseRelativeAmplificationRadius_sup_tendsto_condition_of_linearized_witnesses_of_small_right_inverses
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D Bmap : ι → ComplexVectorMap n n} {a s B0 : ℝ}
    {rho d b Q : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (Bmap i) (b i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationRadius
        να νβ A S a s (rho i) (Q i)) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0))
    (hb_bound : Filter.Eventually (fun i => |b i| ≤ B0) l)
    (hB0 : 0 ≤ B0) :
    Filter.Tendsto Q l (nhds (a * s)) := by
  have hBlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (Bmap i)) l := by
    filter_upwards [hDlin, hB_right, hsmall, hD] with
      i hDlin_i hB_right_i hsmall_i hD_i
    exact inversePerturbation_perturbedRightInverse_linear_of_small
      hα hSlin hDlin_i hS_left hB_right_i (le_of_lt hspos) hsmall_i hS hD_i.1
  exact
    mixedInverseRelativeAmplificationRadius_sup_tendsto_condition_of_linearized_witnesses_of_linear_right_inverses
      hn hα hβ hSlin hS_left hapos hspos hS hDlin hBlin hB_right hdpos
      hdradius hsmall hD hB hlin hQ hrho hd_tendsto hb_bound hB0

/-- Source-radius convergence squeeze with the resolvent perturbed-inverse
    bound derived from the right-inverse equation.  This specializes the
    inverse-bound scale to `s / (1 - s*d_i)`, derives both linearity and the
    mixed subordinate bound for `B_i`, and then applies the small-right-inverse
    radius squeeze.

    The remaining source-facing obligation is now the actual construction of
    right-inverse witnesses `B_i` for the chosen small perturbations. -/
theorem mixedInverseRelativeAmplificationRadius_sup_tendsto_condition_of_resolvent_right_inverses
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D Bmap : ι → ComplexVectorMap n n} {a s : ℝ}
    {rho d Q : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hB_right : Filter.Eventually
      (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationRadius
        να νβ A S a s (rho i) (Q i)) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0)) :
    Filter.Tendsto Q l (nhds (a * s)) := by
  let b : ι → ℝ := fun i => s / (1 - s * d i)
  have hB : Filter.Eventually
      (fun i => MixedSubordinateBound νβ να (Bmap i) (b i)) l := by
    filter_upwards [hB_right, hD, hsmall] with i hB_right_i hD_i hsmall_i
    exact inversePerturbation_perturbedInverse_bound_of_small
      hα hSlin hS_left hB_right_i (le_of_lt hspos) hsmall_i hS hD_i.1
  have hb_nonneg : Filter.Eventually (fun i => 0 ≤ b i) l := by
    filter_upwards [hsmall] with i hsmall_i
    have hden : 0 < 1 - s * d i := by linarith
    exact div_nonneg (le_of_lt hspos) (le_of_lt hden)
  have hb_resolvent : Filter.Eventually (fun i => b i ≤ s / (1 - s * d i)) l :=
    Filter.Eventually.of_forall (fun _ => le_rfl)
  have hb_bound : Filter.Eventually (fun i => |b i| ≤ 2 * s) l :=
    eventually_abs_le_two_mul_of_resolvent_bound_tendsto_zero
      hspos hd_tendsto hb_nonneg hb_resolvent
  have hB0 : 0 ≤ 2 * s := by nlinarith [hspos]
  exact
    mixedInverseRelativeAmplificationRadius_sup_tendsto_condition_of_linearized_witnesses_of_small_right_inverses
      (b := b) hn hα hβ hSlin hS_left hapos hspos hS hDlin hB_right hdpos
      hdradius hsmall hD hB hlin hQ hrho hd_tendsto hb_bound hB0

/-- Source-radius convergence squeeze with perturbed right inverses constructed
    internally from small linear perturbations.  This combines the finite
    dimensional inverse-existence theorem
    `exists_inversePerturbation_perturbedRightInverse_of_small` with the
    resolvent right-inverse convergence wrapper, so callers no longer need to
    supply a family `B_i` satisfying `(A + D_i) B_i = I`.

    The remaining proof-facing assumptions are the radius suprema `Q_i` and the
    sharp linearized sandwich witnesses. -/
theorem mixedInverseRelativeAmplificationRadius_sup_tendsto_condition_of_constructed_right_inverses
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D : ι → ComplexVectorMap n n} {a s : ℝ}
    {rho d Q : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hAlin : IsComplexVectorMapLinear A)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hQ : Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationRadius
        να νβ A S a s (rho i) (Q i)) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0)) :
    Filter.Tendsto Q l (nhds (a * s)) := by
  classical
  let P : ι → ComplexVectorMap n n → Prop := fun i B =>
    IsComplexVectorMapLinear B ∧
      (∀ x : CVec n, complexVectorMapAdd A (D i) (B x) = x) ∧
        MixedSubordinateBound νβ να B (s / (1 - s * d i))
  have hex : Filter.Eventually (fun i => ∃ B : ComplexVectorMap n n, P i B) l := by
    filter_upwards [hDlin, hsmall, hD] with i hDlin_i hsmall_i hD_i
    exact exists_inversePerturbation_perturbedRightInverse_of_small
      hα hAlin hSlin hDlin_i hS_left (le_of_lt hspos) hsmall_i hS hD_i.1
  let Bmap : ι → ComplexVectorMap n n := fun i =>
    if h : ∃ B : ComplexVectorMap n n, P i B then Classical.choose h else fun _ => 0
  have hBprops : Filter.Eventually (fun i => P i (Bmap i)) l := by
    filter_upwards [hex] with i hi
    have hchoose : P i (Classical.choose hi) := Classical.choose_spec hi
    have hBmap : Bmap i = Classical.choose hi := by
      dsimp [Bmap]
      rw [dif_pos hi]
    simpa [hBmap] using hchoose
  have hB_right :
      Filter.Eventually
        (fun i => ∀ x : CVec n, complexVectorMapAdd A (D i) (Bmap i x) = x) l := by
    filter_upwards [hBprops] with i hi
    exact hi.2.1
  exact
    mixedInverseRelativeAmplificationRadius_sup_tendsto_condition_of_resolvent_right_inverses
      (Bmap := Bmap) hn hα hβ hSlin hS_left hapos hspos hS hDlin hB_right
      hdpos hdradius hsmall hD hlin hQ hrho hd_tendsto

/-- The concrete source-radius feasible set is bounded above on a small radius,
    using the resolvent envelope at the radius endpoint. -/
theorem mixedInverseRelativeAmplificationRadius_bddAbove_of_small
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hradiusSmall : s * (rho * a) < 1)
    (hS : MixedSubordinateBound νβ να S s) :
    BddAbove (MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho) := by
  refine ⟨a * s * (1 + (rho * a) * (s / (1 - s * (rho * a)))), ?_⟩
  intro q hq
  exact mixedInverseRelativeAmplificationRadius_value_le
    hα hSlin hS_left hapos hspos hradiusSmall hS hq

/-- Along a shrinking radius family, the concrete source-radius feasible sets are
    eventually bounded above by the resolvent endpoint envelope. -/
theorem eventually_mixedInverseRelativeAmplificationRadius_bddAbove_of_tendsto_zero
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {rho : ι → ℝ} {a s : ℝ} (hα : IsComplexVectorNorm να)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hrho : Filter.Tendsto rho l (nhds 0)) :
    Filter.Eventually
      (fun i => BddAbove
        (MixedInverseRelativeAmplificationRadiusSet να νβ A S a s (rho i))) l := by
  have hsmall : Filter.Eventually (fun i => s * (rho i * a) < 1) l :=
    eventually_radius_resolvent_small_of_tendsto_zero hspos hrho
  filter_upwards [hsmall] with i hsmall_i
  exact mixedInverseRelativeAmplificationRadius_bddAbove_of_small
    hα hSlin hS_left hapos hspos hsmall_i hS

/-- A small perturbation with a local mixed-norm value makes the source-radius
    feasible set nonempty: finite-dimensional invertibility constructs the
    perturbed right inverse, and the local least-value API packages `B - S`. -/
theorem mixedInverseRelativeAmplificationRadius_nonempty_of_small_perturbation
    {n : ℕ} {να νβ : CVec n → ℝ} {A S D : ComplexVectorMap n n}
    {a s rho d : ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hAlin : IsComplexVectorMapLinear A)
    (hSlin : IsComplexVectorMapLinear S)
    (hDlin : IsComplexVectorMapLinear D)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hspos : 0 < s) (hdpos : 0 < d)
    (hdradius : d ≤ rho * a) (hsmall : s * d < 1)
    (hS : MixedSubordinateBound νβ να S s)
    (hD : IsMixedSubordinateNormValue να νβ D d) :
    (MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho).Nonempty := by
  obtain ⟨B, hBlin, hB_right, hBbound⟩ :=
    exists_inversePerturbation_perturbedRightInverse_of_small
      hα hAlin hSlin hDlin hS_left (le_of_lt hspos) hsmall hS hD.1
  have hdiff_lin :
      IsComplexVectorMapLinear (complexVectorMapSub B S) :=
    complexVectorMapSub_linear hBlin hSlin
  have hdiff_bound :
      MixedSubordinateBound νβ να (complexVectorMapSub B S)
        (s / (1 - s * d) + s) :=
    mixedSubordinateBound_sub hα hBbound hS
  obtain ⟨e, hdiff⟩ :=
    exists_mixedSubordinateNormValue_of_bound_nonempty
      (n := n) (m := n) (να := νβ) (νβ := να)
      hn hβ hα hdiff_lin hdiff_bound
  exact ⟨(e / s) / (d / a),
    mixedInverseRelativeAmplificationRadius_mem
      hDlin hdpos hdradius hsmall hD hB_right hdiff⟩

/-- Indexed nonemptiness wrapper for source-radius feasible sets, derived from
    eventual small perturbations and the constructed right-inverse theorem. -/
theorem eventually_mixedInverseRelativeAmplificationRadius_nonempty_of_small_perturbations
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D : ι → ComplexVectorMap n n} {a s : ℝ} {rho d : ι → ℝ}
    (hn : 0 < n) (hα : IsComplexVectorNorm να)
    (hβ : IsComplexVectorNorm νβ)
    (hAlin : IsComplexVectorMapLinear A)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l) :
    Filter.Eventually
      (fun i =>
        (MixedInverseRelativeAmplificationRadiusSet να νβ A S a s (rho i)).Nonempty) l := by
  filter_upwards [hDlin, hdpos, hdradius, hsmall, hD] with
    i hDlin_i hdpos_i hdradius_i hsmall_i hD_i
  exact mixedInverseRelativeAmplificationRadius_nonempty_of_small_perturbation
    hn hα hβ hAlin hSlin hDlin_i hS_left hspos hdpos_i hdradius_i
    hsmall_i hS hD_i

/-- The concrete `sSup` function realizes the predicate-level source-radius
    supremum whenever the feasible set is nonempty and bounded above. -/
theorem isSup_mixedInverseRelativeAmplificationRadiusSup
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s rho : ℝ}
    (hne : (MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho).Nonempty)
    (hbdd : BddAbove (MixedInverseRelativeAmplificationRadiusSet να νβ A S a s rho)) :
    IsSupMixedInverseRelativeAmplificationRadius να νβ A S a s rho
      (mixedInverseRelativeAmplificationRadiusSup να νβ A S a s rho) := by
  constructor
  · intro q hq
    simpa [mixedInverseRelativeAmplificationRadiusSup] using le_csSup hbdd hq
  · intro U hU
    simpa [mixedInverseRelativeAmplificationRadiusSup] using csSup_le hne hU

/-- Eventual concrete-`sSup` wrapper for source-radius suprema. -/
theorem eventually_isSup_mixedInverseRelativeAmplificationRadiusSup
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {rho : ι → ℝ} {a s : ℝ}
    (hne : Filter.Eventually
      (fun i =>
        (MixedInverseRelativeAmplificationRadiusSet να νβ A S a s (rho i)).Nonempty) l)
    (hbdd : Filter.Eventually
      (fun i => BddAbove
        (MixedInverseRelativeAmplificationRadiusSet να νβ A S a s (rho i))) l) :
    Filter.Eventually
      (fun i => IsSupMixedInverseRelativeAmplificationRadius να νβ A S a s
        (rho i) (mixedInverseRelativeAmplificationRadiusSup να νβ A S a s (rho i))) l := by
  filter_upwards [hne, hbdd] with i hne_i hbdd_i
  exact isSup_mixedInverseRelativeAmplificationRadiusSup hne_i hbdd_i

/-- Concrete source-radius `sSup` convergence form of the Theorem 6.4 local
    condition-number bridge.  The external indexed supremum variable `Q_i` is
    replaced by the actual `sSup` of the source-radius feasible set; boundedness
    and nonemptiness are derived from the shrinking-radius and small-perturbation
    hypotheses. -/
theorem mixedInverseRelativeAmplificationRadiusSup_tendsto_condition_of_constructed_right_inverses
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {D : ι → ComplexVectorMap n n} {a s : ℝ}
    {rho d : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hAlin : IsComplexVectorMapLinear A)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : MixedSubordinateBound νβ να S s)
    (hDlin : Filter.Eventually (fun i => IsComplexVectorMapLinear (D i)) l)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hD : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue να νβ (D i) (d i)) l)
    (hlin : Filter.Eventually
      (fun i => IsMixedSubordinateNormValue νβ να
        (complexVectorMapComp S (complexVectorMapComp (D i) S)) (s ^ 2 * d i)) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0)) :
    Filter.Tendsto
      (fun i => mixedInverseRelativeAmplificationRadiusSup να νβ A S a s (rho i))
      l (nhds (a * s)) := by
  have hne :
      Filter.Eventually
        (fun i =>
          (MixedInverseRelativeAmplificationRadiusSet να νβ A S a s (rho i)).Nonempty) l :=
    eventually_mixedInverseRelativeAmplificationRadius_nonempty_of_small_perturbations
      hn hα hβ hAlin hSlin hS_left hspos hS hDlin hdpos hdradius hsmall hD
  have hbdd :
      Filter.Eventually
        (fun i => BddAbove
          (MixedInverseRelativeAmplificationRadiusSet να νβ A S a s (rho i))) l :=
    eventually_mixedInverseRelativeAmplificationRadius_bddAbove_of_tendsto_zero
      hα hSlin hS_left hapos hspos hS hrho
  have hQ :
      Filter.Eventually
        (fun i => IsSupMixedInverseRelativeAmplificationRadius να νβ A S a s
          (rho i)
          (mixedInverseRelativeAmplificationRadiusSup να νβ A S a s (rho i))) l :=
    eventually_isSup_mixedInverseRelativeAmplificationRadiusSup hne hbdd
  exact
    mixedInverseRelativeAmplificationRadius_sup_tendsto_condition_of_constructed_right_inverses
      (Q := fun i => mixedInverseRelativeAmplificationRadiusSup να νβ A S a s (rho i))
      hn hα hβ hAlin hSlin hS_left hapos hspos hS hDlin hdpos hdradius
      hsmall hD hlin hQ hrho hd_tendsto

/-- Concrete source-radius `sSup` convergence with the sharp linearized
    perturbation family chosen internally from the shrinking scale `d_i`.

    This removes the remaining supplied-`D_i` assumption from the local
    Theorem 6.4 radius-limit bridge: callers provide only the scale/radius
    hypotheses, while `exists_inverseSandwich_scaled_normValue_family_eq_square_mul`
    supplies the perturbations that realize the sharp lower derivative. -/
theorem mixedInverseRelativeAmplificationRadiusSup_tendsto_condition_of_sharp_scales
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s : ℝ} {rho d : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hAlin : IsComplexVectorMapLinear A)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : IsMixedSubordinateNormValue νβ να S s)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0)) :
    Filter.Tendsto
      (fun i => mixedInverseRelativeAmplificationRadiusSup να νβ A S a s (rho i))
      l (nhds (a * s)) := by
  obtain ⟨D, hDlin, hD, hlin⟩ :=
    exists_inverseSandwich_scaled_normValue_family_eq_square_mul
      hn hα hβ hSlin hS hspos hdpos
  exact
    mixedInverseRelativeAmplificationRadiusSup_tendsto_condition_of_constructed_right_inverses
      (D := D) hn hα hβ hAlin hSlin hS_left hapos hspos hS.1
      hDlin hdpos hdradius hsmall hD hlin hrho hd_tendsto

/-- Source-facing perturbation-radius condition-number limit value.  For a
    shrinking radius family `rho`, this says that the nonlinear relative inverse
    amplification supremum tends to the value `κ`.

    This is the local limit/supremum side of Higham Theorem 6.4; the separate
    product predicate `IsMixedConditionNumberProductValue` records the
    `||A|| * ||A^{-1}||` expression. -/
def IsMixedConditionNumberRadiusLimitValue
    {ι : Type*} (l : Filter ι)
    {n : ℕ} (να νβ : CVec n → ℝ) (A S : ComplexVectorMap n n)
    (a s : ℝ) (rho : ι → ℝ) (κ : ℝ) : Prop :=
  Filter.Tendsto
    (fun i => mixedInverseRelativeAmplificationRadiusSup να νβ A S a s (rho i))
    l (nhds κ)

/-- The perturbation-radius condition-number limit equals the product
    `||A||_{α,β} * ||A^{-1}||_{β,α}` in the local mixed least-bound model, once
    the source radius is probed by a shrinking positive scale family. -/
theorem mixedConditionNumberRadiusLimitValue_eq_norm_mul_inverse_norm_of_sharp_scales
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s : ℝ} {rho d : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hAlin : IsComplexVectorMapLinear A)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hS : IsMixedSubordinateNormValue νβ να S s)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0)) :
    IsMixedConditionNumberRadiusLimitValue l να νβ A S a s rho (a * s) := by
  exact
    mixedInverseRelativeAmplificationRadiusSup_tendsto_condition_of_sharp_scales
      hn hα hβ hAlin hSlin hS_left hapos hspos hS hdpos hdradius
      hsmall hrho hd_tendsto

/-- Product-form packaging of the perturbation-radius condition-number theorem:
    the same value is both the local product-form condition number and the
    radius-limit value. -/
theorem mixedConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_sharp_scales
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s : ℝ} {rho d : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hAlin : IsComplexVectorMapLinear A)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hS : IsMixedSubordinateNormValue νβ να S s)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l)
    (hsmall : Filter.Eventually (fun i => s * d i < 1) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0)) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue να νβ A S κ ∧
        IsMixedConditionNumberRadiusLimitValue l να νβ A S a s rho κ := by
  refine ⟨a * s, mixedConditionNumberProductValue_norm_mul_inverse_norm hA hS, ?_⟩
  exact
    mixedConditionNumberRadiusLimitValue_eq_norm_mul_inverse_norm_of_sharp_scales
      hn hα hβ hAlin hSlin hS_left hapos hspos hS hdpos hdradius
      hsmall hrho hd_tendsto

/-- Source-radius condition-number theorem with no supplied perturbation scale:
    along any eventually positive radius family `rho -> 0`, choose the sharp
    lower-witness scale `d_i = rho_i * a / 2` internally. -/
theorem mixedConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_positive_radii
    {ι : Type*} {l : Filter ι}
    {n : ℕ} {να νβ : CVec n → ℝ} {A S : ComplexVectorMap n n}
    {a s : ℝ} {rho : ι → ℝ} (hn : 0 < n)
    (hα : IsComplexVectorNorm να) (hβ : IsComplexVectorNorm νβ)
    (hAlin : IsComplexVectorMapLinear A)
    (hSlin : IsComplexVectorMapLinear S)
    (hS_left : ∀ x : CVec n, S (A x) = x)
    (hapos : 0 < a) (hspos : 0 < s)
    (hA : IsMixedSubordinateNormValue να νβ A a)
    (hS : IsMixedSubordinateNormValue νβ να S s)
    (hrho_pos : Filter.Eventually (fun i => 0 < rho i) l)
    (hrho : Filter.Tendsto rho l (nhds 0)) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue να νβ A S κ ∧
        IsMixedConditionNumberRadiusLimitValue l να νβ A S a s rho κ := by
  let d : ι → ℝ := fun i => rho i * a / 2
  have hdpos : Filter.Eventually (fun i => 0 < d i) l := by
    filter_upwards [hrho_pos] with i hrho_i
    dsimp [d]
    nlinarith [mul_pos hrho_i hapos]
  have hdradius : Filter.Eventually (fun i => d i ≤ rho i * a) l := by
    filter_upwards [hrho_pos] with i hrho_i
    dsimp [d]
    nlinarith [mul_pos hrho_i hapos]
  have hd_tendsto : Filter.Tendsto d l (nhds 0) := by
    have h := hrho.mul_const (a / 2)
    simpa [d, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hsmall : Filter.Eventually (fun i => s * d i < 1) l := by
    have hraw :
        Filter.Eventually (fun i => s * (d i * (1 : ℝ)) < 1) l :=
      eventually_radius_resolvent_small_of_tendsto_zero
        (a := (1 : ℝ)) hspos hd_tendsto
    filter_upwards [hraw] with i hi
    simpa using hi
  exact
    mixedConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_sharp_scales
      (rho := rho) (d := d) hn hα hβ hAlin hSlin hS_left hapos hspos
      hA hS hdpos hdradius hsmall hrho hd_tendsto

/-- Concrete matrix `p`-norm wrapper for the local Theorem 6.4
    perturbation-radius condition-number theorem.  The matrix inverse relation is
    still expressed as the source-facing map identity
    `Ainv (A x) = x`; a later concrete matrix-inverse API can specialize this
    hypothesis. -/
theorem complexMatrixLpConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_sharp_scales
    {ι : Type*} {l : Filter ι} {n : ℕ} (hn : 0 < n)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {A Ainv : CMatrix n n}
    {rho d : ι → ℝ}
    (hAinv_left : ∀ x : CVec n, complexMatrixVecMul Ainv (complexMatrixVecMul A x) = x)
    (hapos : 0 < complexMatrixLpNorm hn p A)
    (hspos : 0 < complexMatrixLpNorm hn p Ainv)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually
      (fun i => d i ≤ rho i * complexMatrixLpNorm hn p A) l)
    (hsmall : Filter.Eventually
      (fun i => complexMatrixLpNorm hn p Ainv * d i < 1) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0)) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue
        (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
        (complexMatrixVecMul A) (complexMatrixVecMul Ainv) κ ∧
        IsMixedConditionNumberRadiusLimitValue l
          (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
          (complexMatrixVecMul A) (complexMatrixVecMul Ainv)
          (complexMatrixLpNorm hn p A) (complexMatrixLpNorm hn p Ainv)
          rho κ := by
  have hA :
      IsMixedSubordinateNormValue
        (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
        (complexMatrixVecMul A) (complexMatrixLpNorm hn p A) := by
    simpa [IsComplexMatrixLpNormValue, IsMixedSubordinateMatrixNormValue] using
      complexMatrixLpNorm_isComplexMatrixLpNormValue (m := n) (n := n) hn p A
  have hAinv :
      IsMixedSubordinateNormValue
        (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
        (complexMatrixVecMul Ainv) (complexMatrixLpNorm hn p Ainv) := by
    simpa [IsComplexMatrixLpNormValue, IsMixedSubordinateMatrixNormValue] using
      complexMatrixLpNorm_isComplexMatrixLpNormValue (m := n) (n := n) hn p Ainv
  exact
    mixedConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_sharp_scales
      (hn := hn)
      (hα := complexVecLpNorm_isComplexVectorNorm (n := n) p)
      (hβ := complexVecLpNorm_isComplexVectorNorm (n := n) p)
      (hAlin := complexMatrixVecMul_linear A)
      (hSlin := complexMatrixVecMul_linear Ainv)
      (hS_left := hAinv_left)
      hapos hspos hA hAinv hdpos hdradius hsmall hrho hd_tendsto

/-- Finite-real convenience form of the concrete matrix `p`-norm
    perturbation-radius condition-number wrapper. -/
theorem complexMatrixLpNormOfReal_conditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_sharp_scales
    {ι : Type*} {l : Filter ι} {n : ℕ} (hn : 0 < n)
    {p : ℝ} (hp : 1 ≤ p) {A Ainv : CMatrix n n} {rho d : ι → ℝ}
    (hAinv_left : ∀ x : CVec n, complexMatrixVecMul Ainv (complexMatrixVecMul A x) = x)
    (hapos : 0 < complexMatrixLpNormOfReal hn p hp A)
    (hspos : 0 < complexMatrixLpNormOfReal hn p hp Ainv)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually
      (fun i => d i ≤ rho i * complexMatrixLpNormOfReal hn p hp A) l)
    (hsmall : Filter.Eventually
      (fun i => complexMatrixLpNormOfReal hn p hp Ainv * d i < 1) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0)) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexMatrixVecMul A) (complexMatrixVecMul Ainv) κ ∧
        IsMixedConditionNumberRadiusLimitValue l
          (complexVecLpNorm (n := n) (ENNReal.ofReal p))
          (complexVecLpNorm (n := n) (ENNReal.ofReal p))
          (complexMatrixVecMul A) (complexMatrixVecMul Ainv)
          (complexMatrixLpNormOfReal hn p hp A)
          (complexMatrixLpNormOfReal hn p hp Ainv) rho κ := by
  haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  simpa [complexMatrixLpNormOfReal] using
    complexMatrixLpConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_sharp_scales
      (hn := hn) (p := ENNReal.ofReal p) (A := A) (Ainv := Ainv)
      (rho := rho) (d := d) hAinv_left hapos hspos hdpos hdradius hsmall
      hrho hd_tendsto

/-- Concrete matrix `p`-norm condition-number radius theorem along any
    eventually positive shrinking radius family.  The sharp perturbation scales
    are chosen internally. -/
theorem complexMatrixLpConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_positive_radii
    {ι : Type*} {l : Filter ι} {n : ℕ} (hn : 0 < n)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {A Ainv : CMatrix n n} {rho : ι → ℝ}
    (hAinv_left : ∀ x : CVec n, complexMatrixVecMul Ainv (complexMatrixVecMul A x) = x)
    (hapos : 0 < complexMatrixLpNorm hn p A)
    (hspos : 0 < complexMatrixLpNorm hn p Ainv)
    (hrho_pos : Filter.Eventually (fun i => 0 < rho i) l)
    (hrho : Filter.Tendsto rho l (nhds 0)) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue
        (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
        (complexMatrixVecMul A) (complexMatrixVecMul Ainv) κ ∧
        IsMixedConditionNumberRadiusLimitValue l
          (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
          (complexMatrixVecMul A) (complexMatrixVecMul Ainv)
          (complexMatrixLpNorm hn p A) (complexMatrixLpNorm hn p Ainv)
          rho κ := by
  have hA :
      IsMixedSubordinateNormValue
        (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
        (complexMatrixVecMul A) (complexMatrixLpNorm hn p A) := by
    simpa [IsComplexMatrixLpNormValue, IsMixedSubordinateMatrixNormValue] using
      complexMatrixLpNorm_isComplexMatrixLpNormValue (m := n) (n := n) hn p A
  have hAinv :
      IsMixedSubordinateNormValue
        (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
        (complexMatrixVecMul Ainv) (complexMatrixLpNorm hn p Ainv) := by
    simpa [IsComplexMatrixLpNormValue, IsMixedSubordinateMatrixNormValue] using
      complexMatrixLpNorm_isComplexMatrixLpNormValue (m := n) (n := n) hn p Ainv
  exact
    mixedConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_positive_radii
      (hn := hn)
      (hα := complexVecLpNorm_isComplexVectorNorm (n := n) p)
      (hβ := complexVecLpNorm_isComplexVectorNorm (n := n) p)
      (hAlin := complexMatrixVecMul_linear A)
      (hSlin := complexMatrixVecMul_linear Ainv)
      (hS_left := hAinv_left)
      hapos hspos hA hAinv hrho_pos hrho

/-- Finite-real convenience form of the concrete positive-radius
    condition-number theorem. -/
theorem complexMatrixLpNormOfReal_conditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_positive_radii
    {ι : Type*} {l : Filter ι} {n : ℕ} (hn : 0 < n)
    {p : ℝ} (hp : 1 ≤ p) {A Ainv : CMatrix n n} {rho : ι → ℝ}
    (hAinv_left : ∀ x : CVec n, complexMatrixVecMul Ainv (complexMatrixVecMul A x) = x)
    (hapos : 0 < complexMatrixLpNormOfReal hn p hp A)
    (hspos : 0 < complexMatrixLpNormOfReal hn p hp Ainv)
    (hrho_pos : Filter.Eventually (fun i => 0 < rho i) l)
    (hrho : Filter.Tendsto rho l (nhds 0)) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexMatrixVecMul A) (complexMatrixVecMul Ainv) κ ∧
        IsMixedConditionNumberRadiusLimitValue l
          (complexVecLpNorm (n := n) (ENNReal.ofReal p))
          (complexVecLpNorm (n := n) (ENNReal.ofReal p))
          (complexMatrixVecMul A) (complexMatrixVecMul Ainv)
          (complexMatrixLpNormOfReal hn p hp A)
          (complexMatrixLpNormOfReal hn p hp Ainv) rho κ := by
  haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  simpa [complexMatrixLpNormOfReal] using
    complexMatrixLpConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_positive_radii
      (hn := hn) (p := ENNReal.ofReal p) (A := A) (Ainv := Ainv)
      (rho := rho) hAinv_left hapos hspos hrho_pos hrho

/-- Source-facing `A^{-1}` version of the concrete matrix `p`-norm
    perturbation-radius condition-number theorem with supplied sharp scales.
    The two-sided inverse predicate specializes the left-inverse hypothesis
    required by the local perturbation argument. -/
theorem complexMatrixLpConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_sharp_scales_of_inverse
    {ι : Type*} {l : Filter ι} {n : ℕ} (hn : 0 < n)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {A Ainv : CMatrix n n}
    {rho d : ι → ℝ}
    (hAinv : IsComplexMatrixInverse A Ainv)
    (hapos : 0 < complexMatrixLpNorm hn p A)
    (hspos : 0 < complexMatrixLpNorm hn p Ainv)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually
      (fun i => d i ≤ rho i * complexMatrixLpNorm hn p A) l)
    (hsmall : Filter.Eventually
      (fun i => complexMatrixLpNorm hn p Ainv * d i < 1) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0)) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue
        (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
        (complexMatrixVecMul A) (complexMatrixVecMul Ainv) κ ∧
        IsMixedConditionNumberRadiusLimitValue l
          (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
          (complexMatrixVecMul A) (complexMatrixVecMul Ainv)
          (complexMatrixLpNorm hn p A) (complexMatrixLpNorm hn p Ainv)
          rho κ := by
  exact
    complexMatrixLpConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_sharp_scales
      (hn := hn) (p := p) (A := A) (Ainv := Ainv) (rho := rho) (d := d)
      (isComplexMatrixLeftInverse_of_inverse hAinv)
      hapos hspos hdpos hdradius hsmall hrho hd_tendsto

/-- Finite-real source-facing `A^{-1}` version of the supplied-scale concrete
    matrix `p`-norm perturbation-radius condition-number theorem. -/
theorem complexMatrixLpNormOfReal_conditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_sharp_scales_of_inverse
    {ι : Type*} {l : Filter ι} {n : ℕ} (hn : 0 < n)
    {p : ℝ} (hp : 1 ≤ p) {A Ainv : CMatrix n n} {rho d : ι → ℝ}
    (hAinv : IsComplexMatrixInverse A Ainv)
    (hapos : 0 < complexMatrixLpNormOfReal hn p hp A)
    (hspos : 0 < complexMatrixLpNormOfReal hn p hp Ainv)
    (hdpos : Filter.Eventually (fun i => 0 < d i) l)
    (hdradius : Filter.Eventually
      (fun i => d i ≤ rho i * complexMatrixLpNormOfReal hn p hp A) l)
    (hsmall : Filter.Eventually
      (fun i => complexMatrixLpNormOfReal hn p hp Ainv * d i < 1) l)
    (hrho : Filter.Tendsto rho l (nhds 0))
    (hd_tendsto : Filter.Tendsto d l (nhds 0)) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexMatrixVecMul A) (complexMatrixVecMul Ainv) κ ∧
        IsMixedConditionNumberRadiusLimitValue l
          (complexVecLpNorm (n := n) (ENNReal.ofReal p))
          (complexVecLpNorm (n := n) (ENNReal.ofReal p))
          (complexMatrixVecMul A) (complexMatrixVecMul Ainv)
          (complexMatrixLpNormOfReal hn p hp A)
          (complexMatrixLpNormOfReal hn p hp Ainv) rho κ := by
  exact
    complexMatrixLpNormOfReal_conditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_sharp_scales
      (hn := hn) (hp := hp) (A := A) (Ainv := Ainv) (rho := rho) (d := d)
      (isComplexMatrixLeftInverse_of_inverse hAinv)
      hapos hspos hdpos hdradius hsmall hrho hd_tendsto

/-- Source-facing `A^{-1}` version of the concrete matrix `p`-norm
    condition-number theorem along any eventually positive shrinking radius
    family.  The sharp perturbation scales are chosen internally. -/
theorem complexMatrixLpConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_positive_radii_of_inverse
    {ι : Type*} {l : Filter ι} {n : ℕ} (hn : 0 < n)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {A Ainv : CMatrix n n} {rho : ι → ℝ}
    (hAinv : IsComplexMatrixInverse A Ainv)
    (hapos : 0 < complexMatrixLpNorm hn p A)
    (hspos : 0 < complexMatrixLpNorm hn p Ainv)
    (hrho_pos : Filter.Eventually (fun i => 0 < rho i) l)
    (hrho : Filter.Tendsto rho l (nhds 0)) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue
        (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
        (complexMatrixVecMul A) (complexMatrixVecMul Ainv) κ ∧
        IsMixedConditionNumberRadiusLimitValue l
          (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := n) p)
          (complexMatrixVecMul A) (complexMatrixVecMul Ainv)
          (complexMatrixLpNorm hn p A) (complexMatrixLpNorm hn p Ainv)
          rho κ := by
  exact
    complexMatrixLpConditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_positive_radii
      (hn := hn) (p := p) (A := A) (Ainv := Ainv) (rho := rho)
      (isComplexMatrixLeftInverse_of_inverse hAinv)
      hapos hspos hrho_pos hrho

/-- Finite-real source-facing `A^{-1}` version of the concrete positive-radius
    condition-number theorem. -/
theorem complexMatrixLpNormOfReal_conditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_positive_radii_of_inverse
    {ι : Type*} {l : Filter ι} {n : ℕ} (hn : 0 < n)
    {p : ℝ} (hp : 1 ≤ p) {A Ainv : CMatrix n n} {rho : ι → ℝ}
    (hAinv : IsComplexMatrixInverse A Ainv)
    (hapos : 0 < complexMatrixLpNormOfReal hn p hp A)
    (hspos : 0 < complexMatrixLpNormOfReal hn p hp Ainv)
    (hrho_pos : Filter.Eventually (fun i => 0 < rho i) l)
    (hrho : Filter.Tendsto rho l (nhds 0)) :
    ∃ κ : ℝ,
      IsMixedConditionNumberProductValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexMatrixVecMul A) (complexMatrixVecMul Ainv) κ ∧
        IsMixedConditionNumberRadiusLimitValue l
          (complexVecLpNorm (n := n) (ENNReal.ofReal p))
          (complexVecLpNorm (n := n) (ENNReal.ofReal p))
          (complexMatrixVecMul A) (complexMatrixVecMul Ainv)
          (complexMatrixLpNormOfReal hn p hp A)
          (complexMatrixLpNormOfReal hn p hp Ainv) rho κ := by
  exact
    complexMatrixLpNormOfReal_conditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_positive_radii
      (hn := hn) (hp := hp) (A := A) (Ainv := Ainv) (rho := rho)
      (isComplexMatrixLeftInverse_of_inverse hAinv)
      hapos hspos hrho_pos hrho

end NumStability
