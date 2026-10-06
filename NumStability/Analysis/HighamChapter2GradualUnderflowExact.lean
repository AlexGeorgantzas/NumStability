/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/

import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

namespace FloatingPointFormat

/-!
# Higham Chapter 2, Problem 2.19: exact underflowing sums and differences

Higham's body text on printed page 45 uses Problem 2.19 to remove the
no-underflow proviso from Theorems 2.4 and 2.5.  The printed problem asks for
the more general Hauser fact: with gradual underflow, an underflowing `x ± y`
of two floating-point operands is exact.

The key source bridge is not a rounding estimate.  Every finite value is an
integer multiple of the smallest subnormal spacing.  A sum or difference in
the underflow range has a coefficient smaller than the first normal mantissa,
and hence is itself a finite (zero or subnormal) value.  Correct rounding
therefore fixes it exactly.
-/

/-- Every finite value lies on the common lattice whose spacing is the
smallest positive subnormal magnitude.  This includes normalized values: their
exponent is shifted down to `emin` and the corresponding radix power is moved
into the integer coefficient. -/
theorem finiteSystem_exists_int_mul_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {x : Real}
    (hx : fmt.finiteSystem x) :
    ∃ k : Int, x = (k : Real) * fmt.minSubnormalMagnitude := by
  rcases hx with rfl | hnormal | hsubnormal
  · exact ⟨0, by simp⟩
  · rcases hnormal with ⟨negative, m, e, hm, he, rfl⟩
    let shift : Nat := Int.toNat (e - fmt.emin)
    have hshift_cast : (shift : Int) = e - fmt.emin := by
      have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
      simpa [shift] using Int.toNat_of_nonneg hnonneg
    have hendpoint : e - (shift : Int) = fmt.emin := by
      omega
    refine ⟨fmt.signedMantissaCoeff negative (m * fmt.beta ^ shift), ?_⟩
    rw [fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
      negative m shift e hendpoint]
    cases negative <;>
      simp [subnormalValue, signValue, signedMantissaCoeff,
        minSubnormalMagnitude]
  · rcases hsubnormal with ⟨negative, m, hm, rfl⟩
    refine ⟨fmt.signedMantissaCoeff negative m, ?_⟩
    cases negative <;>
      simp [subnormalValue, signValue, signedMantissaCoeff,
        minSubnormalMagnitude]

/-- Hauser's lattice lemma for addition: two finite operands whose exact sum
lies below the smallest normal magnitude have a finite exact sum. -/
theorem finiteSystem_add_finiteSystem_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : Real}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hunder : fmt.finiteUnderflowRange (x + y)) :
    fmt.finiteSystem (x + y) := by
  obtain ⟨kx, hkx⟩ :=
    fmt.finiteSystem_exists_int_mul_minSubnormalMagnitude hx
  obtain ⟨ky, hky⟩ :=
    fmt.finiteSystem_exists_int_mul_minSubnormalMagnitude hy
  let k : Int := kx + ky
  have hrepr : x + y = (k : Real) * fmt.minSubnormalMagnitude := by
    rw [hkx, hky]
    simp [k]
    ring
  have heta_pos : 0 < fmt.minSubnormalMagnitude :=
    fmt.minSubnormalMagnitude_pos
  have hcoefficient_real :
      |(k : Real)| < (fmt.minNormalMantissa : Real) := by
    rw [finiteUnderflowRange, hrepr,
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude,
      abs_mul, abs_of_pos heta_pos] at hunder
    exact lt_of_mul_lt_mul_right hunder (le_of_lt heta_pos)
  have hnatabs_cast : ((k.natAbs : Nat) : Real) = |(k : Real)| := by
    norm_num [Int.cast_abs]
  have hk_small_real :
      ((k.natAbs : Nat) : Real) < (fmt.minNormalMantissa : Real) := by
    rw [hnatabs_cast]
    exact hcoefficient_real
  have hk_small : k.natAbs < fmt.minNormalMantissa := by
    exact_mod_cast hk_small_real
  have hk_mantissa : k.natAbs < fmt.beta ^ fmt.t :=
    lt_trans hk_small fmt.minNormalMantissa_lt_mantissaBound
  have hemin : fmt.exponentInRange fmt.emin :=
    ⟨le_rfl, fmt.emin_le_emax⟩
  have hfinite :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := false) (k := k) (e := fmt.emin) hemin hk_mantissa
  rw [hrepr]
  simpa [signValue, minSubnormalMagnitude] using hfinite

/-- Subtraction form of the Hauser lattice lemma. -/
theorem finiteSystem_sub_finiteSystem_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : Real}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hunder : fmt.finiteUnderflowRange (x - y)) :
    fmt.finiteSystem (x - y) := by
  have hyneg : fmt.finiteSystem (-y) := fmt.finiteSystem_neg hy
  have hunder' : fmt.finiteUnderflowRange (x + (-y)) := by
    simpa [sub_eq_add_neg] using hunder
  simpa [sub_eq_add_neg] using
    fmt.finiteSystem_add_finiteSystem_of_finiteUnderflowRange hx hyneg hunder'

/-- **Higham Problem 2.19 (Hauser), addition.**  Under gradual underflow,
correct round-to-even addition of finite operands is exact whenever the exact
sum lies in the underflow range. -/
theorem finiteRoundToEvenOp_add_eq_exact_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : Real}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hunder : fmt.finiteUnderflowRange (x + y)) :
    fmt.finiteRoundToEvenOp BasicOp.add x y = x + y := by
  have hfinite : fmt.finiteSystem (BasicOp.exact BasicOp.add x y) := by
    simpa [BasicOp.exact] using
      fmt.finiteSystem_add_finiteSystem_of_finiteUnderflowRange hx hy hunder
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite)

/-- **Higham Problem 2.19 (Hauser), subtraction.**  Under gradual underflow,
correct round-to-even subtraction of finite operands is exact whenever the
exact difference lies in the underflow range. -/
theorem finiteRoundToEvenOp_sub_eq_exact_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : Real}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hunder : fmt.finiteUnderflowRange (x - y)) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfinite : fmt.finiteSystem (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      fmt.finiteSystem_sub_finiteSystem_of_finiteUnderflowRange hx hy hunder
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite)

/-- Gradual-underflow form of Higham Theorem 2.4: the printed Ferguson
magnitude/exponent condition already reconstructs a finite exact difference,
so the explicit no-underflow proviso is unnecessary. -/
theorem finiteRoundToEvenOp_sub_eq_exact_of_fergusonMagnitudeExponentConditionLe_gradualUnderflow
    {fmt : FloatingPointFormat} {x y : Real}
    (hcond : fmt.fergusonMagnitudeExponentConditionLe x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  have hfinite : fmt.finiteSystem (BasicOp.exact BasicOp.sub x y) := by
    simpa [BasicOp.exact] using
      fmt.fergusonMagnitudeExponentConditionLe_sub_finiteSystem hcond
  simpa [BasicOp.exact] using
    (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem hfinite)

/-- Joint body-level corollary: gradual underflow removes the proviso from
Ferguson's Theorem 2.4 and Sterbenz's Theorem 2.5. -/
theorem higham2_gradualUnderflow_removes_theorems2_4_and2_5_provisos
    {fmt : FloatingPointFormat} {x y : Real}
    (hx : fmt.finiteSystem x) (hy : fmt.finiteSystem y)
    (hferguson : fmt.fergusonMagnitudeExponentConditionLe x y)
    (hsterbenz : fmt.sterbenzRatioConditionLe x y) :
    fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y ∧
      fmt.finiteRoundToEvenOp BasicOp.sub x y = x - y := by
  exact ⟨
    fmt.finiteRoundToEvenOp_sub_eq_exact_of_fergusonMagnitudeExponentConditionLe_gradualUnderflow
      hferguson,
    fmt.finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioConditionLe
      hx hy hsterbenz⟩

end FloatingPointFormat

end NumStability
