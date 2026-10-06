import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.Rounding
import NumStability.FloatingPoint.FusedMultiplyAdd.Core
import NumStability.FloatingPoint.Model

-- Analysis/FusedMultiplyAdd.lean
--
-- Finite single-rounding FMA surface for Higham Chapter 2, §2.6.



namespace NumStability

noncomputable section

/-!
# Fused Multiply-Add

Higham Chapter 2, §2.6 notes that a fused multiply-add forms `x*y + z` as
though it were a single floating-point operation, with one rounding at the end.
This file records the finite real-valued theorem surface for that statement.
It is not a full IEEE FMA semantics: exception flags, signed zeros, infinities,
NaNs, traps, and payload behavior remain in the IEEE ledger.
-/





namespace FloatingPointFormat

































































































/-- Corrected source-facing form of Higham Chapter 2, Section 2.6 and
Problem 2.26.  Two FMAs produce an exact two-term product expansion provided
the low correction is representable in the finite format.  This condition is
essential in the presence of deep gradual underflow; see
`higham2_twoFMA_productExpansion_source_discrepancy_ieeeSingle` below. -/
theorem higham2_twoFMA_productExpansion_corrected
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcorr :
      fmt.finiteSystem (x * y - fmt.finiteRoundToEvenOp BasicOp.mul x y)) :
    fmt.finiteRoundToEvenOp BasicOp.mul x y +
        fmt.finiteRoundToEvenFMA x y
          (-(fmt.finiteRoundToEvenOp BasicOp.mul x y)) =
      x * y :=
  fmt.finiteRoundToEvenFMA_product_expansion_with_rounded_product hcorr

/-- Deep-underflow obstruction to the unconditional two-FMA product claim.

Let `eta` be the smallest positive subnormal.  If `eta < 1/2`, then `eta^2`
is strictly inside the round-to-zero cell.  Consequently both the ordinary
rounded high product and the FMA-computed low correction are zero, even though
the exact product is positive.  The result also records that `eta` itself is a
finite representable input. -/
theorem twoFMA_productExpansion_deepUnderflow_counterexample
    (fmt : FloatingPointFormat)
    (hsub : fmt.subnormalMantissa 1)
    (heta : fmt.minSubnormalMagnitude < (1 / 2 : ℝ)) :
    let eta := fmt.minSubnormalMagnitude
    fmt.finiteSystem eta ∧
      fmt.finiteRoundToEvenOp BasicOp.mul eta eta = 0 ∧
      fmt.finiteRoundToEvenFMA eta eta
          (-(fmt.finiteRoundToEvenOp BasicOp.mul eta eta)) = 0 ∧
      fmt.finiteRoundToEvenOp BasicOp.mul eta eta +
          fmt.finiteRoundToEvenFMA eta eta
            (-(fmt.finiteRoundToEvenOp BasicOp.mul eta eta)) ≠
        eta * eta := by
  let eta := fmt.minSubnormalMagnitude
  have heta_pos : 0 < eta := fmt.minSubnormalMagnitude_pos
  have heta_fin : fmt.finiteSystem eta :=
    Or.inr (Or.inr
      (fmt.minSubnormalMagnitude_mem_subnormalSystem_of_subnormalMantissa_one hsub))
  have hsmall : |eta * eta| < (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
    rw [abs_of_pos (mul_pos heta_pos heta_pos)]
    dsimp [eta]
    nlinarith
  have hround_zero : fmt.finiteRoundToEven (eta * eta) = 0 :=
    fmt.nearestRoundingToFinite_eq_zero_of_abs_lt_half_minSubnormalMagnitude
      (fmt.finiteRoundToEven_nearestRoundingToFinite (eta * eta)) hsmall
  have hmul_zero :
      fmt.finiteRoundToEvenOp BasicOp.mul eta eta = 0 := by
    simpa [finiteRoundToEvenOp, BasicOp.exact] using hround_zero
  have hfma_zero :
      fmt.finiteRoundToEvenFMA eta eta
          (-(fmt.finiteRoundToEvenOp BasicOp.mul eta eta)) = 0 := by
    rw [hmul_zero]
    simpa [finiteRoundToEvenFMA, fusedMultiplyAddExact] using hround_zero
  have hfma_zero_of_zero : fmt.finiteRoundToEvenFMA eta eta 0 = 0 := by
    simpa [hmul_zero] using hfma_zero
  change fmt.finiteSystem eta ∧
    fmt.finiteRoundToEvenOp BasicOp.mul eta eta = 0 ∧
    fmt.finiteRoundToEvenFMA eta eta
        (-(fmt.finiteRoundToEvenOp BasicOp.mul eta eta)) = 0 ∧
    fmt.finiteRoundToEvenOp BasicOp.mul eta eta +
        fmt.finiteRoundToEvenFMA eta eta
          (-(fmt.finiteRoundToEvenOp BasicOp.mul eta eta)) ≠ eta * eta
  refine ⟨heta_fin, hmul_zero, hfma_zero, ?_⟩
  rw [hmul_zero, neg_zero, hfma_zero_of_zero, zero_add]
  exact ne_of_lt (mul_pos heta_pos heta_pos)

/-- IEEE single precision has a genuine first positive subnormal. -/
theorem ieeeSingleFormat_subnormalMantissa_one :
    ieeeSingleFormat.subnormalMantissa 1 := by
  norm_num [subnormalMantissa, ieeeSingleFormat, minNormalMantissa]

/-- The smallest IEEE-single subnormal is far below one half. -/
theorem ieeeSingleFormat_minSubnormalMagnitude_lt_half :
    ieeeSingleFormat.minSubnormalMagnitude < (1 / 2 : ℝ) := by
  norm_num [minSubnormalMagnitude, ieeeSingleFormat, betaR, zpow_neg]

/-- Formal source discrepancy for the unconditional wording in Higham
Chapter 2, Section 2.6 and Problem 2.26.  With both inputs equal to the smallest
positive IEEE-single subnormal, the returned high-plus-low expansion is not
the exact product. -/
theorem higham2_twoFMA_productExpansion_source_discrepancy_ieeeSingle :
    let fmt := ieeeSingleFormat
    let eta := fmt.minSubnormalMagnitude
    fmt.finiteSystem eta ∧
      fmt.finiteRoundToEvenOp BasicOp.mul eta eta = 0 ∧
      fmt.finiteRoundToEvenFMA eta eta
          (-(fmt.finiteRoundToEvenOp BasicOp.mul eta eta)) = 0 ∧
      fmt.finiteRoundToEvenOp BasicOp.mul eta eta +
          fmt.finiteRoundToEvenFMA eta eta
            (-(fmt.finiteRoundToEvenOp BasicOp.mul eta eta)) ≠
        eta * eta := by
  exact twoFMA_productExpansion_deepUnderflow_counterexample
    ieeeSingleFormat ieeeSingleFormat_subnormalMantissa_one
      ieeeSingleFormat_minSubnormalMagnitude_lt_half

/-! ## FMA versus conventional dot-product rounding counts -/



























































































end FloatingPointFormat

end

end NumStability
