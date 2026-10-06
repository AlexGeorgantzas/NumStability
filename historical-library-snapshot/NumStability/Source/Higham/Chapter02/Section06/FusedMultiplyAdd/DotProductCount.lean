import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.FloatingPoint.FusedMultiplyAdd.DotProductCounts

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


































































































































































































/-! ## FMA versus conventional dot-product rounding counts -/














































































/-- Source-facing closure of Higham Section 2.6's exact operation-count
comparison: an `n`-term FMA inner product has `n` rounding sites, while the
usual nonempty multiply-then-add trace has `2*n - 1`. -/
theorem higham2_fma_dotProduct_rounding_count_savings
    (fmt : FloatingPointFormat) (first : ℝ × ℝ)
    (rest : List (ℝ × ℝ)) :
    let terms := first :: rest
    (fmt.finiteFMADotProductListTrace terms).2 = terms.length ∧
      (fmt.finiteConventionalDotProductListTrace terms).2 =
        2 * terms.length - 1 := by
  exact ⟨fmt.finiteFMADotProductListTrace_count (first :: rest),
    fmt.finiteConventionalDotProductListTrace_count first rest⟩

end FloatingPointFormat

end

end NumStability
