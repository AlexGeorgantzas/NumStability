-- Analysis/FusedMultiplyAdd.lean
--
-- Finite single-rounding FMA surface for Higham Chapter 2, §2.6.

import NumStability.Analysis.FloatingPointArithmetic

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

/-- Exact real value computed before the single final FMA rounding. -/
def fusedMultiplyAddExact (x y z : ℝ) : ℝ :=
  x * y + z

namespace FloatingPointFormat

/-- Source-facing finite round-to-even FMA: round the exact `x*y+z` once at the
end. -/
def finiteRoundToEvenFMA (fmt : FloatingPointFormat) (x y z : ℝ) : ℝ :=
  fmt.finiteRoundToEven (fusedMultiplyAddExact x y z)

/-- Source-facing finite FMA parameterized by an IEEE rounding mode. -/
def finiteRoundToModeFMA
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (x y z : ℝ) : ℝ :=
  fmt.finiteRoundToMode mode (fusedMultiplyAddExact x y z)

theorem finiteRoundToModeFMA_nearestEven
    (fmt : FloatingPointFormat) (x y z : ℝ) :
    fmt.finiteRoundToModeFMA IeeeRoundingMode.nearestEven x y z =
      fmt.finiteRoundToEvenFMA x y z := rfl

/-- The finite FMA wrapper is a single final rounding of the exact product-plus
addend. -/
theorem finiteRoundToEvenFMA_eq_round_exact
    (fmt : FloatingPointFormat) (x y z : ℝ) :
    fmt.finiteRoundToEvenFMA x y z =
      fmt.finiteRoundToEven (x * y + z) := rfl

/-- If the exact fused result is representable in the finite system, the
finite FMA returns it exactly. -/
theorem finiteRoundToEvenFMA_eq_exact_of_finiteSystem
    {fmt : FloatingPointFormat} {x y z : ℝ}
    (hxyz : fmt.finiteSystem (fusedMultiplyAddExact x y z)) :
    fmt.finiteRoundToEvenFMA x y z = fusedMultiplyAddExact x y z := by
  exact fmt.finiteRoundToEven_eq_self_of_finiteSystem hxyz

/-- In the finite-normal, non-exceptional case, the single-rounded finite FMA
satisfies the strict standard-model relative-error equation. -/
theorem finiteRoundToEvenFMA_standardModel_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x y z : ℝ}
    (hxyz : fmt.finiteNormalRange (fusedMultiplyAddExact x y z)) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        fmt.finiteRoundToEvenFMA x y z =
          fusedMultiplyAddExact x y z * (1 + δ) := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hxyz with
    ⟨δ, _hround, hδ, hwit⟩
  exact
    ⟨δ, hδ,
      by simpa [finiteRoundToEvenFMA, fusedMultiplyAddExact,
        signedRelErrorWitness] using hwit⟩

theorem finiteRoundToEvenFMA_inverseRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x y z : ℝ}
    (hxyz : fmt.finiteNormalRange (fusedMultiplyAddExact x y z)) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite (fusedMultiplyAddExact x y z)
          (fmt.finiteRoundToEvenFMA x y z) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteRoundToEvenFMA x y z)
            (fusedMultiplyAddExact x y z) δ := by
  rcases
    fmt.finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange
      hxyz with
    ⟨δ, hround, hδ, hwit⟩
  exact
    ⟨δ,
      by simpa [finiteRoundToEvenFMA, fusedMultiplyAddExact] using hround,
      hδ,
      by simpa [finiteRoundToEvenFMA, fusedMultiplyAddExact] using hwit⟩

/-- Higham Chapter 2, Problem 2.26 product-decomposition core: if the FMA
correction `x*y - a` is exactly representable, then `a` plus the rounded FMA
correction is exactly the real product `x*y`. -/
theorem finiteRoundToEvenFMA_product_correction_add_eq_product_of_finiteSystem
    {fmt : FloatingPointFormat} {x y a : ℝ}
    (hcorr : fmt.finiteSystem (x * y - a)) :
    a + fmt.finiteRoundToEvenFMA x y (-a) = x * y := by
  have hcorr' : fmt.finiteSystem (fusedMultiplyAddExact x y (-a)) := by
    simpa [fusedMultiplyAddExact, sub_eq_add_neg] using hcorr
  rw [fmt.finiteRoundToEvenFMA_eq_exact_of_finiteSystem hcorr']
  rw [fusedMultiplyAddExact]
  ring

/-- Source-shaped Problem 2.26 wrapper: take the high product to be the ordinary
finite round-to-even product and the low correction to be a single FMA.  If the
correction is representable, the two-term expansion is exact. -/
theorem finiteRoundToEvenFMA_product_expansion_with_rounded_product
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hcorr :
      fmt.finiteSystem (x * y - fmt.finiteRoundToEvenOp BasicOp.mul x y)) :
    fmt.finiteRoundToEvenOp BasicOp.mul x y +
        fmt.finiteRoundToEvenFMA x y
          (-(fmt.finiteRoundToEvenOp BasicOp.mul x y)) =
      x * y := by
  exact
    fmt.finiteRoundToEvenFMA_product_correction_add_eq_product_of_finiteSystem
      hcorr

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

/-- Left-to-right dot-product loop using one fused multiply-add per term.
The state records both the computed value and the number of rounded
operations actually issued by the recurrence. -/
def finiteFMADotProductListLoop (fmt : FloatingPointFormat) :
    ℝ × ℕ → List (ℝ × ℝ) → ℝ × ℕ
  | state, [] => state
  | state, xy :: rest =>
      finiteFMADotProductListLoop fmt
        (fmt.finiteRoundToEvenFMA xy.1 xy.2 state.1, state.2 + 1) rest

/-- The FMA dot-product trace starts from an exact zero accumulator. -/
def finiteFMADotProductListTrace (fmt : FloatingPointFormat)
    (terms : List (ℝ × ℝ)) : ℝ × ℕ :=
  fmt.finiteFMADotProductListLoop (0, 0) terms

theorem finiteFMADotProductListLoop_count
    (fmt : FloatingPointFormat) (state : ℝ × ℕ)
    (terms : List (ℝ × ℝ)) :
    (fmt.finiteFMADotProductListLoop state terms).2 =
      state.2 + terms.length := by
  induction terms generalizing state with
  | nil => simp [finiteFMADotProductListLoop]
  | cons xy rest ih =>
      simp only [List.length_cons]
      rw [finiteFMADotProductListLoop, ih]
      omega

/-- The actual FMA recurrence commits exactly one rounding per product term. -/
theorem finiteFMADotProductListTrace_count
    (fmt : FloatingPointFormat) (terms : List (ℝ × ℝ)) :
    (fmt.finiteFMADotProductListTrace terms).2 = terms.length := by
  rw [finiteFMADotProductListTrace, finiteFMADotProductListLoop_count]
  simp

/-- Tail loop for the conventional dot product.  Each new term first rounds
its product and then rounds its addition to the accumulator. -/
def finiteConventionalDotProductListTailLoop (fmt : FloatingPointFormat) :
    ℝ × ℕ → List (ℝ × ℝ) → ℝ × ℕ
  | state, [] => state
  | state, xy :: rest =>
      let product := fmt.finiteRoundToEvenOp BasicOp.mul xy.1 xy.2
      let sum := fmt.finiteRoundToEvenOp BasicOp.add state.1 product
      finiteConventionalDotProductListTailLoop fmt (sum, state.2 + 2) rest

/-- Conventional nonempty dot-product trace: one rounded first product,
followed by one rounded product and one rounded addition for every tail term. -/
def finiteConventionalDotProductListTrace (fmt : FloatingPointFormat) :
    List (ℝ × ℝ) → ℝ × ℕ
  | [] => (0, 0)
  | xy :: rest =>
      fmt.finiteConventionalDotProductListTailLoop
        (fmt.finiteRoundToEvenOp BasicOp.mul xy.1 xy.2, 1) rest

theorem finiteConventionalDotProductListTailLoop_count
    (fmt : FloatingPointFormat) (state : ℝ × ℕ)
    (terms : List (ℝ × ℝ)) :
    (fmt.finiteConventionalDotProductListTailLoop state terms).2 =
      state.2 + 2 * terms.length := by
  induction terms generalizing state with
  | nil => simp [finiteConventionalDotProductListTailLoop]
  | cons xy rest ih =>
      simp only [List.length_cons]
      rw [finiteConventionalDotProductListTailLoop, ih]
      omega

/-- The actual conventional recurrence for a nonempty `n`-term dot product
commits `2*n - 1` rounded operations. -/
theorem finiteConventionalDotProductListTrace_count
    (fmt : FloatingPointFormat) (first : ℝ × ℝ)
    (rest : List (ℝ × ℝ)) :
    (fmt.finiteConventionalDotProductListTrace (first :: rest)).2 =
      2 * (first :: rest).length - 1 := by
  rw [finiteConventionalDotProductListTrace,
    finiteConventionalDotProductListTailLoop_count]
  simp
  omega

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
