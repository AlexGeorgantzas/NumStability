import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeValue
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.StandardModel
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


































































































/-! ## FMA versus conventional dot-product rounding counts -/



























































































end FloatingPointFormat

end

end NumStability
