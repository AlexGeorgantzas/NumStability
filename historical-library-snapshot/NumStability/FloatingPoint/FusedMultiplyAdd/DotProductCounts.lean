import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
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














end FloatingPointFormat

end

end NumStability
