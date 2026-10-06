import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.RingTheory.Algebraic.Basic
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results

/-!
# Chapter02 Section10 Tablemaker FiniteSeparation Basic

Canonical destination for material split out of
`NumStability.Analysis.HighamChapter2Tablemaker` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

namespace FloatingPointFormat

/-- Every normalized value is the real cast of a rational number. -/
theorem normalizedValue_exists_ratCast (fmt : FloatingPointFormat)
    (negative : Bool) (m : ℕ) (e : ℤ) :
    ∃ q : ℚ, (q : ℝ) = fmt.normalizedValue negative m e := by
  cases negative with
  | false =>
      refine ⟨(m : ℚ) * (fmt.beta : ℚ) ^ (e - (fmt.t : ℤ)), ?_⟩
      simp [normalizedValue, signValue, betaR, Rat.cast_zpow]
  | true =>
      refine ⟨-(m : ℚ) * (fmt.beta : ℚ) ^ (e - (fmt.t : ℤ)), ?_⟩
      simp [normalizedValue, signValue, betaR, Rat.cast_zpow]

/-- Every subnormal value is the real cast of a rational number. -/
theorem subnormalValue_exists_ratCast (fmt : FloatingPointFormat)
    (negative : Bool) (m : ℕ) :
    ∃ q : ℚ, (q : ℝ) = fmt.subnormalValue negative m := by
  cases negative with
  | false =>
      refine ⟨(m : ℚ) * (fmt.beta : ℚ) ^
        (fmt.emin - (fmt.t : ℤ)), ?_⟩
      simp [subnormalValue, signValue, betaR, Rat.cast_zpow]
  | true =>
      refine ⟨-(m : ℚ) * (fmt.beta : ℚ) ^
        (fmt.emin - (fmt.t : ℤ)), ?_⟩
      simp [subnormalValue, signValue, betaR, Rat.cast_zpow]

/-- Every member of a finite floating-point format is rational. -/
theorem finiteSystem_exists_ratCast
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    ∃ q : ℚ, (q : ℝ) = x := by
  rcases hx with rfl | hnormal | hsubnormal
  · exact ⟨0, by norm_num⟩
  · rcases hnormal with ⟨negative, m, e, _hm, _he, rfl⟩
    exact fmt.normalizedValue_exists_ratCast negative m e
  · rcases hsubnormal with ⟨negative, m, _hm, rfl⟩
    exact fmt.subnormalValue_exists_ratCast negative m

/-- Consequently every finite floating-point value is algebraic over `ℚ`. -/
theorem finiteSystem_isAlgebraic_rat
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    IsAlgebraic ℚ x := by
  rcases fmt.finiteSystem_exists_ratCast hx with ⟨q, rfl⟩
  exact isAlgebraic_rat ℚ q

/-- The midpoint of any two finite floating-point values is rational. -/
theorem finiteSystem_midpoint_exists_ratCast
    {fmt : FloatingPointFormat} {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b) :
    ∃ q : ℚ, (q : ℝ) = (a + b) / 2 := by
  rcases fmt.finiteSystem_exists_ratCast ha with ⟨qa, rfl⟩
  rcases fmt.finiteSystem_exists_ratCast hb with ⟨qb, rfl⟩
  refine ⟨(qa + qb) / 2, ?_⟩
  push_cast
  ring

/-- Hence a midpoint between finite floating-point values is algebraic. -/
theorem finiteSystem_midpoint_isAlgebraic_rat
    {fmt : FloatingPointFormat} {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b) :
    IsAlgebraic ℚ ((a + b) / 2) := by
  rcases fmt.finiteSystem_midpoint_exists_ratCast ha hb with ⟨q, hq⟩
  rw [← hq]
  exact isAlgebraic_rat ℚ q

end FloatingPointFormat

/-- The exact Hermite--Lindemann consequence needed by Higham's paragraph.
It is named as a proposition because the current dependency stack does not
provide the theorem. -/
def Higham2LindemannExpProperty : Prop :=
  ∀ x : ℝ, x ≠ 0 → IsAlgebraic ℚ x → Transcendental ℚ (Real.exp x)

/-- Conditional closure of the machine-number and halfway-case separation.

All finite-format reasoning is discharged here.  The only external premise is
`Higham2LindemannExpProperty`; the subsequent claim that sufficiently many
computed digits determine rounding also requires a specified convergent
elementary-function algorithm and is deliberately not hidden in this result.
-/
theorem higham2_lindemann_exp_not_machine_or_midpoint
    (hLindemann : Higham2LindemannExpProperty)
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) (hx0 : x ≠ 0) :
    ¬ fmt.finiteSystem (Real.exp x) ∧
      ∀ a b : ℝ, fmt.finiteSystem a → fmt.finiteSystem b →
        Real.exp x ≠ (a + b) / 2 := by
  have hxalg : IsAlgebraic ℚ x := fmt.finiteSystem_isAlgebraic_rat hx
  have hexp : Transcendental ℚ (Real.exp x) := hLindemann x hx0 hxalg
  constructor
  · intro hfinite
    exact hexp (fmt.finiteSystem_isAlgebraic_rat hfinite)
  · intro a b ha hb heq
    apply hexp
    rw [heq]
    exact fmt.finiteSystem_midpoint_isAlgebraic_rat ha hb

end NumStability

end
