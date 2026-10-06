import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.RingTheory.Algebraic.Basic
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Source.Higham.Chapter02.Section10.Tablemaker.FiniteSeparation.Basic
import NumStability.Upstream.Lindemann.Basic

/-!
# Chapter02 Section10 Tablemaker HermiteLindemann Basic

Canonical destination for material split out of
`NumStability.Analysis.HighamChapter2Lindemann` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Finset

noncomputable section

namespace NumStability

/-- Real Hermite--Lindemann, in the exact coefficient-ring form used by the
existing Chapter 2 tablemaker interface. -/
theorem higham2_real_exp_transcendental
    {x : ℝ} (hx0 : x ≠ 0) (hxalg : IsAlgebraic ℚ x) :
    Transcendental ℚ (Real.exp x) := by
  letI : Algebra.IsAlgebraic ℤ ℚ :=
    IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hxcQ : IsAlgebraic ℚ (x : ℂ) := hxalg.algebraMap
  have hxcZ : IsAlgebraic ℤ (x : ℂ) := hxcQ.restrictScalars ℤ
  have htransC : Transcendental ℤ (Complex.exp (x : ℂ)) :=
    transcendental_exp (Complex.ofReal_ne_zero.mpr hx0) hxcZ
  intro hexpQ
  have hexpCQ : IsAlgebraic ℚ ((Real.exp x : ℝ) : ℂ) := hexpQ.algebraMap
  have hexpCZ : IsAlgebraic ℤ ((Real.exp x : ℝ) : ℂ) :=
    hexpCQ.restrictScalars ℤ
  apply htransC
  simpa only [Complex.ofReal_exp] using hexpCZ

/-- The formerly external Chapter 2 Lindemann premise is now discharged. -/
theorem higham2_lindemannExpProperty : Higham2LindemannExpProperty :=
  fun _x hx0 hxalg ↦ higham2_real_exp_transcendental hx0 hxalg

/-- Unconditional source-facing exclusion of machine values and halfway
values for the exponential of a nonzero finite machine input. -/
theorem higham2_exp_not_machine_or_midpoint
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) (hx0 : x ≠ 0) :
    ¬ fmt.finiteSystem (Real.exp x) ∧
      ∀ a b : ℝ, fmt.finiteSystem a → fmt.finiteSystem b →
        Real.exp x ≠ (a + b) / 2 :=
  higham2_lindemann_exp_not_machine_or_midpoint
    higham2_lindemannExpProperty hx hx0

namespace FloatingPointFormat

/-- A finite enumeration containing every normalized value of `fmt`.
The filter in `finiteValues` below removes parameter tuples that do not satisfy
the normalized-mantissa predicate. -/
noncomputable def normalizedValueCandidates
    (fmt : FloatingPointFormat) : Finset ℝ := by
  classical
  exact
    ((((Finset.univ : Finset Bool).product
          (Finset.range (fmt.beta ^ fmt.t))).product
        (Finset.Icc fmt.emin fmt.emax)).image fun p ↦
      fmt.normalizedValue p.1.1 p.1.2 p.2)

/-- A finite enumeration containing every subnormal value of `fmt`. -/
noncomputable def subnormalValueCandidates
    (fmt : FloatingPointFormat) : Finset ℝ := by
  classical
  exact
    (((Finset.univ : Finset Bool).product
        (Finset.range fmt.minNormalMantissa)).image fun p ↦
      fmt.subnormalValue p.1 p.2)

/-- A finite parameter-generated superset of the finite machine values. -/
noncomputable def finiteValueCandidates
    (fmt : FloatingPointFormat) : Finset ℝ := by
  classical
  exact {0} ∪ fmt.normalizedValueCandidates ∪ fmt.subnormalValueCandidates

theorem finiteSystem_mem_finiteValueCandidates
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    x ∈ fmt.finiteValueCandidates := by
  classical
  rcases hx with rfl | hnormal | hsubnormal
  · simp [finiteValueCandidates]
  · rcases hnormal with ⟨negative, m, e, hm, he, rfl⟩
    have hp : ((negative, m), e) ∈
        (((Finset.univ : Finset Bool).product
          (Finset.range (fmt.beta ^ fmt.t))).product
            (Finset.Icc fmt.emin fmt.emax)) := by
      simpa [FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.exponentInRange] using
        (show fmt.mantissaInRange m ∧ fmt.exponentInRange e from ⟨hm.2, he⟩)
    have hv : fmt.normalizedValue negative m e ∈
        fmt.normalizedValueCandidates := by
      exact Finset.mem_image.mpr ⟨((negative, m), e), hp, rfl⟩
    simp [finiteValueCandidates, hv]
  · rcases hsubnormal with ⟨negative, m, hm, rfl⟩
    have hp : (negative, m) ∈
        ((Finset.univ : Finset Bool).product
          (Finset.range fmt.minNormalMantissa)) := by
      simp [hm.2]
    have hv : fmt.subnormalValue negative m ∈
        fmt.subnormalValueCandidates := by
      exact Finset.mem_image.mpr ⟨(negative, m), hp, rfl⟩
    simp [finiteValueCandidates, hv]

/-- The exact finite set of real values represented by `fmt`. -/
noncomputable def finiteValues (fmt : FloatingPointFormat) : Finset ℝ := by
  classical
  exact fmt.finiteValueCandidates.filter fmt.finiteSystem

theorem mem_finiteValues_iff
    {fmt : FloatingPointFormat} {x : ℝ} :
    x ∈ fmt.finiteValues ↔ fmt.finiteSystem x := by
  classical
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    exact Finset.mem_filter.mpr
      ⟨fmt.finiteSystem_mem_finiteValueCandidates hx, hx⟩

/-- All halfway values generated by pairs of finite values of `fmt`. -/
noncomputable def finiteMidpoints (fmt : FloatingPointFormat) : Finset ℝ := by
  classical
  exact (fmt.finiteValues.product fmt.finiteValues).image
    (fun p ↦ (p.1 + p.2) / 2)

theorem mem_finiteMidpoints_iff
    {fmt : FloatingPointFormat} {y : ℝ} :
    y ∈ fmt.finiteMidpoints ↔
      ∃ a b : ℝ, fmt.finiteSystem a ∧ fmt.finiteSystem b ∧
        y = (a + b) / 2 := by
  classical
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨⟨a, b⟩, hab, rfl⟩
    have hab' := Finset.mem_product.mp hab
    exact ⟨a, b, mem_finiteValues_iff.mp hab'.1,
      mem_finiteValues_iff.mp hab'.2, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact Finset.mem_image.mpr
      ⟨(a, b), Finset.mem_product.mpr
        ⟨mem_finiteValues_iff.mpr ha, mem_finiteValues_iff.mpr hb⟩, rfl⟩

end FloatingPointFormat
end NumStability

end
