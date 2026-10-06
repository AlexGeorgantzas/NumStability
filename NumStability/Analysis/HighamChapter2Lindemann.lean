import NumStability.Analysis.HighamChapter2Tablemaker
import NumStability.Upstream.Lindemann.Basic

namespace NumStability

open Filter Finset

noncomputable section

/-!
# Higham Chapter 2: Lindemann and finite tablemaker separation

Higham uses the Hermite--Lindemann theorem in Section 2.10 to exclude two
rounding-boundary cases for `exp x`: when a nonzero machine number `x` is the
input, `exp x` is neither a machine number nor halfway between two machine
numbers.  The upstream theorem used here was adapted from mathlib4 PR #28013,
https://github.com/leanprover-community/mathlib4/pull/28013, at commit
`5abb7c68488b527e4d7ecf5d7bbe085db8d2a388`.

The final results below also extract a positive distance from every midpoint
of a fixed finite format and show that any approximation sequence converging
to `exp x` eventually preserves all midpoint comparisons.  They do not assert
termination of an unspecified digit-generation algorithm.
-/

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

private theorem exists_pos_uniform_abs_separation
    (s : Finset ℝ) (z : ℝ) (hz : ∀ y ∈ s, z ≠ y) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ s, ε ≤ |z - y| := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, by positivity, by simp⟩
  | @insert a s ha ih =>
      have hza : 0 < |z - a| := abs_pos.mpr (sub_ne_zero.mpr (hz a (by simp)))
      have hzrest : ∀ y ∈ s, z ≠ y := by
        intro y hy
        exact hz y (by simp [hy])
      obtain ⟨ε, hε0, hε⟩ := ih hzrest
      refine ⟨min ε |z - a|, lt_min hε0 hza, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hε y hy)

/-- A fixed finite format has a positive separation between `exp x` and every
rounding midpoint.  This is the finite-distance content behind the tablemaker
paragraph, independent of any digit-generation procedure. -/
theorem higham2_exp_finite_midpoint_separation
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) (hx0 : x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ a b : ℝ, fmt.finiteSystem a → fmt.finiteSystem b →
        ε ≤ |Real.exp x - (a + b) / 2| := by
  classical
  have hnot := (higham2_exp_not_machine_or_midpoint hx hx0).2
  have hmid : ∀ y ∈ fmt.finiteMidpoints, Real.exp x ≠ y := by
    intro y hy
    rcases FloatingPointFormat.mem_finiteMidpoints_iff.mp hy with
      ⟨a, b, ha, hb, rfl⟩
    exact hnot a b ha hb
  obtain ⟨ε, hε0, hε⟩ :=
    exists_pos_uniform_abs_separation fmt.finiteMidpoints (Real.exp x) hmid
  refine ⟨ε, hε0, ?_⟩
  intro a b ha hb
  exact hε ((a + b) / 2)
    (FloatingPointFormat.mem_finiteMidpoints_iff.mpr
      ⟨a, b, ha, hb, rfl⟩)

private theorem midpoint_comparisons_stable_of_abs_error_lt
    {z y m ε : ℝ} (hz : z ≠ m) (
      hsep : ε ≤ |z - m|) (hy : |y - z| < ε) :
    (y < m ↔ z < m) ∧ (m < y ↔ m < z) := by
  have herr : |y - z| < |z - m| := hy.trans_le hsep
  rcases lt_or_gt_of_ne hz with hzm | hmz
  · have hdist : |y - z| < m - z := by
      simpa [abs_of_neg (sub_neg.mpr hzm)] using herr
    have hylt : y < m := by
      have := (abs_lt.mp hdist).2
      linarith
    exact ⟨iff_of_true hylt hzm, iff_of_false (not_lt_of_ge hylt.le)
      (not_lt_of_ge hzm.le)⟩
  · have hdist : |y - z| < z - m := by
      simpa [abs_of_pos (sub_pos.mpr hmz)] using herr
    have hmy : m < y := by
      have := (abs_lt.mp hdist).1
      linarith
    exact ⟨iff_of_false (not_lt_of_ge hmy.le) (not_lt_of_ge hmz.le),
      iff_of_true hmy hmz⟩

/-- Any real approximation sequence converging to `exp x` eventually lies on
the same side of every midpoint of the fixed finite format.  The theorem is an
interface for a separately specified approximation/error algorithm; it does
not infer such an algorithm from the word "digits". -/
theorem higham2_exp_eventually_stable_midpoint_comparisons
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) (hx0 : x ≠ 0)
    (approx : ℕ → ℝ)
    (happrox : Tendsto approx atTop (nhds (Real.exp x))) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a b : ℝ,
      fmt.finiteSystem a → fmt.finiteSystem b →
        (approx n < (a + b) / 2 ↔ Real.exp x < (a + b) / 2) ∧
        ((a + b) / 2 < approx n ↔ (a + b) / 2 < Real.exp x) := by
  obtain ⟨ε, hε0, hsep⟩ := higham2_exp_finite_midpoint_separation hx hx0
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp happrox) ε hε0
  refine ⟨N, ?_⟩
  intro n hn a b ha hb
  have herr : |approx n - Real.exp x| < ε := by
    simpa [Real.dist_eq] using hN n hn
  exact midpoint_comparisons_stable_of_abs_error_lt
    ((higham2_exp_not_machine_or_midpoint hx hx0).2 a b ha hb)
    (hsep a b ha hb) herr

end

end NumStability
