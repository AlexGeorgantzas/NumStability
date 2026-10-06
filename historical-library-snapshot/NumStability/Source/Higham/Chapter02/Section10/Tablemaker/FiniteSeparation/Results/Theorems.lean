-- NumStability/Source/Higham/Chapter02/Section10/Tablemaker/FiniteSeparation/Results/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Analysis.HighamChapter2Lindemann`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Source.Higham.Chapter02.Section10.Tablemaker.FiniteSeparation.Basic
import NumStability.Source.Higham.Chapter02.Section10.Tablemaker.HermiteLindemann.Basic
import NumStability.Upstream.Lindemann.Basic

/-!
# Theorems

Relocated from `NumStability.Analysis.HighamChapter2Lindemann` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# HighamChapter2Lindemann (compatibility module)

Historical path, retained so existing imports of `NumStability.Analysis.HighamChapter2Lindemann`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open Filter Finset

noncomputable section

namespace NumStability

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

end NumStability

end
