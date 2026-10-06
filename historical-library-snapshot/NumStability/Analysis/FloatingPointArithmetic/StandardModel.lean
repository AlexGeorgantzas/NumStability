import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.ScalarProperties
import NumStability.Analysis.Error.Measures.ScalarWitnesses
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.FloatingPointArithmetic.RoundToEvenLocalError
import NumStability.Analysis.FloatingPointArithmetic.Rounding

namespace NumStability

/-!
# Standard floating-point model

Reusable relative-error model and witness API for finite floating-point
formats. The Higham Chapter 2 source entry point imports this module.
-/

noncomputable section

namespace FloatingPointFormat

theorem relErrorComputedDenom_le_unitRoundoff_of_abs_sub_le_unitRoundoff_mul_abs
    {fmt : FloatingPointFormat} {computed exact : ℝ}
    (hcomputed : computed ≠ 0)
    (hbound : |exact - computed| ≤ fmt.unitRoundoff * |computed|) :
    relErrorComputedDenom computed exact ≤ fmt.unitRoundoff := by
  unfold relErrorComputedDenom
  have hbound' : |computed - exact| ≤ fmt.unitRoundoff * |computed| := by
    simpa [abs_sub_comm] using hbound
  calc
    |computed - exact| / |computed| ≤
        (fmt.unitRoundoff * |computed|) / |computed| :=
      div_le_div_of_nonneg_right hbound' (abs_nonneg computed)
    _ = fmt.unitRoundoff := by
      have hcomputed_abs_pos : 0 < |computed| := abs_pos.mpr hcomputed
      field_simp [ne_of_gt hcomputed_abs_pos]
theorem nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)) :
    relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hy_ne : y ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
  have hbound :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_rounded_of_realOrderAdjacent_between
      hround hadj hbetween
  exact
    fmt.relErrorComputedDenom_le_unitRoundoff_of_abs_sub_le_unitRoundoff_mul_abs
      hy_ne hbound
theorem nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
    {fmt : FloatingPointFormat} {x : ℝ}
    (_hx : fmt.unboundedNormalizedSystem x) :
    relErrorComputedDenom x x ≤ fmt.unitRoundoff := by
  unfold relErrorComputedDenom
  simpa using fmt.unitRoundoff_nonneg
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases fmt.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween with ⟨y, _hyab, hround⟩
  have hy_ne : y ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
  have hrel :=
    fmt.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
      hround hadj (Or.inl hbetween)
  exact ⟨y, hround, hy_ne, hrel⟩
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_sameExponent_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x)
    (hmax : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
      hmin hmax with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨false, m, e, hm, hx_eq⟩
    exact
      ⟨x, fmt.nearestRoundingToUnbounded_self hx_mem,
        fmt.unboundedNormalizedSystem_ne_zero hx_mem,
        fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
          hx_mem⟩
  · rcases hbracket with ⟨a, b, hadj, _ha_nonneg, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_ordered_between
        hadj ⟨ha_le_x, hx_le_b⟩
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_sameExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x)
    (hhi : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative
      hlo hhi with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨true, m, e, hm, hx_eq⟩
    exact
      ⟨x, fmt.nearestRoundingToUnbounded_self hx_mem,
        fmt.unboundedNormalizedSystem_ne_zero hx_mem,
        fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
          hx_mem⟩
  · rcases hbracket with ⟨a, b, hadj, _hb_nonpos, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_ordered_between
        hadj ⟨ha_le_x, hx_le_b⟩
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerInterval_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.betaR ^ (e - 1) ≤ x)
    (hmax : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hmin' : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hmin
  have hmax' : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e := by
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hmax
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_sameExponent_positive
      (e := e) hmin' hmax'
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerInterval_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hlo' : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hhi' : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_sameExponent_negative
      (e := e) hlo' hhi'
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerBoundary_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa e
  let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, e, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue false fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue false fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_ordered_between
      hadj ⟨ha_le_x, hx_le_b⟩
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerBoundary_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  let a := fmt.normalizedValue true fmt.minNormalMantissa (e + 1)
  let b := fmt.normalizedValue true fmt.maxNormalMantissa e
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨true, e, Or.inr ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue true fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue true fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_ordered_between
      hadj ⟨ha_le_x, hx_le_b⟩
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerSlice_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ (e - 1) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  by_cases hbin : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))
  · exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerInterval_positive
        (e := e) hlo hbin
  · have hgap_lo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x :=
      le_of_lt (lt_of_not_ge hbin)
    exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerBoundary_positive
        (e := e) hgap_lo hhi
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerSlice_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  by_cases hboundary : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))
  · exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerBoundary_negative
        (e := e) hlo hboundary
  · have hinterval_lo :
        -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x :=
      le_of_lt (lt_of_not_ge hboundary)
    exact
      fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerInterval_negative
        (e := e) hinterval_lo hhi
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases fmt.exists_powerSliceExponent_positive (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerSlice_positive
      (e := e) hlo hhi
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases fmt.exists_powerSliceExponent_negative (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_powerSlice_negative
      (e := e) hlo hhi
theorem exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_nonzero
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x ≠ 0) :
    ∃ y : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_negative hneg
  · exact False.elim (hx hzero)
  · exact fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_positive hpos
theorem sourceRoundAwayEvidence_relErrorComputedDenom_le_unitRoundoff
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteNormalRange x)
    (hpolicy : fmt.sourceRoundAwayEvidence x y) :
    y ≠ 0 ∧ relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨false, m, e, hm, hx_eq⟩
      constructor
      · rw [hy_eq]
        exact hx_ne
      · simpa [hy_eq] using
          fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
            hx_unbounded
    · rcases hbracket with ⟨a, b, hadj, _ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      have hround : fmt.nearestRoundingToUnbounded x y := by
        rw [hy_eq]
        exact
          fmt.nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
            hadj ⟨ha_le_x, hx_le_b⟩
      have hy_ne : y ≠ 0 :=
        fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
      have hrel :=
        fmt.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
          hround hadj (Or.inl ⟨ha_le_x, hx_le_b⟩)
      exact ⟨hy_ne, hrel⟩
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨true, m, e, hm, hx_eq⟩
      constructor
      · rw [hy_eq]
        exact hx_ne
      · simpa [hy_eq] using
          fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
            hx_unbounded
    · rcases hbracket with ⟨a, b, hadj, _hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      have hround : fmt.nearestRoundingToUnbounded x y := by
        rw [hy_eq]
        exact
          fmt.nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
            hadj ⟨ha_le_x, hx_le_b⟩
      have hy_ne : y ≠ 0 :=
        fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
      have hrel :=
        fmt.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
          hround hadj (Or.inl ⟨ha_le_x, hx_le_b⟩)
      exact ⟨hy_ne, hrel⟩
theorem sourceRoundToEvenEvidence_relErrorComputedDenom_le_unitRoundoff
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteNormalRange x)
    (hpolicy : fmt.sourceRoundToEvenEvidence x y) :
    y ≠ 0 ∧ relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨false, m, e, hm, hx_eq⟩
      constructor
      · rw [hy_eq]
        exact hx_ne
      · simpa [hy_eq] using
          fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
            hx_unbounded
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      have hround : fmt.nearestRoundingToUnbounded x y := by
        rw [hy_eq]
        exact
          fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
            leftMantissa hadj ⟨ha_le_x, hx_le_b⟩
      have hy_ne : y ≠ 0 :=
        fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
      have hrel :=
        fmt.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
          hround hadj (Or.inl ⟨ha_le_x, hx_le_b⟩)
      exact ⟨hy_ne, hrel⟩
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨true, m, e, hm, hx_eq⟩
      constructor
      · rw [hy_eq]
        exact hx_ne
      · simpa [hy_eq] using
          fmt.nearestRoundingToUnbounded_exact_relErrorComputedDenom_le_unitRoundoff
            hx_unbounded
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      have hround : fmt.nearestRoundingToUnbounded x y := by
        rw [hy_eq]
        exact
          fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
            leftMantissa hadj ⟨ha_le_x, hx_le_b⟩
      have hy_ne : y ≠ 0 :=
        fmt.unboundedNormalizedSystem_ne_zero (nearestRoundingIn_mem hround)
      have hrel :=
        fmt.nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_of_realOrderAdjacent_between
          hround hadj (Or.inl ⟨ha_le_x, hx_le_b⟩)
      exact ⟨hy_ne, hrel⟩
theorem exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_positive_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    ∃ y : ℝ,
      fmt.nearestRoundingToFinite x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hxpos : 0 < x := lt_of_lt_of_le fmt.minNormalMagnitude_pos hxlo
  rcases fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_positive
      (x := x) hxpos with ⟨y, hround, hy_ne, hrel⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
      hround hyfin hxlo
  exact ⟨y, hfiniteRound, hy_ne, hrel⟩
theorem exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_negative_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    ∃ y : ℝ,
      fmt.nearestRoundingToFinite x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  have hxneg : x < 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  rcases fmt.exists_nearestRoundingToUnbounded_relErrorComputedDenom_le_unitRoundoff_negative
      (x := x) hxneg with ⟨y, hround, hy_ne, hrel⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
      hround hyfin hxhi
  exact ⟨y, hfiniteRound, hy_ne, hrel⟩
theorem exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y : ℝ,
      fmt.nearestRoundingToFinite x y ∧ y ≠ 0 ∧
        relErrorComputedDenom y x ≤ fmt.unitRoundoff := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hx_abs : |x| = -x := abs_of_neg hneg
    have hxlo : -fmt.maxFiniteMagnitude ≤ x := by
      have h := hx.2
      rw [hx_abs] at h
      linarith
    have hxhi : x ≤ -fmt.minNormalMagnitude := by
      have h := hx.1
      rw [hx_abs] at h
      linarith
    exact
      fmt.exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_negative_finiteNormalRange
        hxlo hxhi
  · subst x
    have hmin_pos := fmt.minNormalMagnitude_pos
    rcases hx with ⟨hxlo, _hxhi⟩
    rw [abs_zero] at hxlo
    exact False.elim (not_lt_of_ge hxlo hmin_pos)
  · have hx_abs : |x| = x := abs_of_pos hpos
    have hxlo : fmt.minNormalMagnitude ≤ x := by
      simpa [hx_abs] using hx.1
    have hxhi : x ≤ fmt.maxFiniteMagnitude := by
      simpa [hx_abs] using hx.2
    exact
      fmt.exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_positive_finiteNormalRange
        hxlo hxhi
end FloatingPointFormat

/-- Higham Chapter 2 inverse relative-error witness: the computed value is the
exact value divided by a small factor `1 + δ`. -/
def inverseRelErrorWitness (computed exact δ : ℝ) : Prop :=
  1 + δ ≠ 0 ∧ computed = exact / (1 + δ)
/-- Higham Chapter 2 equation (2.5), packaged with a displayed error bound. -/
def inverseRelErrorModel (computed exact u : ℝ) : Prop :=
  ∃ δ : ℝ, |δ| ≤ u ∧ inverseRelErrorWitness computed exact δ
/-- The inverse witness `computed = exact/(1+δ)` is algebraically equivalent to
the usual signed relative-error witness with the computed value as denominator. -/
theorem inverseRelErrorWitness_iff_signedRelErrorWitness (computed exact δ : ℝ)
    (hδ : 1 + δ ≠ 0) :
    inverseRelErrorWitness computed exact δ ↔
      signedRelErrorWitness exact computed δ := by
  constructor
  · intro h
    rcases h with ⟨_, hcomp⟩
    unfold signedRelErrorWitness
    rw [hcomp]
    field_simp [hδ]
  · intro h
    refine ⟨hδ, ?_⟩
    unfold signedRelErrorWitness at h
    rw [h]
    field_simp [hδ]
/-- Computed-denominator relative error is the magnitude of the inverse
relative-error factor. -/
theorem relErrorComputedDenom_eq_abs_inverse_factor (computed exact : ℝ)
    (hcomputed : computed ≠ 0) :
    relErrorComputedDenom computed exact = |exact / computed - 1| := by
  unfold relErrorComputedDenom
  have hrewrite :
      exact / computed - 1 = (exact - computed) / computed := by
    field_simp [hcomputed]
  rw [hrewrite, abs_div, abs_sub_comm]
/-- A computed-denominator relative-error bound yields the inverse model (2.5)
when the exact and computed values are nonzero. -/
theorem inverseRelErrorModel_of_relErrorComputedDenom_le
    (computed exact u : ℝ)
    (hcomputed : computed ≠ 0) (hexact : exact ≠ 0)
    (hbound : relErrorComputedDenom computed exact ≤ u) :
    inverseRelErrorModel computed exact u := by
  let δ : ℝ := exact / computed - 1
  refine ⟨δ, ?_, ?_⟩
  · rw [← relErrorComputedDenom_eq_abs_inverse_factor computed exact hcomputed]
    exact hbound
  · have hden : 1 + δ ≠ 0 := by
      have hone : 1 + δ = exact / computed := by
        unfold δ
        ring
      rw [hone]
      exact div_ne_zero hexact hcomputed
    refine ⟨hden, ?_⟩
    have hone : 1 + δ = exact / computed := by
      unfold δ
      ring
    rw [hone]
    field_simp [hexact, hcomputed]
/-- The inverse model (2.5) implies the computed-denominator relative-error
bound, provided the computed value is nonzero. -/
theorem relErrorComputedDenom_le_of_inverseRelErrorModel
    (computed exact u : ℝ)
    (hcomputed : computed ≠ 0)
    (hmodel : inverseRelErrorModel computed exact u) :
    relErrorComputedDenom computed exact ≤ u := by
  rcases hmodel with ⟨δ, hδbound, hδ⟩
  rcases hδ with ⟨hden, hcomp⟩
  have hsigned : signedRelErrorWitness exact computed δ := by
    exact (inverseRelErrorWitness_iff_signedRelErrorWitness computed exact δ hden).mp
      ⟨hden, hcomp⟩
  have hrel : relError exact computed = |δ| :=
    relError_eq_abs_of_signedRelErrorWitness hcomputed hsigned
  rw [relErrorComputedDenom_eq_relError_swap, hrel]
  exact hδbound
/-- Exact theorem-surface equivalence between Higham's equation (2.5) and a
computed-denominator relative-error bound. -/
theorem inverseRelErrorModel_iff_relErrorComputedDenom_le
    (computed exact u : ℝ)
    (hcomputed : computed ≠ 0) (hexact : exact ≠ 0) :
    inverseRelErrorModel computed exact u ↔
      relErrorComputedDenom computed exact ≤ u := by
  constructor
  · exact relErrorComputedDenom_le_of_inverseRelErrorModel computed exact u hcomputed
  · exact inverseRelErrorModel_of_relErrorComputedDenom_le computed exact u hcomputed hexact
/-- Higham's modified model (2.5) implies the computed-denominator absolute
error form used in Chapter 3 running error analyses:
`|exact - computed| <= u * |computed|`. -/
theorem inverseRelErrorModel_abs_exact_sub_computed_le
    (computed exact u : ℝ)
    (hmodel : inverseRelErrorModel computed exact u) :
    |exact - computed| ≤ u * |computed| := by
  rcases hmodel with ⟨δ, hδbound, hδ⟩
  rcases hδ with ⟨hden, hcomp⟩
  have hsigned : signedRelErrorWitness exact computed δ :=
    (inverseRelErrorWitness_iff_signedRelErrorWitness computed exact δ hden).mp
      ⟨hden, hcomp⟩
  have hdiff : exact - computed = computed * δ := by
    unfold signedRelErrorWitness at hsigned
    rw [hsigned]
    ring
  calc
    |exact - computed| = |computed| * |δ| := by
      rw [hdiff, abs_mul]
    _ ≤ |computed| * u :=
      mul_le_mul_of_nonneg_left hδbound (abs_nonneg computed)
    _ = u * |computed| := by ring
namespace FloatingPointFormat

theorem exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        inverseRelErrorModel y x fmt.unitRoundoff := by
  rcases fmt.exists_nearestRoundingToFinite_relErrorComputedDenom_le_unitRoundoff_finiteNormalRange
      hx with ⟨y, hround, hy_ne, hrel⟩
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    have hmin_pos := fmt.minNormalMagnitude_pos
    have hxlo := hx.1
    rw [hx_zero, abs_zero] at hxlo
    exact (not_lt_of_ge hxlo) hmin_pos
  exact
    ⟨y, hround,
      inverseRelErrorModel_of_relErrorComputedDenom_le
        y x fmt.unitRoundoff hy_ne hx_ne hrel⟩
theorem exists_nearestRoundingToFinite_inverseRelErrorWitness_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ inverseRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange
      hx with ⟨y, hround, hmodel⟩
  rcases hmodel with ⟨δ, hδ, hwit⟩
  exact ⟨y, δ, hround, hδ, hwit⟩
theorem finiteNormalRoundAway_inverseRelErrorModel
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    inverseRelErrorModel (fmt.finiteNormalRoundAway x hx) x
      fmt.unitRoundoff := by
  have hpolicy := fmt.finiteNormalRoundAway_sourceRoundAwayEvidence hx
  rcases
    fmt.sourceRoundAwayEvidence_relErrorComputedDenom_le_unitRoundoff
      hx hpolicy with
    ⟨hy_ne, hrel⟩
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  exact
    inverseRelErrorModel_of_relErrorComputedDenom_le
      (fmt.finiteNormalRoundAway x hx) x fmt.unitRoundoff hy_ne hx_ne hrel
theorem finiteNormalRoundAway_inverseRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundAway x hx) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteNormalRoundAway x hx) x δ := by
  rcases fmt.finiteNormalRoundAway_inverseRelErrorModel hx with ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteNormalRoundAway_nearestRoundingToFinite hx, hδ, hwit⟩
theorem finiteNormalRoundToEven_inverseRelErrorModel
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    inverseRelErrorModel (fmt.finiteNormalRoundToEven x hx) x
      fmt.unitRoundoff := by
  have hpolicy := fmt.finiteNormalRoundToEven_sourceRoundToEvenEvidence hx
  rcases
    fmt.sourceRoundToEvenEvidence_relErrorComputedDenom_le_unitRoundoff
      hx hpolicy with
    ⟨hy_ne, hrel⟩
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  exact
    inverseRelErrorModel_of_relErrorComputedDenom_le
      (fmt.finiteNormalRoundToEven x hx) x fmt.unitRoundoff hy_ne hx_ne hrel
theorem finiteNormalRoundToEven_inverseRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundToEven x hx) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteNormalRoundToEven x hx) x δ := by
  rcases fmt.finiteNormalRoundToEven_inverseRelErrorModel hx with ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteNormalRoundToEven_nearestRoundingToFinite hx, hδ, hwit⟩
theorem finiteRoundAway_inverseRelErrorModel_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    inverseRelErrorModel (fmt.finiteRoundAway x) x fmt.unitRoundoff := by
  have hpolicy :=
    fmt.finiteRoundAway_sourceRoundAwayEvidence_of_finiteNormalRange hx
  rcases
    fmt.sourceRoundAwayEvidence_relErrorComputedDenom_le_unitRoundoff
      hx hpolicy with
    ⟨hy_ne, hrel⟩
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  exact
    inverseRelErrorModel_of_relErrorComputedDenom_le
      (fmt.finiteRoundAway x) x fmt.unitRoundoff hy_ne hx_ne hrel
theorem finiteRoundAway_inverseRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteRoundAway x) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteRoundAway x) x δ := by
  rcases
    fmt.finiteRoundAway_inverseRelErrorModel_of_finiteNormalRange hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteRoundAway_nearestRoundingToFinite x, hδ, hwit⟩
theorem finiteRoundToEven_inverseRelErrorModel_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    inverseRelErrorModel (fmt.finiteRoundToEven x) x fmt.unitRoundoff := by
  have hpolicy :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hx
  rcases
    fmt.sourceRoundToEvenEvidence_relErrorComputedDenom_le_unitRoundoff
      hx hpolicy with
    ⟨hy_ne, hrel⟩
  have hx_ne := fmt.finiteNormalRange_ne_zero hx
  exact
    inverseRelErrorModel_of_relErrorComputedDenom_le
      (fmt.finiteRoundToEven x) x fmt.unitRoundoff hy_ne hx_ne hrel
theorem finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteRoundToEven x) x δ := by
  rcases
    fmt.finiteRoundToEven_inverseRelErrorModel_of_finiteNormalRange hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteRoundToEven_nearestRoundingToFinite x, hδ, hwit⟩
theorem finiteRoundToEvenOp_inverseRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {op : BasicOp} {x y : ℝ}
    (hxy : fmt.finiteNormalRange (BasicOp.exact op x y)) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite (BasicOp.exact op x y)
          (fmt.finiteRoundToEvenOp op x y) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteRoundToEvenOp op x y)
            (BasicOp.exact op x y) δ := by
  rcases
    fmt.finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange
      hxy with
    ⟨δ, hround, hδ, hwit⟩
  exact
    ⟨δ, by simpa [finiteRoundToEvenOp] using hround, hδ,
      by simpa [finiteRoundToEvenOp] using hwit⟩
theorem finiteRoundToEvenSqrt_inverseRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsqrt : fmt.finiteNormalRange (Real.sqrt x)) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite (Real.sqrt x)
          (fmt.finiteRoundToEvenSqrt x) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteRoundToEvenSqrt x)
            (Real.sqrt x) δ := by
  rcases
    fmt.finiteRoundToEven_inverseRelErrorWitness_of_finiteNormalRange
      hsqrt with
    ⟨δ, hround, hδ, hwit⟩
  exact
    ⟨δ, by simpa [finiteRoundToEvenSqrt] using hround, hδ,
      by simpa [finiteRoundToEvenSqrt] using hwit⟩
/-- Source-style arbitrary tie choice for `fl` on the finite normal range.
This is a noncomputable choice from the nearest-rounding relation, not a
round-to-even or IEEE tie-breaking rule. -/
noncomputable def finiteNormalFl (fmt : FloatingPointFormat) (x : ℝ)
    (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose
    (fmt.exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange hx)
theorem finiteNormalFl_spec
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteNormalFl x hx) ∧
      inverseRelErrorModel (fmt.finiteNormalFl x hx) x fmt.unitRoundoff := by
  exact
    Classical.choose_spec
      (fmt.exists_nearestRoundingToFinite_inverseRelErrorModel_finiteNormalRange hx)
theorem finiteNormalFl_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteNormalFl x hx) :=
  (fmt.finiteNormalFl_spec hx).1
theorem finiteNormalFl_inverseRelErrorModel
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    inverseRelErrorModel (fmt.finiteNormalFl x hx) x fmt.unitRoundoff :=
  (fmt.finiteNormalFl_spec hx).2
theorem finiteNormalFl_inverseRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalFl x hx) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          inverseRelErrorWitness (fmt.finiteNormalFl x hx) x δ := by
  rcases fmt.finiteNormalFl_inverseRelErrorModel hx with ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteNormalFl_nearestRoundingToFinite hx, hδ, hwit⟩
theorem finiteNormalFl_signedRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalFl x hx) ∧
        |δ| ≤ fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalFl x hx) x δ := by
  rcases
    fmt.nearestRoundingToFinite_signedRelErrorWitness_of_finiteNormalRange
      (fmt.finiteNormalFl_nearestRoundingToFinite hx) hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteNormalFl_nearestRoundingToFinite hx, hδ, hwit⟩
theorem finiteNormalFl_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalFl x hx) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalFl x hx) x δ := by
  rcases
    fmt.nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange
      (fmt.finiteNormalFl_nearestRoundingToFinite hx) hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, fmt.finiteNormalFl_nearestRoundingToFinite hx, hδ, hwit⟩

end FloatingPointFormat

end

end NumStability
