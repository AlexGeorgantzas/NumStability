import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.ScalarWitnesses
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.IeeeValue
import NumStability.Analysis.FloatingPointArithmetic.Rounding

namespace NumStability

/-!
# NearestRoundingError

Extracted without change from FloatingPointArithmetic.
-/

noncomputable section

namespace FloatingPointFormat

/-- Strict source-style variant of exact finite rounding: the zero witness
satisfies `|delta| < u` because `u` is positive. -/
theorem nearestRoundingToFinite_exact_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness x x δ ∧
          fmt.nearestRoundingToFinite x x := by
  refine ⟨0, ?_, ?_, fmt.nearestRoundingToFinite_self hx⟩
  · simpa using fmt.unitRoundoff_pos
  · unfold signedRelErrorWitness
    ring
/-- Source-facing zero case for the finite-format relation: nearest rounding
has output zero and the signed relative-error witness holds with `delta = 0`. -/
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_zero
    (fmt : FloatingPointFormat) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite 0 y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y 0 δ := by
  rcases fmt.nearestRoundingToFinite_exact_signedRelErrorWitness
      (x := 0) fmt.finiteSystem_zero with ⟨δ, hδ, hwit, hround⟩
  exact ⟨0, δ, hround, hδ, hwit⟩
theorem nearestRoundingToUnbounded_exact_signedRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.unboundedNormalizedSystem x) :
    ∃ δ : ℝ,
      |δ| ≤ fmt.unitRoundoff ∧
        signedRelErrorWitness x x δ ∧
          fmt.nearestRoundingToUnbounded x x := by
  refine ⟨0, ?_, ?_, fmt.nearestRoundingToUnbounded_self hx⟩
  · simpa using fmt.unitRoundoff_nonneg
  · unfold signedRelErrorWitness
    ring
theorem nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.unboundedNormalizedSystem x) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness x x δ ∧
          fmt.nearestRoundingToUnbounded x x := by
  refine ⟨0, ?_, ?_, fmt.nearestRoundingToUnbounded_self hx⟩
  · simpa using fmt.unitRoundoff_pos
  · unfold signedRelErrorWitness
    ring
theorem nearestRoundingIn_abs_sub_le_half_abs_sub_of_between
    {S : ℝ → Prop} {x y z : ℝ}
    (h : nearestRoundingIn S x y) (hz : S z)
    (hbetween : (y ≤ x ∧ x ≤ z) ∨ (z ≤ x ∧ x ≤ y)) :
    |x - y| ≤ (1 / 2 : ℝ) * |y - z| := by
  have hmin : |x - y| ≤ |x - z| :=
    nearestRoundingIn_minimal h hz
  rcases hbetween with hbetween | hbetween
  · rcases hbetween with ⟨hyx, hxz⟩
    have hyz : y ≤ z := le_trans hyx hxz
    have hxy_nonneg : 0 ≤ x - y := sub_nonneg.mpr hyx
    have hxz_nonpos : x - z ≤ 0 := sub_nonpos.mpr hxz
    have hyz_nonpos : y - z ≤ 0 := sub_nonpos.mpr hyz
    have hsum : |y - z| = |x - y| + |x - z| := by
      rw [abs_of_nonpos hyz_nonpos, abs_of_nonneg hxy_nonneg,
        abs_of_nonpos hxz_nonpos]
      ring
    have htwice : 2 * |x - y| ≤ |y - z| := by
      rw [hsum]
      nlinarith
    nlinarith
  · rcases hbetween with ⟨hzx, hxy⟩
    have hzy : z ≤ y := le_trans hzx hxy
    have hxy_nonpos : x - y ≤ 0 := sub_nonpos.mpr hxy
    have hxz_nonneg : 0 ≤ x - z := sub_nonneg.mpr hzx
    have hyz_nonneg : 0 ≤ y - z := sub_nonneg.mpr hzy
    have hsum : |y - z| = |x - y| + |x - z| := by
      rw [abs_of_nonneg hyz_nonneg, abs_of_nonpos hxy_nonpos,
        abs_of_nonneg hxz_nonneg]
      ring
    have htwice : 2 * |x - y| ≤ |y - z| := by
      rw [hsum]
      nlinarith
    nlinarith
theorem nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    y = a ∨ y = b := by
  by_cases hya : y = a
  · exact Or.inl hya
  by_cases hyb : y = b
  · exact Or.inr hyb
  have hy_mem : fmt.unboundedNormalizedSystem y := hround.1
  have ha_mem : fmt.unboundedNormalizedSystem a := hadj.1
  have hb_mem : fmt.unboundedNormalizedSystem b := hadj.2.1
  have hmin_a : |x - y| ≤ |x - a| := hround.2 a ha_mem
  have hmin_b : |x - y| ≤ |x - b| := hround.2 b hb_mem
  rcases lt_or_ge y a with hy_lt_a | ha_le_y
  · have hdist : |x - a| < |x - y| := by
      have hxa_nonneg : 0 ≤ x - a := sub_nonneg.mpr hbetween.1
      have hxy_nonneg : 0 ≤ x - y :=
        sub_nonneg.mpr (le_trans (le_of_lt hy_lt_a) hbetween.1)
      rw [abs_of_nonneg hxa_nonneg, abs_of_nonneg hxy_nonneg]
      linarith
    exact False.elim ((not_lt_of_ge hmin_a) hdist)
  · have ha_lt_y : a < y := by
      exact lt_of_le_of_ne ha_le_y (by
        intro hay
        exact hya hay.symm)
    rcases lt_or_ge y b with hy_lt_b | hb_le_y
    · exact False.elim
        ((hadj.2.2.2 y hy_mem) (Or.inl ⟨ha_lt_y, hy_lt_b⟩))
    · have hb_lt_y : b < y := by
        exact lt_of_le_of_ne hb_le_y (by
          intro hby
          exact hyb hby.symm)
      have hdist : |x - b| < |x - y| := by
        have hxb_nonpos : x - b ≤ 0 := sub_nonpos.mpr hbetween.2
        have hxy_nonpos : x - y ≤ 0 :=
          sub_nonpos.mpr (le_trans hbetween.2 (le_of_lt hb_lt_y))
        rw [abs_of_nonpos hxb_nonpos, abs_of_nonpos hxy_nonpos]
        linarith
      exact False.elim ((not_lt_of_ge hmin_b) hdist)
theorem nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)) :
    y = a ∨ y = b := by
  rcases hbetween with hbetween | hbetween
  · exact
      fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hround hadj hbetween
  · have hsel :=
      fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hround (fmt.realOrderAdjacentNormalized_symm hadj) hbetween
    rcases hsel with hyb | hya
    · exact Or.inr hyb
    · exact Or.inl hya
theorem nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b)
    (hleft : |x - a| ≤ |x - b|) :
    fmt.nearestRoundingToUnbounded x a := by
  refine ⟨hadj.1, ?_⟩
  intro z hz
  by_cases hza_lt : z < a
  · have hxa_nonneg : 0 ≤ x - a := sub_nonneg.mpr hbetween.1
    have hxz_nonneg : 0 ≤ x - z :=
      sub_nonneg.mpr (le_trans (le_of_lt hza_lt) hbetween.1)
    rw [abs_of_nonneg hxa_nonneg, abs_of_nonneg hxz_nonneg]
    linarith
  · have ha_le_z : a ≤ z := le_of_not_gt hza_lt
    by_cases hza : z = a
    · simp [hza]
    · have haz : a < z := lt_of_le_of_ne ha_le_z (by
        intro haz_eq
        exact hza haz_eq.symm)
      by_cases hzb_lt : z < b
      · exact False.elim ((hadj.2.2.2 z hz) (Or.inl ⟨haz, hzb_lt⟩))
      · have hb_le_z : b ≤ z := le_of_not_gt hzb_lt
        by_cases hzb : z = b
        · simpa [hzb] using hleft
        · have hbz : b < z := lt_of_le_of_ne hb_le_z (by
            intro hbz_eq
            exact hzb hbz_eq.symm)
          have hdist_right : |x - b| ≤ |x - z| := by
            have hxb_nonpos : x - b ≤ 0 := sub_nonpos.mpr hbetween.2
            have hxz_nonpos : x - z ≤ 0 :=
              sub_nonpos.mpr (le_trans hbetween.2 (le_of_lt hbz))
            rw [abs_of_nonpos hxb_nonpos, abs_of_nonpos hxz_nonpos]
            linarith
          exact le_trans hleft hdist_right
theorem nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b)
    (hright : |x - b| ≤ |x - a|) :
    fmt.nearestRoundingToUnbounded x b := by
  refine ⟨hadj.2.1, ?_⟩
  intro z hz
  by_cases hza_lt : z < a
  · have hdist_left : |x - a| ≤ |x - z| := by
      have hxa_nonneg : 0 ≤ x - a := sub_nonneg.mpr hbetween.1
      have hxz_nonneg : 0 ≤ x - z :=
        sub_nonneg.mpr (le_trans (le_of_lt hza_lt) hbetween.1)
      rw [abs_of_nonneg hxa_nonneg, abs_of_nonneg hxz_nonneg]
      linarith
    exact le_trans hright hdist_left
  · have ha_le_z : a ≤ z := le_of_not_gt hza_lt
    by_cases hza : z = a
    · simpa [hza] using hright
    · have haz : a < z := lt_of_le_of_ne ha_le_z (by
        intro haz_eq
        exact hza haz_eq.symm)
      by_cases hzb_lt : z < b
      · exact False.elim ((hadj.2.2.2 z hz) (Or.inl ⟨haz, hzb_lt⟩))
      · have hb_le_z : b ≤ z := le_of_not_gt hzb_lt
        by_cases hzb : z = b
        · simp [hzb]
        · have hbz : b < z := lt_of_le_of_ne hb_le_z (by
            intro hbz_eq
            exact hzb hbz_eq.symm)
          have hdist_right : |x - b| ≤ |x - z| := by
            have hxb_nonpos : x - b ≤ 0 := sub_nonpos.mpr hbetween.2
            have hxz_nonpos : x - z ≤ 0 :=
              sub_nonpos.mpr (le_trans hbetween.2 (le_of_lt hbz))
            rw [abs_of_nonpos hxb_nonpos, abs_of_nonpos hxz_nonpos]
            linarith
          exact hdist_right
/-- The local round-away selector is a valid nearest-rounding choice for a
supplied ordered adjacent normalized bracket. -/
theorem nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    fmt.nearestRoundingToUnbounded x (nearestAdjacentRoundAway x a b) := by
  unfold nearestAdjacentRoundAway
  by_cases hleft_lt : |x - a| < |x - b|
  · simp [hleft_lt]
    exact
      fmt.nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
        hadj hbetween (le_of_lt hleft_lt)
  · simp [hleft_lt]
    by_cases hright_lt : |x - b| < |x - a|
    · simp [hright_lt]
      exact
        fmt.nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
          hadj hbetween (le_of_lt hright_lt)
    · simp [hright_lt]
      by_cases haway : |a| ≤ |b|
      · simp [haway]
        exact
          fmt.nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
            hadj hbetween (le_of_not_gt hleft_lt)
      · simp [haway]
        exact
          fmt.nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
            hadj hbetween (le_of_not_gt hright_lt)
theorem nearestAdjacentRoundToEven_eq_left_of_left_closer
    {x a b : ℝ} {leftMantissa : ℕ}
    (hleft : |x - a| < |x - b|) :
    nearestAdjacentRoundToEven x a b leftMantissa = a := by
  unfold nearestAdjacentRoundToEven
  simp [hleft]
theorem nearestAdjacentRoundToEven_eq_right_of_right_closer
    {x a b : ℝ} {leftMantissa : ℕ}
    (hright : |x - b| < |x - a|) :
    nearestAdjacentRoundToEven x a b leftMantissa = b := by
  unfold nearestAdjacentRoundToEven
  have hnot_left : ¬ |x - a| < |x - b| := not_lt_of_gt hright
  simp [hnot_left, hright]
theorem nearestAdjacentRoundToEven_eq_left_of_tie_even
    {x a b : ℝ} {leftMantissa : ℕ}
    (htie : |x - a| = |x - b|)
    (heven : evenMantissa leftMantissa) :
    nearestAdjacentRoundToEven x a b leftMantissa = a := by
  unfold nearestAdjacentRoundToEven
  have hnot_left : ¬ |x - a| < |x - b| := by
    rw [htie]
    exact lt_irrefl _
  have hnot_right : ¬ |x - b| < |x - a| := by
    rw [htie]
    exact lt_irrefl _
  simp [hnot_left, hnot_right, heven]
theorem nearestAdjacentRoundToEven_eq_right_of_tie_odd
    {x a b : ℝ} {leftMantissa : ℕ}
    (htie : |x - a| = |x - b|)
    (hodd : ¬ evenMantissa leftMantissa) :
    nearestAdjacentRoundToEven x a b leftMantissa = b := by
  unfold nearestAdjacentRoundToEven
  have hnot_left : ¬ |x - a| < |x - b| := by
    rw [htie]
    exact lt_irrefl _
  have hnot_right : ¬ |x - b| < |x - a| := by
    rw [htie]
    exact lt_irrefl _
  simp [hnot_left, hnot_right, hodd]
theorem nearestAdjacentRoundToEven_eq_left_endpoint
    (a b : ℝ) (leftMantissa : ℕ) :
    nearestAdjacentRoundToEven a a b leftMantissa = a := by
  by_cases hab : a = b
  · subst b
    simp [nearestAdjacentRoundToEven]
  · have hleft : |a - a| < |a - b| := by
      have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
      have hpos : 0 < |a - b| := abs_pos.mpr hne
      simpa using hpos
    exact nearestAdjacentRoundToEven_eq_left_of_left_closer hleft
theorem nearestAdjacentRoundToEven_eq_right_endpoint
    (a b : ℝ) (leftMantissa : ℕ) :
    nearestAdjacentRoundToEven b a b leftMantissa = b := by
  by_cases hab : a = b
  · subst b
    simp [nearestAdjacentRoundToEven]
  · have hright : |b - b| < |b - a| := by
      have hne : b - a ≠ 0 := by
        exact sub_ne_zero.mpr (fun hba => hab hba.symm)
      have hpos : 0 < |b - a| := abs_pos.mpr hne
      simpa using hpos
    exact nearestAdjacentRoundToEven_eq_right_of_right_closer hright
theorem nearestAdjacentRoundToEven_neg_of_even_right_iff_not_even_left
    {x a b : ℝ} {leftMantissa rightMantissa : ℕ}
    (hparity : evenMantissa rightMantissa ↔ ¬ evenMantissa leftMantissa) :
    nearestAdjacentRoundToEven (-x) (-b) (-a) rightMantissa =
      -nearestAdjacentRoundToEven x a b leftMantissa := by
  unfold nearestAdjacentRoundToEven
  have hdist_right : |-x - -b| = |x - b| := by
    have h : -x - -b = -(x - b) := by ring
    rw [h, abs_neg]
  have hdist_left : |-x - -a| = |x - a| := by
    have h : -x - -a = -(x - a) := by ring
    rw [h, abs_neg]
  rw [hdist_right, hdist_left]
  by_cases hleft : |x - a| < |x - b|
  · have hnot_right : ¬ |x - b| < |x - a| := not_lt_of_gt hleft
    simp [hleft, hnot_right]
  · by_cases hright : |x - b| < |x - a|
    · have hnot_left : ¬ |x - a| < |x - b| := not_lt_of_gt hright
      simp [hright, hnot_left]
    · have htie_left : ¬ |x - a| < |x - b| := hleft
      have htie_right : ¬ |x - b| < |x - a| := hright
      by_cases heven_left : evenMantissa leftMantissa
      · have hodd_right : ¬ evenMantissa rightMantissa := by
          intro heven_right
          exact (hparity.mp heven_right) heven_left
        simp [htie_left, htie_right, heven_left, hodd_right]
      · have heven_right : evenMantissa rightMantissa :=
          hparity.mpr heven_left
        simp [htie_left, htie_right, heven_left, heven_right]
/-- The local round-to-even selector is a valid nearest-rounding choice for a
supplied ordered adjacent normalized bracket.  This proves the source-level
nearest-rounding property of the tie policy, but not a total finite or IEEE
operation. -/
theorem nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ} (leftMantissa : ℕ)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    fmt.nearestRoundingToUnbounded x
      (nearestAdjacentRoundToEven x a b leftMantissa) := by
  unfold nearestAdjacentRoundToEven
  by_cases hleft_lt : |x - a| < |x - b|
  · simp [hleft_lt]
    exact
      fmt.nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
        hadj hbetween (le_of_lt hleft_lt)
  · simp [hleft_lt]
    by_cases hright_lt : |x - b| < |x - a|
    · simp [hright_lt]
      exact
        fmt.nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
          hadj hbetween (le_of_lt hright_lt)
    · simp [hright_lt]
      by_cases heven : evenMantissa leftMantissa
      · simp [heven]
        exact
          fmt.nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
            hadj hbetween (le_of_not_gt hright_lt)
      · simp [heven]
        exact
          fmt.nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
            hadj hbetween (le_of_not_gt hleft_lt)
theorem nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_sameExponentAdjacentNormalized_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ} {leftMantissa : ℕ}
    (hadj : fmt.sameExponentAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    fmt.nearestRoundingToUnbounded x
      (nearestAdjacentRoundToEven x a b leftMantissa) := by
  exact
    fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      leftMantissa
      (fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hadj)
      hbetween
theorem nearestRoundingToUnbounded_eq_left_of_realOrderAdjacent_ordered_between_of_left_closer
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b)
    (hleft : |x - a| < |x - b|) :
    y = a := by
  rcases
      fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hround hadj hbetween with hy | hy
  · exact hy
  · subst y
    have hmin : |x - b| ≤ |x - a| :=
      nearestRoundingIn_minimal hround hadj.1
    exact False.elim ((not_lt_of_ge hmin) hleft)
theorem nearestRoundingToUnbounded_eq_right_of_realOrderAdjacent_ordered_between_of_right_closer
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b)
    (hright : |x - b| < |x - a|) :
    y = b := by
  rcases
      fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hround hadj hbetween with hy | hy
  · subst y
    have hmin : |x - a| ≤ |x - b| :=
      nearestRoundingIn_minimal hround hadj.2.1
    exact False.elim ((not_lt_of_ge hmin) hright)
  · exact hy
theorem realOrderAdjacentNormalized_bracket_unique_of_strict_between
    {fmt : FloatingPointFormat} {x a b c d : ℝ}
    (hab : fmt.realOrderAdjacentNormalized a b)
    (hcd : fmt.realOrderAdjacentNormalized c d)
    (habx : a < x ∧ x < b)
    (hcdx : c ≤ x ∧ x ≤ d) :
    c = a ∧ d = b := by
  have hc_lt_x : c < x := by
    have hc_ne_x : c ≠ x := by
      intro hcx
      apply hab.2.2.2 c hcd.1
      exact Or.inl
        ⟨by simpa [hcx] using habx.1, by simpa [hcx] using habx.2⟩
    exact lt_of_le_of_ne hcdx.1 hc_ne_x
  have hx_lt_d : x < d := by
    have hd_ne_x : d ≠ x := by
      intro hdx
      apply hab.2.2.2 d hcd.2.1
      exact Or.inl
        ⟨by simpa [hdx] using habx.1, by simpa [hdx] using habx.2⟩
    exact lt_of_le_of_ne hcdx.2 hd_ne_x.symm
  have hc_eq_a : c = a := by
    rcases lt_trichotomy c a with hca | hca | hac
    · exfalso
      apply hcd.2.2.2 a hab.1
      exact Or.inl ⟨hca, lt_trans habx.1 hx_lt_d⟩
    · exact hca
    · exfalso
      apply hab.2.2.2 c hcd.1
      exact Or.inl ⟨hac, lt_trans hc_lt_x habx.2⟩
  subst c
  have hd_eq_b : d = b := by
    rcases lt_trichotomy d b with hdb | hdb | hbd
    · exfalso
      apply hab.2.2.2 d hcd.2.1
      exact Or.inl ⟨lt_trans habx.1 hx_lt_d, hdb⟩
    · exact hdb
    · exfalso
      apply hcd.2.2.2 b hab.2.1
      exact Or.inl ⟨lt_trans habx.1 habx.2, hbd⟩
  exact ⟨rfl, hd_eq_b⟩
theorem adjacentRoundTowardNegative_eq_right_of_eq_right
    {x a b : ℝ} (hxb : x = b) :
    adjacentRoundTowardNegative x a b = b := by
  simp [adjacentRoundTowardNegative, hxb]
theorem adjacentRoundTowardNegative_eq_left_of_ne_right
    {x a b : ℝ} (hxb : x ≠ b) :
    adjacentRoundTowardNegative x a b = a := by
  simp [adjacentRoundTowardNegative, hxb]
theorem adjacentRoundTowardPositive_eq_left_of_eq_left
    {x a b : ℝ} (hxa : x = a) :
    adjacentRoundTowardPositive x a b = a := by
  simp [adjacentRoundTowardPositive, hxa]
theorem adjacentRoundTowardPositive_eq_right_of_ne_left
    {x a b : ℝ} (hxa : x ≠ a) :
    adjacentRoundTowardPositive x a b = b := by
  simp [adjacentRoundTowardPositive, hxa]
theorem adjacentRoundTowardZero_eq_towardPositive_of_neg
    {x a b : ℝ} (hx : x < 0) :
    adjacentRoundTowardZero x a b = adjacentRoundTowardPositive x a b := by
  simp [adjacentRoundTowardZero, hx]
theorem adjacentRoundTowardZero_eq_towardNegative_of_nonneg
    {x a b : ℝ} (hx : 0 ≤ x) :
    adjacentRoundTowardZero x a b = adjacentRoundTowardNegative x a b := by
  simp [adjacentRoundTowardZero, not_lt.mpr hx]
theorem adjacentRoundTowardNegative_mem_unboundedNormalized
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b) :
    fmt.unboundedNormalizedSystem (adjacentRoundTowardNegative x a b) := by
  by_cases hxb : x = b
  · simpa [adjacentRoundTowardNegative, hxb] using hadj.2.1
  · simpa [adjacentRoundTowardNegative, hxb] using hadj.1
theorem adjacentRoundTowardPositive_mem_unboundedNormalized
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b) :
    fmt.unboundedNormalizedSystem (adjacentRoundTowardPositive x a b) := by
  by_cases hxa : x = a
  · simpa [adjacentRoundTowardPositive, hxa] using hadj.1
  · simpa [adjacentRoundTowardPositive, hxa] using hadj.2.1
theorem adjacentRoundTowardZero_mem_unboundedNormalized_of_nonneg_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a) (hbetween : a ≤ x ∧ x ≤ b) :
    fmt.unboundedNormalizedSystem (adjacentRoundTowardZero x a b) := by
  have hx_nonneg : 0 ≤ x := le_trans ha_nonneg hbetween.1
  by_cases hxb : x = b
  · have hb_nonneg : 0 ≤ b := by simpa [hxb] using hx_nonneg
    simpa [adjacentRoundTowardZero, adjacentRoundTowardNegative,
      not_lt.mpr hb_nonneg, hxb] using hadj.2.1
  · simpa [adjacentRoundTowardZero, adjacentRoundTowardNegative,
      not_lt.mpr hx_nonneg, hxb] using hadj.1
theorem adjacentRoundTowardZero_mem_unboundedNormalized_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0) (hbetween : a ≤ x ∧ x ≤ b) :
    fmt.unboundedNormalizedSystem (adjacentRoundTowardZero x a b) := by
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos hb_ne
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  by_cases hxa : x = a
  · have ha_neg : a < 0 := by simpa [hxa] using hx_neg
    simpa [adjacentRoundTowardZero, adjacentRoundTowardPositive, ha_neg,
      hxa] using hadj.1
  · simpa [adjacentRoundTowardZero, adjacentRoundTowardPositive, hx_neg,
      hxa] using hadj.2.1
theorem adjacentRoundTowardNegative_le_of_ordered_between
    {x a b : ℝ} (hbetween : a ≤ x ∧ x ≤ b) :
    adjacentRoundTowardNegative x a b ≤ x := by
  by_cases hxb : x = b
  · simp [adjacentRoundTowardNegative, hxb]
  · simpa [adjacentRoundTowardNegative, hxb] using hbetween.1
theorem le_adjacentRoundTowardPositive_of_ordered_between
    {x a b : ℝ} (hbetween : a ≤ x ∧ x ≤ b) :
    x ≤ adjacentRoundTowardPositive x a b := by
  by_cases hxa : x = a
  · simp [adjacentRoundTowardPositive, hxa]
  · simpa [adjacentRoundTowardPositive, hxa] using hbetween.2
theorem adjacentRoundTowardZero_nonneg_le_of_nonneg_between
    {x a b : ℝ} (ha_nonneg : 0 ≤ a) (hbetween : a ≤ x ∧ x ≤ b) :
    0 ≤ adjacentRoundTowardZero x a b ∧
      adjacentRoundTowardZero x a b ≤ x := by
  have hx_nonneg : 0 ≤ x := le_trans ha_nonneg hbetween.1
  by_cases hxb : x = b
  · constructor
    · have hb_nonneg : 0 ≤ b := by simpa [hxb] using hx_nonneg
      simpa [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hb_nonneg, hxb] using hb_nonneg
    · have hb_nonneg : 0 ≤ b := by simpa [hxb] using hx_nonneg
      simp [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hb_nonneg, hxb]
  · constructor
    · simpa [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hx_nonneg, hxb] using ha_nonneg
    · simpa [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hx_nonneg, hxb] using hbetween.1
theorem adjacentRoundTowardZero_le_nonpos_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0) (hbetween : a ≤ x ∧ x ≤ b) :
    x ≤ adjacentRoundTowardZero x a b ∧
      adjacentRoundTowardZero x a b ≤ 0 := by
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos hb_ne
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  have hx_nonpos : x ≤ 0 := le_trans hbetween.2 hb_nonpos
  by_cases hxa : x = a
  · constructor
    · have ha_neg : a < 0 := by simpa [hxa] using hx_neg
      simp [adjacentRoundTowardZero, adjacentRoundTowardPositive, ha_neg,
        hxa]
    · have ha_neg : a < 0 := by simpa [hxa] using hx_neg
      simpa [adjacentRoundTowardZero, adjacentRoundTowardPositive, ha_neg,
        hxa] using hx_nonpos
  · constructor
    · simpa [adjacentRoundTowardZero, adjacentRoundTowardPositive, hx_neg,
        hxa] using hbetween.2
    · simpa [adjacentRoundTowardZero, adjacentRoundTowardPositive, hx_neg,
        hxa] using hb_nonpos
theorem adjacentRoundTowardZero_abs_le_abs_of_nonneg_between
    {x a b : ℝ} (ha_nonneg : 0 ≤ a) (hbetween : a ≤ x ∧ x ≤ b) :
    |adjacentRoundTowardZero x a b| ≤ |x| := by
  have hx_nonneg : 0 ≤ x := le_trans ha_nonneg hbetween.1
  by_cases hxb : x = b
  · have hsel : adjacentRoundTowardZero x a b = x := by
      have hb_nonneg : 0 ≤ b := by simpa [hxb] using hx_nonneg
      simp [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hb_nonneg, hxb]
    rw [hsel]
  · have hsel : adjacentRoundTowardZero x a b = a := by
      simp [adjacentRoundTowardZero, adjacentRoundTowardNegative,
        not_lt.mpr hx_nonneg, hxb]
    rw [hsel, abs_of_nonneg ha_nonneg, abs_of_nonneg hx_nonneg]
    exact hbetween.1
theorem adjacentRoundTowardZero_abs_le_abs_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0) (hbetween : a ≤ x ∧ x ≤ b) :
    |adjacentRoundTowardZero x a b| ≤ |x| := by
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos hb_ne
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  have hx_nonpos : x ≤ 0 := le_trans hbetween.2 hb_nonpos
  by_cases hxa : x = a
  · have hsel : adjacentRoundTowardZero x a b = x := by
      have ha_neg : a < 0 := by simpa [hxa] using hx_neg
      simp [adjacentRoundTowardZero, adjacentRoundTowardPositive, ha_neg,
        hxa]
    rw [hsel]
  · have hsel : adjacentRoundTowardZero x a b = b := by
      simp [adjacentRoundTowardZero, adjacentRoundTowardPositive, hx_neg,
        hxa]
    rw [hsel, abs_of_nonpos hb_nonpos, abs_of_nonpos hx_nonpos]
    linarith
theorem exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y : ℝ, (y = a ∨ y = b) ∧ fmt.nearestRoundingToUnbounded x y := by
  rcases le_total |x - a| |x - b| with hleft | hright
  · exact ⟨a, Or.inl rfl,
      fmt.nearestRoundingToUnbounded_left_of_realOrderAdjacent_ordered_between
        hadj hbetween hleft⟩
  · exact ⟨b, Or.inr rfl,
      fmt.nearestRoundingToUnbounded_right_of_realOrderAdjacent_ordered_between
        hadj hbetween hright⟩
theorem nearestRoundingToUnbounded_abs_sub_le_half_adjacent_gap
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)) :
    |x - y| ≤ (1 / 2 : ℝ) * |a - b| := by
  have hsel :=
    fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_between
      hround hadj hbetween
  rcases hsel with hya | hyb
  · have hbetween_y : (y ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ y) := by
      simpa [hya] using hbetween
    have hhalf :=
      nearestRoundingIn_abs_sub_le_half_abs_sub_of_between
        hround hadj.2.1 hbetween_y
    simpa [hya] using hhalf
  · have hbetween' : (b ≤ x ∧ x ≤ a) ∨ (a ≤ x ∧ x ≤ b) := by
      rcases hbetween with hbetween | hbetween
      · exact Or.inr hbetween
      · exact Or.inl hbetween
    have hbetween_y : (y ≤ x ∧ x ≤ a) ∨ (a ≤ x ∧ x ≤ y) := by
      simpa [hyb] using hbetween'
    have hhalf :=
      nearestRoundingIn_abs_sub_le_half_abs_sub_of_between
        hround hadj.1 hbetween_y
    simpa [hyb, abs_sub_comm] using hhalf
theorem nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_anchor_of_realOrderAdjacent_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a))
    (hanchor : |a| ≤ |x|) :
    |x - y| ≤ fmt.unitRoundoff * |x| := by
  have hhalf :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_half_adjacent_gap
      hround hadj hbetween
  have hspace : |a - b| ≤ fmt.machineEpsilon * |a| :=
    (fmt.realOrderAdjacentNormalized_spacing_bounds_left hadj).2
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have heps_nonneg : 0 ≤ fmt.machineEpsilon := by
    unfold machineEpsilon
    exact le_of_lt (fmt.betaR_zpow_pos (1 - (fmt.t : ℤ)))
  have hgap_le :
      (1 / 2 : ℝ) * |a - b| ≤
        (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) :=
    mul_le_mul_of_nonneg_left hspace hhalf_nonneg
  have hanchor_le :
      fmt.machineEpsilon * |a| ≤ fmt.machineEpsilon * |x| :=
    mul_le_mul_of_nonneg_left hanchor heps_nonneg
  have hanchor_scaled :
      (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) ≤
        (1 / 2 : ℝ) * (fmt.machineEpsilon * |x|) :=
    mul_le_mul_of_nonneg_left hanchor_le hhalf_nonneg
  have hmain :
      |x - y| ≤ (1 / 2 : ℝ) * (fmt.machineEpsilon * |x|) :=
    le_trans hhalf (le_trans hgap_le hanchor_scaled)
  simpa [unitRoundoff, mul_assoc] using hmain
theorem nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonneg_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    |x - y| ≤ fmt.unitRoundoff * |x| := by
  have hx_nonneg : 0 ≤ x := le_trans ha_nonneg hbetween.1
  have hanchor : |a| ≤ |x| := by
    rw [abs_of_nonneg ha_nonneg, abs_of_nonneg hx_nonneg]
    exact hbetween.1
  exact
    fmt.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_anchor_of_realOrderAdjacent_between
      hround hadj (Or.inl hbetween) hanchor
theorem nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonpos_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    |x - y| ≤ fmt.unitRoundoff * |x| := by
  have hx_nonpos : x ≤ 0 := le_trans hbetween.2 hb_nonpos
  have hanchor : |b| ≤ |x| := by
    rw [abs_of_nonpos hb_nonpos, abs_of_nonpos hx_nonpos]
    linarith
  exact
    fmt.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_anchor_of_realOrderAdjacent_between
      hround (fmt.realOrderAdjacentNormalized_symm hadj) (Or.inr hbetween) hanchor
theorem nearestRoundingToUnbounded_abs_sub_lt_unitRoundoff_mul_self_of_nonneg_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    |x - y| < fmt.unitRoundoff * |x| := by
  have ha_ne : a ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.1
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (by
    intro hzero
    exact ha_ne hzero.symm)
  have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hbetween.1
  have hu_pos : 0 < fmt.unitRoundoff := fmt.unitRoundoff_pos
  have hhalf :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_half_adjacent_gap
      hround hadj (Or.inl hbetween)
  have hspace : |a - b| ≤ fmt.machineEpsilon * |a| :=
    (fmt.realOrderAdjacentNormalized_spacing_bounds_left hadj).2
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hgap_le :
      (1 / 2 : ℝ) * |a - b| ≤
        (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) :=
    mul_le_mul_of_nonneg_left hspace hhalf_nonneg
  have hmain_anchor :
      |x - y| ≤ fmt.unitRoundoff * |a| := by
    have hmain :
        |x - y| ≤ (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) :=
      le_trans hhalf hgap_le
    simpa [unitRoundoff, mul_assoc] using hmain
  have hsel :=
    fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
      hround hadj hbetween
  rcases hsel with hya | hyb
  · by_cases hxa : x = a
    · have hpos_rhs : 0 < fmt.unitRoundoff * |x| :=
        mul_pos hu_pos (abs_pos.mpr (by
          intro hxzero
          exact ha_ne (by simpa [hxa] using hxzero)))
      simpa [hxa, hya] using hpos_rhs
    · have ha_lt_x : a < x := lt_of_le_of_ne hbetween.1 (by
        intro hax
        exact hxa hax.symm)
      have hanchor_lt : fmt.unitRoundoff * |a| < fmt.unitRoundoff * |x| := by
        rw [abs_of_pos ha_pos, abs_of_pos hx_pos]
        exact mul_lt_mul_of_pos_left ha_lt_x hu_pos
      exact lt_of_le_of_lt hmain_anchor hanchor_lt
  · by_cases hxb : x = b
    · have hpos_rhs : 0 < fmt.unitRoundoff * |x| :=
        mul_pos hu_pos (abs_pos.mpr (by
          intro hxzero
          exact hb_ne (by simpa [hxb] using hxzero)))
      simpa [hxb, hyb] using hpos_rhs
    · by_cases hxa : x = a
      · have hmin_a :=
          nearestRoundingIn_minimal hround hadj.1
        have hgap_le_zero : |a - b| ≤ 0 := by
          simpa [hxa, hyb] using hmin_a
        have hgap_pos : 0 < |a - b| :=
          abs_pos.mpr (by
            intro hzero
            exact hadj.2.2.1 (sub_eq_zero.mp hzero))
        exact False.elim ((not_lt_of_ge hgap_le_zero) hgap_pos)
      · have ha_lt_x : a < x := lt_of_le_of_ne hbetween.1 (by
          intro hax
          exact hxa hax.symm)
        have hanchor_lt : fmt.unitRoundoff * |a| < fmt.unitRoundoff * |x| := by
          rw [abs_of_pos ha_pos, abs_of_pos hx_pos]
          exact mul_lt_mul_of_pos_left ha_lt_x hu_pos
        exact lt_of_le_of_lt hmain_anchor hanchor_lt
theorem nearestRoundingToUnbounded_abs_sub_lt_unitRoundoff_mul_self_of_nonpos_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    |x - y| < fmt.unitRoundoff * |x| := by
  have ha_ne : a ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.1
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos (by
    intro hzero
    exact hb_ne hzero)
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  have hu_pos : 0 < fmt.unitRoundoff := fmt.unitRoundoff_pos
  have hhalf :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_half_adjacent_gap
      hround hadj (Or.inl hbetween)
  have hspace : |a - b| ≤ fmt.machineEpsilon * |b| := by
    have hspace' :=
      (fmt.realOrderAdjacentNormalized_spacing_bounds_left
        (fmt.realOrderAdjacentNormalized_symm hadj)).2
    simpa [abs_sub_comm] using hspace'
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hgap_le :
      (1 / 2 : ℝ) * |a - b| ≤
        (1 / 2 : ℝ) * (fmt.machineEpsilon * |b|) :=
    mul_le_mul_of_nonneg_left hspace hhalf_nonneg
  have hmain_anchor :
      |x - y| ≤ fmt.unitRoundoff * |b| := by
    have hmain :
        |x - y| ≤ (1 / 2 : ℝ) * (fmt.machineEpsilon * |b|) :=
      le_trans hhalf hgap_le
    simpa [unitRoundoff, mul_assoc] using hmain
  have hsel :=
    fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
      hround hadj hbetween
  rcases hsel with hya | hyb
  · by_cases hxa : x = a
    · have hpos_rhs : 0 < fmt.unitRoundoff * |x| :=
        mul_pos hu_pos (abs_pos.mpr (by
          intro hxzero
          exact ha_ne (by simpa [hxa] using hxzero)))
      simpa [hxa, hya] using hpos_rhs
    · by_cases hxb : x = b
      · have hmin_b :=
          nearestRoundingIn_minimal hround hadj.2.1
        have hgap_le_zero : |b - a| ≤ 0 := by
          simpa [hxb, hya] using hmin_b
        have hgap_pos : 0 < |b - a| :=
          abs_pos.mpr (by
            intro hzero
            exact hadj.2.2.1 (sub_eq_zero.mp hzero).symm)
        exact False.elim ((not_lt_of_ge hgap_le_zero) hgap_pos)
      · have hx_lt_b : x < b := lt_of_le_of_ne hbetween.2 hxb
        have hanchor_lt : fmt.unitRoundoff * |b| < fmt.unitRoundoff * |x| := by
          rw [abs_of_neg hb_neg, abs_of_neg hx_neg]
          have hneg : -b < -x := neg_lt_neg hx_lt_b
          exact mul_lt_mul_of_pos_left hneg hu_pos
        exact lt_of_le_of_lt hmain_anchor hanchor_lt
  · by_cases hxb : x = b
    · have hpos_rhs : 0 < fmt.unitRoundoff * |x| :=
        mul_pos hu_pos (abs_pos.mpr (by
          intro hxzero
          exact hb_ne (by simpa [hxb] using hxzero)))
      simpa [hxb, hyb] using hpos_rhs
    · have hx_lt_b : x < b := lt_of_le_of_ne hbetween.2 hxb
      have hanchor_lt : fmt.unitRoundoff * |b| < fmt.unitRoundoff * |x| := by
        rw [abs_of_neg hb_neg, abs_of_neg hx_neg]
        have hneg : -b < -x := neg_lt_neg hx_lt_b
        exact mul_lt_mul_of_pos_left hneg hu_pos
      exact lt_of_le_of_lt hmain_anchor hanchor_lt
theorem nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_rounded_of_realOrderAdjacent_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : (a ≤ x ∧ x ≤ b) ∨ (b ≤ x ∧ x ≤ a)) :
    |x - y| ≤ fmt.unitRoundoff * |y| := by
  have hhalf :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_half_adjacent_gap
      hround hadj hbetween
  have hsel :=
    fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_between
      hround hadj hbetween
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  rcases hsel with hya | hyb
  · have hspace : |a - b| ≤ fmt.machineEpsilon * |a| :=
      (fmt.realOrderAdjacentNormalized_spacing_bounds_left hadj).2
    have hgap_le :
        (1 / 2 : ℝ) * |a - b| ≤
          (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) :=
      mul_le_mul_of_nonneg_left hspace hhalf_nonneg
    have hmain :
        |x - y| ≤ (1 / 2 : ℝ) * (fmt.machineEpsilon * |a|) :=
      le_trans hhalf hgap_le
    simpa [hya, unitRoundoff, mul_assoc] using hmain
  · have hspace : |a - b| ≤ fmt.machineEpsilon * |b| := by
      have hspace' :=
        (fmt.realOrderAdjacentNormalized_spacing_bounds_left
          (fmt.realOrderAdjacentNormalized_symm hadj)).2
      simpa [abs_sub_comm] using hspace'
    have hgap_le :
        (1 / 2 : ℝ) * |a - b| ≤
          (1 / 2 : ℝ) * (fmt.machineEpsilon * |b|) :=
      mul_le_mul_of_nonneg_left hspace hhalf_nonneg
    have hmain :
        |x - y| ≤ (1 / 2 : ℝ) * (fmt.machineEpsilon * |b|) :=
      le_trans hhalf hgap_le
    simpa [hyb, unitRoundoff, mul_assoc] using hmain
theorem signedRelErrorWitness_of_abs_sub_le_unitRoundoff_mul_abs
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : x ≠ 0)
    (hbound : |x - y| ≤ fmt.unitRoundoff * |x|) :
    ∃ δ : ℝ, |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases exists_signedRelErrorWitness_of_relErrorDefined y x hx with
    ⟨δ, hδ, hrel⟩
  refine ⟨δ, ?_, hδ⟩
  rw [← hrel]
  unfold relError
  have hxabs_pos : 0 < |x| := abs_pos.mpr hx
  have hbound' : |y - x| ≤ fmt.unitRoundoff * |x| := by
    simpa [abs_sub_comm] using hbound
  calc
    |y - x| / |x| ≤ (fmt.unitRoundoff * |x|) / |x| :=
      div_le_div_of_nonneg_right hbound' (abs_nonneg x)
    _ = fmt.unitRoundoff := by
      field_simp [ne_of_gt hxabs_pos]
theorem signedRelErrorWitness_of_abs_sub_lt_unitRoundoff_mul_abs
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : x ≠ 0)
    (hbound : |x - y| < fmt.unitRoundoff * |x|) :
    ∃ δ : ℝ, |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases exists_signedRelErrorWitness_of_relErrorDefined y x hx with
    ⟨δ, hδ, hrel⟩
  refine ⟨δ, ?_, hδ⟩
  rw [← hrel]
  unfold relError
  have hxabs_pos : 0 < |x| := abs_pos.mpr hx
  have hbound' : |y - x| < fmt.unitRoundoff * |x| := by
    simpa [abs_sub_comm] using hbound
  calc
    |y - x| / |x| < (fmt.unitRoundoff * |x|) / |x| :=
      div_lt_div_of_pos_right hbound' hxabs_pos
    _ = fmt.unitRoundoff := by
      field_simp [ne_of_gt hxabs_pos]
theorem nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| ≤ fmt.unitRoundoff ∧
        signedRelErrorWitness y x δ ∧
          fmt.nearestRoundingToUnbounded x y := by
  have ha_ne : a ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.1
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (by
    intro hzero
    exact ha_ne hzero.symm)
  have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hbetween.1
  have hbound :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonneg_between
      hround hadj ha_nonneg hbetween
  rcases fmt.signedRelErrorWitness_of_abs_sub_le_unitRoundoff_mul_abs
      (ne_of_gt hx_pos) hbound with ⟨δ, hδ, hwit⟩
  exact ⟨δ, hδ, hwit, hround⟩
theorem nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| ≤ fmt.unitRoundoff ∧
        signedRelErrorWitness y x δ ∧
          fmt.nearestRoundingToUnbounded x y := by
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos (by
    intro hzero
    exact hb_ne hzero)
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  have hbound :=
    fmt.nearestRoundingToUnbounded_abs_sub_le_unitRoundoff_mul_self_of_nonpos_between
      hround hadj hb_nonpos hbetween
  rcases fmt.signedRelErrorWitness_of_abs_sub_le_unitRoundoff_mul_abs
      (ne_of_lt hx_neg) hbound with ⟨δ, hδ, hwit⟩
  exact ⟨δ, hδ, hwit, hround⟩
theorem nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness y x δ ∧
          fmt.nearestRoundingToUnbounded x y := by
  have ha_ne : a ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.1
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (by
    intro hzero
    exact ha_ne hzero.symm)
  have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hbetween.1
  have hbound :=
    fmt.nearestRoundingToUnbounded_abs_sub_lt_unitRoundoff_mul_self_of_nonneg_between
      hround hadj ha_nonneg hbetween
  rcases fmt.signedRelErrorWitness_of_abs_sub_lt_unitRoundoff_mul_abs
      (ne_of_gt hx_pos) hbound with ⟨δ, hδ, hwit⟩
  exact ⟨δ, hδ, hwit, hround⟩
theorem nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness y x δ ∧
          fmt.nearestRoundingToUnbounded x y := by
  have hb_ne : b ≠ 0 :=
    fmt.unboundedNormalizedSystem_ne_zero hadj.2.1
  have hb_neg : b < 0 := lt_of_le_of_ne hb_nonpos (by
    intro hzero
    exact hb_ne hzero)
  have hx_neg : x < 0 := lt_of_le_of_lt hbetween.2 hb_neg
  have hbound :=
    fmt.nearestRoundingToUnbounded_abs_sub_lt_unitRoundoff_mul_self_of_nonpos_between
      hround hadj hb_nonpos hbetween
  rcases fmt.signedRelErrorWitness_of_abs_sub_lt_unitRoundoff_mul_abs
      (ne_of_lt hx_neg) hbound with ⟨δ, hδ, hwit⟩
  exact ⟨δ, hδ, hwit, hround⟩
/-- The explicit local round-away selector inherits Higham's strict
source-relative error witness on nonnegative adjacent brackets. -/
theorem nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonneg_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness (nearestAdjacentRoundAway x a b) x δ ∧
          fmt.nearestRoundingToUnbounded x (nearestAdjacentRoundAway x a b) := by
  have hround :=
    fmt.nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween
  rcases
    fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
      hround hadj ha_nonneg hbetween with
    ⟨δ, hδ, hwit, hround'⟩
  exact ⟨δ, hδ, hwit, hround'⟩
/-- The explicit local round-away selector inherits Higham's strict
source-relative error witness on nonpositive adjacent brackets. -/
theorem nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧
        signedRelErrorWitness (nearestAdjacentRoundAway x a b) x δ ∧
          fmt.nearestRoundingToUnbounded x (nearestAdjacentRoundAway x a b) := by
  have hround :=
    fmt.nearestAdjacentRoundAway_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween
  rcases
    fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
      hround hadj hb_nonpos hbetween with
    ⟨δ, hδ, hwit, hround'⟩
  exact ⟨δ, hδ, hwit, hround'⟩
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween with ⟨y, _hyab, hround⟩
  rcases fmt.nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between
      hround hadj ha_nonneg hbetween with ⟨δ, hδ, hwit, _⟩
  exact ⟨y, δ, hround, hδ, hwit⟩
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween with ⟨y, _hyab, hround⟩
  rcases fmt.nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between
      hround hadj hb_nonpos hbetween with ⟨δ, hδ, hwit, _⟩
  exact ⟨y, δ, hround, hδ, hwit⟩
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (ha_nonneg : 0 ≤ a)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween with ⟨y, _hyab, hround⟩
  rcases fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
      hround hadj ha_nonneg hbetween with ⟨δ, hδ, hwit, _⟩
  exact ⟨y, δ, hround, hδ, hwit⟩
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
    {fmt : FloatingPointFormat} {x a b : ℝ}
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hb_nonpos : b ≤ 0)
    (hbetween : a ≤ x ∧ x ≤ b) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
      hadj hbetween with ⟨y, _hyab, hround⟩
  rcases fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
      hround hadj hb_nonpos hbetween with ⟨δ, hδ, hwit, _⟩
  exact ⟨y, δ, hround, hδ, hwit⟩
/-- Same-exponent positive nearest-rounding theorem.  Once a positive input
is known to lie between the smallest and largest normalized values at a fixed
exponent, the floor bracketing theorem and local adjacent-rounding bounds
produce Higham's signed relative-error witness for nearest rounding in `G`. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x)
    (hmax : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
      hmin hmax with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨false, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between
        hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩
/-- Same-exponent negative-bin nearest-rounding theorem.  This is the sign
mirror of the positive fixed-exponent theorem and packages the adjacent-bracket
core into Higham's signed relative-error form for negative inputs in one
exponent bin. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x)
    (hhi : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative
      hlo hhi with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨true, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between
        hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_sameExponent_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x)
    (hmax : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
      hmin hmax with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨false, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
        hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_sameExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x)
    (hhi : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative
      hlo hhi with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨true, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b⟩
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
        hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩
/-- Same-exponent positive theorem with the local round-away selector exposed.
In the exact case the selected value is `x`; in the adjacent-bracket case it is
`nearestAdjacentRoundAway x a b`. -/
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x)
    (hmax : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue false m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
      hmin hmax with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨false, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b⟩
    rcases
      fmt.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonneg_between
        hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩ with
      ⟨δ, hδ, hwit, hround⟩
    exact
      ⟨nearestAdjacentRoundAway x a b, δ, hround, hδ, hwit,
        Or.inr ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩
/-- Same-exponent negative theorem with the local round-away selector exposed.
In the exact case the selected value is `x`; in the adjacent-bracket case it is
`nearestAdjacentRoundAway x a b`. -/
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x)
    (hhi : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue true m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative
      hlo hhi with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hx_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨true, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact ⟨x, δ, hround, hδ, hwit, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b⟩
    rcases
      fmt.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonpos_between
        hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩ with
      ⟨δ, hδ, hwit, hround⟩
    exact
      ⟨nearestAdjacentRoundAway x a b, δ, hround, hδ, hwit,
        Or.inr ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩
/-- Source-shaped positive fixed-exponent interval version of the local
Theorem 2.2 bridge.  The hypotheses are the displayed lower and upper
normalized endpoints for one exponent bin. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.betaR ^ (e - 1) ≤ x)
    (hmax : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hmin' : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hmin
  have hmax' : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e := by
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hmax
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_positive
      (e := e) hmin' hmax'
/-- Source-shaped negative fixed-exponent interval version of the local
Theorem 2.2 bridge.  The hypotheses are the negated upper/lower displayed
endpoints for one exponent bin. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hlo' : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hhi' : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_sameExponent_negative
      (e := e) hlo' hhi'
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerInterval_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.betaR ^ (e - 1) ≤ x)
    (hmax : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hmin' : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hmin
  have hmax' : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e := by
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hmax
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_sameExponent_positive
      (e := e) hmin' hmax'
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerInterval_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hlo' : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hhi' : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_sameExponent_negative
      (e := e) hlo' hhi'
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.betaR ^ (e - 1) ≤ x)
    (hmax : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue false m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  have hmin' : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hmin
  have hmax' : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e := by
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hmax
  exact
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_positive
      (e := e) hmin' hmax'
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue true m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  have hlo' : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hhi' : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e := by
    rw [fmt.normalizedValue_true_eq_neg_false,
      fmt.normalizedValue_false_minNormalMantissa_eq]
    exact hhi
  exact
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_sameExponent_negative
      (e := e) hlo' hhi'
/-- Source-shaped positive exponent-boundary interval version of the local
Theorem 2.2 bridge.  This covers the gap between the largest value at exponent
`e` and the smallest value at exponent `e+1`. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa e
  let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, e, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_nonneg : 0 ≤ a :=
    le_of_lt
      (fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue false fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue false fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonneg_between
      hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩
/-- Source-shaped negative exponent-boundary interval version of the local
Theorem 2.2 bridge.  This is the sign mirror of the positive boundary case. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  let a := fmt.normalizedValue true fmt.minNormalMantissa (e + 1)
  let b := fmt.normalizedValue true fmt.maxNormalMantissa e
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨true, e, Or.inr ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hb_nonpos : b ≤ 0 :=
    le_of_lt
      (fmt.normalizedValue_true_neg
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
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
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_of_nonpos_between
      hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerBoundary_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa e
  let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, e, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_nonneg : 0 ≤ a :=
    le_of_lt
      (fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue false fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue false fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hhi
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
      hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerBoundary_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  let a := fmt.normalizedValue true fmt.minNormalMantissa (e + 1)
  let b := fmt.normalizedValue true fmt.maxNormalMantissa e
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨true, e, Or.inr ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hb_nonpos : b ≤ 0 :=
    le_of_lt
      (fmt.normalizedValue_true_neg
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
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
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
      hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ ∧
          ∃ a b : ℝ,
            fmt.realOrderAdjacentNormalized a b ∧
              0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                y = nearestAdjacentRoundAway x a b := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa e
  let b := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, e, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have ha_nonneg : 0 ≤ a :=
    le_of_lt
      (fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
  have ha_le_x : a ≤ x := by
    rw [show a = fmt.normalizedValue false fmt.maxNormalMantissa e from rfl]
    rw [fmt.normalizedValue_false_maxNormalMantissa_eq]
    exact hlo
  have hx_le_b : x ≤ b := by
    rw [show b = fmt.normalizedValue false fmt.minNormalMantissa (e + 1) from rfl]
    rw [fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
    exact hhi
  rcases
    fmt.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonneg_between
      hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩ with
    ⟨δ, hδ, hwit, hround⟩
  exact
    ⟨nearestAdjacentRoundAway x a b, δ, hround, hδ, hwit,
      ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ ∧
          ∃ a b : ℝ,
            fmt.realOrderAdjacentNormalized a b ∧
              b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                y = nearestAdjacentRoundAway x a b := by
  let a := fmt.normalizedValue true fmt.minNormalMantissa (e + 1)
  let b := fmt.normalizedValue true fmt.maxNormalMantissa e
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨true, e, Or.inr ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hb_nonpos : b ≤ 0 :=
    le_of_lt
      (fmt.normalizedValue_true_neg
        (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized)
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
  rcases
    fmt.nearestAdjacentRoundAway_signedRelErrorWitness_lt_of_nonpos_between
      hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩ with
    ⟨δ, hδ, hwit, hround⟩
  exact
    ⟨nearestAdjacentRoundAway x a b, δ, hround, hδ, hwit,
      ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩
/-- Source-shaped positive one-exponent slice for the local Theorem 2.2 bridge.
The interval is split at the largest normalized value with exponent `e`; the
right-hand part is the exponent-boundary gap to the smallest value at
exponent `e+1`. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ (e - 1) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  by_cases hbin : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))
  · exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_positive
        (e := e) hlo hbin
  · have hgap_lo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x :=
      le_of_lt (lt_of_not_ge hbin)
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_positive
        (e := e) hgap_lo hhi
/-- Source-shaped negative one-exponent slice for the local Theorem 2.2 bridge.
This is the sign mirror of the positive slice, splitting at the negated largest
normalized value with exponent `e`. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  by_cases hboundary : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))
  · exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerBoundary_negative
        (e := e) hlo hboundary
  · have hinterval_lo :
        -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x :=
      le_of_lt (lt_of_not_ge hboundary)
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerInterval_negative
        (e := e) hinterval_lo hhi
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerSlice_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ (e - 1) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  by_cases hbin : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))
  · exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerInterval_positive
        (e := e) hlo hbin
  · have hgap_lo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x :=
      le_of_lt (lt_of_not_ge hbin)
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerBoundary_positive
        (e := e) hgap_lo hhi
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerSlice_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  by_cases hboundary : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))
  · exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerBoundary_negative
        (e := e) hlo hboundary
  · have hinterval_lo :
        -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x :=
      le_of_lt (lt_of_not_ge hboundary)
    exact
      fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerInterval_negative
        (e := e) hinterval_lo hhi
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_positive
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.betaR ^ (e - 1) ≤ x)
    (hhi : x ≤ fmt.betaR ^ e) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue false m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  by_cases hbin : x ≤ fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))
  · exact
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_positive
        (e := e) hlo hbin
  · have hgap_lo : fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))) ≤ x :=
      le_of_lt (lt_of_not_ge hbin)
    rcases
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_positive
        (e := e) hgap_lo hhi with
      ⟨y, δ, hround, hδ, hwit, hpolicy⟩
    exact ⟨y, δ, hround, hδ, hwit, Or.inr hpolicy⟩
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : -(fmt.betaR ^ e) ≤ x)
    (hhi : x ≤ -(fmt.betaR ^ (e - 1))) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ m : ℕ,
                fmt.normalizedMantissa m ∧
                  x = fmt.normalizedValue true m e ∧ y = x) ∨
              ∃ a b : ℝ,
                fmt.realOrderAdjacentNormalized a b ∧
                  b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                    y = nearestAdjacentRoundAway x a b) := by
  by_cases hboundary : x ≤ -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ))))
  · rcases
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerBoundary_negative
        (e := e) hlo hboundary with
      ⟨y, δ, hround, hδ, hwit, hpolicy⟩
    exact ⟨y, δ, hround, hδ, hwit, Or.inr hpolicy⟩
  · have hinterval_lo :
        -(fmt.betaR ^ e * (1 - fmt.betaR ^ (-(fmt.t : ℤ)))) ≤ x :=
      le_of_lt (lt_of_not_ge hboundary)
    exact
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerInterval_negative
        (e := e) hinterval_lo hhi
/-- Global positive exponent selection for the source-shaped power slices:
every positive real lies in some interval `beta^(e-1) <= x <= beta^e`. -/
theorem exists_powerSliceExponent_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ e : ℤ, fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e := by
  have hbeta : 1 < fmt.betaR := by
    unfold betaR
    exact_mod_cast fmt.one_lt_beta
  rcases exists_mem_Ioc_zpow (K := ℝ) (x := x) (y := fmt.betaR) hx hbeta with
    ⟨n, hn⟩
  rcases Set.mem_Ioc.mp hn with ⟨hlo, hhi⟩
  refine ⟨n + 1, ?_, ?_⟩
  · have hexp : (n + 1 - 1 : ℤ) = n := by ring
    simpa [hexp] using le_of_lt hlo
  · exact hhi
/-- Global negative exponent selection, mirrored from the positive source
power-slice selection theorem. -/
theorem exists_powerSliceExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ e : ℤ, -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) := by
  have hneg_pos : 0 < -x := by linarith
  rcases fmt.exists_powerSliceExponent_positive (x := -x) hneg_pos with
    ⟨e, hlo, hhi⟩
  exact ⟨e, by linarith, by linarith⟩
/-- Global positive unbounded-normalized nearest-rounding bridge for the
non-strict Theorem 2.2 relative-error witness. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_powerSliceExponent_positive (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_positive
      (e := e) hlo hhi
/-- Global negative unbounded-normalized nearest-rounding bridge for the
non-strict Theorem 2.2 relative-error witness. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_powerSliceExponent_negative (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_powerSlice_negative
      (e := e) hlo hhi
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_powerSliceExponent_positive (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerSlice_positive
      (e := e) hlo hhi
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_powerSliceExponent_negative (x := x) hx with ⟨e, hlo, hhi⟩
  exact
    fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_powerSlice_negative
      (e := e) hlo hhi
/-- Global positive unbounded-normalized nearest-rounding bridge that carries
the explicit local round-away selector evidence through exponent selection. -/
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ∃ e : ℤ,
              fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
                ((∃ m : ℕ,
                    fmt.normalizedMantissa m ∧
                      x = fmt.normalizedValue false m e ∧ y = x) ∨
                  ∃ a b : ℝ,
                    fmt.realOrderAdjacentNormalized a b ∧
                      0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                        y = nearestAdjacentRoundAway x a b) := by
  rcases fmt.exists_powerSliceExponent_positive (x := x) hx with ⟨e, hlo, hhi⟩
  rcases
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_positive
      (e := e) hlo hhi with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  exact ⟨y, δ, hround, hδ, hwit, ⟨e, hlo, hhi, hpolicy⟩⟩
/-- Global negative unbounded-normalized nearest-rounding bridge that carries
the explicit local round-away selector evidence through exponent selection. -/
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ∃ e : ℤ,
              -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
                ((∃ m : ℕ,
                    fmt.normalizedMantissa m ∧
                      x = fmt.normalizedValue true m e ∧ y = x) ∨
                  ∃ a b : ℝ,
                    fmt.realOrderAdjacentNormalized a b ∧
                      b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                        y = nearestAdjacentRoundAway x a b) := by
  rcases fmt.exists_powerSliceExponent_negative (x := x) hx with ⟨e, hlo, hhi⟩
  rcases
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_powerSlice_negative
      (e := e) hlo hhi with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  exact ⟨y, δ, hround, hδ, hwit, ⟨e, hlo, hhi, hpolicy⟩⟩
/-- Global nonzero unbounded-normalized nearest-rounding bridge.  This closes
the exponent-selection part of the non-strict Theorem 2.2 foundation for `G`;
finite-format overflow/underflow and total tie-policy surfaces are separate. -/
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_nonzero
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x ≠ 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_negative hneg
  · exact False.elim (hx hzero)
  · exact fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_positive hpos
theorem exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_nonzero
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x ≠ 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_negative hneg
  · exact False.elim (hx hzero)
  · exact fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_positive hpos
/-- Global nonzero unbounded-normalized nearest-rounding bridge with explicit
local round-away selector evidence.  This is still an existential source-level
bridge for `G`, not a total finite-format rounding function. -/
theorem exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_nonzero
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x ≠ 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            ((∃ e : ℤ,
                fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
                  ((∃ m : ℕ,
                      fmt.normalizedMantissa m ∧
                        x = fmt.normalizedValue false m e ∧ y = x) ∨
                    ∃ a b : ℝ,
                      fmt.realOrderAdjacentNormalized a b ∧
                        0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                          y = nearestAdjacentRoundAway x a b)) ∨
              ∃ e : ℤ,
                -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
                  ((∃ m : ℕ,
                      fmt.normalizedMantissa m ∧
                        x = fmt.normalizedValue true m e ∧ y = x) ∨
                    ∃ a b : ℝ,
                      fmt.realOrderAdjacentNormalized a b ∧
                        b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                          y = nearestAdjacentRoundAway x a b)) := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · rcases
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
        hneg with
      ⟨y, δ, hround, hδ, hwit, hpolicy⟩
    exact ⟨y, δ, hround, hδ, hwit, Or.inr hpolicy⟩
  · exact False.elim (hx hzero)
  · rcases
      fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
        hpos with
      ⟨y, δ, hround, hδ, hwit, hpolicy⟩
    exact ⟨y, δ, hround, hδ, hwit, Or.inl hpolicy⟩
/-- Evidence that a source-level nearest-rounded output was obtained by the
local round-away selector after choosing a signed exponent slice.  Exact
representable inputs are allowed to return themselves; non-exact inputs expose
the adjacent bracket and the value `nearestAdjacentRoundAway x a b`. -/
def sourceRoundAwayEvidence (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  (∃ e : ℤ,
    fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue false m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
              y = nearestAdjacentRoundAway x a b)) ∨
  ∃ e : ℤ,
    -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue true m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
              y = nearestAdjacentRoundAway x a b)
/-- Evidence that a source-level nearest-rounded output was obtained by the
local round-to-even selector after choosing a signed exponent slice.  In an
adjacent-bracket case the evidence records the normalized mantissa of the left
endpoint in the real-order bracket; exact representable inputs return
themselves.  This is a source-facing tie-policy witness, not an IEEE operation
semantics. -/
def sourceRoundToEvenEvidence (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  (∃ e : ℤ,
    fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue false m e ∧ y = x) ∨
        ∃ a b : ℝ,
          ∃ leftMantissa : ℕ,
            fmt.realOrderAdjacentNormalized a b ∧
              (∃ negative eLeft,
                fmt.normalizedMantissa leftMantissa ∧
                  a = fmt.normalizedValue negative leftMantissa eLeft) ∧
                0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
                  y = nearestAdjacentRoundToEven x a b leftMantissa)) ∨
  ∃ e : ℤ,
    -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue true m e ∧ y = x) ∨
        ∃ a b : ℝ,
          ∃ leftMantissa : ℕ,
            fmt.realOrderAdjacentNormalized a b ∧
              (∃ negative eLeft,
                fmt.normalizedMantissa leftMantissa ∧
                  a = fmt.normalizedValue negative leftMantissa eLeft) ∧
                b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
                  y = nearestAdjacentRoundToEven x a b leftMantissa)
theorem realOrderAdjacentNormalized_right_mantissa_parity
    {fmt : FloatingPointFormat} {a b : ℝ} {leftMantissa : ℕ}
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hleft :
      ∃ negative eLeft,
        fmt.normalizedMantissa leftMantissa ∧
          a = fmt.normalizedValue negative leftMantissa eLeft) :
    ∃ rightMantissa negativeRight eRight,
      fmt.normalizedMantissa rightMantissa ∧
        b = fmt.normalizedValue negativeRight rightMantissa eRight ∧
          (evenMantissa rightMantissa ↔ ¬ evenMantissa leftMantissa) := by
  rcases hleft with ⟨negativeLeft, eLeft, hmLeft, haLeft⟩
  rcases fmt.adjacentNormalized_of_realOrderAdjacentNormalized hadj with
    hsame | hboundary
  · rcases hsame with ⟨negative, m, e, hm, hmnext, hab⟩
    rcases hab with hab | hab
    · rcases hab with ⟨ha, hb⟩
      have hleft_eq : leftMantissa = m := by
        have hval :
            fmt.normalizedValue negativeLeft leftMantissa eLeft =
              fmt.normalizedValue negative m e := by
          rw [← haLeft, ha]
        exact (fmt.normalizedValue_eq_sign_exp_mantissa hmLeft hm hval).2.2
      exact
        ⟨m + 1, negative, e, hmnext, hb,
          by simpa [hleft_eq] using
            (evenMantissa_succ_iff_not_evenMantissa m)⟩
    · rcases hab with ⟨ha, hb⟩
      have hleft_eq : leftMantissa = m + 1 := by
        have hval :
            fmt.normalizedValue negativeLeft leftMantissa eLeft =
              fmt.normalizedValue negative (m + 1) e := by
          rw [← haLeft, ha]
        exact (fmt.normalizedValue_eq_sign_exp_mantissa hmLeft hmnext hval).2.2
      exact
        ⟨m, negative, e, hm, hb,
          by simpa [hleft_eq] using
            (evenMantissa_iff_not_evenMantissa_succ m)⟩
  · rcases hboundary with ⟨negative, e, hab⟩
    rcases hab with hab | hab
    · rcases hab with ⟨ha, hb⟩
      have hleft_eq : leftMantissa = fmt.maxNormalMantissa := by
        have hval :
            fmt.normalizedValue negativeLeft leftMantissa eLeft =
              fmt.normalizedValue negative fmt.maxNormalMantissa e := by
          rw [← haLeft, ha]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hmLeft fmt.maxNormalMantissa_normalized hval).2.2
      exact
        ⟨fmt.minNormalMantissa, negative, e + 1,
          fmt.minNormalMantissa_normalized, hb,
          by simpa [hleft_eq] using
            (fmt.evenMantissa_minNormalMantissa_iff_not_evenMantissa_maxNormalMantissa_of_even_beta
              hbeta ht)⟩
    · rcases hab with ⟨ha, hb⟩
      have hleft_eq : leftMantissa = fmt.minNormalMantissa := by
        have hval :
            fmt.normalizedValue negativeLeft leftMantissa eLeft =
              fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) := by
          rw [← haLeft, ha]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hmLeft fmt.minNormalMantissa_normalized hval).2.2
      exact
        ⟨fmt.maxNormalMantissa, negative, e,
          fmt.maxNormalMantissa_normalized, hb,
          by simpa [hleft_eq] using
            (fmt.evenMantissa_maxNormalMantissa_iff_not_evenMantissa_minNormalMantissa_of_even_beta
              hbeta ht)⟩
theorem sourceRoundToEvenEvidence_neg
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (hpolicy : fmt.sourceRoundToEvenEvidence x y) :
    fmt.sourceRoundToEvenEvidence (-x) (-y) := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, hlo, hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_neg :
          -x = fmt.normalizedValue true m e := by
        rw [hx_eq]
        exact (fmt.normalizedValue_not_eq_neg false m e).symm
      have hy_neg : -y = -x := by
        rw [hy_eq]
      exact
        Or.inr ⟨e, by linarith, by linarith,
          Or.inl ⟨m, hm, hx_neg, hy_neg⟩⟩
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, hleft, ha_nonneg,
          ha_le_x, hx_le_b, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_right_mantissa_parity
            hbeta ht hadj hleft with
        ⟨rightMantissa, negativeRight, eRight, hmRight, hb_repr, hparity⟩
      have hleft_neg :
          ∃ negative eLeft,
            fmt.normalizedMantissa rightMantissa ∧
              -b = fmt.normalizedValue negative rightMantissa eLeft := by
        refine ⟨!negativeRight, eRight, hmRight, ?_⟩
        rw [hb_repr]
        exact (fmt.normalizedValue_not_eq_neg negativeRight rightMantissa eRight).symm
      have hy_neg :
          -y =
            nearestAdjacentRoundToEven (-x) (-b) (-a) rightMantissa := by
        rw [hy_eq]
        exact
          (nearestAdjacentRoundToEven_neg_of_even_right_iff_not_even_left
            (x := x) (a := a) (b := b)
            (leftMantissa := leftMantissa)
            (rightMantissa := rightMantissa) hparity).symm
      exact
        Or.inr ⟨e, by linarith, by linarith,
          Or.inr
            ⟨-b, -a, rightMantissa,
              fmt.realOrderAdjacentNormalized_neg_ordered hadj,
              hleft_neg,
              by linarith,
              by linarith,
              by linarith,
              hy_neg⟩⟩
  · rcases hneg with ⟨e, hlo, hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_neg :
          -x = fmt.normalizedValue false m e := by
        rw [hx_eq]
        exact (fmt.normalizedValue_not_eq_neg true m e).symm
      have hy_neg : -y = -x := by
        rw [hy_eq]
      exact
        Or.inl ⟨e, by linarith, by linarith,
          Or.inl ⟨m, hm, hx_neg, hy_neg⟩⟩
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, hleft, hb_nonpos,
          ha_le_x, hx_le_b, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_right_mantissa_parity
            hbeta ht hadj hleft with
        ⟨rightMantissa, negativeRight, eRight, hmRight, hb_repr, hparity⟩
      have hleft_neg :
          ∃ negative eLeft,
            fmt.normalizedMantissa rightMantissa ∧
              -b = fmt.normalizedValue negative rightMantissa eLeft := by
        refine ⟨!negativeRight, eRight, hmRight, ?_⟩
        rw [hb_repr]
        exact (fmt.normalizedValue_not_eq_neg negativeRight rightMantissa eRight).symm
      have hy_neg :
          -y =
            nearestAdjacentRoundToEven (-x) (-b) (-a) rightMantissa := by
        rw [hy_eq]
        exact
          (nearestAdjacentRoundToEven_neg_of_even_right_iff_not_even_left
            (x := x) (a := a) (b := b)
            (leftMantissa := leftMantissa)
            (rightMantissa := rightMantissa) hparity).symm
      exact
        Or.inl ⟨e, by linarith, by linarith,
          Or.inr
            ⟨-b, -a, rightMantissa,
              fmt.realOrderAdjacentNormalized_neg_ordered hadj,
              hleft_neg,
              by linarith,
              by linarith,
              by linarith,
              hy_neg⟩⟩
/-- Evidence that a source-level output was obtained by local rounding toward
negative infinity after choosing a signed exponent slice.  Exact representable
inputs return themselves; non-exact inputs expose the adjacent bracket and the
exact-endpoint-preserving local selector. -/
def sourceRoundTowardNegativeEvidence
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  (∃ e : ℤ,
    fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue false m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardNegative x a b)) ∨
  ∃ e : ℤ,
    -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue true m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardNegative x a b)
/-- Evidence that a source-level output was obtained by local rounding toward
positive infinity after choosing a signed exponent slice. -/
def sourceRoundTowardPositiveEvidence
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  (∃ e : ℤ,
    fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue false m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardPositive x a b)) ∨
  ∃ e : ℤ,
    -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue true m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardPositive x a b)
/-- Evidence that a source-level output was obtained by local rounding toward
zero after choosing a signed exponent slice. -/
def sourceRoundTowardZeroEvidence
    (fmt : FloatingPointFormat) (x y : ℝ) : Prop :=
  (∃ e : ℤ,
    fmt.betaR ^ (e - 1) ≤ x ∧ x ≤ fmt.betaR ^ e ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue false m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            0 ≤ a ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardZero x a b)) ∨
  ∃ e : ℤ,
    -(fmt.betaR ^ e) ≤ x ∧ x ≤ -(fmt.betaR ^ (e - 1)) ∧
      ((∃ m : ℕ,
          fmt.normalizedMantissa m ∧
            x = fmt.normalizedValue true m e ∧ y = x) ∨
        ∃ a b : ℝ,
          fmt.realOrderAdjacentNormalized a b ∧
            b ≤ 0 ∧ a ≤ x ∧ x ≤ b ∧
              y = adjacentRoundTowardZero x a b)
theorem finiteNormalRange_ne_zero
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    x ≠ 0 := by
  intro hx_zero
  have hmin_pos := fmt.minNormalMagnitude_pos
  have hxlo := hx.1
  rw [hx_zero, abs_zero] at hxlo
  exact (not_lt_of_ge hxlo) hmin_pos
theorem sourceRoundTowardNegativeEvidence_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardNegativeEvidence x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨false, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, _ha_nonneg, _ha_le_x, _hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact fmt.adjacentRoundTowardNegative_mem_unboundedNormalized hadj
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨true, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, _hb_nonpos, _ha_le_x, _hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact fmt.adjacentRoundTowardNegative_mem_unboundedNormalized hadj
theorem sourceRoundTowardPositiveEvidence_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardPositiveEvidence x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨false, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, _ha_nonneg, _ha_le_x, _hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact fmt.adjacentRoundTowardPositive_mem_unboundedNormalized hadj
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨true, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, _hb_nonpos, _ha_le_x, _hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact fmt.adjacentRoundTowardPositive_mem_unboundedNormalized hadj
theorem sourceRoundTowardZeroEvidence_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardZeroEvidence x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨false, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        fmt.adjacentRoundTowardZero_mem_unboundedNormalized_of_nonneg_between
          hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      exact ⟨true, m, e, hm, by rw [hy_eq, hx_eq]⟩
    · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        fmt.adjacentRoundTowardZero_mem_unboundedNormalized_of_nonpos_between
          hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩
theorem sourceRoundTowardNegativeEvidence_le
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardNegativeEvidence x y) :
    y ≤ x := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, _hadj, _ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact adjacentRoundTowardNegative_le_of_ordered_between ⟨ha_le_x, hx_le_b⟩
  · rcases hneg with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, _hadj, _hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact adjacentRoundTowardNegative_le_of_ordered_between ⟨ha_le_x, hx_le_b⟩
theorem sourceRoundTowardPositiveEvidence_le
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardPositiveEvidence x y) :
    x ≤ y := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, _hadj, _ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact le_adjacentRoundTowardPositive_of_ordered_between ⟨ha_le_x, hx_le_b⟩
  · rcases hneg with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, _hadj, _hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact le_adjacentRoundTowardPositive_of_ordered_between ⟨ha_le_x, hx_le_b⟩
theorem sourceRoundTowardZeroEvidence_abs_le_abs
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundTowardZeroEvidence x y) :
    |y| ≤ |x| := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, _hadj, ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        adjacentRoundTowardZero_abs_le_abs_of_nonneg_between
          ha_nonneg ⟨ha_le_x, hx_le_b⟩
  · rcases hneg with ⟨_e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      rw [hy_eq]
    · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        fmt.adjacentRoundTowardZero_abs_le_abs_of_nonpos_between
          hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩
theorem exists_sourceRoundTowardNegativeEvidence_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y : ℝ, fmt.sourceRoundTowardNegativeEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inl ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardNegative x a b,
        Or.inl ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩⟩
theorem exists_sourceRoundTowardNegativeEvidence_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y : ℝ, fmt.sourceRoundTowardNegativeEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inr ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardNegative x a b,
        Or.inr ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩⟩
theorem exists_sourceRoundTowardPositiveEvidence_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y : ℝ, fmt.sourceRoundTowardPositiveEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inl ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardPositive x a b,
        Or.inl ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩⟩
theorem exists_sourceRoundTowardPositiveEvidence_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y : ℝ, fmt.sourceRoundTowardPositiveEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inr ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardPositive x a b,
        Or.inr ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩⟩
theorem exists_sourceRoundTowardZeroEvidence_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y : ℝ, fmt.sourceRoundTowardZeroEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inl ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardZero x a b,
        Or.inl ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩⟩
theorem exists_sourceRoundTowardZeroEvidence_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y : ℝ, fmt.sourceRoundTowardZeroEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
      (x := x) hx with
    ⟨_y, _δ, _hround, _hδ, _hwit, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    exact ⟨x, Or.inr ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, _hy_eq⟩
    exact
      ⟨adjacentRoundTowardZero x a b,
        Or.inr ⟨e, hlo, hhi,
          Or.inr ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩⟩
theorem exists_sourceRoundTowardNegativeEvidence_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y : ℝ, fmt.sourceRoundTowardNegativeEvidence x y := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_sourceRoundTowardNegativeEvidence_negative hneg
  · exact False.elim (fmt.finiteNormalRange_ne_zero hx hzero)
  · exact fmt.exists_sourceRoundTowardNegativeEvidence_positive hpos
theorem exists_sourceRoundTowardPositiveEvidence_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y : ℝ, fmt.sourceRoundTowardPositiveEvidence x y := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_sourceRoundTowardPositiveEvidence_negative hneg
  · exact False.elim (fmt.finiteNormalRange_ne_zero hx hzero)
  · exact fmt.exists_sourceRoundTowardPositiveEvidence_positive hpos
theorem exists_sourceRoundTowardZeroEvidence_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y : ℝ, fmt.sourceRoundTowardZeroEvidence x y := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact fmt.exists_sourceRoundTowardZeroEvidence_negative hneg
  · exact False.elim (fmt.finiteNormalRange_ne_zero hx hzero)
  · exact fmt.exists_sourceRoundTowardZeroEvidence_positive hpos
theorem sourceRoundToEvenEvidence_nearestRoundingToUnbounded
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y) :
    fmt.nearestRoundingToUnbounded x y := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨false, m, e, hm, hx_eq⟩
      rw [hy_eq]
      exact fmt.nearestRoundingToUnbounded_self hx_unbounded
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _ha_nonneg, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
          leftMantissa hadj ⟨ha_le_x, hx_le_b⟩
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_unbounded : fmt.unboundedNormalizedSystem x :=
        ⟨true, m, e, hm, hx_eq⟩
      rw [hy_eq]
      exact fmt.nearestRoundingToUnbounded_self hx_unbounded
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _hb_nonpos, ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
          leftMantissa hadj ⟨ha_le_x, hx_le_b⟩
theorem sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hstrict : a < x ∧ x < b)
    (hleftCloser : |x - a| < |x - b|) :
    y = a := by
  have hnot_exact (hx_mem : fmt.unboundedNormalizedSystem x) : False := by
    exact (hadj.2.2.2 x hx_mem) (Or.inl hstrict)
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨false, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, _m, hcd, _hleft, _hc_nonneg, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_left_of_left_closer hleftCloser
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨true, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, _m, hcd, _hleft, _hd_nonpos, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_left_of_left_closer hleftCloser
theorem sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hstrict : a < x ∧ x < b)
    (hrightCloser : |x - b| < |x - a|) :
    y = b := by
  have hnot_exact (hx_mem : fmt.unboundedNormalizedSystem x) : False := by
    exact (hadj.2.2.2 x hx_mem) (Or.inl hstrict)
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨false, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, _m, hcd, _hleft, _hc_nonneg, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_right_of_right_closer hrightCloser
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨true, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, _m, hcd, _hleft, _hd_nonpos, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_right_of_right_closer hrightCloser
theorem sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
    {fmt : FloatingPointFormat} {x y a b : ℝ} {leftMantissa : ℕ}
    {negative : Bool} {eLeft : ℤ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hstrict : a < x ∧ x < b)
    (hleftMantissa : fmt.normalizedMantissa leftMantissa)
    (hleft : a = fmt.normalizedValue negative leftMantissa eLeft)
    (htie : |x - a| = |x - b|)
    (heven : evenMantissa leftMantissa) :
    y = a := by
  have hnot_exact (hx_mem : fmt.unboundedNormalizedSystem x) : False := by
    exact (hadj.2.2.2 x hx_mem) (Or.inl hstrict)
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨false, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, m, hcd, hleft', _hc_nonneg, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rcases hleft' with ⟨negative', eLeft', hm', hc_repr⟩
      have hm_eq : m = leftMantissa := by
        have hval :
            fmt.normalizedValue negative' m eLeft' =
              fmt.normalizedValue negative leftMantissa eLeft := by
          rw [← hc_repr, ← hleft]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hm' hleftMantissa hval).2.2
      have heven_m : evenMantissa m := by
        simpa [hm_eq] using heven
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_left_of_tie_even htie heven_m
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨true, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, m, hcd, hleft', _hd_nonpos, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rcases hleft' with ⟨negative', eLeft', hm', hc_repr⟩
      have hm_eq : m = leftMantissa := by
        have hval :
            fmt.normalizedValue negative' m eLeft' =
              fmt.normalizedValue negative leftMantissa eLeft := by
          rw [← hc_repr, ← hleft]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hm' hleftMantissa hval).2.2
      have heven_m : evenMantissa m := by
        simpa [hm_eq] using heven
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_left_of_tie_even htie heven_m
theorem sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
    {fmt : FloatingPointFormat} {x y a b : ℝ} {leftMantissa : ℕ}
    {negative : Bool} {eLeft : ℤ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hstrict : a < x ∧ x < b)
    (hleftMantissa : fmt.normalizedMantissa leftMantissa)
    (hleft : a = fmt.normalizedValue negative leftMantissa eLeft)
    (htie : |x - a| = |x - b|)
    (hodd : ¬ evenMantissa leftMantissa) :
    y = b := by
  have hnot_exact (hx_mem : fmt.unboundedNormalizedSystem x) : False := by
    exact (hadj.2.2.2 x hx_mem) (Or.inl hstrict)
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨false, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, m, hcd, hleft', _hc_nonneg, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rcases hleft' with ⟨negative', eLeft', hm', hc_repr⟩
      have hm_eq : m = leftMantissa := by
        have hval :
            fmt.normalizedValue negative' m eLeft' =
              fmt.normalizedValue negative leftMantissa eLeft := by
          rw [← hc_repr, ← hleft]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hm' hleftMantissa hval).2.2
      have hodd_m : ¬ evenMantissa m := by
        simpa [hm_eq] using hodd
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_right_of_tie_odd htie hodd_m
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
      exact False.elim (hnot_exact ⟨true, m, e, hm, hx_eq⟩)
    · rcases hbracket with
        ⟨c, d, m, hcd, hleft', _hd_nonpos, hc_le_x, hx_le_d, hy_eq⟩
      rcases
          fmt.realOrderAdjacentNormalized_bracket_unique_of_strict_between
            hadj hcd hstrict ⟨hc_le_x, hx_le_d⟩ with
        ⟨hc_eq, hd_eq⟩
      subst c
      subst d
      rcases hleft' with ⟨negative', eLeft', hm', hc_repr⟩
      have hm_eq : m = leftMantissa := by
        have hval :
            fmt.normalizedValue negative' m eLeft' =
              fmt.normalizedValue negative leftMantissa eLeft := by
          rw [← hc_repr, ← hleft]
        exact
          (fmt.normalizedValue_eq_sign_exp_mantissa
            hm' hleftMantissa hval).2.2
      have hodd_m : ¬ evenMantissa m := by
        simpa [hm_eq] using hodd
      rw [hy_eq]
      exact nearestAdjacentRoundToEven_eq_right_of_tie_odd htie hodd_m
theorem sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx_mem : fmt.unboundedNormalizedSystem x)
    (hpolicy : fmt.sourceRoundToEvenEvidence x y) :
    y = x := by
  rcases hpolicy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      exact hy_eq
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _ha_nonneg,
          ha_le_x, hx_le_b, hy_eq⟩
      rcases lt_or_eq_of_le ha_le_x with ha_lt_x | hax
      · rcases lt_or_eq_of_le hx_le_b with hx_lt_b | hxb
        · exfalso
          exact hadj.2.2.2 x hx_mem (Or.inl ⟨ha_lt_x, hx_lt_b⟩)
        · rw [hy_eq, hxb]
          exact nearestAdjacentRoundToEven_eq_right_endpoint a b leftMantissa
      · rw [hy_eq, ← hax]
        exact nearestAdjacentRoundToEven_eq_left_endpoint a b leftMantissa
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨_m, _hm, _hx_eq, hy_eq⟩
      exact hy_eq
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, _hleft, _hb_nonpos,
          ha_le_x, hx_le_b, hy_eq⟩
      rcases lt_or_eq_of_le ha_le_x with ha_lt_x | hax
      · rcases lt_or_eq_of_le hx_le_b with hx_lt_b | hxb
        · exfalso
          exact hadj.2.2.2 x hx_mem (Or.inl ⟨ha_lt_x, hx_lt_b⟩)
        · rw [hy_eq, hxb]
          exact nearestAdjacentRoundToEven_eq_right_endpoint a b leftMantissa
      · rw [hy_eq, ← hax]
        exact nearestAdjacentRoundToEven_eq_left_endpoint a b leftMantissa
theorem sourceRoundToEvenEvidence_eq_nearest_of_realOrderAdjacent_between
    {fmt : FloatingPointFormat} {x y a b : ℝ} {leftMantissa : ℕ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hleft :
      ∃ negative eLeft,
        fmt.normalizedMantissa leftMantissa ∧
          a = fmt.normalizedValue negative leftMantissa eLeft)
    (hbetween : a ≤ x ∧ x ≤ b) :
    y = nearestAdjacentRoundToEven x a b leftMantissa := by
  rcases lt_or_eq_of_le hbetween.1 with ha_lt_x | hax
  · rcases lt_or_eq_of_le hbetween.2 with hx_lt_b | hxb
    · by_cases hleftCloser : |x - a| < |x - b|
      · rw [
          sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
            hpolicy hadj ⟨ha_lt_x, hx_lt_b⟩ hleftCloser,
          nearestAdjacentRoundToEven_eq_left_of_left_closer hleftCloser]
      · by_cases hrightCloser : |x - b| < |x - a|
        · rw [
            sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
              hpolicy hadj ⟨ha_lt_x, hx_lt_b⟩ hrightCloser,
            nearestAdjacentRoundToEven_eq_right_of_right_closer hrightCloser]
        · have htie : |x - a| = |x - b| := by
            exact le_antisymm (le_of_not_gt hrightCloser)
              (le_of_not_gt hleftCloser)
          rcases hleft with ⟨negative, eLeft, hm, ha_repr⟩
          by_cases heven : evenMantissa leftMantissa
          · rw [
              sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
                hpolicy hadj ⟨ha_lt_x, hx_lt_b⟩ hm ha_repr htie heven,
              nearestAdjacentRoundToEven_eq_left_of_tie_even htie heven]
          · rw [
              sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
                hpolicy hadj ⟨ha_lt_x, hx_lt_b⟩ hm ha_repr htie heven,
              nearestAdjacentRoundToEven_eq_right_of_tie_odd htie heven]
    · have hx_mem : fmt.unboundedNormalizedSystem x := by
        simpa [hxb] using hadj.2.1
      rw [
        sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem hx_mem hpolicy,
        hxb,
        nearestAdjacentRoundToEven_eq_right_endpoint]
  · have hx_mem : fmt.unboundedNormalizedSystem x := by
      simpa [← hax] using hadj.1
    rw [
      sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem hx_mem hpolicy,
      ← hax,
      nearestAdjacentRoundToEven_eq_left_endpoint]
/-- Source round-to-even evidence can only select one of the two endpoints of
an ordered adjacent bracket that contains the source value. -/
theorem sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b) :
    y = a ∨ y = b :=
  fmt.nearestRoundingToUnbounded_eq_left_or_right_of_realOrderAdjacent_ordered_between
    (fmt.sourceRoundToEvenEvidence_nearestRoundingToUnbounded hpolicy)
    hadj hbetween
/-- Same-exponent endpoint-index form of source round-to-even selection.

If the adjacent bracket endpoints are `q` and `q+1` on the same normalized
lattice, any normalized output with the same sign and exponent has mantissa
`q` or `q+1`.  This is the source-policy bridge needed by the binary
guard-word branch of the C4.4 addition roundoff-error proof. -/
theorem sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket
    {fmt : FloatingPointFormat} {x y a b : ℝ}
    {negative : Bool} {l q : ℕ} {e : ℤ}
    (hpolicy : fmt.sourceRoundToEvenEvidence x y)
    (hadj : fmt.realOrderAdjacentNormalized a b)
    (hbetween : a ≤ x ∧ x ≤ b)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue negative l e)
    (ha : a = fmt.normalizedValue negative q e)
    (hb : b = fmt.normalizedValue negative (q + 1) e) :
    l = q ∨ l = q + 1 := by
  rcases
      fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
        hpolicy hadj hbetween with hleft | hright
  · have hval :
        fmt.normalizedValue negative l e =
          fmt.normalizedValue negative q e := by
      rw [← hy, hleft, ha]
    exact Or.inl (fmt.normalizedValue_eq_sign_exp_mantissa hl hq hval).2.2
  · have hval :
        fmt.normalizedValue negative l e =
          fmt.normalizedValue negative (q + 1) e := by
      rw [← hy, hright, hb]
    exact Or.inr (fmt.normalizedValue_eq_sign_exp_mantissa hl hqs hval).2.2
/-- Positive aligned binary guard-word source evidence selects the lower
quotient endpoint or, only in the non-exact case, the upper successor endpoint.

This composes the concrete quotient bracket for `k = beta*q+r`, source
round-to-even endpoint selection, and normalized-value uniqueness.  It is the
local bridge needed before applying
`binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil`. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_mantissa_eq_or_succ_of_bracket
    {fmt : FloatingPointFormat} {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue false l (e + 1)) :
    l = q ∨ (l = q + 1 ∧ r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_left :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue false q (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨false, q, e + 1, hq, hsource_eq_left⟩
    have hy_self :
        y = (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    have hval :
        fmt.normalizedValue false l (e + 1) =
          fmt.normalizedValue false q (e + 1) := by
      rw [← hy, hy_self, hsource_eq_left]
    exact Or.inl (fmt.normalizedValue_eq_sign_exp_mantissa hl hq hval).2.2
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue false q (e + 1))
          (fmt.normalizedValue false (q + 1) (e + 1)) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨false, q, e + 1, hq, hqs, Or.inl ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.binaryGuardSource_between_sameExponentEndpoints_positive
        (k := k) (q := q) (r := r) (e := e) hk hr
    have hsel :
        l = q ∨ l = q + 1 :=
      fmt.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket
        (a := fmt.normalizedValue false q (e + 1))
        (b := fmt.normalizedValue false (q + 1) (e + 1))
        hpolicy hadj hbetween hl hq hqs hy rfl rfl
    rcases hsel with hlq | hlqs
    · exact Or.inl hlq
    · exact Or.inr ⟨hlqs, hrzero⟩
/-- Positive aligned binary guard-word source evidence gives the `t`-digit
coefficient gap required for finite representability of the local add error. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue false l (e + 1)) :
    (((k : ℤ) - ((fmt.beta * l : ℕ) : ℤ)).natAbs <
      fmt.beta ^ fmt.t) := by
  have hsel :=
    fmt.sourceRoundToEvenEvidence_positive_binaryGuard_mantissa_eq_or_succ_of_bracket
      (k := k) (q := q) (r := r) (l := l) (e := e)
      hk hr hpolicy hl hq hqs hy
  exact
    fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
      hbeta hk hr hsel
/-- Negative aligned binary guard-word source evidence selects the quotient
endpoint or, only in the non-exact case, the successor endpoint.

The real-order bracket is reversed for negative values, so this proof reads the
left/right endpoint cases directly instead of using the positive-oriented
same-exponent helper. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_mantissa_eq_or_succ_of_bracket
    {fmt : FloatingPointFormat} {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue true l (e + 1)) :
    l = q ∨ (l = q + 1 ∧ r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_right :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue true q (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          (fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨true, q, e + 1, hq, hsource_eq_right⟩
    have hy_self :
        y = fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    have hval :
        fmt.normalizedValue true l (e + 1) =
          fmt.normalizedValue true q (e + 1) := by
      rw [← hy, hy_self, hsource_eq_right]
    exact Or.inl (fmt.normalizedValue_eq_sign_exp_mantissa hl hq hval).2.2
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue true (q + 1) (e + 1))
          (fmt.normalizedValue true q (e + 1)) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨true, q, e + 1, hq, hqs, Or.inr ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.binaryGuardSource_between_sameExponentEndpoints_negative
        (k := k) (q := q) (r := r) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hleft | hright
    · have hval :
          fmt.normalizedValue true l (e + 1) =
            fmt.normalizedValue true (q + 1) (e + 1) := by
        rw [← hy, hleft]
      exact Or.inr
        ⟨(fmt.normalizedValue_eq_sign_exp_mantissa hl hqs hval).2.2,
          hrzero⟩
    · have hval :
          fmt.normalizedValue true l (e + 1) =
            fmt.normalizedValue true q (e + 1) := by
        rw [← hy, hright]
      exact Or.inl (fmt.normalizedValue_eq_sign_exp_mantissa hl hq hval).2.2
/-- Negative aligned binary guard-word source evidence gives the same
`t`-digit coefficient gap as the positive branch. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue true l (e + 1)) :
    (((k : ℤ) - ((fmt.beta * l : ℕ) : ℤ)).natAbs <
      fmt.beta ^ fmt.t) := by
  have hsel :=
    fmt.sourceRoundToEvenEvidence_negative_binaryGuard_mantissa_eq_or_succ_of_bracket
      (k := k) (q := q) (r := r) (l := l) (e := e)
      hk hr hpolicy hl hq hqs hy
  exact
    fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
      hbeta hk hr hsel
/-- Positive multi-guard source evidence selects the lower quotient endpoint
or, only in the non-exact case, the upper successor endpoint.

This is the source-policy bridge for the complementary ordered-exponent C4.4
branch after the coefficient is decomposed as `k = beta^d*q+r`. -/
theorem sourceRoundToEvenEvidence_positive_multiGuard_mantissa_eq_or_succ_of_bracket
    {fmt : FloatingPointFormat} {y : ℝ} {k q r l d : ℕ} {e : ℤ}
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue false l (e + (d : ℤ))) :
    l = q ∨ (l = q + 1 ∧ r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta ^ d * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_left :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue false q (e + (d : ℤ)) := by
      rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta ^ d * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul, Nat.cast_pow]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨false, q, e + (d : ℤ), hq, hsource_eq_left⟩
    have hy_self :
        y = (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    have hval :
        fmt.normalizedValue false l (e + (d : ℤ)) =
          fmt.normalizedValue false q (e + (d : ℤ)) := by
      rw [← hy, hy_self, hsource_eq_left]
    exact Or.inl (fmt.normalizedValue_eq_sign_exp_mantissa hl hq hval).2.2
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue false q (e + (d : ℤ)))
          (fmt.normalizedValue false (q + 1) (e + (d : ℤ))) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨false, q, e + (d : ℤ), hq, hqs, Or.inl ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.multiGuardSource_between_sameExponentEndpoints_positive
        (k := k) (q := q) (r := r) (d := d) (e := e) hk hr
    have hsel :
        l = q ∨ l = q + 1 :=
      fmt.sourceRoundToEvenEvidence_sameExponent_mantissa_eq_or_succ_of_bracket
        (a := fmt.normalizedValue false q (e + (d : ℤ)))
        (b := fmt.normalizedValue false (q + 1) (e + (d : ℤ)))
        hpolicy hadj hbetween hl hq hqs hy rfl rfl
    rcases hsel with hlq | hlqs
    · exact Or.inl hlq
    · exact Or.inr ⟨hlqs, hrzero⟩
/-- Positive multi-guard source evidence gives the `t`-digit coefficient gap
required for finite representability of the local add error. -/
theorem sourceRoundToEvenEvidence_positive_multiGuard_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {y : ℝ} {k q r l d : ℕ} {e : ℤ}
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue false l (e + (d : ℤ))) :
    (((k : ℤ) - (((fmt.beta ^ d) * l : ℕ) : ℤ)).natAbs <
      fmt.beta ^ fmt.t) := by
  have hsel :=
    fmt.sourceRoundToEvenEvidence_positive_multiGuard_mantissa_eq_or_succ_of_bracket
      (k := k) (q := q) (r := r) (l := l) (d := d) (e := e)
      hk hr hpolicy hl hq hqs hy
  exact
    fmt.multiGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
      hdle hk hr hsel
/-- Negative multi-guard source evidence selects the quotient endpoint or, only
in the non-exact case, the successor endpoint.

The real-order bracket is reversed for negative values, so the endpoint cases
are read directly from the ordered adjacent bracket. -/
theorem sourceRoundToEvenEvidence_negative_multiGuard_mantissa_eq_or_succ_of_bracket
    {fmt : FloatingPointFormat} {y : ℝ} {k q r l d : ℕ} {e : ℤ}
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue true l (e + (d : ℤ))) :
    l = q ∨ (l = q + 1 ∧ r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta ^ d * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_right :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue true q (e + (d : ℤ)) := by
      rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta ^ d * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul, Nat.cast_pow]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          (fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨true, q, e + (d : ℤ), hq, hsource_eq_right⟩
    have hy_self :
        y = fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    have hval :
        fmt.normalizedValue true l (e + (d : ℤ)) =
          fmt.normalizedValue true q (e + (d : ℤ)) := by
      rw [← hy, hy_self, hsource_eq_right]
    exact Or.inl (fmt.normalizedValue_eq_sign_exp_mantissa hl hq hval).2.2
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue true (q + 1) (e + (d : ℤ)))
          (fmt.normalizedValue true q (e + (d : ℤ))) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨true, q, e + (d : ℤ), hq, hqs, Or.inr ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.multiGuardSource_between_sameExponentEndpoints_negative
        (k := k) (q := q) (r := r) (d := d) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hleft | hright
    · have hval :
          fmt.normalizedValue true l (e + (d : ℤ)) =
            fmt.normalizedValue true (q + 1) (e + (d : ℤ)) := by
        rw [← hy, hleft]
      exact Or.inr
        ⟨(fmt.normalizedValue_eq_sign_exp_mantissa hl hqs hval).2.2,
          hrzero⟩
    · have hval :
          fmt.normalizedValue true l (e + (d : ℤ)) =
            fmt.normalizedValue true q (e + (d : ℤ)) := by
        rw [← hy, hright]
      exact Or.inl (fmt.normalizedValue_eq_sign_exp_mantissa hl hq hval).2.2
/-- Negative multi-guard source evidence gives the same `t`-digit coefficient
gap as the positive branch. -/
theorem sourceRoundToEvenEvidence_negative_multiGuard_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {y : ℝ} {k q r l d : ℕ} {e : ℤ}
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue true l (e + (d : ℤ))) :
    (((k : ℤ) - (((fmt.beta ^ d) * l : ℕ) : ℤ)).natAbs <
      fmt.beta ^ fmt.t) := by
  have hsel :=
    fmt.sourceRoundToEvenEvidence_negative_multiGuard_mantissa_eq_or_succ_of_bracket
      (k := k) (q := q) (r := r) (l := l) (d := d) (e := e)
      hk hr hpolicy hl hq hqs hy
  exact
    fmt.multiGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
      hdle hk hr hsel
/-- Positive multi-guard source evidence gives finite representability of the
local roundoff error once the rounded endpoint is represented on the same
shifted-exponent lattice. -/
theorem sourceRoundToEvenEvidence_positive_multiGuard_error_finiteSystem
    {fmt : FloatingPointFormat} {y : ℝ} {k q r l d : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue false l (e + (d : ℤ))) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  have hdiff :=
    fmt.sourceRoundToEvenEvidence_positive_multiGuard_coeffDiff_natAbs_lt_mantissaBound
      hdle hk hr hpolicy hl hq hqs hy
  rw [hy, fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
  simpa [signValue] using
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false) (k := (k : ℤ))
      (l := (((fmt.beta ^ d) * l : ℕ) : ℤ)) (e := e) he hdiff)
/-- Negative multi-guard source evidence gives finite representability of the
local roundoff error once the rounded endpoint is represented on the same
shifted-exponent lattice. -/
theorem sourceRoundToEvenEvidence_negative_multiGuard_error_finiteSystem
    {fmt : FloatingPointFormat} {y : ℝ} {k q r l d : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue true l (e + (d : ℤ))) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  have hdiff :=
    fmt.sourceRoundToEvenEvidence_negative_multiGuard_coeffDiff_natAbs_lt_mantissaBound
      hdle hk hr hpolicy hl hq hqs hy
  rw [hy, fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
  exact
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := true) (k := (k : ℤ))
      (l := (((fmt.beta ^ d) * l : ℕ) : ℤ)) (e := e) he hdiff)
/-- Positive multi-guard source evidence gives finite representability of the
local roundoff error directly from normalized quotient endpoint data, without
separately supplying the rounded endpoint's mantissa. -/
theorem sourceRoundToEvenEvidence_positive_multiGuard_error_finiteSystem_of_normalizedQuotient
    {fmt : FloatingPointFormat} {y : ℝ} {k q r d : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1)) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta ^ d * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_left :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue false q (e + (d : ℤ)) := by
      rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta ^ d * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul, Nat.cast_pow]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨false, q, e + (d : ℤ), hq, hsource_eq_left⟩
    have hy_self :
        y = (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    rw [hy_self]
    have hzero :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) -
            (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) = 0 := by
      ring
    rw [hzero]
    exact Or.inl rfl
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue false q (e + (d : ℤ)))
          (fmt.normalizedValue false (q + 1) (e + (d : ℤ))) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨false, q, e + (d : ℤ), hq, hqs, Or.inl ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.multiGuardSource_between_sameExponentEndpoints_positive
        (k := k) (q := q) (r := r) (d := d) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hy | hy
    · have hdiff :=
        fmt.multiGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hdle hk hr (l := q) (Or.inl rfl)
      rw [hy, fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := false) (k := (k : ℤ))
          (l := (((fmt.beta ^ d) * q : ℕ) : ℤ)) (e := e) he hdiff)
    · have hdiff :=
        fmt.multiGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hdle hk hr (l := q + 1) (Or.inr ⟨rfl, hrzero⟩)
      rw [hy, fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := false) (k := (k : ℤ))
          (l := (((fmt.beta ^ d) * (q + 1) : ℕ) : ℤ)) (e := e) he hdiff)
/-- Negative multi-guard source evidence gives finite representability of the
local roundoff error directly from normalized quotient endpoint data, without
separately supplying the rounded endpoint's mantissa. -/
theorem sourceRoundToEvenEvidence_negative_multiGuard_error_finiteSystem_of_normalizedQuotient
    {fmt : FloatingPointFormat} {y : ℝ} {k q r d : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1)) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta ^ d * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_right :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue true q (e + (d : ℤ)) := by
      rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta ^ d * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul, Nat.cast_pow]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          (fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨true, q, e + (d : ℤ), hq, hsource_eq_right⟩
    have hy_self :
        y = fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    rw [hy_self]
    have hzero :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) -
          fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) = 0 := by
      ring
    rw [hzero]
    exact Or.inl rfl
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue true (q + 1) (e + (d : ℤ)))
          (fmt.normalizedValue true q (e + (d : ℤ))) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨true, q, e + (d : ℤ), hq, hqs, Or.inr ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.multiGuardSource_between_sameExponentEndpoints_negative
        (k := k) (q := q) (r := r) (d := d) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hy | hy
    · have hdiff :=
        fmt.multiGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hdle hk hr (l := q + 1) (Or.inr ⟨rfl, hrzero⟩)
      rw [hy, fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := true) (k := (k : ℤ))
          (l := (((fmt.beta ^ d) * (q + 1) : ℕ) : ℤ)) (e := e) he hdiff)
    · have hdiff :=
        fmt.multiGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hdle hk hr (l := q) (Or.inl rfl)
      rw [hy, fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := true) (k := (k : ℤ))
          (l := (((fmt.beta ^ d) * q : ℕ) : ℤ)) (e := e) he hdiff)
/-- Positive aligned binary guard-word source evidence gives finite
representability of the local roundoff error once the rounded endpoint is
represented on the same next-exponent lattice. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue false l (e + 1)) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  have hdiff :=
    fmt.sourceRoundToEvenEvidence_positive_binaryGuard_coeffDiff_natAbs_lt_mantissaBound
      hbeta hk hr hpolicy hl hq hqs hy
  rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
  simpa [signValue] using
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false) (k := (k : ℤ))
      (l := ((fmt.beta * l : ℕ) : ℤ)) (e := e) he hdiff)
/-- Negative aligned binary guard-word source evidence gives finite
representability of the local roundoff error once the rounded endpoint is
represented on the same next-exponent lattice. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r l : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hl : fmt.normalizedMantissa l)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hy : y = fmt.normalizedValue true l (e + 1)) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  have hdiff :=
    fmt.sourceRoundToEvenEvidence_negative_binaryGuard_coeffDiff_natAbs_lt_mantissaBound
      hbeta hk hr hpolicy hl hq hqs hy
  rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
  exact
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := true) (k := (k : ℤ))
      (l := ((fmt.beta * l : ℕ) : ℤ)) (e := e) he hdiff)
/-- Positive aligned binary guard-word source evidence gives finite
representability of the local roundoff error from normalized quotient endpoint
data, without separately supplying the rounded endpoint's mantissa. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_normalizedQuotient
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1)) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_left :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue false q (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨false, q, e + 1, hq, hsource_eq_left⟩
    have hy_self :
        y = (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    rw [hy_self]
    have hzero :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) -
            (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) = 0 := by ring
    rw [hzero]
    exact Or.inl rfl
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue false q (e + 1))
          (fmt.normalizedValue false (q + 1) (e + 1)) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨false, q, e + 1, hq, hqs, Or.inl ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.binaryGuardSource_between_sameExponentEndpoints_positive
        (k := k) (q := q) (r := r) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hy | hy
    · have hdiff :=
        fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hbeta hk hr (l := q) (Or.inl rfl)
      rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := false) (k := (k : ℤ))
          (l := ((fmt.beta * q : ℕ) : ℤ)) (e := e) he hdiff)
    · have hdiff :=
        fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hbeta hk hr (l := q + 1) (Or.inr ⟨rfl, hrzero⟩)
      rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := false) (k := (k : ℤ))
          (l := ((fmt.beta * (q + 1) : ℕ) : ℤ)) (e := e) he hdiff)
/-- Negative aligned binary guard-word source evidence gives finite
representability of the local roundoff error from normalized quotient endpoint
data, without separately supplying the rounded endpoint's mantissa. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_normalizedQuotient
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1)) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * q := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_right :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue true q (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast : (k : ℝ) = (((fmt.beta * q : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          (fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨true, q, e + 1, hq, hsource_eq_right⟩
    have hy_self :
        y = fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    rw [hy_self]
    have hzero :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) -
          fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) = 0 := by ring
    rw [hzero]
    exact Or.inl rfl
  · have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue true (q + 1) (e + 1))
          (fmt.normalizedValue true q (e + 1)) :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
        ⟨true, q, e + 1, hq, hqs, Or.inr ⟨rfl, rfl⟩⟩
    have hbetween :=
      fmt.binaryGuardSource_between_sameExponentEndpoints_negative
        (k := k) (q := q) (r := r) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hy | hy
    · have hdiff :=
        fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hbeta hk hr (l := q + 1) (Or.inr ⟨rfl, hrzero⟩)
      rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := true) (k := (k : ℤ))
          (l := ((fmt.beta * (q + 1) : ℕ) : ℤ)) (e := e) he hdiff)
    · have hdiff :=
        fmt.binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
          hbeta hk hr (l := q) (Or.inl rfl)
      rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simpa [signValue] using
        (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
          (negative := true) (k := (k : ℤ))
          (l := ((fmt.beta * q : ℕ) : ℤ)) (e := e) he hdiff)
/-- Positive boundary binary guard-word source evidence selects the ceiling-binade
lower endpoint or, only in the non-exact case, the next-binade minimum endpoint.
-/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_boundary_eq_max_or_min
    {fmt : FloatingPointFormat} {y : ℝ} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    y = fmt.normalizedValue false fmt.maxNormalMantissa (e + 1) ∨
      (y = fmt.normalizedValue false fmt.minNormalMantissa (e + 2) ∧
        r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * fmt.maxNormalMantissa := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_left :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue false fmt.maxNormalMantissa (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast :
          (k : ℝ) = (((fmt.beta * fmt.maxNormalMantissa : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨false, fmt.maxNormalMantissa, e + 1,
        fmt.maxNormalMantissa_normalized, hsource_eq_left⟩
    have hy_self :
        y = (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    exact Or.inl (by rw [hy_self, hsource_eq_left])
  · have hboundary :
        fmt.boundaryAdjacentNormalized
          (fmt.normalizedValue false fmt.maxNormalMantissa (e + 1))
          (fmt.normalizedValue false fmt.minNormalMantissa (e + 2)) := by
      refine ⟨false, e + 1, Or.inl ?_⟩
      constructor
      · rfl
      · rw [show e + 1 + 1 = e + 2 by ring]
    have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue false fmt.maxNormalMantissa (e + 1))
          (fmt.normalizedValue false fmt.minNormalMantissa (e + 2)) :=
      fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
    have hbetween :=
      fmt.binaryGuardSource_between_boundaryEndpoints_positive
        (k := k) (r := r) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hleft | hright
    · exact Or.inl hleft
    · exact Or.inr ⟨hright, hrzero⟩
/-- Negative boundary binary guard-word source evidence selects the ceiling-binade
lower endpoint or, only in the non-exact case, the next-binade minimum endpoint.
The real-order bracket is reversed, but the returned coefficient cases match the
positive statement. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_boundary_eq_max_or_min
    {fmt : FloatingPointFormat} {y : ℝ} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    y = fmt.normalizedValue true fmt.maxNormalMantissa (e + 1) ∨
      (y = fmt.normalizedValue true fmt.minNormalMantissa (e + 2) ∧
        r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta * fmt.maxNormalMantissa := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_right :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue true fmt.maxNormalMantissa (e + 1) := by
      rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
      simp [signValue]
      have hk_cast :
          (k : ℝ) = (((fmt.beta * fmt.maxNormalMantissa : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          (fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨true, fmt.maxNormalMantissa, e + 1,
        fmt.maxNormalMantissa_normalized, hsource_eq_right⟩
    have hy_self :
        y = fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    exact Or.inl (by rw [hy_self, hsource_eq_right])
  · have hboundary :
        fmt.boundaryAdjacentNormalized
          (fmt.normalizedValue true fmt.minNormalMantissa (e + 2))
          (fmt.normalizedValue true fmt.maxNormalMantissa (e + 1)) := by
      refine ⟨true, e + 1, Or.inr ?_⟩
      constructor
      · rw [show e + 1 + 1 = e + 2 by ring]
      · rfl
    have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue true fmt.minNormalMantissa (e + 2))
          (fmt.normalizedValue true fmt.maxNormalMantissa (e + 1)) :=
      fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
    have hbetween :=
      fmt.binaryGuardSource_between_boundaryEndpoints_negative
        (k := k) (r := r) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hleft | hright
    · exact Or.inr ⟨hleft, hrzero⟩
    · exact Or.inl hright
/-- Positive boundary binary guard-word source evidence gives a rounded endpoint
coefficient on the original exponent lattice whose gap has fewer than `t`
digits. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    ∃ c : ℕ,
      y = fmt.signValue false * (c : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
        (((k : ℤ) - (c : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
  rcases
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_eq_max_or_min
        (k := k) (r := r) (e := e) hk hr hpolicy with hy | hy
  · refine ⟨fmt.beta * fmt.maxNormalMantissa, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    · exact
        fmt.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hbeta hk hr (Or.inl rfl)
  · rcases hy with ⟨hy, hrne⟩
    refine ⟨fmt.minNormalMantissa * fmt.beta ^ 2, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger]
    · exact
        fmt.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hbeta hk hr (Or.inr ⟨rfl, hrne⟩)
/-- Negative boundary binary guard-word source evidence gives a rounded endpoint
coefficient on the original exponent lattice whose gap has fewer than `t`
digits. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    ∃ c : ℕ,
      y = fmt.signValue true * (c : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
        (((k : ℤ) - (c : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
  rcases
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_eq_max_or_min
        (k := k) (r := r) (e := e) hk hr hpolicy with hy | hy
  · refine ⟨fmt.beta * fmt.maxNormalMantissa, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    · exact
        fmt.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hbeta hk hr (Or.inl rfl)
  · rcases hy with ⟨hy, hrne⟩
    refine ⟨fmt.minNormalMantissa * fmt.beta ^ 2, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger]
    · exact
        fmt.binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hbeta hk hr (Or.inr ⟨rfl, hrne⟩)
/-- Positive boundary binary guard-word source evidence gives finite
representability of the local roundoff error. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
        hbeta hk hr hpolicy with ⟨c, hy, hdiff⟩
  rw [hy]
  simpa [signValue] using
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false) (k := (k : ℤ)) (l := (c : ℤ)) (e := e)
      he hdiff)
/-- Negative boundary binary guard-word source evidence gives finite
representability of the local roundoff error. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
        hbeta hk hr hpolicy with ⟨c, hy, hdiff⟩
  rw [hy]
  exact
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := true) (k := (k : ℤ)) (l := (c : ℤ)) (e := e)
      he hdiff)
/-- Positive boundary multi-guard source evidence selects the shifted
ceiling-binade lower endpoint or, only in the non-exact case, the next-binade
minimum endpoint. -/
theorem sourceRoundToEvenEvidence_positive_multiGuard_boundary_eq_max_or_min
    {fmt : FloatingPointFormat} {y : ℝ} {k r d : ℕ} {e : ℤ}
    (hk : k = fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    y = fmt.normalizedValue false fmt.maxNormalMantissa (e + (d : ℤ)) ∨
      (y = fmt.normalizedValue false fmt.minNormalMantissa
          (e + ((d + 1 : ℕ) : ℤ)) ∧ r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta ^ d * fmt.maxNormalMantissa := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_left :
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue false fmt.maxNormalMantissa
            (e + (d : ℤ)) := by
      rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
      simp [signValue]
      have hk_cast :
          (k : ℝ) =
            (((fmt.beta ^ d * fmt.maxNormalMantissa : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul, Nat.cast_pow]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨false, fmt.maxNormalMantissa, e + (d : ℤ),
        fmt.maxNormalMantissa_normalized, hsource_eq_left⟩
    have hy_self :
        y = (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    exact Or.inl (by rw [hy_self, hsource_eq_left])
  · have hsucc :
        e + (d : ℤ) + 1 = e + ((d + 1 : ℕ) : ℤ) := by
      omega
    have hboundary :
        fmt.boundaryAdjacentNormalized
          (fmt.normalizedValue false fmt.maxNormalMantissa (e + (d : ℤ)))
          (fmt.normalizedValue false fmt.minNormalMantissa
            (e + ((d + 1 : ℕ) : ℤ))) := by
      refine ⟨false, e + (d : ℤ), Or.inl ?_⟩
      constructor
      · rfl
      · rw [hsucc]
    have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue false fmt.maxNormalMantissa (e + (d : ℤ)))
          (fmt.normalizedValue false fmt.minNormalMantissa
            (e + ((d + 1 : ℕ) : ℤ))) :=
      fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
    have hbetween :=
      fmt.multiGuardSource_between_boundaryEndpoints_positive
        (k := k) (r := r) (d := d) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hleft | hright
    · exact Or.inl hleft
    · exact Or.inr ⟨hright, hrzero⟩
/-- Negative boundary multi-guard source evidence selects the shifted
ceiling-binade lower endpoint or, only in the non-exact case, the next-binade
minimum endpoint.  The real-order bracket is reversed, but the returned
coefficient cases match the positive statement. -/
theorem sourceRoundToEvenEvidence_negative_multiGuard_boundary_eq_max_or_min
    {fmt : FloatingPointFormat} {y : ℝ} {k r d : ℕ} {e : ℤ}
    (hk : k = fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    y = fmt.normalizedValue true fmt.maxNormalMantissa (e + (d : ℤ)) ∨
      (y = fmt.normalizedValue true fmt.minNormalMantissa
          (e + ((d + 1 : ℕ) : ℤ)) ∧ r ≠ 0) := by
  by_cases hrzero : r = 0
  · have hk_exact : k = fmt.beta ^ d * fmt.maxNormalMantissa := by
      rw [hk, hrzero, Nat.add_zero]
    have hsource_eq_right :
        fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) =
          fmt.normalizedValue true fmt.maxNormalMantissa
            (e + (d : ℤ)) := by
      rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
      simp [signValue]
      have hk_cast :
          (k : ℝ) =
            (((fmt.beta ^ d * fmt.maxNormalMantissa : ℕ) : ℝ)) := by
        exact_mod_cast hk_exact
      rw [hk_cast]
      simp [Nat.cast_mul, Nat.cast_pow]
    have hx_mem :
        fmt.unboundedNormalizedSystem
          (fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ))) := by
      exact ⟨true, fmt.maxNormalMantissa, e + (d : ℤ),
        fmt.maxNormalMantissa_normalized, hsource_eq_right⟩
    have hy_self :
        y = fmt.signValue true * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) :=
      fmt.sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
        hx_mem hpolicy
    exact Or.inl (by rw [hy_self, hsource_eq_right])
  · have hsucc :
        e + (d : ℤ) + 1 = e + ((d + 1 : ℕ) : ℤ) := by
      omega
    have hboundary :
        fmt.boundaryAdjacentNormalized
          (fmt.normalizedValue true fmt.minNormalMantissa
            (e + ((d + 1 : ℕ) : ℤ)))
          (fmt.normalizedValue true fmt.maxNormalMantissa (e + (d : ℤ))) := by
      refine ⟨true, e + (d : ℤ), Or.inr ?_⟩
      constructor
      · rw [hsucc]
      · rfl
    have hadj :
        fmt.realOrderAdjacentNormalized
          (fmt.normalizedValue true fmt.minNormalMantissa
            (e + ((d + 1 : ℕ) : ℤ)))
          (fmt.normalizedValue true fmt.maxNormalMantissa (e + (d : ℤ))) :=
      fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
    have hbetween :=
      fmt.multiGuardSource_between_boundaryEndpoints_negative
        (k := k) (r := r) (d := d) (e := e) hk hr
    rcases
        fmt.sourceRoundToEvenEvidence_eq_left_or_right_of_realOrderAdjacent_ordered_between
          hpolicy hadj hbetween with hleft | hright
    · exact Or.inr ⟨hleft, hrzero⟩
    · exact Or.inl hright
/-- Positive boundary multi-guard source evidence gives a rounded endpoint
coefficient on the original exponent lattice whose gap has fewer than `t`
digits. -/
theorem sourceRoundToEvenEvidence_positive_multiGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {y : ℝ} {k r d : ℕ} {e : ℤ}
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    ∃ c : ℕ,
      y = fmt.signValue false * (c : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
        (((k : ℤ) - (c : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
  rcases
      fmt.sourceRoundToEvenEvidence_positive_multiGuard_boundary_eq_max_or_min
        (k := k) (r := r) (d := d) (e := e) hk hr hpolicy with hy | hy
  · refine ⟨fmt.beta ^ d * fmt.maxNormalMantissa, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    · exact
        fmt.multiGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hdle hk hr (Or.inl rfl)
  · rcases hy with ⟨hy, hrne⟩
    refine ⟨fmt.beta ^ (d + 1) * fmt.minNormalMantissa, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    · exact
        fmt.multiGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hdle hk hr (Or.inr ⟨rfl, hrne⟩)
/-- Negative boundary multi-guard source evidence gives a rounded endpoint
coefficient on the original exponent lattice whose gap has fewer than `t`
digits. -/
theorem sourceRoundToEvenEvidence_negative_multiGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {y : ℝ} {k r d : ℕ} {e : ℤ}
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    ∃ c : ℕ,
      y = fmt.signValue true * (c : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
        (((k : ℤ) - (c : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
  rcases
      fmt.sourceRoundToEvenEvidence_negative_multiGuard_boundary_eq_max_or_min
        (k := k) (r := r) (d := d) (e := e) hk hr hpolicy with hy | hy
  · refine ⟨fmt.beta ^ d * fmt.maxNormalMantissa, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    · exact
        fmt.multiGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hdle hk hr (Or.inl rfl)
  · rcases hy with ⟨hy, hrne⟩
    refine ⟨fmt.beta ^ (d + 1) * fmt.minNormalMantissa, ?_, ?_⟩
    · rw [hy, fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    · exact
        fmt.multiGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
          hdle hk hr (Or.inr ⟨rfl, hrne⟩)
/-- Positive boundary multi-guard source evidence gives finite representability
of the local roundoff error. -/
theorem sourceRoundToEvenEvidence_positive_multiGuard_boundary_error_finiteSystem
    {fmt : FloatingPointFormat} {y : ℝ} {k r d : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.sourceRoundToEvenEvidence_positive_multiGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
        hdle hk hr hpolicy with ⟨c, hy, hdiff⟩
  rw [hy]
  simpa [signValue] using
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := false) (k := (k : ℤ)) (l := (c : ℤ)) (e := e)
      he hdiff)
/-- Negative boundary multi-guard source evidence gives finite representability
of the local roundoff error. -/
theorem sourceRoundToEvenEvidence_negative_multiGuard_boundary_error_finiteSystem
    {fmt : FloatingPointFormat} {y : ℝ} {k r d : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.sourceRoundToEvenEvidence_negative_multiGuard_boundary_coeffDiff_natAbs_lt_mantissaBound
        hdle hk hr hpolicy with ⟨c, hy, hdiff⟩
  rw [hy]
  exact
    (fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := true) (k := (k : ℤ)) (l := (c : ℤ)) (e := e)
      he hdiff)
/-- Positive multi-guard source evidence gives finite representability of the
local roundoff error from a supplied scaled mantissa range.

The range dispatcher chooses either ordinary normalized quotient endpoints or
the shifted exponent-boundary/carry branch. -/
theorem sourceRoundToEvenEvidence_positive_multiGuard_error_finiteSystem_of_scaledMantissaRange
    {fmt : FloatingPointFormat} {y : ℝ} {k q r d : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hlo : fmt.beta ^ d * fmt.minNormalMantissa ≤ k)
    (hhi : k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.multiGuardQuotient_normalized_or_max_of_scaledMantissaRange
        hk hr hlo hhi with hnorm | hmax
  · exact
      fmt.sourceRoundToEvenEvidence_positive_multiGuard_error_finiteSystem_of_normalizedQuotient
        he hdle hk hr hpolicy hnorm.1 hnorm.2
  · have hkmax :
        k = fmt.beta ^ d * fmt.maxNormalMantissa + r := by
      simpa [hmax] using hk
    exact
      fmt.sourceRoundToEvenEvidence_positive_multiGuard_boundary_error_finiteSystem
        he hdle hkmax hr hpolicy
/-- Negative multi-guard source evidence gives finite representability of the
local roundoff error from a supplied scaled mantissa range.

The range dispatcher chooses either ordinary normalized quotient endpoints or
the shifted exponent-boundary/carry branch. -/
theorem sourceRoundToEvenEvidence_negative_multiGuard_error_finiteSystem_of_scaledMantissaRange
    {fmt : FloatingPointFormat} {y : ℝ} {k q r d : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hlo : fmt.beta ^ d * fmt.minNormalMantissa ≤ k)
    (hhi : k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.multiGuardQuotient_normalized_or_max_of_scaledMantissaRange
        hk hr hlo hhi with hnorm | hmax
  · exact
      fmt.sourceRoundToEvenEvidence_negative_multiGuard_error_finiteSystem_of_normalizedQuotient
        he hdle hk hr hpolicy hnorm.1 hnorm.2
  · have hkmax :
        k = fmt.beta ^ d * fmt.maxNormalMantissa + r := by
      simpa [hmax] using hk
    exact
      fmt.sourceRoundToEvenEvidence_negative_multiGuard_boundary_error_finiteSystem
        he hdle hkmax hr hpolicy
/-- Positive aligned binary guard-word source evidence gives finite
representability of the local roundoff error directly from the guard coefficient
range.  The quotient dispatcher chooses between the ordinary `q,q+1` bracket
and the exponent-boundary branch. -/
theorem sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hlo : fmt.beta ^ fmt.t ≤ k)
    (hhi : k < 2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        ((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      (((k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul
        hbeta hk hr hlo hhi with hordinary | hboundary
  · exact
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_normalizedQuotient
        hbeta he hk hr hpolicy hordinary.1 hordinary.2
  · subst q
    exact
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_boundary_error_finiteSystem
        hbeta he hk hr hpolicy
/-- Negative aligned binary guard-word source evidence gives finite
representability of the local roundoff error directly from the guard coefficient
range.  The quotient dispatcher chooses between the ordinary reversed bracket
and the exponent-boundary branch. -/
theorem sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {k q r : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hlo : fmt.beta ^ fmt.t ≤ k)
    (hhi : k < 2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y) :
    fmt.finiteSystem
      ((fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) := by
  rcases
      fmt.binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul
        hbeta hk hr hlo hhi with hordinary | hboundary
  · exact
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_normalizedQuotient
        hbeta he hk hr hpolicy hordinary.1 hordinary.2
  · subst q
    exact
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_boundary_error_finiteSystem
        hbeta he hk hr hpolicy
/-- Positive same-sign, same-exponent normalized addition has finite
representable local roundoff error under binary round-to-even evidence.

This bridges the operand-level C4.4 addition case to the guard-word dispatcher:
the exact sum of two aligned normalized operands has coefficient `m+n`, whose
binary quotient/remainder supplies the one-guard-digit source interval. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false m e + fmt.normalizedValue false n e) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false m e + fmt.normalizedValue false n e) - y) := by
  let k : ℕ := m + n
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo : fmt.beta ^ fmt.t ≤ k := by
    have hsum_min : fmt.minNormalMantissa + fmt.minNormalMantissa ≤ m + n :=
      Nat.add_le_add hm.1 hn.1
    have hB_eq :
        fmt.beta ^ fmt.t = fmt.minNormalMantissa + fmt.minNormalMantissa := by
      rw [← fmt.minNormalMantissa_mul_beta_eq_mantissaBound, hbeta]
      ring
    omega
  have hhi : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k] using
      (normalizedMantissa_add_lt_two_mul_mantissaBound
        (fmt := fmt) hm hn)
  have hsource :
      fmt.normalizedValue false m e + fmt.normalizedValue false n e =
        ((k : ℕ) : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    simpa [k, signValue] using
      (fmt.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger
        false m n e)
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (((k : ℕ) : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((((k : ℕ) : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds
      hbeta he hk hr hlo hhi hpolicy'
  simpa [hsource] using hfin
/-- Negative same-sign, same-exponent normalized addition has finite
representable local roundoff error under binary round-to-even evidence. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true m e + fmt.normalizedValue true n e) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true m e + fmt.normalizedValue true n e) - y) := by
  let k : ℕ := m + n
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo : fmt.beta ^ fmt.t ≤ k := by
    have hsum_min : fmt.minNormalMantissa + fmt.minNormalMantissa ≤ m + n :=
      Nat.add_le_add hm.1 hn.1
    have hB_eq :
        fmt.beta ^ fmt.t = fmt.minNormalMantissa + fmt.minNormalMantissa := by
      rw [← fmt.minNormalMantissa_mul_beta_eq_mantissaBound, hbeta]
      ring
    omega
  have hhi : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k] using
      (normalizedMantissa_add_lt_two_mul_mantissaBound
        (fmt := fmt) hm hn)
  have hsource :
      fmt.normalizedValue true m e + fmt.normalizedValue true n e =
        fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    simpa [k] using
      (fmt.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger
        true m n e)
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds
      hbeta he hk hr hlo hhi hpolicy'
  simpa [hsource] using hfin
/-- Sign-generic same-sign, same-exponent normalized addition has finite
representable local roundoff error under binary round-to-even evidence. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {y : ℝ} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.normalizedMantissa n)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e + fmt.normalizedValue negative n e) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e + fmt.normalizedValue negative n e) -
        y) := by
  cases negative
  · exact
      fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
        hbeta he hm hn hpolicy
  · exact
      fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_sameSign_sameExponent_error_finiteSystem
        hbeta he hm hn hpolicy
/-- Same-sign normalized ordered-exponent addition has finite local error under
binary round-to-even evidence in the one-guard-word branch.  The high-exponent
operand is shifted onto the lower exponent lattice, yielding the source
coefficient `mHigh * beta^(eHigh-eLow) + mLow`. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {y : ℝ}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) - y) := by
  let shift := Int.toNat (eHigh - eLow)
  let k : ℕ := mHigh * fmt.beta ^ shift + mLow
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : eHigh - (shift : ℤ) = eLow := by
    omega
  have hshift :
      fmt.normalizedValue negative (mHigh * fmt.beta ^ shift) eLow =
        fmt.normalizedValue negative mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := negative) (m := mHigh) (shift := shift) (e := eHigh)
    rw [hshift_endpoint] at h
    exact h
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo' : fmt.beta ^ fmt.t ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k, shift] using hhi
  have hsource :
      fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow =
        fmt.signValue negative * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    rw [← hshift]
    simp [k, normalizedValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring
  cases negative
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
      simpa [hsource, signValue] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds
        hbeta heLow hk hr hlo' hhi' hpolicy'
    simpa [hsource, signValue] using hfin
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
      simpa [hsource] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds
        hbeta heLow hk hr hlo' hhi' hpolicy'
    simpa [hsource] using hfin
/-- Same-sign normalized ordered-exponent addition has finite local error
under source round-to-even evidence once a normalized multi-guard quotient
bracket for the aligned source coefficient is supplied.

This is the source-level complementary ordered-exponent wrapper for the C4.4
route: the high operand is shifted onto the lower exponent lattice, the exact
source coefficient is decomposed as `k = beta^d*q+r`, and normalized endpoints
`q,q+1` at exponent `eLow+d` provide the adjacent bracket.  Deriving those
normalized quotient hypotheses automatically from the complementary coefficient
range is a separate dispatcher. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardNormalizedQuotient
    {fmt : FloatingPointFormat}
    {negative : Bool} {y : ℝ}
    {mHigh mLow q r d : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hq : fmt.normalizedMantissa q)
    (hqs : fmt.normalizedMantissa (q + 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) - y) := by
  let shift := Int.toNat (eHigh - eLow)
  let k : ℕ := mHigh * fmt.beta ^ shift + mLow
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : eHigh - (shift : ℤ) = eLow := by
    omega
  have hshift :
      fmt.normalizedValue negative (mHigh * fmt.beta ^ shift) eLow =
        fmt.normalizedValue negative mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := negative) (m := mHigh) (shift := shift) (e := eHigh)
    rw [hshift_endpoint] at h
    exact h
  have hk' : k = fmt.beta ^ d * q + r := by
    simpa [k, shift] using hk
  have hsource :
      fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow =
        fmt.signValue negative * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    rw [← hshift]
    simp [k, normalizedValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring
  cases negative
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
      simpa [hsource, signValue] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_positive_multiGuard_error_finiteSystem_of_normalizedQuotient
        heLow hdle hk' hr hpolicy' hq hqs
    simpa [hsource, signValue] using hfin
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
      simpa [hsource] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_negative_multiGuard_error_finiteSystem_of_normalizedQuotient
        heLow hdle hk' hr hpolicy' hq hqs
    simpa [hsource] using hfin
/-- Same-sign normalized ordered-exponent addition has finite local error under
source round-to-even evidence in the shifted exponent-boundary multi-guard
case.

This is the boundary/carry companion to the normalized quotient wrapper above:
the aligned source coefficient has the form
`k = beta^d * maxNormalMantissa + r`, so the adjacent rounded endpoints cross
from the largest mantissa at exponent `eLow+d` to the smallest mantissa at
`eLow+d+1`. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardBoundary
    {fmt : FloatingPointFormat}
    {negative : Bool} {y : ℝ}
    {mHigh mLow r d : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) - y) := by
  let shift := Int.toNat (eHigh - eLow)
  let k : ℕ := mHigh * fmt.beta ^ shift + mLow
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : eHigh - (shift : ℤ) = eLow := by
    omega
  have hshift :
      fmt.normalizedValue negative (mHigh * fmt.beta ^ shift) eLow =
        fmt.normalizedValue negative mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := negative) (m := mHigh) (shift := shift) (e := eHigh)
    rw [hshift_endpoint] at h
    exact h
  have hk' : k = fmt.beta ^ d * fmt.maxNormalMantissa + r := by
    simpa [k, shift] using hk
  have hsource :
      fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow =
        fmt.signValue negative * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    rw [← hshift]
    simp [k, normalizedValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring
  cases negative
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
      simpa [hsource, signValue] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_positive_multiGuard_boundary_error_finiteSystem
        heLow hdle hk' hr hpolicy'
    simpa [hsource, signValue] using hfin
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
      simpa [hsource] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_negative_multiGuard_boundary_error_finiteSystem
        heLow hdle hk' hr hpolicy'
    simpa [hsource] using hfin
/-- Same-sign normalized ordered-exponent addition has finite local error under
source round-to-even evidence from a supplied multi-guard scaled mantissa range.

This composes the ordinary normalized-quotient and shifted boundary/carry
multi-guard branches with the quotient dispatcher.  It removes the need for a
caller to decide whether the rounded endpoints stay in the same binade or cross
to the next-binade minimum endpoint. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardScaledMantissaRange
    {fmt : FloatingPointFormat}
    {negative : Bool} {y : ℝ}
    {mHigh mLow q r d : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) - y) := by
  let shift := Int.toNat (eHigh - eLow)
  let k : ℕ := mHigh * fmt.beta ^ shift + mLow
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : eHigh - (shift : ℤ) = eLow := by
    omega
  have hshift :
      fmt.normalizedValue negative (mHigh * fmt.beta ^ shift) eLow =
        fmt.normalizedValue negative mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := negative) (m := mHigh) (shift := shift) (e := eHigh)
    rw [hshift_endpoint] at h
    exact h
  have hk' : k = fmt.beta ^ d * q + r := by
    simpa [k, shift] using hk
  have hlo' : fmt.beta ^ d * fmt.minNormalMantissa ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1) := by
    simpa [k, shift] using hhi
  have hsource :
      fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow =
        fmt.signValue negative * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    rw [← hshift]
    simp [k, normalizedValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring
  cases negative
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
      simpa [hsource, signValue] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_positive_multiGuard_error_finiteSystem_of_scaledMantissaRange
        heLow hdle hk' hr hlo' hhi' hpolicy'
    simpa [hsource, signValue] using hfin
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
      simpa [hsource] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_negative_multiGuard_error_finiteSystem_of_scaledMantissaRange
        heLow hdle hk' hr hlo' hhi' hpolicy'
    simpa [hsource] using hfin
/-- Same-sign normalized ordered-exponent addition has finite local error under
source round-to-even evidence from a supplied multi-guard scale and scaled
mantissa range.

This is the quotient/remainder-free companion to
`sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardScaledMantissaRange`:
the caller supplies only the scale `d` and the normalized scaled range, while
the quotient and remainder are derived internally by Euclidean division. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
    {fmt : FloatingPointFormat}
    {negative : Bool} {y : ℝ}
    {mHigh mLow d : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hdle : d ≤ fmt.t)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) - y) := by
  let k : ℕ := mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow
  let q : ℕ := k / fmt.beta ^ d
  let r : ℕ := k % fmt.beta ^ d
  have hpow_pos : 0 < fmt.beta ^ d :=
    Nat.pow_pos (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow =
        fmt.beta ^ d * q + r := by
    change k = fmt.beta ^ d * (k / fmt.beta ^ d) + k % fmt.beta ^ d
    exact (Nat.div_add_mod k (fmt.beta ^ d)).symm
  have hr : r < fmt.beta ^ d := by
    rw [show r = k % fmt.beta ^ d by rfl]
    exact Nat.mod_lt k hpow_pos
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardScaledMantissaRange
      hmHigh hmLow heHigh heLow hle hdle hk hr hlo hhi hpolicy
/-- Positive normalized high operand plus a negative lower normalized operand
has finite local error under source evidence in the binary one-guard-word
aligned-difference branch. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  let shift := Int.toNat (eHigh - eLow)
  let k : ℕ := mHigh * fmt.beta ^ shift - mLow
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : eHigh - (shift : ℤ) = eLow := by
    omega
  have hcoeff_le' : mLow ≤ mHigh * fmt.beta ^ shift := by
    simpa [shift] using hcoeff_le
  have hshift :
      fmt.normalizedValue false (mHigh * fmt.beta ^ shift) eLow =
        fmt.normalizedValue false mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := false) (m := mHigh) (shift := shift) (e := eHigh)
    rw [hshift_endpoint] at h
    exact h
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo' : fmt.beta ^ fmt.t ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k, shift] using hhi
  have hsource :
      fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow =
        ((k : ℕ) : ℝ) * fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    rw [← hshift, fmt.normalizedValue_true_eq_neg_false]
    simp [k, normalizedValue, signValue, Nat.cast_sub hcoeff_le',
      Nat.cast_mul, Nat.cast_pow]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (((k : ℕ) : ℝ) * fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((((k : ℕ) : ℝ) * fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds
      hbeta heLow hk hr hlo' hhi' hpolicy'
  simpa [hsource] using hfin
/-- Negative normalized high operand plus a positive lower normalized operand
has finite local error under source evidence in the binary one-guard-word
aligned-difference branch. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  let shift := Int.toNat (eHigh - eLow)
  let k : ℕ := mHigh * fmt.beta ^ shift - mLow
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : eHigh - (shift : ℤ) = eLow := by
    omega
  have hcoeff_le' : mLow ≤ mHigh * fmt.beta ^ shift := by
    simpa [shift] using hcoeff_le
  have hshift :
      fmt.normalizedValue true (mHigh * fmt.beta ^ shift) eLow =
        fmt.normalizedValue true mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := true) (m := mHigh) (shift := shift) (e := eHigh)
    rw [hshift_endpoint] at h
    exact h
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo' : fmt.beta ^ fmt.t ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k, shift] using hhi
  have hsource :
      fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow =
        fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    rw [← hshift]
    simp [k, normalizedValue, signValue, Nat.cast_sub hcoeff_le',
      Nat.cast_mul, Nat.cast_pow]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds
      hbeta heLow hk hr hlo' hhi' hpolicy'
  simpa [hsource] using hfin
/-- Positive normalized high operand plus a negative lower normalized operand
has finite local error under source round-to-even evidence once the aligned
difference coefficient is bracketed in a supplied multi-guard scale range.

This is the ordinary-cancellation counterpart of the same-sign multi-guard
bridge above.  The exact source is placed on the lower exponent lattice with
coefficient `mHigh * beta^(eHigh-eLow) - mLow`, then the existing positive
multi-guard finite-error dispatcher supplies the rounded-endpoint comparison.
-/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
    {fmt : FloatingPointFormat}
    {y : ℝ} {mHigh mLow d : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hdle : d ≤ fmt.t)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  let shift := Int.toNat (eHigh - eLow)
  let k : ℕ := mHigh * fmt.beta ^ shift - mLow
  let q : ℕ := k / fmt.beta ^ d
  let r : ℕ := k % fmt.beta ^ d
  have hpow_pos : 0 < fmt.beta ^ d :=
    Nat.pow_pos (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : eHigh - (shift : ℤ) = eLow := by
    omega
  have hcoeff_le' : mLow ≤ mHigh * fmt.beta ^ shift := by
    simpa [shift] using hcoeff_le
  have hshift :
      fmt.normalizedValue false (mHigh * fmt.beta ^ shift) eLow =
        fmt.normalizedValue false mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := false) (m := mHigh) (shift := shift) (e := eHigh)
    rw [hshift_endpoint] at h
    exact h
  have hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow =
        fmt.beta ^ d * q + r := by
    change k = fmt.beta ^ d * (k / fmt.beta ^ d) + k % fmt.beta ^ d
    exact (Nat.div_add_mod k (fmt.beta ^ d)).symm
  have hr : r < fmt.beta ^ d := by
    rw [show r = k % fmt.beta ^ d by rfl]
    exact Nat.mod_lt k hpow_pos
  have hlo' : fmt.beta ^ d * fmt.minNormalMantissa ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1) := by
    simpa [k, shift] using hhi
  have hsource :
      fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow =
        ((k : ℕ) : ℝ) * fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    rw [← hshift, fmt.normalizedValue_true_eq_neg_false]
    simp [k, normalizedValue, signValue, Nat.cast_sub hcoeff_le',
      Nat.cast_mul, Nat.cast_pow]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (((k : ℕ) : ℝ) * fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((((k : ℕ) : ℝ) * fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_positive_multiGuard_error_finiteSystem_of_scaledMantissaRange
      heLow hdle hk hr hlo' hhi' hpolicy'
  simpa [hsource] using hfin
/-- Negative normalized high operand plus a positive lower normalized operand
has finite local error in the same supplied multi-guard aligned-difference
range by using the negative multi-guard dispatcher. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
    {fmt : FloatingPointFormat}
    {y : ℝ} {mHigh mLow d : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hdle : d ≤ fmt.t)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  let shift := Int.toNat (eHigh - eLow)
  let k : ℕ := mHigh * fmt.beta ^ shift - mLow
  let q : ℕ := k / fmt.beta ^ d
  let r : ℕ := k % fmt.beta ^ d
  have hpow_pos : 0 < fmt.beta ^ d :=
    Nat.pow_pos (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : eHigh - (shift : ℤ) = eLow := by
    omega
  have hcoeff_le' : mLow ≤ mHigh * fmt.beta ^ shift := by
    simpa [shift] using hcoeff_le
  have hshift :
      fmt.normalizedValue true (mHigh * fmt.beta ^ shift) eLow =
        fmt.normalizedValue true mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := true) (m := mHigh) (shift := shift) (e := eHigh)
    rw [hshift_endpoint] at h
    exact h
  have hk :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow =
        fmt.beta ^ d * q + r := by
    change k = fmt.beta ^ d * (k / fmt.beta ^ d) + k % fmt.beta ^ d
    exact (Nat.div_add_mod k (fmt.beta ^ d)).symm
  have hr : r < fmt.beta ^ d := by
    rw [show r = k % fmt.beta ^ d by rfl]
    exact Nat.mod_lt k hpow_pos
  have hlo' : fmt.beta ^ d * fmt.minNormalMantissa ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1) := by
    simpa [k, shift] using hhi
  have hsource :
      fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow =
        fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ)) := by
    rw [← hshift]
    simp [k, normalizedValue, signValue, Nat.cast_sub hcoeff_le',
      Nat.cast_mul, Nat.cast_pow]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence
        (fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ))) y := by
    simpa [hsource] using hpolicy
  have hfin :
      fmt.finiteSystem
        ((fmt.signValue true * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ))) - y) :=
    fmt.sourceRoundToEvenEvidence_negative_multiGuard_error_finiteSystem_of_scaledMantissaRange
      heLow hdle hk hr hlo' hhi' hpolicy'
  simpa [hsource] using hfin
/-- Positive normalized high operand plus a negative lower normalized operand
has finite local error under source evidence once the aligned-difference
coefficient is in the base-2 multi-guard coefficient range. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ (2 * fmt.t))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  rcases fmt.multiGuardScaleRange_exists_of_baseTwo_bounds hbeta hlo hhi with
    ⟨d, hdle, hrange_lo, hrange_hi⟩
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
      hmHigh hmLow heHigh heLow hle hcoeff_le hdle hrange_lo hrange_hi
      hpolicy
/-- Negative normalized high operand plus a positive lower normalized operand
has finite local error in the base-2 aligned-difference multi-guard coefficient
range. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ (2 * fmt.t))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  rcases fmt.multiGuardScaleRange_exists_of_baseTwo_bounds hbeta hlo hhi with
    ⟨d, hdle, hrange_lo, hrange_hi⟩
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
      hmHigh hmLow heHigh heLow hle hcoeff_le hdle hrange_lo hrange_hi
      hpolicy
/-- Positive normalized high operand plus a negative lower normalized operand
has finite local error in the ordinary-cancellation complementary multi-guard
region.

The lower bound says the aligned difference coefficient needs at least two
precision units; the exponent-window hypothesis supplies the two-precision
upper bound. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hwindow : eLow + (fmt.t : ℤ) > eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  have hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.alignedDiffCoeff_lt_two_precision_bound_of_normalizedMantissas_window
      hbeta hmHigh hmLow hle hwindow
  exact
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hhi hpolicy
/-- Negative normalized high operand plus a positive lower normalized operand
has finite local error in the same ordinary-cancellation complementary
multi-guard region. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {y : ℝ} {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff_le :
      mLow ≤ mHigh * fmt.beta ^ Int.toNat (eHigh - eLow))
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow)
    (hwindow : eLow + (fmt.t : ℤ) > eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  have hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.alignedDiffCoeff_lt_two_precision_bound_of_normalizedMantissas_window
      hbeta hmHigh hmLow hle hwindow
  exact
    fmt.sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hmHigh hmLow heHigh heLow hle hcoeff_le hlo hhi hpolicy
/-- Same-sign normalized ordered-exponent addition has finite local error once
the complementary aligned coefficient is bracketed between two precision units
and the two-precision upper bound.

This packages the logarithmic base-2 binade selector with the quotient-free
multi-guard wrapper.  The remaining raw C4.4 dependency is proving the upper
coefficient bound from the normalized mantissas and exponent-window
assumptions. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {y : ℝ}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ (2 * fmt.t))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) - y) := by
  rcases fmt.multiGuardScaleRange_exists_of_baseTwo_bounds hbeta hlo hhi with
    ⟨d, hdle, hrange_lo, hrange_hi⟩
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardScaleRange
      hmHigh hmLow heHigh heLow hle hdle hrange_lo hrange_hi hpolicy
/-- Same-sign normalized ordered-exponent addition has finite local error in
the complementary multi-guard region.

The caller supplies the lower complementary bound
`2*beta^t <= alignedCoeff` and the exponent-window hypothesis
`eLow + t > eHigh`; the two-precision upper bound and logarithmic scale are
derived internally. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {y : ℝ}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow)
    (hwindow : eLow + (fmt.t : ℤ) > eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative mHigh eHigh +
          fmt.normalizedValue negative mLow eLow) - y) := by
  have hhi :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.alignedCoeff_lt_two_precision_bound_of_normalizedMantissas_window
      hbeta hmHigh hmLow hle hwindow
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hmHigh hmLow heHigh heLow hle hlo hhi hpolicy
/-- Positive same-sign normalized ordered-exponent addition has finite local
roundoff error when the lower addend lies strictly inside the left half-cell of
the higher addend.

This is the first large-alignment branch beyond the exact-or-one-guard
coefficient range used in the C4.4/FastTwoSum route: source round-to-even
evidence selects the higher operand, and the local error is exactly the lower
finite operand.  Boundary, tie/right, and negative-sign companion branches are
kept separate. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_sameSign_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmHighSucc : fmt.normalizedMantissa (mHigh + 1))
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  let a := fmt.normalizedValue false mHigh eHigh
  let b := fmt.normalizedValue false (mHigh + 1) eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hulp_pos : 0 < fmt.ulpAtExponent eHigh := fmt.ulpAtExponent_pos eHigh
  have hlow_lt_ulp : low < fmt.ulpAtExponent eHigh := by
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false mHigh eHigh)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, mHigh, eHigh, hmHigh, hmHighSucc, Or.inl ?_⟩
    exact ⟨rfl, rfl⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have ha_lt_source : a < a + low := by
    linarith
  have hsource_lt_b : a + low < b := by
    linarith
  have hleft_abs : |(a + low) - a| = low := by
    have hsub : (a + low) - a = low := by ring
    rw [hsub, abs_of_pos hlow_pos]
  have hright_abs :
      |(a + low) - b| = fmt.ulpAtExponent eHigh - low := by
    have hsub : (a + low) - b = low - fmt.ulpAtExponent eHigh := by
      linarith
    have hneg : low - fmt.ulpAtExponent eHigh < 0 := by
      linarith
    rw [hsub, abs_of_neg hneg]
    ring
  have hleftCloser : |(a + low) - a| < |(a + low) - b| := by
    rw [hleft_abs, hright_abs]
    linarith
  have hy : y = a := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
        hpolicy hadj ⟨ha_lt_source, hsource_lt_b⟩ hleftCloser
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inl ⟨false, mLow, eLow, hmLow, heLow, rfl⟩)
  rw [hy]
  convert hlow_fin using 1
  dsimp [a, low]
  ring
/-- Positive normalized `high + (-low)` has finite local error in the strict
right half-cell around the high operand, provided the high operand has a
same-exponent predecessor.

This is the first far-magnitude opposite-sign C4.4 branch: the exact source
value lies between the predecessor of the high operand and the high operand
itself, closer to the high endpoint.  Source round-to-even therefore selects
the high endpoint, and the residual is the negative of the finite lower
operand. -/
theorem sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  let a := fmt.normalizedValue false (mHigh - 1) eHigh
  let b := fmt.normalizedValue false mHigh eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hmHighPred :
      fmt.normalizedMantissa (mHigh - 1) :=
    fmt.normalizedMantissa_pred_of_ne_minNormalMantissa hmHigh hneHighMin
  have hmHigh_pos : 0 < mHigh :=
    fmt.normalizedMantissa_pos hmHigh
  have hpred_succ : (mHigh - 1) + 1 = mHigh := by
    omega
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hlow_lt_ulp : low < fmt.ulpAtExponent eHigh := by
    have hulp_pos : 0 < fmt.ulpAtExponent eHigh :=
      fmt.ulpAtExponent_pos eHigh
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent eHigh := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_succ_sub_sameExponent false (mHigh - 1) eHigh)
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, mHigh - 1, eHigh, hmHighPred, ?_, Or.inl ?_⟩
    · simpa [hpred_succ] using hmHigh
    · exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hsource_eq :
      fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow =
        b - low := by
    dsimp [b, low]
    rw [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have ha_lt_source : a < b - low := by
    linarith
  have hsource_lt_b : b - low < b := by
    linarith
  have hright_abs : |(b - low) - b| = low := by
    have hsub : (b - low) - b = -low := by ring
    rw [hsub, abs_neg, abs_of_pos hlow_pos]
  have hleft_abs :
      |(b - low) - a| = fmt.ulpAtExponent eHigh - low := by
    have hsub : (b - low) - a = fmt.ulpAtExponent eHigh - low := by
      linarith
    have hpos : 0 < fmt.ulpAtExponent eHigh - low := by
      linarith
    rw [hsub, abs_of_pos hpos]
  have hrightCloser : |(b - low) - b| < |(b - low) - a| := by
    rw [hright_abs, hleft_abs]
    linarith
  have hy : y = b := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
        hpolicy' hadj ⟨ha_lt_source, hsource_lt_b⟩ hrightCloser
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inl ⟨false, mLow, eLow, hmLow, heLow, rfl⟩)
  have hneg_low_fin : fmt.finiteSystem (-low) :=
    fmt.finiteSystem_neg hlow_fin
  rw [hy]
  convert hneg_low_fin using 1
  dsimp [b, low]
  rw [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Negative normalized `high + (-low)` has finite local error in the strict
predecessor half-cell branch, by sign symmetry from the positive branch.

Equivalently, this covers a large negative operand plus a smaller positive
operand whose magnitude is strictly below half an ulp at the large operand's
exponent. -/
theorem sourceRoundToEvenEvidence_negative_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hneHighMin : mHigh ≠ fmt.minNormalMantissa)
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent eHigh)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true mHigh eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false mHigh eHigh +
          fmt.normalizedValue true mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false mHigh eHigh +
            fmt.normalizedValue true mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_lt_half_ulp
      hmHigh hneHighMin hmLow heLow hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Positive minimum-mantissa normalized `high + (-low)` has finite local error
in the strict half-cell around the exponent-boundary predecessor.

When the high endpoint is `minNormalMantissa`, its immediate predecessor is
`maxNormalMantissa` at the previous exponent.  If the lower opposite-sign
operand is strictly below half of that boundary spacing, source round-to-even
selects the high endpoint and the residual is the negative finite lower
operand. -/
theorem sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_lt_half_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) - y) := by
  let a := fmt.normalizedValue false fmt.maxNormalMantissa (eHigh - 1)
  let b := fmt.normalizedValue false fmt.minNormalMantissa eHigh
  let low := fmt.normalizedValue false mLow eLow
  have hpred_succ : eHigh - 1 + 1 = eHigh := by
    ring
  have hlow_pos : 0 < low := by
    dsimp [low]
    exact fmt.normalizedValue_false_pos hmLow
  have hlow_lt_ulp : low < fmt.ulpAtExponent (eHigh - 1) := by
    have hulp_pos : 0 < fmt.ulpAtExponent (eHigh - 1) :=
      fmt.ulpAtExponent_pos (eHigh - 1)
    linarith
  have hb_sub_a : b - a = fmt.ulpAtExponent (eHigh - 1) := by
    dsimp [a, b]
    simpa [hpred_succ, ulpAtExponent, signValue] using
      (fmt.normalizedValue_boundary_sub false (eHigh - 1))
  have hboundary : fmt.boundaryAdjacentNormalized a b := by
    refine ⟨false, eHigh - 1, Or.inl ?_⟩
    exact ⟨rfl, by dsimp [b]; rw [hpred_succ]⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_boundaryAdjacentNormalized hboundary
  have hsource_eq :
      fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow =
        b - low := by
    dsimp [b, low]
    rw [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hpolicy' :
      fmt.sourceRoundToEvenEvidence (b - low) y := by
    simpa [hsource_eq] using hpolicy
  have ha_lt_source : a < b - low := by
    linarith
  have hsource_lt_b : b - low < b := by
    linarith
  have hright_abs : |(b - low) - b| = low := by
    have hsub : (b - low) - b = -low := by ring
    rw [hsub, abs_neg, abs_of_pos hlow_pos]
  have hleft_abs :
      |(b - low) - a| = fmt.ulpAtExponent (eHigh - 1) - low := by
    have hsub :
        (b - low) - a = fmt.ulpAtExponent (eHigh - 1) - low := by
      linarith
    have hpos : 0 < fmt.ulpAtExponent (eHigh - 1) - low := by
      linarith
    rw [hsub, abs_of_pos hpos]
  have hrightCloser : |(b - low) - b| < |(b - low) - a| := by
    rw [hright_abs, hleft_abs]
    linarith
  have hy : y = b := by
    exact
      fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
        hpolicy' hadj ⟨ha_lt_source, hsource_lt_b⟩ hrightCloser
  have hlow_fin : fmt.finiteSystem low :=
    Or.inr (Or.inl ⟨false, mLow, eLow, hmLow, heLow, rfl⟩)
  have hneg_low_fin : fmt.finiteSystem (-low) :=
    fmt.finiteSystem_neg hlow_fin
  rw [hy]
  convert hneg_low_fin using 1
  dsimp [b, low]
  rw [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Negative minimum-mantissa normalized `high + (-low)` has finite local error
in the strict boundary predecessor half-cell, by sign symmetry. -/
theorem sourceRoundToEvenEvidence_negative_min_normalizedValue_add_pos_orderedExponent_error_finiteSystem_of_low_lt_half_pred_ulp
    {fmt : FloatingPointFormat} {y : ℝ}
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {mLow : ℕ} {eHigh eLow : ℤ}
    (hmLow : fmt.normalizedMantissa mLow)
    (heLow : fmt.exponentInRange eLow)
    (hlow :
      fmt.normalizedValue false mLow eLow <
        (1 / 2 : ℝ) * fmt.ulpAtExponent (eHigh - 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue true fmt.minNormalMantissa eHigh +
          fmt.normalizedValue false mLow eLow) - y) := by
  have hpolicy_pos :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue false fmt.minNormalMantissa eHigh +
          fmt.normalizedValue true mLow eLow) (-y) := by
    have hbeta_even : evenMantissa fmt.beta := by
      rw [hbeta]
      norm_num [evenMantissa]
    have hneg := fmt.sourceRoundToEvenEvidence_neg hbeta_even ht hpolicy
    convert hneg using 1
    simp [fmt.normalizedValue_true_eq_neg_false]
    ring
  have hfin_pos :
      fmt.finiteSystem
        ((fmt.normalizedValue false fmt.minNormalMantissa eHigh +
            fmt.normalizedValue true mLow eLow) - (-y)) :=
    fmt.sourceRoundToEvenEvidence_positive_min_normalizedValue_add_neg_orderedExponent_error_finiteSystem_of_low_lt_half_pred_ulp
      hmLow heLow hlow hpolicy_pos
  have hfin_neg := fmt.finiteSystem_neg hfin_pos
  convert hfin_neg using 1
  simp [fmt.normalizedValue_true_eq_neg_false]
  ring
/-- Same-sign mixed normal/subnormal addition has finite local error under
binary round-to-even evidence in the one-guard-word branch.  The normalized
operand is shifted onto the subnormal lattice, yielding the source coefficient
`m * beta^(e-emin) + n`. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_guardCoeffBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {y : ℝ}
    {m n : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlo :
      fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        2 * fmt.beta ^ fmt.t)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) - y) := by
  let shift := Int.toNat (e - fmt.emin)
  let k : ℕ := m * fmt.beta ^ shift + n
  let q : ℕ := k / fmt.beta
  let r : ℕ := k % fmt.beta
  have hshift_cast : ((shift : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : e - (shift : ℤ) = fmt.emin := by
    omega
  have hshift :
      fmt.normalizedValue negative m e =
        fmt.subnormalValue negative (m * fmt.beta ^ shift) :=
    fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
      (negative := negative) (m := m) (shift := shift) (e := e)
      hshift_endpoint
  have hk : k = fmt.beta * q + r := by
    rw [show q = k / fmt.beta by rfl, show r = k % fmt.beta by rfl]
    exact (Nat.div_add_mod k fmt.beta).symm
  have hr : r < fmt.beta := by
    rw [show r = k % fmt.beta by rfl]
    exact Nat.mod_lt k (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hlo' : fmt.beta ^ fmt.t ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < 2 * fmt.beta ^ fmt.t := by
    simpa [k, shift] using hhi
  have hemin : fmt.exponentInRange fmt.emin :=
    ⟨le_rfl, fmt.emin_le_emax⟩
  have hsource :
      fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n =
        fmt.signValue negative * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
    rw [hshift]
    simp [k, subnormalValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring
  cases negative
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) y := by
      simpa [hsource, signValue] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_positive_binaryGuard_error_finiteSystem_of_guardCoeffBounds
        hbeta hemin hk hr hlo' hhi' hpolicy'
    simpa [hsource, signValue] using hfin
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) y := by
      simpa [hsource] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_negative_binaryGuard_error_finiteSystem_of_guardCoeffBounds
        hbeta hemin hk hr hlo' hhi' hpolicy'
    simpa [hsource] using hfin
/-- Same-sign mixed normal/subnormal addition has finite local error under
source round-to-even evidence from a supplied multi-guard scaled mantissa
range.

This is the mixed analogue of the normalized ordered-exponent multi-guard
handoff: the normalized operand is first shifted onto the `emin` subnormal
lattice, and the quotient/range dispatcher chooses the ordinary or boundary
rounded endpoints. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_multiGuardScaledMantissaRange
    {fmt : FloatingPointFormat}
    {negative : Bool} {y : ℝ}
    {m n q r d : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdle : d ≤ fmt.t)
    (hk :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n =
        fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) - y) := by
  let shift := Int.toNat (e - fmt.emin)
  let k : ℕ := m * fmt.beta ^ shift + n
  have hshift_cast : ((shift : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_endpoint : e - (shift : ℤ) = fmt.emin := by
    omega
  have hshift :
      fmt.normalizedValue negative m e =
        fmt.subnormalValue negative (m * fmt.beta ^ shift) :=
    fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
      (negative := negative) (m := m) (shift := shift) (e := e)
      hshift_endpoint
  have hk' : k = fmt.beta ^ d * q + r := by
    simpa [k, shift] using hk
  have hlo' : fmt.beta ^ d * fmt.minNormalMantissa ≤ k := by
    simpa [k, shift] using hlo
  have hhi' : k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1) := by
    simpa [k, shift] using hhi
  have hemin : fmt.exponentInRange fmt.emin :=
    ⟨le_rfl, fmt.emin_le_emax⟩
  have hsource :
      fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n =
        fmt.signValue negative * ((k : ℕ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
    rw [hshift]
    simp [k, subnormalValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring
  cases negative
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) y := by
      simpa [hsource, signValue] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_positive_multiGuard_error_finiteSystem_of_scaledMantissaRange
        hemin hdle hk' hr hlo' hhi' hpolicy'
    simpa [hsource, signValue] using hfin
  · have hpolicy' :
        fmt.sourceRoundToEvenEvidence
          (fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) y := by
      simpa [hsource] using hpolicy
    have hfin :
        fmt.finiteSystem
          ((fmt.signValue true * ((k : ℕ) : ℝ) *
            fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) - y) :=
      fmt.sourceRoundToEvenEvidence_negative_multiGuard_error_finiteSystem_of_scaledMantissaRange
        hemin hdle hk' hr hlo' hhi' hpolicy'
    simpa [hsource] using hfin
/-- Same-sign mixed normal/subnormal addition has finite local error under
source round-to-even evidence from a supplied multi-guard scale and scaled
mantissa range.  The quotient and remainder are derived internally. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_multiGuardScaleRange
    {fmt : FloatingPointFormat}
    {negative : Bool} {y : ℝ}
    {m n d : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hdle : d ≤ fmt.t)
    (hlo :
      fmt.beta ^ d * fmt.minNormalMantissa ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) - y) := by
  let k : ℕ := m * fmt.beta ^ Int.toNat (e - fmt.emin) + n
  let q : ℕ := k / fmt.beta ^ d
  let r : ℕ := k % fmt.beta ^ d
  have hpow_pos : 0 < fmt.beta ^ d :=
    Nat.pow_pos (lt_trans Nat.zero_lt_one fmt.one_lt_beta)
  have hk :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n =
        fmt.beta ^ d * q + r := by
    change k = fmt.beta ^ d * (k / fmt.beta ^ d) + k % fmt.beta ^ d
    exact (Nat.div_add_mod k (fmt.beta ^ d)).symm
  have hr : r < fmt.beta ^ d := by
    rw [show r = k % fmt.beta ^ d by rfl]
    exact Nat.mod_lt k hpow_pos
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_multiGuardScaledMantissaRange
      hm hn he hdle hk hr hlo hhi hpolicy
/-- Same-sign mixed normal/subnormal addition has finite local error under
source round-to-even evidence once the mixed aligned coefficient is bracketed
between two precision units and the two-precision upper bound. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_multiGuardCoefficientBounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {y : ℝ}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        fmt.beta ^ (2 * fmt.t))
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) - y) := by
  rcases fmt.multiGuardScaleRange_exists_of_baseTwo_bounds hbeta hlo hhi with
    ⟨d, hdle, hrange_lo, hrange_hi⟩
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_multiGuardScaleRange
      hm hn he hdle hrange_lo hrange_hi hpolicy
/-- Base-two upper bound for the mixed normal/subnormal complementary
coefficient.

If the normal exponent is still inside one precision window above `emin`, then
the subnormal-lattice aligned coefficient
`m * beta^(e-emin) + n` is strictly below `beta^(2*t)`. -/
theorem mixedAlignedCoeff_lt_two_precision_bound_of_normalized_subnormal_window
    {fmt : FloatingPointFormat}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hwindow : fmt.emin + (fmt.t : ℤ) > e) :
    m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
      fmt.beta ^ (2 * fmt.t) := by
  let shift := Int.toNat (e - fmt.emin)
  have hshift_nonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
  have hshift_cast : ((shift : ℕ) : ℤ) = e - fmt.emin := by
    simpa [shift] using Int.toNat_of_nonneg hshift_nonneg
  have hshift_lt_t : shift < fmt.t := by
    have ht_int : e - fmt.emin < (fmt.t : ℤ) := by omega
    omega
  have hshift_le_pred : shift ≤ fmt.t - 1 := by
    omega
  have hbeta_pos : 0 < fmt.beta := lt_trans Nat.zero_lt_one fmt.one_lt_beta
  have hshift_pow_le : fmt.beta ^ shift ≤ fmt.beta ^ (fmt.t - 1) :=
    Nat.pow_le_pow_right hbeta_pos hshift_le_pred
  have hm_mul_lt :
      m * fmt.beta ^ shift < fmt.beta ^ fmt.t * fmt.beta ^ (fmt.t - 1) := by
    exact Nat.mul_lt_mul_of_lt_of_le hm.2 hshift_pow_le
      (Nat.pow_pos hbeta_pos)
  have hn_lt : n < fmt.beta ^ (fmt.t - 1) := by
    simpa [minNormalMantissa] using hn.2
  have hsum_lt :
      m * fmt.beta ^ shift + n <
        fmt.beta ^ fmt.t * fmt.beta ^ (fmt.t - 1) +
          fmt.beta ^ (fmt.t - 1) :=
    Nat.add_lt_add hm_mul_lt hn_lt
  have hpow_t_pos : 0 < fmt.beta ^ fmt.t := Nat.pow_pos hbeta_pos
  have hone_le_pow_t : 1 ≤ fmt.beta ^ fmt.t :=
    Nat.succ_le_of_lt hpow_t_pos
  have hpow_t_add_one_le :
      fmt.beta ^ fmt.t + 1 ≤ fmt.beta * fmt.beta ^ fmt.t := by
    calc
      fmt.beta ^ fmt.t + 1 ≤ fmt.beta ^ fmt.t + fmt.beta ^ fmt.t :=
        Nat.add_le_add_left hone_le_pow_t (fmt.beta ^ fmt.t)
      _ = 2 * fmt.beta ^ fmt.t := by omega
      _ ≤ fmt.beta * fmt.beta ^ fmt.t :=
        Nat.mul_le_mul_right (fmt.beta ^ fmt.t) fmt.beta_ge_two
  have hbeta_mul_pred :
      fmt.beta * fmt.beta ^ (fmt.t - 1) = fmt.beta ^ fmt.t := by
    calc
      fmt.beta * fmt.beta ^ (fmt.t - 1) =
          fmt.beta ^ (fmt.t - 1) * fmt.beta := by rw [Nat.mul_comm]
      _ = fmt.beta ^ ((fmt.t - 1) + 1) := by rw [pow_succ]
      _ = fmt.beta ^ fmt.t := by
        congr 1
        omega
  have hbound_le :
      fmt.beta ^ fmt.t * fmt.beta ^ (fmt.t - 1) +
          fmt.beta ^ (fmt.t - 1) ≤
        fmt.beta ^ (2 * fmt.t) := by
    calc
      fmt.beta ^ fmt.t * fmt.beta ^ (fmt.t - 1) +
          fmt.beta ^ (fmt.t - 1) =
          (fmt.beta ^ fmt.t + 1) * fmt.beta ^ (fmt.t - 1) := by ring
      _ ≤ (fmt.beta * fmt.beta ^ fmt.t) * fmt.beta ^ (fmt.t - 1) :=
        Nat.mul_le_mul_right (fmt.beta ^ (fmt.t - 1)) hpow_t_add_one_le
      _ = fmt.beta ^ fmt.t * (fmt.beta * fmt.beta ^ (fmt.t - 1)) := by ring
      _ = fmt.beta ^ fmt.t * fmt.beta ^ fmt.t := by rw [hbeta_mul_pred]
      _ = fmt.beta ^ (fmt.t + fmt.t) := by rw [pow_add]
      _ = fmt.beta ^ (2 * fmt.t) := by
        congr 1
        omega
  simpa [shift] using lt_of_lt_of_le hsum_lt hbound_le
/-- Same-sign mixed normal/subnormal addition has finite local error in the
base-2 complementary multi-guard region.

The lower complementary bound supplies `2*beta^t <= alignedCoeff`; the
precision-window hypothesis supplies the strict two-precision upper bound. -/
theorem sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_multiGuardComplementaryRegion
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {negative : Bool} {y : ℝ}
    {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hlo :
      2 * fmt.beta ^ fmt.t ≤
        m * fmt.beta ^ Int.toNat (e - fmt.emin) + n)
    (hwindow : fmt.emin + (fmt.t : ℤ) > e)
    (hpolicy :
      fmt.sourceRoundToEvenEvidence
        (fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) y) :
    fmt.finiteSystem
      ((fmt.normalizedValue negative m e +
          fmt.subnormalValue negative n) - y) := by
  have hhi :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.mixedAlignedCoeff_lt_two_precision_bound_of_normalized_subnormal_window
      hm hn he hwindow
  exact
    fmt.sourceRoundToEvenEvidence_normalizedValue_add_sameSign_subnormal_error_finiteSystem_of_multiGuardCoefficientBounds
      hbeta hm hn he hlo hhi hpolicy
theorem sourceRoundToEvenEvidence_unique
    {fmt : FloatingPointFormat} {x y z : ℝ}
    (hy : fmt.sourceRoundToEvenEvidence x y)
    (hz : fmt.sourceRoundToEvenEvidence x z) :
    y = z := by
  rcases hy with hpos | hneg
  · rcases hpos with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_mem : fmt.unboundedNormalizedSystem x :=
        ⟨false, m, e, hm, hx_eq⟩
      rw [hy_eq]
      exact
        (sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
          hx_mem hz).symm
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, hleft, _ha_nonneg,
          ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        (sourceRoundToEvenEvidence_eq_nearest_of_realOrderAdjacent_between
          hz hadj hleft ⟨ha_le_x, hx_le_b⟩).symm
  · rcases hneg with ⟨e, _hlo, _hhi, hexact | hbracket⟩
    · rcases hexact with ⟨m, hm, hx_eq, hy_eq⟩
      have hx_mem : fmt.unboundedNormalizedSystem x :=
        ⟨true, m, e, hm, hx_eq⟩
      rw [hy_eq]
      exact
        (sourceRoundToEvenEvidence_eq_self_of_unboundedNormalizedSystem
          hx_mem hz).symm
    · rcases hbracket with
        ⟨a, b, leftMantissa, hadj, hleft, _hb_nonpos,
          ha_le_x, hx_le_b, hy_eq⟩
      rw [hy_eq]
      exact
        (sourceRoundToEvenEvidence_eq_nearest_of_realOrderAdjacent_between
          hz hadj hleft ⟨ha_le_x, hx_le_b⟩).symm
/-- Source-facing positive finite-normal-range nearest-rounding theorem for the
finite relation.  This is the non-strict `|delta| <= u` variant of Higham's
Theorem 2.2 for positive normal-range inputs. -/
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_positive_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hxpos : 0 < x := lt_of_lt_of_le fmt.minNormalMagnitude_pos hxlo
  rcases fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_positive
      (x := x) hxpos with ⟨y, δ, hround, hδ, hwit⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
      hround hyfin hxlo
  exact ⟨y, δ, hfiniteRound, hδ, hwit⟩
/-- Source-facing negative finite-normal-range nearest-rounding theorem for the
finite relation.  This is the sign mirror of the positive normal-range wrapper. -/
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_negative_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hxneg : x < 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  rcases fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_negative
      (x := x) hxneg with ⟨y, δ, hround, hδ, hwit⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
      hround hyfin hxhi
  exact ⟨y, δ, hfiniteRound, hδ, hwit⟩
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_lt_positive_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hxpos : 0 < x := lt_of_lt_of_le fmt.minNormalMagnitude_pos hxlo
  rcases fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_positive
      (x := x) hxpos with ⟨y, δ, hround, hδ, hwit⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
      hround hyfin hxlo
  exact ⟨y, δ, hfiniteRound, hδ, hwit⟩
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_lt_negative_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  have hxneg : x < 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  rcases fmt.exists_nearestRoundingToUnbounded_signedRelErrorWitness_lt_negative
      (x := x) hxneg with ⟨y, δ, hround, hδ, hwit⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
      hround hyfin hxhi
  exact ⟨y, δ, hfiniteRound, hδ, hwit⟩
/-- Source-facing finite-normal-range nearest-rounding theorem for the finite
relation.  This packages the positive and negative wrappers into the
non-strict `|delta| <= u` finite-format relation version of Higham Theorem 2.2
over `finiteNormalRange`.  It remains relation-valued and does not choose a
total tie policy. -/
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
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
      fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_negative_finiteNormalRange
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
      fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_positive_finiteNormalRange
        hxlo hxhi
/-- Every real input has at least one finite nearest-rounded value in the
relation-valued finite system.  This is the total existence theorem for the
nearest-rounding relation; it still does not choose among ties or define an
operational IEEE `fl` function. -/
theorem exists_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    ∃ y : ℝ, fmt.nearestRoundingToFinite x y := by
  by_cases hunder : fmt.finiteUnderflowRange x
  · exact fmt.exists_nearestRoundingToFinite_finiteUnderflowRange hunder
  · have hmin_le : fmt.minNormalMagnitude ≤ |x| := by
      rw [finiteUnderflowRange] at hunder
      exact le_of_not_gt hunder
    by_cases hover : fmt.finiteOverflowRange x
    · exact
        ⟨fmt.finiteOverflowSaturation x,
          fmt.finiteOverflowSaturation_nearestRoundingToFinite_of_finiteOverflowRange
            hover⟩
    · have hmax_le : |x| ≤ fmt.maxFiniteMagnitude := by
        rw [finiteOverflowRange] at hover
        exact le_of_not_gt hover
      rcases fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_finiteNormalRange
          ⟨hmin_le, hmax_le⟩ with
        ⟨y, _δ, hround, _hδ, _hwit⟩
      exact ⟨y, hround⟩
/-- A total source-facing finite nearest-rounding choice.  It chooses an
arbitrary nearest value from the relation, so ties are intentionally not
specified; round-to-even and IEEE exception behavior remain separate. -/
noncomputable def finiteNearestFl (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  Classical.choose (fmt.exists_nearestRoundingToFinite x)
theorem finiteNearestFl_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.nearestRoundingToFinite x (fmt.finiteNearestFl x) :=
  Classical.choose_spec (fmt.exists_nearestRoundingToFinite x)
theorem finiteNearestFl_output_not_finiteOverflowRange
    (fmt : FloatingPointFormat) (x : ℝ) :
    ¬ fmt.finiteOverflowRange (fmt.finiteNearestFl x) :=
  fmt.nearestRoundingToFinite_output_not_finiteOverflowRange
    (fmt.finiteNearestFl_nearestRoundingToFinite x)
theorem finiteNearestFl_output_abs_le_maxFiniteMagnitude
    (fmt : FloatingPointFormat) (x : ℝ) :
    |fmt.finiteNearestFl x| ≤ fmt.maxFiniteMagnitude :=
  fmt.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude
    (fmt.finiteNearestFl_nearestRoundingToFinite x)
/-- Strict source-facing finite-normal-range nearest-rounding theorem for the
finite relation, matching Higham Theorem 2.2's `|delta| < u` over the normal
range.  It remains relation-valued and independent of a concrete tie policy. -/
theorem exists_nearestRoundingToFinite_signedRelErrorWitness_lt_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
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
      fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_lt_negative_finiteNormalRange
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
      fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_lt_positive_finiteNormalRange
        hxlo hxhi
/-- Positive finite-normal-range nearest-rounding theorem that preserves the
explicit source-level round-away selector evidence. -/
theorem exists_finiteNormalRoundAway_signedRelErrorWitness_lt_positive_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundAwayEvidence x y := by
  have hxpos : 0 < x := lt_of_lt_of_le fmt.minNormalMagnitude_pos hxlo
  rcases
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
      (x := x) hxpos with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
      hround hyfin hxlo
  exact ⟨y, δ, hfiniteRound, hδ, hwit, Or.inl hpolicy⟩
/-- Negative finite-normal-range nearest-rounding theorem that preserves the
explicit source-level round-away selector evidence. -/
theorem exists_finiteNormalRoundAway_signedRelErrorWitness_lt_negative_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundAwayEvidence x y := by
  have hxneg : x < 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  rcases
    fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
      (x := x) hxneg with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
      hround hyfin hxhi
  exact ⟨y, δ, hfiniteRound, hδ, hwit, Or.inr hpolicy⟩
/-- Finite-normal-range nearest-rounding theorem that chooses a nearest value
by the source-level round-away policy.  This is still a normal-range theorem:
finite underflow/overflow and IEEE exception behavior remain separate. -/
theorem exists_finiteNormalRoundAway_signedRelErrorWitness_lt_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundAwayEvidence x y := by
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
      fmt.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_negative_finiteNormalRange
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
      fmt.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_positive_finiteNormalRange
        hxlo hxhi
/-- Global positive unbounded-normalized nearest-rounding bridge that carries
the explicit local round-to-even selector evidence through exponent selection.
The left endpoint's normalized mantissa is recorded for the tie rule. -/
theorem exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_positive
    {fmt : FloatingPointFormat} {x : ℝ} (hx : 0 < x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundToEvenEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_positive
      hx with
    ⟨_yAway, _δAway, _hroundAway, _hδAway, _hwitAway, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨false, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact
      ⟨x, δ, hround, hδ, hwit,
        Or.inl ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b, _hy_eq⟩
    rcases hadj.1 with ⟨negative, leftMantissa, eLeft, hmLeft, ha_repr⟩
    let y := nearestAdjacentRoundToEven x a b leftMantissa
    have hround : fmt.nearestRoundingToUnbounded x y := by
      dsimp [y]
      exact
        fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
          leftMantissa hadj ⟨ha_le_x, hx_le_b⟩
    rcases
      fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonneg_between
        hround hadj ha_nonneg ⟨ha_le_x, hx_le_b⟩ with
      ⟨δ, hδ, hwit, _hround⟩
    exact
      ⟨y, δ, hround, hδ, hwit,
        Or.inl ⟨e, hlo, hhi,
          Or.inr
            ⟨a, b, leftMantissa, hadj,
              ⟨negative, eLeft, hmLeft, ha_repr⟩,
              ha_nonneg, ha_le_x, hx_le_b, rfl⟩⟩⟩
/-- Global negative unbounded-normalized nearest-rounding bridge that carries
the explicit local round-to-even selector evidence through exponent selection.
The left endpoint's normalized mantissa is recorded for the tie rule. -/
theorem exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_negative
    {fmt : FloatingPointFormat} {x : ℝ} (hx : x < 0) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToUnbounded x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundToEvenEvidence x y := by
  rcases fmt.exists_nearestAdjacentRoundAway_signedRelErrorWitness_lt_negative
      hx with
    ⟨_yAway, _δAway, _hroundAway, _hδAway, _hwitAway, hpolicy⟩
  rcases hpolicy with ⟨e, hlo, hhi, hexact | hbracket⟩
  · rcases hexact with ⟨m, hm, hx_eq, _hy_eq⟩
    have hx_mem : fmt.unboundedNormalizedSystem x :=
      ⟨true, m, e, hm, hx_eq⟩
    rcases fmt.nearestRoundingToUnbounded_exact_signedRelErrorWitness_lt hx_mem with
      ⟨δ, hδ, hwit, hround⟩
    exact
      ⟨x, δ, hround, hδ, hwit,
        Or.inr ⟨e, hlo, hhi, Or.inl ⟨m, hm, hx_eq, rfl⟩⟩⟩
  · rcases hbracket with ⟨a, b, hadj, hb_nonpos, ha_le_x, hx_le_b, _hy_eq⟩
    rcases hadj.1 with ⟨negative, leftMantissa, eLeft, hmLeft, ha_repr⟩
    let y := nearestAdjacentRoundToEven x a b leftMantissa
    have hround : fmt.nearestRoundingToUnbounded x y := by
      dsimp [y]
      exact
        fmt.nearestAdjacentRoundToEven_nearestRoundingToUnbounded_of_realOrderAdjacent_ordered_between
          leftMantissa hadj ⟨ha_le_x, hx_le_b⟩
    rcases
      fmt.nearestRoundingToUnbounded_signedRelErrorWitness_lt_of_nonpos_between
        hround hadj hb_nonpos ⟨ha_le_x, hx_le_b⟩ with
      ⟨δ, hδ, hwit, _hround⟩
    exact
      ⟨y, δ, hround, hδ, hwit,
        Or.inr ⟨e, hlo, hhi,
          Or.inr
            ⟨a, b, leftMantissa, hadj,
              ⟨negative, eLeft, hmLeft, ha_repr⟩,
              hb_nonpos, ha_le_x, hx_le_b, rfl⟩⟩⟩
/-- Positive finite-normal-range nearest-rounding theorem that preserves the
explicit source-level round-to-even selector evidence. -/
theorem exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_positive_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundToEvenEvidence x y := by
  have hxpos : 0 < x := lt_of_lt_of_le fmt.minNormalMagnitude_pos hxlo
  rcases
    fmt.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_positive
      (x := x) hxpos with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
      hround hyfin hxlo
  exact ⟨y, δ, hfiniteRound, hδ, hwit, hpolicy⟩
/-- Negative finite-normal-range nearest-rounding theorem that preserves the
explicit source-level round-to-even selector evidence. -/
theorem exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_negative_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundToEvenEvidence x y := by
  have hxneg : x < 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  rcases
    fmt.exists_nearestAdjacentRoundToEven_signedRelErrorWitness_lt_negative
      (x := x) hxneg with
    ⟨y, δ, hround, hδ, hwit, hpolicy⟩
  have hyfin :=
    fmt.nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
      hround hxlo hxhi
  have hfiniteRound :=
    fmt.nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
      hround hyfin hxhi
  exact ⟨y, δ, hfiniteRound, hδ, hwit, hpolicy⟩
/-- Finite-normal-range nearest-rounding theorem that chooses a nearest value
by the source-level round-to-even policy.  This is still a normal-range theorem:
finite underflow/overflow and IEEE exception behavior remain separate. -/
theorem exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ y δ : ℝ,
      fmt.nearestRoundingToFinite x y ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness y x δ ∧
            fmt.sourceRoundToEvenEvidence x y := by
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
      fmt.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_negative_finiteNormalRange
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
      fmt.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_positive_finiteNormalRange
        hxlo hxhi
/-- Any finite nearest-rounded value of a finite-normal input satisfies the
non-strict forward relative-error model.  This upgrades the relation-valued
existence theorem into an arbitrary-output theorem for the finite nearest
relation; tie choices may select any nearest endpoint. -/
theorem nearestRoundingToFinite_signedRelErrorWitness_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToFinite x y)
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      |δ| ≤ fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_finiteNormalRange
      hx with ⟨y₀, δ₀, hround₀, hδ₀, hwit₀⟩
  have hmin : |x - y| ≤ |x - y₀| :=
    nearestRoundingIn_minimal hround (nearestRoundingIn_mem hround₀)
  have hy₀_bound : |x - y₀| ≤ fmt.unitRoundoff * |x| := by
    have hdiff : x - y₀ = -x * δ₀ := by
      unfold signedRelErrorWitness at hwit₀
      rw [hwit₀]
      ring
    calc
      |x - y₀| = |x| * |δ₀| := by
        rw [hdiff, abs_mul, abs_neg]
      _ ≤ |x| * fmt.unitRoundoff :=
        mul_le_mul_of_nonneg_left hδ₀ (abs_nonneg x)
      _ = fmt.unitRoundoff * |x| := by ring
  have hbound : |x - y| ≤ fmt.unitRoundoff * |x| :=
    le_trans hmin hy₀_bound
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    have hmin_pos := fmt.minNormalMagnitude_pos
    have hxlo := hx.1
    rw [hx_zero, abs_zero] at hxlo
    exact (not_lt_of_ge hxlo) hmin_pos
  exact fmt.signedRelErrorWitness_of_abs_sub_le_unitRoundoff_mul_abs hx_ne hbound
/-- Strict arbitrary-output version of Higham Theorem 2.2 on the finite normal
range: every finite nearest-rounded value, not only the existentially selected
one, satisfies a strict signed relative-error witness. -/
theorem nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToFinite x y)
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      |δ| < fmt.unitRoundoff ∧ signedRelErrorWitness y x δ := by
  rcases fmt.exists_nearestRoundingToFinite_signedRelErrorWitness_lt_finiteNormalRange
      hx with ⟨y₀, δ₀, hround₀, hδ₀, hwit₀⟩
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    have hmin_pos := fmt.minNormalMagnitude_pos
    have hxlo := hx.1
    rw [hx_zero, abs_zero] at hxlo
    exact (not_lt_of_ge hxlo) hmin_pos
  have hxabs_pos : 0 < |x| := abs_pos.mpr hx_ne
  have hmin : |x - y| ≤ |x - y₀| :=
    nearestRoundingIn_minimal hround (nearestRoundingIn_mem hround₀)
  have hy₀_bound : |x - y₀| < fmt.unitRoundoff * |x| := by
    have hdiff : x - y₀ = -x * δ₀ := by
      unfold signedRelErrorWitness at hwit₀
      rw [hwit₀]
      ring
    calc
      |x - y₀| = |x| * |δ₀| := by
        rw [hdiff, abs_mul, abs_neg]
      _ < |x| * fmt.unitRoundoff :=
        mul_lt_mul_of_pos_left hδ₀ hxabs_pos
      _ = fmt.unitRoundoff * |x| := by ring
  have hbound : |x - y| < fmt.unitRoundoff * |x| :=
    lt_of_le_of_lt hmin hy₀_bound
  exact fmt.signedRelErrorWitness_of_abs_sub_lt_unitRoundoff_mul_abs hx_ne hbound
/-- Source-style round-away tie choice for `fl` on the finite normal range.
Exact representable inputs return themselves; non-exact inputs use
`nearestAdjacentRoundAway` after sign and exponent-slice bracketing.  This is
not a full finite-format operation with underflow/overflow or IEEE exceptions. -/
noncomputable def finiteNormalRoundAway (fmt : FloatingPointFormat) (x : ℝ)
    (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose
    (fmt.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_finiteNormalRange hx)
theorem finiteNormalRoundAway_spec
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundAway x hx) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalRoundAway x hx) x δ ∧
            fmt.sourceRoundAwayEvidence x (fmt.finiteNormalRoundAway x hx) := by
  exact
    Classical.choose_spec
      (fmt.exists_finiteNormalRoundAway_signedRelErrorWitness_lt_finiteNormalRange hx)
theorem finiteNormalRoundAway_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundAway x hx) := by
  rcases fmt.finiteNormalRoundAway_spec hx with ⟨δ, hround, _hδ, _hwit, _hpolicy⟩
  exact hround
theorem finiteNormalRoundAway_sourceRoundAwayEvidence
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundAwayEvidence x (fmt.finiteNormalRoundAway x hx) := by
  rcases fmt.finiteNormalRoundAway_spec hx with ⟨δ, _hround, _hδ, _hwit, hpolicy⟩
  exact hpolicy
theorem finiteNormalRoundAway_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundAway x hx) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalRoundAway x hx) x δ := by
  rcases fmt.finiteNormalRoundAway_spec hx with ⟨δ, hround, hδ, hwit, _hpolicy⟩
  exact ⟨δ, hround, hδ, hwit⟩
/-- Source-style round-to-even tie choice for `fl` on the finite normal range.
Exact representable inputs return themselves; non-exact inputs use
`nearestAdjacentRoundToEven` after sign and exponent-slice bracketing, with the
left endpoint's normalized mantissa recorded for tie parity.  This is not a
full finite-format operation with underflow/overflow or IEEE exceptions. -/
noncomputable def finiteNormalRoundToEven (fmt : FloatingPointFormat) (x : ℝ)
    (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose
    (fmt.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_finiteNormalRange hx)
theorem finiteNormalRoundToEven_spec
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundToEven x hx) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalRoundToEven x hx) x δ ∧
            fmt.sourceRoundToEvenEvidence x (fmt.finiteNormalRoundToEven x hx) := by
  exact
    Classical.choose_spec
      (fmt.exists_finiteNormalRoundToEven_signedRelErrorWitness_lt_finiteNormalRange hx)
theorem finiteNormalRoundToEven_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundToEven x hx) := by
  rcases fmt.finiteNormalRoundToEven_spec hx with
    ⟨δ, hround, _hδ, _hwit, _hpolicy⟩
  exact hround
theorem finiteNormalRoundToEven_sourceRoundToEvenEvidence
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundToEvenEvidence x (fmt.finiteNormalRoundToEven x hx) := by
  rcases fmt.finiteNormalRoundToEven_spec hx with
    ⟨δ, _hround, _hδ, _hwit, hpolicy⟩
  exact hpolicy
theorem finiteNormalRoundToEven_eq_of_sourceRoundToEvenEvidence
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteNormalRange x)
    (hpolicy : fmt.sourceRoundToEvenEvidence x y) :
    fmt.finiteNormalRoundToEven x hx = y :=
  sourceRoundToEvenEvidence_unique
    (fmt.finiteNormalRoundToEven_sourceRoundToEvenEvidence hx) hpolicy
theorem finiteNormalRoundToEven_neg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (hx : fmt.finiteNormalRange x) (hxneg : fmt.finiteNormalRange (-x)) :
    fmt.finiteNormalRoundToEven (-x) hxneg =
      -fmt.finiteNormalRoundToEven x hx := by
  have hpolicy :=
    fmt.finiteNormalRoundToEven_sourceRoundToEvenEvidence hx
  have hpolicy_neg :=
    fmt.sourceRoundToEvenEvidence_neg hbeta ht hpolicy
  exact
    fmt.finiteNormalRoundToEven_eq_of_sourceRoundToEvenEvidence
      hxneg hpolicy_neg
theorem finiteNormalRoundToEven_signedRelErrorWitness_lt
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteNormalRoundToEven x hx) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteNormalRoundToEven x hx) x δ := by
  rcases fmt.finiteNormalRoundToEven_spec hx with
    ⟨δ, hround, hδ, hwit, _hpolicy⟩
  exact ⟨δ, hround, hδ, hwit⟩
/-- Source-style finite-normal selector for rounding toward negative infinity.
This is a normal-range selector only; finite underflow/overflow and IEEE flags
are handled by later total finite/IEEE layers. -/
noncomputable def finiteNormalRoundTowardNegative
    (fmt : FloatingPointFormat) (x : ℝ) (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose (fmt.exists_sourceRoundTowardNegativeEvidence_finiteNormalRange hx)
theorem finiteNormalRoundTowardNegative_sourceRoundTowardNegativeEvidence
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundTowardNegativeEvidence x
      (fmt.finiteNormalRoundTowardNegative x hx) :=
  Classical.choose_spec
    (fmt.exists_sourceRoundTowardNegativeEvidence_finiteNormalRange hx)
theorem finiteNormalRoundTowardNegative_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.unboundedNormalizedSystem (fmt.finiteNormalRoundTowardNegative x hx) :=
  fmt.sourceRoundTowardNegativeEvidence_unboundedNormalizedSystem
    (fmt.finiteNormalRoundTowardNegative_sourceRoundTowardNegativeEvidence hx)
theorem finiteNormalRoundTowardNegative_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.finiteNormalRoundTowardNegative x hx ≤ x :=
  sourceRoundTowardNegativeEvidence_le
    (fmt.finiteNormalRoundTowardNegative_sourceRoundTowardNegativeEvidence hx)
/-- Source-style finite-normal selector for rounding toward positive infinity. -/
noncomputable def finiteNormalRoundTowardPositive
    (fmt : FloatingPointFormat) (x : ℝ) (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose (fmt.exists_sourceRoundTowardPositiveEvidence_finiteNormalRange hx)
theorem finiteNormalRoundTowardPositive_sourceRoundTowardPositiveEvidence
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundTowardPositiveEvidence x
      (fmt.finiteNormalRoundTowardPositive x hx) :=
  Classical.choose_spec
    (fmt.exists_sourceRoundTowardPositiveEvidence_finiteNormalRange hx)
theorem finiteNormalRoundTowardPositive_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.unboundedNormalizedSystem (fmt.finiteNormalRoundTowardPositive x hx) :=
  fmt.sourceRoundTowardPositiveEvidence_unboundedNormalizedSystem
    (fmt.finiteNormalRoundTowardPositive_sourceRoundTowardPositiveEvidence hx)
theorem le_finiteNormalRoundTowardPositive
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    x ≤ fmt.finiteNormalRoundTowardPositive x hx :=
  sourceRoundTowardPositiveEvidence_le
    (fmt.finiteNormalRoundTowardPositive_sourceRoundTowardPositiveEvidence hx)
/-- Source-style finite-normal selector for rounding toward zero. -/
noncomputable def finiteNormalRoundTowardZero
    (fmt : FloatingPointFormat) (x : ℝ) (hx : fmt.finiteNormalRange x) : ℝ :=
  Classical.choose (fmt.exists_sourceRoundTowardZeroEvidence_finiteNormalRange hx)
theorem finiteNormalRoundTowardZero_sourceRoundTowardZeroEvidence
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundTowardZeroEvidence x
      (fmt.finiteNormalRoundTowardZero x hx) :=
  Classical.choose_spec
    (fmt.exists_sourceRoundTowardZeroEvidence_finiteNormalRange hx)
theorem finiteNormalRoundTowardZero_unboundedNormalizedSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.unboundedNormalizedSystem (fmt.finiteNormalRoundTowardZero x hx) :=
  fmt.sourceRoundTowardZeroEvidence_unboundedNormalizedSystem
    (fmt.finiteNormalRoundTowardZero_sourceRoundTowardZeroEvidence hx)
theorem finiteNormalRoundTowardZero_abs_le_abs
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    |fmt.finiteNormalRoundTowardZero x hx| ≤ |x| :=
  sourceRoundTowardZeroEvidence_abs_le_abs
    (fmt.finiteNormalRoundTowardZero_sourceRoundTowardZeroEvidence hx)
/-- Values that are neither in the source-facing underflow range nor in the
source-facing overflow range are exactly in the finite normal magnitude band. -/
theorem finiteNormalRange_of_not_finiteUnderflowRange_of_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : ¬ fmt.finiteUnderflowRange x)
    (hover : ¬ fmt.finiteOverflowRange x) :
    fmt.finiteNormalRange x := by
  have hmin : fmt.minNormalMagnitude ≤ |x| := by
    rw [finiteUnderflowRange] at hunder
    exact le_of_not_gt hunder
  have hmax : |x| ≤ fmt.maxFiniteMagnitude := by
    rw [finiteOverflowRange] at hover
    exact le_of_not_gt hover
  exact ⟨hmin, hmax⟩
/-- Total source-facing finite selector for rounding toward negative infinity.
Underflow uses the subnormal directed lattice, finite-normal inputs use the
source-level adjacent-bracket selector, and overflow uses finite saturation.
This is still a finite-value selector; IEEE infinities and flags are modeled by
the separate IEEE result layer. -/
noncomputable def finiteRoundTowardNegative
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  by
    classical
    exact
      if hunder : fmt.finiteUnderflowRange x then
        fmt.finiteUnderflowRoundTowardNegative x
      else if hover : fmt.finiteOverflowRange x then
        fmt.finiteOverflowSaturation x
      else
        fmt.finiteNormalRoundTowardNegative x
          (fmt.finiteNormalRange_of_not_finiteUnderflowRange_of_not_finiteOverflowRange
            hunder hover)
/-- Total source-facing finite selector for rounding toward positive infinity. -/
noncomputable def finiteRoundTowardPositive
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  by
    classical
    exact
      if hunder : fmt.finiteUnderflowRange x then
        fmt.finiteUnderflowRoundTowardPositive x
      else if hover : fmt.finiteOverflowRange x then
        fmt.finiteOverflowSaturation x
      else
        fmt.finiteNormalRoundTowardPositive x
          (fmt.finiteNormalRange_of_not_finiteUnderflowRange_of_not_finiteOverflowRange
            hunder hover)
/-- Total source-facing finite selector for rounding toward zero. -/
noncomputable def finiteRoundTowardZero
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  by
    classical
    exact
      if hunder : fmt.finiteUnderflowRange x then
        fmt.finiteUnderflowRoundTowardZero x
      else if hover : fmt.finiteOverflowRange x then
        fmt.finiteOverflowSaturation x
      else
        fmt.finiteNormalRoundTowardZero x
          (fmt.finiteNormalRange_of_not_finiteUnderflowRange_of_not_finiteOverflowRange
            hunder hover)
theorem finiteRoundTowardNegative_eq_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteRoundTowardNegative x =
      fmt.finiteUnderflowRoundTowardNegative x := by
  classical
  unfold finiteRoundTowardNegative
  simp [hunder]
theorem finiteRoundTowardPositive_eq_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteRoundTowardPositive x =
      fmt.finiteUnderflowRoundTowardPositive x := by
  classical
  unfold finiteRoundTowardPositive
  simp [hunder]
theorem finiteRoundTowardZero_eq_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteRoundTowardZero x =
      fmt.finiteUnderflowRoundTowardZero x := by
  classical
  unfold finiteRoundTowardZero
  simp [hunder]
theorem finiteRoundTowardNegative_eq_overflow_of_not_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : ¬ fmt.finiteUnderflowRange x)
    (hover : fmt.finiteOverflowRange x) :
    fmt.finiteRoundTowardNegative x = fmt.finiteOverflowSaturation x := by
  classical
  unfold finiteRoundTowardNegative
  simp [hunder, hover]
theorem finiteRoundTowardPositive_eq_overflow_of_not_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : ¬ fmt.finiteUnderflowRange x)
    (hover : fmt.finiteOverflowRange x) :
    fmt.finiteRoundTowardPositive x = fmt.finiteOverflowSaturation x := by
  classical
  unfold finiteRoundTowardPositive
  simp [hunder, hover]
theorem finiteRoundTowardZero_eq_overflow_of_not_underflow
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : ¬ fmt.finiteUnderflowRange x)
    (hover : fmt.finiteOverflowRange x) :
    fmt.finiteRoundTowardZero x = fmt.finiteOverflowSaturation x := by
  classical
  unfold finiteRoundTowardZero
  simp [hunder, hover]
theorem finiteRoundTowardNegative_le_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteRoundTowardNegative x ≤ x := by
  rw [fmt.finiteRoundTowardNegative_eq_underflow hunder]
  exact fmt.finiteUnderflowRoundTowardNegative_le hunder
theorem le_finiteRoundTowardPositive_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    x ≤ fmt.finiteRoundTowardPositive x := by
  rw [fmt.finiteRoundTowardPositive_eq_underflow hunder]
  exact fmt.le_finiteUnderflowRoundTowardPositive hunder
theorem finiteRoundTowardZero_abs_le_abs_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    |fmt.finiteRoundTowardZero x| ≤ |x| := by
  rw [fmt.finiteRoundTowardZero_eq_underflow hunder]
  exact fmt.finiteUnderflowRoundTowardZero_abs_le_abs hunder
theorem finiteRoundTowardNegative_le_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.finiteRoundTowardNegative x ≤ x := by
  classical
  unfold finiteRoundTowardNegative
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro h
    exact not_lt_of_ge hx.1 h
  have hover : ¬ fmt.finiteOverflowRange x := by
    intro h
    exact not_lt_of_ge hx.2 h
  simp [hunder, hover]
  exact fmt.finiteNormalRoundTowardNegative_le _
theorem le_finiteRoundTowardPositive_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    x ≤ fmt.finiteRoundTowardPositive x := by
  classical
  unfold finiteRoundTowardPositive
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro h
    exact not_lt_of_ge hx.1 h
  have hover : ¬ fmt.finiteOverflowRange x := by
    intro h
    exact not_lt_of_ge hx.2 h
  simp [hunder, hover]
  exact fmt.le_finiteNormalRoundTowardPositive _
theorem finiteRoundTowardZero_abs_le_abs_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    |fmt.finiteRoundTowardZero x| ≤ |x| := by
  classical
  unfold finiteRoundTowardZero
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro h
    exact not_lt_of_ge hx.1 h
  have hover : ¬ fmt.finiteOverflowRange x := by
    intro h
    exact not_lt_of_ge hx.2 h
  simp [hunder, hover]
  exact fmt.finiteNormalRoundTowardZero_abs_le_abs _
theorem finiteRoundTowardZero_abs_le_abs
    (fmt : FloatingPointFormat) (x : ℝ) :
    |fmt.finiteRoundTowardZero x| ≤ |x| := by
  classical
  unfold finiteRoundTowardZero
  by_cases hunder : fmt.finiteUnderflowRange x
  · simp [hunder]
    exact fmt.finiteUnderflowRoundTowardZero_abs_le_abs hunder
  · simp [hunder]
    by_cases hover : fmt.finiteOverflowRange x
    · simp [hover]
      exact fmt.finiteOverflowSaturation_abs_le_abs_of_finiteOverflowRange
        hover
    · simp [hover]
      exact fmt.finiteNormalRoundTowardZero_abs_le_abs _
/-- Total source-facing finite round-away selector.  Underflow uses the
subnormal-lattice round-away selector, finite normal inputs use the
source-level adjacent-bracket round-away selector, and overflow saturates to
the signed largest finite endpoint.  This is still not an IEEE operation:
exception flags, infinities, NaNs, directed modes, and signed zeros are outside
this model. -/
noncomputable def finiteRoundAway (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  by
    classical
    exact
      if hunder : fmt.finiteUnderflowRange x then
        fmt.finiteUnderflowRoundAway x
      else if hover : fmt.finiteOverflowRange x then
        fmt.finiteOverflowSaturation x
      else
        fmt.finiteNormalRoundAway x (by
          have hmin : fmt.minNormalMagnitude ≤ |x| := by
            rw [finiteUnderflowRange] at hunder
            exact le_of_not_gt hunder
          have hmax : |x| ≤ fmt.maxFiniteMagnitude := by
            rw [finiteOverflowRange] at hover
            exact le_of_not_gt hover
          exact ⟨hmin, hmax⟩)
theorem finiteRoundAway_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.nearestRoundingToFinite x (fmt.finiteRoundAway x) := by
  classical
  unfold finiteRoundAway
  by_cases hunder : fmt.finiteUnderflowRange x
  · simp [hunder]
    exact fmt.finiteUnderflowRoundAway_nearestRoundingToFinite hunder
  · simp [hunder]
    by_cases hover : fmt.finiteOverflowRange x
    · simp [hover]
      exact
        fmt.finiteOverflowSaturation_nearestRoundingToFinite_of_finiteOverflowRange
          hover
    · simp [hover]
      exact fmt.finiteNormalRoundAway_nearestRoundingToFinite _
theorem finiteRoundAway_output_not_finiteOverflowRange
    (fmt : FloatingPointFormat) (x : ℝ) :
    ¬ fmt.finiteOverflowRange (fmt.finiteRoundAway x) :=
  fmt.nearestRoundingToFinite_output_not_finiteOverflowRange
    (fmt.finiteRoundAway_nearestRoundingToFinite x)
theorem finiteRoundAway_output_abs_le_maxFiniteMagnitude
    (fmt : FloatingPointFormat) (x : ℝ) :
    |fmt.finiteRoundAway x| ≤ fmt.maxFiniteMagnitude :=
  fmt.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude
    (fmt.finiteRoundAway_nearestRoundingToFinite x)
theorem finiteRoundAway_sourceRoundAwayEvidence_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundAwayEvidence x (fmt.finiteRoundAway x) := by
  classical
  unfold finiteRoundAway
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro h
    exact not_lt_of_ge hx.1 h
  have hover : ¬ fmt.finiteOverflowRange x := by
    intro h
    exact not_lt_of_ge hx.2 h
  simp [hunder, hover]
  exact fmt.finiteNormalRoundAway_sourceRoundAwayEvidence _
theorem finiteRoundAway_signedRelErrorWitness_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteRoundAway x) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteRoundAway x) x δ := by
  have hround := fmt.finiteRoundAway_nearestRoundingToFinite x
  rcases
    fmt.nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange
      hround hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, hround, hδ, hwit⟩
/-- Total source-facing finite round-to-even selector.  Underflow uses the
subnormal-lattice round-to-even selector, finite normal inputs use the
source-level adjacent-bracket round-to-even selector, and overflow saturates to
the signed largest finite endpoint.  This is still not an IEEE operation:
exception flags, infinities, NaNs, directed modes, and signed zeros are outside
this model. -/
noncomputable def finiteRoundToEven (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  by
    classical
    exact
      if hunder : fmt.finiteUnderflowRange x then
        fmt.finiteUnderflowRoundToEven x
      else if hover : fmt.finiteOverflowRange x then
        fmt.finiteOverflowSaturation x
      else
        fmt.finiteNormalRoundToEven x (by
          have hmin : fmt.minNormalMagnitude ≤ |x| := by
            rw [finiteUnderflowRange] at hunder
            exact le_of_not_gt hunder
          have hmax : |x| ≤ fmt.maxFiniteMagnitude := by
            rw [finiteOverflowRange] at hover
            exact le_of_not_gt hover
          exact ⟨hmin, hmax⟩)
/-- Total source-facing finite selector parameterized by an IEEE rounding mode.
The nearest/even branch uses the nearest-even finite selector, while the
directed branches use the total finite directed selectors.  This remains a
finite real-valued selector; IEEE infinities, NaNs, signed zeros, and exception
flags live in the separate IEEE result layer. -/
noncomputable def finiteRoundToMode
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode) (x : ℝ) : ℝ :=
  match mode with
  | IeeeRoundingMode.nearestEven => fmt.finiteRoundToEven x
  | IeeeRoundingMode.towardZero => fmt.finiteRoundTowardZero x
  | IeeeRoundingMode.towardPositive => fmt.finiteRoundTowardPositive x
  | IeeeRoundingMode.towardNegative => fmt.finiteRoundTowardNegative x
theorem finiteRoundToMode_nearestEven
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteRoundToMode IeeeRoundingMode.nearestEven x =
      fmt.finiteRoundToEven x := rfl
theorem finiteRoundToMode_towardZero
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteRoundToMode IeeeRoundingMode.towardZero x =
      fmt.finiteRoundTowardZero x := rfl
theorem finiteRoundToMode_towardPositive
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteRoundToMode IeeeRoundingMode.towardPositive x =
      fmt.finiteRoundTowardPositive x := rfl
theorem finiteRoundToMode_towardNegative
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteRoundToMode IeeeRoundingMode.towardNegative x =
      fmt.finiteRoundTowardNegative x := rfl
/-- Operation-level finite rounding selector parameterized by an IEEE rounding
mode. -/
noncomputable def finiteRoundToModeOp
    (fmt : FloatingPointFormat) (mode : IeeeRoundingMode)
    (op : BasicOp) (x y : ℝ) : ℝ :=
  fmt.finiteRoundToMode mode (BasicOp.exact op x y)
theorem finiteRoundToEven_nearestRoundingToFinite
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) := by
  classical
  unfold finiteRoundToEven
  by_cases hunder : fmt.finiteUnderflowRange x
  · simp [hunder]
    exact fmt.finiteUnderflowRoundToEven_nearestRoundingToFinite hunder
  · simp [hunder]
    by_cases hover : fmt.finiteOverflowRange x
    · simp [hover]
      exact
        fmt.finiteOverflowSaturation_nearestRoundingToFinite_of_finiteOverflowRange
          hover
    · simp [hover]
      exact fmt.finiteNormalRoundToEven_nearestRoundingToFinite _
/-- The total finite round-to-even selector always returns a finite
representable value. -/
theorem finiteRoundToEven_finiteSystem
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteSystem (fmt.finiteRoundToEven x) :=
  nearestRoundingIn_mem (fmt.finiteRoundToEven_nearestRoundingToFinite x)
theorem finiteRoundToEven_neg_of_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteRoundToEven (-x) = -fmt.finiteRoundToEven x := by
  classical
  have hunder_neg : fmt.finiteUnderflowRange (-x) :=
    (fmt.finiteUnderflowRange_neg_iff x).2 hunder
  unfold finiteRoundToEven
  simp [hunder, hunder_neg, fmt.finiteUnderflowRoundToEven_neg x]
theorem finiteRoundToEven_neg_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hover : fmt.finiteOverflowRange x) :
    fmt.finiteRoundToEven (-x) = -fmt.finiteRoundToEven x := by
  classical
  have hover_neg : fmt.finiteOverflowRange (-x) :=
    (fmt.finiteOverflowRange_neg_iff x).2 hover
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro hunder
    have hle := fmt.minNormalMagnitude_le_maxFiniteMagnitude
    rw [finiteUnderflowRange] at hunder
    rw [finiteOverflowRange] at hover
    linarith
  have hunder_neg : ¬ fmt.finiteUnderflowRange (-x) := by
    intro h
    exact hunder ((fmt.finiteUnderflowRange_neg_iff x).1 h)
  unfold finiteRoundToEven
  simp [hunder, hunder_neg, hover, hover_neg,
    fmt.finiteOverflowSaturation_neg_of_finiteOverflowRange hover]
theorem finiteRoundToEven_neg_of_not_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hnot : ¬ fmt.finiteNormalRange x) :
    fmt.finiteRoundToEven (-x) = -fmt.finiteRoundToEven x := by
  by_cases hunder : fmt.finiteUnderflowRange x
  · exact fmt.finiteRoundToEven_neg_of_finiteUnderflowRange hunder
  · by_cases hover : fmt.finiteOverflowRange x
    · exact fmt.finiteRoundToEven_neg_of_finiteOverflowRange hover
    · have hnormal :=
        fmt.finiteNormalRange_of_not_finiteUnderflowRange_of_not_finiteOverflowRange
          hunder hover
      exact False.elim (hnot hnormal)
theorem finiteRoundToEven_output_not_finiteOverflowRange
    (fmt : FloatingPointFormat) (x : ℝ) :
    ¬ fmt.finiteOverflowRange (fmt.finiteRoundToEven x) :=
  fmt.nearestRoundingToFinite_output_not_finiteOverflowRange
    (fmt.finiteRoundToEven_nearestRoundingToFinite x)
theorem finiteRoundToEven_output_abs_le_maxFiniteMagnitude
    (fmt : FloatingPointFormat) (x : ℝ) :
    |fmt.finiteRoundToEven x| ≤ fmt.maxFiniteMagnitude :=
  fmt.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude
    (fmt.finiteRoundToEven_nearestRoundingToFinite x)
theorem finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) := by
  classical
  unfold finiteRoundToEven
  have hunder : ¬ fmt.finiteUnderflowRange x := by
    intro h
    exact not_lt_of_ge hx.1 h
  have hover : ¬ fmt.finiteOverflowRange x := by
    intro h
    exact not_lt_of_ge hx.2 h
  simp [hunder, hover]
  exact fmt.finiteNormalRoundToEven_sourceRoundToEvenEvidence _
theorem finiteRoundToEven_eq_finiteNormalRoundToEven_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    fmt.finiteRoundToEven x = fmt.finiteNormalRoundToEven x hx :=
  sourceRoundToEvenEvidence_unique
    (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hx)
    (fmt.finiteNormalRoundToEven_sourceRoundToEvenEvidence hx)
theorem finiteRoundToEven_neg_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (hx : fmt.finiteNormalRange x) :
    fmt.finiteRoundToEven (-x) = -fmt.finiteRoundToEven x := by
  have hxneg : fmt.finiteNormalRange (-x) :=
    (fmt.finiteNormalRange_neg_iff x).2 hx
  have hpolicy :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hx
  have hpolicy_neg :=
    fmt.sourceRoundToEvenEvidence_neg hbeta ht hpolicy
  exact
    sourceRoundToEvenEvidence_unique
      (fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
        hxneg)
      hpolicy_neg
theorem finiteRoundToEven_neg
    (fmt : FloatingPointFormat)
    (hbeta : evenMantissa fmt.beta) (ht : 1 < fmt.t)
    (x : ℝ) :
    fmt.finiteRoundToEven (-x) = -fmt.finiteRoundToEven x := by
  by_cases hx : fmt.finiteNormalRange x
  · exact fmt.finiteRoundToEven_neg_of_finiteNormalRange hbeta ht hx
  · exact fmt.finiteRoundToEven_neg_of_not_finiteNormalRange hx
theorem finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteNormalRange x) :
    ∃ δ : ℝ,
      fmt.nearestRoundingToFinite x (fmt.finiteRoundToEven x) ∧
        |δ| < fmt.unitRoundoff ∧
          signedRelErrorWitness (fmt.finiteRoundToEven x) x δ := by
  have hround := fmt.finiteRoundToEven_nearestRoundingToFinite x
  rcases
    fmt.nearestRoundingToFinite_signedRelErrorWitness_lt_of_finiteNormalRange
      hround hx with
    ⟨δ, hδ, hwit⟩
  exact ⟨δ, hround, hδ, hwit⟩
/-- Exact finite representable inputs are fixed by the total finite
round-to-even selector. -/
theorem finiteRoundToEven_eq_self_of_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    fmt.finiteRoundToEven x = x :=
  fmt.nearestRoundingToFinite_eq_self_of_finiteSystem hx
    (fmt.finiteRoundToEven_nearestRoundingToFinite x)
/-- Operation-level finite round-to-even wrapper for Higham's primitive
arithmetic operations.  It rounds the exact real operation with the total
source-facing finite selector.  This is the ordinary finite, non-exceptional
bridge; IEEE special values, exception flags, directed modes, and signed zeros
remain outside this real-valued wrapper. -/
noncomputable def finiteRoundToEvenOp (fmt : FloatingPointFormat)
    (op : BasicOp) (x y : ℝ) : ℝ :=
  fmt.finiteRoundToEven (BasicOp.exact op x y)

end FloatingPointFormat

end

end NumStability
