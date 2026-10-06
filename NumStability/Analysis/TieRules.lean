-- Analysis/TieRules.lean
--
-- Local tie-rule examples for Higham Chapter 2, §2.9.

import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

namespace FloatingPointFormat

/-!
# Tie Rules

Higham Chapter 2, §2.9 contrasts round-to-even and round-to-odd on the decimal
chain `2.445`.  The core finite-format library already defines the local
round-to-even selector on an adjacent bracket.  This file adds the analogous
local round-to-odd selector and proves the exact rational decimal sequence from
the text.
-/

/-- Local round-to-odd selector for an ordered adjacent bracket.  It agrees
with nearest rounding away from exact ties, and in a tie chooses the endpoint
whose last supplied digit has odd parity. -/
def nearestAdjacentRoundToOdd (x a b : ℝ) (leftMantissa : ℕ) : ℝ :=
  if |x - a| < |x - b| then a
  else if |x - b| < |x - a| then b
  else if evenMantissa leftMantissa then b else a

theorem nearestAdjacentRoundToOdd_eq_left_of_left_closer
    {x a b : ℝ} {leftMantissa : ℕ}
    (hleftCloser : |x - a| < |x - b|) :
    nearestAdjacentRoundToOdd x a b leftMantissa = a := by
  unfold nearestAdjacentRoundToOdd
  simp [hleftCloser]

theorem nearestAdjacentRoundToOdd_eq_right_of_right_closer
    {x a b : ℝ} {leftMantissa : ℕ}
    (hrightCloser : |x - b| < |x - a|) :
    nearestAdjacentRoundToOdd x a b leftMantissa = b := by
  unfold nearestAdjacentRoundToOdd
  have hnot_left : ¬ |x - a| < |x - b| := by
    exact not_lt_of_ge (le_of_lt hrightCloser)
  simp [hnot_left, hrightCloser]

theorem nearestAdjacentRoundToOdd_eq_right_of_tie_even
    {x a b : ℝ} {leftMantissa : ℕ}
    (htie : |x - a| = |x - b|)
    (heven : evenMantissa leftMantissa) :
    nearestAdjacentRoundToOdd x a b leftMantissa = b := by
  unfold nearestAdjacentRoundToOdd
  have hnot_left : ¬ |x - a| < |x - b| := by
    rw [htie]
    exact lt_irrefl _
  have hnot_right : ¬ |x - b| < |x - a| := by
    rw [htie]
    exact lt_irrefl _
  simp [hnot_left, hnot_right, heven]

theorem nearestAdjacentRoundToOdd_eq_left_of_tie_odd
    {x a b : ℝ} {leftMantissa : ℕ}
    (htie : |x - a| = |x - b|)
    (hodd : ¬ evenMantissa leftMantissa) :
    nearestAdjacentRoundToOdd x a b leftMantissa = a := by
  unfold nearestAdjacentRoundToOdd
  have hnot_left : ¬ |x - a| < |x - b| := by
    rw [htie]
    exact lt_irrefl _
  have hnot_right : ¬ |x - b| < |x - a| := by
    rw [htie]
    exact lt_irrefl _
  simp [hnot_left, hnot_right, hodd]

/-- Higham's decimal round-to-even first step: `2.445` rounds to `2.44` at
two decimal places. -/
theorem decimal_2445_roundToEven_two_places :
    nearestAdjacentRoundToEven ((489 : ℝ) / 200) ((61 : ℝ) / 25)
        ((49 : ℝ) / 20) 244 =
      (61 : ℝ) / 25 := by
  apply nearestAdjacentRoundToEven_eq_left_of_tie_even
  · norm_num
  · norm_num [evenMantissa]

/-- Higham's decimal round-to-even second step: `2.44` rounds to `2.4` at one
decimal place. -/
theorem decimal_244_roundToEven_one_place :
    nearestAdjacentRoundToEven ((61 : ℝ) / 25) ((12 : ℝ) / 5)
        ((5 : ℝ) / 2) 24 =
      (12 : ℝ) / 5 := by
  apply nearestAdjacentRoundToEven_eq_left_of_left_closer
  norm_num

/-- Higham's displayed round-to-even chain `2.445, 2.44, 2.4`. -/
theorem decimal_2445_roundToEven_chain :
    nearestAdjacentRoundToEven
        (nearestAdjacentRoundToEven ((489 : ℝ) / 200) ((61 : ℝ) / 25)
          ((49 : ℝ) / 20) 244)
        ((12 : ℝ) / 5) ((5 : ℝ) / 2) 24 =
      (12 : ℝ) / 5 := by
  rw [decimal_2445_roundToEven_two_places]
  exact decimal_244_roundToEven_one_place

/-- Higham's decimal round-to-odd first step: `2.445` rounds to `2.45` at two
decimal places. -/
theorem decimal_2445_roundToOdd_two_places :
    nearestAdjacentRoundToOdd ((489 : ℝ) / 200) ((61 : ℝ) / 25)
        ((49 : ℝ) / 20) 244 =
      (49 : ℝ) / 20 := by
  apply nearestAdjacentRoundToOdd_eq_right_of_tie_even
  · norm_num
  · norm_num [evenMantissa]

/-- Higham's decimal round-to-odd second step: `2.45` rounds to `2.5` at one
decimal place. -/
theorem decimal_245_roundToOdd_one_place :
    nearestAdjacentRoundToOdd ((49 : ℝ) / 20) ((12 : ℝ) / 5)
        ((5 : ℝ) / 2) 24 =
      (5 : ℝ) / 2 := by
  apply nearestAdjacentRoundToOdd_eq_right_of_tie_even
  · norm_num
  · norm_num [evenMantissa]

/-- Higham's displayed round-to-odd chain `2.445, 2.45, 2.5`. -/
theorem decimal_2445_roundToOdd_chain :
    nearestAdjacentRoundToOdd
        (nearestAdjacentRoundToOdd ((489 : ℝ) / 200) ((61 : ℝ) / 25)
          ((49 : ℝ) / 20) 244)
        ((12 : ℝ) / 5) ((5 : ℝ) / 2) 24 =
      (5 : ℝ) / 2 := by
  rw [decimal_2445_roundToOdd_two_places]
  exact decimal_245_roundToOdd_one_place

/-- One-decimal local round-to-even first half of a Reiser--Knuth-shaped
add/sub step: `1 + 0.05` rounds back to `1.0`. -/
theorem decimal_105_roundToEven_one_place :
    nearestAdjacentRoundToEven ((21 : ℝ) / 20) (1 : ℝ)
        ((11 : ℝ) / 10) 10 =
      (1 : ℝ) := by
  apply nearestAdjacentRoundToEven_eq_left_of_tie_even
  · norm_num
  · norm_num [evenMantissa]

/-- One-decimal local round-to-even second half of a Reiser--Knuth-shaped
add/sub step: `1.0 - 0.05` rounds back to `1.0`. -/
theorem decimal_095_roundToEven_one_place :
    nearestAdjacentRoundToEven ((19 : ℝ) / 20) ((9 : ℝ) / 10)
        (1 : ℝ) 9 =
      (1 : ℝ) := by
  apply nearestAdjacentRoundToEven_eq_right_of_tie_odd
  · norm_num
  · norm_num [evenMantissa]

/-- The local one-decimal round-to-even computed value of `(1 + 0.05) - 0.05`
is stable at `1.0`. -/
def decimalOnePlaceRoundToEvenAddSubFromOne : ℝ :=
  nearestAdjacentRoundToEven
    (nearestAdjacentRoundToEven ((1 : ℝ) + (1 / 20 : ℝ)) (1 : ℝ)
        ((11 : ℝ) / 10) 10 - (1 / 20 : ℝ))
    ((9 : ℝ) / 10) (1 : ℝ) 9

theorem decimalOnePlaceRoundToEvenAddSubFromOne_eq_one :
    decimalOnePlaceRoundToEvenAddSubFromOne = (1 : ℝ) := by
  unfold decimalOnePlaceRoundToEvenAddSubFromOne
  rw [show ((1 : ℝ) + (1 / 20 : ℝ)) = (21 : ℝ) / 20 by norm_num]
  rw [decimal_105_roundToEven_one_place]
  rw [show ((1 : ℝ) - (1 / 20 : ℝ)) = (19 : ℝ) / 20 by norm_num]
  exact decimal_095_roundToEven_one_place

/-- A concrete local Reiser--Knuth-shaped stability instance for round-to-even:
after one rounded add/sub step at one decimal place, applying the same rounded
add/sub step again gives the same result. -/
theorem decimalOnePlaceRoundToEven_reiserKnuth_stable_from_one :
    nearestAdjacentRoundToEven
        (nearestAdjacentRoundToEven
            (decimalOnePlaceRoundToEvenAddSubFromOne + (1 / 20 : ℝ))
            (1 : ℝ) ((11 : ℝ) / 10) 10 -
          (1 / 20 : ℝ))
        ((9 : ℝ) / 10) (1 : ℝ) 9 =
      decimalOnePlaceRoundToEvenAddSubFromOne := by
  rw [decimalOnePlaceRoundToEvenAddSubFromOne_eq_one]
  exact decimalOnePlaceRoundToEvenAddSubFromOne_eq_one

/-- One-decimal local round-to-odd first half of a Reiser--Knuth-shaped add/sub
step: `1 + 0.05` rounds to `1.1`. -/
theorem decimal_105_roundToOdd_one_place :
    nearestAdjacentRoundToOdd ((21 : ℝ) / 20) (1 : ℝ)
        ((11 : ℝ) / 10) 10 =
      (11 : ℝ) / 10 := by
  apply nearestAdjacentRoundToOdd_eq_right_of_tie_even
  · norm_num
  · norm_num [evenMantissa]

/-- One-decimal local round-to-odd tie: `1.15` rounds back to `1.1`, since the
left mantissa is odd. -/
theorem decimal_115_roundToOdd_one_place :
    nearestAdjacentRoundToOdd ((23 : ℝ) / 20) ((11 : ℝ) / 10)
        ((6 : ℝ) / 5) 11 =
      (11 : ℝ) / 10 := by
  apply nearestAdjacentRoundToOdd_eq_left_of_tie_odd
  · norm_num
  · norm_num [evenMantissa]

/-- The local one-decimal round-to-odd computed value of `(1 + 0.05) - 0.05`
is the first rounded fixed point `1.1`. -/
def decimalOnePlaceRoundToOddAddSubFromOne : ℝ :=
  nearestAdjacentRoundToOdd
    (nearestAdjacentRoundToOdd ((1 : ℝ) + (1 / 20 : ℝ)) (1 : ℝ)
        ((11 : ℝ) / 10) 10 - (1 / 20 : ℝ))
    (1 : ℝ) ((11 : ℝ) / 10) 10

theorem decimalOnePlaceRoundToOddAddSubFromOne_eq_eleven_tenths :
    decimalOnePlaceRoundToOddAddSubFromOne = (11 : ℝ) / 10 := by
  unfold decimalOnePlaceRoundToOddAddSubFromOne
  rw [show ((1 : ℝ) + (1 / 20 : ℝ)) = (21 : ℝ) / 20 by norm_num]
  rw [decimal_105_roundToOdd_one_place]
  rw [show (((11 : ℝ) / 10) - (1 / 20 : ℝ)) = (21 : ℝ) / 20 by norm_num]
  exact decimal_105_roundToOdd_one_place

/-- A concrete local Reiser--Knuth-shaped stability instance for round-to-odd:
the second one-decimal rounded add/sub step remains at the first rounded
value `1.1`. -/
theorem decimalOnePlaceRoundToOdd_reiserKnuth_stable_after_first_step :
    nearestAdjacentRoundToOdd
        (nearestAdjacentRoundToOdd
            (decimalOnePlaceRoundToOddAddSubFromOne + (1 / 20 : ℝ))
            ((11 : ℝ) / 10) ((6 : ℝ) / 5) 11 -
          (1 / 20 : ℝ))
        (1 : ℝ) ((11 : ℝ) / 10) 10 =
      decimalOnePlaceRoundToOddAddSubFromOne := by
  rw [decimalOnePlaceRoundToOddAddSubFromOne_eq_eleven_tenths]
  rw [show (((11 : ℝ) / 10) + (1 / 20 : ℝ)) = (23 : ℝ) / 20 by norm_num]
  rw [decimal_115_roundToOdd_one_place]
  rw [show (((11 : ℝ) / 10) - (1 / 20 : ℝ)) = (21 : ℝ) / 20 by norm_num]
  exact decimal_105_roundToOdd_one_place

/-- One-decimal local round-away first tie: `1.05` rounds away from zero to
`1.1`. -/
theorem decimal_105_roundAway_one_place :
    nearestAdjacentRoundAway ((21 : ℝ) / 20) (1 : ℝ)
        ((11 : ℝ) / 10) =
      (11 : ℝ) / 10 := by
  unfold nearestAdjacentRoundAway
  norm_num

/-- One-decimal local round-away next tie: `1.15` rounds away from zero to
`1.2`. -/
theorem decimal_115_roundAway_one_place :
    nearestAdjacentRoundAway ((23 : ℝ) / 20) ((11 : ℝ) / 10)
        ((6 : ℝ) / 5) =
      (6 : ℝ) / 5 := by
  unfold nearestAdjacentRoundAway
  norm_num

/-- The first local one-decimal round-away add/sub step moves from `1.0` to
`1.1`. -/
def decimalOnePlaceRoundAwayAddSubFromOne : ℝ :=
  nearestAdjacentRoundAway
    (nearestAdjacentRoundAway ((1 : ℝ) + (1 / 20 : ℝ)) (1 : ℝ)
        ((11 : ℝ) / 10) - (1 / 20 : ℝ))
    (1 : ℝ) ((11 : ℝ) / 10)

theorem decimalOnePlaceRoundAwayAddSubFromOne_eq_eleven_tenths :
    decimalOnePlaceRoundAwayAddSubFromOne = (11 : ℝ) / 10 := by
  unfold decimalOnePlaceRoundAwayAddSubFromOne
  rw [show ((1 : ℝ) + (1 / 20 : ℝ)) = (21 : ℝ) / 20 by norm_num]
  rw [decimal_105_roundAway_one_place]
  rw [show (((11 : ℝ) / 10) - (1 / 20 : ℝ)) = (21 : ℝ) / 20 by norm_num]
  exact decimal_105_roundAway_one_place

/-- The second local one-decimal round-away add/sub step moves from `1.1` to
`1.2`. -/
def decimalOnePlaceRoundAwayAddSubFromElevenTenths : ℝ :=
  nearestAdjacentRoundAway
    (nearestAdjacentRoundAway (((11 : ℝ) / 10) + (1 / 20 : ℝ))
        ((11 : ℝ) / 10) ((6 : ℝ) / 5) - (1 / 20 : ℝ))
    ((11 : ℝ) / 10) ((6 : ℝ) / 5)

theorem decimalOnePlaceRoundAwayAddSubFromElevenTenths_eq_six_fifths :
    decimalOnePlaceRoundAwayAddSubFromElevenTenths = (6 : ℝ) / 5 := by
  unfold decimalOnePlaceRoundAwayAddSubFromElevenTenths
  rw [show (((11 : ℝ) / 10) + (1 / 20 : ℝ)) = (23 : ℝ) / 20 by norm_num]
  rw [decimal_115_roundAway_one_place]
  rw [show (((6 : ℝ) / 5) - (1 / 20 : ℝ)) = (23 : ℝ) / 20 by norm_num]
  exact decimal_115_roundAway_one_place

/-- A concrete local drift trace for the non-Reiser--Knuth round-away policy:
two repeated add/sub steps with the same `0.05` strictly increase the rounded
one-decimal value from `1.1` to `1.2`. -/
theorem decimalOnePlaceRoundAway_drift_first_two_steps :
    decimalOnePlaceRoundAwayAddSubFromOne <
      decimalOnePlaceRoundAwayAddSubFromElevenTenths := by
  rw [decimalOnePlaceRoundAwayAddSubFromOne_eq_eleven_tenths,
    decimalOnePlaceRoundAwayAddSubFromElevenTenths_eq_six_fifths]
  norm_num

end FloatingPointFormat

end

end NumStability
