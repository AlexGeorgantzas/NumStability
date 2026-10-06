-- Analysis/NearInteger.lean
--
-- Exact table-ambiguity algebra for Higham Chapter 1, Problem 1.2.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

namespace NumStability

/-!
# Near-Integer Table Ambiguity

Higham Problem 1.2 gives rounded evaluations of
`y = exp (pi * sqrt 163)` and asks whether the table implies that the last
digit before the decimal point is `4`.

This file formalizes the finite-precision table statement itself.  It proves
that the displayed one-unit-in-the-last-place error bars are consistent both
with the nearby integer ending in `4` and with a value just below that integer,
whose integer part ends in `3`.  Thus the table data alone do not force the
last digit to be `4`.

No transcendental interval for `exp (pi * sqrt 163)` is claimed here.
-/

/-- The nearby integer shown by the Problem 1.2 table. -/
def problem12NearInteger : ℕ :=
  262537412640768744

/-- Candidate exactly at the nearby integer. -/
noncomputable def problem12CandidateInteger : ℝ :=
  problem12NearInteger

/-- Candidate just below the nearby integer, still within the last displayed
one-ulp interval. -/
noncomputable def problem12CandidateBelow : ℝ :=
  (problem12NearInteger : ℝ) - 1 / (2 * (10 : ℝ) ^ 12)

/-- Problem 1.2's "within one unit in the least significant digit" predicate. -/
def problem12WithinOneUnit (approx unit y : ℝ) : Prop :=
  |y - approx| ≤ unit

noncomputable def problem12Table10 : ℝ := 262537412600000000
noncomputable def problem12Table15 : ℝ := 262537412640769000
noncomputable def problem12Table20 : ℝ := problem12NearInteger
noncomputable def problem12Table25 : ℝ := problem12NearInteger
noncomputable def problem12Table30 : ℝ :=
  (problem12NearInteger : ℝ) - 1 / ((10 : ℝ) ^ 12)

noncomputable def problem12Unit10 : ℝ := (10 : ℝ) ^ 8
noncomputable def problem12Unit15 : ℝ := (10 : ℝ) ^ 3
noncomputable def problem12Unit20 : ℝ := 1 / ((10 : ℝ) ^ 2)
noncomputable def problem12Unit25 : ℝ := 1 / ((10 : ℝ) ^ 7)
noncomputable def problem12Unit30 : ℝ := 1 / ((10 : ℝ) ^ 12)

/-- All five displayed Problem 1.2 rows are within their stated one-ulp
least-significant-digit error bars. -/
def problem12TableConsistent (y : ℝ) : Prop :=
  problem12WithinOneUnit problem12Table10 problem12Unit10 y ∧
  problem12WithinOneUnit problem12Table15 problem12Unit15 y ∧
  problem12WithinOneUnit problem12Table20 problem12Unit20 y ∧
  problem12WithinOneUnit problem12Table25 problem12Unit25 y ∧
  problem12WithinOneUnit problem12Table30 problem12Unit30 y

/-- The table is consistent with a value just below the nearby integer. -/
theorem problem_1_2_candidateBelow_consistent :
    problem12TableConsistent problem12CandidateBelow := by
  norm_num [problem12TableConsistent, problem12WithinOneUnit,
    problem12CandidateBelow, problem12Table10, problem12Table15,
    problem12Table20, problem12Table25, problem12Table30,
    problem12Unit10, problem12Unit15, problem12Unit20,
    problem12Unit25, problem12Unit30, problem12NearInteger]

/-- The just-below candidate has integer part strictly below the nearby integer. -/
theorem problem_1_2_candidateBelow_between :
    ((problem12NearInteger - 1 : ℕ) : ℝ) < problem12CandidateBelow ∧
      problem12CandidateBelow < (problem12NearInteger : ℝ) := by
  norm_num [problem12CandidateBelow, problem12NearInteger]

/-- The integer part below the nearby integer ends in digit `3`. -/
theorem problem_1_2_candidateBelow_integer_part_last_digit_three :
    (problem12NearInteger - 1) % 10 = 3 := by
  norm_num [problem12NearInteger]

/-- The table is also consistent with the nearby integer itself. -/
theorem problem_1_2_candidateInteger_consistent :
    problem12TableConsistent problem12CandidateInteger := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [problem12WithinOneUnit, problem12CandidateInteger,
      problem12Table10, problem12Table15, problem12Table20,
      problem12Table25, problem12Table30, problem12Unit10,
      problem12Unit15, problem12Unit20, problem12Unit25,
      problem12Unit30, problem12NearInteger] <;>
    norm_num

/-- The nearby integer itself ends in digit `4`. -/
theorem problem_1_2_candidateInteger_last_digit_four :
    problem12NearInteger % 10 = 4 := by
  norm_num [problem12NearInteger]

/-- Formal answer to Problem 1.2: the displayed table data do not force the
last digit before the decimal point to be `4`; both a `3`-ending integer part
and a `4`-ending integer are consistent with the stated error bars. -/
theorem problem_1_2_table_does_not_force_last_digit_four :
    problem12TableConsistent problem12CandidateBelow ∧
      ((problem12NearInteger - 1 : ℕ) : ℝ) < problem12CandidateBelow ∧
      problem12CandidateBelow < (problem12NearInteger : ℝ) ∧
      (problem12NearInteger - 1) % 10 = 3 ∧
      problem12TableConsistent problem12CandidateInteger ∧
      problem12NearInteger % 10 = 4 := by
  exact ⟨problem_1_2_candidateBelow_consistent,
    problem_1_2_candidateBelow_between.1,
    problem_1_2_candidateBelow_between.2,
    problem_1_2_candidateBelow_integer_part_last_digit_three,
    problem_1_2_candidateInteger_consistent,
    problem_1_2_candidateInteger_last_digit_four⟩

end NumStability
