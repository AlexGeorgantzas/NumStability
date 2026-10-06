-- NumStability/Source/Higham/Chapter04/Problem02/WilkinsonAttainability/IeeeDoubleTrace/Results.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Algorithms.WilkinsonAttainability`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Tactic
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Source.Higham.Chapter02.Problem10.DivisionRoundTrip.ExhaustiveBinary64.Results
import NumStability.Source.Higham.Chapter04.Problem02.WilkinsonAttainability.Basic

/-!
# Results

Relocated from `NumStability.Algorithms.WilkinsonAttainability` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# WilkinsonAttainability (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.WilkinsonAttainability`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

namespace NumStability

private theorem finiteRoundToEvenListSum_replicate_eq_fin_foldl
    {α β : Type*} (f : β → α → β) (x : α) :
    ∀ (n : ℕ) (start : β),
      (List.replicate n x).foldl f start =
        Fin.foldl n (fun acc _ => f acc x) start
  | 0, start => by
      simp
  | n + 1, start => by
      rw [List.replicate_succ, List.foldl_cons, Fin.foldl_succ]
      exact finiteRoundToEvenListSum_replicate_eq_fin_foldl f x n (f start x)

private theorem finiteRoundToEven_eq_right_of_pos_same_exp_tie_odd
    {fmt : FloatingPointFormat} {x a b : ℝ} {leftMantissa : ℕ} {e : ℤ}
    (hxnormal : fmt.finiteNormalRange x)
    (hleftMantissa : fmt.normalizedMantissa leftMantissa)
    (hrightMantissa : fmt.normalizedMantissa (leftMantissa + 1))
    (hleft : a = fmt.normalizedValue false leftMantissa e)
    (hright : b = fmt.normalizedValue false (leftMantissa + 1) e)
    (hstrict : a < x ∧ x < b)
    (htie : |x - a| = |x - b|)
    (hodd : ¬ FloatingPointFormat.evenMantissa leftMantissa) :
    fmt.finiteRoundToEven x = b := by
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange hxnormal
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, leftMantissa, e, hleftMantissa, hrightMantissa, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  exact
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hleftMantissa hleft htie hodd

private theorem wilkinsonProblem42_ieeeDouble_sameBinade_right_mantissa
    {j N : ℕ} (hj : j ≤ 51) (hlo : 2 ^ j < N)
    (hhi : N < 2 ^ (j + 1)) :
    FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
      (N * 2 ^ (52 - j)) := by
  constructor
  · change 2 ^ 52 ≤ N * 2 ^ (52 - j)
    have hleN : 2 ^ j ≤ N := Nat.le_of_lt hlo
    have hprod : 2 ^ j * 2 ^ (52 - j) ≤ N * 2 ^ (52 - j) :=
      Nat.mul_le_mul_right _ hleN
    have hpoweq : 2 ^ j * 2 ^ (52 - j) = 2 ^ 52 := by
      rw [← pow_add]
      congr 1
      omega
    simpa [hpoweq] using hprod
  · change N * 2 ^ (52 - j) < 2 ^ 53
    have hprod : N * 2 ^ (52 - j) < 2 ^ (j + 1) * 2 ^ (52 - j) :=
      Nat.mul_lt_mul_of_pos_right hhi (pow_pos (by norm_num) _)
    have hpoweq : 2 ^ (j + 1) * 2 ^ (52 - j) = 2 ^ 53 := by
      rw [← pow_add]
      congr 1
      omega
    simpa [hpoweq] using hprod

private theorem wilkinsonProblem42_ieeeDouble_sameBinade_left_mantissa
    {j N : ℕ} (hj : j ≤ 51) (hlo : 2 ^ j < N)
    (hhi : N < 2 ^ (j + 1)) :
    FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
      (N * 2 ^ (52 - j) - 1) := by
  constructor
  · change 2 ^ 52 ≤ N * 2 ^ (52 - j) - 1
    have hN_ge_succ : 2 ^ j + 1 ≤ N := Nat.succ_le_of_lt hlo
    have hprod : (2 ^ j + 1) * 2 ^ (52 - j) ≤ N * 2 ^ (52 - j) :=
      Nat.mul_le_mul_right _ hN_ge_succ
    have hpoweq : 2 ^ j * 2 ^ (52 - j) = 2 ^ 52 := by
      rw [← pow_add]
      congr 1
      omega
    have hPone : 1 ≤ 2 ^ (52 - j) :=
      Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) (52 - j))
    have hsum_ge : 2 ^ 52 + 1 ≤ (2 ^ j + 1) * 2 ^ (52 - j) := by
      rw [add_mul, one_mul, hpoweq]
      exact Nat.add_le_add_left hPone (2 ^ 52)
    have hM_ge : 2 ^ 52 + 1 ≤ N * 2 ^ (52 - j) :=
      le_trans hsum_ge hprod
    omega
  · change N * 2 ^ (52 - j) - 1 < 2 ^ 53
    have hprod : N * 2 ^ (52 - j) < 2 ^ (j + 1) * 2 ^ (52 - j) :=
      Nat.mul_lt_mul_of_pos_right hhi (pow_pos (by norm_num) _)
    have hpoweq : 2 ^ (j + 1) * 2 ^ (52 - j) = 2 ^ 53 := by
      rw [← pow_add]
      congr 1
      omega
    have hMlt : N * 2 ^ (52 - j) < 2 ^ 53 := by
      simpa [hpoweq] using hprod
    omega

private theorem wilkinsonProblem42_ieeeDouble_sameBinade_left_mantissa_odd
    {j N : ℕ} (hj : j ≤ 51) (hlo : 2 ^ j < N) :
    ¬ FloatingPointFormat.evenMantissa (N * 2 ^ (52 - j) - 1) := by
  have hevenRight :
      FloatingPointFormat.evenMantissa (N * 2 ^ (52 - j)) := by
    have hpos : 0 < 52 - j := by omega
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨d, hd⟩
    unfold FloatingPointFormat.evenMantissa
    rw [hd, pow_succ]
    rw [show N * (2 ^ d * 2) = 2 * (N * 2 ^ d) by ring]
    exact Nat.mul_mod_right 2 (N * 2 ^ d)
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hlo
  have hMpos : 0 < N * 2 ^ (52 - j) :=
    Nat.mul_pos hNpos (pow_pos (by norm_num : 0 < 2) _)
  have hsucc : N * 2 ^ (52 - j) - 1 + 1 = N * 2 ^ (52 - j) := by
    omega
  rw [← hsucc] at hevenRight
  exact
    (FloatingPointFormat.evenMantissa_succ_iff_not_evenMantissa
      (N * 2 ^ (52 - j) - 1)).mp hevenRight

private theorem wilkinsonProblem42_ieeeDouble_sameBinade_right_value
    {j N : ℕ} (hj : j ≤ 51) :
    FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
        (N * 2 ^ (52 - j)) (((j + 1 : ℕ) : ℤ)) =
      (N : ℝ) := by
  simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR]
  rw [← zpow_natCast]
  calc
    (N : ℝ) * (2 : ℝ) ^ ((52 - j : ℕ) : ℤ) *
        (2 : ℝ) ^ (((j + 1 : ℕ) : ℤ) - 53) =
      (N : ℝ) * ((2 : ℝ) ^ ((52 - j : ℕ) : ℤ) *
        (2 : ℝ) ^ (((j + 1 : ℕ) : ℤ) - 53)) := by ring
    _ = (N : ℝ) *
        (2 : ℝ) ^ (((52 - j : ℕ) : ℤ) +
          (((j + 1 : ℕ) : ℤ) - 53)) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = (N : ℝ) := by
      have hexp :
          ((52 - j : ℕ) : ℤ) + (((j + 1 : ℕ) : ℤ) - 53) = 0 := by
        omega
      rw [hexp]
      ring

private theorem wilkinsonProblem42_ieeeDouble_sameBinade_left_value
    {j N : ℕ} (hj : j ≤ 51) (hlo : 2 ^ j < N) :
    FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
        (N * 2 ^ (52 - j) - 1) (((j + 1 : ℕ) : ℤ)) =
      (N : ℝ) - (2 : ℝ) ^ (((j + 1 : ℕ) : ℤ) - 53) := by
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hlo
  have hMone : 1 ≤ N * 2 ^ (52 - j) := by
    exact Nat.succ_le_of_lt (Nat.mul_pos hNpos (pow_pos (by norm_num) _))
  simp [FloatingPointFormat.normalizedValue, FloatingPointFormat.ieeeDoubleFormat,
    FloatingPointFormat.signValue, FloatingPointFormat.betaR]
  rw [Nat.cast_sub hMone]
  rw [Nat.cast_one]
  calc
    (((N * 2 ^ (52 - j) : ℕ) : ℝ) - 1) *
        (2 : ℝ) ^ (((j + 1 : ℕ) : ℤ) - 53) =
      ((N * 2 ^ (52 - j) : ℕ) : ℝ) *
          (2 : ℝ) ^ (((j + 1 : ℕ) : ℤ) - 53) -
        (2 : ℝ) ^ (((j + 1 : ℕ) : ℤ) - 53) := by ring
    _ = (N : ℝ) - (2 : ℝ) ^ (((j + 1 : ℕ) : ℤ) - 53) := by
      have hright_prod :
          ((N * 2 ^ (52 - j) : ℕ) : ℝ) *
              (2 : ℝ) ^ (((j + 1 : ℕ) : ℤ) - 53) =
            (N : ℝ) := by
        simpa [FloatingPointFormat.normalizedValue,
          FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.signValue,
          FloatingPointFormat.betaR] using
            (wilkinsonProblem42_ieeeDouble_sameBinade_right_value
              (j := j) (N := N) hj)
      rw [hright_prod]

private theorem wilkinsonProblem42_ieeeDouble_sameBinade_midpoint_finiteNormalRange
    {j N : ℕ} (hj : j ≤ 51) (hlo : 2 ^ j < N)
    (hhi : N < 2 ^ (j + 1)) :
    FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange
      ((N : ℝ) - (2 : ℝ) ^ ((j : ℤ) - 53)) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let x : ℝ := (N : ℝ) - (2 : ℝ) ^ ((j : ℤ) - 53)
  have htail_pos : 0 < (2 : ℝ) ^ ((j : ℤ) - 53) :=
    zpow_pos (by norm_num : (0 : ℝ) < 2) _
  have htail_le_one : (2 : ℝ) ^ ((j : ℤ) - 53) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hpow_pos_nat : 0 < 2 ^ j := pow_pos (by norm_num : 0 < 2) j
  have hpow_ge_one : 1 ≤ 2 ^ j := Nat.succ_le_of_lt hpow_pos_nat
  have hN_ge_two_nat : 2 ≤ N := by omega
  have hN_ge_two : (2 : ℝ) ≤ N := by exact_mod_cast hN_ge_two_nat
  have hx_ge_one : (1 : ℝ) ≤ x := by
    dsimp [x]
    nlinarith
  have hx_nonneg : 0 ≤ x := by linarith
  rw [FloatingPointFormat.finiteNormalRange]
  rw [show |(N : ℝ) - (2 : ℝ) ^ ((j : ℤ) - 53)| = x by
    dsimp [x]
    exact abs_of_nonneg hx_nonneg]
  constructor
  · have hmin_le_one : fmt.minNormalMagnitude ≤ (1 : ℝ) := by
      simpa [fmt, FloatingPointFormat.ieeeDoubleFormat,
        FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR] using
        (zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (-1022 : ℤ) ≤ 0))
    exact le_trans hmin_le_one hx_ge_one
  · have hx_le_N : x ≤ (N : ℝ) := by
      dsimp [x]
      nlinarith [le_of_lt htail_pos]
    have hN_le_pow_nat : N ≤ 2 ^ (j + 1) := Nat.le_of_lt hhi
    have hN_le_pow_real : (N : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
      exact_mod_cast hN_le_pow_nat
    have hpow_le_max : (2 : ℝ) ^ (j + 1) ≤ fmt.maxFiniteMagnitude := by
      simpa [fmt] using
        (FloatingPointFormat.problem2_10_ieeeDouble_two_pow_le_maxFiniteMagnitude
          (k := j + 1) (by omega))
    exact le_trans hx_le_N (le_trans hN_le_pow_real hpow_le_max)

private theorem wilkinsonProblem42_ieeeDouble_sameBinade_midpoint_rounds_to_nat
    {j N : ℕ} (hj : j ≤ 51) (hlo : 2 ^ j < N)
    (hhi : N < 2 ^ (j + 1)) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
      ((N : ℝ) - (2 : ℝ) ^ ((j : ℤ) - 53)) =
      (N : ℝ) := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let x : ℝ := (N : ℝ) - (2 : ℝ) ^ ((j : ℤ) - 53)
  let a : ℝ := (N : ℝ) - (2 : ℝ) ^ ((((j + 1 : ℕ) : ℤ) - 53))
  let b : ℝ := (N : ℝ)
  let leftMantissa : ℕ := N * 2 ^ (52 - j) - 1
  let e : ℤ := ((j + 1 : ℕ) : ℤ)
  have hxnormal : fmt.finiteNormalRange x := by
    simpa [fmt, x] using
      wilkinsonProblem42_ieeeDouble_sameBinade_midpoint_finiteNormalRange
        hj hlo hhi
  have hleftMantissa : fmt.normalizedMantissa leftMantissa := by
    simpa [fmt, leftMantissa] using
      wilkinsonProblem42_ieeeDouble_sameBinade_left_mantissa
        hj hlo hhi
  have hrightMantissa : fmt.normalizedMantissa (leftMantissa + 1) := by
    have hsucc : leftMantissa + 1 = N * 2 ^ (52 - j) := by
      dsimp [leftMantissa]
      have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hlo
      have hMpos : 0 < N * 2 ^ (52 - j) :=
        Nat.mul_pos hNpos (pow_pos (by norm_num : 0 < 2) _)
      omega
    rw [hsucc]
    simpa [fmt] using
      wilkinsonProblem42_ieeeDouble_sameBinade_right_mantissa hj hlo hhi
  have hstep :
      (2 : ℝ) ^ (((j : ℤ) + 1 - 53)) =
        2 * (2 : ℝ) ^ ((j : ℤ) - 53) := by
    have hexp : ((j : ℤ) + 1 - 53) = ((j : ℤ) - 53) + 1 := by
      ring
    rw [hexp]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have htail_pos : 0 < (2 : ℝ) ^ ((j : ℤ) - 53) :=
    zpow_pos (by norm_num : (0 : ℝ) < 2) _
  have hleft : a = fmt.normalizedValue false leftMantissa e := by
    dsimp [a, fmt, leftMantissa, e]
    exact (wilkinsonProblem42_ieeeDouble_sameBinade_left_value hj hlo).symm
  have hright : b = fmt.normalizedValue false (leftMantissa + 1) e := by
    have hsucc : leftMantissa + 1 = N * 2 ^ (52 - j) := by
      dsimp [leftMantissa]
      have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hlo
      have hMpos : 0 < N * 2 ^ (52 - j) :=
        Nat.mul_pos hNpos (pow_pos (by norm_num : 0 < 2) _)
      omega
    dsimp [b, fmt, e]
    rw [hsucc]
    exact (wilkinsonProblem42_ieeeDouble_sameBinade_right_value (N := N) hj).symm
  have hstrict : a < x ∧ x < b := by
    dsimp [a, x, b]
    constructor
    · rw [hstep]
      nlinarith
    · nlinarith
  have htie : |x - a| = |x - b| := by
    dsimp [x, a, b]
    rw [hstep]
    have hleft_abs :
        |((N : ℝ) - (2 : ℝ) ^ ((j : ℤ) - 53)) -
            ((N : ℝ) - 2 * (2 : ℝ) ^ ((j : ℤ) - 53))| =
          (2 : ℝ) ^ ((j : ℤ) - 53) := by
      rw [show ((N : ℝ) - (2 : ℝ) ^ ((j : ℤ) - 53)) -
            ((N : ℝ) - 2 * (2 : ℝ) ^ ((j : ℤ) - 53)) =
          (2 : ℝ) ^ ((j : ℤ) - 53) by ring]
      exact abs_of_pos htail_pos
    have hright_abs :
        |((N : ℝ) - (2 : ℝ) ^ ((j : ℤ) - 53)) - (N : ℝ)| =
          (2 : ℝ) ^ ((j : ℤ) - 53) := by
      rw [show ((N : ℝ) - (2 : ℝ) ^ ((j : ℤ) - 53)) - (N : ℝ) =
          -((2 : ℝ) ^ ((j : ℤ) - 53)) by ring]
      simp [abs_of_neg (neg_lt_zero.mpr htail_pos)]
    rw [hleft_abs, hright_abs]
  have hodd : ¬ FloatingPointFormat.evenMantissa leftMantissa := by
    simpa [leftMantissa] using
      wilkinsonProblem42_ieeeDouble_sameBinade_left_mantissa_odd hj hlo
  simpa [fmt, x, b] using
    finiteRoundToEven_eq_right_of_pos_same_exp_tie_odd
      (fmt := fmt) hxnormal hleftMantissa hrightMantissa hleft hright
      hstrict htie hodd

/-- Reusable IEEE-double same-binade Wilkinson block step.  If the next integer
`N` lies strictly inside the binade `(2^j, 2^(j+1))`, then adding the `j`th
Wilkinson block value to the previous integer accumulator `N-1` lands exactly at
the midpoint below `N`, and round-to-even chooses `N`. -/
theorem wilkinsonProblem42_ieeeDouble_sameBinade_add_rounds_to_nat
    {j N : ℕ} (hj : j ≤ 51) (hlo : 2 ^ j < N)
    (hhi : N < 2 ^ (j + 1)) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        ((N - 1 : ℕ) : ℝ) (wilkinsonProblem42BlockValue 53 j) =
      (N : ℝ) := by
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
      (((N - 1 : ℕ) : ℝ) + wilkinsonProblem42BlockValue 53 j) =
    (N : ℝ)
  have hNone : 1 ≤ N := by
    have hpow_pos : 0 < 2 ^ j := pow_pos (by norm_num : 0 < 2) j
    omega
  have harg :
      (((N - 1 : ℕ) : ℝ) + wilkinsonProblem42BlockValue 53 j) =
        (N : ℝ) - (2 : ℝ) ^ ((j : ℤ) - 53) := by
    rw [Nat.cast_sub hNone]
    norm_num [wilkinsonProblem42BlockValue]
  rw [harg]
  exact
    wilkinsonProblem42_ieeeDouble_sameBinade_midpoint_rounds_to_nat
      hj hlo hhi

/-- Reusable IEEE-double power-boundary Wilkinson block step.  The last addition
in the `j`th block lands at the midpoint below `2^(j+1)`, and round-to-even
selects the power-of-two endpoint. -/
theorem wilkinsonProblem42_ieeeDouble_block_boundary_add_rounds_to_pow
    {j : ℕ} (hj : j ≤ 51) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        ((2 ^ (j + 1) - 1 : ℕ) : ℝ) (wilkinsonProblem42BlockValue 53 j) =
      (2 : ℝ) ^ (j + 1) := by
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
      (((2 ^ (j + 1) - 1 : ℕ) : ℝ) + wilkinsonProblem42BlockValue 53 j) =
    (2 : ℝ) ^ (j + 1)
  have hOne : 1 ≤ 2 ^ (j + 1) :=
    Nat.succ_le_of_lt (pow_pos (by norm_num : 0 < 2) (j + 1))
  have harg :
      (((2 ^ (j + 1) - 1 : ℕ) : ℝ) + wilkinsonProblem42BlockValue 53 j) =
        (2 : ℝ) ^ (j + 1) - (2 : ℝ) ^ (((j + 1 : ℕ) : ℤ) - 54) := by
    rw [Nat.cast_sub hOne]
    have hexp : (((j + 1 : ℕ) : ℤ) - 54) = ((j : ℤ) - 53) := by
      omega
    rw [hexp]
    norm_num [wilkinsonProblem42BlockValue]
  rw [harg]
  exact
    (FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_two_pow_rounds_to_two_pow
      (k := j + 1) (by omega))

/-- Prefix invariant for a complete IEEE-double Wilkinson block.  Starting a
`j`th block at the exact accumulator `2^j`, after any `m <= 2^j` repeated
round-to-even additions of the block value the accumulator is the integer
`2^j + m`. -/
theorem wilkinsonProblem42_ieeeDouble_block_prefix_accumulator
    {j m : ℕ} (hj : j ≤ 51) (hm : m ≤ 2 ^ j) :
    Fin.foldl m
      (fun acc _ =>
        FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
          acc (wilkinsonProblem42BlockValue 53 j))
      ((2 : ℝ) ^ j) =
      ((2 ^ j + m : ℕ) : ℝ) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Fin.foldl_succ_last]
      have hm' : m ≤ 2 ^ j := by omega
      rw [ih hm']
      have hNsub :
          (2 ^ j + m : ℕ) = 2 ^ j + (m + 1) - 1 := by
        have hpos : 0 < 2 ^ j + (m + 1) := by positivity
        omega
      have hcast_prev :
          (((2 ^ j + m : ℕ) : ℝ)) =
            (((2 ^ j + (m + 1) - 1 : ℕ) : ℝ)) := by
        rw [hNsub]
      rw [hcast_prev]
      rcases Nat.lt_or_eq_of_le hm with hlt | heq
      · have hlo : 2 ^ j < 2 ^ j + (m + 1) := by omega
        have hhi : 2 ^ j + (m + 1) < 2 ^ (j + 1) := by
          have hsum : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
            rw [Nat.pow_succ]
            ring
          omega
        simpa using
          (wilkinsonProblem42_ieeeDouble_sameBinade_add_rounds_to_nat
            (j := j) (N := 2 ^ j + (m + 1)) hj hlo hhi)
      · have hN : 2 ^ j + (m + 1) = 2 ^ (j + 1) := by
          have hsum : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
            rw [Nat.pow_succ]
            ring
          omega
        rw [hN]
        simpa using
          (wilkinsonProblem42_ieeeDouble_block_boundary_add_rounds_to_pow
            (j := j) hj)

/-- A complete IEEE-double Wilkinson block maps the exact accumulator `2^j` to
`2^(j+1)`.  This is the block-iteration dependency needed before proving the
arbitrary positive-length finite recursive trace. -/
theorem wilkinsonProblem42_ieeeDouble_block_rounds_pow_to_next_pow
    {j : ℕ} (hj : j ≤ 51) :
    Fin.foldl (2 ^ j)
      (fun acc _ =>
        FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
          acc (wilkinsonProblem42BlockValue 53 j))
      ((2 : ℝ) ^ j) =
      (2 : ℝ) ^ (j + 1) := by
  have h :=
    wilkinsonProblem42_ieeeDouble_block_prefix_accumulator
      (j := j) (m := 2 ^ j) hj le_rfl
  have hpow : ((2 ^ j + 2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ (j + 1) := by
    rw [show 2 ^ j + 2 ^ j = 2 ^ (j + 1) by
      rw [Nat.pow_succ]
      ring]
    norm_num
  exact h.trans hpow

/-- List-shaped arbitrary-length IEEE-double trace for Wilkinson's Problem 4.2
source family.  For every `r <= 52`, recursive round-to-even summation of the
displayed list with `t = 53` follows the integer accumulator path and returns
`2^r`. -/
theorem wilkinsonProblem42_ieeeDouble_listRecursiveSum_eq_pow
    {r : ℕ} (hr : r ≤ 52) :
    finiteRoundToEvenListSum FloatingPointFormat.ieeeDoubleFormat
        (wilkinsonProblem42Input 53 r) =
      (2 : ℝ) ^ r := by
  induction r with
  | zero =>
      simp [finiteRoundToEvenListSum, wilkinsonProblem42Input,
        FloatingPointFormat.finiteRoundToEvenOp_add_zero_of_finiteSystem,
        FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_one]
  | succ r ih =>
      have hr' : r ≤ 52 := by omega
      have hj : r ≤ 51 := by omega
      change (wilkinsonProblem42Input 53 r ++
          List.replicate (2 ^ r) (wilkinsonProblem42BlockValue 53 r)).foldl
          (fun acc x =>
            FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
              acc x) 0 =
        (2 : ℝ) ^ (r + 1)
      rw [List.foldl_append]
      change (List.replicate (2 ^ r) (wilkinsonProblem42BlockValue 53 r)).foldl
          (fun acc x =>
            FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
              acc x)
          (finiteRoundToEvenListSum FloatingPointFormat.ieeeDoubleFormat
            (wilkinsonProblem42Input 53 r)) =
        (2 : ℝ) ^ (r + 1)
      rw [ih hr']
      rw [finiteRoundToEvenListSum_replicate_eq_fin_foldl]
      exact wilkinsonProblem42_ieeeDouble_block_rounds_pow_to_next_pow
        (j := r) hj

/-- Arbitrary-length IEEE-double finite recursive trace for Wilkinson's
Problem 4.2 source family.  Under the IEEE-double `t = 53` instantiation and
`r <= 52`, the concrete finite round-to-even recursive trace returns `2^r`. -/
theorem wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow
    {r : ℕ} (hr : r ≤ 52) :
    finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
        (2 ^ r) (wilkinsonProblem42Vector 53 r) =
      (2 : ℝ) ^ r := by
  rw [finiteRoundToEvenRecursiveSum_eq_listSum,
    wilkinsonProblem42Vector_toList]
  exact wilkinsonProblem42_ieeeDouble_listRecursiveSum_eq_pow hr

/-- Concrete IEEE-double realized absolute error for Wilkinson's Problem 4.2
family.  Once the arbitrary rounded trace is closed, the exact forward error is
the low-order defect. -/
theorem wilkinsonProblem42_ieeeDouble_abs_error_eq_defect
    {r : ℕ} (hr : r ≤ 52) :
    |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
        (2 ^ r) (wilkinsonProblem42Vector 53 r) -
        wilkinsonProblem42ExactSum 53 r| =
      wilkinsonProblem42Defect 53 r := by
  have htrace :=
    wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow (r := r) hr
  have hdiff :
      (2 : ℝ) ^ r - wilkinsonProblem42ExactSum 53 r =
        wilkinsonProblem42Defect 53 r := by
    have hsum := wilkinsonProblem42ExactSum_add_defect 53 r
    linarith
  rw [htrace, hdiff]
  exact abs_of_nonneg (wilkinsonProblem42Defect_nonneg 53 r)

/-- Closed form for the realized IEEE-double absolute error in Wilkinson's
Problem 4.2 family. -/
theorem wilkinsonProblem42_ieeeDouble_abs_error_closed_form
    {r : ℕ} (hr : r ≤ 52) :
    3 * |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
        (2 ^ r) (wilkinsonProblem42Vector 53 r) -
        wilkinsonProblem42ExactSum 53 r| + (2 : ℝ) ^ (-53 : ℤ) =
      (2 : ℝ) ^ (((2 * r : ℕ) : ℤ) - (53 : ℤ)) := by
  rw [wilkinsonProblem42_ieeeDouble_abs_error_eq_defect hr]
  exact wilkinsonProblem42Defect_closed_form 53 r

/-- Actual-error version of the first-order scale comparison for the concrete
IEEE-double Wilkinson trace. -/
theorem wilkinsonProblem42_ieeeDouble_first_order_bound_le_three_abs_error_plus_u
    {r : ℕ} (hr : r ≤ 52) :
    (((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ))) *
        wilkinsonProblem42ExactSum 53 r ≤
      3 * |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
          (2 ^ r) (wilkinsonProblem42Vector 53 r) -
          wilkinsonProblem42ExactSum 53 r| + (2 : ℝ) ^ (-(53 : ℤ)) := by
  simpa [wilkinsonProblem42_ieeeDouble_abs_error_eq_defect hr] using
    (wilkinsonProblem42_first_order_bound_le_three_defect_plus_u 53 r)

/-- Constant-factor near-attainment of the first-order recursive-summation
scale by Wilkinson's concrete IEEE-double family.  For positive `r <= 52`, the
source first-order scale is at most four times the realized absolute error. -/
theorem wilkinsonProblem42_ieeeDouble_first_order_bound_le_four_abs_error
    {r : ℕ} (hr : r ≤ 52) (hrpos : 0 < r) :
    (((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ))) *
        wilkinsonProblem42ExactSum 53 r ≤
      4 * |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
          (2 ^ r) (wilkinsonProblem42Vector 53 r) -
          wilkinsonProblem42ExactSum 53 r| := by
  have hfirst :=
    wilkinsonProblem42_ieeeDouble_first_order_bound_le_three_abs_error_plus_u
      (r := r) hr
  have hu :=
    wilkinsonProblem42_unit_roundoff_le_defect_of_pos (t := 53) (r := r) hrpos
  have hu' : (2 : ℝ) ^ (-(53 : ℤ)) ≤ wilkinsonProblem42Defect 53 r := by
    simpa using hu
  have habs := wilkinsonProblem42_ieeeDouble_abs_error_eq_defect hr
  have htail :
      3 * |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
          (2 ^ r) (wilkinsonProblem42Vector 53 r) -
          wilkinsonProblem42ExactSum 53 r| + (2 : ℝ) ^ (-(53 : ℤ)) ≤
        4 * |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
          (2 ^ r) (wilkinsonProblem42Vector 53 r) -
          wilkinsonProblem42ExactSum 53 r| := by
    rw [habs]
    nlinarith
  exact le_trans hfirst htail

/-- Actual-error version of the exact `gamma` denominator comparison for the
concrete IEEE-double Wilkinson trace. -/
theorem wilkinsonProblem42_ieeeDouble_gamma_bound_le_three_abs_error_plus_u_div
    (fp : FPModel) {r : ℕ}
    (hr : r ≤ 52)
    (hunit : fp.u = (2 : ℝ) ^ (-(53 : ℤ)))
    (hvalid : gammaValid fp (2 ^ r - 1)) :
    gamma fp (2 ^ r - 1) * wilkinsonProblem42ExactSum 53 r ≤
      (3 * |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
          (2 ^ r) (wilkinsonProblem42Vector 53 r) -
          wilkinsonProblem42ExactSum 53 r| + (2 : ℝ) ^ (-(53 : ℤ))) /
        (1 - ((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ))) := by
  simpa [wilkinsonProblem42_ieeeDouble_abs_error_eq_defect hr] using
    (wilkinsonProblem42_gamma_bound_le_three_defect_plus_u_div
      fp 53 r hunit hvalid)

/-- Denominator-aware constant-factor near-attainment for the exact `gamma`
recursive-summation bound.  If the usual denominator satisfies
`2*(2^r-1)*u <= 1`, the exact `gamma` scale is at most eight times the
realized absolute error of Wilkinson's IEEE-double trace. -/
theorem wilkinsonProblem42_ieeeDouble_gamma_bound_le_eight_abs_error
    (fp : FPModel) {r : ℕ}
    (hr : r ≤ 52) (hrpos : 0 < r)
    (hunit : fp.u = (2 : ℝ) ^ (-(53 : ℤ)))
    (hsmall :
      2 * (((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ))) ≤ 1) :
    gamma fp (2 ^ r - 1) * wilkinsonProblem42ExactSum 53 r ≤
      8 * |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
          (2 ^ r) (wilkinsonProblem42Vector 53 r) -
          wilkinsonProblem42ExactSum 53 r| := by
  let k : ℝ := ((2 ^ r - 1 : ℕ) : ℝ)
  let u : ℝ := (2 : ℝ) ^ (-(53 : ℤ))
  let A : ℝ :=
    |finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
        (2 ^ r) (wilkinsonProblem42Vector 53 r) -
        wilkinsonProblem42ExactSum 53 r|
  have hu_pos : 0 < u := by
    dsimp [u]
    positivity
  have hk_nonneg : 0 ≤ k := by
    dsimp [k]
    exact_mod_cast Nat.zero_le _
  have hku_le_half : k * u ≤ (1 : ℝ) / 2 := by
    change (((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ))) ≤
      (1 : ℝ) / 2
    calc
      ((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ)) =
          (1 / 2 : ℝ) *
            (2 * (((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ)))) := by
        ring
      _ ≤ (1 / 2 : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _ = (1 : ℝ) / 2 := by ring
  have hvalid : gammaValid fp (2 ^ r - 1) := by
    unfold gammaValid
    rw [hunit]
    dsimp [k, u] at hku_le_half
    nlinarith [hu_pos, hk_nonneg]
  have hgamma :=
    wilkinsonProblem42_ieeeDouble_gamma_bound_le_three_abs_error_plus_u_div
      fp (r := r) hr hunit hvalid
  have hden_pos :
      0 < 1 - ((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ)) := by
    dsimp [k, u] at hku_le_half
    nlinarith
  have hden_ge_half :
      (1 : ℝ) / 2 ≤
        1 - ((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ)) := by
    dsimp [k, u] at hku_le_half
    nlinarith
  have hu_def :=
    wilkinsonProblem42_unit_roundoff_le_defect_of_pos (t := 53) (r := r) hrpos
  have hu_def' : (2 : ℝ) ^ (-(53 : ℤ)) ≤ wilkinsonProblem42Defect 53 r := by
    simpa using hu_def
  have habs := wilkinsonProblem42_ieeeDouble_abs_error_eq_defect hr
  have hnum_le :
      3 * A + (2 : ℝ) ^ (-(53 : ℤ)) ≤ 4 * A := by
    dsimp [A]
    rw [habs]
    nlinarith
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact abs_nonneg _
  have hdiv_num :
      (3 * A + (2 : ℝ) ^ (-(53 : ℤ))) /
          (1 - ((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ))) ≤
        (4 * A) /
          (1 - ((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ))) := by
    exact div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)
  have hdiv_den :
      (4 * A) /
          (1 - ((2 ^ r - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(53 : ℤ))) ≤
        8 * A := by
    rw [div_le_iff₀ hden_pos]
    nlinarith
  exact le_trans hgamma (le_trans hdiv_num hdiv_den)

/-- The first nontrivial Wilkinson block is exactly the IEEE-double midpoint
below `2`, hence round-to-even chooses the even power-of-two endpoint. -/
theorem wilkinsonProblem42_ieeeDouble_first_block_rounds_to_two :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (1 : ℝ) (wilkinsonProblem42BlockValue 53 0) =
      2 := by
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
      ((1 : ℝ) + wilkinsonProblem42BlockValue 53 0) = 2
  have harg :
      (1 : ℝ) + wilkinsonProblem42BlockValue 53 0 =
        (2 : ℝ) ^ (1 : ℕ) - (2 : ℝ) ^ (((1 : ℕ) : ℤ) - 54) := by
    norm_num [wilkinsonProblem42BlockValue]
  rw [harg]
  simpa using
    (FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_two_pow_rounds_to_two_pow
      (k := 1) (by norm_num))

/-- Concrete IEEE-double recursive trace for the first positive Wilkinson
length.  This closes the `r = 1` instance of the finite-format trace: the
initial zero-add stores `1`, and the first Wilkinson block rounds to `2`. -/
theorem wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow_one :
    finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
        (2 ^ 1) (wilkinsonProblem42Vector 53 1) =
      (2 : ℝ) ^ 1 := by
  simp [finiteRoundToEvenRecursiveSum, wilkinsonProblem42Vector,
    wilkinsonProblem42Input, Fin.foldl_succ,
    FloatingPointFormat.finiteRoundToEvenOp_add_zero_of_finiteSystem,
    FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_one,
    wilkinsonProblem42_ieeeDouble_first_block_rounds_to_two]

private theorem wilkinsonProblem42_ieeeDouble_second_block_first_add_rounds_to_three :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (2 : ℝ) (wilkinsonProblem42BlockValue 53 1) =
      3 := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let x : ℝ := (3 : ℝ) - (2 : ℝ) ^ (-52 : ℤ)
  let a : ℝ := fmt.normalizedValue false 6755399441055743 (2 : ℤ)
  let b : ℝ := fmt.normalizedValue false 6755399441055744 (2 : ℤ)
  have harg :
      (2 : ℝ) + wilkinsonProblem42BlockValue 53 1 = x := by
    norm_num [x, wilkinsonProblem42BlockValue]
  have hxnormal : fmt.finiteNormalRange x := by
    rw [FloatingPointFormat.finiteNormalRange]
    have hxnonneg : 0 ≤ x := by
      norm_num [x, zpow_neg]
    rw [abs_of_nonneg hxnonneg]
    constructor
    · have hmin_le_tail :
          fmt.minNormalMagnitude ≤ (2 : ℝ) ^ (-52 : ℤ) := by
        norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
          FloatingPointFormat.minNormalMagnitude, FloatingPointFormat.betaR,
          zpow_neg]
        have hden : (2 : ℝ) ^ (52 : ℕ) ≤ (2 : ℝ) ^ (1022 : ℕ) := by
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num)
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (52 : ℕ) := by positivity
        have hpow52 : (2 : ℝ) ^ (52 : ℕ) = 4503599627370496 := by
          norm_num
        simpa [one_div, hpow52] using one_div_le_one_div_of_le hpos hden
      have htail_le_x : (2 : ℝ) ^ (-52 : ℤ) ≤ x := by
        norm_num [x, zpow_neg]
      exact le_trans hmin_le_tail htail_le_x
    · have hle_two :
          x ≤ (2 : ℝ) ^ (2 : ℕ) := by
        have htail_nonneg : 0 ≤ (2 : ℝ) ^ (-52 : ℤ) :=
          le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) _)
        norm_num [x]
      exact le_trans hle_two
        (FloatingPointFormat.problem2_10_ieeeDouble_two_pow_le_maxFiniteMagnitude
          (k := 2) (by norm_num))
  have hleftMantissa : fmt.normalizedMantissa 6755399441055743 := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have hrightMantissa :
      fmt.normalizedMantissa (6755399441055743 + 1) := by
    norm_num [fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa]
  have ha_value : a = (3 : ℝ) - (2 : ℝ) ^ (-51 : ℤ) := by
    norm_num [a, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
  have hb_value : b = (3 : ℝ) := by
    norm_num [b, fmt, FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue, FloatingPointFormat.betaR, zpow_neg]
    rfl
  have hstrict : a < x ∧ x < b := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hleft : a = fmt.normalizedValue false 6755399441055743 (2 : ℤ) := rfl
  have hright :
      b = fmt.normalizedValue false (6755399441055743 + 1) (2 : ℤ) := by
    norm_num [b]
  have htie : |x - a| = |x - b| := by
    rw [ha_value, hb_value]
    norm_num [x, zpow_neg]
  have hodd : ¬ FloatingPointFormat.evenMantissa 6755399441055743 := by
    norm_num [FloatingPointFormat.evenMantissa]
  change fmt.finiteRoundToEven ((2 : ℝ) + wilkinsonProblem42BlockValue 53 1) = 3
  rw [harg]
  simpa [hb_value] using
    finiteRoundToEven_eq_right_of_pos_same_exp_tie_odd
      (fmt := fmt) hxnormal hleftMantissa hrightMantissa hleft hright
      hstrict htie hodd

private theorem wilkinsonProblem42_ieeeDouble_second_block_second_add_rounds_to_four :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEvenOp BasicOp.add
        (3 : ℝ) (wilkinsonProblem42BlockValue 53 1) =
      4 := by
  change FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven
      ((3 : ℝ) + wilkinsonProblem42BlockValue 53 1) = 4
  have harg :
      (3 : ℝ) + wilkinsonProblem42BlockValue 53 1 =
        (2 : ℝ) ^ (2 : ℕ) - (2 : ℝ) ^ (((2 : ℕ) : ℤ) - 54) := by
    norm_num [wilkinsonProblem42BlockValue]
  rw [harg]
  have hround :=
    (FloatingPointFormat.problem2_10_ieeeDouble_midpoint_below_two_pow_rounds_to_two_pow
      (k := 2) (by norm_num))
  have hpow : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
  rw [← hpow]
  exact hround

/-- Concrete IEEE-double recursive trace for the second positive Wilkinson
length.  This covers the first same-binade midpoint and the following
power-boundary midpoint in Wilkinson's block construction. -/
theorem wilkinsonProblem42_ieeeDouble_finiteRecursiveSum_eq_pow_two :
    finiteRoundToEvenRecursiveSum FloatingPointFormat.ieeeDoubleFormat
        (2 ^ 2) (wilkinsonProblem42Vector 53 2) =
      (2 : ℝ) ^ 2 := by
  simp [finiteRoundToEvenRecursiveSum, wilkinsonProblem42Vector,
    wilkinsonProblem42Input, Fin.foldl_succ,
    FloatingPointFormat.finiteRoundToEvenOp_add_zero_of_finiteSystem,
    FloatingPointFormat.problem2_10_ieeeDouble_finiteSystem_one,
    wilkinsonProblem42_ieeeDouble_first_block_rounds_to_two,
    wilkinsonProblem42_ieeeDouble_second_block_first_add_rounds_to_three,
    wilkinsonProblem42_ieeeDouble_second_block_second_add_rounds_to_four]
  norm_num

end NumStability
