/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter26.AlternatingDirections.ExactExecution
import Mathlib.Tactic

namespace NumStability

/-! # Higham Chapter 26: Crude Alternating-Directions Line Search

The finite signed and doubled line-search producer described on page 475, with its monotonicity results.
-/

/-- Higham, 2nd ed., p. 475: the first alternating-directions trial step,
`10⁻⁴ xᵢ`, with the printed zero-coordinate fallback
`10⁻⁴ max (‖x‖∞, 1)`.  The norm on a finite real function is its sup norm. -/
noncomputable def higham26ADInitialStep {n : Nat}
    (x : RVec n) (i : Fin n) : Real :=
  if x i = 0 then
    ((1 : Real) / 10000) * max ‖x‖ 1
  else
    ((1 : Real) / 10000) * x i

@[simp] theorem higham26ADInitialStep_of_eq_zero {n : Nat}
    (x : RVec n) (i : Fin n) (hxi : x i = 0) :
    higham26ADInitialStep x i =
      ((1 : Real) / 10000) * max ‖x‖ 1 := by
  simp [higham26ADInitialStep, hxi]

@[simp] theorem higham26ADInitialStep_of_ne_zero {n : Nat}
    (x : RVec n) (i : Fin n) (hxi : x i ≠ 0) :
    higham26ADInitialStep x i = ((1 : Real) / 10000) * x i := by
  simp [higham26ADInitialStep, hxi]

/-- The source's sign-reversal rule: reverse the initial trial precisely when
the first evaluation gives no strict increase over the current point. -/
noncomputable def higham26ADDirectedStep {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) : Real :=
  let h := higham26ADInitialStep x i
  if f (adCoordinateLinePoint x i h) ≤ f x then -h else h

theorem higham26ADDirectedStep_of_noIncrease {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n)
    (h : f (adCoordinateLinePoint x i (higham26ADInitialStep x i)) ≤ f x) :
    higham26ADDirectedStep f x i = -higham26ADInitialStep x i := by
  simp [higham26ADDirectedStep, h]

theorem higham26ADDirectedStep_of_increase {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n)
    (h : f x < f (adCoordinateLinePoint x i (higham26ADInitialStep x i))) :
    higham26ADDirectedStep f x i = higham26ADInitialStep x i := by
  simp [higham26ADDirectedStep, not_le.mpr h]

/-- Starting from a successful signed trial `h`, double it while the newly
doubled trial strictly improves on the previous one.  `fuel` is the exact
upper bound on the number of doublings attempted. -/
noncomputable def higham26ADDoubleSearch {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) : Nat → Real → Real
  | 0, h => h
  | fuel + 1, h =>
      let next := 2 * h
      if f (adCoordinateLinePoint x i h) <
          f (adCoordinateLinePoint x i next) then
        higham26ADDoubleSearch f x i fuel next
      else
        h

/-- The doubling loop never returns a trial with a smaller objective value
than the successful trial with which it started. -/
theorem higham26ADDoubleSearch_value_ge {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n)
    (fuel : Nat) (h : Real) :
    f (adCoordinateLinePoint x i h) ≤
      f (adCoordinateLinePoint x i
        (higham26ADDoubleSearch f x i fuel h)) := by
  induction fuel generalizing h with
  | zero => simp [higham26ADDoubleSearch]
  | succ fuel ih =>
      by_cases hinc : f (adCoordinateLinePoint x i h) <
          f (adCoordinateLinePoint x i (2 * h))
      · simp only [higham26ADDoubleSearch, hinc, if_true]
        exact le_trans (le_of_lt hinc) (ih (2 * h))
      · simp [higham26ADDoubleSearch, hinc]

/-- After at most `fuel` doublings, the returned displacement is exactly
`2^k h` for some `k ≤ fuel`. -/
theorem higham26ADDoubleSearch_eq_pow {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n)
    (fuel : Nat) (h : Real) :
    ∃ k : Nat, k ≤ fuel ∧
      higham26ADDoubleSearch f x i fuel h = (2 : Real) ^ k * h := by
  induction fuel generalizing h with
  | zero =>
      exact ⟨0, le_rfl, by simp [higham26ADDoubleSearch]⟩
  | succ fuel ih =>
      by_cases hinc : f (adCoordinateLinePoint x i h) <
          f (adCoordinateLinePoint x i (2 * h))
      · rcases ih (2 * h) with ⟨k, hk, hout⟩
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
        simp only [higham26ADDoubleSearch, hinc, if_true]
        rw [hout]
        ring
      · exact ⟨0, Nat.zero_le _, by simp [higham26ADDoubleSearch, hinc]⟩

/-- Literal p. 475 crude line-search result.  If the signed trial fails to
improve on `x`, the displacement is zero.  Otherwise it is doubled at most
25 times, stopping at the last strictly improving trial. -/
noncomputable def higham26ADCrudeAlpha {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) : Real :=
  let h := higham26ADDirectedStep f x i
  if f x < f (adCoordinateLinePoint x i h) then
    higham26ADDoubleSearch f x i 25 h
  else
    0

/-- The literal crude line search cannot decrease the objective. -/
theorem higham26ADCrudeAlpha_value_ge {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) :
    f x ≤ f (adCoordinateLinePoint x i (higham26ADCrudeAlpha f x i)) := by
  by_cases hinc : f x <
      f (adCoordinateLinePoint x i (higham26ADDirectedStep f x i))
  · simp only [higham26ADCrudeAlpha, hinc, if_true]
    exact le_trans (le_of_lt hinc)
      (higham26ADDoubleSearch_value_ge f x i 25
        (higham26ADDirectedStep f x i))
  · simp [higham26ADCrudeAlpha, hinc, adCoordinateLinePoint_zero]

/-- The returned displacement is either zero or exactly `2^k` times the
signed trial for some `k ≤ 25`; hence the implementation performs no more
than the 25 doublings printed in the source. -/
theorem higham26ADCrudeAlpha_eq_zero_or_pow {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) :
    ∃ k : Nat, k ≤ 25 ∧
      (higham26ADCrudeAlpha f x i = 0 ∨
        higham26ADCrudeAlpha f x i =
          (2 : Real) ^ k * higham26ADDirectedStep f x i) := by
  by_cases hinc : f x <
      f (adCoordinateLinePoint x i (higham26ADDirectedStep f x i))
  · rcases higham26ADDoubleSearch_eq_pow f x i 25
        (higham26ADDirectedStep f x i) with ⟨k, hk, hout⟩
    exact ⟨k, hk, Or.inr (by simpa [higham26ADCrudeAlpha, hinc] using hout)⟩
  · exact ⟨0, by omega, Or.inl (by simp [higham26ADCrudeAlpha, hinc])⟩

/-- The source's actual finite coordinate-search function, suitable for the
existing `adSweep` and `ADSearchTrace` control-flow definitions. -/
noncomputable def higham26ADCrudeSearch {n : Nat}
    (f : RVec n → Real) : RVec n → Fin n → Real :=
  fun x i => higham26ADCrudeAlpha f x i

theorem higham26ADCrudeCoordinateStep_nondecreasing {n : Nat}
    (f : RVec n → Real) (x : RVec n) (i : Fin n) :
    f x ≤ f (adCoordinateStep (higham26ADCrudeSearch f) x i) := by
  exact higham26ADCrudeAlpha_value_ge f x i

private theorem higham26ADCrudeFold_nondecreasing {n : Nat}
    (f : RVec n → Real) (coordinates : List (Fin n)) (x : RVec n) :
    f x ≤ f (coordinates.foldl
      (adCoordinateStep (higham26ADCrudeSearch f)) x) := by
  induction coordinates generalizing x with
  | nil => simp
  | cons i coordinates ih =>
      exact le_trans (higham26ADCrudeCoordinateStep_nondecreasing f x i)
        (ih (adCoordinateStep (higham26ADCrudeSearch f) x i))

/-- A full literal coordinate-order sweep is objective-nondecreasing. -/
theorem higham26ADCrudeSweep_nondecreasing {n : Nat}
    (f : RVec n → Real) (x : RVec n) :
    f x ≤ f (adSweep (higham26ADCrudeSearch f) x) := by
  exact higham26ADCrudeFold_nondecreasing f
    (List.ofFn (fun i : Fin n => i)) x

end NumStability
