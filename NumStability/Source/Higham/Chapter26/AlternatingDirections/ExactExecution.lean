/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter26.Equation02

namespace NumStability

/-! # Higham Chapter 26: Exact Alternating-Directions Execution

Exact coordinate-line search, coordinate sweeps, and operational traces from Section 26.2.
-/

/-! ### Alternating-directions executor (Section 26.2) -/

/-- The point on the coordinate line through `x` in direction `e_i` with
scalar displacement `alpha`. -/
def adCoordinateLinePoint {n : Nat} (x : RVec n) (i : Fin n)
    (alpha : Real) : RVec n :=
  fun j => if j = i then x j + alpha else x j

@[simp] theorem adCoordinateLinePoint_zero {n : Nat}
    (x : RVec n) (i : Fin n) :
    adCoordinateLinePoint x i 0 = x := by
  funext j
  by_cases hji : j = i <;> simp [adCoordinateLinePoint, hji]

/-- Contract of the exact one-dimensional maximization used by Higham's
alternating-directions pseudocode.  Existence of such a maximizer is an honest
domain condition on the objective; no global maximizer in `Real^n` is assumed. -/
def ADExactLineSearch {n : Nat}
    (f : RVec n -> Real) (search : RVec n -> Fin n -> Real) : Prop :=
  forall x i alpha,
    f (adCoordinateLinePoint x i alpha) <=
      f (adCoordinateLinePoint x i (search x i))

/-- Apply one exact coordinate-line maximization selected by `search`. -/
def adCoordinateStep {n : Nat} (search : RVec n -> Fin n -> Real)
    (x : RVec n) (i : Fin n) : RVec n :=
  adCoordinateLinePoint x i (search x i)

/-- One complete alternating-directions sweep, in source coordinate order
`0,...,n-1`. -/
def adSweep {n : Nat} (search : RVec n -> Fin n -> Real)
    (x : RVec n) : RVec n :=
  (List.ofFn (fun i : Fin n => i)).foldl (adCoordinateStep search) x

/-- A completed exact coordinate step cannot decrease the objective. -/
theorem adCoordinateStep_nondecreasing {n : Nat}
    (f : RVec n -> Real) (search : RVec n -> Fin n -> Real)
    (hsearch : ADExactLineSearch f search) (x : RVec n) (i : Fin n) :
    f x <= f (adCoordinateStep search x i) := by
  have h := hsearch x i 0
  simpa [adCoordinateStep] using h

/-- Operational trace for the alternating-directions method.  A trace stops
exactly at the printed relative-increase test (26.2); otherwise it performs a
full coordinate sweep and repeats. -/
inductive ADSearchTrace {n : Nat} (tol : Real) (f : RVec n -> Real)
    (search : RVec n -> Fin n -> Real) : RVec n -> RVec n -> Prop where
  | stop (x : RVec n)
      (hstop : adConverged tol (f x) (f (adSweep search x))) :
      ADSearchTrace tol f search x (adSweep search x)
  | next {x output : RVec n}
      (hcontinue : Not (adConverged tol (f x) (f (adSweep search x))))
      (htail : ADSearchTrace tol f search (adSweep search x) output) :
      ADSearchTrace tol f search x output

/-- Finite-fuel observation of the same control flow.  `none` means only that
the observation budget ended before (26.2) held. -/
noncomputable def adRun {n : Nat} (fuel : Nat) (tol : Real) (f : RVec n -> Real)
    (search : RVec n -> Fin n -> Real) (x : RVec n) : Option (RVec n) := by
  classical
  cases fuel with
  | zero => exact none
  | succ remaining =>
      let next := adSweep search x
      exact if adConverged tol (f x) (f next) then some next
        else adRun remaining tol f search next
termination_by fuel

end NumStability
