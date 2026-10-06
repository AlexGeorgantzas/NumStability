/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Flat factors for the rounded Algorithm 11.2 execution

This file flattens the stagewise symmetric interchanges and block eliminations
of `Higham11RoundedBunchKaufmanExecution` into one global permutation and named
finite matrices `Lhat,Dhat`.  Later stages permute only the current trailing
indices; the lift operations below make that invariant explicit.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedClosure

open scoped BigOperators

namespace NumStability

open Ch11Closure.Mixed

/-! ## Lifting trailing permutations -/

/-- Fix the leading index and lift a permutation of the trailing indices. -/
def higham11_2_liftPermOne {n : Nat} (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.cases 0 (fun i => (e i).succ)
  invFun := Fin.cases 0 (fun i => (e.symm i).succ)
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp

@[simp] theorem higham11_2_liftPermOne_zero {n : Nat}
    (e : Equiv.Perm (Fin n)) : higham11_2_liftPermOne e 0 = 0 := rfl

@[simp] theorem higham11_2_liftPermOne_succ {n : Nat}
    (e : Equiv.Perm (Fin n)) (i : Fin n) :
    higham11_2_liftPermOne e i.succ = (e i).succ := rfl

/-- Fix the two leading indices and lift a permutation of the trailing
indices. -/
def higham11_2_liftPermTwo {n : Nat} (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 2)) where
  toFun := fun I =>
    Fin.cases 0
      (fun K => Fin.cases (Fin.succ 0) (fun i => (e i).succ.succ) K) I
  invFun := fun I =>
    Fin.cases 0
      (fun K => Fin.cases (Fin.succ 0) (fun i => (e.symm i).succ.succ) K) I
  left_inv := by
    intro I
    refine Fin.cases ?_ (fun K => ?_) I
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) K
      · rfl
      · simp
  right_inv := by
    intro I
    refine Fin.cases ?_ (fun K => ?_) I
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) K
      · rfl
      · simp

@[simp] theorem higham11_2_liftPermTwo_zero {n : Nat}
    (e : Equiv.Perm (Fin n)) : higham11_2_liftPermTwo e 0 = 0 := rfl

@[simp] theorem higham11_2_liftPermTwo_one {n : Nat}
    (e : Equiv.Perm (Fin n)) :
    higham11_2_liftPermTwo e (Fin.succ 0) = Fin.succ 0 := rfl

@[simp] theorem higham11_2_liftPermTwo_succ_succ {n : Nat}
    (e : Equiv.Perm (Fin n)) (i : Fin n) :
    higham11_2_liftPermTwo e i.succ.succ = (e i).succ.succ := rfl

namespace Higham11RoundedBunchKaufmanExecution

/-! ## Global permutation and named flat factors -/

/-- Global permutation from final pivot order to the original input order.
The convention is `A (perm i) (perm j)` for the globally permuted input. -/
noncomputable def permutation : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    Higham11RoundedBunchKaufmanExecution fp A -> Equiv.Perm (Fin n)
  | _, _, .nil _ => Equiv.refl _
  | _, _, .noAction _ _ _ tail =>
      higham11_2_liftPermOne tail.permutation
  | _, _, .case1 A _ _ tail =>
      (higham11_2_liftPermOne tail.permutation).trans
        (higham11_2_bunchKaufmanFirstPerm (by omega)
          higham11_1_bunchParlettAlpha A)
  | _, _, .case2 A _ _ tail =>
      (higham11_2_liftPermOne tail.permutation).trans
        (higham11_2_bunchKaufmanFirstPerm (by omega)
          higham11_1_bunchParlettAlpha A)
  | _, _, .case3 A _ _ tail =>
      (higham11_2_liftPermOne tail.permutation).trans
        (higham11_2_bunchKaufmanFirstPerm (by omega)
          higham11_1_bunchParlettAlpha A)
  | _, _, .case4 A _ _ _ tail =>
      (higham11_2_liftPermTwo tail.permutation).trans
        (higham11_2_bunchKaufmanFirstPerm (by omega)
          higham11_1_bunchParlettAlpha A)
  | _, _, .case4Breakdown A _ _ _ =>
      higham11_2_bunchKaufmanFirstPerm (by omega)
        higham11_1_bunchParlettAlpha A

/-- Flat unit-lower block factor in final pivot order.  A tail permutation
reorders the current multiplier rows before the tail factor is embedded. -/
noncomputable def flatL : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
      Fin n -> Fin n -> Real
  | _, _, .nil _ => fun I _ => Fin.elim0 I
  | _, _, .noAction _ _ _ tail => fun I J =>
      Fin.cases (Fin.cases 1 (fun _ => 0) J)
        (fun i => Fin.cases 0 (fun j => tail.flatL i j) J) I
  | _, _, .case1 A _ _ tail => fun I J =>
      let B := higham11_2_bunchKaufmanRoundedActive A
      let tau := tail.permutation
      Fin.cases (Fin.cases 1 (fun _ => 0) J)
        (fun i => Fin.cases
          (fp.fl_div (B (tau i).succ 0) (B 0 0))
          (fun j => tail.flatL i j) J) I
  | _, _, .case2 A _ _ tail => fun I J =>
      let B := higham11_2_bunchKaufmanRoundedActive A
      let tau := tail.permutation
      Fin.cases (Fin.cases 1 (fun _ => 0) J)
        (fun i => Fin.cases
          (fp.fl_div (B (tau i).succ 0) (B 0 0))
          (fun j => tail.flatL i j) J) I
  | _, _, .case3 A _ _ tail => fun I J =>
      let B := higham11_2_bunchKaufmanRoundedActive A
      let tau := tail.permutation
      Fin.cases (Fin.cases 1 (fun _ => 0) J)
        (fun i => Fin.cases
          (fp.fl_div (B (tau i).succ 0) (B 0 0))
          (fun j => tail.flatL i j) J) I
  | _, _, .case4 A _ _ _ tail => fun I J =>
      let tau := tail.permutation
      Fin.cases
        (Fin.cases 1 (fun K => Fin.cases 0 (fun _ => 0) K) J)
        (fun K => Fin.cases
          (Fin.cases 0 (fun L => Fin.cases 1 (fun _ => 0) L) J)
          (fun i => Fin.cases
            (higham11_2_bunchKaufmanFlMultTwo fp A (tau i) 0)
            (fun L => Fin.cases
              (higham11_2_bunchKaufmanFlMultTwo fp A (tau i) 1)
              (fun j => tail.flatL i j) L) J) K) I
  | _, _, .case4Breakdown _ _ _ _ => fun I J => if I = J then 1 else 0

/-- Flat block-diagonal factor in final pivot order. -/
noncomputable def flatD : {n : Nat} ->
    {A : Higham11RoundedBunchKaufmanMatrix n} ->
    (exec : Higham11RoundedBunchKaufmanExecution fp A) ->
      Fin n -> Fin n -> Real
  | _, _, .nil _ => fun I _ => Fin.elim0 I
  | _, _, .noAction A _ _ tail => fun I J =>
      Fin.cases (Fin.cases (A 0 0) (fun _ => 0) J)
        (fun i => Fin.cases 0 (fun j => tail.flatD i j) J) I
  | _, _, .case1 A _ _ tail => fun I J =>
      let B := higham11_2_bunchKaufmanRoundedActive A
      Fin.cases (Fin.cases (B 0 0) (fun _ => 0) J)
        (fun i => Fin.cases 0 (fun j => tail.flatD i j) J) I
  | _, _, .case2 A _ _ tail => fun I J =>
      let B := higham11_2_bunchKaufmanRoundedActive A
      Fin.cases (Fin.cases (B 0 0) (fun _ => 0) J)
        (fun i => Fin.cases 0 (fun j => tail.flatD i j) J) I
  | _, _, .case3 A _ _ tail => fun I J =>
      let B := higham11_2_bunchKaufmanRoundedActive A
      Fin.cases (Fin.cases (B 0 0) (fun _ => 0) J)
        (fun i => Fin.cases 0 (fun j => tail.flatD i j) J) I
  | _, _, .case4 A _ _ _ tail => fun I J =>
      let B := higham11_2_bunchKaufmanRoundedActive A
      Fin.cases
        (Fin.cases (B 0 0)
          (fun K => Fin.cases (B 0 (Fin.succ 0)) (fun _ => 0) K) J)
        (fun K => Fin.cases
          (Fin.cases (B (Fin.succ 0) 0)
            (fun L => Fin.cases (B (Fin.succ 0) (Fin.succ 0))
              (fun _ => 0) L) J)
          (fun i => Fin.cases 0
            (fun L => Fin.cases 0 (fun j => tail.flatD i j) L) J) K) I
  | _, _, .case4Breakdown A _ _ _ => fun I J =>
      higham11_2_bunchKaufmanRoundedActive A I J

/-- The exact flat product `Lhat Dhat Lhat^T`. -/
noncomputable def flatProduct {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) :
    Fin n -> Fin n -> Real :=
  fun i j => ∑ k₁, ∑ k₂,
    exec.flatL i k₁ * exec.flatD k₁ k₂ * exec.flatL j k₂

/-- The absolute product `|Lhat| |Dhat| |Lhat^T|` from Theorems 11.3--11.4. -/
noncomputable def flatAbsProduct {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) :
    Fin n -> Fin n -> Real :=
  higham11_4_bunchKaufmanProductEntry n exec.flatL exec.flatD

/-- Original input in the final global pivot order. -/
noncomputable def permutedInput {n : Nat}
    {A : Higham11RoundedBunchKaufmanMatrix n}
    (exec : Higham11RoundedBunchKaufmanExecution fp A) :
    Fin n -> Fin n -> Real :=
  fun i j => A (exec.permutation i) (exec.permutation j)

end Higham11RoundedBunchKaufmanExecution

end NumStability
