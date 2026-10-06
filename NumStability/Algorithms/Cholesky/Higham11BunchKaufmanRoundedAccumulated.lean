/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Accumulated rounded Bunch--Kaufman factorization

This module proves the global factorization endpoint for the flat permutation
and factors produced from the literal rounded Algorithm 11.2 execution.
-/

import NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedFactors

open scoped BigOperators

namespace NumStability

open Ch11Closure.Mixed

/-! ## Generic one- and two-column block assembly -/

noncomputable def higham11_2_blockOneL {n : Nat}
    (w : Fin n -> Real) (Ls : Fin n -> Fin n -> Real) :
    Fin (n + 1) -> Fin (n + 1) -> Real :=
  fun I J => Fin.cases (Fin.cases 1 (fun _ => 0) J)
    (fun i => Fin.cases (w i) (fun j => Ls i j) J) I

noncomputable def higham11_2_blockOneD {n : Nat} (d : Real)
    (Ds : Fin n -> Fin n -> Real) : Fin (n + 1) -> Fin (n + 1) -> Real :=
  fun I J => Fin.cases (Fin.cases d (fun _ => 0) J)
    (fun i => Fin.cases 0 (fun j => Ds i j) J) I

noncomputable def higham11_2_blockTwoL {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (Ls : Fin n -> Fin n -> Real) :
    Fin (n + 2) -> Fin (n + 2) -> Real :=
  fun I J => Fin.cases
    (Fin.cases 1 (fun K => Fin.cases 0 (fun _ => 0) K) J)
    (fun K => Fin.cases
      (Fin.cases 0 (fun L => Fin.cases 1 (fun _ => 0) L) J)
      (fun i => Fin.cases (W i 0)
        (fun L => Fin.cases (W i 1) (fun j => Ls i j) L) J) K) I

noncomputable def higham11_2_blockTwoD {n : Nat}
    (E : Fin 2 -> Fin 2 -> Real) (Ds : Fin n -> Fin n -> Real) :
    Fin (n + 2) -> Fin (n + 2) -> Real :=
  fun I J => Fin.cases
    (Fin.cases (E 0 0) (fun K => Fin.cases (E 0 1) (fun _ => 0) K) J)
    (fun K => Fin.cases
      (Fin.cases (E 1 0) (fun L => Fin.cases (E 1 1) (fun _ => 0) L) J)
      (fun i => Fin.cases 0
        (fun L => Fin.cases 0 (fun j => Ds i j) L) J) K) I

noncomputable def higham11_2_ldltProduct {n : Nat}
    (L D : Fin n -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun i j => ∑ k₁, ∑ k₂, L i k₁ * D k₁ k₂ * L j k₂

@[simp] theorem higham11_2_blockOneL_00 {n : Nat} (w) (Ls) :
    higham11_2_blockOneL (n := n) w Ls 0 0 = 1 := by
  simp [higham11_2_blockOneL]

@[simp] theorem higham11_2_blockOneL_0s {n : Nat} (w) (Ls) (j : Fin n) :
    higham11_2_blockOneL (n := n) w Ls 0 j.succ = 0 := by
  simp [higham11_2_blockOneL]

@[simp] theorem higham11_2_blockOneL_s0 {n : Nat} (w) (Ls) (i : Fin n) :
    higham11_2_blockOneL (n := n) w Ls i.succ 0 = w i := by
  simp [higham11_2_blockOneL]

@[simp] theorem higham11_2_blockOneL_ss {n : Nat} (w) (Ls) (i j : Fin n) :
    higham11_2_blockOneL (n := n) w Ls i.succ j.succ = Ls i j := by
  simp [higham11_2_blockOneL]

@[simp] theorem higham11_2_blockOneD_00 {n : Nat} (d) (Ds) :
    higham11_2_blockOneD (n := n) d Ds 0 0 = d := by
  simp [higham11_2_blockOneD]

@[simp] theorem higham11_2_blockOneD_0s {n : Nat} (d) (Ds) (j : Fin n) :
    higham11_2_blockOneD (n := n) d Ds 0 j.succ = 0 := by
  simp [higham11_2_blockOneD]

@[simp] theorem higham11_2_blockOneD_s0 {n : Nat} (d) (Ds) (i : Fin n) :
    higham11_2_blockOneD (n := n) d Ds i.succ 0 = 0 := by
  simp [higham11_2_blockOneD]

@[simp] theorem higham11_2_blockOneD_ss {n : Nat} (d) (Ds) (i j : Fin n) :
    higham11_2_blockOneD (n := n) d Ds i.succ j.succ = Ds i j := by
  simp [higham11_2_blockOneD]

theorem higham11_2_blockOne_product_00 {n : Nat} (w) (Ls) (d) (Ds) :
    higham11_2_ldltProduct
      (higham11_2_blockOneL (n := n) w Ls)
      (higham11_2_blockOneD (n := n) d Ds) 0 0 = d := by
  simp [higham11_2_ldltProduct, Fin.sum_univ_succ]

theorem higham11_2_blockOne_product_0s {n : Nat} (w) (Ls) (d) (Ds)
    (j : Fin n) :
    higham11_2_ldltProduct
      (higham11_2_blockOneL (n := n) w Ls)
      (higham11_2_blockOneD (n := n) d Ds) 0 j.succ = d * w j := by
  simp [higham11_2_ldltProduct, Fin.sum_univ_succ]

theorem higham11_2_blockOne_product_s0 {n : Nat} (w) (Ls) (d) (Ds)
    (i : Fin n) :
    higham11_2_ldltProduct
      (higham11_2_blockOneL (n := n) w Ls)
      (higham11_2_blockOneD (n := n) d Ds) i.succ 0 = w i * d := by
  simp [higham11_2_ldltProduct, Fin.sum_univ_succ]

theorem higham11_2_blockOne_product_ss {n : Nat} (w) (Ls) (d) (Ds)
    (i j : Fin n) :
    higham11_2_ldltProduct
      (higham11_2_blockOneL (n := n) w Ls)
      (higham11_2_blockOneD (n := n) d Ds) i.succ j.succ =
      w i * d * w j + higham11_2_ldltProduct Ls Ds i j := by
  simp [higham11_2_ldltProduct, Fin.sum_univ_succ]

@[simp] theorem higham11_2_blockTwoL_00 {n : Nat} (W) (Ls) :
    higham11_2_blockTwoL (n := n) W Ls 0 0 = 1 := by
  simp only [higham11_2_blockTwoL, Fin.cases_zero]

@[simp] theorem higham11_2_blockTwoL_01 {n : Nat} (W) (Ls) :
    higham11_2_blockTwoL (n := n) W Ls 0 (Fin.succ 0) = 0 := by
  simp only [higham11_2_blockTwoL, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoL_0t {n : Nat} (W) (Ls) (j : Fin n) :
    higham11_2_blockTwoL (n := n) W Ls 0 j.succ.succ = 0 := by
  simp only [higham11_2_blockTwoL, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoL_10 {n : Nat} (W) (Ls) :
    higham11_2_blockTwoL (n := n) W Ls (Fin.succ 0) 0 = 0 := by
  simp only [higham11_2_blockTwoL, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoL_11 {n : Nat} (W) (Ls) :
    higham11_2_blockTwoL (n := n) W Ls (Fin.succ 0) (Fin.succ 0) = 1 := by
  simp only [higham11_2_blockTwoL, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoL_1t {n : Nat} (W) (Ls) (j : Fin n) :
    higham11_2_blockTwoL (n := n) W Ls (Fin.succ 0) j.succ.succ = 0 := by
  simp only [higham11_2_blockTwoL, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoL_t0 {n : Nat} (W) (Ls) (i : Fin n) :
    higham11_2_blockTwoL (n := n) W Ls i.succ.succ 0 = W i 0 := by
  simp only [higham11_2_blockTwoL, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoL_t1 {n : Nat} (W) (Ls) (i : Fin n) :
    higham11_2_blockTwoL (n := n) W Ls i.succ.succ (Fin.succ 0) = W i 1 := by
  simp only [higham11_2_blockTwoL, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoL_tt {n : Nat} (W) (Ls) (i j : Fin n) :
    higham11_2_blockTwoL (n := n) W Ls i.succ.succ j.succ.succ = Ls i j := by
  simp only [higham11_2_blockTwoL, Fin.cases_succ]

/- The first generic version of these reductions used `embedTwo` under
`fin_cases`; proof-irrelevant `Fin` witnesses made that interface brittle.
The source-facing reductions below use the literal coordinates 0 and 1. -/
/-
@[simp] theorem higham11_2_blockTwoD_pp {n : Nat}
    (E : Fin 2 -> Fin 2 -> Real) (Ds) (p q : Fin 2) :
    higham11_2_blockTwoD (n := n) E Ds (embedTwo n p) (embedTwo n q) = E p q := by
  fin_cases p <;> fin_cases q <;>
    simp only [embedTwo_zero, embedTwo_one, higham11_2_blockTwoD,
      Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoD_pt {n : Nat} (E) (Ds)
    (p : Fin 2) (j : Fin n) :
    higham11_2_blockTwoD (n := n) E Ds (embedTwo n p) j.succ.succ = 0 := by
  fin_cases p <;>
    simp only [embedTwo_zero, embedTwo_one, higham11_2_blockTwoD,
      Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoD_tp {n : Nat} (E) (Ds)
    (i : Fin n) (q : Fin 2) :
    higham11_2_blockTwoD (n := n) E Ds i.succ.succ (embedTwo n q) = 0 := by
  fin_cases q <;>
    simp only [embedTwo_zero, embedTwo_one, higham11_2_blockTwoD,
      Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoD_tt {n : Nat} (E) (Ds) (i j : Fin n) :
    higham11_2_blockTwoD (n := n) E Ds i.succ.succ j.succ.succ = Ds i j := by
  simp only [higham11_2_blockTwoD, Fin.cases_succ]

theorem higham11_2_blockTwo_product_pp {n : Nat} (W) (Ls)
    (E : Fin 2 -> Fin 2 -> Real) (Ds) (p q : Fin 2) :
    higham11_2_ldltProduct
      (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD (n := n) E Ds)
      (embedTwo n p) (embedTwo n q) = E p q := by
  fin_cases p <;> fin_cases q <;>
    simp only [embedTwo_zero, embedTwo_one, higham11_2_ldltProduct, sum_fin_add_two,
      higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
      higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
      higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
      higham11_2_blockTwoD_pp, higham11_2_blockTwoD_pt,
      zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
      Finset.sum_const_zero]

theorem higham11_2_blockTwo_product_pt {n : Nat} (W) (Ls)
    (E : Fin 2 -> Fin 2 -> Real) (Ds) (p : Fin 2) (j : Fin n) :
    higham11_2_ldltProduct
      (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD (n := n) E Ds)
      (embedTwo n p) j.succ.succ = ∑ q : Fin 2, E p q * W j q := by
  fin_cases p <;>
    simp only [embedTwo_zero, embedTwo_one, higham11_2_ldltProduct, sum_fin_add_two,
      higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
      higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
      higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
      higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
      higham11_2_blockTwoL_tt, higham11_2_blockTwoD_pp,
      higham11_2_blockTwoD_pt, zero_mul, mul_zero, one_mul, mul_one,
      add_zero, zero_add, Finset.sum_const_zero, Fin.sum_univ_two]

theorem higham11_2_blockTwo_product_tp {n : Nat} (W) (Ls)
    (E : Fin 2 -> Fin 2 -> Real) (Ds) (i : Fin n) (q : Fin 2) :
    higham11_2_ldltProduct
      (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD (n := n) E Ds)
      i.succ.succ (embedTwo n q) = ∑ p : Fin 2, W i p * E p q := by
  fin_cases q <;>
    simp only [embedTwo_zero, embedTwo_one, higham11_2_ldltProduct, sum_fin_add_two,
      higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
      higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
      higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
      higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
      higham11_2_blockTwoL_tt, higham11_2_blockTwoD_pp,
      higham11_2_blockTwoD_tp, higham11_2_blockTwoD_tt,
      zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
      Finset.sum_const_zero, Fin.sum_univ_two]

theorem higham11_2_blockTwo_product_tt {n : Nat} (W) (Ls)
    (E : Fin 2 -> Fin 2 -> Real) (Ds) (i j : Fin n) :
    higham11_2_ldltProduct
      (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD (n := n) E Ds) i.succ.succ j.succ.succ =
      (∑ p : Fin 2, ∑ q : Fin 2, W i p * E p q * W j q) +
        higham11_2_ldltProduct Ls Ds i j := by
  simp only [higham11_2_ldltProduct, sum_fin_add_two,
    higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
    higham11_2_blockTwoL_tt, higham11_2_blockTwoD_pp,
    higham11_2_blockTwoD_pt, higham11_2_blockTwoD_tp,
    higham11_2_blockTwoD_tt, zero_mul, mul_zero, add_zero, zero_add,
    Finset.sum_const_zero]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]

/-! ## Absolute-product splits -/

theorem higham11_2_blockOne_absProduct_ss {n : Nat} (w) (Ls) (d) (Ds)
    (i j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 1)
      (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds)
      i.succ j.succ =
      |w i| * |d| * |w j| +
        higham11_4_bunchKaufmanProductEntry n Ls Ds i j := by
  simp [higham11_4_bunchKaufmanProductEntry, Fin.sum_univ_succ]

theorem higham11_2_blockTwo_absProduct_tt {n : Nat} (W) (Ls) (E) (Ds)
    (i j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      i.succ.succ j.succ.succ =
      (∑ p : Fin 2, ∑ q : Fin 2, |W i p| * |E p q| * |W j q|) +
        higham11_4_bunchKaufmanProductEntry n Ls Ds i j := by
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
    higham11_2_blockTwoL_tt, higham11_2_blockTwoD_pp,
    higham11_2_blockTwoD_pt, higham11_2_blockTwoD_tp,
    higham11_2_blockTwoD_tt, abs_zero, abs_one, zero_mul, mul_zero,
    one_mul, add_zero, zero_add, Finset.sum_const_zero]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]

theorem higham11_2_blockTwo_absProduct_pt {n : Nat} (W) (Ls) (E) (Ds)
    (p : Fin 2) (j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      (embedTwo n p) j.succ.succ = ∑ q : Fin 2, |E p q| * |W j q| := by
  fin_cases p <;>
    simp only [embedTwo_zero, embedTwo_one, higham11_4_bunchKaufmanProductEntry,
      sum_fin_add_two,
      higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
      higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
      higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
      higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
      higham11_2_blockTwoL_tt, higham11_2_blockTwoD_pp,
      higham11_2_blockTwoD_pt, abs_zero, abs_one, zero_mul, mul_zero,
      one_mul, add_zero, zero_add, Finset.sum_const_zero,
      Fin.sum_univ_two]

theorem higham11_2_blockTwo_absProduct_tp {n : Nat} (W) (Ls) (E) (Ds)
    (i : Fin n) (q : Fin 2) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      i.succ.succ (embedTwo n q) = ∑ p : Fin 2, |W i p| * |E p q| := by
  fin_cases q <;>
    simp only [embedTwo_zero, embedTwo_one, higham11_4_bunchKaufmanProductEntry,
      sum_fin_add_two,
      higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
      higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
      higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
      higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
      higham11_2_blockTwoL_tt, higham11_2_blockTwoD_pp,
      higham11_2_blockTwoD_tp, higham11_2_blockTwoD_tt,
      abs_zero, abs_one, zero_mul, mul_zero, one_mul, add_zero,
      zero_add, Finset.sum_const_zero, Fin.sum_univ_two]

-/

@[simp] theorem higham11_2_blockTwoD_00 {n : Nat} (E) (Ds) :
    higham11_2_blockTwoD (n := n) E Ds 0 0 = E 0 0 := by
  simp only [higham11_2_blockTwoD, Fin.cases_zero]

@[simp] theorem higham11_2_blockTwoD_01 {n : Nat} (E) (Ds) :
    higham11_2_blockTwoD (n := n) E Ds 0 (Fin.succ 0) = E 0 1 := by
  simp only [higham11_2_blockTwoD, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoD_0t {n : Nat} (E) (Ds) (j : Fin n) :
    higham11_2_blockTwoD (n := n) E Ds 0 j.succ.succ = 0 := by
  simp only [higham11_2_blockTwoD, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoD_10 {n : Nat} (E) (Ds) :
    higham11_2_blockTwoD (n := n) E Ds (Fin.succ 0) 0 = E 1 0 := by
  simp only [higham11_2_blockTwoD, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoD_11 {n : Nat} (E) (Ds) :
    higham11_2_blockTwoD (n := n) E Ds (Fin.succ 0) (Fin.succ 0) = E 1 1 := by
  simp only [higham11_2_blockTwoD, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoD_1t {n : Nat} (E) (Ds) (j : Fin n) :
    higham11_2_blockTwoD (n := n) E Ds (Fin.succ 0) j.succ.succ = 0 := by
  simp only [higham11_2_blockTwoD, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoD_t0 {n : Nat} (E) (Ds) (i : Fin n) :
    higham11_2_blockTwoD (n := n) E Ds i.succ.succ 0 = 0 := by
  simp only [higham11_2_blockTwoD, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoD_t1 {n : Nat} (E) (Ds) (i : Fin n) :
    higham11_2_blockTwoD (n := n) E Ds i.succ.succ (Fin.succ 0) = 0 := by
  simp only [higham11_2_blockTwoD, Fin.cases_zero, Fin.cases_succ]

@[simp] theorem higham11_2_blockTwoD_tt {n : Nat} (E) (Ds) (i j : Fin n) :
    higham11_2_blockTwoD (n := n) E Ds i.succ.succ j.succ.succ = Ds i j := by
  simp only [higham11_2_blockTwoD, Fin.cases_succ]

theorem higham11_2_blockTwo_product_00 {n : Nat} (W) (Ls) (E) (Ds) :
    higham11_2_ldltProduct (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD E Ds) 0 0 = E 0 0 := by
  simp only [higham11_2_ldltProduct, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoD_00,
    higham11_2_blockTwoD_01, higham11_2_blockTwoD_0t,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]

theorem higham11_2_blockTwo_product_01 {n : Nat} (W) (Ls) (E) (Ds) :
    higham11_2_ldltProduct (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD E Ds) 0 (Fin.succ 0) = E 0 1 := by
  simp only [higham11_2_ldltProduct, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
    higham11_2_blockTwoD_00, higham11_2_blockTwoD_01,
    higham11_2_blockTwoD_0t, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

theorem higham11_2_blockTwo_product_10 {n : Nat} (W) (Ls) (E) (Ds) :
    higham11_2_ldltProduct (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD E Ds) (Fin.succ 0) 0 = E 1 0 := by
  simp only [higham11_2_ldltProduct, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
    higham11_2_blockTwoD_10, higham11_2_blockTwoD_11,
    higham11_2_blockTwoD_1t, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

theorem higham11_2_blockTwo_product_11 {n : Nat} (W) (Ls) (E) (Ds) :
    higham11_2_ldltProduct (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD E Ds) (Fin.succ 0) (Fin.succ 0) = E 1 1 := by
  simp only [higham11_2_ldltProduct, sum_fin_add_two,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_1t, higham11_2_blockTwoD_10,
    higham11_2_blockTwoD_11, higham11_2_blockTwoD_1t,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    Finset.sum_const_zero]

theorem higham11_2_blockTwo_product_0t {n : Nat} (W) (Ls) (E) (Ds)
    (j : Fin n) :
    higham11_2_ldltProduct (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD E Ds) 0 j.succ.succ =
      E 0 0 * W j 0 + E 0 1 * W j 1 := by
  simp only [higham11_2_ldltProduct, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_t0,
    higham11_2_blockTwoL_t1, higham11_2_blockTwoL_tt,
    higham11_2_blockTwoD_00, higham11_2_blockTwoD_01,
    higham11_2_blockTwoD_0t, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

theorem higham11_2_blockTwo_product_1t {n : Nat} (W) (Ls) (E) (Ds)
    (j : Fin n) :
    higham11_2_ldltProduct (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD E Ds) (Fin.succ 0) j.succ.succ =
      E 1 0 * W j 0 + E 1 1 * W j 1 := by
  simp only [higham11_2_ldltProduct, sum_fin_add_two,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_1t, higham11_2_blockTwoL_t0,
    higham11_2_blockTwoL_t1, higham11_2_blockTwoL_tt,
    higham11_2_blockTwoD_10, higham11_2_blockTwoD_11,
    higham11_2_blockTwoD_1t, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

theorem higham11_2_blockTwo_product_t0 {n : Nat} (W) (Ls) (E) (Ds)
    (i : Fin n) :
    higham11_2_ldltProduct (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD E Ds) i.succ.succ 0 =
      W i 0 * E 0 0 + W i 1 * E 1 0 := by
  simp only [higham11_2_ldltProduct, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_t0,
    higham11_2_blockTwoL_t1, higham11_2_blockTwoL_tt,
    higham11_2_blockTwoD_00, higham11_2_blockTwoD_10,
    higham11_2_blockTwoD_t0, higham11_2_blockTwoD_01,
    higham11_2_blockTwoD_11, higham11_2_blockTwoD_t1,
    higham11_2_blockTwoD_0t, higham11_2_blockTwoD_1t,
    higham11_2_blockTwoD_tt, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

theorem higham11_2_blockTwo_product_t1 {n : Nat} (W) (Ls) (E) (Ds)
    (i : Fin n) :
    higham11_2_ldltProduct (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD E Ds) i.succ.succ (Fin.succ 0) =
      W i 0 * E 0 1 + W i 1 * E 1 1 := by
  simp only [higham11_2_ldltProduct, sum_fin_add_two,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_1t, higham11_2_blockTwoL_t0,
    higham11_2_blockTwoL_t1, higham11_2_blockTwoL_tt,
    higham11_2_blockTwoD_00, higham11_2_blockTwoD_10,
    higham11_2_blockTwoD_t0, higham11_2_blockTwoD_01,
    higham11_2_blockTwoD_11, higham11_2_blockTwoD_t1,
    higham11_2_blockTwoD_0t, higham11_2_blockTwoD_1t,
    higham11_2_blockTwoD_tt, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

noncomputable def higham11_2_blockTwoPivotPath {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (E : Fin 2 -> Fin 2 -> Real)
    (i j : Fin n) : Real :=
  ∑ p : Fin 2, ∑ q : Fin 2, W i p * E p q * W j q

theorem higham11_2_blockTwo_product_tt {n : Nat} (W) (Ls) (E) (Ds)
    (i j : Fin n) :
    higham11_2_ldltProduct (higham11_2_blockTwoL (n := n) W Ls)
      (higham11_2_blockTwoD E Ds) i.succ.succ j.succ.succ =
      higham11_2_blockTwoPivotPath W E i j +
        higham11_2_ldltProduct Ls Ds i j := by
  simp only [higham11_2_ldltProduct, sum_fin_add_two,
    higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
    higham11_2_blockTwoL_tt, higham11_2_blockTwoD_00,
    higham11_2_blockTwoD_01, higham11_2_blockTwoD_10,
    higham11_2_blockTwoD_11, higham11_2_blockTwoD_0t,
    higham11_2_blockTwoD_1t, higham11_2_blockTwoD_t0,
    higham11_2_blockTwoD_t1, higham11_2_blockTwoD_tt,
    zero_mul, mul_zero, add_zero, zero_add, Finset.sum_const_zero]
  rw [higham11_2_blockTwoPivotPath, Fin.sum_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two]

/-! ## Absolute-product splits -/

theorem higham11_2_blockOne_absProduct_ss' {n : Nat} (w) (Ls) (d) (Ds)
    (i j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 1)
      (higham11_2_blockOneL w Ls) (higham11_2_blockOneD d Ds)
      i.succ j.succ =
      |w i| * |d| * |w j| +
        higham11_4_bunchKaufmanProductEntry n Ls Ds i j := by
  simp [higham11_4_bunchKaufmanProductEntry, Fin.sum_univ_succ]

noncomputable def higham11_2_blockTwoPivotPathAbs {n : Nat}
    (W : Fin n -> Fin 2 -> Real) (E : Fin 2 -> Fin 2 -> Real)
    (i j : Fin n) : Real :=
  ∑ p : Fin 2, ∑ q : Fin 2, |W i p| * |E p q| * |W j q|

theorem higham11_2_blockTwo_absProduct_tt' {n : Nat} (W) (Ls) (E) (Ds)
    (i j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      i.succ.succ j.succ.succ =
      higham11_2_blockTwoPivotPathAbs W E i j +
        higham11_4_bunchKaufmanProductEntry n Ls Ds i j := by
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
    higham11_2_blockTwoL_tt, higham11_2_blockTwoD_00,
    higham11_2_blockTwoD_01, higham11_2_blockTwoD_10,
    higham11_2_blockTwoD_11, higham11_2_blockTwoD_0t,
    higham11_2_blockTwoD_1t, higham11_2_blockTwoD_t0,
    higham11_2_blockTwoD_t1, higham11_2_blockTwoD_tt,
    abs_zero, zero_mul, mul_zero, add_zero, zero_add,
    Finset.sum_const_zero]
  rw [higham11_2_blockTwoPivotPathAbs, Fin.sum_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two]

theorem higham11_2_blockTwo_absProduct_0t' {n : Nat} (W) (Ls) (E) (Ds)
    (j : Fin n) :
  higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      0 j.succ.succ = ∑ q : Fin 2, |E 0 q| * |W j q| := by
  rw [Fin.sum_univ_two]
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
    higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
    higham11_2_blockTwoL_tt, higham11_2_blockTwoD_00,
    higham11_2_blockTwoD_01, higham11_2_blockTwoD_0t,
    higham11_2_blockTwoD_10, higham11_2_blockTwoD_11,
    higham11_2_blockTwoD_1t, higham11_2_blockTwoD_t0,
    higham11_2_blockTwoD_t1, higham11_2_blockTwoD_tt,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

theorem higham11_2_blockTwo_absProduct_1t' {n : Nat} (W) (Ls) (E) (Ds)
    (j : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      (Fin.succ 0) j.succ.succ = ∑ q : Fin 2, |E 1 q| * |W j q| := by
  rw [Fin.sum_univ_two]
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
    higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
    higham11_2_blockTwoL_tt, higham11_2_blockTwoD_00,
    higham11_2_blockTwoD_01, higham11_2_blockTwoD_0t,
    higham11_2_blockTwoD_10, higham11_2_blockTwoD_11,
    higham11_2_blockTwoD_1t, higham11_2_blockTwoD_t0,
    higham11_2_blockTwoD_t1, higham11_2_blockTwoD_tt,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

theorem higham11_2_blockTwo_absProduct_t0' {n : Nat} (W) (Ls) (E) (Ds)
    (i : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      i.succ.succ 0 = ∑ p : Fin 2, |W i p| * |E p 0| := by
  rw [Fin.sum_univ_two]
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
    higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
    higham11_2_blockTwoL_tt, higham11_2_blockTwoD_00,
    higham11_2_blockTwoD_01, higham11_2_blockTwoD_0t,
    higham11_2_blockTwoD_10, higham11_2_blockTwoD_11,
    higham11_2_blockTwoD_1t, higham11_2_blockTwoD_t0,
    higham11_2_blockTwoD_t1, higham11_2_blockTwoD_tt,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

theorem higham11_2_blockTwo_absProduct_t1' {n : Nat} (W) (Ls) (E) (Ds)
    (i : Fin n) :
    higham11_4_bunchKaufmanProductEntry (n + 2)
      (higham11_2_blockTwoL W Ls) (higham11_2_blockTwoD E Ds)
      i.succ.succ (Fin.succ 0) = ∑ p : Fin 2, |W i p| * |E p 1| := by
  rw [Fin.sum_univ_two]
  simp only [higham11_4_bunchKaufmanProductEntry, sum_fin_add_two,
    higham11_2_blockTwoL_00, higham11_2_blockTwoL_01,
    higham11_2_blockTwoL_10, higham11_2_blockTwoL_11,
    higham11_2_blockTwoL_0t, higham11_2_blockTwoL_1t,
    higham11_2_blockTwoL_t0, higham11_2_blockTwoL_t1,
    higham11_2_blockTwoL_tt, higham11_2_blockTwoD_00,
    higham11_2_blockTwoD_01, higham11_2_blockTwoD_0t,
    higham11_2_blockTwoD_10, higham11_2_blockTwoD_11,
    higham11_2_blockTwoD_1t, higham11_2_blockTwoD_t0,
    higham11_2_blockTwoD_t1, higham11_2_blockTwoD_tt,
    abs_zero, abs_one, zero_mul, mul_zero, one_mul, mul_one,
    add_zero, zero_add, Finset.sum_const_zero]

end NumStability
