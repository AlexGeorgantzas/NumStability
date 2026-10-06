/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter26.MultidirectionalSearch.InitialSimplexGeometry
import NumStability.Source.Higham.Chapter26.MultidirectionalSearch.Simplex
import Mathlib.Tactic

namespace NumStability

open scoped BigOperators

/-! # Higham Chapter 26: Regular Initial Simplex

The regular initial-simplex construction from page 476, including its coefficient and edge-length identities.
-/

/-! ## Regular starting simplex from p. 476

The following is the standard coordinate realization used for a regular
simplex with one vertex fixed at `x₀`.  If `s` is the desired side length,
write

`a = s / √2`, `b = s(√(n+1)-1)/(n√2)`

and take the `i`th non-base edge to have coordinate vector `b·1 + a·eᵢ`.
-/

noncomputable def higham26RegularA (s : Real) : Real :=
  s / Real.sqrt 2

noncomputable def higham26RegularB (n : Nat) (s : Real) : Real :=
  s * (Real.sqrt ((n + 1 : Nat) : Real) - 1) /
    ((n : Real) * Real.sqrt 2)

/-- The coefficient identity making every base-to-other edge have squared
length `s²`. -/
theorem higham26Regular_coeff_base_sq (n : Nat) (hn : 0 < n) (s : Real) :
    higham26RegularA s ^ 2 +
        2 * higham26RegularA s * higham26RegularB n s +
        (n : Real) * higham26RegularB n s ^ 2 = s ^ 2 := by
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : Real.sqrt 2 ^ 2 = (2 : Real) :=
    Real.sq_sqrt (by norm_num)
  have hnpos : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hsqrtn : Real.sqrt ((n + 1 : Nat) : Real) ^ 2 =
      ((n + 1 : Nat) : Real) := Real.sq_sqrt (by positivity)
  have hsqrtn' : Real.sqrt ((n + 1 : Nat) : Real) ^ 2 =
      (n : Real) + 1 := by
    simpa using hsqrtn
  have hbracket :
      (n : Real) + 2 * (Real.sqrt ((n + 1 : Nat) : Real) - 1) +
          (Real.sqrt ((n + 1 : Nat) : Real) - 1) ^ 2 = 2 * (n : Real) := by
    nlinarith [hsqrtn']
  unfold higham26RegularA higham26RegularB
  field_simp [ne_of_gt hsqrt2pos, ne_of_gt hnpos]
  rw [hbracket, hsqrt2sq]
  ring

/-- The `a=s/√2` coefficient makes the difference of two distinct edge
vectors have squared length `2a²=s²`. -/
theorem higham26Regular_coeff_pair_sq (s : Real) :
    2 * higham26RegularA s ^ 2 = s ^ 2 := by
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : Real.sqrt 2 ^ 2 = (2 : Real) :=
    Real.sq_sqrt (by norm_num)
  unfold higham26RegularA
  field_simp [ne_of_gt hsqrt2pos]
  nlinarith

/-- Higham p. 476 / Torczon regular starting simplex, with `x₀` as base and
all `n(n+1)/2` edges scaled to `max (‖x₀‖∞,1)`. -/
noncomputable def higham26RegularSimplex {n : Nat}
    (x0 : RVec n) : MDSSimplex n where
  base := x0
  other := fun i j =>
    x0 j + higham26RegularB n (higham26MDSInitialScale x0) +
      if j = i then higham26RegularA (higham26MDSInitialScale x0) else 0

@[simp] theorem higham26RegularSimplex_base {n : Nat} (x0 : RVec n) :
    (higham26RegularSimplex x0).base = x0 := rfl

private theorem higham26Regular_base_sum (n : Nat) (hn : 0 < n)
    (s : Real) (i : Fin n) :
    (∑ j : Fin n,
        (higham26RegularB n s +
          if j = i then higham26RegularA s else 0) ^ 2) = s ^ 2 := by
  let a := higham26RegularA s
  let b := higham26RegularB n s
  change (∑ j : Fin n, (b + if j = i then a else 0) ^ 2) = s ^ 2
  have hpoint : ∀ j : Fin n,
      (b + if j = i then a else 0) ^ 2 =
        b ^ 2 + if j = i then a ^ 2 + 2 * a * b else 0 := by
    intro j
    by_cases hji : j = i <;> simp [hji] <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp
  have hcoeff := higham26Regular_coeff_base_sq n hn s
  dsimp [a, b]
  nlinarith

/-- Every edge from the base of the constructed regular simplex has the
printed squared length. -/
theorem higham26RegularSimplex_base_edge_sq {n : Nat} (hn : 0 < n)
    (x0 : RVec n) (i : Fin n) :
    higham26SquaredDistance ((higham26RegularSimplex x0).other i) x0 =
      higham26MDSInitialScale x0 ^ 2 := by
  unfold higham26SquaredDistance higham26RegularSimplex
  convert higham26Regular_base_sum n hn (higham26MDSInitialScale x0) i using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem higham26Regular_pair_sum (n : Nat) (s : Real)
    (i k : Fin n) (hik : i ≠ k) :
    (∑ j : Fin n,
      ((if j = i then higham26RegularA s else 0) -
        (if j = k then higham26RegularA s else 0)) ^ 2) = s ^ 2 := by
  let a := higham26RegularA s
  have hpoint : ∀ j : Fin n,
      ((if j = i then a else 0) - (if j = k then a else 0)) ^ 2 =
        (if j = i then a ^ 2 else 0) +
          (if j = k then a ^ 2 else 0) := by
    intro j
    by_cases hji : j = i <;> by_cases hjk : j = k
    · subst j
      exact (hik hjk).elim
    · subst j
      simp [hik]
    · subst j
      simp [Ne.symm hik]
    · simp [hji, hjk]
  change (∑ j : Fin n,
      ((if j = i then a else 0) - (if j = k then a else 0)) ^ 2) = s ^ 2
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp
  simpa [a, two_mul] using higham26Regular_coeff_pair_sq s

/-- Every edge between two distinct non-base vertices also has the printed
squared length, so the constructor is genuinely regular. -/
theorem higham26RegularSimplex_other_edge_sq {n : Nat}
    (x0 : RVec n) (i k : Fin n) (hik : i ≠ k) :
    higham26SquaredDistance
        ((higham26RegularSimplex x0).other i)
        ((higham26RegularSimplex x0).other k) =
      higham26MDSInitialScale x0 ^ 2 := by
  unfold higham26SquaredDistance higham26RegularSimplex
  convert higham26Regular_pair_sum n (higham26MDSInitialScale x0) i k hik using 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Euclidean length statement for base edges of the regular simplex. -/
theorem higham26RegularSimplex_base_edge_length {n : Nat} (hn : 0 < n)
    (x0 : RVec n) (i : Fin n) :
    Real.sqrt
        (higham26SquaredDistance ((higham26RegularSimplex x0).other i) x0) =
      higham26MDSInitialScale x0 := by
  rw [higham26RegularSimplex_base_edge_sq hn]
  exact Real.sqrt_sq (higham26MDSInitialScale_nonneg x0)

/-- Euclidean length statement for all other regular-simplex edges. -/
theorem higham26RegularSimplex_other_edge_length {n : Nat}
    (x0 : RVec n) (i k : Fin n) (hik : i ≠ k) :
    Real.sqrt
        (higham26SquaredDistance
          ((higham26RegularSimplex x0).other i)
          ((higham26RegularSimplex x0).other k)) =
      higham26MDSInitialScale x0 := by
  rw [higham26RegularSimplex_other_edge_sq x0 i k hik]
  exact Real.sqrt_sq (higham26MDSInitialScale_nonneg x0)

end NumStability
