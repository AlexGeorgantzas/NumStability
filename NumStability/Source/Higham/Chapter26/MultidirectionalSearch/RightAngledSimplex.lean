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

/-! # Higham Chapter 26: Right-Angled Initial Simplex

The right-angled initial-simplex construction from page 476 and its edge geometry.
-/

/-- Higham p. 476 / Torczon right-angled starting simplex: it contains `x₀`
as its base and adds one scaled coordinate vector for each other vertex. -/
noncomputable def higham26RightAngledSimplex {n : Nat}
    (x0 : RVec n) : MDSSimplex n where
  base := x0
  other := fun i j =>
    x0 j + if j = i then higham26MDSInitialScale x0 else 0

@[simp] theorem higham26RightAngledSimplex_base {n : Nat} (x0 : RVec n) :
    (higham26RightAngledSimplex x0).base = x0 := rfl

/-- Every right-angled edge joined to `x₀` has the printed scale as its
Euclidean length (squared form). -/
theorem higham26RightAngledSimplex_edge_sq {n : Nat}
    (x0 : RVec n) (i : Fin n) :
    higham26SquaredDistance ((higham26RightAngledSimplex x0).other i) x0 =
      higham26MDSInitialScale x0 ^ 2 := by
  unfold higham26SquaredDistance higham26RightAngledSimplex
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Euclidean edge-length form of the same p. 476 scaling statement. -/
theorem higham26RightAngledSimplex_edge_length {n : Nat}
    (x0 : RVec n) (i : Fin n) :
    Real.sqrt
        (higham26SquaredDistance ((higham26RightAngledSimplex x0).other i) x0) =
      higham26MDSInitialScale x0 := by
  rw [higham26RightAngledSimplex_edge_sq]
  exact Real.sqrt_sq (higham26MDSInitialScale_nonneg x0)

/-- Distinct coordinate edges of the constructed simplex are orthogonal,
which justifies the source term “right-angled”. -/
theorem higham26RightAngledSimplex_edges_orthogonal {n : Nat}
    (x0 : RVec n) (i k : Fin n) (hik : i ≠ k) :
    higham26EdgeDot x0
      ((higham26RightAngledSimplex x0).other i)
      ((higham26RightAngledSimplex x0).other k) = 0 := by
  unfold higham26EdgeDot higham26RightAngledSimplex
  apply Finset.sum_eq_zero
  intro j _
  by_cases hji : j = i <;> by_cases hjk : j = k
  · subst j
    exact (hik hjk).elim
  · subst j
    simp [hik]
  · subst j
    simp [Ne.symm hik]
  · simp [hji, hjk]

end NumStability
